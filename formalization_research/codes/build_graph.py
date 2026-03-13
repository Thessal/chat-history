import sys
import os
import json
import argparse
from collections import defaultdict

import pandas as pd
import networkx as nx

def load_file(input_path):
    try:
        with open(input_path, 'r') as f:
            works = json.load(f)['response']['results']
    except:
        print(f"Error: Invalid JSON file : input_path")
        works = []

    return works

def process_works(input_path):
    works = []
    if input_path.endswith('.json'):
        print(f"Loading single JSON file: {input_path}")
        works = load_file(input_path)
    else:
        print(f"Loading JSON Lines from directory/file: {input_path}")
        if os.path.isdir(input_path):
            files = [os.path.join(input_path, f) for f in os.listdir(input_path) if f.endswith('.jsonl') or f.endswith('.json')]
        else:
            files = [input_path]

        for filepath in files:
            works.extend(load_file(filepath))
    return works

def build_network(works, output_dir):
    os.makedirs(output_dir, exist_ok=True)
    
    # 1. Preprocessing: dict_author_citation
    print("Preprocessing: Building dict_author_citation...")
    dict_author_citation = defaultdict(lambda: defaultdict(int))
    
    parsed_works = []
    
    for work in works:
        if not isinstance(work, dict):
            continue
            
        wid = work.get('id', '')
        if not wid:
            continue
            
        pub_year = work.get('publication_year')
        wtype = work.get('type')
        
        authorships = work.get('authorships', [])
        author_ids = []
        institution_lineages = []
        
        for authorship in authorships:
            author = authorship.get('author')
            if author:
                aid = author.get('id')
                if aid:
                    author_ids.append(aid)
            
            institutions = authorship.get('institutions', [])
            for inst in institutions:
                lineage = inst.get('lineage', [])
                institution_lineages.extend(lineage)
                iid = inst.get('id')
                if iid:
                    institution_lineages.append(iid)
                    
        author_ids = list(set(author_ids))
        institution_lineages = list(set(institution_lineages))
        
        counts_by_year = work.get('counts_by_year', [])
        citation_counts = {}
        if counts_by_year:
            for entry in counts_by_year:
                yr = entry.get('year')
                cnt = entry.get('cited_by_count', 0)
                if yr is not None:
                    citation_counts[yr] = cnt
                    
        for aid in author_ids:
            for yr, cnt in citation_counts.items():
                dict_author_citation[aid][yr] += cnt
                
        inst_dist_count = work.get('institutions_distinct_count')
        if inst_dist_count is None:
            inst_dist_count = len(set(i.get('id') for a in authorships for i in a.get('institutions', []) if i.get('id')))
            
        open_access_info = work.get('open_access', {})
        is_oa = open_access_info.get('is_oa') if isinstance(open_access_info, dict) else False
        
        indexed_in = work.get('indexed_in', [])
        language = work.get('language')
        display_name = work.get('display_name', '')
        title = work.get('title', '')
        
        len_display_name = len(display_name) if display_name else 0
        display_name_lower = (display_name or "").lower()
        title_lower = (title or "").lower()
        is_review = 1 if ('review' in display_name_lower or 'review' in title_lower) else 0
        
        pub_year_int = pub_year if pub_year is not None else 0
        first_year_citation_count = citation_counts.get(pub_year_int, 0)
        ten_year_citation_count = sum(citation_counts.get(y, 0) for y in range(pub_year_int, pub_year_int + 11))
        # Do not use dict_author_citation and use cited_by_count directly
        total_cited_by_count = work.get('cited_by_count', 0)
        
        referenced_works_count = work.get('referenced_works_count', 0)
        referenced_works = work.get('referenced_works', [])
        if referenced_works and isinstance(referenced_works, list):
            if len(referenced_works) > 0 and isinstance(referenced_works[0], dict):
                referenced_works = [rw.get('id') for rw in referenced_works if isinstance(rw, dict) and rw.get('id')]
            elif len(referenced_works) > 0 and isinstance(referenced_works[0], str):
                referenced_works = [rw for rw in referenced_works if isinstance(rw, str)]
        
        # Keywords and Topics extraction
        keywords_list = work.get('keywords', [])
        keywords_data = []
        for kw in keywords_list:
            if isinstance(kw, dict):
                score = round(kw.get('score', 0), 3) if kw.get('score') is not None else 0
                keywords_data.append(f"{kw.get('display_name', '')}::{score}")
        keywords_str = "|".join(keywords_data)

        topics_list = work.get('topics', [])
        topic_ids = []
        subfield_ids = []
        field_ids = []
        domain_ids = []
        
        for t in topics_list:
            if isinstance(t, dict):
                tid = t.get('id', '').split('/')[-1] if t.get('id') else ''
                if tid: topic_ids.append(tid)
                
                sf = t.get('subfield', {})
                sfid = sf.get('id', '').split('/')[-1] if isinstance(sf, dict) and sf.get('id') else ''
                if sfid: subfield_ids.append(sfid)
                
                fid = t.get('field', {})
                fid_val = fid.get('id', '').split('/')[-1] if isinstance(fid, dict) and fid.get('id') else ''
                if fid_val: field_ids.append(fid_val)
                
                did = t.get('domain', {})
                did_val = did.get('id', '').split('/')[-1] if isinstance(did, dict) and did.get('id') else ''
                if did_val: domain_ids.append(did_val)
                
        topic_ids_str = "|".join(list(dict.fromkeys(topic_ids)))
        subfield_ids_str = "|".join(list(dict.fromkeys(subfield_ids)))
        field_ids_str = "|".join(list(dict.fromkeys(field_ids)))
        domain_ids_str = "|".join(list(dict.fromkeys(domain_ids)))

        error_status = 0
        if not wid or pub_year is None:
            error_status = -1
            
        parsed_works.append({
            'id': str(wid),
            'pub_year': pub_year_int,
            'work_type': str(wtype) if wtype else "",
            'author_ids': author_ids,
            'institution_lineages': institution_lineages,
            'citation_counts': citation_counts,
            'inst_dist_count': int(inst_dist_count),
            'is_oa': bool(is_oa),
            'indexed_in': "|".join([str(x) for x in indexed_in]) if isinstance(indexed_in, list) else "",
            'language': str(language) if language else "",
            'len_display_name': len_display_name,
            'is_review': is_review,
            'first_year_citation_count': first_year_citation_count,
            'ten_year_citation_count': ten_year_citation_count,
            'total_cited_by_count': total_cited_by_count,
            'referenced_works_count': int(referenced_works_count),
            'referenced_works': [str(x) for x in referenced_works],
            'error_status': error_status,
            'keywords': keywords_str,
            'topic_ids': topic_ids_str,
            'subfield_ids': subfield_ids_str,
            'field_ids': field_ids_str,
            'domain_ids': domain_ids_str
        })
        
    # Save dict_author_citation to file
    dict_path = os.path.join(output_dir, 'dict_author_citation.json')
    with open(dict_path, 'w') as f:
        json.dump({k: dict(v) for k,v in dict_author_citation.items()}, f)
    print(f"Saved dict_author_citation to {dict_path}")

    print("Building Graph Nodes...")
    G = nx.DiGraph()
    
    nodes_data = []
    works_by_id = {}
    
    for w in parsed_works:
        works_by_id[w['id']] = w
        
        target_year = w['pub_year'] - 1
        max_cit = 0
        for aid in w['author_ids']:
            if aid in dict_author_citation and target_year in dict_author_citation[aid]:
                c = dict_author_citation[aid][target_year]
                if c > max_cit:
                    max_cit = c
                    
        node_attr = {
            'published_year': w['pub_year'],
            'work_type': w['work_type'],
            'institutions_distinct_count': w['inst_dist_count'],
            'max_prev_year_author_citation': max_cit,
            'open_access': w['is_oa'],
            'indexed_in': w['indexed_in'],
            'language': w['language'],
            'len_display_name': w['len_display_name'],
            'is_review': w['is_review'],
            'first_year_citation_count': w['first_year_citation_count'],
            'ten_year_citation_count': w['ten_year_citation_count'],
            'total_cited_by_count': w['total_cited_by_count'],
            'error_status': w['error_status'],
            'referenced_works_count': w['referenced_works_count'],
            'keywords': w['keywords'],
            'topic_ids': w['topic_ids'],
            'subfield_ids': w['subfield_ids'],
            'field_ids': w['field_ids'],
            'domain_ids': w['domain_ids']
        }
        
        G.add_node(w['id'], **node_attr)
        
        node_row = {'id': w['id']}
        node_row.update(node_attr)
        nodes_data.append(node_row)
        
    print("Building Graph Edges...")
    edges_data = []
    
    for w in parsed_works:
        src = w['id']
        src_authors = set(w['author_ids'])
        src_insts = set(w['institution_lineages'])
        ref_count = w['referenced_works_count']
        weight = 1.0 / ref_count if ref_count > 0 else 0.0
        
        # Keep track of added edges to avoid duplicates in edge_data list if referenced_works has repetitions
        seen_targets = set()
        for dst in w['referenced_works']:
            if dst in seen_targets:
                continue
            seen_targets.add(dst)
            
            dst_work = works_by_id.get(dst)
            if dst_work:
                dst_authors = set(dst_work['author_ids'])
                dst_insts = set(dst_work['institution_lineages'])
                
                author_prev = 1 if src_authors.intersection(dst_authors) else 0
                inst_prev = 1 if src_insts.intersection(dst_insts) else 0
            else:
                author_prev = 0
                inst_prev = 0
                
            G.add_edge(src, dst, 
                       author_previous_work=author_prev, 
                       institution_previous_work=inst_prev,
                       weight=weight)
                       
            edges_data.append({
                'source': src,
                'target': dst,
                'author_previous_work': author_prev,
                'institution_previous_work': inst_prev,
                'weight': weight
            })
            
    print(f"Graph built with {G.number_of_nodes()} nodes and {G.number_of_edges()} edges.")
    
    # Save networkx graph
    graphml_path = os.path.join(output_dir, 'citation_network.graphml')
    nx.write_graphml(G, graphml_path)
    print(f"Saved GraphML to {graphml_path}")
    
    print("Exporting data to Pandas CSV...")
    nodes_df = pd.DataFrame(nodes_data)
    edges_df = pd.DataFrame(edges_data)
    
    if not nodes_df.empty:
        nodes_df.to_csv(os.path.join(output_dir, 'nodelist.csv'), index=False)
    else:
        print("Warning: nodes dataframe is empty.")
        
    if not edges_df.empty:
        edges_df.to_csv(os.path.join(output_dir, 'edgelist.csv'), index=False)
    else:
        print("Warning: edges dataframe is empty.")
        
    print("Finished successfully!")

def main():
    parser = argparse.ArgumentParser(description="Build Citation Network from OpenAlex data")
    parser.add_argument("--input", required=True, help="Input directory or single JSON file")
    parser.add_argument("--output_dir", required=True, help="Output directory for CSVs and JSON")
    args = parser.parse_args()
    
    works = process_works(args.input)
    if not works:
        print("No works found to process.")
        return
        
    build_network(works, args.output_dir)

if __name__ == "__main__":
    main()
