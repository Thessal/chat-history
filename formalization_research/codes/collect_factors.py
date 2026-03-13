import requests
import time
import pandas as pd
import os
import sys
import pickle
import json

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
RESULTS_DIR = os.path.join(BASE_DIR, "results")
os.makedirs(RESULTS_DIR, exist_ok=True)

def read_key_file(filename):
    key_path = os.path.join(BASE_DIR, filename)
    try:
        with open(key_path, 'r') as f:
            return f.read().strip()
    except FileNotFoundError:
        return ""

EMAIL = read_key_file("id.key")
API_KEY = read_key_file("secret.key")
BASE_URL = "https://api.openalex.org/works"

FIELD_FILTER = "topics.field.id:17|18|20|26|31"
CHECKPOINT_FILE = "papers_checkpoint.pkl"

query_counter = 0

def load_checkpoint():
    if os.path.exists(CHECKPOINT_FILE):
        print(f"Loading previous state from {CHECKPOINT_FILE}...")
        with open(CHECKPOINT_FILE, 'rb') as f:
            return pickle.load(f)
    return {}

def save_checkpoint(data):
    with open(CHECKPOINT_FILE, 'wb') as f:
        pickle.dump(data, f)
    print("\n[State Checkpointed]")

def save_raw_response(prefix, counter, params, res):
    filename = os.path.join(RESULTS_DIR, f"{prefix}_query_{counter}.json")
    try:
        resp_data = res.json()
    except Exception:
        resp_data = {"raw_text": res.text}
    with open(filename, 'w', encoding='utf-8') as f:
        json.dump({"params": params, "response": resp_data}, f, ensure_ascii=False, indent=2)

def get_abstract_length(inverted_index):
    if not inverted_index:
        return 0
    return sum(len(positions) for positions in inverted_index.values())

def parse_work_data(work, depth_label):
    return {
        "id": work.get("id"),
        "title": work.get("title"),
        "doi": work.get("doi"),
        "publication_year": work.get("publication_year"),
        "publication_date": work.get("publication_date"),
        "cited_by_count": work.get("cited_by_count", 0),
        "out_degree": len(work.get("referenced_works", [])),
        "referenced_works": work.get("referenced_works", []),
        "title_length": len(work.get("title").split()) if work.get("title") else 0,
        "abstract_length": get_abstract_length(work.get("abstract_inverted_index")),
        "is_oa": work.get("open_access", {}).get("is_oa", False),
        "language": work.get("language", "unknown"),
        "depth": depth_label
    }

def get_base_params():
    params = {}
    if EMAIL:
        params["mailto"] = EMAIL
    if API_KEY:
        params["api_key"] = API_KEY
    return params

def fetch_symbolic_regression_papers():
    """Fetches Depth-0 papers (root papers directly matching the SR query)."""
    global query_counter
    params = get_base_params()
    params.update({
        "search": "symbolic regression",
        "filter": f"publication_year:2016-2026,title.search:review,cited_by_count:>100,{FIELD_FILTER}",
        "per_page": 200,
        "cursor": "*"
    })
    
    papers_data = {}
    
    while params.get("cursor"):
        res = requests.get(BASE_URL, params=params)
        query_counter += 1
        
        save_raw_response("depth0", query_counter, params, res)
        
        if res.status_code == 429:
            print("\nRate limited! Sleeping...")
            time.sleep(2)
            continue
        if res.status_code != 200:
            print(f"\nAPI Error ({res.status_code}): {res.text}")
            break
            
        data = res.json()
        results = data.get("results", [])
        if not results:
            break
            
        for work in results:
            work_id = work.get("id")
            title = work.get("title") or "No Title"
            print(f"[{title[:30]}...]", end=", ", flush=True)
            papers_data[work_id] = parse_work_data(work, 0)
            
        params["cursor"] = data.get("meta", {}).get("next_cursor")
        time.sleep(0.1)
        
    return papers_data

def fetch_works_by_ids(work_ids, depth_label, all_papers_state):
    """Fetches works by a list of openalex IDs and returns parsed paper data."""
    global query_counter
    papers_data = {}
    chunk_size = 50
    work_ids = list(work_ids)
    
    print(f"\n[Depth {depth_label}] Fetching {len(work_ids)} referenced papers in chunks of {chunk_size}...")
    
    for i in range(0, len(work_ids), chunk_size):
        chunk = work_ids[i:i+chunk_size]
        short_ids = [cid.split('/')[-1] for cid in chunk] 
        id_filter = "openalex:" + "|".join(short_ids)
        
        params = get_base_params()
        params.update({
            "filter": f"{id_filter},{FIELD_FILTER}",
            "per_page": 50
        })
        
        retries = 3
        while retries > 0:
            res = requests.get(BASE_URL, params=params)
            query_counter += 1
            
            save_raw_response(f"depth{depth_label}", query_counter, params, res)
            
            if res.status_code == 429:
                print("\nRate limited! Sleeping...", flush=True)
                time.sleep(2)
                retries -= 1
                continue
            if res.status_code != 200:
                print(f"\nAPI Error ({res.status_code}) on chunk: {res.text}", flush=True)
                break
                
            data = res.json()
            results = data.get("results", [])
            for work in results:
                work_id = work.get("id")
                title = work.get("title") or "No Title"
                print(f"[{title[:30]}...]", end=" | ", flush=True)
                new_work = parse_work_data(work, depth_label)
                papers_data[work_id] = new_work
                all_papers_state[work_id] = new_work  # Instantly inject into global cache
            break
            
        time.sleep(0.1)
        
        # Save state every 10 queries
        if query_counter % 10 == 0:
            save_checkpoint(all_papers_state)
            
    return papers_data

def collect_citation_network(max_depth=2):
    all_papers = load_checkpoint()
    
    # Identify depth 0 papers we already have
    depth_0_papers = {k: v for k, v in all_papers.items() if v['depth'] == 0}
    
    if not depth_0_papers:
        print("\n=== Extracting Depth 0 (Root Symbolic Regression Papers) ===")
        depth_0_papers = fetch_symbolic_regression_papers()
        all_papers.update(depth_0_papers)
        save_checkpoint(all_papers)
    else:
        print(f"\nLoaded {len(depth_0_papers)} existing Depth 0 papers from checkpoint.")
    
    for current_depth in range(1, max_depth + 1):
        print(f"\n=== Extracting Depth {current_depth} ===")
        
        # We find what the previous layer was to track references
        previous_layer = {k: v for k, v in all_papers.items() if v['depth'] == current_depth - 1}
        
        next_ids_to_fetch = set()
        for p in previous_layer.values():
            for ref_id in p.get("referenced_works", []):
                if ref_id not in all_papers:
                    next_ids_to_fetch.add(ref_id)
        
        if not next_ids_to_fetch:
            print(f"\nNo new references to fetch at Depth {current_depth}. Moving on.")
            continue
            
        fetch_works_by_ids(next_ids_to_fetch, current_depth, all_papers)
        
    return pd.DataFrame(list(all_papers.values()))

if __name__ == "__main__":
    print(f"Starting Data Collection... (Email: {'OK' if EMAIL else 'Missing'}, API Key: {'OK' if API_KEY else 'Missing'})")
    df = collect_citation_network(max_depth=2)
    
    outfile = "symbolic_regression_papers_network_d2.csv"
    df.to_csv(outfile, index=False)
    print(f"\nData collection complete. Wrote {len(df)} total papers to {outfile}")
