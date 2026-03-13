import argparse
import os
import pandas as pd
import networkx as nx

def calculate_cd_index(G, f):
    """
    Calculate the local CD (Consolidating/Disruptive) index for a focal node f.
    This uses the Wu, Wang, Evans (2019) formulation:
    CD = (n_I - n_J) / (n_I + n_J + n_K)
    
    Assuming graph G has directed edges: Citing Paper -> Cited Paper
    """
    try:
        # B: set of backward references (papers cited by f)
        B = set(G.successors(f))
        # F: set of forward citations (papers that cite f)
        F = set(G.predecessors(f))
        
        if not F and not B:
            return -999, -999, -999, -999
            
        n_I = 0
        n_K = 0
        n_J = 0
        
        # Find all papers in the network that cite at least one paper in B
        papers_citing_B = set()
        for b in B:
            papers_citing_B.update(G.predecessors(b))
            
        # Classify citing papers in F
        for p in F:
            # Check if p cites any paper in B
            citations_of_p = set(G.successors(p))
            if citations_of_p.intersection(B):
                n_J += 1  # CORRECTED: Cites f AND B
            else:
                n_I += 1  # Cites f ONLY
                
        # Count n_K: papers that cite B, but do NOT cite f (and are not f itself)
        for p in papers_citing_B:
            if p != f and p not in F:
                n_K += 1  # CORRECTED: Cites B ONLY
                
        denominator = n_I + n_J + n_K
        if denominator == 0:
            return -999, -999, -999, -999
            
        return (n_I - n_J) / denominator, n_I, n_J, n_K
    except Exception as e:
        return -999, -999, -999, -999

def main():
    parser = argparse.ArgumentParser(description="Calculate network features from citation graph")
    parser.add_argument("--graphml", default="citation_network.graphml", help="Path to input GraphML file")
    parser.add_argument("--nodelist", default="nodelist.csv", help="Path to input nodelist CSV")
    parser.add_argument("--output", default="nodelist_networkfeatures.csv", help="Path to output CSV")
    args = parser.parse_args()

    print(f"Loading graph from {args.graphml} ...")
    if not os.path.exists(args.graphml):
        raise FileNotFoundError(f"Could not find {args.graphml}")
        
    # networkx reads GraphML
    G = nx.read_graphml(args.graphml)
    print(f"Graph loaded with {G.number_of_nodes()} nodes and {G.number_of_edges()} edges.")

    print(f"Loading nodelist from {args.nodelist} ...")
    df = pd.read_csv(args.nodelist)

    print("Calculating In-Degree and Out-Degree ...")
    # In-degree: number of incoming edges (citations to the paper)
    # Out-degree: number of outgoing edges (references made by the paper)
    in_degrees = dict(G.in_degree())
    out_degrees = dict(G.out_degree())
    
    df['indegree'] = df['id'].map(in_degrees)
    df['outdegree'] = df['id'].map(out_degrees)

    # print("Calculating Betweenness Centrality (this may take a while depending on graph size) ...")
    # # Using endpoints=False and normalized=True by default
    # betweenness = nx.betweenness_centrality(G)
    # df['betweenness_centrality'] = df['id'].map(betweenness)

    print("Calculating CD Index for each node ...")
    cd_indices = {}
    n_Is = {}
    n_Js = {}
    n_Ks = {}
    for i, node in enumerate(G.nodes()):
        cd_indices[node], n_Is[node], n_Js[node], n_Ks[node] = calculate_cd_index(G, node)
        if (i+1) % 1000 == 0:
            print(f"Processed {i+1} nodes for CD index...")
            
    df['cd_index'] = df['id'].map(cd_indices)
    df['n_I'] = df['id'].map(n_Is)
    df['n_J'] = df['id'].map(n_Js)
    df['n_K'] = df['id'].map(n_Ks)

    # ---------------------------------------------------------------------
    # OPTIONAL: Additional useful network features to consider
    # ---------------------------------------------------------------------
    
    print("Calculating PageRank ...")
    pagerank = nx.pagerank(G, alpha=0.85)
    df['pagerank'] = df['id'].map(pagerank)
    
    print("Calculating HITS (Hubs and Authorities) ...")
    try:
        hubs, authorities = nx.hits(G, max_iter=100)
        df['hub_score'] = df['id'].map(hubs)
        df['authority_score'] = df['id'].map(authorities)
    except nx.PowerIterationFailedConvergence:
        print("HITS failed to converge.")

    print("Calculating Clustering Coefficient ...")
    # I don't mean to count circular citations, so I use G.to_undirected()
    clustering = nx.clustering(G.to_undirected())
    df['clustering_coefficient'] = df['id'].map(clustering)

    print(f"Saving new nodelist to {args.output} ...")
    df.to_csv(args.output, index=False)
    print("Done!")

if __name__ == "__main__":
    main()
