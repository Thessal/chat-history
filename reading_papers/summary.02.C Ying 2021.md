# Do Transformers Really Perform Bad for Graph Representation?
**Authors**: Chengxuan Ying, Tianle Cai, Shengjie Luo, Shuxin Zheng, Guolin Ke, Di He, Yanming Shen, Tie-Yan Liu (NeurIPS 2021)

## General Facts
* Standard Transformers struggle with graph-level prediction compared to mainstream GNNs.
* Self-attention naturally calculates semantic similarity without explicitly utilizing topological structure.
* Virtual node heuristics conventionally improve GNN models.

## Methods
* Centrality Encoding: Adds learnable degree embeddings to input nodes.
* Spatial Encoding: Incorporates shortest path distance (SPD) as a bias term in softmax attention.
* Edge Encoding: Incorporates edge characteristics via an average of dot-products along the shortest path as a bias term.
* Applies a virtual node [VNode] natively leveraging self-attention for full graph readout.

## Claims
* Graphormer mathematically encapsulates AGGREGATE and COMBINE steps of common GNNs.
* The spatial encoding allows the model to exceed the expressive power of the 1-Weisfeiler-Lehman test.
* Classic message passing architectures function effectively as special cases of Graphormer.
* Eliminates the over-smoothing problem inherent to deep GNN layers.

## Novelty
* First Transformer to achieve state-of-the-art results directly on OGB Large-Scale Challenge graph representations.
* Custom structural encodings gracefully inject topological data directly into self-attention heads.
