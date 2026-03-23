# End-to-end Symbolic Regression with Transformers
**Authors**: Pierre-Alexandre Kamienny, Stéphane d'Ascoli, Guillaume Lample, François Charton (NeurIPS 2022)

## General Facts
* Machine learning models generally overfits and exhibits poor extrapolation.

## Methods 
* Transformers predict expressions alongside explicit numerical constants.
* Symbolic-numeric vocabulary with transformer, and additional optimization using BFGS.
* Inputs are scaled.
* Inference time bagging for diverse solution, rather than beam search.

## Claims
* End-to-end prediction outperforms two-step skeleton predictor methods.
* Skeleton prediction is an ill-posed problem because without constants, the search space for the solver is highly non-convex and prone to spurious local optima.
* Embedder is used to fit in long data into limited context by linearly transforming datapoints into tensors.
* Attention head analysis shows that the model learns Fourier-like rhythmic signal extraction patterns.

## Novelty
* Bypasses skeleton generation using symbolic-numeric vocabulary.
* Attention head analysis proves transformer's ability to natively extract functional and geometric properties through individual self-attention heads automatically.
