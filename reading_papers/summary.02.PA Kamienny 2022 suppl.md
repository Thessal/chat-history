# End-to-end Symbolic Regression with Transformers (Supplementary)
**Authors**: Pierre-Alexandre Kamienny, Stéphane d'Ascoli, Guillaume Lample, François Charton (NeurIPS 2022)

## General Facts
* Transformers are notoriously sensitive to absolute mathematical scales during inference.
* Beam-search actively harms generation by creating a lack of solution diversity.

## Methods
* Generating synthetic evaluation data heavily utilizes Gaussian clusters combined with Haar rotations.
* Dynamic dataset bagging safely partitions large evaluation inputs overcoming strict memory constraints.
* Inputs are rigorously whitened, scaling parameters directly before sequence generation.

## Claims
* Normalizing variances successfully prevents out-of-domain failures when extrapolating data bounds.
* The sequential embedder successfully condenses continuous multi-dimensional input without sequence explosions.
* Scaling is an absolute necessity for achieving competitive robustness against multiplicative target noise.

## Novelty
* Validates dataset whitening as a functional stabilizer for generic deep symbolic regressions.
* Un-scaling sequentially predicted constants provides perfectly accurate final parameters.
