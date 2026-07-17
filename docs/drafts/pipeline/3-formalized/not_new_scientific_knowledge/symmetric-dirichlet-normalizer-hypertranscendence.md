# Multiclass symmetric Dirichlet normalization is hypertranscendental

- **ID:** `symmetric-dirichlet-normalizer-hypertranscendence`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** M. Sensoy, L. Kaplan, and M. Kandemir, *Evidential Deep Learning to Quantify Classification Uncertainty*, NeurIPS 2018 / arXiv:1806.01768; T. Tvedebrink, P. S. Eriksen, and N. Morling, *The multivariate Dirichlet-multinomial distribution and its application in forensic genetics*, arXiv:1406.6508; Dirichlet-multinomial sequencing applications in `DRIMSeq` and whole-genome error modeling
- **Statement:** For every positive category count `K`, the symmetric Dirichlet normalizer `Gamma(Kz)/Gamma(z)^K` is DA exactly when `K=1`, and HT exactly when `K>1`.

## Goal

Turn the exact Gamma normalization shared by evidential machine learning and genomic/genetic
Dirichlet-multinomial models into a general HTGeometry theorem.  The result must classify the
normalization observable itself, not make claims about neural-network training or biological
evolution.

## Gates

- [x] 0 → 1 in-progress: exact Dirichlet normalizer located in primary AI and genomics/genetics sources
- [x] 1 → 2 fully-proven: Gauss orbit charges and exact category-count dichotomy proved
- [x] 2 → 3 formalized: exact module build, direct file check, and axiom audit pass
- [ ] 3 → 4 publication-ready: application note not yet written

## Source relation

For a Dirichlet density on `K` categories,

`f(p;alpha)=Gamma(sum alpha_i)/prod_i Gamma(alpha_i)
              * prod_i p_i^(alpha_i-1)`.

Sensoy--Kaplan--Kandemir use this density as the predictive distribution of an evidential neural
classifier.  Dirichlet-multinomial models use the same normalization in forensic genetics,
RNA-sequencing, whole-genome error models, and other overdispersed genomic counts.

On the symmetric concentration slice `alpha_i=z`, the concentration-dependent normalizer is

`N_K(z)=Gamma(Kz)/Gamma(z)^K`.

## Exact positive statement

Gauss multiplication refines the numerator into shifts `k/K`, `0 <= k < K`.  After dividing by
`Gamma(z)^K`, the zero orbit has charge `1-K`, while every nonzero fractional orbit has charge one.
For `K>1`, the `1/K` orbit is separated from every other chosen representative and therefore forces
HT.  For `K=1`, the normalizer is exactly one.

Consequently, for every `K>0`,

`DA(N_K) iff K=1`, and `HT(N_K) iff 1<K`.

This is the nontrivial positive classification: multiclass normalization itself creates an
uncancellable fractional Gamma-orbit structure.  The scalar-aware finite-circuit corollary adds
source extraction: learned rational-function weights and offsets are free, but any exact finite
circuit for the multiclass normalizer must still contain an HT non-scalar atom.

## Corpus value

The theorem directly applies the general positive-integer rescaling API to a family not previously
represented in the corpus.  It adds a parameter-uniform orbit-charge construction and an exact
degenerate-versus-multiclass boundary.  The same theorem serves AI uncertainty models and genomic
count models without changing the mathematics.

## Lean certificate

Module: `GaloisForLFunctions.HTGeometry.SymmetricDirichletNormalizerBoundary`

- `symmetricDirichletNormalizerMero_normalForm`
- `hypertranscendentalOver_symmetricDirichletNormalizerMero`
- `symmetricDirichletNormalizerMero_one`
- `differentialAlgebraicOver_symmetricDirichletNormalizerMero_iff_one`
- `hypertranscendentalOver_symmetricDirichletNormalizerMero_iff_multiclass`
- `exists_hypertranscendental_atom_of_symmetricDirichletNormalizerCircuit`

All audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Limits

The theorem concerns the symmetric concentration slice.  It does not assert that a trained neural
network is HT, that optimization dynamics are HT, that genomic time evolution is HT, or that every
asymmetric Dirichlet normalizer has the same selector.  It classifies the exact normalization
observable as a function of common concentration.

## RH pressure test

The result strengthens the general HT corpus and supplies a clean example where finite category
count creates multiple fractional archimedean orbits.  For RH work it reinforces the rule that
normalization factors must be reduced orbitwise before searching for arithmetic content.  It does
not close any current `RHTower` source, positivity, zero-free, or sign hypothesis.

## Log

- 2026-07-17 — AI/genomics/genetics Dirichlet normalization extracted; exact multiclass HT and
  one-category DA boundary formalized and verified.
