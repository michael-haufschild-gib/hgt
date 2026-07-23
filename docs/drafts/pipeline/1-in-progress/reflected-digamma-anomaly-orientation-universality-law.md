# Reflected digamma anomaly orientation universality law

- **ID:** reflected-digamma-anomaly-orientation-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of reflected anomaly identity and strict horizontal digamma
  anti-monotonicity
- **Statement:** At every positive height, the imaginary reflected digamma anomaly is strictly
  decreasing across the open strip, odd under reflection about `1/2`, positive on the left
  half-strip, zero exactly on the critical line, and negative on the right half-strip.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: exact-file Lean passed; final axiom audit pending
- [ ] 3 → 4 publication-ready: post-proof literature audit complete; final audit pending

## Corpus inputs

- `ReflectedDigammaAnomaly.anomaly_im_eq_sub`
- `ReflectedDigammaAnomaly.verticalDigammaIm_strictAnti`
- `ReflectedDigammaAnomaly.anomaly_im_eq_zero_iff`

## Proof

`[PROVED HERE]` Write `v_t(σ) = Im ψ(σ+it)`.  The corpus proves that `v_t` is strictly decreasing
on the nonnegative real axis for every `t>0`, while the anomaly has imaginary part

`A_t(σ) = v_t(σ) - v_t(1-σ)`.

If `0<σ<τ<1`, then `v_t(τ)<v_t(σ)` and
`v_t(1-σ)<v_t(1-τ)`, so `A_t(τ)<A_t(σ)`.  Substitution gives
`A_t(1-σ)=-A_t(σ)`.  Since the existing zero theorem gives `A_t(1/2)=0`, strict decrease yields
the exact positive/zero/negative trichotomy.  No computation is used.

## Lean certificate

- Module:
  `GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomalyOrientationUniversalityLaw`
- Main theorem:
  `ReflectedDigammaAnomaly.reflectedDigammaAnomaly_orientationUniversality`
- Exact source check:
  `lake env lean GaloisForLFunctions/HTGeometry/ReflectedDigammaAnomalyOrientationUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Imported by `GaloisForLFunctions/HTGeometry.lean`.

## Novelty protocol

No literature search before exact Lean proof.

## Post-proof literature audit

Performed only after exact Lean source check passed.

- Dipierro--Ros-Oton--Valdinoci--Weidner,
  *The Neumann problem for the fractional Laplacian: optimal regularity via the Mellin transform*
  ([preprint PDF](https://borowiecki.dev/pdf/2510.13340)), uses positivity and an upper bound for
  `Im ψ(x+iy)` in a Mellin boundary argument, not strict horizontal anti-monotonicity of the
  reflected sum or its half-strip sign classification.
- Ismail--Muldoon, *Inequalities and monotonicity properties for gamma and q-gamma functions*
  ([arXiv:1301.1749](https://arxiv.org/abs/1301.1749)), studies real and selected complex
  Gamma-function bounds, but the inspected scope does not state the reflected-anomaly orientation
  theorem.
- Joubat--Sandeu--Prygarin, *Pole decomposition of BFKL eigenvalue at zero conformal spin and the
  real part of digamma function*
  ([DOI:10.1016/j.physletb.2023.138319](https://doi.org/10.1016/j.physletb.2023.138319)),
  records the critical-line reflection formula and the explicit value of
  `Im ψ(1/2+it)`, not the strict open-strip orientation of
  `Im(ψ(σ+it)+ψ(1-σ-it))`.
- Kalinin, *A half-shift reflection identity for the digamma function*
  ([arXiv:2510.00012](https://arxiv.org/abs/2510.00012)), proves a different half-shift integral
  identity.

Targeted searches for the exact reflected sum, its imaginary-part monotonicity in `σ`, and its
positive/zero/negative half-strip trichotomy found no matching theorem.  Door 2 remains open rather
than claimed closed.

## Log

- 2026-07-23 — Whole-corpus terminal scan exposed that the existing reflected-anomaly endpoint
  recorded only the zero locus, while its strict anti-monotonicity input forces a full oriented
  strip law.
- 2026-07-23 — Main theorem exact-checked warning-free, wired into HTGeometry umbrella, and
  post-proof primary-source collision audit found no exact match.
