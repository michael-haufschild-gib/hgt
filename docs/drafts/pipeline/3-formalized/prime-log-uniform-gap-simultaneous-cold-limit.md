# Prime-log uniform-gap simultaneous cold limit

- **ID:** prime-log-uniform-gap-simultaneous-cold-limit
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [BRIDGE] Low-temperature Lehmann expansion for gapped quantum response (Essler--Konik, arXiv:0907.0779); KMS spectral detailed balance (Jain--Gaspard, arXiv:2408.09419); existing prime-log Hermitian Gibbs carrier
- **Statement:** The uniform prime energy gap `log 2` gives a finite-subsystem-independent Boltzmann error bound, so the Hermitian Gibbs response converges to the universal prime carrier in one simultaneous cold and thermodynamic limit; this limit selects exactly the all-positive orientation.

## Goal

Strengthen the existing iterated zero-temperature-then-thermodynamic selector by removing its order-of-limits freedom.  The useful corpus gain is quantitative and direct: every finite prime subsystem shares one cold cutoff because every prime-log excitation has energy at least `log 2` and the dyadic prime weights have finite total mass.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted build green, axiom audit clean
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

For `Im z > 0`, expand the difference between the Gibbs carrier and the directed carrier as the reverse-transition sum.  Bound every resolvent by `(Im z)⁻¹`, every Boltzmann factor by `exp (-β log 2)`, and every finite weight sum by the existing summable total prime mass.  The resulting bound is uniform in the finite prime set.  Combine it with the existing thermodynamic convergence of the directed carrier.  Package the result as a cofinal two-parameter limit and prove uniqueness, then reuse the existing orientation nonnegativity characterization.

## Proof

[PROVED HERE] For every prime `p`, `log 2 ≤ log p`.  For `β ≥ 0`, monotonicity of the exponential gives `exp (-β log p) ≤ exp (-β log 2)`.  If `Im z > 0`, the imaginary part of `log p + z` is `Im z`, hence `‖(log p + z)⁻¹‖ ≤ (Im z)⁻¹`.  Expanding the reverse-transition sum, applying the triangle inequality, and bounding the finite weight sum by the existing summable total mass gives

`‖G_{P,β}(z) - H_P(z)‖ ≤ exp (-β log 2) (Im z)⁻¹ ∑'_p ‖w_p‖`.

The right side is independent of `P` and tends to zero as `β → ∞`.  The existing directed finite-prime convergence `H_P(z) → H(z)` then yields `G_{P,β}(z) → H(z)` along `atTop` on `Finset primes × ℝ`.  Uniqueness of this joint limit and the existing imaginary-part orientation characterization select exactly the all-positive orientation.

Lean certificates are in `formal/GaloisForLFunctions/HTGeometry/PrimeLogGibbsJointLimit.lean`: `finitePrimeLogHermitianGibbsCarrier_sub_bound`, `finitePrimeLogHermitianGibbsCarrier_tendsto_joint`, `universalPrimeOrientationHermitianGibbsJointLimit_iff`, and `universalPrimeOrientationHermitianGibbsJointLimit_iff_coldLimit`.

## Log

- 2026-07-14 — Created in 1-in-progress after corpus search found no existing simultaneous prime Gibbs limit.  The `log 2` prime lower-bound lemmas already present in `RHTower` are candidates for reuse or local generalization.
- 2026-07-14 — Formalized the uniform error estimate and genuine product-directed joint limit.  Target build passed 8,552 jobs; full `GaloisForLFunctions.HTGeometry` build passed 9,120 jobs; axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`; formal lint passed.
