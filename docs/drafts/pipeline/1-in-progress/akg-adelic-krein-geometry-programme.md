# Adelic Krein Geometry (AKG) programme

- **ID:** akg
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-3010/obstacles-summary.md §2.6
- **Statement:** Indefinite (finite negative index) harmonic analysis on `Aff(ℚ)` and its adelic completion: index calculus, zero-or-infinity laws, Pontryagin extensions of Weil's correlation, local–global signature calculus, conformal symmetry.

## Goal
Develop the field asked for in §2.6: answer its six questions as theorems or sharp no-gos with positive survivors, build its tools in Lean under `formal/GaloisForLFunctions/AdelicKreinGeometry/`.

## Gates
- [x] 0 → 1  README first draft; objects and questions fixed
- [ ] 1 → 2  paper proofs of the pillar theorems A–E
- [ ] 2 → 3  Lean modules, each checked with `lake --old env lean`, wired into `AdelicKreinGeometry.lean`

## Approach (pillars and status)
- A. Index calculus on groups (witness complement, escape ⇒ κ ∈ {0,∞}, pullback, extension by zero): paper proof done (see below); Lean pending.
- B. Hecke-supported states on Aff(ℚ) have κ ∈ {0,∞}; Kakutani wall is an index wall: paper proof done; Lean pending.
- C. Pontryagin extensions of Weil's correlation: minimum = blind; Hecke-supported finite ⇒ PD ⇒ RH; no finite-index Hecke-supported state with Weil dilation part and integer successor: paper proof done; Lean pending.
- D. Signature calculus: shared polar hyperplane, gluing bound, counterexample. [A6 finite sieve is formalized](../3-formalized/matched-prime-form-hodge-index-uniform-in-the-sieve.md), with a horizon independent of the sieve; transfer to the complete Weil form remains open.
- E. Conformal symmetry: PD no-go; stable kernels; log endpoint: paper sketch.

## Paper proofs

**A1 (witness complement).** κ(k) = m < ∞ attained on x. If c on a family y satisfies Σ_b k(x_a⁻¹y_b)c_b = 0 ∀a and Q_y(c) < 0, then on x ⊔ y the span of an m-dim negative subspace of Q_x and c is negative of dim m+1 (cross terms vanish). Contradiction.

**A2 (escape).** If for all finite x, y there is t with k(x_a⁻¹ t y_b) = 0, then κ < ∞ ⇒ κ = 0: Gram(t·y) = Gram(y) and every coefficient vector on t·y is witness-orthogonal.

**B (Hecke escape).** For x_a⁻¹ t_{1/P} y_b with P prime not dividing any numerator/denominator: shift = slope(x_a)⁻¹(1/P + shift(y_b) − shift(x_a)) has v_P = −1 and den(slope) is prime to P, so den(slope)·shift ∉ ℤ.

**C.** Restriction lowers κ; slope pullback is surjective; APD `isPosDefOnGroup_heckeState_iff`, `riemannHypothesis_iff_exists_affine_posDef`, `normSq_dilation_le`.

## Log
- 2026-10-30 — created; README first draft written.
