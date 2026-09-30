# The Bohr–ζ law and the ζ-mass deficit law

- **ID:** weil-zeta-mass-deficit-law
- **Stage:** 3-formalized (2026-09-29)
- **Type:** THEOREM (paper + Lean)
- **Source:** `1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`, L155. Builds on L151–L154.
- **Statement.**
  - **Setting.** An odd Weil function `Φ` with `Γ̃ + 1/(s−1) − Σ lam(n)n^{−s} = Φ` on `Re s > 1`, and `J` the holomorphic continuation to `Re τ > 0` of the Laplace transform of its thin-strip defect.
  - **Exact Bohr–ζ law** (no ζ-mass hypothesis). For every `n ≥ 1`, `lim_{ε→0⁺} εJ(ε+in)` exists and
    `(1⋆(lam−Λ))(n) + 2β = 2π · lim_{ε→0⁺} εJ(ε+in)`.
  - **For spectral measures.** Here `J(τ) = −∫(c/π)(atomLaplace(½+it,τ) + atomLaplace(½−it,τ))dν`.
  - **Deficit law.** If `δ·∫|c||ζ(½+it)|e^{−δt}dν ≤ A` for all small `δ > 0`, then
    - `‖(1⋆(lam−Λ))(n) + 2β‖ ≤ 6(n+1)A` for every `n ≥ 1`;
    - `|lam(p) − log p| ≤ 6(p+3)A` for every prime `p`.
- **Reading.**
  - The arithmetic distance of a represented completion from `Λ` is bounded linearly by its Abel-damped ζ-mass density.
  - `A = 0` recovers sublinear rigidity (L152).
  - Consequence for producers: a Weil-positive system with `lam(p) ≠ log p` carries Abel-damped ζ-mass density at least `|lam(p) − log p|/(6(p+3))`.
  - The damped mass is affine on the cone, so the density `A(lam) = limsup δM(δ)` is a convex functional on `W`. It vanishes only at `Λ` and dominates the weighted sup-norm `sup_p |lam(p) − log p|/(6(p+3))`.
- **Proof.**
  - The full-filter residue limits of `(t−in₀)K(t)` at `in₀` exist and are explicit: `a₁/(2π) + c` at `n₀ = 0`, and `(a_{n₀+1}−a_{n₀})/(2π)` for `n₀ ≥ 1`.
  - The horizontal ray reads them off.
  - `εJ(ε) → 0` always holds, since the damping rate on the real axis is `1`.
  - Telescoping gives the exact law, and the ray bound `‖εJ(ε+im)‖ ≤ (3/π)(m+1)·δM(δ)` gives the deficit law.
  - For primes: `(1⋆w)(p) − (1⋆w)(1) = w(p)`.

## Lean
- **Module** `formal/GaloisForLFunctions/RHTower/WeilDefectBohrZetaLaw.lean`, wired after `SpectralMeasureZetaMassRigidity`.
- **Declarations:**
  - `tendsto_sub_mul_defect_residue`;
  - `tendsto_mul_weilLaplace_bohr` (abstract exact law);
  - `tendsto_mul_spectralMeasureLaplace_bohr`;
  - `norm_crystallineCoeff_add_le_of_dampedZetaMass`;
  - `abs_sub_vonMangoldt_le_of_dampedZetaMass`.
- **Axioms:** `propext, Classical.choice, Quot.sound`.

## Log
- 2026-09-29 — paper and Lean closed on the same day.
