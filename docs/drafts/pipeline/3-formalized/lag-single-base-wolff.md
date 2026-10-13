# Single-base lag samples can vanish identically at a non-attained top

- **ID:** lag-single-base-wolff
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** JAS goal loop row 187
- **Statement:** For `ℓ > 0` and `Θ > 0` there is a countable, injective, locally finite family `ρ_i` with positive summable weights, real parts in `(½, ½+Θ)` with non-attained supremum `½+Θ`, and `Σ_i c_i e^{mℓ(ρ_i−½)} = 0` for every `m ≥ 1`.

## Goal
Decide whether zero-side structure (positivity of weights, summability, local finiteness) can close the single-base lag law at a non-attained top. It cannot.

## Gates
- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven (Wolff disc decomposition with positive weights)
- [x] 2 → 3 formalized:
  - `GaloisForLFunctions.HTGeometry.PositiveWolffMeasure.exists_positive_wolff_annulus`
  - `RHTower.exists_positive_lag_configuration_vanishing_progression`
  - `RHTower.exists_symmetric_lag_configuration_vanishing_samples` (MUST-1373, row 189). With the full symmetric quadruple, every two-sided sample `m ≠ 0` vanishes, so even single-base Toeplitz positive-definiteness is blind.
  - `lake build --old` green; axioms are only propext, Classical.choice and Quot.sound.

## Approach
1. The annulus `1 < |z| < e^{Θℓ}` is rotation invariant, so `∫ z^k = 0` for every `k ≥ 1`.
2. Discs satisfy the mean value identity `∫_D z^k = πρ²a^k`.
3. Besicovitch gives a disjoint disc cover of almost all of the annulus. The centres carry weights `πρ²` and accumulate at the outer circle.
4. The lift `ρ = ½ + (log x + 2πiN_x)/ℓ` turns the moments `x^m` into lag samples and makes the ordinates locally finite.

## No-go closure
- **Killed conjecture:** zero-side inputs exclude non-attained tops along a progression. These inputs are positivity of the weights, summability, symmetry, zero counting and density.
  - It is false for the one-sided law: the corpus already owns this as `chainSum_neg`.
  - It is false for the two-sided law, by the theorem above. The samples are identically zero, so they are bounded on both sides.
- **Strongest positive survivor:** the corpus shadow law (`riemannHypothesis_of_forall_abs_le_of_clean_shadows`) together with the Baire law (MUST-1363) is sharp.
  - A Wolff configuration has every shadow unclean, since its nodes are dense in the annulus.
  - The non-meagre threshold cannot be lowered to a single spacing. Paper: the corpus chain extends to any countable family of spacings via simultaneous Dirichlet approximation.
- **New insight:** single-base receivers need arithmetic (prime-side) input. A producer for lag families must deliver bounds on a non-meagre set of spacings.
- **Diagnosis (paper, competitor-based design only; the diagonal-Bochner capstone `riemannHypothesis_iff_jasDressedPSD_one` already removes the side condition):** in the quasi-RH chain exclusion, quasi-RH enters only through a Perron step.
  - The step needs shifted twisted prime sums with power saving, at heights `γ − γ₀` of the heavy zeros.
  - Vinogradov–Korobov saves only `exp(−c log x/(log h)^{2/3})` there.
  - This fails on chains near the VK boundary. For a zero-free width `c/(log h)^κ`, farther zeros above height `γ₀^{K}` with `K > (3/2)^{1/κ}` escape.
  - The arithmetic obstruction is a resonant triple: off-line zeros near `Re s = 1` at heights approximately equal to differences `γ − γ₀` of heavy ordinates.
- **Status:** closed in Lean as above.
