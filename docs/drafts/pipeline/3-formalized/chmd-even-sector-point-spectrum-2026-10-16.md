# CHMD: the even primitive sector detects RH; the point spectrum above 1/2 is the ground state

- **ID:** chmd-even-sector-point-spectrum-2026-10-16
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), unconditional
- **Source:** CHMD route; continuation of chmd-odd-sector-criterion-2026-10-16; corpus inputs: `WeilOneSided.riemannHypothesis_iff_positiveOnEvenNonnegCone`, `zeta_W_eq_weilFullFunctional`, `WeilWorkPBAP.energy_paperSplitRealMixture`/`defect_paperSplitRealMixture`, `WeilOneSided.re_weilFullFunctional_eq`, `phiDoobInv`
- **Statement:** (1) `J1 = 1`, `J tanh = −tanh`, so `⟪w, tanh⟫ = 0` for even `w`; (2) the constant graph vector is null for the Weil bilinear form (`weilBilin q (constantLift 1) = 0` for every `q`), hence for even `p`: `weilForm p = sourceEnergy (p − 2⟪Sp,1⟫·constantLift 1)`; (3) Doob energy `≥ 0` on the even primitive sector ⟹ `Re W(g,g) ≥ 0` for every even real `C²_c` test `g`, hence for every even complex test (`Re W(f,f) = Re W(Re f, Re f) + Re W(Im f, Im f)`), hence RH by the even-cone criterion; (4) `RH ⟺ R ≤ ½ on the even primitive sector ⟺ no even primitive eigenvector above ½`; `¬RH ⟺ ∃ even primitive bound state`; odd bound states exist ⟺ even primitive bound states exist; (5) every eigenvector with `μ ≠ 1` is primitive, and `RH ⟺ (∀ μ ∈ (½,1]∖{1}, no eigenvector) ∧ (eigenspace at 1 = ℝ·1)`, also within the even sector.
- **Status:** STATUS MUST-1556. One leaf (`CHMDEvenSectorPointSpectrum`; 40 declarations), axioms propext/Classical.choice/Quot.sound; plain `lake env lean` audit clean; `lake build --old` green; wired; global lint clean of proof debt (remaining errors are other agents' unwired modules).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below = the Lean development)
- [x] 2 → 3  formalized: `weilForm_eq_sourceEnergy_evenPrimitivePart`, `re_weilFullFunctional_split`, `riemannHypothesis_iff_no_evenPrimitive_bound_state`, `riemannHypothesis_iff_point_spectrum_above_half`, `riemannHypothesis_iff_even_point_spectrum_above_half`
- [ ] 3 → 4  publication-ready

## Obstacle addressed
The corpus has odd and full Dirichlet–Poincaré criteria but no even one, so the even sector of the
arithmetic resolvent had no RH dictionary and the spectral criterion still carried the primitive
hyperplane as an external constraint. Two structural facts remove both: the constant graph vector
is `weilBilin`-null (so the mass constraint is absorbed into the Weil form itself: the Weil form of
an even vector is the energy of its primitive projection), and the real/imaginary splitting of the
Weil functional lifts real even positivity to the complex even cone. The point-spectrum statement
then no longer mentions any hyperplane: RH is exactly "the only bound state of `R` above the
essential threshold `½` is the ground state `1`, and it is simple".

## Paper proof
*Polar vectors.* `(J1)(x) = 1(−x) = 1`; `(J tanh)(x) = tanh(−x/2) = −tanh(x/2)` (a.e., via the
measure-preserving reflection). For even `w`: `⟪w, tanh⟫ = ⟪Jw, J tanh⟫ = −⟪w, tanh⟫`.

*Null constant vector.* With `C = constantLift 1 = Riesz(1)` and `SC = 1`:
`weilBilin q C = ⟪q, C⟫ − 2⟪Sq, 1⟫ + 2⟪Sq,1⟫‖1‖² − 2⟪Sq, τ⟫⟪1, τ⟫ = ⟪Sq,1⟫(1 − 2 + 1) − 0 = 0`,
using `⟪q, Riesz 1⟫ = ⟪Sq, 1⟫`, `‖1‖² = ½`, `⟪τ, 1⟫ = 0`.

*Even reduction.* For `p` with even source, `p₀ = p − 2⟪Sp,1⟫ C` has even primitive source, and
bilinearity plus nullity give `weilForm p = weilBilin p₀ p₀ = E(p₀) + 2⟪Sp₀,1⟫² − 2⟪Sp₀,τ⟫² = E(p₀)`.

*Even positivity ⟹ RH.* For even real `g ∈ C²_c`, `v = g/K` (K the Riemann kernel, even) is even,
`compactLift v` is even, and `Re W(g,g) = weilForm(compactLift v) = E(p₀) ≥ 0`. For a complex even
test `f`, the corpus mixture identities give `Re W(f,f) = Re W(Re f) + Re W(Im f) ≥ 0`, which is
`PositiveOnEvenNonnegCone Λ` term by term, hence RH.

*Point spectrum.* `⟪Rw, 1⟫ = ⟪w, R1⟫ = ⟪w, 1⟫`, so `Rw = μw` with `μ ≠ 1` forces `⟪w,1⟫ = 0`.
At `μ = 1`, `w − 2⟪w,1⟫·1` is a primitive eigenvector at `1`, hence zero under the no-primitive-
bound-state condition. The converse checks `μ = 1` and `μ ≠ 1` separately.

## Lean module (namespace `RHTower.CHMDPolar`)
`RHTower/CHMDEvenSectorPointSpectrum.lean` — `reflectMass_oneL`, `reflectMass_tanhL`,
`inner_tanhL_eq_zero_of_even`, `evenOp`, `evenSector`, `mem_evenSector`, `isClosed_evenSector`,
`resolventInvariant_evenSector`, `primitiveSector` (= `(ℝ ∙ oneL)ᗮ`), `mem_primitiveSector`,
`isClosed_primitiveSector`, `resolventInvariant_primitiveSector`, `evenPrimitiveSector`,
`mem_evenPrimitiveSector`, `isClosed_evenPrimitiveSector`, `resolventInvariant_evenPrimitiveSector`,
`weilBilin_smul_left`, `weilBilin_smul_right`, `weilBilin_constantLift_one`,
`weilBilin_constantLift_one_left`, `evenPrimitivePart`, `evenPrimitivePart_fst`,
`inner_evenPrimitivePart_oneL`, `evenPrimitivePart_fst_mem`, `weilForm_eq_sourceEnergy_evenPrimitivePart`,
`reflectMass_compactLift_fst_of_even`, `weilForm_compactLift_nonneg_of_even_energy`,
`re_W_ofReal_nonneg_of_even_energy`, `re_weilFullFunctional_split`,
`re_weilFullFunctional_nonneg_of_even_energy`, `sourceEnergy_nonneg_of_rh_evenPrimitive`,
`riemannHypothesis_of_evenPrimitive_energy`, `riemannHypothesis_iff_evenPrimitive_half_bound`,
`riemannHypothesis_iff_no_evenPrimitive_bound_state`, `not_riemannHypothesis_iff_exists_evenPrimitive_bound_state`,
`exists_odd_bound_state_iff_exists_evenPrimitive_bound_state`, `inner_oneL_eq_zero_of_eigenvector`,
`eq_smul_oneL_of_eigen_one`, `riemannHypothesis_iff_point_spectrum_above_half`,
`riemannHypothesis_iff_even_point_spectrum_above_half`.

## Big picture
- The CHMD spectral dictionary is now hyperplane-free: `σ(R) ⊆ [0,1]`, essential spectrum
  `⊆ [0,½]` with `½` attained, the point spectrum above `½` is finite-dimensional and locally
  finite, and RH ⟺ this point spectrum is `{1}` with the ground vector as its only eigenvector.
- Parity: the odd sector and the even primitive sector each detect RH; bound states of both
  parities exist simultaneously or not at all. Under `¬RH` the total primitive multiplicity is at
  most `2·#(off-line zeros)` (MUST-1553).

## Next conjectures
1. Lower Birman–Schwinger: from an off-line zero build an explicit graph vector of negative Weil
   form (corpus deep-zero detection), hence a bound state above `½` with an explicit eigenvalue
   lower bound.
2. Odd Birman–Schwinger with sharp constant (pairing `ρ ↔ ρ̄`).
3. Even sector: the even bound states are pole-free and primitive automatically for `μ ≠ 1`;
   identify the even bound states with pairs `(ρ, 1−ρ)` of off-line zeros via the zero-side
   parity of `paperFT`.
