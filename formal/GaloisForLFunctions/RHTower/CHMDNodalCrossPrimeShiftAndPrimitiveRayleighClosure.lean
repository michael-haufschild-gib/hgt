import GaloisForLFunctions.RHTower.CHMDEigenvectorNodalLobeEnergiesAndPrimitiveLobeBounds

/-!
# Nodal-Cross vs. Prime-Shift Closure, Odd Half-Mass Lobe Laws, and Primitive-Contraction Rayleigh Identities

This module closes the coupled `CHMD` target on `SourceGraph` by unifying the primitive-contraction
nodal bounds of `CHMDSpectralBesselAndPrimitiveContractionNodalBounds`, the stationary vs.
prime-shift decomposition of `CHMDStationaryNodalDecompositionAndPrimeShiftPositivity`, the
resolvent nodal polarization laws of `CHMDStationaryResolventDictionaryAndNodalPolarization`, and
the individual nodal-lobe energy identities of `CHMDEigenvectorNodalLobeEnergiesAndPrimitiveLobeBounds`:

1. **Bilateral Stationary + Prime-Shift Reinforcement in Primitive-Contraction Nodal Bounds**:
   - `neg_four_sourcePair_posGraph_negGraph_eq_stationary_add_primeShift`:
     `-4 * sourcePair (posGraph p) (negGraph p) = -4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ + 4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`,
     where both summands on the right-hand side are nonnegative (`≥ 0`), and the stationary cross-jump
     summand is strictly positive (`> 0`) whenever `posGraph p ≠ 0` and `negGraph p ≠ 0`.
   - `eigenvector_stationary_and_primeShift_nodal_cross_le_of_primGraph_absGraph_rayleigh_le` and
     `eigenvector_stationary_and_primeShift_nodal_cross_le_spectral_gap_mul_oneL_sq`:
     both the stationary Beurling–Deny cross-jump penalty and the prime-shift cross-jump term
     `4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ` reinforce the
     spectral-gap term `((ν - μ_max) / (ν * μ_max)) * ‖p.val.fst‖ ^ 2` with positive signs.
   - `eigenvalue_le_of_oneL_defect_le_neg_four_sourcePair` and
     `eigenvalue_lt_of_primitive_oneL_defect_le_four_primeShift`:
     for any nonzero eigenvector `resolvent v = ν • v` (`0 < ν`), if the primitive `oneL`-defect
     `((1 - μ_max) / μ_max) * (2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2)` is bounded by
     `-4 * sourcePair (posGraph p) (negGraph p)`, then `ν ≤ μ_max`; if `v` is primitive (`⟪v, oneL⟫_ℝ = 0`)
     and the `oneL`-defect is bounded by `4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`
     alone, then the strict positivity of the stationary cross-jump forces the strict upper bound
     **`ν < μ_max`**.

2. **Three-Term Nonnegative Nodal-Lobe Decomposition**:
   - `posGraph_three_term_nonneg_decomposition_of_eigenvector` and
     `negGraph_three_term_nonneg_decomposition_of_eigenvector`:
     for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
     `‖(posGraph q).val.snd‖ ^ 2 - ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ + ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ = ((1 - μ) / μ) * ‖(posGraph q).val.fst‖ ^ 2`
     (and symmetrically for `negGraph q`), where all three left-hand terms are nonnegative.

3. **Odd-Sector Exact Half-Mass Lobe Laws**:
   - `norm_posGraph_and_negGraph_snd_sq_of_odd`: for any odd `p : SourceGraph` (`reflectGraph p = -p`),
     `‖(posGraph p).val.snd‖ ^ 2 = ‖(negGraph p).val.snd‖ ^ 2 = (1 / 2) * ‖p.val.snd‖ ^ 2 + sourcePair (posGraph p) (negGraph p)`.
   - `odd_eigenvector_lobe_energy_and_snd_sq`: for any odd eigenvector `resolvent w = μ • w`
     (`μ ≠ 0`, `reflectMass w = -w`) with `q = rieszLift w`,
     `sourceEnergy (posGraph q) = sourceEnergy (negGraph q) = ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q)`
     and
     `‖(posGraph q).val.snd‖ ^ 2 = ‖(negGraph q).val.snd‖ ^ 2 = ((1 - μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q)`.

4. **Universal Primitive-Contraction Resolvent Polarization and Rayleigh Excess**:
   - `inner_resolvent_primGraph_absGraph_sub_self`: for every `p : SourceGraph`,
     `⟪resolvent (primGraph (absGraph p)).val.fst, (primGraph (absGraph p)).val.fst⟫_ℝ - ⟪resolvent p.val.fst, p.val.fst⟫_ℝ = 4 * ⟪resolvent (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ - 2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2`.
   - `inner_resolvent_primGraph_posGraph_negGraph_eq_of_primitive`: for primitive `p`,
     `⟪resolvent (primGraph (posGraph p)).val.fst, (primGraph (negGraph p)).val.fst⟫_ℝ = ⟪resolvent (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ - (1 / 2) * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2`.
   - `eigenvector_primGraph_absGraph_rayleigh_excess`: for any eigenvector `resolvent v = ν • v`
     with `p = rieszLift v`,
     `⟪resolvent (primGraph (absGraph p)).val.fst, (primGraph (absGraph p)).val.fst⟫_ℝ - ν * ‖(primGraph (absGraph p)).val.fst‖ ^ 2 = 4 * ⟪resolvent (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ - 2 * (1 - ν) * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2`.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump CHMDTranslation ThetaSourceWard

/-! ## Section 1: Bilateral Stationary + Prime-Shift Decomposition and Eigenvalue Upper Bounds -/

/-- The cross-jump penalty `-sourcePair (posGraph p) (negGraph p)` decomposes into the sum of two
nonnegative terms: the stationary cross-jump penalty
`-⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ` and the
opposite-sign prime-shift pairing `⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`. -/
theorem neg_sourcePair_posGraph_negGraph_eq_stationary_add_primeShift (p : SourceGraph) :
    -sourcePair (posGraph p) (negGraph p) =
      -⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ +
        ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  have h := sourcePair_posGraph_negGraph_eq_stationary_sub_primeShift p
  linarith

/-- Four times the cross-jump penalty decomposes into four times the stationary cross-jump penalty
plus four times the prime-shift cross-jump pairing. -/
theorem neg_four_sourcePair_posGraph_negGraph_eq_stationary_add_primeShift (p : SourceGraph) :
    -4 * sourcePair (posGraph p) (negGraph p) =
      -4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ +
        4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  have h := sourcePair_posGraph_negGraph_eq_stationary_sub_primeShift p
  linarith

/-- Both components of `-sourcePair (posGraph p) (negGraph p)` are nonnegative and each is bounded
above by `-sourcePair (posGraph p) (negGraph p)`. -/
theorem stationary_and_primeShift_le_neg_sourcePair_posGraph_negGraph (p : SourceGraph) :
    0 ≤ -⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ ∧
      0 ≤ ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ∧
      -⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ ≤
        -sourcePair (posGraph p) (negGraph p) ∧
      ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ≤
        -sourcePair (posGraph p) (negGraph p) := by
  have hstat : 0 ≤ -⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ :=
    neg_nonneg.mpr (inner_fullGroundEquiv_posGraph_negGraph_snd_nonpos p)
  have hprime : 0 ≤ ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ :=
    inner_primeShiftOperator_posGraph_negGraph_nonneg p
  have hdecomp := neg_sourcePair_posGraph_negGraph_eq_stationary_add_primeShift p
  exact ⟨hstat, hprime, by linarith, by linarith⟩

/-- Whenever `p : SourceGraph` changes sign (`posGraph p ≠ 0` and `negGraph p ≠ 0`), the stationary
cross-jump penalty is strictly positive, so `-sourcePair (posGraph p) (negGraph p)` strictly exceeds
the prime-shift cross term `⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`. -/
theorem primeShift_lt_neg_sourcePair_posGraph_negGraph_of_ne_zero {p : SourceGraph}
    (hp_pos : posGraph p ≠ 0) (hp_neg : negGraph p ≠ 0) :
    ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ <
      -sourcePair (posGraph p) (negGraph p) := by
  have hstat := inner_fullGroundEquiv_posGraph_negGraph_snd_neg_of_ne_zero hp_pos hp_neg
  have hdecomp := neg_sourcePair_posGraph_negGraph_eq_stationary_add_primeShift p
  linarith

/-- **Bilateral Stationary + Prime-Shift Primitive-Contraction Nodal Bound**:
for any `p : SourceGraph` and `0 < μ_max`, if `u_0 = (primGraph (absGraph p)).val.fst` satisfies
`⟪resolvent u_0, u_0⟫_ℝ ≤ μ_max * ‖u_0‖ ^ 2`, then both the stationary cross-jump penalty and the
prime-shift cross-jump term reinforce each other on the left-hand side:
`-sourceEnergy p - ((2 * μ_max - 1) / μ_max) * ‖p.val.fst‖ ^ 2 - 4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ + 4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ≤ ((1 - μ_max) / μ_max) * (2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2)`. -/
theorem stationary_and_primeShift_nodal_cross_le_of_primGraph_absGraph_rayleigh_le
    {p : SourceGraph} {μ_max : ℝ} (hμ : 0 < μ_max)
    (hray : ⟪resolvent (primGraph (absGraph p)).val.fst, (primGraph (absGraph p)).val.fst⟫_ℝ ≤
      μ_max * ‖(primGraph (absGraph p)).val.fst‖ ^ 2) :
    -sourceEnergy p - ((2 * μ_max - 1) / μ_max) * ‖p.val.fst‖ ^ 2 -
        4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ +
        4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ≤
      ((1 - μ_max) / μ_max) * (2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2) := by
  have h1 := nodal_cross_le_of_primGraph_absGraph_rayleigh_le hμ hray
  have h2 := neg_four_sourcePair_posGraph_negGraph_eq_stationary_add_primeShift p
  linarith

/-- **Bilateral Stationary + Prime-Shift Eigenvector Nodal Bound**:
for any eigenvector `resolvent v = ν • v` (`0 < ν`) with `p = rieszLift v` and `0 < μ_max`, if
`u_0 = (primGraph (absGraph p)).val.fst` satisfies `⟪resolvent u_0, u_0⟫_ℝ ≤ μ_max * ‖u_0‖ ^ 2`, then
`((ν - μ_max) / (ν * μ_max)) * ‖p.val.fst‖ ^ 2 - 4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ + 4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ≤ ((1 - μ_max) / μ_max) * (2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2)`. -/
theorem eigenvector_stationary_and_primeShift_nodal_cross_le_of_primGraph_absGraph_rayleigh_le
    {ν μ_max : ℝ} (hν : 0 < ν) (hμ : 0 < μ_max) {v : MassSpace}
    (heig : resolvent v = ν • v)
    (hray : ⟪resolvent (primGraph (absGraph (rieszLift v))).val.fst,
        (primGraph (absGraph (rieszLift v))).val.fst⟫_ℝ ≤
      μ_max * ‖(primGraph (absGraph (rieszLift v))).val.fst‖ ^ 2) :
    let p := rieszLift v
    ((ν - μ_max) / (ν * μ_max)) * ‖p.val.fst‖ ^ 2 -
        4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ +
        4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ≤
      ((1 - μ_max) / μ_max) * (2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2) := by
  intro p
  have h1 := eigenvector_nodal_cross_le_of_primGraph_absGraph_rayleigh_le hν hμ heig hray
  have h2 := neg_four_sourcePair_posGraph_negGraph_eq_stationary_add_primeShift p
  linarith

/-- **Sharp Spectral-Gap Weighted Bilateral Stationary + Prime-Shift Nodal Bound**:
for any eigenvector `resolvent v = ν • v` (`0 < ν`) with `q = rieszLift v` and `0 < μ_max`, if
`u_0 = (primGraph (absGraph q)).val.fst` satisfies `⟪resolvent u_0, u_0⟫_ℝ ≤ μ_max * ‖u_0‖ ^ 2`, then
`((ν - μ_max) / (ν * μ_max)) * ‖u_0‖ ^ 2 - 4 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ + 4 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ≤ ((1 - ν) / ν) * (2 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2)`. -/
theorem eigenvector_stationary_and_primeShift_nodal_cross_le_spectral_gap_mul_oneL_sq
    {ν μ_max : ℝ} (hν : 0 < ν) (hμ : 0 < μ_max) {v : MassSpace}
    (heig : resolvent v = ν • v)
    (hray : ⟪resolvent (primGraph (absGraph (rieszLift v))).val.fst,
        (primGraph (absGraph (rieszLift v))).val.fst⟫_ℝ ≤
      μ_max * ‖(primGraph (absGraph (rieszLift v))).val.fst‖ ^ 2) :
    let q := rieszLift v
    ((ν - μ_max) / (ν * μ_max)) * ‖(primGraph (absGraph q)).val.fst‖ ^ 2 -
        4 * ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        4 * ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ≤
      ((1 - ν) / ν) * (2 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2) := by
  intro q
  have h1 := eigenvector_nodal_cross_le_spectral_gap_mul_oneL_sq hν hμ heig hray
  have h2 := neg_four_sourcePair_posGraph_negGraph_eq_stationary_add_primeShift q
  linarith

/-- **Eigenvalue Upper Bound (`ν ≤ μ_max`) from Cross-Jump Dominance over the `oneL`-Defect**:
for any nonzero eigenvector `resolvent v = ν • v` (`0 < ν`, `v ≠ 0`) with `p = rieszLift v` and
`0 < μ_max`, if `u_0 = (primGraph (absGraph p)).val.fst` satisfies
`⟪resolvent u_0, u_0⟫_ℝ ≤ μ_max * ‖u_0‖ ^ 2` and the primitive `oneL`-defect is dominated by the
nodal cross-jump penalty:
`((1 - μ_max) / μ_max) * (2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2) ≤ -4 * sourcePair (posGraph p) (negGraph p)`,
then **`ν ≤ μ_max`**. -/
theorem eigenvalue_le_of_oneL_defect_le_neg_four_sourcePair
    {ν μ_max : ℝ} (hν : 0 < ν) (hμ : 0 < μ_max) {v : MassSpace} (hv0 : v ≠ 0)
    (heig : resolvent v = ν • v)
    (hray : ⟪resolvent (primGraph (absGraph (rieszLift v))).val.fst,
        (primGraph (absGraph (rieszLift v))).val.fst⟫_ℝ ≤
      μ_max * ‖(primGraph (absGraph (rieszLift v))).val.fst‖ ^ 2)
    (hdom : ((1 - μ_max) / μ_max) * (2 * ⟪(absGraph (rieszLift v)).val.fst, oneL⟫_ℝ ^ 2) ≤
      -4 * sourcePair (posGraph (rieszLift v)) (negGraph (rieszLift v))) :
    ν ≤ μ_max := by
  set p := rieszLift v
  have hp_fst : p.val.fst = ν • v := heig
  have hp_pos : 0 < ‖p.val.fst‖ ^ 2 := by
    rw [hp_fst, norm_smul, Real.norm_of_nonneg hν.le, mul_pow]
    exact mul_pos (sq_pos_of_pos hν) (sq_pos_of_pos (norm_pos_iff.mpr hv0))
  have h1 := eigenvector_nodal_cross_le_of_primGraph_absGraph_rayleigh_le hν hμ heig hray
  have hgap_nonpos : ((ν - μ_max) / (ν * μ_max)) * ‖p.val.fst‖ ^ 2 ≤ 0 := by linarith
  have hdiv_nonpos : (ν - μ_max) / (ν * μ_max) ≤ 0 :=
    nonpos_of_mul_nonpos_left hgap_nonpos hp_pos
  have hnum_nonpos : ν - μ_max ≤ 0 := by
    by_contra hlt
    have hgt : 0 < ν - μ_max := not_le.mp hlt
    have hdiv_pos : 0 < (ν - μ_max) / (ν * μ_max) :=
      div_pos hgt (mul_pos hν hμ)
    linarith
  linarith

/-- **Strict Eigenvalue Upper Bound (`ν < μ_max`) from Prime-Shift Cross Dominance**:
for any nonzero primitive eigenvector `resolvent v = ν • v` (`0 < ν`, `v ≠ 0`, `⟪v, oneL⟫_ℝ = 0`)
with `p = rieszLift v` and `0 < μ_max`, if `u_0 = (primGraph (absGraph p)).val.fst` satisfies
`⟪resolvent u_0, u_0⟫_ℝ ≤ μ_max * ‖u_0‖ ^ 2` and the primitive `oneL`-defect is dominated by the
prime-shift cross-jump term alone:
`((1 - μ_max) / μ_max) * (2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2) ≤ 4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`,
then the strict positivity of the stationary cross-jump across the nodal interface forces the
strict eigenvalue bound **`ν < μ_max`**. -/
theorem eigenvalue_lt_of_primitive_oneL_defect_le_four_primeShift
    {ν μ_max : ℝ} (hν : 0 < ν) (hμ : 0 < μ_max) {v : MassSpace} (hv0 : v ≠ 0)
    (hprim : ⟪v, oneL⟫_ℝ = 0) (heig : resolvent v = ν • v)
    (hray : ⟪resolvent (primGraph (absGraph (rieszLift v))).val.fst,
        (primGraph (absGraph (rieszLift v))).val.fst⟫_ℝ ≤
      μ_max * ‖(primGraph (absGraph (rieszLift v))).val.fst‖ ^ 2)
    (hdom : ((1 - μ_max) / μ_max) * (2 * ⟪(absGraph (rieszLift v)).val.fst, oneL⟫_ℝ ^ 2) ≤
      4 * ⟪primeShiftOperator (posGraph (rieszLift v)).val.fst,
        (negGraph (rieszLift v)).val.fst⟫_ℝ) :
    ν < μ_max := by
  set p := rieszLift v
  have hp_fst : p.val.fst = ν • v := heig
  have hp0 : p ≠ 0 := by
    intro h
    have hf : p.val.fst = 0 := by rw [h]; rfl
    rw [hp_fst, smul_eq_zero] at hf
    exact hv0 (hf.resolve_left hν.ne')
  have hp_prim : ⟪p.val.fst, oneL⟫_ℝ = 0 := by
    rw [hp_fst, real_inner_smul_left, hprim, mul_zero]
  obtain ⟨hpos_ne, hneg_ne⟩ := posGraph_ne_zero_and_negGraph_ne_zero_of_primitive hp0 hp_prim
  have hstat_neg := inner_fullGroundEquiv_posGraph_negGraph_snd_neg_of_ne_zero hpos_ne hneg_ne
  have h1 : ((ν - μ_max) / (ν * μ_max)) * ‖p.val.fst‖ ^ 2 -
      4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ +
      4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ ≤
      ((1 - μ_max) / μ_max) * (2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2) :=
    eigenvector_stationary_and_primeShift_nodal_cross_le_of_primGraph_absGraph_rayleigh_le
      hν hμ heig hray
  have hgap_neg : ((ν - μ_max) / (ν * μ_max)) * ‖p.val.fst‖ ^ 2 < 0 := by linarith
  have hp_sq_nonneg : 0 ≤ ‖p.val.fst‖ ^ 2 := sq_nonneg _
  by_contra hge
  have hle : μ_max ≤ ν := not_lt.mp hge
  have hdiv_nonneg : 0 ≤ (ν - μ_max) / (ν * μ_max) :=
    div_nonneg (sub_nonneg.mpr hle) (mul_pos hν hμ).le
  have hprod_nonneg : 0 ≤ ((ν - μ_max) / (ν * μ_max)) * ‖p.val.fst‖ ^ 2 :=
    mul_nonneg hdiv_nonneg hp_sq_nonneg
  linarith

/-! ## Section 2: Three-Term Nonnegative Nodal-Lobe Decomposition and Individual Lobe Bounds -/

/-- **Positive-Lobe Three-Term Nonnegative Decomposition for Any Resolvent Eigenvector**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`‖(posGraph q).val.snd‖ ^ 2 - ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ + ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ = ((1 - μ) / μ) * ‖(posGraph q).val.fst‖ ^ 2`,
where all three summands on the left-hand side are nonnegative. -/
theorem posGraph_three_term_nonneg_decomposition_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0)
    {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w
    ‖(posGraph q).val.snd‖ ^ 2 -
        ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ =
      ((1 - μ) / μ) * ‖(posGraph q).val.fst‖ ^ 2 := by
  intro q
  have h1 := norm_posGraph_snd_sq_rieszLift_of_eigenvector hμ heig
  have h2 := sourcePair_posGraph_negGraph_eq_stationary_sub_primeShift q
  linarith

/-- **Negative-Lobe Three-Term Nonnegative Decomposition for Any Resolvent Eigenvector**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`‖(negGraph q).val.snd‖ ^ 2 - ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ + ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ = ((1 - μ) / μ) * ‖(negGraph q).val.fst‖ ^ 2`,
where all three summands on the left-hand side are nonnegative. -/
theorem negGraph_three_term_nonneg_decomposition_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0)
    {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w
    ‖(negGraph q).val.snd‖ ^ 2 -
        ⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ +
        ⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ =
      ((1 - μ) / μ) * ‖(negGraph q).val.fst‖ ^ 2 := by
  intro q
  have h1 := norm_negGraph_snd_sq_rieszLift_of_eigenvector hμ heig
  have h2 := sourcePair_posGraph_negGraph_eq_stationary_sub_primeShift q
  linarith

/-- **Individual Lobe Upper Bounds on the Stationary and Prime-Shift Cross-Jump Pairings**:
for every eigenvector `resolvent w = μ • w` (`0 < μ`) with `q = rieszLift w`, both the stationary
cross-jump penalty `-⟪(fullGroundEquiv (posGraph q)).val.snd, (fullGroundEquiv (negGraph q)).val.snd⟫_ℝ`
and the prime-shift cross-jump term `⟪primeShiftOperator (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`
are bounded above by `((1 - μ) / μ)` times the $L^2$ norm-squared of each nodal lobe individually. -/
theorem stationary_and_primeShift_posGraph_negGraph_le_lobe_fst_sq_of_eigenvector
    {μ : ℝ} (hμ : 0 < μ) {w : MassSpace} (heig : resolvent w = μ • w) :
    -⟪(fullGroundEquiv (posGraph (rieszLift w))).val.snd,
        (fullGroundEquiv (negGraph (rieszLift w))).val.snd⟫_ℝ ≤
        ((1 - μ) / μ) * ‖(posGraph (rieszLift w)).val.fst‖ ^ 2 ∧
      -⟪(fullGroundEquiv (posGraph (rieszLift w))).val.snd,
          (fullGroundEquiv (negGraph (rieszLift w))).val.snd⟫_ℝ ≤
        ((1 - μ) / μ) * ‖(negGraph (rieszLift w)).val.fst‖ ^ 2 ∧
      ⟪primeShiftOperator (posGraph (rieszLift w)).val.fst,
          (negGraph (rieszLift w)).val.fst⟫_ℝ ≤
        ((1 - μ) / μ) * ‖(posGraph (rieszLift w)).val.fst‖ ^ 2 ∧
      ⟪primeShiftOperator (posGraph (rieszLift w)).val.fst,
          (negGraph (rieszLift w)).val.fst⟫_ℝ ≤
        ((1 - μ) / μ) * ‖(negGraph (rieszLift w)).val.fst‖ ^ 2 := by
  obtain ⟨hp, hn⟩ := neg_sourcePair_posGraph_negGraph_le_pos_and_neg_lobe_of_eigenvector hμ heig
  obtain ⟨_, _, hstat, hprime⟩ :=
    stationary_and_primeShift_le_neg_sourcePair_posGraph_negGraph (rieszLift w)
  exact ⟨hstat.trans hp, hstat.trans hn, hprime.trans hp, hprime.trans hn⟩

/-! ## Section 3: Odd-Sector Exact Half-Mass Lobe Laws and Odd Eigenvector Lobe Identities -/

/-- For every `p : SourceGraph`, the sum of the positive and negative lobe edge norms-squared satisfies
`‖(posGraph p).val.snd‖ ^ 2 + ‖(negGraph p).val.snd‖ ^ 2 = ‖p.val.snd‖ ^ 2 + 2 * sourcePair (posGraph p) (negGraph p)`. -/
theorem norm_posGraph_snd_sq_add_negGraph_snd_sq (p : SourceGraph) :
    ‖(posGraph p).val.snd‖ ^ 2 + ‖(negGraph p).val.snd‖ ^ 2 =
      ‖p.val.snd‖ ^ 2 + 2 * sourcePair (posGraph p) (negGraph p) := by
  have hEp : sourceEnergy p = ‖p.val.snd‖ ^ 2 - ‖p.val.fst‖ ^ 2 := rfl
  have hEpos : sourceEnergy (posGraph p) =
      ‖(posGraph p).val.snd‖ ^ 2 - ‖(posGraph p).val.fst‖ ^ 2 := rfl
  have hEneg : sourceEnergy (negGraph p) =
      ‖(negGraph p).val.snd‖ ^ 2 - ‖(negGraph p).val.fst‖ ^ 2 := rfl
  have h1 := sourceEnergy_eq_posGraph_add_negGraph_sub_two_sourcePair p
  have h2 := norm_posGraph_fst_sq_add_negGraph_fst_sq p
  rw [hEp, hEpos, hEneg] at h1
  linarith

/-- For any odd graph vector `p` (`reflectGraph p = -p`), its positive and negative lobes have equal
`EdgeSpace` norm-squared, each equal to
`(1 / 2) * ‖p.val.snd‖ ^ 2 + sourcePair (posGraph p) (negGraph p)`. -/
theorem norm_posGraph_and_negGraph_snd_sq_of_odd {p : SourceGraph} (hp : reflectGraph p = -p) :
    ‖(posGraph p).val.snd‖ ^ 2 =
        (1 / 2 : ℝ) * ‖p.val.snd‖ ^ 2 + sourcePair (posGraph p) (negGraph p) ∧
      ‖(negGraph p).val.snd‖ ^ 2 =
        (1 / 2 : ℝ) * ‖p.val.snd‖ ^ 2 + sourcePair (posGraph p) (negGraph p) := by
  have hE := sourceEnergy_posGraph_eq_negGraph_of_odd hp
  obtain ⟨hf_pos, hf_neg⟩ := norm_posGraph_and_negGraph_fst_sq_eq_half_of_odd hp
  have hEpos : sourceEnergy (posGraph p) =
      ‖(posGraph p).val.snd‖ ^ 2 - ‖(posGraph p).val.fst‖ ^ 2 := rfl
  have hEneg : sourceEnergy (negGraph p) =
      ‖(negGraph p).val.snd‖ ^ 2 - ‖(negGraph p).val.fst‖ ^ 2 := rfl
  have heq : ‖(posGraph p).val.snd‖ ^ 2 = ‖(negGraph p).val.snd‖ ^ 2 := by
    rw [hEpos, hEneg, hf_pos, hf_neg] at hE
    linarith
  have hsum := norm_posGraph_snd_sq_add_negGraph_snd_sq p
  exact ⟨by linarith, by linarith⟩

/-- **Odd-Sector Eigenvector Half-Mass Nodal-Lobe Identities**:
for every odd eigenvector `resolvent w = μ • w` (`μ ≠ 0`, `reflectMass w = -w`) with
`q = rieszLift w`:
- `reflectGraph q = -q`,
- `sourceEnergy (posGraph q) = ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q)`,
- `sourceEnergy (negGraph q) = ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q)`,
- `‖(posGraph q).val.snd‖ ^ 2 = ((1 - μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q)`,
- `‖(negGraph q).val.snd‖ ^ 2 = ((1 - μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q)`. -/
theorem odd_eigenvector_lobe_energy_and_snd_sq {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (hodd : reflectMass w = -w) (heig : resolvent w = μ • w) :
    let q := rieszLift w
    reflectGraph q = -q ∧
      sourceEnergy (posGraph q) =
        ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q) ∧
      sourceEnergy (negGraph q) =
        ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q) ∧
      ‖(posGraph q).val.snd‖ ^ 2 =
        ((1 - μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q) ∧
      ‖(negGraph q).val.snd‖ ^ 2 =
        ((1 - μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 + sourcePair (posGraph q) (negGraph q) := by
  intro q
  have hq_odd : reflectGraph q = -q := by
    change reflectGraph (rieszLift w) = -rieszLift w
    rw [← rieszLift_reflectMass, hodd, ← neg_one_smul ℝ w, rieszLift_smul, neg_one_smul]
  obtain ⟨hf_pos, hf_neg⟩ := norm_posGraph_and_negGraph_fst_sq_eq_half_of_odd hq_odd
  have hEpos := sourceEnergy_posGraph_rieszLift_of_eigenvector hμ heig
  have hEneg := sourceEnergy_negGraph_rieszLift_of_eigenvector hμ heig
  have hsnd_pos := norm_posGraph_snd_sq_rieszLift_of_eigenvector hμ heig
  have hsnd_neg := norm_negGraph_snd_sq_rieszLift_of_eigenvector hμ heig
  rw [hf_pos] at hEpos hsnd_pos
  rw [hf_neg] at hEneg hsnd_neg
  have hid1 : ((1 - 2 * μ) / μ) * ((1 / 2 : ℝ) * ‖q.val.fst‖ ^ 2) =
      ((1 - 2 * μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 := by
    field_simp [hμ]
  have hid2 : ((1 - μ) / μ) * ((1 / 2 : ℝ) * ‖q.val.fst‖ ^ 2) =
      ((1 - μ) / (2 * μ)) * ‖q.val.fst‖ ^ 2 := by
    field_simp [hμ]
  refine ⟨hq_odd, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith

/-! ## Section 4: Universal Primitive-Contraction Resolvent Polarization and Rayleigh Excess -/

/-- **Universal Primitive-Contraction Resolvent Polarization Identity**:
for every `p : SourceGraph`,
`⟪resolvent (primGraph (absGraph p)).val.fst, (primGraph (absGraph p)).val.fst⟫_ℝ - ⟪resolvent p.val.fst, p.val.fst⟫_ℝ = 4 * ⟪resolvent (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ - 2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2`. -/
theorem inner_resolvent_primGraph_absGraph_sub_self (p : SourceGraph) :
    ⟪resolvent (primGraph (absGraph p)).val.fst, (primGraph (absGraph p)).val.fst⟫_ℝ -
        ⟪resolvent p.val.fst, p.val.fst⟫_ℝ =
      4 * ⟪resolvent (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ -
        2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2 := by
  have h1 := inner_resolvent_primGraph_fst (absGraph p)
  have h2 := inner_resolvent_absGraph_sub_self p
  linarith

/-- **Primitive-Lobe vs. Raw-Lobe Resolvent Cross-Pairing Identity**:
for every primitive `p : SourceGraph` (`⟪p.val.fst, oneL⟫_ℝ = 0`),
`⟪resolvent (primGraph (posGraph p)).val.fst, (primGraph (negGraph p)).val.fst⟫_ℝ = ⟪resolvent (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ - (1 / 2) * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2`. -/
theorem inner_resolvent_primGraph_posGraph_negGraph_eq_of_primitive {p : SourceGraph}
    (hp : ⟪p.val.fst, oneL⟫_ℝ = 0) :
    ⟪resolvent (primGraph (posGraph p)).val.fst, (primGraph (negGraph p)).val.fst⟫_ℝ =
      ⟪resolvent (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ -
        (1 / 2 : ℝ) * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2 := by
  have h1 := inner_resolvent_primGraph_absGraph_sub_self_of_primitive hp
  have h2 := inner_resolvent_primGraph_absGraph_sub_self p
  linarith

/-- **Exact Primitive-Contraction Rayleigh Excess Identity for Any Eigenvector**:
for every eigenvector `resolvent v = ν • v` with `p = rieszLift v`, the Rayleigh excess of
`u_0 = (primGraph (absGraph p)).val.fst` above `ν * ‖u_0‖ ^ 2` is given identically by
`⟪resolvent u_0, u_0⟫_ℝ - ν * ‖u_0‖ ^ 2 = 4 * ⟪resolvent (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ - 2 * (1 - ν) * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2`. -/
theorem eigenvector_primGraph_absGraph_rayleigh_excess {ν : ℝ} {v : MassSpace}
    (heig : resolvent v = ν • v) :
    let p := rieszLift v
    ⟪resolvent (primGraph (absGraph p)).val.fst, (primGraph (absGraph p)).val.fst⟫_ℝ -
        ν * ‖(primGraph (absGraph p)).val.fst‖ ^ 2 =
      4 * ⟪resolvent (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ -
        2 * (1 - ν) * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2 := by
  intro p
  have hp_fst : p.val.fst = ν • v := heig
  have hp_eig : resolvent p.val.fst = ν • p.val.fst := by
    rw [hp_fst, map_smul, heig]
  have hinner_p : ⟪resolvent p.val.fst, p.val.fst⟫_ℝ = ν * ‖p.val.fst‖ ^ 2 := by
    rw [hp_eig, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hnorm : ‖(primGraph (absGraph p)).val.fst‖ ^ 2 =
      ‖p.val.fst‖ ^ 2 - 2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2 := by
    rw [norm_primGraph_fst_sq, norm_absGraph_fst_sq]
  have h1 := inner_resolvent_primGraph_absGraph_sub_self p
  have h2 : ν * ‖(primGraph (absGraph p)).val.fst‖ ^ 2 =
      ν * ‖p.val.fst‖ ^ 2 - 2 * ν * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2 := by
    linarith [congrArg (ν * ·) hnorm]
  linarith

end RHTower.CHMDPolar
