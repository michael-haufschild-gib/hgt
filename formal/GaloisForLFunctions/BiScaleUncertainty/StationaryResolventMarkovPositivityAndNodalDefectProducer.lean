import GaloisForLFunctions.BiScaleUncertainty.CoshDecayGroundPotentialAndThetaVolumeCollarProducer

/-!
# Beurling–Deny Markov Positivity of `stationaryResolvent`, Modulus Domination, and the Nodal Defect Graph

This module establishes the Beurling–Deny Markov positivity of `stationaryResolvent` on `MassSpace`,
its positivity on combined `id + archDiagonalOperator + primeShiftOperator` inputs, the pointwise and
Hilbert-norm modulus domination of `stationaryResolvent` on `SourceGraph`, and the common nodal defect
graph `nodalDefectGraph` for `resolvent` eigenvectors:

## Mathematical Overview

1. **Polarized `primeShiftOperator` Integral Formula and Positivity of `archDiagonalOperator` and
   `primeShiftOperator` (§1)**:
   - `inner_primeShiftOperator_eq_integral`:
     polarizing `inner_primeShiftOperator_self_eq_integral` yields, for all `u, v : MassSpace`,
     `⟪primeShiftOperator u, v⟫_ℝ = ∫ e, (u (left e) * v (right e) + v (left e) * u (right e)) ∂allPrimeMeasure`.
   - `inner_primeShiftOperator_nonneg_of_ae_nonneg`:
     for any `u, v : MassSpace` with `0 ≤ᵐ[massMeasure] u` and `0 ≤ᵐ[massMeasure] v`,
     `0 ≤ ⟪primeShiftOperator u, v⟫_ℝ`.
   - `archDiagonalOperator_ae_nonneg_of_ae_nonneg` and `inner_massSpace_nonneg_of_ae_nonneg`:
     positivity preservation of `archDiagonalOperator` and inner-product nonnegativity on `MassSpace`.

2. **Universal `stationaryGraphLift` Lobe Balance and Beurling–Deny Markov Positivity of
   `stationaryResolvent` (§2)**:
   - `stationaryGraphLift_posGraph_and_negGraph_balance`:
     for every `w : MassSpace` with `p = stationaryGraphLift w`, testing `inner_stationaryRieszLift_snd`
     against `posGraph p` and `negGraph p` gives
     `‖(posGraph p).val.fst‖ ^ 2 + stationaryEnergy (thetaProduct (posGraph p).val.fst) - ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ = ⟪(posGraph p).val.fst, w⟫_ℝ`
     and
     `‖(negGraph p).val.fst‖ ^ 2 + stationaryEnergy (thetaProduct (negGraph p).val.fst) - ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ = -⟪(negGraph p).val.fst, w⟫_ℝ`.
   - `negGraph_stationaryGraphLift_eq_zero_of_inner_nonneg`:
     because all three left-hand summands are nonnegative, whenever
     `0 ≤ ⟪(negGraph (stationaryGraphLift w)).val.fst, w⟫_ℝ`, the negative lobe vanishes identically
     (`negGraph (stationaryGraphLift w) = 0`) and `0 ≤ᵐ[massMeasure] (stationaryResolvent w : ℝ → ℝ)`.
   - `stationaryResolvent_ae_nonneg_of_ae_nonneg` and `stationaryResolvent_combo_ae_nonneg_of_ae_nonneg`:
     `stationaryResolvent` preserves almost-everywhere nonnegativity on `MassSpace` and maps any
     nonnegative linear combination `a • u + b • archDiagonalOperator u + c • primeShiftOperator u`
     (`0 ≤ᵐ[massMeasure] u`, `0 ≤ a, b, c`) to an almost-everywhere nonnegative function.

3. **Cross-Lobe Positivity and Modulus Domination of `stationaryResolvent` on `SourceGraph` (§3)**:
   - `inner_stationaryResolvent_posGraph_negGraph_nonneg` and `inner_stationaryResolvent_self_le_absGraph`:
     for all `p, q : SourceGraph`, `0 ≤ ⟪stationaryResolvent (posGraph p).val.fst, (negGraph q).val.fst⟫_ℝ`
     and `⟪stationaryResolvent p.val.fst, p.val.fst⟫_ℝ ≤ ⟪stationaryResolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ`.
   - `abs_stationaryResolvent_ae_le_stationaryResolvent_absGraph` and
     `norm_stationaryResolvent_absGraph_sq_sub_self_sq`:
     `|stationaryResolvent p.val.fst x| ≤ stationaryResolvent (absGraph p).val.fst x` almost everywhere
     on `massMeasure`, and `‖stationaryResolvent p.val.fst‖ ^ 2 ≤ ‖stationaryResolvent (absGraph p).val.fst‖ ^ 2`.

4. **The Common Nodal Defect Graph `nodalDefectGraph`, Pointwise Lobe Sub-Invariance, and
   `stationaryGroundGraph` Cauchy–Schwarz Lower Bound (§4)**:
   - `stationaryCollarPotential` and `nodalDefectGraph`:
     for any `μ : ℝ` and `q : SourceGraph`, defines
     `stationaryCollarPotential μ u = ((1 - μ) / μ) • u + archDiagonalOperator u + primeShiftOperator u`
     and `nodalDefectGraph μ q = stationaryGraphLift (stationaryCollarPotential μ (posGraph q).val.fst) - posGraph q`.
   - `nodalDefectGraph_eq_negGraph_defect_of_eigenvector`:
     for any eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`, the positive and
     negative lobes have the exact same nodal defect graph:
     `nodalDefectGraph μ q = stationaryGraphLift (stationaryCollarPotential μ (negGraph q).val.fst) - negGraph q`.
   - `nodalDefectGraph_fst_ae_nonneg_and_lobe_subinvariance_of_eigenvector`:
     for `0 < μ ≤ 1`, disjointness of the nodal supports (`posFun * negFun = 0`) and Markov positivity
     of `stationaryResolvent` force `0 ≤ᵐ[massMeasure] (nodalDefectGraph μ q).val.fst` and the
     pointwise lobe sub-invariance inequalities
     `(posGraph q).val.fst ≤ᵐ[massMeasure] stationaryResolvent (stationaryCollarPotential μ (posGraph q).val.fst)`
     and
     `(negGraph q).val.fst ≤ᵐ[massMeasure] stationaryResolvent (stationaryCollarPotential μ (negGraph q).val.fst)`.
   - `inner_fullGroundEquiv_nodalDefectGraph_of_eigenvector`:
     in `stationaryGroundGraph`, `fullGroundEquiv (nodalDefectGraph μ q)` has inner product
     `-sourcePair (posGraph q) (negGraph q)` with both `fullGroundEquiv (posGraph q)` and
     `fullGroundEquiv (negGraph q)`, is orthogonal to `fullGroundEquiv q`, and satisfies the
     quantitative Cauchy–Schwarz lower bound
     `4 * sourcePair (posGraph q) (negGraph q) ^ 2 ≤ (‖(nodalDefectGraph μ q).val.fst‖ ^ 2 + stationaryEnergy (thetaProduct (nodalDefectGraph μ q).val.fst)) * (‖q.val.fst‖ ^ 2 + stationaryEnergy (thetaProduct (absGraph q).val.fst))`.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators
noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

open _root_.RHTower
open _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.CHMDClosedJump
open _root_.RHTower.CHMDTranslation
open _root_.RHTower.ThetaSourceWard
open _root_.RHTower.CHMDPolar

/-! ## Section 1: Polarized `primeShiftOperator` Integral Formula and Positivity of `archDiagonalOperator` and `primeShiftOperator` -/

/-- Polarized `allPrimeMeasure` integral formula for `primeShiftOperator`:
for all `u, v : MassSpace`,
`⟪primeShiftOperator u, v⟫_ℝ = ∫ e, (u (left e) * v (right e) + v (left e) * u (right e)) ∂allPrimeMeasure`. -/
theorem inner_primeShiftOperator_eq_integral (u v : MassSpace) :
    ⟪primeShiftOperator u, v⟫_ℝ =
      ∫ e, (u (left e) * v (right e) + v (left e) * u (right e)) ∂allPrimeMeasure := by
  have hpol : 2 * ⟪primeShiftOperator u, v⟫_ℝ =
      ⟪primeShiftOperator (u + v), u + v⟫_ℝ -
        ⟪primeShiftOperator u, u⟫_ℝ - ⟪primeShiftOperator v, v⟫_ℝ := by
    rw [map_add, inner_add_left, inner_add_right, inner_add_right,
      real_inner_comm v (primeShiftOperator u), primeShiftOperator_symmetric v u]
    ring
  have h_uv := inner_primeShiftOperator_self_eq_integral (u + v)
  have h_u := inner_primeShiftOperator_self_eq_integral u
  have h_v := inner_primeShiftOperator_self_eq_integral v
  have hint_uu := integrable_allPrime_left_mul_right u u
  have hint_vv := integrable_allPrime_left_mul_right v v
  have hint_uv := integrable_allPrime_left_mul_right u v
  have hint_vu := integrable_allPrime_left_mul_right v u
  have h_add_ae : (fun e => (u + v) (left e) * (u + v) (right e)) =ᵐ[allPrimeMeasure]
      fun e => (u (left e) * u (right e) + v (left e) * v (right e)) +
        (u (left e) * v (right e) + v (left e) * u (right e)) := by
    filter_upwards [nonsingular_allPrime_left.ae_eq_comp (Lp.coeFn_add u v),
      nonsingular_allPrime_right.ae_eq_comp (Lp.coeFn_add u v)] with e hl hr
    simp only [Function.comp_apply, Pi.add_apply] at hl hr
    rw [hl, hr]
    ring
  have h_int_add : (∫ e, (u + v) (left e) * (u + v) (right e) ∂allPrimeMeasure) =
      (∫ e, u (left e) * u (right e) ∂allPrimeMeasure) +
        (∫ e, v (left e) * v (right e) ∂allPrimeMeasure) +
        ∫ e, (u (left e) * v (right e) + v (left e) * u (right e)) ∂allPrimeMeasure := by
    have h1 := integral_add (hint_uu.add hint_vv) (hint_uv.add hint_vu)
    have h2 := integral_add hint_uu hint_vv
    dsimp only [Pi.add_apply] at h1 h2
    rw [integral_congr_ae h_add_ae, h1, h2]
  linarith

/-- Nonnegativity of `⟪primeShiftOperator u, v⟫_ℝ` for a.e. nonnegative `u, v : MassSpace`. -/
theorem inner_primeShiftOperator_nonneg_of_ae_nonneg {u v : MassSpace}
    (hu : 0 ≤ᵐ[massMeasure] (u : ℝ → ℝ)) (hv : 0 ≤ᵐ[massMeasure] (v : ℝ → ℝ)) :
    0 ≤ ⟪primeShiftOperator u, v⟫_ℝ := by
  rw [inner_primeShiftOperator_eq_integral]
  refine integral_nonneg_of_ae ?_
  filter_upwards [nonsingular_allPrime_left.ae hu, nonsingular_allPrime_right.ae hu,
    nonsingular_allPrime_left.ae hv, nonsingular_allPrime_right.ae hv] with e hul hur hvl hvr
  exact add_nonneg (mul_nonneg hul hvr) (mul_nonneg hvl hur)

/-- Almost-everywhere nonnegativity of `archDiagonalOperator u` for a.e. nonnegative `u : MassSpace`. -/
theorem archDiagonalOperator_ae_nonneg_of_ae_nonneg {u : MassSpace}
    (hu : 0 ≤ᵐ[massMeasure] (u : ℝ → ℝ)) :
    0 ≤ᵐ[massMeasure] (archDiagonalOperator u : ℝ → ℝ) := by
  filter_upwards [archDiagonalOperator_ae u, hu] with x harch hux
  rw [harch]
  have hpos : 0 ≤ archGroundConstant * riemannKernelReal x / Real.cosh (x / 2) :=
    div_nonneg (mul_nonneg archGroundConstant_pos.le (riemannKernelReal_pos x).le)
      (Real.cosh_pos (x / 2)).le
  exact mul_nonneg hpos hux

/-- Inner product nonnegativity in `MassSpace` for a.e. nonnegative functions. -/
theorem inner_massSpace_nonneg_of_ae_nonneg {u v : MassSpace}
    (hu : 0 ≤ᵐ[massMeasure] (u : ℝ → ℝ)) (hv : 0 ≤ᵐ[massMeasure] (v : ℝ → ℝ)) :
    0 ≤ ⟪u, v⟫_ℝ := by
  rw [L2.inner_def]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hu, hv] with x hux hvx
  simp only [RCLike.inner_apply, conj_trivial]
  exact mul_nonneg hvx hux

theorem posGraph_fst_ae_nonneg (p : SourceGraph) :
    0 ≤ᵐ[massMeasure] ((posGraph p).val.fst : ℝ → ℝ) := by
  filter_upwards [posGraph_fst_ae p] with x hx
  change 0 ≤ (posGraph p).val.fst x
  rw [hx]
  exact posFun_nonneg _

theorem negGraph_fst_ae_nonneg (p : SourceGraph) :
    0 ≤ᵐ[massMeasure] ((negGraph p).val.fst : ℝ → ℝ) := by
  filter_upwards [negGraph_fst_ae p] with x hx
  change 0 ≤ (negGraph p).val.fst x
  rw [hx]
  exact negFun_nonneg _

theorem absGraph_fst_ae_nonneg (p : SourceGraph) :
    0 ≤ᵐ[massMeasure] ((absGraph p).val.fst : ℝ → ℝ) := by
  filter_upwards [absGraph_fst_ae p] with x hx
  change 0 ≤ (absGraph p).val.fst x
  rw [hx]
  exact abs_nonneg _

/-! ## Section 2: Universal `stationaryGraphLift` Lobe Balance and Beurling–Deny Markov Positivity of `stationaryResolvent` -/

/-- Universal `stationaryGraphLift` lobe balance identities: for every `w : MassSpace` with
`p = stationaryGraphLift w`,
`‖(posGraph p).val.fst‖ ^ 2 + stationaryEnergy (thetaProduct (posGraph p).val.fst) - ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ = ⟪(posGraph p).val.fst, w⟫_ℝ`
and
`‖(negGraph p).val.fst‖ ^ 2 + stationaryEnergy (thetaProduct (negGraph p).val.fst) - ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ = -⟪(negGraph p).val.fst, w⟫_ℝ`. -/
theorem stationaryGraphLift_posGraph_and_negGraph_balance (w : MassSpace) :
    let p := stationaryGraphLift w
    ‖(posGraph p).val.fst‖ ^ 2 +
        stationaryEnergy (thetaProduct (posGraph p).val.fst) -
        ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ =
      ⟪(posGraph p).val.fst, w⟫_ℝ ∧
    ‖(negGraph p).val.fst‖ ^ 2 +
        stationaryEnergy (thetaProduct (negGraph p).val.fst) -
        ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ =
      -⟪(negGraph p).val.fst, w⟫_ℝ := by
  intro p
  have hsub : (fullGroundEquiv p).val.snd =
      (fullGroundEquiv (posGraph p)).val.snd - (fullGroundEquiv (negGraph p)).val.snd :=
    congrArg (fun r : stationaryGroundGraph => r.val.snd)
      (fullGroundEquiv_posGraph_sub_negGraph p).symm
  have hpos_fst : (fullGroundEquiv (posGraph p)).val.fst = (posGraph p).val.fst :=
    fullGroundEquiv_source (posGraph p)
  have hneg_fst : (fullGroundEquiv (negGraph p)).val.fst = (negGraph p).val.fst :=
    fullGroundEquiv_source (negGraph p)
  have hp_lift : stationaryRieszLift w = fullGroundEquiv p :=
    (fullGroundEquiv_stationaryGraphLift w).symm
  have hp_res : stationaryResolvent w = p.val.fst :=
    (stationaryGraphLift_fst w).symm
  refine ⟨?_, ?_⟩
  · have h1 := inner_stationaryRieszLift_snd w (posGraph p)
    rw [hp_lift, hp_res, hsub, inner_sub_right, real_inner_self_eq_norm_sq,
      stationaryGround_edge_energy, hpos_fst, inner_sub_right, inner_posGraph_self_fst] at h1
    linarith
  · have h1 := inner_stationaryRieszLift_snd w (negGraph p)
    rw [hp_lift, hp_res, hsub, inner_sub_right,
      real_inner_comm (fullGroundEquiv (posGraph p)).val.snd (fullGroundEquiv (negGraph p)).val.snd,
      real_inner_self_eq_norm_sq, stationaryGround_edge_energy, hneg_fst,
      inner_sub_right, inner_negGraph_self_fst] at h1
    linarith

/-- Whenever `0 ≤ ⟪(negGraph (stationaryGraphLift w)).val.fst, w⟫_ℝ`, the negative lobe of
`stationaryGraphLift w` vanishes identically (`negGraph (stationaryGraphLift w) = 0`), and
`0 ≤ᵐ[massMeasure] (stationaryResolvent w : ℝ → ℝ)`. -/
theorem negGraph_stationaryGraphLift_eq_zero_of_inner_nonneg {w : MassSpace}
    (hw : 0 ≤ ⟪(negGraph (stationaryGraphLift w)).val.fst, w⟫_ℝ) :
    negGraph (stationaryGraphLift w) = 0 ∧
      posGraph (stationaryGraphLift w) = stationaryGraphLift w ∧
      absGraph (stationaryGraphLift w) = stationaryGraphLift w ∧
      0 ≤ᵐ[massMeasure] (stationaryResolvent w : ℝ → ℝ) := by
  set p := stationaryGraphLift w
  have hbal := (stationaryGraphLift_posGraph_and_negGraph_balance w).2
  change ‖(negGraph p).val.fst‖ ^ 2 +
      stationaryEnergy (thetaProduct (negGraph p).val.fst) -
      ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ =
    -⟪(negGraph p).val.fst, w⟫_ℝ at hbal
  have hstat_nn : 0 ≤ stationaryEnergy (thetaProduct (negGraph p).val.fst) := by
    have hnf : (fullGroundEquiv (negGraph p)).val.fst = (negGraph p).val.fst :=
      fullGroundEquiv_source (negGraph p)
    rw [← hnf, ← stationaryGround_edge_energy]
    exact sq_nonneg _
  have hcross_nn : 0 ≤ -⟪(fullGroundEquiv (posGraph p)).val.snd,
      (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ :=
    neg_nonneg.mpr (inner_fullGroundEquiv_posGraph_negGraph_snd_nonpos p)
  have hnorm_sq : ‖(negGraph p).val.fst‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖(negGraph p).val.fst‖]
  have hneg_fst : (negGraph p).val.fst = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm_sq)
  have hneg0 : negGraph p = 0 :=
    source_projection_injective (hneg_fst.trans rfl)
  have hpos_eq : posGraph p = p := by
    have hsub := posGraph_sub_negGraph p
    rw [hneg0, sub_zero] at hsub
    exact hsub
  have habs_eq : absGraph p = p := by
    rw [← posGraph_add_negGraph p, hneg0, add_zero, hpos_eq]
  have hae : 0 ≤ᵐ[massMeasure] (stationaryResolvent w : ℝ → ℝ) := by
    have h1 : 0 ≤ᵐ[massMeasure] (p.val.fst : ℝ → ℝ) := by
      rw [← hpos_eq]
      exact posGraph_fst_ae_nonneg p
    rwa [stationaryGraphLift_fst w] at h1
  exact ⟨hneg0, hpos_eq, habs_eq, hae⟩

/-- **Beurling–Deny Markov Positivity of `stationaryResolvent`**:
for every `w : MassSpace` with `0 ≤ᵐ[massMeasure] (w : ℝ → ℝ)`,
`0 ≤ᵐ[massMeasure] (stationaryResolvent w : ℝ → ℝ)`. -/
theorem stationaryResolvent_ae_nonneg_of_ae_nonneg {w : MassSpace}
    (hw : 0 ≤ᵐ[massMeasure] (w : ℝ → ℝ)) :
    0 ≤ᵐ[massMeasure] (stationaryResolvent w : ℝ → ℝ) :=
  (negGraph_stationaryGraphLift_eq_zero_of_inner_nonneg
    (inner_massSpace_nonneg_of_ae_nonneg (negGraph_fst_ae_nonneg (stationaryGraphLift w)) hw)).2.2.2

/-- **Positivity of `stationaryResolvent` on Combined `id + archDiagonalOperator + primeShiftOperator` Inputs**:
for every `u : MassSpace` with `0 ≤ᵐ[massMeasure] (u : ℝ → ℝ)` and `0 ≤ a`, `0 ≤ b`, `0 ≤ c`,
`0 ≤ᵐ[massMeasure] (stationaryResolvent (a • u + b • archDiagonalOperator u + c • primeShiftOperator u) : ℝ → ℝ)`. -/
theorem stationaryResolvent_combo_ae_nonneg_of_ae_nonneg {u : MassSpace}
    (hu : 0 ≤ᵐ[massMeasure] (u : ℝ → ℝ)) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ᵐ[massMeasure]
      (stationaryResolvent (a • u + b • archDiagonalOperator u + c • primeShiftOperator u) : ℝ → ℝ) := by
  set w := a • u + b • archDiagonalOperator u + c • primeShiftOperator u
  set v := (negGraph (stationaryGraphLift w)).val.fst
  have hv : 0 ≤ᵐ[massMeasure] (v : ℝ → ℝ) := negGraph_fst_ae_nonneg (stationaryGraphLift w)
  have hvu : 0 ≤ ⟪v, u⟫_ℝ := inner_massSpace_nonneg_of_ae_nonneg hv hu
  have hv_arch : 0 ≤ ⟪v, archDiagonalOperator u⟫_ℝ :=
    inner_massSpace_nonneg_of_ae_nonneg hv (archDiagonalOperator_ae_nonneg_of_ae_nonneg hu)
  have hv_prime : 0 ≤ ⟪v, primeShiftOperator u⟫_ℝ := by
    rw [real_inner_comm]
    exact inner_primeShiftOperator_nonneg_of_ae_nonneg hu hv
  have hvw : 0 ≤ ⟪v, w⟫_ℝ := by
    change 0 ≤ ⟪v, a • u + b • archDiagonalOperator u + c • primeShiftOperator u⟫_ℝ
    rw [inner_add_right, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_right]
    positivity
  exact (negGraph_stationaryGraphLift_eq_zero_of_inner_nonneg hvw).2.2.2

/-! ## Section 3: Cross-Lobe Positivity and Modulus Domination of `stationaryResolvent` on `SourceGraph` -/

/-- For all `p, q : SourceGraph`, `0 ≤ ⟪stationaryResolvent (posGraph p).val.fst, (negGraph q).val.fst⟫_ℝ`. -/
theorem inner_stationaryResolvent_posGraph_negGraph_nonneg (p q : SourceGraph) :
    0 ≤ ⟪stationaryResolvent (posGraph p).val.fst, (negGraph q).val.fst⟫_ℝ :=
  inner_massSpace_nonneg_of_ae_nonneg
    (stationaryResolvent_ae_nonneg_of_ae_nonneg (posGraph_fst_ae_nonneg p))
    (negGraph_fst_ae_nonneg q)

/-- For all `p, q : SourceGraph`, `0 ≤ ⟪stationaryResolvent (posGraph p).val.fst, stationaryResolvent (negGraph q).val.fst⟫_ℝ`. -/
theorem inner_stationaryResolvent_posGraph_stationaryResolvent_negGraph_nonneg (p q : SourceGraph) :
    0 ≤ ⟪stationaryResolvent (posGraph p).val.fst, stationaryResolvent (negGraph q).val.fst⟫_ℝ :=
  inner_massSpace_nonneg_of_ae_nonneg
    (stationaryResolvent_ae_nonneg_of_ae_nonneg (posGraph_fst_ae_nonneg p))
    (stationaryResolvent_ae_nonneg_of_ae_nonneg (negGraph_fst_ae_nonneg q))

/-- **Universal Stationary Resolvent Nodal Contraction Inequality**:
for every `p : SourceGraph`,
`⟪stationaryResolvent p.val.fst, p.val.fst⟫_ℝ ≤ ⟪stationaryResolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ`. -/
theorem inner_stationaryResolvent_self_le_absGraph (p : SourceGraph) :
    ⟪stationaryResolvent p.val.fst, p.val.fst⟫_ℝ ≤
      ⟪stationaryResolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ := by
  have h1 := inner_stationaryResolvent_absGraph_sub_self p
  have h2 := inner_stationaryResolvent_posGraph_negGraph_nonneg p p
  linarith

/-- **Pointwise Modulus Domination of `stationaryResolvent` on `SourceGraph`**:
for every `p : SourceGraph`,
`(fun x => |stationaryResolvent p.val.fst x|) ≤ᵐ[massMeasure] (stationaryResolvent (absGraph p).val.fst : ℝ → ℝ)`. -/
theorem abs_stationaryResolvent_ae_le_stationaryResolvent_absGraph (p : SourceGraph) :
    (fun x => |stationaryResolvent p.val.fst x|) ≤ᵐ[massMeasure]
      (stationaryResolvent (absGraph p).val.fst : ℝ → ℝ) := by
  have hadd : (absGraph p).val.fst = (posGraph p).val.fst + (negGraph p).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_add_negGraph p).symm
  have hsub : p.val.fst = (posGraph p).val.fst - (negGraph p).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_sub_negGraph p).symm
  have hres_add : stationaryResolvent (absGraph p).val.fst =
      stationaryResolvent (posGraph p).val.fst + stationaryResolvent (negGraph p).val.fst := by
    rw [hadd, map_add]
  have hres_sub : stationaryResolvent p.val.fst =
      stationaryResolvent (posGraph p).val.fst - stationaryResolvent (negGraph p).val.fst := by
    rw [hsub, map_sub]
  have hpos_nn := stationaryResolvent_ae_nonneg_of_ae_nonneg (posGraph_fst_ae_nonneg p)
  have hneg_nn := stationaryResolvent_ae_nonneg_of_ae_nonneg (negGraph_fst_ae_nonneg p)
  have hcoe_add : (stationaryResolvent (absGraph p).val.fst : ℝ → ℝ) =ᵐ[massMeasure]
      fun x => stationaryResolvent (posGraph p).val.fst x +
        stationaryResolvent (negGraph p).val.fst x := by
    rw [hres_add]
    exact Lp.coeFn_add _ _
  have hcoe_sub : (stationaryResolvent p.val.fst : ℝ → ℝ) =ᵐ[massMeasure]
      fun x => stationaryResolvent (posGraph p).val.fst x -
        stationaryResolvent (negGraph p).val.fst x := by
    rw [hres_sub]
    exact Lp.coeFn_sub _ _
  filter_upwards [hpos_nn, hneg_nn, hcoe_add, hcoe_sub] with x hxp hxn hca hcs
  have hxp' : 0 ≤ stationaryResolvent (posGraph p).val.fst x := hxp
  have hxn' : 0 ≤ stationaryResolvent (negGraph p).val.fst x := hxn
  rw [hca, hcs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Norm-Squared Polarization and Domination of `stationaryResolvent` on `SourceGraph`**:
for every `p : SourceGraph`,
`‖stationaryResolvent (absGraph p).val.fst‖ ^ 2 - ‖stationaryResolvent p.val.fst‖ ^ 2 = 4 * ⟪stationaryResolvent (posGraph p).val.fst, stationaryResolvent (negGraph p).val.fst⟫_ℝ`
and `‖stationaryResolvent p.val.fst‖ ^ 2 ≤ ‖stationaryResolvent (absGraph p).val.fst‖ ^ 2`. -/
theorem norm_stationaryResolvent_absGraph_sq_sub_self_sq (p : SourceGraph) :
    ‖stationaryResolvent (absGraph p).val.fst‖ ^ 2 - ‖stationaryResolvent p.val.fst‖ ^ 2 =
        4 * ⟪stationaryResolvent (posGraph p).val.fst,
          stationaryResolvent (negGraph p).val.fst⟫_ℝ ∧
      ‖stationaryResolvent p.val.fst‖ ^ 2 ≤ ‖stationaryResolvent (absGraph p).val.fst‖ ^ 2 := by
  have hadd : (absGraph p).val.fst = (posGraph p).val.fst + (negGraph p).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_add_negGraph p).symm
  have hsub : p.val.fst = (posGraph p).val.fst - (negGraph p).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_sub_negGraph p).symm
  have heq : ‖stationaryResolvent (absGraph p).val.fst‖ ^ 2 -
      ‖stationaryResolvent p.val.fst‖ ^ 2 =
      4 * ⟪stationaryResolvent (posGraph p).val.fst,
        stationaryResolvent (negGraph p).val.fst⟫_ℝ := by
    rw [hadd, hsub, map_add, map_sub, norm_add_sq_real, norm_sub_sq_real]
    ring
  have hnn := inner_stationaryResolvent_posGraph_stationaryResolvent_negGraph_nonneg p p
  exact ⟨heq, by linarith⟩

/-! ## Section 4: The Common Nodal Defect Graph `nodalDefectGraph` and Pointwise Lobe Sub-Invariance -/

/-- The stationary collar potential operator associated with spectral parameter `μ : ℝ`:
`stationaryCollarPotential μ u = ((1 - μ) / μ) • u + archDiagonalOperator u + primeShiftOperator u`. -/
def stationaryCollarPotential (μ : ℝ) (u : MassSpace) : MassSpace :=
  ((1 - μ) / μ) • u + archDiagonalOperator u + primeShiftOperator u

theorem stationaryCollarPotential_add (μ : ℝ) (u v : MassSpace) :
    stationaryCollarPotential μ (u + v) =
      stationaryCollarPotential μ u + stationaryCollarPotential μ v := by
  unfold stationaryCollarPotential
  rw [smul_add, map_add, map_add]
  abel

theorem stationaryCollarPotential_sub (μ : ℝ) (u v : MassSpace) :
    stationaryCollarPotential μ (u - v) =
      stationaryCollarPotential μ u - stationaryCollarPotential μ v := by
  unfold stationaryCollarPotential
  rw [smul_sub, map_sub, map_sub]
  abel

theorem stationaryGraphLift_add (u v : MassSpace) :
    stationaryGraphLift (u + v) = stationaryGraphLift u + stationaryGraphLift v := by
  unfold stationaryGraphLift
  rw [map_add, map_add]

theorem stationaryGraphLift_sub (u v : MassSpace) :
    stationaryGraphLift (u - v) = stationaryGraphLift u - stationaryGraphLift v := by
  unfold stationaryGraphLift
  rw [map_sub, map_sub]

/-- For every `v : MassSpace` and `p : SourceGraph`,
`⟪fullGroundEquiv (stationaryGraphLift v), fullGroundEquiv p⟫_ℝ = ⟪v, p.val.fst⟫_ℝ`. -/
theorem inner_fullGroundEquiv_stationaryGraphLift (v : MassSpace) (p : SourceGraph) :
    ⟪fullGroundEquiv (stationaryGraphLift v), fullGroundEquiv p⟫_ℝ = ⟪v, p.val.fst⟫_ℝ := by
  rw [fullGroundEquiv_stationaryGraphLift, inner_stationaryRieszLift, fullGroundEquiv_source]
  rfl

/-- For every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`q = stationaryGraphLift (stationaryCollarPotential μ q.val.fst)`. -/
theorem rieszLift_eq_stationaryGraphLift_stationaryCollarPotential_of_eigenvector
    {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace} (heig : resolvent w = μ • w) :
    rieszLift w = stationaryGraphLift (stationaryCollarPotential μ (rieszLift w).val.fst) := by
  set q := rieszLift w
  have h1 := (sourcePair_eq_inner_iff_stationaryRieszLift q
    (((1 - 2 * μ) / μ) • q.val.fst)).mp
    (sourcePair_rieszLift_eq_inner_of_eigenvector hμ heig)
  have hcomb : q.val.fst + archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst +
      ((1 - 2 * μ) / μ) • q.val.fst = stationaryCollarPotential μ q.val.fst := by
    unfold stationaryCollarPotential
    have hsmul : q.val.fst + ((1 - 2 * μ) / μ) • q.val.fst = ((1 - μ) / μ) • q.val.fst := by
      nth_rw 1 [← one_smul ℝ q.val.fst]
      rw [← add_smul]
      congr 1
      field_simp [hμ]
      ring
    calc q.val.fst + archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst +
          ((1 - 2 * μ) / μ) • q.val.fst
        = (q.val.fst + ((1 - 2 * μ) / μ) • q.val.fst) +
            archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst := by abel
      _ = ((1 - μ) / μ) • q.val.fst +
            archDiagonalOperator q.val.fst + primeShiftOperator q.val.fst := by rw [hsmul]
  rw [hcomb] at h1
  unfold stationaryGraphLift
  rw [← h1, fullGroundEquiv.symm_apply_apply]

/-- **The Nodal Defect Graph `nodalDefectGraph`**:
for any `μ : ℝ` and `q : SourceGraph`,
`nodalDefectGraph μ q = stationaryGraphLift (stationaryCollarPotential μ (posGraph q).val.fst) - posGraph q`. -/
def nodalDefectGraph (μ : ℝ) (q : SourceGraph) : SourceGraph :=
  stationaryGraphLift (stationaryCollarPotential μ (posGraph q).val.fst) - posGraph q

/-- **Common Nodal Defect Graph Identity for `resolvent` Eigenvectors**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`, the positive and
negative lobes share the exact same nodal defect graph:
`nodalDefectGraph μ q = stationaryGraphLift (stationaryCollarPotential μ (negGraph q).val.fst) - negGraph q`. -/
theorem nodalDefectGraph_eq_negGraph_defect_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) :
    let q := rieszLift w
    nodalDefectGraph μ q =
      stationaryGraphLift (stationaryCollarPotential μ (negGraph q).val.fst) - negGraph q := by
  intro q
  have hq := rieszLift_eq_stationaryGraphLift_stationaryCollarPotential_of_eigenvector hμ heig
  change q = stationaryGraphLift (stationaryCollarPotential μ q.val.fst) at hq
  have hsub_fst : q.val.fst = (posGraph q).val.fst - (negGraph q).val.fst :=
    congrArg (fun r : SourceGraph => r.val.fst) (posGraph_sub_negGraph q).symm
  rw [hsub_fst, stationaryCollarPotential_sub, stationaryGraphLift_sub] at hq
  have hq' : posGraph q - negGraph q =
      stationaryGraphLift (stationaryCollarPotential μ (posGraph q).val.fst) -
        stationaryGraphLift (stationaryCollarPotential μ (negGraph q).val.fst) :=
    (posGraph_sub_negGraph q).trans hq
  unfold nodalDefectGraph
  calc stationaryGraphLift (stationaryCollarPotential μ (posGraph q).val.fst) - posGraph q
      = (stationaryGraphLift (stationaryCollarPotential μ (posGraph q).val.fst) -
          stationaryGraphLift (stationaryCollarPotential μ (negGraph q).val.fst)) -
          (posGraph q - negGraph q) +
          (stationaryGraphLift (stationaryCollarPotential μ (negGraph q).val.fst) - negGraph q) := by
        abel
    _ = stationaryGraphLift (stationaryCollarPotential μ (negGraph q).val.fst) - negGraph q := by
        rw [← hq', sub_self, zero_add]

/-- **Almost-Everywhere Nonnegativity of `nodalDefectGraph` and Pointwise Lobe Sub-Invariance**:
for every eigenvector `resolvent w = μ • w` with `0 < μ` and `μ ≤ 1` and `q = rieszLift w`:
1. `0 ≤ᵐ[massMeasure] ((nodalDefectGraph μ q).val.fst : ℝ → ℝ)`,
2. `((posGraph q).val.fst : ℝ → ℝ) ≤ᵐ[massMeasure] (stationaryResolvent (stationaryCollarPotential μ (posGraph q).val.fst) : ℝ → ℝ)`,
3. `((negGraph q).val.fst : ℝ → ℝ) ≤ᵐ[massMeasure] (stationaryResolvent (stationaryCollarPotential μ (negGraph q).val.fst) : ℝ → ℝ)`. -/
theorem nodalDefectGraph_fst_ae_nonneg_and_lobe_subinvariance_of_eigenvector
    {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w
    0 ≤ᵐ[massMeasure] ((nodalDefectGraph μ q).val.fst : ℝ → ℝ) ∧
      ((posGraph q).val.fst : ℝ → ℝ) ≤ᵐ[massMeasure]
        (stationaryResolvent (stationaryCollarPotential μ (posGraph q).val.fst) : ℝ → ℝ) ∧
      ((negGraph q).val.fst : ℝ → ℝ) ≤ᵐ[massMeasure]
        (stationaryResolvent (stationaryCollarPotential μ (negGraph q).val.fst) : ℝ → ℝ) := by
  intro q
  have ha : 0 ≤ (1 - μ) / μ := div_nonneg (sub_nonneg.mpr hμ1) hμ0.le
  have hpos_res_nn : 0 ≤ᵐ[massMeasure]
      (stationaryResolvent (stationaryCollarPotential μ (posGraph q).val.fst) : ℝ → ℝ) := by
    simpa [stationaryCollarPotential, one_smul] using
      stationaryResolvent_combo_ae_nonneg_of_ae_nonneg (posGraph_fst_ae_nonneg q)
        ha zero_le_one zero_le_one
  have hneg_res_nn : 0 ≤ᵐ[massMeasure]
      (stationaryResolvent (stationaryCollarPotential μ (negGraph q).val.fst) : ℝ → ℝ) := by
    simpa [stationaryCollarPotential, one_smul] using
      stationaryResolvent_combo_ae_nonneg_of_ae_nonneg (negGraph_fst_ae_nonneg q)
        ha zero_le_one zero_le_one
  have hdef_pos : (nodalDefectGraph μ q).val.fst =
      stationaryResolvent (stationaryCollarPotential μ (posGraph q).val.fst) -
        (posGraph q).val.fst := by
    change (stationaryGraphLift (stationaryCollarPotential μ (posGraph q).val.fst)).val.fst -
      (posGraph q).val.fst = _
    rw [stationaryGraphLift_fst]
  have hdef_neg : (nodalDefectGraph μ q).val.fst =
      stationaryResolvent (stationaryCollarPotential μ (negGraph q).val.fst) -
        (negGraph q).val.fst := by
    have heq := congrArg (fun r : SourceGraph => r.val.fst)
      (nodalDefectGraph_eq_negGraph_defect_of_eigenvector hμ0.ne' heig)
    change (nodalDefectGraph μ q).val.fst =
      (stationaryGraphLift (stationaryCollarPotential μ (negGraph q).val.fst)).val.fst -
        (negGraph q).val.fst at heq
    rwa [stationaryGraphLift_fst] at heq
  have hcoe_pos : ((nodalDefectGraph μ q).val.fst : ℝ → ℝ) =ᵐ[massMeasure]
      fun x => stationaryResolvent (stationaryCollarPotential μ (posGraph q).val.fst) x -
        (posGraph q).val.fst x := by
    rw [hdef_pos]
    exact Lp.coeFn_sub _ _
  have hcoe_neg : ((nodalDefectGraph μ q).val.fst : ℝ → ℝ) =ᵐ[massMeasure]
      fun x => stationaryResolvent (stationaryCollarPotential μ (negGraph q).val.fst) x -
        (negGraph q).val.fst x := by
    rw [hdef_neg]
    exact Lp.coeFn_sub _ _
  have hdef_nn : 0 ≤ᵐ[massMeasure] ((nodalDefectGraph μ q).val.fst : ℝ → ℝ) := by
    filter_upwards [hpos_res_nn, hneg_res_nn, hcoe_pos, hcoe_neg,
      posGraph_fst_ae q, negGraph_fst_ae q] with x hpr hnr hcp hcn hp hn
    change 0 ≤ (nodalDefectGraph μ q).val.fst x
    have hmul := mul_eq_zero.mp (posFun_mul_negFun (q.val.fst x))
    rcases hmul with hp0 | hn0
    · rw [hcp, hp, hp0, sub_zero]
      exact hpr
    · rw [hcn, hn, hn0, sub_zero]
      exact hnr
  have hle_pos : ((posGraph q).val.fst : ℝ → ℝ) ≤ᵐ[massMeasure]
      (stationaryResolvent (stationaryCollarPotential μ (posGraph q).val.fst) : ℝ → ℝ) := by
    filter_upwards [hdef_nn, hcoe_pos] with x hd hcp
    have hd' : 0 ≤ (nodalDefectGraph μ q).val.fst x := hd
    linarith [hcp]
  have hle_neg : ((negGraph q).val.fst : ℝ → ℝ) ≤ᵐ[massMeasure]
      (stationaryResolvent (stationaryCollarPotential μ (negGraph q).val.fst) : ℝ → ℝ) := by
    filter_upwards [hdef_nn, hcoe_neg] with x hd hcn
    have hd' : 0 ≤ (nodalDefectGraph μ q).val.fst x := hd
    linarith [hcn]
  exact ⟨hdef_nn, hle_pos, hle_neg⟩

/-- **Exact `stationaryGroundGraph` Pairings, Orthogonality, and Cauchy–Schwarz Lower Bound of `nodalDefectGraph`**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`:
1. `⟪fullGroundEquiv (nodalDefectGraph μ q), fullGroundEquiv (posGraph q)⟫_ℝ = -sourcePair (posGraph q) (negGraph q)`,
2. `⟪fullGroundEquiv (nodalDefectGraph μ q), fullGroundEquiv (negGraph q)⟫_ℝ = -sourcePair (posGraph q) (negGraph q)`,
3. `⟪fullGroundEquiv (nodalDefectGraph μ q), fullGroundEquiv q⟫_ℝ = 0`,
4. `⟪fullGroundEquiv (nodalDefectGraph μ q), fullGroundEquiv (absGraph q)⟫_ℝ = -2 * sourcePair (posGraph q) (negGraph q)`,
5. `4 * sourcePair (posGraph q) (negGraph q) ^ 2 ≤ (‖(nodalDefectGraph μ q).val.fst‖ ^ 2 + stationaryEnergy (thetaProduct (nodalDefectGraph μ q).val.fst)) * (‖q.val.fst‖ ^ 2 + stationaryEnergy (thetaProduct (absGraph q).val.fst))`. -/
theorem inner_fullGroundEquiv_nodalDefectGraph_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) :
    let q := rieszLift w
    ⟪fullGroundEquiv (nodalDefectGraph μ q), fullGroundEquiv (posGraph q)⟫_ℝ =
        -sourcePair (posGraph q) (negGraph q) ∧
      ⟪fullGroundEquiv (nodalDefectGraph μ q), fullGroundEquiv (negGraph q)⟫_ℝ =
        -sourcePair (posGraph q) (negGraph q) ∧
      ⟪fullGroundEquiv (nodalDefectGraph μ q), fullGroundEquiv q⟫_ℝ = 0 ∧
      ⟪fullGroundEquiv (nodalDefectGraph μ q), fullGroundEquiv (absGraph q)⟫_ℝ =
        -2 * sourcePair (posGraph q) (negGraph q) ∧
      4 * sourcePair (posGraph q) (negGraph q) ^ 2 ≤
        (‖(nodalDefectGraph μ q).val.fst‖ ^ 2 +
            stationaryEnergy (thetaProduct (nodalDefectGraph μ q).val.fst)) *
          (‖q.val.fst‖ ^ 2 + stationaryEnergy (thetaProduct (absGraph q).val.fst)) := by
  intro q
  have hpair := neg_sourcePair_posGraph_negGraph_eq_stationary_add_primeShift q
  have hneg : ⟪fullGroundEquiv (nodalDefectGraph μ q), fullGroundEquiv (negGraph q)⟫_ℝ =
      -sourcePair (posGraph q) (negGraph q) := by
    unfold nodalDefectGraph stationaryCollarPotential
    rw [map_sub, inner_sub_left, inner_fullGroundEquiv_stationaryGraphLift,
      inner_add_left, inner_add_left, real_inner_smul_left,
      inner_posGraph_negGraph_fst, mul_zero, zero_add,
      inner_archDiagonalOperator_posGraph_negGraph, zero_add,
      inner_fullGroundEquiv_posGraph_negGraph_eq_snd]
    linarith
  have hpos : ⟪fullGroundEquiv (nodalDefectGraph μ q), fullGroundEquiv (posGraph q)⟫_ℝ =
      -sourcePair (posGraph q) (negGraph q) := by
    have hdef : nodalDefectGraph μ q =
        stationaryGraphLift (stationaryCollarPotential μ (negGraph q).val.fst) - negGraph q :=
      nodalDefectGraph_eq_negGraph_defect_of_eigenvector hμ heig
    rw [hdef]
    unfold stationaryCollarPotential
    rw [map_sub, inner_sub_left, inner_fullGroundEquiv_stationaryGraphLift,
      inner_add_left, inner_add_left, real_inner_smul_left,
      real_inner_comm (posGraph q).val.fst (negGraph q).val.fst,
      inner_posGraph_negGraph_fst, mul_zero, zero_add,
      archDiagonalOperator_symmetric (negGraph q).val.fst (posGraph q).val.fst,
      real_inner_comm (archDiagonalOperator (posGraph q).val.fst) (negGraph q).val.fst,
      inner_archDiagonalOperator_posGraph_negGraph, zero_add,
      primeShiftOperator_symmetric (negGraph q).val.fst (posGraph q).val.fst,
      real_inner_comm (primeShiftOperator (posGraph q).val.fst) (negGraph q).val.fst,
      real_inner_comm (fullGroundEquiv (posGraph q)) (fullGroundEquiv (negGraph q)),
      inner_fullGroundEquiv_posGraph_negGraph_eq_snd]
    linarith
  have hq : ⟪fullGroundEquiv (nodalDefectGraph μ q), fullGroundEquiv q⟫_ℝ = 0 := by
    rw [← fullGroundEquiv_posGraph_sub_negGraph q, inner_sub_right, hpos, hneg, sub_self]
  have habs : ⟪fullGroundEquiv (nodalDefectGraph μ q), fullGroundEquiv (absGraph q)⟫_ℝ =
      -2 * sourcePair (posGraph q) (negGraph q) := by
    rw [← fullGroundEquiv_posGraph_add_negGraph q, inner_add_right, hpos, hneg]
    ring
  have hcs : 4 * sourcePair (posGraph q) (negGraph q) ^ 2 ≤
      (‖(nodalDefectGraph μ q).val.fst‖ ^ 2 +
          stationaryEnergy (thetaProduct (nodalDefectGraph μ q).val.fst)) *
        (‖q.val.fst‖ ^ 2 + stationaryEnergy (thetaProduct (absGraph q).val.fst)) := by
    have hnn : 0 ≤ -2 * sourcePair (posGraph q) (negGraph q) := by
      have hsp := sourcePair_posGraph_negGraph_nonpos q
      linarith
    have h1 : -2 * sourcePair (posGraph q) (negGraph q) ≤
        ‖fullGroundEquiv (nodalDefectGraph μ q)‖ * ‖fullGroundEquiv (absGraph q)‖ := by
      rw [← habs]
      exact real_inner_le_norm _ _
    have hsq := pow_le_pow_left₀ hnn h1 2
    have hpow : (-2 * sourcePair (posGraph q) (negGraph q)) ^ 2 =
        4 * sourcePair (posGraph q) (negGraph q) ^ 2 := by ring
    rw [hpow, mul_pow, norm_fullGroundEquiv_sq, norm_fullGroundEquiv_sq,
      norm_absGraph_fst_sq] at hsq
    exact hsq
  exact ⟨hpos, hneg, hq, habs, hcs⟩

end GaloisForLFunctions.BiScaleUncertainty
