import GaloisForLFunctions.RHTower.CHMDEigenvectorNodalLobeEnergiesAndPrimitiveLobeBounds

/-!
# Stationary Resolvent Cauchy–Schwarz, Rayleigh-to-Energy Bounds, and Stationary Nodal Boost

This module establishes the stationary-coordinates counterparts of the resolvent Cauchy–Schwarz
inequality, the Rayleigh-to-energy lower bound, the nodal polarization identity, and the Courant
nodal Rayleigh boost for `stationaryResolvent` on `MassSpace` and `SourceGraph`:

1. **Stationary Graph Norm and `stationaryResolvent` Cauchy–Schwarz Inequality**:
   - `norm_stationaryGroundGraph_sq`: for every `r : stationaryGroundGraph`,
     `‖r‖ ^ 2 = ‖r.val.fst‖ ^ 2 + stationaryEnergy (thetaProduct r.val.fst)`.
   - `norm_fullGroundEquiv_sq`: for every `p : SourceGraph`,
     `‖fullGroundEquiv p‖ ^ 2 = ‖p.val.fst‖ ^ 2 + stationaryEnergy (thetaProduct p.val.fst)`.
   - `inner_stationaryResolvent_self`: for every `w : MassSpace`,
     `⟪stationaryResolvent w, w⟫_ℝ = ‖stationaryRieszLift w‖ ^ 2`.
   - `norm_fst_pow_four_le_inner_stationaryResolvent_mul`: for every `p : SourceGraph`,
     `‖p.val.fst‖ ^ 4 ≤ ⟪stationaryResolvent p.val.fst, p.val.fst⟫_ℝ * (stationaryEnergy (thetaProduct p.val.fst) + ‖p.val.fst‖ ^ 2)`.
   - `stationaryEnergy_ge_of_inner_stationaryResolvent_le`: for any `p : SourceGraph` and `0 < σ_max`,
     if `⟪stationaryResolvent p.val.fst, p.val.fst⟫_ℝ ≤ σ_max * ‖p.val.fst‖ ^ 2`, then
     `((1 - σ_max) / σ_max) * ‖p.val.fst‖ ^ 2 ≤ stationaryEnergy (thetaProduct p.val.fst)`.

2. **Stationary Resolvent Nodal Polarization and Contraction-to-Energy Inequalities**:
   - `inner_stationaryResolvent_absGraph_sub_self`:
     `⟪stationaryResolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ - ⟪stationaryResolvent p.val.fst, p.val.fst⟫_ℝ = 4 * ⟪stationaryResolvent (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`.
   - `stationary_nodal_cross_le_of_absGraph_rayleigh_le`: because `stationaryGenerator` has no
     constant zero mode, applying `stationaryEnergy_ge_of_inner_stationaryResolvent_le` directly to
     `absGraph p` produces no `oneL` ground-projection error term:
     if `⟪stationaryResolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ ≤ σ_max * ‖p.val.fst‖ ^ 2`,
     then
     `((1 - σ_max) / σ_max) * ‖p.val.fst‖ ^ 2 - 4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ ≤ stationaryEnergy (thetaProduct p.val.fst)`,
     and for any bound-state vector (`sourceEnergy p ≤ 0`),
     `((1 - σ_max) / σ_max) * ‖p.val.fst‖ ^ 2 - 4 * sourcePair (posGraph p) (negGraph p) ≤ archGroundConstant * ‖thetaToVolume p.val.fst‖ ^ 2 + ⟪primeShiftOperator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ`.

3. **Stationary Eigenvector Nodal identities and Strict Rayleigh Boost**:
   for every eigenvector `stationaryResolvent w = σ • w` (`σ ≠ 0`) with
   `p = fullGroundEquiv.symm (stationaryRieszLift w)`:
   - `stationaryEnergy (thetaProduct p.val.fst) = ((1 - σ) / σ) * ‖p.val.fst‖ ^ 2`,
   - `stationaryEnergy (thetaProduct (posGraph p).val.fst) = ((1 - σ) / σ) * ‖(posGraph p).val.fst‖ ^ 2 + ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ`,
   - `stationaryEnergy (thetaProduct (negGraph p).val.fst) = ((1 - σ) / σ) * ‖(negGraph p).val.fst‖ ^ 2 + ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ`,
   - and whenever `0 < σ` and `p` changes sign (`posGraph p ≠ 0` and `negGraph p ≠ 0`, in particular
     whenever `w ≠ 0` and `⟪w, oneL⟫_ℝ = 0`), both `(posGraph p).val.fst` and `(absGraph p).val.fst`
     have `stationaryResolvent` Rayleigh quotient strictly greater than `σ`:
     `σ * ‖(posGraph p).val.fst‖ ^ 2 < ⟪stationaryResolvent (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ`
     and
     `σ * ‖(absGraph p).val.fst‖ ^ 2 < ⟪stationaryResolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ`.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump CHMDTranslation ThetaSourceWard

/-! ## Section 1: Stationary Graph Norm and `stationaryResolvent` Cauchy–Schwarz Inequality -/

/-- For every `r : stationaryGroundGraph`,
`‖r‖ ^ 2 = ‖r.val.fst‖ ^ 2 + stationaryEnergy (thetaProduct r.val.fst)`. -/
theorem norm_stationaryGroundGraph_sq (r : stationaryGroundGraph) :
    ‖r‖ ^ 2 = ‖r.val.fst‖ ^ 2 + stationaryEnergy (thetaProduct r.val.fst) := by
  rw [← real_inner_self_eq_norm_sq, Submodule.coe_inner, WithLp.prod_inner_apply]
  change ⟪r.val.fst, r.val.fst⟫_ℝ + ⟪r.val.snd, r.val.snd⟫_ℝ = _
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, stationaryGround_edge_energy]

/-- For every `p : SourceGraph`,
`‖fullGroundEquiv p‖ ^ 2 = ‖p.val.fst‖ ^ 2 + stationaryEnergy (thetaProduct p.val.fst)`. -/
theorem norm_fullGroundEquiv_sq (p : SourceGraph) :
    ‖fullGroundEquiv p‖ ^ 2 = ‖p.val.fst‖ ^ 2 + stationaryEnergy (thetaProduct p.val.fst) := by
  have hp : (fullGroundEquiv p).val.fst = p.val.fst := fullGroundEquiv_source p
  rw [norm_stationaryGroundGraph_sq, hp]

/-- Symmetry of `stationaryResolvent` on `MassSpace`. -/
theorem stationaryResolvent_symm (u v : MassSpace) :
    ⟪stationaryResolvent u, v⟫_ℝ = ⟪u, stationaryResolvent v⟫_ℝ :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp stationaryResolvent_isSelfAdjoint u v

/-- For every `w : MassSpace`, `⟪stationaryResolvent w, w⟫_ℝ = ‖stationaryRieszLift w‖ ^ 2`. -/
theorem inner_stationaryResolvent_self (w : MassSpace) :
    ⟪stationaryResolvent w, w⟫_ℝ = ‖stationaryRieszLift w‖ ^ 2 := by
  rw [stationaryResolvent_symm, stationaryResolvent_apply,
    ← inner_stationaryRieszLift, real_inner_self_eq_norm_sq]

/-- **Stationary Graph Cauchy–Schwarz Inequality**:
for every `p : SourceGraph`,
`‖p.val.fst‖ ^ 4 ≤ ⟪stationaryResolvent p.val.fst, p.val.fst⟫_ℝ * (stationaryEnergy (thetaProduct p.val.fst) + ‖p.val.fst‖ ^ 2)`. -/
theorem norm_fst_pow_four_le_inner_stationaryResolvent_mul (p : SourceGraph) :
    ‖p.val.fst‖ ^ 4 ≤
      ⟪stationaryResolvent p.val.fst, p.val.fst⟫_ℝ *
        (stationaryEnergy (thetaProduct p.val.fst) + ‖p.val.fst‖ ^ 2) := by
  have hp : stationaryGroundSourceMap (fullGroundEquiv p) = p.val.fst := fullGroundEquiv_source p
  have h1 : ‖p.val.fst‖ ^ 2 ≤ ‖stationaryRieszLift p.val.fst‖ * ‖fullGroundEquiv p‖ := by
    calc ‖p.val.fst‖ ^ 2 = ⟪p.val.fst, stationaryGroundSourceMap (fullGroundEquiv p)⟫_ℝ := by
          rw [hp, real_inner_self_eq_norm_sq]
      _ = ⟪stationaryRieszLift p.val.fst, fullGroundEquiv p⟫_ℝ :=
          (inner_stationaryRieszLift p.val.fst (fullGroundEquiv p)).symm
      _ ≤ ‖stationaryRieszLift p.val.fst‖ * ‖fullGroundEquiv p‖ :=
          real_inner_le_norm _ _
  have h2 : (‖p.val.fst‖ ^ 2) ^ 2 ≤ (‖stationaryRieszLift p.val.fst‖ * ‖fullGroundEquiv p‖) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  rw [← pow_mul, mul_pow, ← inner_stationaryResolvent_self, norm_fullGroundEquiv_sq,
    add_comm (‖p.val.fst‖ ^ 2)] at h2
  exact h2

/-- **Universal Stationary Rayleigh-to-Energy Lower Bound**:
for every `p : SourceGraph` and every `0 < σ_max`, if
`⟪stationaryResolvent p.val.fst, p.val.fst⟫_ℝ ≤ σ_max * ‖p.val.fst‖ ^ 2`, then
`((1 - σ_max) / σ_max) * ‖p.val.fst‖ ^ 2 ≤ stationaryEnergy (thetaProduct p.val.fst)`. -/
theorem stationaryEnergy_ge_of_inner_stationaryResolvent_le {p : SourceGraph} {σ_max : ℝ}
    (hσ : 0 < σ_max)
    (hray : ⟪stationaryResolvent p.val.fst, p.val.fst⟫_ℝ ≤ σ_max * ‖p.val.fst‖ ^ 2) :
    ((1 - σ_max) / σ_max) * ‖p.val.fst‖ ^ 2 ≤ stationaryEnergy (thetaProduct p.val.fst) := by
  by_cases h0 : ‖p.val.fst‖ = 0
  · have hnn : 0 ≤ stationaryEnergy (thetaProduct p.val.fst) := by
      have hp : (fullGroundEquiv p).val.fst = p.val.fst := fullGroundEquiv_source p
      rw [← hp, ← stationaryGround_edge_energy]
      exact sq_nonneg _
    rw [h0]
    nlinarith
  · have hpos : 0 < ‖p.val.fst‖ ^ 2 := sq_pos_of_ne_zero h0
    have hcs := norm_fst_pow_four_le_inner_stationaryResolvent_mul p
    have hnn : 0 ≤ stationaryEnergy (thetaProduct p.val.fst) + ‖p.val.fst‖ ^ 2 := by
      rw [add_comm, ← norm_fullGroundEquiv_sq]
      exact sq_nonneg _
    have hmul : ‖p.val.fst‖ ^ 4 ≤
        (σ_max * ‖p.val.fst‖ ^ 2) * (stationaryEnergy (thetaProduct p.val.fst) + ‖p.val.fst‖ ^ 2) :=
      hcs.trans (mul_le_mul_of_nonneg_right hray hnn)
    have hpow4 : ‖p.val.fst‖ ^ 4 = ‖p.val.fst‖ ^ 2 * ‖p.val.fst‖ ^ 2 := by ring
    have hle1 : ‖p.val.fst‖ ^ 2 ≤
        σ_max * (stationaryEnergy (thetaProduct p.val.fst) + ‖p.val.fst‖ ^ 2) := by
      nlinarith
    have hdiv : (1 / σ_max) * ‖p.val.fst‖ ^ 2 ≤
        stationaryEnergy (thetaProduct p.val.fst) + ‖p.val.fst‖ ^ 2 := by
      rw [one_div_mul_eq_div, div_le_iff₀' hσ]
      exact hle1
    have hid : ((1 - σ_max) / σ_max) * ‖p.val.fst‖ ^ 2 =
        (1 / σ_max) * ‖p.val.fst‖ ^ 2 - ‖p.val.fst‖ ^ 2 := by
      field_simp [hσ.ne']
    linarith

/-! ## Section 2: Stationary Resolvent Nodal Polarization and Contraction-to-Energy Bounds -/

/-- **Stationary Resolvent Nodal Polarization Identity**:
for every `p : SourceGraph`,
`⟪stationaryResolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ - ⟪stationaryResolvent p.val.fst, p.val.fst⟫_ℝ = 4 * ⟪stationaryResolvent (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`. -/
theorem inner_stationaryResolvent_absGraph_sub_self (p : SourceGraph) :
    ⟪stationaryResolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ -
        ⟪stationaryResolvent p.val.fst, p.val.fst⟫_ℝ =
      4 * ⟪stationaryResolvent (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  have hadd : (absGraph p).val.fst = (posGraph p).val.fst + (negGraph p).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_add_negGraph p).symm
  have hsub : p.val.fst = (posGraph p).val.fst - (negGraph p).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_sub_negGraph p).symm
  rw [hadd]
  conv_lhs => enter [2]; rw [hsub]
  rw [map_add, map_sub, inner_add_left, inner_add_right, inner_add_right,
    inner_sub_left, inner_sub_right, inner_sub_right,
    stationaryResolvent_symm (negGraph p).val.fst (posGraph p).val.fst,
    real_inner_comm (negGraph p).val.fst (stationaryResolvent (posGraph p).val.fst)]
  ring

/-- **Zero-Mode-Free Stationary Contraction Nodal Bound**:
for every `p : SourceGraph` and every `0 < σ_max`, if
`⟪stationaryResolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ ≤ σ_max * ‖p.val.fst‖ ^ 2`,
then
`((1 - σ_max) / σ_max) * ‖p.val.fst‖ ^ 2 - 4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ ≤ stationaryEnergy (thetaProduct p.val.fst)`. -/
theorem stationary_nodal_cross_le_of_absGraph_rayleigh_le {p : SourceGraph} {σ_max : ℝ}
    (hσ : 0 < σ_max)
    (hray : ⟪stationaryResolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ ≤
      σ_max * ‖p.val.fst‖ ^ 2) :
    ((1 - σ_max) / σ_max) * ‖p.val.fst‖ ^ 2 -
        4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ ≤
      stationaryEnergy (thetaProduct p.val.fst) := by
  have hray' : ⟪stationaryResolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ ≤
      σ_max * ‖(absGraph p).val.fst‖ ^ 2 := by
    rwa [norm_absGraph_fst_sq]
  have h1 := stationaryEnergy_ge_of_inner_stationaryResolvent_le hσ hray'
  rw [stationaryEnergy_absGraph_eq, norm_absGraph_fst_sq] at h1
  linarith

/-- **Zero-Mode-Free Stationary Nodal Bound on Bound-State Vectors (`sourceEnergy p ≤ 0`)**:
for every `p : SourceGraph` and every `0 < σ_max`, if
`⟪stationaryResolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ ≤ σ_max * ‖p.val.fst‖ ^ 2`,
then
`-sourceEnergy p + ((1 - σ_max) / σ_max) * ‖p.val.fst‖ ^ 2 - 4 * sourcePair (posGraph p) (negGraph p) ≤ archGroundConstant * ‖thetaToVolume p.val.fst‖ ^ 2 + ⟪primeShiftOperator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ`. -/
theorem stationary_nodal_cross_le_arch_add_primeShift_of_absGraph_rayleigh_le
    {p : SourceGraph} {σ_max : ℝ} (hσ : 0 < σ_max)
    (hray : ⟪stationaryResolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ ≤
      σ_max * ‖p.val.fst‖ ^ 2) :
    -sourceEnergy p + ((1 - σ_max) / σ_max) * ‖p.val.fst‖ ^ 2 -
        4 * sourcePair (posGraph p) (negGraph p) ≤
      archGroundConstant * ‖thetaToVolume p.val.fst‖ ^ 2 +
        ⟪primeShiftOperator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ := by
  have hray' : ⟪stationaryResolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ ≤
      σ_max * ‖(absGraph p).val.fst‖ ^ 2 := by
    rwa [norm_absGraph_fst_sq]
  have h1 := stationaryEnergy_ge_of_inner_stationaryResolvent_le hσ hray'
  have h2 := sourceEnergy_eq_stationary_sub_arch_sub_primeShift (absGraph p)
  rw [sourceEnergy_absGraph_eq, norm_thetaToVolume_absGraph_sq] at h2
  rw [norm_absGraph_fst_sq] at h1
  linarith

/-! ## Section 3: Stationary Eigenvector Nodal Identities and Strict Rayleigh Boost -/

/-- Canonical lift of a `MassSpace` vector `w` to `SourceGraph` via `stationaryRieszLift`:
`stationaryGraphLift w = fullGroundEquiv.symm (stationaryRieszLift w)`. -/
def stationaryGraphLift (w : MassSpace) : SourceGraph :=
  fullGroundEquiv.symm (stationaryRieszLift w)

theorem stationaryGraphLift_fst (w : MassSpace) :
    (stationaryGraphLift w).val.fst = stationaryResolvent w := by
  change sourceMap (fullGroundEquiv.symm (stationaryRieszLift w)) = stationaryResolvent w
  rw [fullGroundEquiv_symm_source, ← stationaryResolvent_apply]

theorem fullGroundEquiv_stationaryGraphLift (w : MassSpace) :
    fullGroundEquiv (stationaryGraphLift w) = stationaryRieszLift w :=
  fullGroundEquiv.apply_symm_apply (stationaryRieszLift w)

/-- For every `w : MassSpace` and `q : SourceGraph`,
`⟪(fullGroundEquiv q).val.snd, (stationaryRieszLift w).val.snd⟫_ℝ = ⟪q.val.fst, w - stationaryResolvent w⟫_ℝ`. -/
theorem inner_stationaryRieszLift_snd (w : MassSpace) (q : SourceGraph) :
    ⟪(fullGroundEquiv q).val.snd, (stationaryRieszLift w).val.snd⟫_ℝ =
      ⟪q.val.fst, w - stationaryResolvent w⟫_ℝ := by
  have h := inner_stationaryRieszLift w (fullGroundEquiv q)
  have hq : stationaryGroundSourceMap (fullGroundEquiv q) = q.val.fst := fullGroundEquiv_source q
  have hq' : (fullGroundEquiv q).val.fst = q.val.fst := fullGroundEquiv_source q
  have hw : (stationaryRieszLift w).val.fst = stationaryResolvent w := rfl
  rw [Submodule.coe_inner, WithLp.prod_inner_apply, hq] at h
  change ⟪(stationaryRieszLift w).val.fst, (fullGroundEquiv q).val.fst⟫_ℝ +
    ⟪(stationaryRieszLift w).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ = ⟪w, q.val.fst⟫_ℝ at h
  rw [hw, hq', real_inner_comm _ (stationaryResolvent w),
    real_inner_comm _ (stationaryRieszLift w).val.snd,
    real_inner_comm _ w] at h
  rw [inner_sub_right]
  linarith

/-- For every eigenvector `stationaryResolvent w = σ • w` (`σ ≠ 0`) with
`p = stationaryGraphLift w`, and every `q : SourceGraph`,
`⟪(fullGroundEquiv q).val.snd, (fullGroundEquiv p).val.snd⟫_ℝ = ((1 - σ) / σ) * ⟪q.val.fst, p.val.fst⟫_ℝ`. -/
theorem inner_stationary_snd_of_eigenvector {σ : ℝ} (hσ : σ ≠ 0) {w : MassSpace}
    (heig : stationaryResolvent w = σ • w) (q : SourceGraph) :
    ⟪(fullGroundEquiv q).val.snd, (fullGroundEquiv (stationaryGraphLift w)).val.snd⟫_ℝ =
      ((1 - σ) / σ) * ⟪q.val.fst, (stationaryGraphLift w).val.fst⟫_ℝ := by
  rw [fullGroundEquiv_stationaryGraphLift, inner_stationaryRieszLift_snd,
    stationaryGraphLift_fst, heig, real_inner_smul_right]
  have hw : w - σ • w = ((1 - σ) / σ) • (σ • w) := by
    rw [smul_smul, div_mul_cancel₀ _ hσ, sub_smul, one_smul]
  rw [hw, real_inner_smul_right, real_inner_smul_right]

/-- **Stationary Energy of an Eigenvector of `stationaryResolvent`**:
for every eigenvector `stationaryResolvent w = σ • w` (`σ ≠ 0`) with `p = stationaryGraphLift w`,
`stationaryEnergy (thetaProduct p.val.fst) = ((1 - σ) / σ) * ‖p.val.fst‖ ^ 2`. -/
theorem stationaryEnergy_of_eigenvector {σ : ℝ} (hσ : σ ≠ 0) {w : MassSpace}
    (heig : stationaryResolvent w = σ • w) :
    stationaryEnergy (thetaProduct (stationaryGraphLift w).val.fst) =
      ((1 - σ) / σ) * ‖(stationaryGraphLift w).val.fst‖ ^ 2 := by
  set p := stationaryGraphLift w
  have hp : (fullGroundEquiv p).val.fst = p.val.fst := fullGroundEquiv_source p
  rw [← hp, ← stationaryGround_edge_energy, ← real_inner_self_eq_norm_sq,
    inner_stationary_snd_of_eigenvector hσ heig p, hp, real_inner_self_eq_norm_sq]

/-- **Positive- and Negative-Lobe Stationary Energies of a `stationaryResolvent` Eigenvector**:
for every eigenvector `stationaryResolvent w = σ • w` (`σ ≠ 0`) with `p = stationaryGraphLift w`,
`stationaryEnergy (thetaProduct (posGraph p).val.fst) = ((1 - σ) / σ) * ‖(posGraph p).val.fst‖ ^ 2 + ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ`
and
`stationaryEnergy (thetaProduct (negGraph p).val.fst) = ((1 - σ) / σ) * ‖(negGraph p).val.fst‖ ^ 2 + ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ`. -/
theorem stationaryEnergy_posGraph_and_negGraph_of_eigenvector {σ : ℝ} (hσ : σ ≠ 0)
    {w : MassSpace} (heig : stationaryResolvent w = σ • w) :
    let p := stationaryGraphLift w
    stationaryEnergy (thetaProduct (posGraph p).val.fst) =
        ((1 - σ) / σ) * ‖(posGraph p).val.fst‖ ^ 2 +
          ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ ∧
      stationaryEnergy (thetaProduct (negGraph p).val.fst) =
        ((1 - σ) / σ) * ‖(negGraph p).val.fst‖ ^ 2 +
          ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ := by
  intro p
  have hsub : (fullGroundEquiv p).val.snd =
      (fullGroundEquiv (posGraph p)).val.snd - (fullGroundEquiv (negGraph p)).val.snd :=
    congrArg (fun r : stationaryGroundGraph => r.val.snd)
      (fullGroundEquiv_posGraph_sub_negGraph p).symm
  have hpos_fst : (fullGroundEquiv (posGraph p)).val.fst = (posGraph p).val.fst :=
    fullGroundEquiv_source (posGraph p)
  have hneg_fst : (fullGroundEquiv (negGraph p)).val.fst = (negGraph p).val.fst :=
    fullGroundEquiv_source (negGraph p)
  refine ⟨?_, ?_⟩
  · have h1 := inner_stationary_snd_of_eigenvector hσ heig (posGraph p)
    change ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv p).val.snd⟫_ℝ =
      ((1 - σ) / σ) * ⟪(posGraph p).val.fst, p.val.fst⟫_ℝ at h1
    rw [hsub, inner_sub_right, real_inner_self_eq_norm_sq, stationaryGround_edge_energy,
      hpos_fst, inner_posGraph_self_fst] at h1
    linarith
  · have h1 := inner_stationary_snd_of_eigenvector hσ heig (negGraph p)
    change ⟪(fullGroundEquiv (negGraph p)).val.snd, (fullGroundEquiv p).val.snd⟫_ℝ =
      ((1 - σ) / σ) * ⟪(negGraph p).val.fst, p.val.fst⟫_ℝ at h1
    rw [hsub, inner_sub_right,
      real_inner_comm (fullGroundEquiv (posGraph p)).val.snd (fullGroundEquiv (negGraph p)).val.snd,
      real_inner_self_eq_norm_sq, stationaryGround_edge_energy,
      hneg_fst, inner_negGraph_self_fst] at h1
    linarith

/-- **Strict `stationaryResolvent` Rayleigh Boost for Any Sign-Changing Eigenvector**:
for every eigenvector `stationaryResolvent w = σ • w` (`0 < σ`) with `p = stationaryGraphLift w`,
if `posGraph p ≠ 0` and `negGraph p ≠ 0` (in particular, whenever `w ≠ 0` and `⟪w, oneL⟫_ℝ = 0`),
both `(posGraph p).val.fst` and `(absGraph p).val.fst` have `stationaryResolvent` Rayleigh quotient
strictly greater than `σ`:
`σ * ‖(posGraph p).val.fst‖ ^ 2 < ⟪stationaryResolvent (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ`
and
`σ * ‖(absGraph p).val.fst‖ ^ 2 < ⟪stationaryResolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ`. -/
theorem stationary_rayleigh_posGraph_and_absGraph_gt_of_ne_zero {σ : ℝ} (hσ : 0 < σ)
    {w : MassSpace} (heig : stationaryResolvent w = σ • w)
    (hpos_ne : posGraph (stationaryGraphLift w) ≠ 0)
    (hneg_ne : negGraph (stationaryGraphLift w) ≠ 0) :
    let p := stationaryGraphLift w
    σ * ‖(posGraph p).val.fst‖ ^ 2 <
        ⟪stationaryResolvent (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ ∧
      σ * ‖(absGraph p).val.fst‖ ^ 2 <
        ⟪stationaryResolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ := by
  intro p
  have hcross_neg :
      ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ < 0 :=
    inner_fullGroundEquiv_posGraph_negGraph_snd_neg_of_ne_zero hpos_ne hneg_ne
  constructor
  · by_contra hle
    have hle' := not_lt.mp hle
    have hge := stationaryEnergy_ge_of_inner_stationaryResolvent_le hσ hle'
    have hpE := (stationaryEnergy_posGraph_and_negGraph_of_eigenvector hσ.ne' heig).1
    change stationaryEnergy (thetaProduct (posGraph p).val.fst) =
      ((1 - σ) / σ) * ‖(posGraph p).val.fst‖ ^ 2 +
        ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ at hpE
    linarith
  · by_contra hle
    have hle' := not_lt.mp hle
    have hge := stationaryEnergy_ge_of_inner_stationaryResolvent_le hσ hle'
    have haE := stationaryEnergy_absGraph_eq p
    have hpE := stationaryEnergy_of_eigenvector hσ.ne' heig
    change stationaryEnergy (thetaProduct p.val.fst) = ((1 - σ) / σ) * ‖p.val.fst‖ ^ 2 at hpE
    rw [norm_absGraph_fst_sq] at hge
    linarith

end RHTower.CHMDPolar
