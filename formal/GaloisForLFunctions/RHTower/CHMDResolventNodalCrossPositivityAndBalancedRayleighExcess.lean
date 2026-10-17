import GaloisForLFunctions.RHTower.CHMDBalancedNodalGraphAndGroundPerturbationResolvent

/-!
# Resolvent Nodal Cross-Positivity, Individual-Lobe Rayleigh Excess, and Doubly-Orthogonal Balanced Nodal Bounds

This module proves the exact `resolvent` quadratic-form identities for the positive lobe `posGraph q`,
negative lobe `negGraph q`, absolute contraction `absGraph q`, and balanced nodal graph
`balancedNodalGraph q` of any eigenvector `resolvent v = ν • v`, establishes the unconditional
quantitative lower bound
`0 ≤ -ν ^ 2 * sourcePair (posGraph q) (negGraph q) ≤ ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`
(strictly positive for every nonzero primitive eigenvector), and derives the doubly-orthogonal
Courant–Fischer nodal bounds on `primGraph (balancedNodalGraph q)`:

1. **Exact `resolvent` Quadratic-Form Identities on Nodal Lobes and `balancedNodalGraph`**:
   for every eigenvector `resolvent v = ν • v` with `q = rieszLift v`:
   - `inner_resolvent_posGraph_and_negGraph_of_eigenvector`:
     `⟪resolvent (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ = ν * ‖(posGraph q).val.fst‖ ^ 2 + ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`
     and
     `⟪resolvent (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ = ν * ‖(negGraph q).val.fst‖ ^ 2 + ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`.
   - `inner_resolvent_absGraph_of_eigenvector`:
     `⟪resolvent (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ = ν * ‖q.val.fst‖ ^ 2 + 4 * ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`.
   - `inner_resolvent_balancedNodalGraph_of_eigenvector`:
     `⟪resolvent (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ = ν * ‖(balancedNodalGraph q).val.fst‖ ^ 2 + ‖q.val.fst‖ ^ 4 * ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`.
   - `inner_resolvent_primGraph_balancedNodalGraph_rayleigh_excess_of_primitive_eigenvector`:
     when `⟪v, oneL⟫_ℝ = 0`,
     `⟪resolvent (primGraph (balancedNodalGraph q)).val.fst, (primGraph (balancedNodalGraph q)).val.fst⟫_ℝ - ν * ‖(primGraph (balancedNodalGraph q)).val.fst‖ ^ 2 = ‖q.val.fst‖ ^ 4 * (⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ - ((1 - ν) / 2) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2)`.

2. **Quantitative Lower Bound and Strict Positivity of `⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`**:
   - `neg_sq_mul_sourcePair_le_inner_resolvent_posGraph_negGraph_mul`:
     for every eigenvector `resolvent v = ν • v` (`0 < ν`) with `q = rieszLift v`,
     `-ν ^ 2 * ‖q.val.fst‖ ^ 2 * sourcePair (posGraph q) (negGraph q) ≤ ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ * (‖q.val.fst‖ ^ 2 + 4 * ν * sourcePair (posGraph q) (negGraph q))`.
   - `neg_sq_mul_sourcePair_le_inner_resolvent_posGraph_negGraph`:
     `0 ≤ -ν ^ 2 * sourcePair (posGraph q) (negGraph q) ≤ ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`.
   - `inner_resolvent_posGraph_negGraph_pos_of_primitive_eigenvector`:
     for every nonzero primitive eigenvector (`0 < ν`, `v ≠ 0`, `⟪v, oneL⟫_ℝ = 0`),
     `0 < -ν ^ 2 * sourcePair (posGraph q) (negGraph q) ≤ ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`.

3. **Doubly-Orthogonal Courant–Fischer Nodal Bounds on `primGraph (balancedNodalGraph q)`**:
   - `eigenvector_balancedNodalGraph_nodal_cross_le_spectral_gap_mul_oneL_sq` and
     `eigenvector_balancedNodalGraph_resolvent_cross_le_of_rayleigh_le`:
     for every primitive eigenvector `resolvent v = ν • v` (`0 < ν`, `⟪v, oneL⟫_ℝ = 0`) with
     `q = rieszLift v` and `u_bal = (primGraph (balancedNodalGraph q)).val.fst` (which is
     orthogonal to both `oneL` and `v`), any Rayleigh bound `⟪resolvent u_bal, u_bal⟫_ℝ ≤ μ_2 * ‖u_bal‖ ^ 2`
     yields quantitative upper bounds on both `-sourcePair (posGraph q) (negGraph q)` and
     `⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ` in terms of `((1 - ν) / 2) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2`.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump CHMDTranslation ThetaSourceWard

/-! ## Section 1: Exact `resolvent` Quadratic-Form Identities on Nodal Lobes and `balancedNodalGraph` -/

/-- **Individual Lobe `resolvent` Quadratic-Form Identities for Any Eigenvector**:
for every eigenvector `resolvent v = ν • v` with `q = rieszLift v`,
`⟪resolvent (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ = ν * ‖(posGraph q).val.fst‖ ^ 2 + ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`
and
`⟪resolvent (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ = ν * ‖(negGraph q).val.fst‖ ^ 2 + ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`. -/
theorem inner_resolvent_posGraph_and_negGraph_of_eigenvector {ν : ℝ} {v : MassSpace}
    (heig : resolvent v = ν • v) :
    let q := rieszLift v
    ⟪resolvent (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ =
        ν * ‖(posGraph q).val.fst‖ ^ 2 +
          ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ∧
      ⟪resolvent (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ =
        ν * ‖(negGraph q).val.fst‖ ^ 2 +
          ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ := by
  intro q
  have hq_fst : q.val.fst = ν • v := heig
  have hq_eig : resolvent q.val.fst = ν • q.val.fst := by
    rw [hq_fst, map_smul, heig]
  have hsub : q.val.fst = (posGraph q).val.fst - (negGraph q).val.fst :=
    congrArg (fun r : SourceGraph => r.val.fst) (posGraph_sub_negGraph q).symm
  have hp : ⟪resolvent q.val.fst, (posGraph q).val.fst⟫_ℝ =
      ν * ‖(posGraph q).val.fst‖ ^ 2 := by
    rw [hq_eig, real_inner_smul_left, real_inner_comm q.val.fst (posGraph q).val.fst,
      inner_posGraph_self_fst]
  have hn : ⟪resolvent q.val.fst, (negGraph q).val.fst⟫_ℝ =
      -ν * ‖(negGraph q).val.fst‖ ^ 2 := by
    rw [hq_eig, real_inner_smul_left, real_inner_comm q.val.fst (negGraph q).val.fst,
      inner_negGraph_self_fst]
    ring
  have hp_exp : ⟪resolvent q.val.fst, (posGraph q).val.fst⟫_ℝ =
      ⟪resolvent (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ -
        ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ := by
    conv_lhs => rw [hsub]
    rw [map_sub, inner_sub_left,
      resolvent_symm (negGraph q).val.fst (posGraph q).val.fst,
      real_inner_comm (resolvent (posGraph q).val.fst) (negGraph q).val.fst]
  have hn_exp : ⟪resolvent q.val.fst, (negGraph q).val.fst⟫_ℝ =
      ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ -
        ⟪resolvent (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ := by
    conv_lhs => rw [hsub]
    rw [map_sub, inner_sub_left]
  exact ⟨by linarith, by linarith⟩

/-- For every eigenvector `resolvent v = ν • v` with `q = rieszLift v`,
`⟪resolvent (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ = ν * ‖q.val.fst‖ ^ 2 + 4 * ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`. -/
theorem inner_resolvent_absGraph_of_eigenvector {ν : ℝ} {v : MassSpace}
    (heig : resolvent v = ν • v) :
    let q := rieszLift v
    ⟪resolvent (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ =
      ν * ‖q.val.fst‖ ^ 2 +
        4 * ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ := by
  intro q
  have hq_fst : q.val.fst = ν • v := heig
  have hq_eig : resolvent q.val.fst = ν • q.val.fst := by
    rw [hq_fst, map_smul, heig]
  have hself : ⟪resolvent q.val.fst, q.val.fst⟫_ℝ = ν * ‖q.val.fst‖ ^ 2 := by
    rw [hq_eig, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have h1 := inner_resolvent_absGraph_sub_self q
  linarith

/-- For every `p : SourceGraph`,
`⟪resolvent (balancedNodalGraph p).val.fst, (balancedNodalGraph p).val.fst⟫_ℝ = ‖(negGraph p).val.fst‖ ^ 4 * ⟪resolvent (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ + ‖(posGraph p).val.fst‖ ^ 4 * ⟪resolvent (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ + 2 * (‖(posGraph p).val.fst‖ ^ 2 * ‖(negGraph p).val.fst‖ ^ 2) * ⟪resolvent (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`. -/
theorem inner_resolvent_balancedNodalGraph (p : SourceGraph) :
    ⟪resolvent (balancedNodalGraph p).val.fst, (balancedNodalGraph p).val.fst⟫_ℝ =
      ‖(negGraph p).val.fst‖ ^ 4 *
          ⟪resolvent (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ +
        ‖(posGraph p).val.fst‖ ^ 4 *
          ⟪resolvent (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ +
        2 * (‖(posGraph p).val.fst‖ ^ 2 * ‖(negGraph p).val.fst‖ ^ 2) *
          ⟪resolvent (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  rw [balancedNodalGraph_fst, map_add, map_smul, map_smul,
    inner_add_left, inner_add_right, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    resolvent_symm (negGraph p).val.fst (posGraph p).val.fst,
    real_inner_comm (resolvent (posGraph p).val.fst) (negGraph p).val.fst]
  ring

/-- **Exact `resolvent` Quadratic Form of `balancedNodalGraph q` for Any Eigenvector**:
for every eigenvector `resolvent v = ν • v` with `q = rieszLift v`,
`⟪resolvent (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ = ν * ‖(balancedNodalGraph q).val.fst‖ ^ 2 + ‖q.val.fst‖ ^ 4 * ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`. -/
theorem inner_resolvent_balancedNodalGraph_of_eigenvector {ν : ℝ} {v : MassSpace}
    (heig : resolvent v = ν • v) :
    let q := rieszLift v
    ⟪resolvent (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ =
      ν * ‖(balancedNodalGraph q).val.fst‖ ^ 2 +
        ‖q.val.fst‖ ^ 4 *
          ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ := by
  intro q
  have h1 := inner_resolvent_balancedNodalGraph q
  obtain ⟨hp, hn⟩ := inner_resolvent_posGraph_and_negGraph_of_eigenvector heig
  have hsum := norm_posGraph_fst_sq_add_negGraph_fst_sq q
  have hnorm := norm_balancedNodalGraph_fst_sq q
  change ⟪resolvent (balancedNodalGraph (rieszLift v)).val.fst,
    (balancedNodalGraph (rieszLift v)).val.fst⟫_ℝ = _ at h1
  rw [hp, hn] at h1
  calc ⟪resolvent (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ
      = ‖(negGraph (rieszLift v)).val.fst‖ ^ 4 *
          (ν * ‖(posGraph (rieszLift v)).val.fst‖ ^ 2 +
            ⟪resolvent (posGraph (rieszLift v)).val.fst, (negGraph (rieszLift v)).val.fst⟫_ℝ) +
        ‖(posGraph (rieszLift v)).val.fst‖ ^ 4 *
          (ν * ‖(negGraph (rieszLift v)).val.fst‖ ^ 2 +
            ⟪resolvent (posGraph (rieszLift v)).val.fst, (negGraph (rieszLift v)).val.fst⟫_ℝ) +
        2 * (‖(posGraph (rieszLift v)).val.fst‖ ^ 2 * ‖(negGraph (rieszLift v)).val.fst‖ ^ 2) *
          ⟪resolvent (posGraph (rieszLift v)).val.fst, (negGraph (rieszLift v)).val.fst⟫_ℝ := h1
    _ = ν * ((‖(posGraph q).val.fst‖ ^ 2 + ‖(negGraph q).val.fst‖ ^ 2) *
          (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2)) +
        (‖(posGraph q).val.fst‖ ^ 2 + ‖(negGraph q).val.fst‖ ^ 2) ^ 2 *
          ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ := by
        change _ = ν * ((‖(posGraph (rieszLift v)).val.fst‖ ^ 2 + ‖(negGraph (rieszLift v)).val.fst‖ ^ 2) * _) + _
        ring
    _ = ν * ‖(balancedNodalGraph q).val.fst‖ ^ 2 +
        ‖q.val.fst‖ ^ 4 *
          ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ := by
        rw [hsum, ← hnorm]
        ring

/-- **Exact Primitive Balanced-Nodal Rayleigh Excess Identity for Primitive Eigenvectors**:
for every primitive eigenvector `resolvent v = ν • v` (`⟪v, oneL⟫_ℝ = 0`) with `q = rieszLift v`,
`⟪resolvent (primGraph (balancedNodalGraph q)).val.fst, (primGraph (balancedNodalGraph q)).val.fst⟫_ℝ - ν * ‖(primGraph (balancedNodalGraph q)).val.fst‖ ^ 2 = ‖q.val.fst‖ ^ 4 * (⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ - ((1 - ν) / 2) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2)`. -/
theorem inner_resolvent_primGraph_balancedNodalGraph_rayleigh_excess_of_primitive_eigenvector
    {ν : ℝ} {v : MassSpace} (hprim : ⟪v, oneL⟫_ℝ = 0) (heig : resolvent v = ν • v) :
    let q := rieszLift v
    ⟪resolvent (primGraph (balancedNodalGraph q)).val.fst,
        (primGraph (balancedNodalGraph q)).val.fst⟫_ℝ -
      ν * ‖(primGraph (balancedNodalGraph q)).val.fst‖ ^ 2 =
      ‖q.val.fst‖ ^ 4 *
        (⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ -
          ((1 - ν) / 2) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2) := by
  intro q
  have hq_prim : ⟪q.val.fst, oneL⟫_ℝ = 0 := by
    change ⟪resolvent v, oneL⟫_ℝ = 0
    rw [heig, real_inner_smul_left, hprim, mul_zero]
  obtain ⟨hinner1, _, _⟩ := primGraph_balancedNodalGraph_orthogonal_of_primitive hq_prim
  have h1 := inner_resolvent_primGraph_fst (balancedNodalGraph q)
  have h2 := norm_primGraph_fst_sq (balancedNodalGraph q)
  have h3 := inner_resolvent_balancedNodalGraph_of_eigenvector heig
  have hsq : 2 * ⟪(balancedNodalGraph q).val.fst, oneL⟫_ℝ ^ 2 =
      (1 / 2 : ℝ) * ‖q.val.fst‖ ^ 4 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 := by
    rw [hinner1]
    ring
  rw [hsq] at h1 h2
  change ⟪resolvent (balancedNodalGraph q).val.fst, (balancedNodalGraph q).val.fst⟫_ℝ = _ at h3
  linarith [congrArg (ν * ·) h2]

/-! ## Section 2: Quantitative Lower Bound and Strict Positivity of `⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ` -/

/-- For every eigenvector `resolvent v = ν • v` (`ν ≠ 0`) with `q = rieszLift v`,
`ν * (2 * ‖(posGraph q).val.fst‖ ^ 2 + sourceEnergy (posGraph q)) = ‖(posGraph q).val.fst‖ ^ 2 + ν * sourcePair (posGraph q) (negGraph q)`,
`ν * (2 * ‖(negGraph q).val.fst‖ ^ 2 + sourceEnergy (negGraph q)) = ‖(negGraph q).val.fst‖ ^ 2 + ν * sourcePair (posGraph q) (negGraph q)`,
and
`ν * (2 * ‖(absGraph q).val.fst‖ ^ 2 + sourceEnergy (absGraph q)) = ‖q.val.fst‖ ^ 2 + 4 * ν * sourcePair (posGraph q) (negGraph q)`. -/
theorem mul_two_norm_fst_sq_add_sourceEnergy_of_eigenvector {ν : ℝ} (hν : ν ≠ 0)
    {v : MassSpace} (heig : resolvent v = ν • v) :
    let q := rieszLift v
    ν * (2 * ‖(posGraph q).val.fst‖ ^ 2 + sourceEnergy (posGraph q)) =
        ‖(posGraph q).val.fst‖ ^ 2 + ν * sourcePair (posGraph q) (negGraph q) ∧
      ν * (2 * ‖(negGraph q).val.fst‖ ^ 2 + sourceEnergy (negGraph q)) =
        ‖(negGraph q).val.fst‖ ^ 2 + ν * sourcePair (posGraph q) (negGraph q) ∧
      ν * (2 * ‖(absGraph q).val.fst‖ ^ 2 + sourceEnergy (absGraph q)) =
        ‖q.val.fst‖ ^ 2 + 4 * ν * sourcePair (posGraph q) (negGraph q) := by
  intro q
  have hp := sourceEnergy_posGraph_rieszLift_of_eigenvector hν heig
  have hn := sourceEnergy_negGraph_rieszLift_of_eigenvector hν heig
  have habs_fst := norm_absGraph_fst_sq q
  have habs_E := sourceEnergy_absGraph_eq q
  have hq_E : sourceEnergy q = ((1 - 2 * ν) / ν) * ‖q.val.fst‖ ^ 2 := by
    have hE : sourceEnergy q = ‖q.val.snd‖ ^ 2 - ‖q.val.fst‖ ^ 2 := rfl
    rw [hE, norm_snd_sq_rieszLift_of_eigenvector hν heig]
    field_simp [hν]
    ring
  refine ⟨?_, ?_, ?_⟩
  · change ν * (2 * ‖(posGraph (rieszLift v)).val.fst‖ ^ 2 +
        sourceEnergy (posGraph (rieszLift v))) = _
    rw [hp]
    field_simp [hν]
    ring
  · change ν * (2 * ‖(negGraph (rieszLift v)).val.fst‖ ^ 2 +
        sourceEnergy (negGraph (rieszLift v))) = _
    rw [hn]
    field_simp [hν]
    ring
  · rw [habs_fst, habs_E, hq_E]
    field_simp [hν]
    ring

/-- **Quantitative Cross-Resolvent Lower Bound with Exact Edge-Norm Denominator Factors**:
for every eigenvector `resolvent v = ν • v` (`0 < ν`) with `q = rieszLift v`:
- `-ν ^ 2 * ‖(posGraph q).val.fst‖ ^ 2 * sourcePair (posGraph q) (negGraph q) ≤ ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ * (‖(posGraph q).val.fst‖ ^ 2 + ν * sourcePair (posGraph q) (negGraph q))`,
- `-ν ^ 2 * ‖(negGraph q).val.fst‖ ^ 2 * sourcePair (posGraph q) (negGraph q) ≤ ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ * (‖(negGraph q).val.fst‖ ^ 2 + ν * sourcePair (posGraph q) (negGraph q))`,
- `-ν ^ 2 * ‖q.val.fst‖ ^ 2 * sourcePair (posGraph q) (negGraph q) ≤ ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ * (‖q.val.fst‖ ^ 2 + 4 * ν * sourcePair (posGraph q) (negGraph q))`. -/
theorem neg_sq_mul_sourcePair_le_inner_resolvent_posGraph_negGraph_mul
    {ν : ℝ} (hν : 0 < ν) {v : MassSpace} (heig : resolvent v = ν • v) :
    let q := rieszLift v;
    -ν ^ 2 * ‖(posGraph q).val.fst‖ ^ 2 * sourcePair (posGraph q) (negGraph q) ≤
        ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ *
          (‖(posGraph q).val.fst‖ ^ 2 + ν * sourcePair (posGraph q) (negGraph q)) ∧
      -ν ^ 2 * ‖(negGraph q).val.fst‖ ^ 2 * sourcePair (posGraph q) (negGraph q) ≤
        ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ *
          (‖(negGraph q).val.fst‖ ^ 2 + ν * sourcePair (posGraph q) (negGraph q)) ∧
      -ν ^ 2 * ‖q.val.fst‖ ^ 2 * sourcePair (posGraph q) (negGraph q) ≤
        ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ *
          (‖q.val.fst‖ ^ 2 + 4 * ν * sourcePair (posGraph q) (negGraph q)) := by
  intro q
  obtain ⟨hp_res, hn_res⟩ := inner_resolvent_posGraph_and_negGraph_of_eigenvector heig
  have habs_res := inner_resolvent_absGraph_of_eigenvector heig
  obtain ⟨hp_E, hn_E, habs_E⟩ := mul_two_norm_fst_sq_add_sourceEnergy_of_eigenvector hν.ne' heig
  have hcs_p := norm_fst_pow_four_le_inner_resolvent_mul (posGraph q)
  have hcs_n := norm_fst_pow_four_le_inner_resolvent_mul (negGraph q)
  have hcs_abs := norm_fst_pow_four_le_inner_resolvent_mul (absGraph q)
  rw [norm_absGraph_fst] at hcs_abs
  have hp_mul := mul_le_mul_of_nonneg_left hcs_p hν.le
  have hn_mul := mul_le_mul_of_nonneg_left hcs_n hν.le
  have habs_mul := mul_le_mul_of_nonneg_left hcs_abs hν.le
  have hp_eq : ν * (⟪resolvent (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ *
      (2 * ‖(posGraph q).val.fst‖ ^ 2 + sourceEnergy (posGraph q))) =
      (ν * ‖(posGraph q).val.fst‖ ^ 2 +
        ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) *
      (‖(posGraph q).val.fst‖ ^ 2 + ν * sourcePair (posGraph q) (negGraph q)) := by
    calc ν * (⟪resolvent (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ *
          (2 * ‖(posGraph q).val.fst‖ ^ 2 + sourceEnergy (posGraph q)))
        = ⟪resolvent (posGraph q).val.fst, (posGraph q).val.fst⟫_ℝ *
            (ν * (2 * ‖(posGraph q).val.fst‖ ^ 2 + sourceEnergy (posGraph q))) := by ring
      _ = (ν * ‖(posGraph q).val.fst‖ ^ 2 +
            ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) *
          (‖(posGraph q).val.fst‖ ^ 2 + ν * sourcePair (posGraph q) (negGraph q)) := by
        rw [hp_res, hp_E]
  have hn_eq : ν * (⟪resolvent (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ *
      (2 * ‖(negGraph q).val.fst‖ ^ 2 + sourceEnergy (negGraph q))) =
      (ν * ‖(negGraph q).val.fst‖ ^ 2 +
        ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) *
      (‖(negGraph q).val.fst‖ ^ 2 + ν * sourcePair (posGraph q) (negGraph q)) := by
    calc ν * (⟪resolvent (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ *
          (2 * ‖(negGraph q).val.fst‖ ^ 2 + sourceEnergy (negGraph q)))
        = ⟪resolvent (negGraph q).val.fst, (negGraph q).val.fst⟫_ℝ *
            (ν * (2 * ‖(negGraph q).val.fst‖ ^ 2 + sourceEnergy (negGraph q))) := by ring
      _ = (ν * ‖(negGraph q).val.fst‖ ^ 2 +
            ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) *
          (‖(negGraph q).val.fst‖ ^ 2 + ν * sourcePair (posGraph q) (negGraph q)) := by
        rw [hn_res, hn_E]
  have habs_eq : ν * (⟪resolvent (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ *
      (2 * ‖(absGraph q).val.fst‖ ^ 2 + sourceEnergy (absGraph q))) =
      (ν * ‖q.val.fst‖ ^ 2 +
        4 * ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) *
      (‖q.val.fst‖ ^ 2 + 4 * ν * sourcePair (posGraph q) (negGraph q)) := by
    calc ν * (⟪resolvent (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ *
          (2 * ‖(absGraph q).val.fst‖ ^ 2 + sourceEnergy (absGraph q)))
        = ⟪resolvent (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ *
            (ν * (2 * ‖(absGraph q).val.fst‖ ^ 2 + sourceEnergy (absGraph q))) := by ring
      _ = (ν * ‖q.val.fst‖ ^ 2 +
            4 * ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ) *
          (‖q.val.fst‖ ^ 2 + 4 * ν * sourcePair (posGraph q) (negGraph q)) := by
        rw [habs_res, habs_E]
  rw [hp_eq] at hp_mul
  rw [hn_eq] at hn_mul
  rw [habs_eq] at habs_mul
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **Unconditional Nonnegativity and Quantitative Cross-Jump Lower Bound on `⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`**:
for every eigenvector `resolvent v = ν • v` (`0 < ν`) with `q = rieszLift v`,
`0 ≤ -ν ^ 2 * sourcePair (posGraph q) (negGraph q)` and
`-ν ^ 2 * sourcePair (posGraph q) (negGraph q) ≤ ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`. -/
theorem neg_sq_mul_sourcePair_le_inner_resolvent_posGraph_negGraph
    {ν : ℝ} (hν : 0 < ν) {v : MassSpace} (heig : resolvent v = ν • v) :
    let q := rieszLift v
    0 ≤ -ν ^ 2 * sourcePair (posGraph q) (negGraph q) ∧
      -ν ^ 2 * sourcePair (posGraph q) (negGraph q) ≤
        ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ := by
  intro q
  have hsp : sourcePair (posGraph q) (negGraph q) ≤ 0 := sourcePair_posGraph_negGraph_nonpos q
  have hnn : 0 ≤ -ν ^ 2 * sourcePair (posGraph q) (negGraph q) := by
    nlinarith [sq_nonneg ν]
  refine ⟨hnn, ?_⟩
  by_cases hq : ‖q.val.fst‖ ^ 2 = 0
  · have hpos0 : ‖(posGraph q).val.fst‖ = 0 := by
      have hsum := norm_posGraph_fst_sq_add_negGraph_fst_sq q
      have hsq0 : ‖(posGraph q).val.fst‖ ^ 2 = 0 := by
        linarith [sq_nonneg ‖(posGraph q).val.fst‖, sq_nonneg ‖(negGraph q).val.fst‖]
      exact pow_eq_zero hsq0
    have hpos_fst : (posGraph q).val.fst = 0 := norm_eq_zero.mp hpos0
    have hpos_eq0 : posGraph q = 0 :=
      source_projection_injective (hpos_fst.trans (by rfl))
    rw [hpos_eq0]
    simp [sourcePair]
  · have hq_pos : 0 < ‖q.val.fst‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hq)
    have h3 := (neg_sq_mul_sourcePair_le_inner_resolvent_posGraph_negGraph_mul hν heig).2.2
    obtain ⟨_, _, habs_E⟩ := mul_two_norm_fst_sq_add_sourceEnergy_of_eigenvector hν.ne' heig
    have hdenom_eq : ‖q.val.fst‖ ^ 2 + 4 * ν * sourcePair (posGraph q) (negGraph q) =
        ν * (‖q.val.fst‖ ^ 2 + ‖(absGraph q).val.snd‖ ^ 2) := by
      have hE : sourceEnergy (absGraph q) =
          ‖(absGraph q).val.snd‖ ^ 2 - ‖(absGraph q).val.fst‖ ^ 2 := rfl
      rw [← habs_E, hE, norm_absGraph_fst_sq]
      ring
    have hdenom_pos : 0 < ‖q.val.fst‖ ^ 2 + 4 * ν * sourcePair (posGraph q) (negGraph q) := by
      rw [hdenom_eq]
      exact mul_pos hν (add_pos_of_pos_of_nonneg hq_pos (sq_nonneg _))
    have hlhs_nn : 0 ≤ -ν ^ 2 * ‖q.val.fst‖ ^ 2 * sourcePair (posGraph q) (negGraph q) := by
      nlinarith
    have hres_nn : 0 ≤ ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ :=
      nonneg_of_mul_nonneg_right (hlhs_nn.trans h3) hdenom_pos
    have hdenom_le : ‖q.val.fst‖ ^ 2 + 4 * ν * sourcePair (posGraph q) (negGraph q) ≤
        ‖q.val.fst‖ ^ 2 := by
      nlinarith
    have h4 : -ν ^ 2 * ‖q.val.fst‖ ^ 2 * sourcePair (posGraph q) (negGraph q) ≤
        ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ * ‖q.val.fst‖ ^ 2 :=
      h3.trans (mul_le_mul_of_nonneg_left hdenom_le hres_nn)
    nlinarith

/-- **Strict Positivity of `⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ` for Nonzero Primitive Eigenvectors**:
for every nonzero primitive eigenvector `resolvent v = ν • v` (`0 < ν`, `v ≠ 0`, `⟪v, oneL⟫_ℝ = 0`)
with `q = rieszLift v`,
`0 < -ν ^ 2 * sourcePair (posGraph q) (negGraph q)` and
`0 < ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ`. -/
theorem inner_resolvent_posGraph_negGraph_pos_of_primitive_eigenvector
    {ν : ℝ} (hν : 0 < ν) {v : MassSpace} (hv0 : v ≠ 0) (hprim : ⟪v, oneL⟫_ℝ = 0)
    (heig : resolvent v = ν • v) :
    let q := rieszLift v
    0 < -ν ^ 2 * sourcePair (posGraph q) (negGraph q) ∧
      0 < ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ := by
  intro q
  have hq_fst : q.val.fst = ν • v := heig
  have hq0 : q ≠ 0 := by
    intro h
    have hf : q.val.fst = 0 := by rw [h]; rfl
    rw [hq_fst, smul_eq_zero] at hf
    exact hv0 (hf.resolve_left hν.ne')
  have hq_prim : ⟪q.val.fst, oneL⟫_ℝ = 0 := by
    rw [hq_fst, real_inner_smul_left, hprim, mul_zero]
  obtain ⟨hpos_ne, hneg_ne⟩ := posGraph_ne_zero_and_negGraph_ne_zero_of_primitive hq0 hq_prim
  have hcross_neg : sourcePair (posGraph q) (negGraph q) < 0 :=
    sourcePair_posGraph_negGraph_neg_of_ne_zero hpos_ne hneg_ne
  have hpos1 : 0 < -ν ^ 2 * sourcePair (posGraph q) (negGraph q) := by
    nlinarith [sq_pos_of_pos hν]
  have hle := (neg_sq_mul_sourcePair_le_inner_resolvent_posGraph_negGraph hν heig).2
  exact ⟨hpos1, hpos1.trans_le hle⟩

/-! ## Section 3: Doubly-Orthogonal Courant–Fischer Nodal Bounds on `primGraph (balancedNodalGraph q)` -/

/-- **Doubly-Orthogonal Spectral-Gap Weighted Nodal Cross-Jump Bound via `primGraph (balancedNodalGraph q)`**:
for every primitive eigenvector `resolvent v = ν • v` (`0 < ν`, `⟪v, oneL⟫_ℝ = 0`) with
`q = rieszLift v`, the vector `u_bal = (primGraph (balancedNodalGraph q)).val.fst` is orthogonal to
both `oneL` and `v`. For any `0 < μ_2` satisfying `⟪resolvent u_bal, u_bal⟫_ℝ ≤ μ_2 * ‖u_bal‖ ^ 2`,
`((ν - μ_2) / (ν * μ_2)) * ‖u_bal‖ ^ 2 - ‖q.val.fst‖ ^ 4 * sourcePair (posGraph q) (negGraph q) ≤ ((1 - ν) / (2 * ν)) * ‖q.val.fst‖ ^ 4 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2`. -/
theorem eigenvector_balancedNodalGraph_nodal_cross_le_spectral_gap_mul_oneL_sq
    {ν μ_2 : ℝ} (hν : 0 < ν) (hμ2 : 0 < μ_2) {v : MassSpace}
    (hprim : ⟪v, oneL⟫_ℝ = 0) (heig : resolvent v = ν • v)
    (hray : ⟪resolvent (primGraph (balancedNodalGraph (rieszLift v))).val.fst,
        (primGraph (balancedNodalGraph (rieszLift v))).val.fst⟫_ℝ ≤
      μ_2 * ‖(primGraph (balancedNodalGraph (rieszLift v))).val.fst‖ ^ 2) :
    let q := rieszLift v
    ((ν - μ_2) / (ν * μ_2)) * ‖(primGraph (balancedNodalGraph q)).val.fst‖ ^ 2 -
        ‖q.val.fst‖ ^ 4 * sourcePair (posGraph q) (negGraph q) ≤
      ((1 - ν) / (2 * ν)) * ‖q.val.fst‖ ^ 4 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 := by
  intro q
  have h1 := sourceEnergy_ge_of_inner_resolvent_le hμ2 hray
  have h2 := (primGraph_balancedNodalGraph_orthogonal_and_energy_of_primitive_eigenvector
    hν.ne' hprim heig).2.2.2
  have hid : -(((1 - 2 * ν) / ν) * ‖(primGraph (balancedNodalGraph q)).val.fst‖ ^ 2) -
      ((2 * μ_2 - 1) / μ_2) * ‖(primGraph (balancedNodalGraph q)).val.fst‖ ^ 2 =
      ((ν - μ_2) / (ν * μ_2)) * ‖(primGraph (balancedNodalGraph q)).val.fst‖ ^ 2 := by
    field_simp [hν.ne', hμ2.ne']
    ring
  linarith

/-- **Doubly-Orthogonal `resolvent` Rayleigh-Excess Nodal Bound via `primGraph (balancedNodalGraph q)`**:
for every primitive eigenvector `resolvent v = ν • v` (`0 < ν`, `⟪v, oneL⟫_ℝ = 0`) with
`q = rieszLift v` and `u_bal = (primGraph (balancedNodalGraph q)).val.fst`, any Rayleigh bound
`⟪resolvent u_bal, u_bal⟫_ℝ ≤ μ_2 * ‖u_bal‖ ^ 2` implies both
`(ν - μ_2) * ‖u_bal‖ ^ 2 + ‖q.val.fst‖ ^ 4 * ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ≤ ((1 - ν) / 2) * ‖q.val.fst‖ ^ 4 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2`
and
`(ν - μ_2) * ‖u_bal‖ ^ 2 - ν ^ 2 * ‖q.val.fst‖ ^ 4 * sourcePair (posGraph q) (negGraph q) ≤ ((1 - ν) / 2) * ‖q.val.fst‖ ^ 4 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2`. -/
theorem eigenvector_balancedNodalGraph_resolvent_cross_le_of_rayleigh_le
    {ν μ_2 : ℝ} (hν : 0 < ν) {v : MassSpace}
    (hprim : ⟪v, oneL⟫_ℝ = 0) (heig : resolvent v = ν • v)
    (hray : ⟪resolvent (primGraph (balancedNodalGraph (rieszLift v))).val.fst,
        (primGraph (balancedNodalGraph (rieszLift v))).val.fst⟫_ℝ ≤
      μ_2 * ‖(primGraph (balancedNodalGraph (rieszLift v))).val.fst‖ ^ 2) :
    let q := rieszLift v
    (ν - μ_2) * ‖(primGraph (balancedNodalGraph q)).val.fst‖ ^ 2 +
        ‖q.val.fst‖ ^ 4 * ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ ≤
      ((1 - ν) / 2) * ‖q.val.fst‖ ^ 4 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 ∧
    (ν - μ_2) * ‖(primGraph (balancedNodalGraph q)).val.fst‖ ^ 2 -
        ν ^ 2 * ‖q.val.fst‖ ^ 4 * sourcePair (posGraph q) (negGraph q) ≤
      ((1 - ν) / 2) * ‖q.val.fst‖ ^ 4 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 := by
  intro q
  have hex := inner_resolvent_primGraph_balancedNodalGraph_rayleigh_excess_of_primitive_eigenvector
    hprim heig
  have hle := (neg_sq_mul_sourcePair_le_inner_resolvent_posGraph_negGraph hν heig).2
  have hle4 : -ν ^ 2 * ‖q.val.fst‖ ^ 4 * sourcePair (posGraph q) (negGraph q) ≤
      ‖q.val.fst‖ ^ 4 * ⟪resolvent (posGraph q).val.fst, (negGraph q).val.fst⟫_ℝ := by
    have hpow : 0 ≤ ‖q.val.fst‖ ^ 4 := by positivity
    nlinarith
  exact ⟨by linarith, by linarith⟩

end RHTower.CHMDPolar
