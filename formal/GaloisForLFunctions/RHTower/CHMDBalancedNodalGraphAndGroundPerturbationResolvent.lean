import GaloisForLFunctions.RHTower.CHMDEigenvectorAbsGraphEdgeNormAndFiveTermLobeBalance

/-!
# Ground-Perturbation Second-Resolvent Identities, `absGraph` Edge Pairings, and the Balanced Nodal Graph

This module establishes the `groundPerturbation` form of the second-resolvent identity and polarized
edge inner product, the `absGraph` edge-pairing identities and eigenvalue-free cross-multiplied lobe
balances, and constructs the balanced nonnegative nodal graph
`balancedNodalGraph q = ‖(negGraph q).val.fst‖ ^ 2 • posGraph q + ‖(posGraph q).val.fst‖ ^ 2 • negGraph q`,
proving its simultaneous orthogonality to `q` in `MassSpace`, `EdgeSpace`, and `sourcePair` together
with the sharp product nodal bound:

1. **Second-Resolvent Identities via `groundPerturbation = groundPotentialOperator + primeGenerator`
   and Polarized Edge Inner Product**:
   - `id_sub_arch_sub_primeShift_eq_groundPerturbation`:
     `ContinuousLinearMap.id ℝ MassSpace - archDiagonalOperator - primeShiftOperator = groundPerturbation`
     and `groundPerturbation = groundPotentialOperator + primeGenerator`.
   - `resolvent_sub_stationaryResolvent_eq_neg_stationaryResolvent_groundPotential_add_primeGenerator`
     and `resolvent_sub_stationaryResolvent_eq_neg_resolvent_groundPerturbation`:
     for every `w : MassSpace`,
     `resolvent w - stationaryResolvent w = -stationaryResolvent (groundPotentialOperator (resolvent w) + primeGenerator (resolvent w))`
     and
     `resolvent w - stationaryResolvent w = -resolvent (groundPotentialOperator (stationaryResolvent w) + primeGenerator (stationaryResolvent w))`.
   - `eigenvector_stationaryResolvent_sub_smul_eq_groundPerturbation`:
     for every eigenvector `resolvent u = μ • u`,
     `stationaryResolvent u - μ • u = μ • stationaryResolvent (groundPerturbation u)`
     and
     `stationaryResolvent u - μ • u = μ • stationaryResolvent (groundPotentialOperator u + primeGenerator u)`.
   - `inner_snd_eq_stationary_add_primeGenerator_add_groundPotential`:
     for all `p, q : SourceGraph`,
     `⟪p.val.snd, q.val.snd⟫_ℝ = ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ + ⟪primeGenerator p.val.fst, q.val.fst⟫_ℝ + ⟪groundPotentialOperator p.val.fst, q.val.fst⟫_ℝ`.

2. **`absGraph` Edge-Pairing Identities and Eigenvalue-Free Cross-Multiplied Lobe Balances**:
   - `inner_posGraph_absGraph_snd`, `inner_negGraph_absGraph_snd`, and `inner_self_absGraph_snd`:
     for every `p : SourceGraph`,
     `⟪(posGraph p).val.snd, (absGraph p).val.snd⟫_ℝ = ‖(posGraph p).val.snd‖ ^ 2 + sourcePair (posGraph p) (negGraph p)`,
     `⟪(negGraph p).val.snd, (absGraph p).val.snd⟫_ℝ = ‖(negGraph p).val.snd‖ ^ 2 + sourcePair (posGraph p) (negGraph p)`,
     and `⟪p.val.snd, (absGraph p).val.snd⟫_ℝ = ‖(posGraph p).val.snd‖ ^ 2 - ‖(negGraph p).val.snd‖ ^ 2`.
   - `norm_posGraph_snd_sq_sub_negGraph_snd_sq_rieszLift_of_eigenvector`:
     for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
     `‖(posGraph q).val.snd‖ ^ 2 - ‖(negGraph q).val.snd‖ ^ 2 = ((1 - μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 - ‖(negGraph q).val.fst‖ ^ 2)`.
   - `eigenvector_lobe_snd_sq_cross_balance` and `eigenvector_lobe_sourceEnergy_cross_balance`:
     `‖(posGraph q).val.snd‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2 - ‖(negGraph q).val.snd‖ ^ 2 * ‖(posGraph q).val.fst‖ ^ 2 = sourcePair (posGraph q) (negGraph q) * (‖(negGraph q).val.fst‖ ^ 2 - ‖(posGraph q).val.fst‖ ^ 2)`.

3. **The Balanced Nonnegative Nodal Graph `balancedNodalGraph` and Product Nodal Bound**:
   - `balancedNodalGraph (q : SourceGraph) : SourceGraph := ‖(negGraph q).val.fst‖ ^ 2 • posGraph q + ‖(posGraph q).val.fst‖ ^ 2 • negGraph q`.
   - `inner_balancedNodalGraph_self_fst` and `norm_balancedNodalGraph_fst_sq`:
     `⟪(balancedNodalGraph q).val.fst, q.val.fst⟫_ℝ = 0` and
     `‖(balancedNodalGraph q).val.fst‖ ^ 2 = ‖q.val.fst‖ ^ 2 * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2)`.
   - `inner_balancedNodalGraph_snd_and_sourcePair_of_eigenvector`:
     for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
     `⟪(balancedNodalGraph q).val.snd, q.val.snd⟫_ℝ = 0` and `sourcePair (balancedNodalGraph q) q = 0`.
   - `norm_balancedNodalGraph_snd_sq_of_eigenvector` and `sourceEnergy_balancedNodalGraph_of_eigenvector`:
     `‖(balancedNodalGraph q).val.snd‖ ^ 2 = ‖q.val.fst‖ ^ 2 * (((1 - μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2) + sourcePair (posGraph q) (negGraph q) * ‖q.val.fst‖ ^ 2)`.
   - `neg_sourcePair_mul_norm_fst_sq_le_lobe_product_of_eigenvector`:
     `-sourcePair (posGraph q) (negGraph q) * ‖q.val.fst‖ ^ 2 ≤ ((1 - μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2)`.
   - `primGraph_balancedNodalGraph_orthogonal_and_energy_of_primitive_eigenvector`:
     for every primitive eigenvector `resolvent w = μ • w` (`μ ≠ 0`, `⟪w, oneL⟫_ℝ = 0`) with `q = rieszLift w`,
     `primGraph (balancedNodalGraph q)` is simultaneously orthogonal to `oneL` and to `q.val.fst`
     (in `MassSpace`, `EdgeSpace`, and `sourcePair`).
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump CHMDTranslation ThetaSourceWard

/-! ## Section 1: `groundPerturbation` Second-Resolvent Identities and Polarized Edge Inner Product -/

/-- On `MassSpace`,
`ContinuousLinearMap.id ℝ MassSpace - archDiagonalOperator - primeShiftOperator = groundPerturbation`
and `groundPerturbation = groundPotentialOperator + primeGenerator`. -/
theorem id_sub_arch_sub_primeShift_eq_groundPerturbation :
    ContinuousLinearMap.id ℝ MassSpace - archDiagonalOperator - primeShiftOperator =
      groundPerturbation ∧
    groundPerturbation = groundPotentialOperator + primeGenerator := by
  refine ⟨?_, add_comm primeGenerator groundPotentialOperator⟩
  have h := groundPerturbation_sub_id_eq
  have h2 : groundPerturbation =
      -primeShiftOperator - archDiagonalOperator + ContinuousLinearMap.id ℝ MassSpace :=
    sub_eq_iff_eq_add.mp h
  rw [h2]
  abel

/-- For every `u : MassSpace`,
`u - archDiagonalOperator u - primeShiftOperator u = groundPerturbation u`
and
`groundPerturbation u = groundPotentialOperator u + primeGenerator u`. -/
theorem sub_arch_sub_primeShift_apply_eq_groundPerturbation (u : MassSpace) :
    u - archDiagonalOperator u - primeShiftOperator u = groundPerturbation u ∧
      groundPerturbation u = groundPotentialOperator u + primeGenerator u := by
  have h := congrArg (fun T : MassSpace →L[ℝ] MassSpace => T u)
    id_sub_arch_sub_primeShift_eq_groundPerturbation.1
  have h2 := congrArg (fun T : MassSpace →L[ℝ] MassSpace => T u)
    id_sub_arch_sub_primeShift_eq_groundPerturbation.2
  exact ⟨h, h2⟩

/-- **Second-Resolvent Identity via `groundPotentialOperator + primeGenerator`**:
for every `w : MassSpace`,
`resolvent w - stationaryResolvent w = -stationaryResolvent (groundPotentialOperator (resolvent w) + primeGenerator (resolvent w))`. -/
theorem resolvent_sub_stationaryResolvent_eq_neg_stationaryResolvent_groundPotential_add_primeGenerator
    (w : MassSpace) :
    resolvent w - stationaryResolvent w =
      -stationaryResolvent
        (groundPotentialOperator (resolvent w) + primeGenerator (resolvent w)) := by
  rw [resolvent_sub_stationaryResolvent_eq_neg_stationaryResolvent w,
    (sub_arch_sub_primeShift_apply_eq_groundPerturbation (resolvent w)).2]

/-- **Dual Second-Resolvent Identity via `groundPerturbation = groundPotentialOperator + primeGenerator`**:
for every `w : MassSpace`,
`resolvent w - stationaryResolvent w = -resolvent (groundPerturbation (stationaryResolvent w))`
and
`resolvent w - stationaryResolvent w = -resolvent (groundPotentialOperator (stationaryResolvent w) + primeGenerator (stationaryResolvent w))`. -/
theorem resolvent_sub_stationaryResolvent_eq_neg_resolvent_groundPerturbation (w : MassSpace) :
    resolvent w - stationaryResolvent w =
        -resolvent (groundPerturbation (stationaryResolvent w)) ∧
      resolvent w - stationaryResolvent w =
        -resolvent
          (groundPotentialOperator (stationaryResolvent w) +
            primeGenerator (stationaryResolvent w)) := by
  have h1 := resolvent_sub_stationaryResolvent_eq_dual w
  have h2 := (neg_groundPerturbation_eq (stationaryResolvent w)).symm
  rw [h2, map_neg] at h1
  have h3 := (sub_arch_sub_primeShift_apply_eq_groundPerturbation (stationaryResolvent w)).2
  exact ⟨h1, by rwa [h3] at h1⟩

/-- **Eigenvector `stationaryResolvent` Identity via `groundPerturbation = groundPotentialOperator + primeGenerator`**:
for every eigenvector `resolvent u = μ • u`,
`stationaryResolvent u - μ • u = μ • stationaryResolvent (groundPerturbation u)`
and
`stationaryResolvent u - μ • u = μ • stationaryResolvent (groundPotentialOperator u + primeGenerator u)`. -/
theorem eigenvector_stationaryResolvent_sub_smul_eq_groundPerturbation
    {μ : ℝ} {u : MassSpace} (heig : resolvent u = μ • u) :
    stationaryResolvent u - μ • u =
        μ • stationaryResolvent (groundPerturbation u) ∧
      stationaryResolvent u - μ • u =
        μ • stationaryResolvent (groundPotentialOperator u + primeGenerator u) := by
  have h1 := resolvent_sub_stationaryResolvent_eq_neg_stationaryResolvent u
  rw [heig, map_smul, map_smul] at h1
  have h2 : stationaryResolvent u - μ • u = μ • stationaryResolvent (groundPerturbation u) := by
    calc stationaryResolvent u - μ • u
        = -(μ • u - stationaryResolvent u) := by abel
      _ = -(-(μ • stationaryResolvent (groundPerturbation u))) := by rw [h1]
      _ = μ • stationaryResolvent (groundPerturbation u) := neg_neg _
  have h3 := (sub_arch_sub_primeShift_apply_eq_groundPerturbation u).2
  exact ⟨h2, by rwa [h3] at h2⟩

/-- **Polarized Edge Inner-Product Formula in `SourceGraph`**:
for all `p, q : SourceGraph`,
`⟪p.val.snd, q.val.snd⟫_ℝ = ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ + ⟪groundPerturbation p.val.fst, q.val.fst⟫_ℝ`
and
`⟪p.val.snd, q.val.snd⟫_ℝ = ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ + ⟪primeGenerator p.val.fst, q.val.fst⟫_ℝ + ⟪groundPotentialOperator p.val.fst, q.val.fst⟫_ℝ`. -/
theorem inner_snd_eq_stationary_add_primeGenerator_add_groundPotential (p q : SourceGraph) :
    ⟪p.val.snd, q.val.snd⟫_ℝ =
        ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ +
          ⟪groundPerturbation p.val.fst, q.val.fst⟫_ℝ ∧
      ⟪p.val.snd, q.val.snd⟫_ℝ =
        ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ +
          ⟪primeGenerator p.val.fst, q.val.fst⟫_ℝ +
          ⟪groundPotentialOperator p.val.fst, q.val.fst⟫_ℝ := by
  have h1 := fullGround_inner_decomposition p q
  rw [graph_inner] at h1
  have hstat : ⟪fullGroundEquiv p, fullGroundEquiv q⟫_ℝ =
      ⟪p.val.fst, q.val.fst⟫_ℝ + ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ := by
    have hp : (fullGroundEquiv p).val.fst = p.val.fst := fullGroundEquiv_source p
    have hq : (fullGroundEquiv q).val.fst = q.val.fst := fullGroundEquiv_source q
    rw [Submodule.coe_inner, WithLp.prod_inner_apply]
    change ⟪(fullGroundEquiv p).val.fst, (fullGroundEquiv q).val.fst⟫_ℝ +
      ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ = _
    rw [hp, hq]
  change ⟪p.val.fst, q.val.fst⟫_ℝ + ⟪p.val.snd, q.val.snd⟫_ℝ =
    ⟪fullGroundEquiv p, fullGroundEquiv q⟫_ℝ +
      ⟪groundPerturbation p.val.fst, q.val.fst⟫_ℝ at h1
  have hpert : ⟪groundPerturbation p.val.fst, q.val.fst⟫_ℝ =
      ⟪primeGenerator p.val.fst, q.val.fst⟫_ℝ +
        ⟪groundPotentialOperator p.val.fst, q.val.fst⟫_ℝ := by
    change ⟪primeGenerator p.val.fst + groundPotentialOperator p.val.fst, q.val.fst⟫_ℝ = _
    rw [inner_add_left]
  exact ⟨by linarith, by linarith⟩

/-! ## Section 2: `absGraph` Edge-Pairing Identities and Cross-Multiplied Lobe Balances -/

/-- For every `p : SourceGraph`,
`⟪(posGraph p).val.snd, (absGraph p).val.snd⟫_ℝ = ‖(posGraph p).val.snd‖ ^ 2 + sourcePair (posGraph p) (negGraph p)`
and
`⟪(negGraph p).val.snd, (absGraph p).val.snd⟫_ℝ = ‖(negGraph p).val.snd‖ ^ 2 + sourcePair (posGraph p) (negGraph p)`. -/
theorem inner_posGraph_and_negGraph_absGraph_snd (p : SourceGraph) :
    ⟪(posGraph p).val.snd, (absGraph p).val.snd⟫_ℝ =
        ‖(posGraph p).val.snd‖ ^ 2 + sourcePair (posGraph p) (negGraph p) ∧
      ⟪(negGraph p).val.snd, (absGraph p).val.snd⟫_ℝ =
        ‖(negGraph p).val.snd‖ ^ 2 + sourcePair (posGraph p) (negGraph p) := by
  have hadd : (absGraph p).val.snd = (posGraph p).val.snd + (negGraph p).val.snd :=
    congrArg (fun r : SourceGraph => r.val.snd) (posGraph_add_negGraph p).symm
  have hpair := (sourcePair_posGraph_negGraph_eq_inner_snd p).symm
  refine ⟨?_, ?_⟩
  · rw [hadd, inner_add_right, real_inner_self_eq_norm_sq, hpair]
  · rw [hadd, inner_add_right, real_inner_comm (posGraph p).val.snd (negGraph p).val.snd,
      real_inner_self_eq_norm_sq, hpair]
    ring

/-- For every `p : SourceGraph`,
`⟪p.val.snd, (absGraph p).val.snd⟫_ℝ = ‖(posGraph p).val.snd‖ ^ 2 - ‖(negGraph p).val.snd‖ ^ 2`. -/
theorem inner_self_absGraph_snd (p : SourceGraph) :
    ⟪p.val.snd, (absGraph p).val.snd⟫_ℝ =
      ‖(posGraph p).val.snd‖ ^ 2 - ‖(negGraph p).val.snd‖ ^ 2 := by
  have hsub : p.val.snd = (posGraph p).val.snd - (negGraph p).val.snd :=
    congrArg (fun r : SourceGraph => r.val.snd) (posGraph_sub_negGraph p).symm
  obtain ⟨hp, hn⟩ := inner_posGraph_and_negGraph_absGraph_snd p
  rw [hsub, inner_sub_left, hp, hn]
  ring

/-- For every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`‖(posGraph q).val.snd‖ ^ 2 - ‖(negGraph q).val.snd‖ ^ 2 = ((1 - μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 - ‖(negGraph q).val.fst‖ ^ 2)`
and
`⟪q.val.snd, (absGraph q).val.snd⟫_ℝ = ((1 - μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 - ‖(negGraph q).val.fst‖ ^ 2)`. -/
theorem norm_posGraph_snd_sq_sub_negGraph_snd_sq_rieszLift_of_eigenvector
    {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w
    ‖(posGraph q).val.snd‖ ^ 2 - ‖(negGraph q).val.snd‖ ^ 2 =
        ((1 - μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 - ‖(negGraph q).val.fst‖ ^ 2) ∧
      ⟪q.val.snd, (absGraph q).val.snd⟫_ℝ =
        ((1 - μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 - ‖(negGraph q).val.fst‖ ^ 2) := by
  intro q
  have hp := norm_posGraph_snd_sq_rieszLift_of_eigenvector hμ heig
  have hn := norm_negGraph_snd_sq_rieszLift_of_eigenvector hμ heig
  have hdiff : ‖(posGraph q).val.snd‖ ^ 2 - ‖(negGraph q).val.snd‖ ^ 2 =
      ((1 - μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 - ‖(negGraph q).val.fst‖ ^ 2) := by
    linarith
  exact ⟨hdiff, (inner_self_absGraph_snd q).trans hdiff⟩

/-- **Eigenvalue-Free Cross-Multiplied Nodal Lobe Edge-Norm and Energy Balances**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`, eliminating `μ`
between the positive and negative lobe identities gives
`‖(posGraph q).val.snd‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2 - ‖(negGraph q).val.snd‖ ^ 2 * ‖(posGraph q).val.fst‖ ^ 2 = sourcePair (posGraph q) (negGraph q) * (‖(negGraph q).val.fst‖ ^ 2 - ‖(posGraph q).val.fst‖ ^ 2)`
and
`sourceEnergy (posGraph q) * ‖(negGraph q).val.fst‖ ^ 2 - sourceEnergy (negGraph q) * ‖(posGraph q).val.fst‖ ^ 2 = sourcePair (posGraph q) (negGraph q) * (‖(negGraph q).val.fst‖ ^ 2 - ‖(posGraph q).val.fst‖ ^ 2)`. -/
theorem eigenvector_lobe_cross_multiplied_balance {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) :
    let q := rieszLift w
    ‖(posGraph q).val.snd‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2 -
        ‖(negGraph q).val.snd‖ ^ 2 * ‖(posGraph q).val.fst‖ ^ 2 =
      sourcePair (posGraph q) (negGraph q) *
        (‖(negGraph q).val.fst‖ ^ 2 - ‖(posGraph q).val.fst‖ ^ 2) ∧
    sourceEnergy (posGraph q) * ‖(negGraph q).val.fst‖ ^ 2 -
        sourceEnergy (negGraph q) * ‖(posGraph q).val.fst‖ ^ 2 =
      sourcePair (posGraph q) (negGraph q) *
        (‖(negGraph q).val.fst‖ ^ 2 - ‖(posGraph q).val.fst‖ ^ 2) := by
  intro q
  have hs_pos := norm_posGraph_snd_sq_rieszLift_of_eigenvector hμ heig
  have hs_neg := norm_negGraph_snd_sq_rieszLift_of_eigenvector hμ heig
  have hE_pos := sourceEnergy_posGraph_rieszLift_of_eigenvector hμ heig
  have hE_neg := sourceEnergy_negGraph_rieszLift_of_eigenvector hμ heig
  refine ⟨?_, ?_⟩
  · change ‖(posGraph (rieszLift w)).val.snd‖ ^ 2 * ‖(negGraph (rieszLift w)).val.fst‖ ^ 2 -
      ‖(negGraph (rieszLift w)).val.snd‖ ^ 2 * ‖(posGraph (rieszLift w)).val.fst‖ ^ 2 = _
    rw [hs_pos, hs_neg]
    ring
  · change sourceEnergy (posGraph (rieszLift w)) * ‖(negGraph (rieszLift w)).val.fst‖ ^ 2 -
      sourceEnergy (negGraph (rieszLift w)) * ‖(posGraph (rieszLift w)).val.fst‖ ^ 2 = _
    rw [hE_pos, hE_neg]
    ring

/-! ## Section 3: The Balanced Nonnegative Nodal Graph `balancedNodalGraph` and Product Nodal Bound -/

/-- **The Balanced Nonnegative Nodal Graph**:
for any `q : SourceGraph`, weighting the positive lobe by `‖(negGraph q).val.fst‖ ^ 2` and the
negative lobe by `‖(posGraph q).val.fst‖ ^ 2` produces a nonnegative graph vector whose vertex
component is identically orthogonal to `q.val.fst` in `MassSpace`. -/
def balancedNodalGraph (q : SourceGraph) : SourceGraph :=
  ‖(negGraph q).val.fst‖ ^ 2 • posGraph q + ‖(posGraph q).val.fst‖ ^ 2 • negGraph q

@[simp]
theorem balancedNodalGraph_fst (q : SourceGraph) :
    (balancedNodalGraph q).val.fst =
      ‖(negGraph q).val.fst‖ ^ 2 • (posGraph q).val.fst +
        ‖(posGraph q).val.fst‖ ^ 2 • (negGraph q).val.fst := rfl

@[simp]
theorem balancedNodalGraph_snd (q : SourceGraph) :
    (balancedNodalGraph q).val.snd =
      ‖(negGraph q).val.fst‖ ^ 2 • (posGraph q).val.snd +
        ‖(posGraph q).val.fst‖ ^ 2 • (negGraph q).val.snd := rfl

/-- For every `q : SourceGraph`, `(balancedNodalGraph q).val.fst` is orthogonal to `q.val.fst` in `MassSpace`. -/
theorem inner_balancedNodalGraph_self_fst (q : SourceGraph) :
    ⟪(balancedNodalGraph q).val.fst, q.val.fst⟫_ℝ = 0 := by
  rw [balancedNodalGraph_fst, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_posGraph_self_fst, inner_negGraph_self_fst]
  ring

/-- For every `q : SourceGraph`,
`‖(balancedNodalGraph q).val.fst‖ ^ 2 = ‖q.val.fst‖ ^ 2 * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2)`. -/
theorem norm_balancedNodalGraph_fst_sq (q : SourceGraph) :
    ‖(balancedNodalGraph q).val.fst‖ ^ 2 =
      ‖q.val.fst‖ ^ 2 * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, balancedNodalGraph_fst,
    inner_add_left, inner_add_right, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm (posGraph q).val.fst (negGraph q).val.fst,
    inner_posGraph_negGraph_fst, ← norm_posGraph_fst_sq_add_negGraph_fst_sq q]
  ring

/-- For every `p : SourceGraph`,
`‖(balancedNodalGraph p).val.snd‖ ^ 2 = ‖(negGraph p).val.fst‖ ^ 4 * ‖(posGraph p).val.snd‖ ^ 2 + ‖(posGraph p).val.fst‖ ^ 4 * ‖(negGraph p).val.snd‖ ^ 2 + 2 * (‖(posGraph p).val.fst‖ ^ 2 * ‖(negGraph p).val.fst‖ ^ 2) * sourcePair (posGraph p) (negGraph p)`. -/
theorem norm_balancedNodalGraph_snd_sq (p : SourceGraph) :
    ‖(balancedNodalGraph p).val.snd‖ ^ 2 =
      ‖(negGraph p).val.fst‖ ^ 4 * ‖(posGraph p).val.snd‖ ^ 2 +
        ‖(posGraph p).val.fst‖ ^ 4 * ‖(negGraph p).val.snd‖ ^ 2 +
        2 * (‖(posGraph p).val.fst‖ ^ 2 * ‖(negGraph p).val.fst‖ ^ 2) *
          sourcePair (posGraph p) (negGraph p) := by
  rw [← real_inner_self_eq_norm_sq, balancedNodalGraph_snd,
    inner_add_left, inner_add_right, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm (posGraph p).val.snd (negGraph p).val.snd,
    ← sourcePair_posGraph_negGraph_eq_inner_snd]
  ring

/-- For every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`balancedNodalGraph q` is simultaneously orthogonal to `q` in `MassSpace`, `EdgeSpace`,
`sourcePair`, and `SourceGraph`. -/
theorem balancedNodalGraph_orthogonal_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) :
    let q := rieszLift w
    ⟪(balancedNodalGraph q).val.fst, q.val.fst⟫_ℝ = 0 ∧
      ⟪(balancedNodalGraph q).val.snd, q.val.snd⟫_ℝ = 0 ∧
      sourcePair (balancedNodalGraph q) q = 0 ∧
      ⟪balancedNodalGraph q, q⟫_ℝ = 0 := by
  intro q
  have hfst := inner_balancedNodalGraph_self_fst q
  have hsnd : ⟪(balancedNodalGraph q).val.snd, q.val.snd⟫_ℝ = 0 := by
    rw [inner_snd_rieszLift_of_eigenvector hμ heig (balancedNodalGraph q), hfst, mul_zero]
  have hpair : sourcePair (balancedNodalGraph q) q = 0 := by
    rw [sourcePair_rieszLift_eq_inner_of_eigenvector hμ heig (balancedNodalGraph q),
      real_inner_smul_right, hfst, mul_zero]
  have hgraph : ⟪balancedNodalGraph q, q⟫_ℝ = 0 := by
    rw [graph_inner, hfst, hsnd, add_zero]
  exact ⟨hfst, hsnd, hpair, hgraph⟩

/-- **Exact Edge Norm Squared of `balancedNodalGraph q` for Any Eigenvector**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`‖(balancedNodalGraph q).val.snd‖ ^ 2 = ‖q.val.fst‖ ^ 2 * (((1 - μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2) + sourcePair (posGraph q) (negGraph q) * ‖q.val.fst‖ ^ 2)`. -/
theorem norm_balancedNodalGraph_snd_sq_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) :
    let q := rieszLift w
    ‖(balancedNodalGraph q).val.snd‖ ^ 2 =
      ‖q.val.fst‖ ^ 2 *
        (((1 - μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2) +
          sourcePair (posGraph q) (negGraph q) * ‖q.val.fst‖ ^ 2) := by
  intro q
  have h1 := norm_balancedNodalGraph_snd_sq q
  have hp := norm_posGraph_snd_sq_rieszLift_of_eigenvector hμ heig
  have hn := norm_negGraph_snd_sq_rieszLift_of_eigenvector hμ heig
  have hsum := norm_posGraph_fst_sq_add_negGraph_fst_sq q
  change ‖(balancedNodalGraph (rieszLift w)).val.snd‖ ^ 2 = _ at h1
  rw [hp, hn] at h1
  calc ‖(balancedNodalGraph q).val.snd‖ ^ 2
      = ‖(negGraph (rieszLift w)).val.fst‖ ^ 4 *
          ((1 - μ) / μ * ‖(posGraph (rieszLift w)).val.fst‖ ^ 2 +
            sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w))) +
        ‖(posGraph (rieszLift w)).val.fst‖ ^ 4 *
          ((1 - μ) / μ * ‖(negGraph (rieszLift w)).val.fst‖ ^ 2 +
            sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w))) +
        2 * (‖(posGraph (rieszLift w)).val.fst‖ ^ 2 * ‖(negGraph (rieszLift w)).val.fst‖ ^ 2) *
          sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) := h1
    _ = (‖(posGraph q).val.fst‖ ^ 2 + ‖(negGraph q).val.fst‖ ^ 2) *
        (((1 - μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2) +
          sourcePair (posGraph q) (negGraph q) *
            (‖(posGraph q).val.fst‖ ^ 2 + ‖(negGraph q).val.fst‖ ^ 2)) := by
        change _ = (‖(posGraph (rieszLift w)).val.fst‖ ^ 2 + ‖(negGraph (rieszLift w)).val.fst‖ ^ 2) * _
        ring
    _ = ‖q.val.fst‖ ^ 2 *
        (((1 - μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2) +
          sourcePair (posGraph q) (negGraph q) * ‖q.val.fst‖ ^ 2) := by
        rw [hsum]

/-- **Exact Doob Energy of `balancedNodalGraph q` for Any Eigenvector**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`sourceEnergy (balancedNodalGraph q) = ‖q.val.fst‖ ^ 2 * (((1 - 2 * μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2) + sourcePair (posGraph q) (negGraph q) * ‖q.val.fst‖ ^ 2)`. -/
theorem sourceEnergy_balancedNodalGraph_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) :
    let q := rieszLift w
    sourceEnergy (balancedNodalGraph q) =
      ‖q.val.fst‖ ^ 2 *
        (((1 - 2 * μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2) +
          sourcePair (posGraph q) (negGraph q) * ‖q.val.fst‖ ^ 2) := by
  intro q
  have hE : sourceEnergy (balancedNodalGraph q) =
      ‖(balancedNodalGraph q).val.snd‖ ^ 2 - ‖(balancedNodalGraph q).val.fst‖ ^ 2 := rfl
  rw [hE, norm_balancedNodalGraph_snd_sq_of_eigenvector hμ heig, norm_balancedNodalGraph_fst_sq]
  have hid : (1 - μ) / μ - 1 = (1 - 2 * μ) / μ := by
    field_simp [hμ]
    ring
  calc ‖q.val.fst‖ ^ 2 *
        (((1 - μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2) +
          sourcePair (posGraph q) (negGraph q) * ‖q.val.fst‖ ^ 2) -
      ‖q.val.fst‖ ^ 2 * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2)
      = ‖q.val.fst‖ ^ 2 *
        (((1 - μ) / μ - 1) * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2) +
          sourcePair (posGraph q) (negGraph q) * ‖q.val.fst‖ ^ 2) := by ring
    _ = ‖q.val.fst‖ ^ 2 *
        (((1 - 2 * μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2) +
          sourcePair (posGraph q) (negGraph q) * ‖q.val.fst‖ ^ 2) := by rw [hid]

/-- **Sharp Product Nodal Cross-Jump Bound for Any Eigenvector**:
for every eigenvector `resolvent w = μ • w` (`μ ≠ 0`) with `q = rieszLift w`,
`-sourcePair (posGraph q) (negGraph q) * ‖q.val.fst‖ ^ 2 ≤ ((1 - μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2)`.
Because `4 * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2) ≤ ‖q.val.fst‖ ^ 4`, this
simultaneously refines both the factor-four bound `-4 * sourcePair (posGraph q) (negGraph q) ≤ ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2`
and the individual lobe bounds. -/
theorem neg_sourcePair_mul_norm_fst_sq_le_lobe_product_of_eigenvector
    {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace} (heig : resolvent w = μ • w) :
    let q := rieszLift w;
    -sourcePair (posGraph q) (negGraph q) * ‖q.val.fst‖ ^ 2 ≤
      ((1 - μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2) := by
  intro q
  by_cases hq : ‖q.val.fst‖ ^ 2 = 0
  · have hpos0 : ‖(posGraph q).val.fst‖ ^ 2 = 0 := by
      have hsum := norm_posGraph_fst_sq_add_negGraph_fst_sq q
      linarith [sq_nonneg ‖(posGraph q).val.fst‖, sq_nonneg ‖(negGraph q).val.fst‖]
    rw [hq, hpos0, mul_zero, zero_mul, mul_zero]
  · have hpos : 0 < ‖q.val.fst‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hq)
    have hsnd := norm_balancedNodalGraph_snd_sq_of_eigenvector hμ heig
    have hnn : 0 ≤ ‖(balancedNodalGraph q).val.snd‖ ^ 2 := sq_nonneg _
    rw [hsnd] at hnn
    have h1 : 0 ≤ ((1 - μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2) +
        sourcePair (posGraph q) (negGraph q) * ‖q.val.fst‖ ^ 2 :=
      nonneg_of_mul_nonneg_right hnn hpos
    linarith

/-- For every primitive `q : SourceGraph` (`⟪q.val.fst, oneL⟫_ℝ = 0`),
`⟪(balancedNodalGraph q).val.fst, oneL⟫_ℝ = (1 / 2) * ‖q.val.fst‖ ^ 2 * ⟪(absGraph q).val.fst, oneL⟫_ℝ`,
`⟪(primGraph (balancedNodalGraph q)).val.fst, oneL⟫_ℝ = 0`,
and `⟪(primGraph (balancedNodalGraph q)).val.fst, q.val.fst⟫_ℝ = 0`. -/
theorem primGraph_balancedNodalGraph_orthogonal_of_primitive {q : SourceGraph}
    (hq : ⟪q.val.fst, oneL⟫_ℝ = 0) :
    ⟪(balancedNodalGraph q).val.fst, oneL⟫_ℝ =
        (1 / 2 : ℝ) * ‖q.val.fst‖ ^ 2 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ∧
      ⟪(primGraph (balancedNodalGraph q)).val.fst, oneL⟫_ℝ = 0 ∧
      ⟪(primGraph (balancedNodalGraph q)).val.fst, q.val.fst⟫_ℝ = 0 := by
  obtain ⟨_, hp1, hn1⟩ := inner_posGraph_and_negGraph_oneL_eq_half_absGraph_of_primitive hq
  have hsum := norm_posGraph_fst_sq_add_negGraph_fst_sq q
  have h1 : ⟪(balancedNodalGraph q).val.fst, oneL⟫_ℝ =
      (1 / 2 : ℝ) * ‖q.val.fst‖ ^ 2 * ⟪(absGraph q).val.fst, oneL⟫_ℝ := by
    rw [balancedNodalGraph_fst, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      hp1, hn1, ← hsum]
    ring
  have h2 : ⟪(primGraph (balancedNodalGraph q)).val.fst, oneL⟫_ℝ = 0 :=
    inner_primGraph_oneL (balancedNodalGraph q)
  have h3 : ⟪(primGraph (balancedNodalGraph q)).val.fst, q.val.fst⟫_ℝ = 0 := by
    rw [primGraph_fst, inner_sub_left, real_inner_smul_left,
      inner_balancedNodalGraph_self_fst, real_inner_comm q.val.fst oneL, hq,
      mul_zero, sub_zero]
  exact ⟨h1, h2, h3⟩

/-- **Simultaneous Orthogonality and Exact Doob Energy of `primGraph (balancedNodalGraph q)` for Primitive Eigenvectors**:
for every primitive eigenvector `resolvent w = μ • w` (`μ ≠ 0`, `⟪w, oneL⟫_ℝ = 0`) with
`q = rieszLift w`, the primitive balanced nodal vector `primGraph (balancedNodalGraph q)` is
simultaneously orthogonal to `oneL` and to `q.val.fst` (in `MassSpace`, `EdgeSpace`, and `sourcePair`),
and satisfies
`sourceEnergy (primGraph (balancedNodalGraph q)) = ((1 - 2 * μ) / μ) * ‖(primGraph (balancedNodalGraph q)).val.fst‖ ^ 2 + ‖q.val.fst‖ ^ 4 * (sourcePair (posGraph q) (negGraph q) + ((1 - μ) / (2 * μ)) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2)`. -/
theorem primGraph_balancedNodalGraph_orthogonal_and_energy_of_primitive_eigenvector
    {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace} (hprim : ⟪w, oneL⟫_ℝ = 0)
    (heig : resolvent w = μ • w) :
    let q := rieszLift w
    ⟪(primGraph (balancedNodalGraph q)).val.fst, oneL⟫_ℝ = 0 ∧
      ⟪(primGraph (balancedNodalGraph q)).val.fst, q.val.fst⟫_ℝ = 0 ∧
      sourcePair (primGraph (balancedNodalGraph q)) q = 0 ∧
      sourceEnergy (primGraph (balancedNodalGraph q)) =
        ((1 - 2 * μ) / μ) * ‖(primGraph (balancedNodalGraph q)).val.fst‖ ^ 2 +
          ‖q.val.fst‖ ^ 4 *
            (sourcePair (posGraph q) (negGraph q) +
              ((1 - μ) / (2 * μ)) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2) := by
  intro q
  have hq_prim : ⟪q.val.fst, oneL⟫_ℝ = 0 := by
    change ⟪resolvent w, oneL⟫_ℝ = 0
    rw [heig, real_inner_smul_left, hprim, mul_zero]
  obtain ⟨hinner1, hprim1, horth⟩ := primGraph_balancedNodalGraph_orthogonal_of_primitive hq_prim
  have hpair : sourcePair (primGraph (balancedNodalGraph q)) q = 0 := by
    rw [sourcePair_rieszLift_eq_inner_of_eigenvector hμ heig (primGraph (balancedNodalGraph q)),
      real_inner_smul_right, horth, mul_zero]
  have hnorm : ‖(balancedNodalGraph q).val.fst‖ ^ 2 =
      ‖(primGraph (balancedNodalGraph q)).val.fst‖ ^ 2 +
        2 * ⟪(balancedNodalGraph q).val.fst, oneL⟫_ℝ ^ 2 := by
    rw [norm_primGraph_fst_sq]
    ring
  have hprod : ‖q.val.fst‖ ^ 2 * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2) =
      ‖(primGraph (balancedNodalGraph q)).val.fst‖ ^ 2 +
        (1 / 2 : ℝ) * ‖q.val.fst‖ ^ 4 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 := by
    rw [← norm_balancedNodalGraph_fst_sq, hnorm, hinner1]
    ring
  have hE := sourceEnergy_balancedNodalGraph_of_eigenvector hμ heig
  have hEp : sourceEnergy (primGraph (balancedNodalGraph q)) =
      sourceEnergy (balancedNodalGraph q) +
        (1 / 2 : ℝ) * ‖q.val.fst‖ ^ 4 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 := by
    rw [sourceEnergy_primGraph, hinner1]
    ring
  refine ⟨hprim1, horth, hpair, ?_⟩
  rw [hEp]
  change sourceEnergy (balancedNodalGraph (rieszLift w)) +
      (1 / 2 : ℝ) * ‖q.val.fst‖ ^ 4 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 = _
  rw [hE]
  change ‖q.val.fst‖ ^ 2 *
        (((1 - 2 * μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2) +
          sourcePair (posGraph q) (negGraph q) * ‖q.val.fst‖ ^ 2) +
      (1 / 2 : ℝ) * ‖q.val.fst‖ ^ 4 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 = _
  calc ‖q.val.fst‖ ^ 2 *
        (((1 - 2 * μ) / μ) * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2) +
          sourcePair (posGraph q) (negGraph q) * ‖q.val.fst‖ ^ 2) +
      (1 / 2 : ℝ) * ‖q.val.fst‖ ^ 4 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2
      = ((1 - 2 * μ) / μ) *
          (‖q.val.fst‖ ^ 2 * (‖(posGraph q).val.fst‖ ^ 2 * ‖(negGraph q).val.fst‖ ^ 2)) +
        ‖q.val.fst‖ ^ 4 * sourcePair (posGraph q) (negGraph q) +
        (1 / 2 : ℝ) * ‖q.val.fst‖ ^ 4 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 := by ring
    _ = ((1 - 2 * μ) / μ) *
          (‖(primGraph (balancedNodalGraph q)).val.fst‖ ^ 2 +
            (1 / 2 : ℝ) * ‖q.val.fst‖ ^ 4 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2) +
        ‖q.val.fst‖ ^ 4 * sourcePair (posGraph q) (negGraph q) +
        (1 / 2 : ℝ) * ‖q.val.fst‖ ^ 4 * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2 := by rw [hprod]
    _ = ((1 - 2 * μ) / μ) * ‖(primGraph (balancedNodalGraph q)).val.fst‖ ^ 2 +
        ‖q.val.fst‖ ^ 4 *
          (sourcePair (posGraph q) (negGraph q) +
            ((1 - μ) / (2 * μ)) * ⟪(absGraph q).val.fst, oneL⟫_ℝ ^ 2) := by
        field_simp [hμ]
        ring

end RHTower.CHMDPolar
