import GaloisForLFunctions.RHTower.CHMDStationaryRayleighBoundsAndNodalBoost

/-!
# Strict Contraction of `stationaryResolvent`, the Second-Resolvent Identity, and Eigenvector Stationary Equations

This module establishes the strict contraction property of `stationaryResolvent` on `MassSpace`,
the exact second-resolvent identities linking `resolvent` and `stationaryResolvent`, the
stationary resolvent equations and Cauchy–Schwarz bounds for `resolvent` eigenvectors, and the
nodal lobe additivity of the diagonal forms (`thetaToVolume`, `archDiagonalOperator`,
`primeDiagonalOperator`, `groundPotentialOperator`):

1. **Strict Contraction and Positivity of `stationaryResolvent` on `MassSpace`**:
   - `stationaryEnergy_stationaryResolvent`: for every `w : MassSpace`,
     `stationaryEnergy (thetaProduct (stationaryResolvent w)) = ⟪stationaryResolvent w, w⟫_ℝ - ‖stationaryResolvent w‖ ^ 2`.
   - `norm_stationaryResolvent_sq_le_inner` and `inner_stationaryResolvent_self_nonneg`:
     `0 ≤ ‖stationaryResolvent w‖ ^ 2 ≤ ⟪stationaryResolvent w, w⟫_ℝ ≤ ‖w‖ ^ 2` and
     `‖stationaryResolvent w‖ ≤ ‖w‖`.
   - `stationaryEnergy_stationaryResolvent_pos_of_ne_zero` and
     `norm_stationaryResolvent_sq_lt_inner_lt_norm_sq_of_ne_zero`: because `stationaryGroundGraph`
     has no constant zero mode (`stationaryGround_edge_zero_iff`), for every `w ≠ 0`,
     `0 < stationaryEnergy (thetaProduct (stationaryResolvent w))` and
     `0 < ‖stationaryResolvent w‖ ^ 2 < ⟪stationaryResolvent w, w⟫_ℝ < ‖w‖ ^ 2`.
   - `stationaryResolvent_eigenvalue_mem_Ioo`: every eigenvalue `σ` of `stationaryResolvent`
     (`stationaryResolvent w = σ • w`, `w ≠ 0`) satisfies `0 < σ < 1`.

2. **Exact Second-Resolvent Identities (`resolvent` vs `stationaryResolvent`)**:
   - `resolvent_sub_stationaryResolvent_eq` and `resolvent_add_stationaryResolvent_resolvent_eq`:
     for every `w : MassSpace`,
     `resolvent w + stationaryResolvent (resolvent w) = stationaryResolvent w + stationaryResolvent (archDiagonalOperator (resolvent w) + primeShiftOperator (resolvent w))`
     and
     `resolvent w + resolvent (stationaryResolvent w) = stationaryResolvent w + resolvent (archDiagonalOperator (stationaryResolvent w) + primeShiftOperator (stationaryResolvent w))`.
   - `inner_resolvent_sub_stationaryResolvent`: for all `u, v : MassSpace`,
     `⟪resolvent u, v⟫_ℝ - ⟪stationaryResolvent u, v⟫_ℝ = ⟪archDiagonalOperator (resolvent u) + primeShiftOperator (resolvent u) - resolvent u, stationaryResolvent v⟫_ℝ`.

3. **Stationary Resolvent Equations and Rayleigh Bounds for `resolvent` Eigenvectors**:
   - `eigenvector_stationaryResolvent_identity`: for every eigenvector `resolvent u = μ • u`,
     `μ • u - (1 - μ) • stationaryResolvent u = μ • stationaryResolvent (archDiagonalOperator u + primeShiftOperator u)`.
   - `eigenvector_inner_sub_stationaryResolvent`: for every eigenvector `resolvent u = μ • u` (`μ ≠ 0`)
     and every `v : MassSpace`,
     `⟪u, v⟫_ℝ - ((1 - μ) / μ) * ⟪stationaryResolvent u, v⟫_ℝ = ⟪archDiagonalOperator u + primeShiftOperator u, stationaryResolvent v⟫_ℝ`.
   - `eigenvector_norm_pow_four_le_stationaryResolvent_mul`: for every eigenvector `resolvent u = μ • u` (`μ ≠ 0`),
     `‖u‖ ^ 4 ≤ ⟪stationaryResolvent u, u⟫_ℝ * (((1 - μ) / μ) * ‖u‖ ^ 2 + archGroundConstant * ‖thetaToVolume u‖ ^ 2 + ⟪primeShiftOperator u, u⟫_ℝ)`.
   - `eigenvector_norm_pow_four_le_stationaryResolvent_absGraph_mul`: zero-mode-free nodal contraction
     Cauchy–Schwarz bound for any eigenvector `resolvent u = μ • u` via `absGraph (rieszLift u)`.

4. **Nodal Lobe Additivity of the Diagonal Forms**:
   - `norm_thetaToVolume_sq_eq_posGraph_add_negGraph`,
   - `inner_archDiagonalOperator_self_eq_posGraph_add_negGraph`,
   - `inner_primeDiagonalOperator_self_eq_posGraph_add_negGraph`,
   - `inner_groundPotentialOperator_self_eq_posGraph_add_negGraph`,
   - `inner_archDiagonalOperator_posGraph_and_negGraph_self`.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump CHMDTranslation ThetaSourceWard

/-! ## Section 1: Strict Contraction and Positivity of `stationaryResolvent` on `MassSpace` -/

/-- For every `w : MassSpace`,
`⟪stationaryResolvent w, w⟫_ℝ = ‖stationaryResolvent w‖ ^ 2 + stationaryEnergy (thetaProduct (stationaryResolvent w))`. -/
theorem inner_stationaryResolvent_eq_norm_sq_add_stationaryEnergy (w : MassSpace) :
    ⟪stationaryResolvent w, w⟫_ℝ =
      ‖stationaryResolvent w‖ ^ 2 + stationaryEnergy (thetaProduct (stationaryResolvent w)) := by
  rw [inner_stationaryResolvent_self, norm_stationaryGroundGraph_sq]
  rfl

/-- For every `w : MassSpace`,
`stationaryEnergy (thetaProduct (stationaryResolvent w)) = ⟪stationaryResolvent w, w⟫_ℝ - ‖stationaryResolvent w‖ ^ 2`. -/
theorem stationaryEnergy_stationaryResolvent (w : MassSpace) :
    stationaryEnergy (thetaProduct (stationaryResolvent w)) =
      ⟪stationaryResolvent w, w⟫_ℝ - ‖stationaryResolvent w‖ ^ 2 := by
  have h := inner_stationaryResolvent_eq_norm_sq_add_stationaryEnergy w
  linarith

/-- For every `w : MassSpace`, `0 ≤ stationaryEnergy (thetaProduct (stationaryResolvent w))`. -/
theorem stationaryEnergy_stationaryResolvent_nonneg (w : MassSpace) :
    0 ≤ stationaryEnergy (thetaProduct (stationaryResolvent w)) := by
  change 0 ≤ stationaryEnergy (thetaProduct (stationaryRieszLift w).val.fst)
  rw [← stationaryGround_edge_energy]
  exact sq_nonneg _

/-- For every `w : MassSpace`, `‖stationaryResolvent w‖ ^ 2 ≤ ⟪stationaryResolvent w, w⟫_ℝ`. -/
theorem norm_stationaryResolvent_sq_le_inner (w : MassSpace) :
    ‖stationaryResolvent w‖ ^ 2 ≤ ⟪stationaryResolvent w, w⟫_ℝ := by
  have h := stationaryEnergy_stationaryResolvent_nonneg w
  rw [stationaryEnergy_stationaryResolvent] at h
  linarith

/-- For every `w : MassSpace`, `0 ≤ ⟪stationaryResolvent w, w⟫_ℝ`. -/
theorem inner_stationaryResolvent_self_nonneg (w : MassSpace) :
    0 ≤ ⟪stationaryResolvent w, w⟫_ℝ := by
  rw [inner_stationaryResolvent_self]
  exact sq_nonneg _

/-- For every `w : MassSpace`, `⟪stationaryResolvent w, w⟫_ℝ ≤ ‖stationaryResolvent w‖ * ‖w‖`. -/
theorem inner_stationaryResolvent_le_norm_mul_norm (w : MassSpace) :
    ⟪stationaryResolvent w, w⟫_ℝ ≤ ‖stationaryResolvent w‖ * ‖w‖ :=
  real_inner_le_norm _ _

/-- Contraction bound `‖stationaryResolvent w‖ ≤ ‖w‖` for every `w : MassSpace`. -/
theorem norm_stationaryResolvent_le (w : MassSpace) :
    ‖stationaryResolvent w‖ ≤ ‖w‖ := by
  have h1 := norm_stationaryResolvent_sq_le_inner w
  have h2 := inner_stationaryResolvent_le_norm_mul_norm w
  nlinarith [norm_nonneg (stationaryResolvent w), norm_nonneg w]

/-- Quadratic contraction bound `⟪stationaryResolvent w, w⟫_ℝ ≤ ‖w‖ ^ 2` for every `w : MassSpace`. -/
theorem inner_stationaryResolvent_self_le_norm_sq (w : MassSpace) :
    ⟪stationaryResolvent w, w⟫_ℝ ≤ ‖w‖ ^ 2 := by
  have h1 := inner_stationaryResolvent_le_norm_mul_norm w
  have h2 := norm_stationaryResolvent_le w
  nlinarith [norm_nonneg (stationaryResolvent w), norm_nonneg w]

/-- Because `stationaryGroundGraph` has no constant zero mode (`stationaryGround_edge_zero_iff`),
for every `w ≠ 0`, `0 < stationaryEnergy (thetaProduct (stationaryResolvent w))`. -/
theorem stationaryEnergy_stationaryResolvent_pos_of_ne_zero {w : MassSpace} (hw : w ≠ 0) :
    0 < stationaryEnergy (thetaProduct (stationaryResolvent w)) := by
  change 0 < stationaryEnergy (thetaProduct (stationaryRieszLift w).val.fst)
  rw [← stationaryGround_edge_energy]
  have hr : stationaryRieszLift w ≠ 0 := by
    intro h0
    apply hw
    apply stationaryResolvent_injective
    rw [stationaryResolvent_apply, h0, map_zero, map_zero]
  have hsnd : (stationaryRieszLift w).val.snd ≠ 0 :=
    fun h => hr ((stationaryGround_edge_zero_iff _).mp h)
  exact sq_pos_of_pos (norm_pos_iff.mpr hsnd)

/-- **Strict Contraction of `stationaryResolvent` on Nonzero Vectors**:
for every `w ≠ 0`,
`0 < ‖stationaryResolvent w‖ ^ 2`,
`‖stationaryResolvent w‖ ^ 2 < ⟪stationaryResolvent w, w⟫_ℝ`,
`⟪stationaryResolvent w, w⟫_ℝ < ‖w‖ ^ 2`, and `‖stationaryResolvent w‖ < ‖w‖`. -/
theorem norm_stationaryResolvent_sq_lt_inner_lt_norm_sq_of_ne_zero {w : MassSpace} (hw : w ≠ 0) :
    0 < ‖stationaryResolvent w‖ ^ 2 ∧
      ‖stationaryResolvent w‖ ^ 2 < ⟪stationaryResolvent w, w⟫_ℝ ∧
      ⟪stationaryResolvent w, w⟫_ℝ < ‖w‖ ^ 2 ∧
      ‖stationaryResolvent w‖ < ‖w‖ := by
  have hne : stationaryResolvent w ≠ 0 :=
    fun h => hw (stationaryResolvent_injective (h.trans (map_zero _).symm))
  have hnorm_pos : 0 < ‖stationaryResolvent w‖ := norm_pos_iff.mpr hne
  have hsq_pos : 0 < ‖stationaryResolvent w‖ ^ 2 := sq_pos_of_pos hnorm_pos
  have hE_pos := stationaryEnergy_stationaryResolvent_pos_of_ne_zero hw
  rw [stationaryEnergy_stationaryResolvent] at hE_pos
  have hlt1 : ‖stationaryResolvent w‖ ^ 2 < ⟪stationaryResolvent w, w⟫_ℝ := by linarith
  have hcs := inner_stationaryResolvent_le_norm_mul_norm w
  have hlt_norm : ‖stationaryResolvent w‖ < ‖w‖ := by nlinarith
  have hlt2 : ⟪stationaryResolvent w, w⟫_ℝ < ‖w‖ ^ 2 := by nlinarith
  exact ⟨hsq_pos, hlt1, hlt2, hlt_norm⟩

/-- Every eigenvalue `σ` of `stationaryResolvent` on a nonzero vector `w ≠ 0` lies strictly
in the open unit interval `(0, 1)`. -/
theorem stationaryResolvent_eigenvalue_mem_Ioo {σ : ℝ} {w : MassSpace}
    (hw : w ≠ 0) (heig : stationaryResolvent w = σ • w) :
    0 < σ ∧ σ < 1 := by
  have hpos : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
  obtain ⟨_, hlt1, hlt2, _⟩ := norm_stationaryResolvent_sq_lt_inner_lt_norm_sq_of_ne_zero hw
  have hin : ⟪stationaryResolvent w, w⟫_ℝ = σ * ‖w‖ ^ 2 := by
    rw [heig, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hsq_nn : 0 ≤ ‖stationaryResolvent w‖ ^ 2 := sq_nonneg _
  constructor <;> nlinarith

/-! ## Section 2: Exact Second-Resolvent Identities (`resolvent` vs `stationaryResolvent`) -/

/-- For every `u : MassSpace`,
`-groundPerturbation u = archDiagonalOperator u + primeShiftOperator u - u`. -/
theorem neg_groundPerturbation_eq (u : MassSpace) :
    -groundPerturbation u = archDiagonalOperator u + primeShiftOperator u - u := by
  have h := congrArg (fun T : MassSpace →L[ℝ] MassSpace => T u) groundPerturbation_sub_id_eq
  change groundPerturbation u - u = -primeShiftOperator u - archDiagonalOperator u at h
  have h2 : groundPerturbation u = -primeShiftOperator u - archDiagonalOperator u + u :=
    sub_eq_iff_eq_add.mp h
  rw [h2]
  abel

/-- **First Second-Resolvent Identity**:
for every `w : MassSpace`,
`resolvent w - stationaryResolvent w = -stationaryResolvent (groundPerturbation (resolvent w))`. -/
theorem resolvent_sub_stationaryResolvent_eq_neg_stationaryResolvent (w : MassSpace) :
    resolvent w - stationaryResolvent w =
      -stationaryResolvent (groundPerturbation (resolvent w)) := by
  have h := (stationaryResolvent_full_shift w).symm
  rw [map_sub, sub_eq_add_neg] at h
  exact sub_eq_iff_eq_add'.mpr h

/-- **Explicit Second-Resolvent Identity via `stationaryResolvent`**:
for every `w : MassSpace`,
`resolvent w - stationaryResolvent w = stationaryResolvent (archDiagonalOperator (resolvent w) + primeShiftOperator (resolvent w) - resolvent w)`. -/
theorem resolvent_sub_stationaryResolvent_eq (w : MassSpace) :
    resolvent w - stationaryResolvent w =
      stationaryResolvent
        (archDiagonalOperator (resolvent w) + primeShiftOperator (resolvent w) - resolvent w) := by
  have h := (stationaryResolvent_full_shift w).symm
  have h1 : w - groundPerturbation (resolvent w) =
      w + (archDiagonalOperator (resolvent w) + primeShiftOperator (resolvent w) - resolvent w) := by
    rw [sub_eq_add_neg, neg_groundPerturbation_eq]
  rw [h1, map_add] at h
  exact sub_eq_iff_eq_add'.mpr h

/-- **Additive Second-Resolvent Identity via `stationaryResolvent`**:
for every `w : MassSpace`,
`resolvent w + stationaryResolvent (resolvent w) = stationaryResolvent w + stationaryResolvent (archDiagonalOperator (resolvent w) + primeShiftOperator (resolvent w))`. -/
theorem resolvent_add_stationaryResolvent_resolvent_eq (w : MassSpace) :
    resolvent w + stationaryResolvent (resolvent w) =
      stationaryResolvent w +
        stationaryResolvent
          (archDiagonalOperator (resolvent w) + primeShiftOperator (resolvent w)) := by
  have h := resolvent_sub_stationaryResolvent_eq w
  calc resolvent w + stationaryResolvent (resolvent w)
      = (resolvent w - stationaryResolvent w) + stationaryResolvent w +
          stationaryResolvent (resolvent w) := by abel
    _ = stationaryResolvent w +
          stationaryResolvent
            (archDiagonalOperator (resolvent w) + primeShiftOperator (resolvent w)) := by
        rw [h, map_sub]
        abel

/-- **Dual Second-Resolvent Identity via `resolvent`**:
for every `w : MassSpace`,
`resolvent w - stationaryResolvent w = resolvent (archDiagonalOperator (stationaryResolvent w) + primeShiftOperator (stationaryResolvent w) - stationaryResolvent w)`. -/
theorem resolvent_sub_stationaryResolvent_eq_dual (w : MassSpace) :
    resolvent w - stationaryResolvent w =
      resolvent
        (archDiagonalOperator (stationaryResolvent w) +
          primeShiftOperator (stationaryResolvent w) - stationaryResolvent w) := by
  have h := fullResolvent_stationary_shift w
  have h1 : w + groundPerturbation (stationaryResolvent w) =
      w - (archDiagonalOperator (stationaryResolvent w) +
        primeShiftOperator (stationaryResolvent w) - stationaryResolvent w) := by
    have h2 := neg_groundPerturbation_eq (stationaryResolvent w)
    calc w + groundPerturbation (stationaryResolvent w)
        = w - (-groundPerturbation (stationaryResolvent w)) := by abel
      _ = w - (archDiagonalOperator (stationaryResolvent w) +
            primeShiftOperator (stationaryResolvent w) - stationaryResolvent w) := by rw [h2]
  rw [h1, map_sub] at h
  exact sub_eq_iff_eq_add.mpr (sub_eq_iff_eq_add'.mp h)

/-- **Bilinear Second-Resolvent Identity**:
for all `u, v : MassSpace`,
`⟪resolvent u, v⟫_ℝ - ⟪stationaryResolvent u, v⟫_ℝ = ⟪archDiagonalOperator (resolvent u) + primeShiftOperator (resolvent u) - resolvent u, stationaryResolvent v⟫_ℝ`. -/
theorem inner_resolvent_sub_stationaryResolvent (u v : MassSpace) :
    ⟪resolvent u, v⟫_ℝ - ⟪stationaryResolvent u, v⟫_ℝ =
      ⟪archDiagonalOperator (resolvent u) + primeShiftOperator (resolvent u) - resolvent u,
        stationaryResolvent v⟫_ℝ := by
  rw [← inner_sub_left, resolvent_sub_stationaryResolvent_eq, stationaryResolvent_symm]

/-! ## Section 3: Stationary Resolvent Equations and Rayleigh Bounds for `resolvent` Eigenvectors -/

/-- **Exact `stationaryResolvent` Identity for Any `resolvent` Eigenvector**:
if `resolvent u = μ • u`, then
`μ • u - (1 - μ) • stationaryResolvent u = μ • stationaryResolvent (archDiagonalOperator u + primeShiftOperator u)`. -/
theorem eigenvector_stationaryResolvent_identity {μ : ℝ} {u : MassSpace}
    (heig : resolvent u = μ • u) :
    μ • u - (1 - μ) • stationaryResolvent u =
      μ • stationaryResolvent (archDiagonalOperator u + primeShiftOperator u) := by
  have h := resolvent_sub_stationaryResolvent_eq u
  rw [heig, map_smul, map_smul, ← smul_add, ← smul_sub, map_smul, map_sub] at h
  calc μ • u - (1 - μ) • stationaryResolvent u
      = (resolvent u - stationaryResolvent u) + μ • stationaryResolvent u := by
        rw [heig, sub_smul, one_smul]
        abel
    _ = μ • stationaryResolvent (archDiagonalOperator u + primeShiftOperator u) := by
        rw [heig, h, smul_sub]
        abel

/-- **Normalized `stationaryResolvent` Identity for Any Nonzero-Eigenvalue `resolvent` Eigenvector**:
if `resolvent u = μ • u` (`μ ≠ 0`), then
`u - ((1 - μ) / μ) • stationaryResolvent u = stationaryResolvent (archDiagonalOperator u + primeShiftOperator u)`. -/
theorem eigenvector_stationaryResolvent_identity_div {μ : ℝ} (hμ : μ ≠ 0) {u : MassSpace}
    (heig : resolvent u = μ • u) :
    u - ((1 - μ) / μ) • stationaryResolvent u =
      stationaryResolvent (archDiagonalOperator u + primeShiftOperator u) := by
  have h := congrArg (fun v : MassSpace => μ⁻¹ • v) (eigenvector_stationaryResolvent_identity heig)
  rw [smul_sub, inv_smul_smul₀ hμ, smul_smul, inv_smul_smul₀ hμ] at h
  rwa [div_eq_inv_mul]

/-- **Bilinear `stationaryResolvent` Pairing Identity for a `resolvent` Eigenvector**:
if `resolvent u = μ • u` (`μ ≠ 0`), then for every `v : MassSpace`,
`⟪u, v⟫_ℝ - ((1 - μ) / μ) * ⟪stationaryResolvent u, v⟫_ℝ = ⟪archDiagonalOperator u + primeShiftOperator u, stationaryResolvent v⟫_ℝ`. -/
theorem eigenvector_inner_sub_stationaryResolvent {μ : ℝ} (hμ : μ ≠ 0) {u : MassSpace}
    (heig : resolvent u = μ • u) (v : MassSpace) :
    ⟪u, v⟫_ℝ - ((1 - μ) / μ) * ⟪stationaryResolvent u, v⟫_ℝ =
      ⟪archDiagonalOperator u + primeShiftOperator u, stationaryResolvent v⟫_ℝ := by
  have h := congrArg (fun w : MassSpace => ⟪w, v⟫_ℝ)
    (eigenvector_stationaryResolvent_identity_div hμ heig)
  rw [inner_sub_left, real_inner_smul_left,
    stationaryResolvent_symm (archDiagonalOperator u + primeShiftOperator u) v] at h
  exact h

/-- **Stationary Energy of an Eigenvector `resolvent u = μ • u` (`μ ≠ 0`)**:
`stationaryEnergy (thetaProduct u) = ((1 - 2 * μ) / μ) * ‖u‖ ^ 2 + archGroundConstant * ‖thetaToVolume u‖ ^ 2 + ⟪primeShiftOperator u, u⟫_ℝ`. -/
theorem stationaryEnergy_of_resolvent_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {u : MassSpace}
    (heig : resolvent u = μ • u) :
    stationaryEnergy (thetaProduct u) =
      ((1 - 2 * μ) / μ) * ‖u‖ ^ 2 +
        archGroundConstant * ‖thetaToVolume u‖ ^ 2 +
        ⟪primeShiftOperator u, u⟫_ℝ := by
  have heig' : resolvent (μ⁻¹ • u) = μ • (μ⁻¹ • u) := by
    rw [map_smul, heig, smul_comm]
  set q : SourceGraph := rieszLift (μ⁻¹ • u)
  have hq_fst : q.val.fst = u := by
    change resolvent (μ⁻¹ • u) = u
    rw [map_smul, heig, inv_smul_smul₀ hμ]
  have hq_pair := sourcePair_rieszLift_eq_inner_of_eigenvector hμ heig'
  have hstat := stationaryEnergy_of_sourcePair_eq_inner hq_pair
  rw [hq_fst, real_inner_smul_right, real_inner_self_eq_norm_sq] at hstat
  linarith

/-- **`stationaryResolvent` Cauchy–Schwarz Inequality for Any `resolvent` Eigenvector**:
if `resolvent u = μ • u` (`μ ≠ 0`), then
`‖u‖ ^ 4 ≤ ⟪stationaryResolvent u, u⟫_ℝ * (((1 - μ) / μ) * ‖u‖ ^ 2 + archGroundConstant * ‖thetaToVolume u‖ ^ 2 + ⟪primeShiftOperator u, u⟫_ℝ)`. -/
theorem eigenvector_norm_pow_four_le_stationaryResolvent_mul {μ : ℝ} (hμ : μ ≠ 0) {u : MassSpace}
    (heig : resolvent u = μ • u) :
    ‖u‖ ^ 4 ≤
      ⟪stationaryResolvent u, u⟫_ℝ *
        (((1 - μ) / μ) * ‖u‖ ^ 2 +
          archGroundConstant * ‖thetaToVolume u‖ ^ 2 +
          ⟪primeShiftOperator u, u⟫_ℝ) := by
  set q : SourceGraph := rieszLift (μ⁻¹ • u)
  have hq_fst : q.val.fst = u := by
    change resolvent (μ⁻¹ • u) = u
    rw [map_smul, heig, inv_smul_smul₀ hμ]
  have hcs := norm_fst_pow_four_le_inner_stationaryResolvent_mul q
  rw [hq_fst, stationaryEnergy_of_resolvent_eigenvector hμ heig] at hcs
  have hid : ((1 - 2 * μ) / μ) * ‖u‖ ^ 2 +
      archGroundConstant * ‖thetaToVolume u‖ ^ 2 + ⟪primeShiftOperator u, u⟫_ℝ + ‖u‖ ^ 2 =
      ((1 - μ) / μ) * ‖u‖ ^ 2 +
        archGroundConstant * ‖thetaToVolume u‖ ^ 2 + ⟪primeShiftOperator u, u⟫_ℝ := by
    have h1 : ((1 - 2 * μ) / μ) * ‖u‖ ^ 2 + ‖u‖ ^ 2 = ((1 - μ) / μ) * ‖u‖ ^ 2 := by
      field_simp [hμ]
      ring
    linarith
  rwa [hid] at hcs

/-- **Zero-Mode-Free Nodal Contraction `stationaryResolvent` Cauchy–Schwarz Bound for an Eigenvector**:
for any eigenvector `resolvent u = μ • u` (`μ ≠ 0`) with `q = rieszLift u` (`q.val.fst = μ • u`),
`‖q.val.fst‖ ^ 4 ≤ ⟪stationaryResolvent (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ * (((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 + 4 * sourcePair (posGraph q) (negGraph q) + archGroundConstant * ‖thetaToVolume q.val.fst‖ ^ 2 + ⟪primeShiftOperator (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ)`. -/
theorem eigenvector_norm_pow_four_le_stationaryResolvent_absGraph_mul {μ : ℝ} (hμ : μ ≠ 0)
    {u : MassSpace} (heig : resolvent u = μ • u) :
    let q := rieszLift u
    ‖q.val.fst‖ ^ 4 ≤
      ⟪stationaryResolvent (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ *
        (((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 +
          4 * sourcePair (posGraph q) (negGraph q) +
          archGroundConstant * ‖thetaToVolume q.val.fst‖ ^ 2 +
          ⟪primeShiftOperator (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ) := by
  intro q
  have hcs := norm_fst_pow_four_le_inner_stationaryResolvent_mul (absGraph q)
  have hnorm : ‖(absGraph q).val.fst‖ ^ 4 = ‖q.val.fst‖ ^ 4 := by
    have h2 : ‖(absGraph q).val.fst‖ ^ 2 = ‖q.val.fst‖ ^ 2 := norm_absGraph_fst_sq q
    calc ‖(absGraph q).val.fst‖ ^ 4 = (‖(absGraph q).val.fst‖ ^ 2) ^ 2 := by ring
      _ = (‖q.val.fst‖ ^ 2) ^ 2 := by rw [h2]
      _ = ‖q.val.fst‖ ^ 4 := by ring
  have hstat := sourceEnergy_eq_stationary_sub_arch_sub_primeShift (absGraph q)
  rw [sourceEnergy_absGraph_eq, norm_thetaToVolume_absGraph_sq] at hstat
  have hqE : sourceEnergy q = ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ 2 := by
    have h1 := sourceEnergy_eq_inner_of_sourcePair_eq_inner
      (sourcePair_rieszLift_eq_inner_of_eigenvector hμ heig)
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq] at h1
    exact h1
  have hid : stationaryEnergy (thetaProduct (absGraph q).val.fst) + ‖(absGraph q).val.fst‖ ^ 2 =
      ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 +
        4 * sourcePair (posGraph q) (negGraph q) +
        archGroundConstant * ‖thetaToVolume q.val.fst‖ ^ 2 +
        ⟪primeShiftOperator (absGraph q).val.fst, (absGraph q).val.fst⟫_ℝ := by
    rw [norm_absGraph_fst_sq]
    have h1 : ((1 - 2 * μ) / μ) * ‖q.val.fst‖ ^ 2 + ‖q.val.fst‖ ^ 2 =
        ((1 - μ) / μ) * ‖q.val.fst‖ ^ 2 := by
      field_simp [hμ]
      ring
    linarith
  rwa [hnorm, hid] at hcs

/-! ## Section 4: Nodal Lobe Additivity of the Diagonal Forms -/

/-- Because `thetaToVolume (posGraph p)` and `thetaToVolume (negGraph p)` have disjoint supports,
`‖thetaToVolume p.val.fst‖ ^ 2 = ‖thetaToVolume (posGraph p).val.fst‖ ^ 2 + ‖thetaToVolume (negGraph p).val.fst‖ ^ 2`. -/
theorem norm_thetaToVolume_sq_eq_posGraph_add_negGraph (p : SourceGraph) :
    ‖thetaToVolume p.val.fst‖ ^ 2 =
      ‖thetaToVolume (posGraph p).val.fst‖ ^ 2 + ‖thetaToVolume (negGraph p).val.fst‖ ^ 2 := by
  have hsub : p.val.fst = (posGraph p).val.fst - (negGraph p).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_sub_negGraph p).symm
  conv_lhs => rw [hsub]
  rw [map_sub, norm_sub_sq_real, inner_thetaToVolume_posGraph_negGraph]
  ring

/-- Nodal lobe additivity of `archDiagonalOperator`:
`⟪archDiagonalOperator p.val.fst, p.val.fst⟫_ℝ = ⟪archDiagonalOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ + ⟪archDiagonalOperator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`. -/
theorem inner_archDiagonalOperator_self_eq_posGraph_add_negGraph (p : SourceGraph) :
    ⟪archDiagonalOperator p.val.fst, p.val.fst⟫_ℝ =
      ⟪archDiagonalOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ +
        ⟪archDiagonalOperator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  rw [inner_archDiagonalOperator_self, inner_archDiagonalOperator_self,
    inner_archDiagonalOperator_self, norm_thetaToVolume_sq_eq_posGraph_add_negGraph, mul_add]

/-- Pairing of `archDiagonalOperator p.val.fst` with `(posGraph p).val.fst` and `(negGraph p).val.fst`. -/
theorem inner_archDiagonalOperator_posGraph_and_negGraph_self (p : SourceGraph) :
    ⟪archDiagonalOperator p.val.fst, (posGraph p).val.fst⟫_ℝ =
        archGroundConstant * ‖thetaToVolume (posGraph p).val.fst‖ ^ 2 ∧
      ⟪archDiagonalOperator p.val.fst, (negGraph p).val.fst⟫_ℝ =
        -archGroundConstant * ‖thetaToVolume (negGraph p).val.fst‖ ^ 2 := by
  have hsub : p.val.fst = (posGraph p).val.fst - (negGraph p).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_sub_negGraph p).symm
  constructor
  · rw [archDiagonalOperator_symmetric, hsub, inner_sub_left,
      ← archDiagonalOperator_symmetric, inner_archDiagonalOperator_self,
      real_inner_comm _ (negGraph p).val.fst, inner_archDiagonalOperator_posGraph_negGraph, sub_zero]
  · rw [archDiagonalOperator_symmetric, hsub, inner_sub_left,
      ← archDiagonalOperator_symmetric, inner_archDiagonalOperator_posGraph_negGraph,
      ← archDiagonalOperator_symmetric, inner_archDiagonalOperator_self]
    ring

/-- Nodal lobe additivity of `primeDiagonalOperator`:
`⟪primeDiagonalOperator p.val.fst, p.val.fst⟫_ℝ = ⟪primeDiagonalOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ + ⟪primeDiagonalOperator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`. -/
theorem inner_primeDiagonalOperator_self_eq_posGraph_add_negGraph (p : SourceGraph) :
    ⟪primeDiagonalOperator p.val.fst, p.val.fst⟫_ℝ =
      ⟪primeDiagonalOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ +
        ⟪primeDiagonalOperator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  have hsub : p.val.fst = (posGraph p).val.fst - (negGraph p).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_sub_negGraph p).symm
  conv_lhs => rw [hsub]
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
    primeDiagonalOperator_symmetric (negGraph p).val.fst (posGraph p).val.fst,
    real_inner_comm _ (negGraph p).val.fst, inner_primeDiagonalOperator_posGraph_negGraph]
  ring

/-- Nodal lobe additivity of `groundPotentialOperator`:
`⟪groundPotentialOperator p.val.fst, p.val.fst⟫_ℝ = ⟪groundPotentialOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ + ⟪groundPotentialOperator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ`. -/
theorem inner_groundPotentialOperator_self_eq_posGraph_add_negGraph (p : SourceGraph) :
    ⟪groundPotentialOperator p.val.fst, p.val.fst⟫_ℝ =
      ⟪groundPotentialOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ +
        ⟪groundPotentialOperator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  have hsub : p.val.fst = (posGraph p).val.fst - (negGraph p).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_sub_negGraph p).symm
  conv_lhs => rw [hsub]
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
    groundPotentialOperator_symmetric (negGraph p).val.fst (posGraph p).val.fst,
    real_inner_comm _ (negGraph p).val.fst, inner_groundPotentialOperator_posGraph_negGraph]
  ring

end RHTower.CHMDPolar
