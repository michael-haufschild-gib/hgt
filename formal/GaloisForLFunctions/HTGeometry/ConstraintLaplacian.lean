import GaloisForLFunctions.HTGeometry.HilbertClosedRange
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The constraint Laplacian and the exactification trichotomy

Finitely many closed subspaces `U i` of a Hilbert space `H` are compared through the
**constraint defect**

`T x = (x - P_{U i} x)_i ∈ ⨁_i H`,

whose adjoint is `(y i)_i ↦ ∑ i, (y i - P_{U i} (y i))`, whose quadratic form is the total
precision defect `E x = ∑ i, dist (x, U i) ^ 2`, and whose normal operator is the
**constraint Laplacian** `Δ = ∑ i (1 - P_{U i})`.

The main results are

* `ker_constraintLaplacian` : `ker Δ = ker T = ⨅ i, U i`;
* `constraintLaplacian_tfae` : a uniform transverse precision gap, a transverse lower bound for
  `T`, closedness of `ran T` and closedness of `∑ i, (U i)ᗮ` are all equivalent;
* `exists_transverse_unit_sequence_of_not_hasUniformPrecisionGap` : in the absence of a gap there
  are transverse unit vectors whose total precision defect tends to zero, so every observer
  becomes asymptotically sharp although no nonzero transverse vector is jointly exact.
-/

open scoped InnerProductSpace Topology ENNReal
open Filter

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H] {ι : Type*} [Fintype ι]

variable (U : ι → Submodule 𝕜 H) [∀ i, (U i).HasOrthogonalProjection]

/-- The joint sector: the vectors accepted by every observer. -/
def jointSector : Submodule 𝕜 H := ⨅ i, U i

/-- The constraint defect operator `x ↦ (x - P_{U i} x)_i`. -/
noncomputable def constraintDefect : H →L[𝕜] PiLp 2 (fun _ : ι => H) :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.id 𝕜 H - (U i).starProjection)

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem constraintDefect_apply (x : H) (i : ι) :
    constraintDefect U x i = x - (U i).starProjection x := rfl

/-- The constraint codefect operator `(y i)_i ↦ ∑ i, (y i - P_{U i} (y i))`. -/
noncomputable def constraintCodefect : PiLp 2 (fun _ : ι => H) →L[𝕜] H :=
  (∑ i : ι, (ContinuousLinearMap.id 𝕜 H - (U i).starProjection) ∘L
      (ContinuousLinearMap.proj i : (∀ _ : ι, H) →L[𝕜] H)) ∘L
    (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => H)).toContinuousLinearMap

omit [CompleteSpace H] in
theorem constraintCodefect_apply (y : PiLp 2 (fun _ : ι => H)) :
    constraintCodefect U y = ∑ i : ι, (y i - (U i).starProjection (y i)) := by
  simp [constraintCodefect, sum_apply]

/-- The constraint Laplacian `Δ = ∑ i (1 - P_{U i})`. -/
noncomputable def constraintLaplacian : H →L[𝕜] H :=
  ∑ i : ι, (ContinuousLinearMap.id 𝕜 H - (U i).starProjection)

omit [CompleteSpace H] in
theorem constraintLaplacian_apply (x : H) :
    constraintLaplacian U x = ∑ i : ι, (x - (U i).starProjection x) := by
  simp [constraintLaplacian, sum_apply]

/-- The total precision defect `E x = ∑ i, dist (x, U i) ^ 2`. -/
noncomputable def constraintEnergy (x : H) : ℝ :=
  ∑ i : ι, ‖x - (U i).starProjection x‖ ^ 2

omit [CompleteSpace H] in
theorem norm_sq_constraintDefect (x : H) :
    ‖constraintDefect U x‖ ^ 2 = constraintEnergy U x := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

omit [CompleteSpace H] [Fintype ι] in
/-- The distance to a closed subspace is realized by the orthogonal projection. -/
theorem infDist_eq_norm_sub_starProjection (x : H) (i : ι) :
    Metric.infDist x ((U i : Submodule 𝕜 H) : Set H) = ‖x - (U i).starProjection x‖ := by
  rw [Metric.infDist_eq_iInf, (U i).starProjection_minimal x]
  exact iInf_congr fun u => by rw [dist_eq_norm]

omit [CompleteSpace H] in
theorem constraintEnergy_eq_sum_infDist_sq (x : H) :
    constraintEnergy U x = ∑ i : ι, Metric.infDist x ((U i : Submodule 𝕜 H) : Set H) ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [infDist_eq_norm_sub_starProjection]

omit [CompleteSpace H] in
theorem constraintEnergy_nonneg (x : H) : 0 ≤ constraintEnergy U x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [CompleteSpace H] in
theorem constraintEnergy_smul (c : 𝕜) (x : H) :
    constraintEnergy U (c • x) = ‖c‖ ^ 2 * constraintEnergy U x := by
  rw [← norm_sq_constraintDefect, ← norm_sq_constraintDefect, map_smul, norm_smul]
  ring

omit [CompleteSpace H] in
theorem constraintEnergy_eq_zero_iff (x : H) :
    constraintEnergy U x = 0 ↔ ∀ i, x ∈ U i := by
  constructor
  · intro h i
    have hsum : ∀ j ∈ Finset.univ, ‖x - (U j).starProjection x‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).mp h
    have hi := hsum i (Finset.mem_univ i)
    have : x - (U i).starProjection x = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hi
      exact norm_eq_zero.mp this
    have hx : (U i).starProjection x = x := by
      rw [sub_eq_zero] at this
      exact this.symm
    rw [← hx]
    exact (U i).starProjection_apply_mem x
  · intro h
    refine Finset.sum_eq_zero fun i _ => ?_
    have hx : (U i).starProjection x = x := (U i).starProjection_eq_self_iff.mpr (h i)
    rw [hx, sub_self, norm_zero]
    norm_num

omit [CompleteSpace H] in
theorem ker_constraintDefect :
    LinearMap.ker ((constraintDefect U : H →L[𝕜] PiLp 2 (fun _ : ι => H)) :
        H →ₗ[𝕜] PiLp 2 (fun _ : ι => H))
      = jointSector U := by
  ext x
  constructor
  · intro hx
    have h0 : constraintDefect U x = 0 := hx
    have henergy : constraintEnergy U x = 0 := by
      rw [← norm_sq_constraintDefect, h0, norm_zero]
      norm_num
    have := (constraintEnergy_eq_zero_iff U x).mp henergy
    exact Submodule.mem_iInf _ |>.mpr this
  · intro hx
    have hmem : ∀ i, x ∈ U i := (Submodule.mem_iInf _).mp hx
    have : constraintDefect U x = 0 := by
      ext i
      have hxi : (U i).starProjection x = x := (U i).starProjection_eq_self_iff.mpr (hmem i)
      simp [hxi]
    exact this

/-- The codefect operator is the adjoint of the defect operator. -/
theorem adjoint_constraintDefect :
    ContinuousLinearMap.adjoint (constraintDefect U) = constraintCodefect U := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro y x
  rw [constraintCodefect_apply, sum_inner]
  rw [show (⟪y, constraintDefect U x⟫_𝕜) = ∑ i : ι, ⟪y i, constraintDefect U x i⟫_𝕜 from
    PiLp.inner_apply y (constraintDefect U x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [constraintDefect_apply]
  have hself : IsSelfAdjoint (U i).starProjection := isSelfAdjoint_starProjection (U i)
  have : ⟪(U i).starProjection (y i), x⟫_𝕜 = ⟪y i, (U i).starProjection x⟫_𝕜 := by
    conv_lhs => rw [← hself]
    exact ContinuousLinearMap.adjoint_inner_left (U i).starProjection x (y i)
  rw [inner_sub_left, inner_sub_right, this]

omit [CompleteSpace H] in
theorem constraintLaplacian_eq_comp :
    constraintLaplacian U = constraintCodefect U ∘L constraintDefect U := by
  ext x
  rw [ContinuousLinearMap.comp_apply, constraintCodefect_apply, constraintLaplacian_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [constraintDefect_apply]
  have hmem := (U i).sub_starProjection_mem_orthogonal x
  rw [← Submodule.ker_starProjection (U i)] at hmem
  have hzero : (U i).starProjection (x - (U i).starProjection x) = 0 := hmem
  rw [hzero, sub_zero]

/-- **Theorem 3.1(1).**  The kernel of the constraint Laplacian is the joint sector. -/
theorem ker_constraintLaplacian :
    LinearMap.ker ((constraintLaplacian U : H →L[𝕜] H) : H →ₗ[𝕜] H) = jointSector U := by
  rw [← ker_constraintDefect U, constraintLaplacian_eq_comp, ← adjoint_constraintDefect]
  exact ContinuousLinearMap.ker_adjoint_comp_self (constraintDefect U)

theorem inner_constraintLaplacian_self (x : H) :
    RCLike.re (⟪constraintLaplacian U x, x⟫_𝕜) = constraintEnergy U x := by
  rw [constraintLaplacian_eq_comp, ← adjoint_constraintDefect,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left (constraintDefect U) x (constraintDefect U x),
    inner_self_eq_norm_sq, norm_sq_constraintDefect]

omit [CompleteSpace H] in
/-- The range of the codefect operator is the sum of the observer complements. -/
theorem range_constraintCodefect :
    LinearMap.range ((constraintCodefect U : PiLp 2 (fun _ : ι => H) →L[𝕜] H) :
        PiLp 2 (fun _ : ι => H) →ₗ[𝕜] H)
      = ⨆ i : ι, (U i)ᗮ := by
  classical
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [show ((constraintCodefect U : PiLp 2 (fun _ : ι => H) →L[𝕜] H) :
        PiLp 2 (fun _ : ι => H) →ₗ[𝕜] H) y
        = constraintCodefect U y from rfl, constraintCodefect_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.mem_iSup_of_mem i ((U i).sub_starProjection_mem_orthogonal (y i))
  · refine iSup_le fun i => ?_
    intro w hw
    refine ⟨PiLp.single 2 i w, ?_⟩
    rw [show ((constraintCodefect U : PiLp 2 (fun _ : ι => H) →L[𝕜] H) :
        PiLp 2 (fun _ : ι => H) →ₗ[𝕜] H)
        (PiLp.single 2 i w) = constraintCodefect U (PiLp.single 2 i w) from rfl,
      constraintCodefect_apply]
    rw [Finset.sum_eq_single i]
    · have hw0 : (U i).starProjection w = 0 := by
        rw [← (U i).ker_starProjection] at hw
        exact hw
      simp [hw0]
    · intro j _ hj
      have hzero : (PiLp.single (2 : ℝ≥0∞) i w : PiLp 2 (fun _ : ι => H)) j = 0 := by
        simp [hj]
      rw [show (PiLp.single (2 : ℝ≥0∞) i w : PiLp 2 (fun _ : ι => H)) j = 0 from hzero,
        map_zero, sub_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

/-- A uniform transverse precision cost. -/
def HasUniformPrecisionGap : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x ∈ (jointSector U)ᗮ, c * ‖x‖ ^ 2 ≤ constraintEnergy U x

omit [CompleteSpace H] in
theorem hasUniformPrecisionGap_iff_hasTransverseLowerBound :
    HasUniformPrecisionGap U ↔
      ContinuousLinearMap.HasTransverseLowerBound (constraintDefect U) := by
  rw [ContinuousLinearMap.HasTransverseLowerBound, ker_constraintDefect]
  constructor
  · rintro ⟨c, hc, hbound⟩
    refine ⟨Real.sqrt c, Real.sqrt_pos.mpr hc, fun x hx => ?_⟩
    have hE := hbound x hx
    rw [← norm_sq_constraintDefect] at hE
    have h1 : (Real.sqrt c * ‖x‖) ^ 2 ≤ ‖constraintDefect U x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc.le]
      exact hE
    exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) (by norm_num)).mp h1
  · rintro ⟨c, hc, hbound⟩
    refine ⟨c ^ 2, by positivity, fun x hx => ?_⟩
    have hE := hbound x hx
    have h1 : (c * ‖x‖) ^ 2 ≤ ‖constraintDefect U x‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hE 2
    rw [← norm_sq_constraintDefect]
    calc c ^ 2 * ‖x‖ ^ 2 = (c * ‖x‖) ^ 2 := by ring
      _ ≤ ‖constraintDefect U x‖ ^ 2 := h1

/-- **Theorem 3.1(2).**  The exactification trichotomy: a uniform transverse precision gap, a
transverse lower bound for the defect operator, closedness of its range, and closedness of the sum
of the observer complements are all equivalent. -/
theorem constraintLaplacian_tfae :
    List.TFAE
      [ HasUniformPrecisionGap U,
        ContinuousLinearMap.HasTransverseLowerBound (constraintDefect U),
        IsClosed (Set.range (constraintDefect U)),
        IsClosed (((⨆ i : ι, (U i)ᗮ : Submodule 𝕜 H) : Set H)) ] := by
  tfae_have 1 ↔ 2 := hasUniformPrecisionGap_iff_hasTransverseLowerBound U
  tfae_have 2 ↔ 3 :=
    ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range (constraintDefect U)
  tfae_have 3 ↔ 4 := by
    rw [← ContinuousLinearMap.isClosed_range_adjoint_iff (constraintDefect U)]
    have hset : Set.range (ContinuousLinearMap.adjoint (constraintDefect U))
        = (((⨆ i : ι, (U i)ᗮ : Submodule 𝕜 H)) : Set H) := by
      rw [← range_constraintCodefect U, adjoint_constraintDefect]
      exact (LinearMap.coe_range _).symm
    rw [hset]
  tfae_finish

omit [CompleteSpace H] in
/-- **Theorem 3.1(3).**  Without a uniform gap there are transverse unit vectors whose total
precision defect tends to zero: every observer becomes asymptotically sharp although no nonzero
transverse vector is jointly exact. -/
theorem exists_transverse_unit_sequence_of_not_hasUniformPrecisionGap
    (h : ¬ HasUniformPrecisionGap U) :
    ∃ u : ℕ → H, (∀ n, u n ∈ (jointSector U)ᗮ) ∧ (∀ n, ‖u n‖ = 1) ∧
      Tendsto (fun n => constraintEnergy U (u n)) atTop (𝓝 0) := by
  classical
  have hstep : ∀ n : ℕ, ∃ x ∈ (jointSector U)ᗮ,
      constraintEnergy U x < (1 / (n + 1 : ℝ)) * ‖x‖ ^ 2 := by
    intro n
    by_contra hcon
    push Not at hcon
    exact h ⟨1 / (n + 1 : ℝ), by positivity, fun x hx => hcon x hx⟩
  choose x hxmem hxlt using hstep
  have hxne : ∀ n, x n ≠ 0 := by
    intro n hzero
    have := hxlt n
    rw [hzero, norm_zero] at this
    have h0 : constraintEnergy U (0 : H) = 0 := by
      rw [← norm_sq_constraintDefect, map_zero, norm_zero]
      norm_num
    rw [h0] at this
    simp at this
  refine ⟨fun n => (‖x n‖ : 𝕜)⁻¹ • x n, fun n => ?_, fun n => ?_, ?_⟩
  · exact Submodule.smul_mem _ _ (hxmem n)
  · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    field_simp [norm_ne_zero_iff.mpr (hxne n)]
  · have hbound : ∀ n : ℕ,
        constraintEnergy U ((‖x n‖ : 𝕜)⁻¹ • x n) ≤ 1 / (n + 1 : ℝ) := by
      intro n
      have hnorm : (0 : ℝ) < ‖x n‖ := norm_pos_iff.mpr (hxne n)
      rw [constraintEnergy_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
      have := (hxlt n).le
      rw [inv_pow, inv_mul_eq_div, div_le_iff₀ (by positivity)]
      calc constraintEnergy U (x n) ≤ 1 / (n + 1 : ℝ) * ‖x n‖ ^ 2 := this
        _ = 1 / (n + 1 : ℝ) * ‖x n‖ ^ 2 := rfl
    refine squeeze_zero (fun n => constraintEnergy_nonneg U _) hbound ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat

end GaloisForLFunctions.HTGeometry
