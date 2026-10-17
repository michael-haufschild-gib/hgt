import GaloisForLFunctions.BiScaleUncertainty.IntegerBlockAggregation

/-!
# Explicit block replication and exact coisometry

The adjoint repeats every coordinate on its integer block. Aggregation after
replication is exactly scalar multiplication, giving an explicit right inverse,
sharp norm, and a concrete projection onto constant blocks.
-/

noncomputable section
open Set
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

def integerBlockReplicate (m : ℕ) : TraceData →L[ℝ] TraceData := (integerBlockSum m).adjoint

theorem integerBlockReplicate_zero (z : TraceData) : integerBlockReplicate 0 z = 0 := by
  have h : integerBlockSum 0 = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    exact integerBlockSum_zero w
  simp only [integerBlockReplicate, h, map_zero, zero_apply]

theorem integerBlockReplicate_coordinate (m : ℕ) (z : TraceData) (k : ℕ) :
    integerBlockReplicate m z k = if m = 0 then 0 else z (k/m) := by
  by_cases hm : m = 0
  · subst m
    simp [integerBlockReplicate_zero]
  · rw [if_neg hm]
    have h := (integerBlockSum m).adjoint_inner_right (lp.single 2 k (1 : ℝ)) z
    change ⟪lp.single 2 k (1 : ℝ), integerBlockReplicate m z⟫ =
      ⟪integerBlockSum m (lp.single 2 k 1), z⟫ at h
    rw [integerBlockSum_single m k (Nat.pos_of_ne_zero hm)] at h
    simpa only [lp.inner_single_left, Real.inner_apply, one_mul] using h

theorem integerBlockSum_replicate (m : ℕ) (z : TraceData) :
    integerBlockSum m (integerBlockReplicate m z) = (m : ℝ) • z := by
  by_cases hm : m = 0
  · subst m
    simp [integerBlockSum_zero]
  · apply lp.ext
    funext j
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [integerBlockSum_coordinate]
    calc
      _ = ∑ _k ∈ Finset.Ico (m*j) (m*(j+1)), z j := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [integerBlockReplicate_coordinate, if_neg hm,
          (mem_integerBlock_iff m j k (Nat.pos_of_ne_zero hm)).mp hk]
      _ = _ := by simp [Nat.mul_add]

theorem integerBlockReplicate_energy (m : ℕ) (z : TraceData) :
    ‖integerBlockReplicate m z‖^2 = (m : ℝ)*‖z‖^2 := by
  have h := (integerBlockSum m).adjoint_inner_right (integerBlockReplicate m z) z
  change ⟪integerBlockReplicate m z, integerBlockReplicate m z⟫ =
    ⟪integerBlockSum m (integerBlockReplicate m z), z⟫ at h
  simpa only [integerBlockSum_replicate, real_inner_smul_left,
    real_inner_self_eq_norm_sq] using h

theorem integerBlockReplicate_norm (m : ℕ) (z : TraceData) :
    ‖integerBlockReplicate m z‖ = Real.sqrt (m : ℝ)*‖z‖ := by
  have h := integerBlockReplicate_energy m z
  have hs : (Real.sqrt (m : ℝ)*‖z‖)^2 = (m : ℝ)*‖z‖^2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  nlinarith only [h, hs, norm_nonneg (integerBlockReplicate m z),
    mul_nonneg (Real.sqrt_nonneg (m : ℝ)) (norm_nonneg z)]

theorem integerBlockSum_surjective (n : ℕ) : Function.Surjective (integerBlockSum (n+1)) := by
  intro z
  refine ⟨(((n+1 : ℕ) : ℝ)⁻¹) • integerBlockReplicate (n+1) z, ?_⟩
  rw [map_smul, integerBlockSum_replicate, smul_smul,
    inv_mul_cancel₀ (by positivity : ((n+1 : ℕ) : ℝ) ≠ 0), one_smul]

theorem norm_integerBlockSum (m : ℕ) : ‖integerBlockSum m‖ = Real.sqrt (m : ℝ) := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (norm_integerBlockSum_le m)
  · by_cases hm : m = 0
    · simp only [hm, Nat.cast_zero, Real.sqrt_zero]
      exact norm_nonneg _
    · have h := (integerBlockSum m).le_opNorm
        (integerBlockReplicate m (lp.single 2 0 (1 : ℝ)))
      rw [integerBlockSum_replicate, norm_smul, integerBlockReplicate_norm] at h
      rw [lp.norm_single (by norm_num)] at h
      simp only [Real.norm_eq_abs, abs_one, mul_one,
        abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))] at h
      have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hm)
      have hmul : Real.sqrt (m : ℝ)*Real.sqrt (m : ℝ) ≤
          ‖integerBlockSum m‖*Real.sqrt (m : ℝ) := by
        nlinarith only [h, Real.sq_sqrt (Nat.cast_nonneg m)]
      exact le_of_mul_le_mul_right hmul hs

def integerBlockMean (m : ℕ) : TraceData →L[ℝ] TraceData :=
  (m : ℝ)⁻¹ • (integerBlockReplicate m ∘L integerBlockSum m)

theorem integerBlockMean_apply (m : ℕ) (w : TraceData) :
    integerBlockMean m w = (m : ℝ)⁻¹ • integerBlockReplicate m (integerBlockSum m w) := rfl

theorem integerBlockMean_idempotent (m : ℕ) (w : TraceData) :
    integerBlockMean m (integerBlockMean m w) = integerBlockMean m w := by
  by_cases hm : m = 0
  · simp [hm, integerBlockMean_apply]
  · have hr : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    simp only [integerBlockMean_apply, map_smul, integerBlockSum_replicate, smul_smul]
    field_simp

theorem integerBlockMean_defect (m : ℕ) (w : TraceData) :
    (m : ℝ)*‖w-integerBlockMean m w‖^2 =
      (m : ℝ)*‖w‖^2-‖integerBlockSum m w‖^2 := by
  by_cases hm : m = 0
  · simp [hm, integerBlockSum_zero]
  · have hr : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hi : ⟪w, integerBlockReplicate m (integerBlockSum m w)⟫ =
        ‖integerBlockSum m w‖^2 := by
      exact ((integerBlockSum m).adjoint_inner_right w (integerBlockSum m w)).trans
        (real_inner_self_eq_norm_sq _)
    rw [integerBlockMean_apply, norm_sub_sq_real, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, integerBlockReplicate_energy,
      real_inner_smul_right, hi]
    field_simp
    ring

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
