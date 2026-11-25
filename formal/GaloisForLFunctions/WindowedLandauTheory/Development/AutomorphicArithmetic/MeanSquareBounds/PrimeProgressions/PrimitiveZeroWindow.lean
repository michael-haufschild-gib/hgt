import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.CriticalStripZeroWindow
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroCopyOrders

/-! The primitive critical-strip zero set in a bounded height range is finite. -/

open Complex Set
open RHTower GaloisForLFunctions.EntireZeroDivisor
open GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

namespace QH.PrimeProgressions

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

theorem finite_primitive_zero_strip (hχ : χ.IsPrimitive) (T : ℝ) :
    {ρ : ℂ | χ.LFunction ρ = 0 ∧ ρ.re ∈ Ioo 0 1 ∧ |ρ.im| ≤ T}.Finite := by
  rcases eq_or_ne χ 1 with rfl | hn
  · have e : N = 1 := by
      have h := hχ
      rwa [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one, eq_comm] at h
    subst N
    simp only [DirichletCharacter.LFunction_modOne_eq]
    have hf := locallyFinite_zeroCopyPoint xi_analyticOnNhd_univ (1 + T)
    refine (hf.image (zeroCopyPoint xi)).subset ?_
    intro ρ hρ
    obtain ⟨q, hq⟩ := xi_zero_copy_exists hρ.2.1 hρ.1
    have eq : zeroCopyPoint xi q = ρ := hq
    refine ⟨q, ?_, eq⟩
    change ‖zeroCopyPoint xi q‖ ≤ 1 + T
    rw [eq]
    refine (norm_le_abs_re_add_abs_im ρ).trans (add_le_add ?_ hρ.2.2)
    rw [abs_of_pos hρ.2.1.1]
    exact hρ.2.1.2.le
  · have hf := finite_primitive_height hn hχ T
    refine (hf.image (LZero.point (χ := χ))).subset ?_
    intro ρ hρ
    obtain ⟨q, hq⟩ := primitive_zero_copy_exists hn hρ.2.1.1 hρ.1
    exact ⟨q, by simpa only [mem_setOf_eq, hq] using hρ.2.2, hq⟩

def primitiveZerosNear (χ : DirichletCharacter ℂ N) (t : ℝ) : Set ℂ :=
  {ρ : ℂ | χ.LFunction ρ = 0 ∧ ρ.re ∈ Ioo 0 1 ∧ |ρ.im - t| ≤ 1}

/-- Critical-strip zeros strictly between the two horizontal edges of a Perron contour. -/
def primitiveInteriorZeros (χ : DirichletCharacter ℂ N) (T : ℝ) : Set ℂ :=
  {ρ | χ.LFunction ρ = 0 ∧ ρ.re ∈ Ioo 0 1 ∧ |ρ.im| < T}

theorem primitiveInteriorZeros_finite (hχ : χ.IsPrimitive) (T : ℝ) :
    (primitiveInteriorZeros χ T).Finite :=
  (finite_primitive_zero_strip hχ T).subset fun _ h => ⟨h.1, h.2.1, h.2.2.le⟩

/-- The critical-strip zero sum with analytic multiplicities has logarithmic growth in each unit-height window. -/
theorem primitive_zero_window :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ t : ℝ, (primitiveZerosNear χ t).Finite ∧
        ∑ᶠ ρ ∈ primitiveZerosNear χ t, (analyticOrderNatAt χ.LFunction ρ : ℝ) ≤
          C * Real.log ((N : ℝ) * (|t| + 2)) := by
  obtain ⟨C, hC, H⟩ := primitive_critical_strip_zero_window
  refine ⟨C, hC, fun N _ χ hχ t => ?_⟩
  have hf : (primitiveZerosNear χ t).Finite := (finite_primitive_zero_strip hχ (1 + |t|)).subset (by
    intro ρ hρ
    refine ⟨hρ.1, hρ.2.1, ?_⟩
    have ht := abs_add_le (ρ.im - t) t
    rw [sub_add_cancel] at ht
    exact ht.trans (add_le_add hρ.2.2 le_rfl))
  refine ⟨hf, ?_⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hf]
  refine H N χ hχ t hf.toFinset (fun ρ hρ => ?_)
  have h := hf.mem_toFinset.mp hρ
  exact ⟨h.1, h.2.1.1, h.2.1.2, h.2.2⟩

end QH.PrimeProgressions
