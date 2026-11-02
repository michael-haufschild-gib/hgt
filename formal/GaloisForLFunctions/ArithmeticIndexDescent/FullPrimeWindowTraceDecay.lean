import GaloisForLFunctions.ArithmeticIndexDescent.TheFullPrimeWindowCancelsTheGrowingHeadPole

/-!
# Exponential spatial decay of the full prime-window trace

The actual support cutoff, rather than the full summation horizon, gives
an integrable square majorant for normalized prime-window traces.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.ArithmeticIndexDescent

lemma sqrtChebyshev_le_sqrt_cutoff {x : ℝ} (_hx : 0 ≤ x) :
    sqrtChebyshev x ≤ 2 * RHTower.FreeLagTrace.chebyshevConst * Real.sqrt x := by
  by_cases hx1 : 1 ≤ x
  · have he : sqrtChebyshev x = ∑ n ∈ Icc 2 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
      symm
      apply sum_subset (Icc_subset_Icc_left (by omega : 0 ≤ 2))
      intro n hn hn'
      have hn01 : n=0 ∨ n=1 := by
        simp only [mem_Icc] at hn hn'
        omega
      rcases hn01 with rfl | rfl <;> simp
    rw [he]
    exact RHTower.FreeLagTrace.sum_vonMangoldt_div_sqrt_le hx1
  · have hf : ⌊x⌋₊=0 := Nat.floor_eq_zero.mpr (lt_of_not_ge hx1)
    have hz : sqrtChebyshev x=0 := by simp [sqrtChebyshev,hf]
    rw [hz]
    exact mul_nonneg (mul_nonneg (by norm_num)
      RHTower.FreeLagTrace.chebyshevConst_pos.le) (Real.sqrt_nonneg _)

/-- The square-root Chebyshev bound follows the active support cutoff. -/
lemma headWindowMass_le_sqrt_cutoff (Y : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    headWindowMass Y γ ≤
      2 * RHTower.FreeLagTrace.chebyshevConst * Real.sqrt (γ * Y) := by
  exact (headWindowMass_le Y γ).trans
    ((sqrtChebyshev_mono (mul_le_mul_of_nonneg_right (min_le_left γ 1)
      (Nat.cast_nonneg Y))).trans
      (sqrtChebyshev_le_sqrt_cutoff (mul_nonneg hγ (Nat.cast_nonneg Y))))

lemma headTrace_le_sqrt_cutoff {Y b : ℕ} (hY : 1 ≤ Y) (hb : 1 ≤ b) (u : ℝ) :
    headTrace Y b u ≤ 4 * RHTower.FreeLagTrace.chebyshevConst *
      Real.sqrt (((2:ℝ)*b+2)*Real.exp (-u)*Y) := by
  rw [headTrace_eq hY hb]
  have h0 := headWindowMass_nonneg Y (2*b*Real.exp (-u))
  have h1 := headWindowMass_le_sqrt_cutoff Y
    (show 0 ≤ ((2:ℝ)*b+2)*Real.exp (-u) by positivity)
  linarith only [h0,h1]

/-- Normalized full traces have an exponentially decaying bound on the whole real line. -/
theorem fullPrimeWindowTrace_div_sqrt_le_exp {Y b : ℕ}
    (hY : 1 ≤ Y) (hb : 1 ≤ b) (u : ℝ) :
    0 ≤ fullPrimeWindowTrace Y b u / Real.sqrt Y ∧
      fullPrimeWindowTrace Y b u / Real.sqrt Y ≤
        (4 * RHTower.FreeLagTrace.chebyshevConst * Real.sqrt ((2:ℝ)*b+2)) *
          Real.exp (-u/2) := by
  have hY0 : (0:ℝ) < Y := by exact_mod_cast hY
  have hRY : 1 ≤ (b+1)*Y := by nlinarith only [hY,Nat.zero_le (b*Y)]
  have hr : (0:ℝ) < b+1 := by positivity
  have h0 := (headTrace_nonneg_le hRY hb (u+Real.log ((b:ℝ)+1))).1
  have h1 := headTrace_le_sqrt_cutoff hRY hb (u+Real.log ((b:ℝ)+1))
  have he : (((2:ℝ)*b+2)*Real.exp (-(u+Real.log ((b:ℝ)+1)))*
      (((b+1)*Y:ℕ):ℝ)) = (((2:ℝ)*b+2)*Real.exp (-u))*(Y:ℝ) := by
    rw [neg_add,Real.exp_add,Real.exp_neg (Real.log ((b:ℝ)+1)),Real.exp_log hr]
    push_cast
    field_simp [hr.ne']
  rw [he,Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity),
    ← Real.exp_half] at h1
  refine ⟨div_nonneg h0 (Real.sqrt_nonneg _),?_⟩
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hY0)]
  exact h1.trans_eq (by ring)

#print axioms sqrtChebyshev_le_sqrt_cutoff
#print axioms headWindowMass_le_sqrt_cutoff
#print axioms headTrace_le_sqrt_cutoff
#print axioms fullPrimeWindowTrace_div_sqrt_le_exp
end GaloisForLFunctions.ArithmeticIndexDescent
