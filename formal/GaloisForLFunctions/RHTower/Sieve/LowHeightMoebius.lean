import GaloisForLFunctions.RHTower.Sieve.LowHeightPoly
import GaloisForLFunctions.RHTower.Sieve.MoebiusMaximalWindow

/-!
# The Möbius Dirichlet polynomial at low heights

Abel summation transfers the cancellation of the Mertens function to the Dirichlet polynomial:

```text
‖ ∑_{n ≤ M} μ(n)·n^{2πiw} ‖  ≤  mertensSup(M)·( 1 + 2π|w|·log M ) ,
```

and `mertensSup M = o(M)` is the prime number theorem.  Integrating over `|w| ≤ T` gives

```text
∫_{|w| ≤ T} ‖ ∑_{n ≤ M} μ(n)·n^{2πiw} ‖² dw  ≤  2T·mertensSup(M)²·(1 + 2πT log M)² ,
```

which is `o(M²)` for every height `T ≪ 1/log M`.  Below that scale the mean square of the Möbius
polynomial is unconditionally smaller than the mean value theorem's `≍ M²`, with no zero-free
region and no distance estimate: the phase has too little total variation to undo the cancellation
already present in the coefficients.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Finset
open scoped ArithmeticFunction.Moebius

/-- The real Möbius coefficient sequence. -/
theorem sum_range_moebius_shift_eq_mertensM (k : ℕ) :
    ∑ j ∈ Finset.range k, ((μ (j + 1) : ℤ) : ℝ) = mertensM k := by
  rw [mertensM, Finset.sum_range_succ']
  have hzero : ((μ 0 : ℤ) : ℝ) = 0 := by
    simp
  rw [hzero, add_zero]

/-- **The Möbius Dirichlet polynomial at height `w`.** -/
theorem norm_logPoly_moebius_le (M : ℕ) (w : ℝ) :
    ‖logPoly (fun n => (((μ n : ℤ) : ℝ) : ℂ)) (Finset.Icc 1 M) w‖
      ≤ mertensSup M * (1 + 2 * Real.pi * |w| * Real.log M) := by
  refine norm_logPoly_le_partial (fun n => ((μ n : ℤ) : ℝ)) M (fun k hk => ?_) w
  rw [sum_range_moebius_shift_eq_mertensM]
  exact abs_mertensM_le_mertensSup hk

/-- **The Möbius mean square at low heights.** -/
theorem integral_Icc_normSq_logPoly_moebius_le (M : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ w in Set.Icc (-T) T, ‖logPoly (fun n => (((μ n : ℤ) : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
      ≤ 2 * T * (mertensSup M * (1 + 2 * Real.pi * T * Real.log M)) ^ 2 := by
  classical
  set a : ℕ → ℂ := fun n => (((μ n : ℤ) : ℝ) : ℂ) with hadef
  set C : ℝ := mertensSup M * (1 + 2 * Real.pi * T * Real.log M) with hCdef
  have hlogM : 0 ≤ Real.log (M : ℝ) := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    · refine Real.log_nonneg ?_
      exact_mod_cast hM
  have hB0 : 0 ≤ mertensSup M := mertensSup_nonneg M
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    have : (0 : ℝ) ≤ 2 * Real.pi * T * Real.log (M : ℝ) := by
      have := Real.pi_pos
      positivity
    exact mul_nonneg hB0 (by linarith)
  have hcont : Continuous fun w : ℝ => ‖logPoly a (Finset.Icc 1 M) w‖ ^ 2 :=
    ((continuous_logPoly a _).norm).pow 2
  have hle : ∀ w ∈ Set.Icc (-T) T, ‖logPoly a (Finset.Icc 1 M) w‖ ^ 2 ≤ C ^ 2 := by
    intro w hw
    rw [Set.mem_Icc] at hw
    have hwT : |w| ≤ T := abs_le.2 ⟨hw.1, hw.2⟩
    have hstep : ‖logPoly a (Finset.Icc 1 M) w‖ ≤ C := by
      refine le_trans (norm_logPoly_moebius_le M w) ?_
      rw [hCdef]
      refine mul_le_mul_of_nonneg_left ?_ hB0
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      have : 2 * Real.pi * |w| * Real.log (M : ℝ) ≤ 2 * Real.pi * T * Real.log (M : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ hlogM
        exact mul_le_mul_of_nonneg_left hwT (by linarith)
      linarith
    exact pow_le_pow_left₀ (norm_nonneg _) hstep 2
  have hconstInt : IntegrableOn (fun _ : ℝ => C ^ 2) (Set.Icc (-T) T) volume :=
    (continuous_const).integrableOn_Icc
  have hmono := setIntegral_mono_on hcont.integrableOn_Icc hconstInt measurableSet_Icc hle
  refine le_trans hmono (le_of_eq ?_)
  rw [setIntegral_const, smul_eq_mul]
  have hval : volume.real (Set.Icc (-T) T) = 2 * T := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hval]

end RHTower.Sieve

end
