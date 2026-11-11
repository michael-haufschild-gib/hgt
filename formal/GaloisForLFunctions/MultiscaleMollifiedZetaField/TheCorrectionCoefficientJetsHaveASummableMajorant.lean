import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShiftedCorrectionHasASummablePairMajorant
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheCorrectionJetsKeepTheSummableEnvelope

/-!
# Correction-coefficient jets with a summable pair majorant

The finite divisor fibres extend each correction coefficient to an entire
function. The absolute pair mass controls its normalized continuation and
all its Cauchy jets. Positive-order normalized jets vanish along every
bounded sequence of centres.
-/

open Filter Set Topology
open RHTower.Sieve

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Entire continuation of the pushed Euler correction coefficient. -/
def complexSelbergCorrectionCoeff (m n : ℕ) (z : ℂ) : ℂ :=
  if m = 0 ∨ n = 0 then 0 else
    ∑ r : {r // r ∈ (Nat.gcd m n).divisors},
      complexSelbergCorrectionWeight r.1 (m / r.1) (n / r.1) z

theorem complexSelbergCorrectionCoeff_ofReal (m n : ℕ) (s : ℝ) :
    complexSelbergCorrectionCoeff m n (s : ℂ) = (shiftedSelbergCorrectionCoeff s m n : ℂ) := by
  classical
  by_cases h : m = 0 ∨ n = 0 <;>
    simp [complexSelbergCorrectionCoeff, shiftedSelbergCorrectionCoeff, h,
      complexSelbergCorrectionWeight_ofReal]

theorem differentiable_complexSelbergCorrectionCoeff (m n : ℕ) :
    Differentiable ℂ (complexSelbergCorrectionCoeff m n) := by
  classical
  unfold complexSelbergCorrectionCoeff
  split_ifs
  · exact (differentiable_const (0 : ℂ) : Differentiable ℂ (fun _ : ℂ => (0 : ℂ)))
  · have h (r : {r // r ∈ (Nat.gcd m n).divisors}) :=
      differentiable_complexSelbergCorrectionWeight r.1 (m / r.1) (n / r.1)
    fun_prop

/-- The complex normalized coefficient has the same absolute pair majorant. -/
theorem norm_complexSelbergCorrectionCoeff_log_shift_le {N m n : ℕ} (hN : 1 < N)
    (z : ℂ) (hm : m ≤ N) (hn : n ≤ N) :
    ‖complexSelbergCorrectionCoeff m n (z / (Real.log N : ℂ))‖ ≤
      Real.exp (4 * ‖z‖) * absoluteSelbergCorrectionCoeff m n := by
  classical
  by_cases hzero : m = 0 ∨ n = 0
  · simp only [complexSelbergCorrectionCoeff, absoluteSelbergCorrectionCoeff, if_pos hzero,
      norm_zero, mul_zero, le_refl]
  · simp only [complexSelbergCorrectionCoeff, absoluteSelbergCorrectionCoeff, if_neg hzero]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    exact norm_complexSelbergCorrectionWeight_log_shift_le hN z r.1
      ((Nat.div_le_self _ _).trans hm) ((Nat.div_le_self _ _).trans hn)

/-- Every normalized coefficient jet is bounded by the summable absolute pair mass. -/
theorem norm_normalizedCorrectionCoeffJet_le {N m n : ℕ} (hN : 1 < N)
    (C : ℂ) (j : ℕ) (hm : m ≤ N) (hn : n ≤ N) :
    ‖iteratedDeriv j (fun z => complexSelbergCorrectionCoeff m n (z / (Real.log N : ℂ))) C‖ ≤
      (j.factorial : ℝ) * Real.exp (4 * (‖C‖ + 1)) * absoluteSelbergCorrectionCoeff m n := by
  have hf : Differentiable ℂ (fun z => complexSelbergCorrectionCoeff m n (z / (Real.log N : ℂ))) :=
    (differentiable_complexSelbergCorrectionCoeff m n).comp (differentiable_id.div_const _)
  have hb : ∀ z ∈ sphere C 1,
      ‖complexSelbergCorrectionCoeff m n (z / (Real.log N : ℂ))‖ ≤
        Real.exp (4 * (‖C‖ + 1)) * absoluteSelbergCorrectionCoeff m n := by
    intro z hz
    have hz1 : ‖z - C‖ = 1 := by simpa only [mem_sphere, dist_eq_norm] using hz
    have hzn : ‖z‖ ≤ ‖C‖ + 1 := by
      have hh := norm_add_le (z - C) C
      rw [sub_add_cancel, hz1] at hh
      linarith only [hh]
    refine (norm_complexSelbergCorrectionCoeff_log_shift_le hN z hm hn).trans ?_
    apply mul_le_mul_of_nonneg_right _ (absoluteSelbergCorrectionCoeff_nonneg _ _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzn (by norm_num))
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j zero_lt_one hf.diffContOnCl hb
  simpa only [one_pow, div_one, mul_assoc] using hh

/-- Real normalized displacement jets of the correction coefficient. -/
def realNormalizedCorrectionCoeffJet (N m n j : ℕ) (C : ℝ) : ℝ :=
  (iteratedDeriv j (fun z => complexSelbergCorrectionCoeff m n (z / (Real.log N : ℂ))) (C : ℂ)).re

@[simp] theorem realNormalizedCorrectionCoeffJet_zero (N m n : ℕ) (C : ℝ) :
    realNormalizedCorrectionCoeffJet N m n 0 C = shiftedSelbergCorrectionCoeff (C / Real.log N) m n := by
  simp only [realNormalizedCorrectionCoeffJet, iteratedDeriv_zero, ← Complex.ofReal_div,
    complexSelbergCorrectionCoeff_ofReal, Complex.ofReal_re]

/-- The real coefficient jets are literal successive derivatives. -/
theorem hasDerivAt_realNormalizedCorrectionCoeffJet (N m n j : ℕ) (C : ℝ) :
    HasDerivAt (realNormalizedCorrectionCoeffJet N m n j)
      (realNormalizedCorrectionCoeffJet N m n (j + 1) C) C := by
  let f : ℂ → ℂ := fun z => complexSelbergCorrectionCoeff m n (z / (Real.log N : ℂ))
  have hf : Differentiable ℂ f :=
    (differentiable_complexSelbergCorrectionCoeff m n).comp (differentiable_id.div_const _)
  have ha : ∀ k : ℕ, AnalyticAt ℂ (iteratedDeriv k f) (C : ℂ) := by
    intro k
    induction k with
    | zero => exact hf.differentiableOn.analyticOnNhd isOpen_univ _ (mem_univ _)
    | succ k hk => simpa only [iteratedDeriv_succ] using hk.deriv
  simpa only [realNormalizedCorrectionCoeffJet, iteratedDeriv_succ, f] using
    (ha j).differentiableAt.hasDerivAt.real_of_complex

/-- Real jets inherit the absolute pair majorant. -/
theorem abs_realNormalizedCorrectionCoeffJet_le {N m n : ℕ} (hN : 1 < N)
    (C : ℝ) (j : ℕ) (hm : m ≤ N) (hn : n ≤ N) :
    |realNormalizedCorrectionCoeffJet N m n j C| ≤
      (j.factorial : ℝ) * Real.exp (4 * (|C| + 1)) * absoluteSelbergCorrectionCoeff m n := by
  refine (Complex.abs_re_le_norm _).trans ?_
  simpa only [Complex.norm_real, Real.norm_eq_abs] using norm_normalizedCorrectionCoeffJet_le hN (C : ℂ) j hm hn

/-- Positive-order normalized coefficient jets vanish for every bounded moving centre. -/
theorem tendsto_realNormalizedCorrectionCoeffJet_succ {C : ℕ → ℝ} {R : ℝ}
    (hR : ∀ᶠ N : ℕ in atTop, |C N| ≤ R) (m n j : ℕ) :
    Tendsto (fun N : ℕ => realNormalizedCorrectionCoeffJet N m n (j + 1) (C N)) atTop (𝓝 0) := by
  have hc : ∀ᶠ N : ℕ in atTop, ‖(C N : ℂ)‖ ≤ R := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hR
  have hh := tendsto_entire_normalized_jet_succ_of_bounded_centres
    (differentiable_complexSelbergCorrectionCoeff m n) hc j
  simpa only [realNormalizedCorrectionCoeffJet, Complex.zero_re, Function.comp_def] using
    Complex.continuous_re.continuousAt.tendsto.comp hh

end GaloisForLFunctions.MultiscaleMollifiedZetaField
