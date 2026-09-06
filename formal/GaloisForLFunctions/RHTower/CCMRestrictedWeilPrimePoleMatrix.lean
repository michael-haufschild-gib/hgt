import GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimePolarArithmeticAction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact prime matrix on the two exponential pole profiles

Every visible prime atom has a closed self and cross pairing obtained from its
actual endpoint-cutoff representative. The complete prime self entry reduces to
Chebyshev and reciprocal-Mangoldt cumulatives. Its cross entry is the literal
moving prime tent, retaining all prime powers. No sign of the full Weil form or
Riemann-hypothesis premise is assumed.
-/

open Complex MeasureTheory Set
open scoped InnerProduct BigOperators
noncomputable section
namespace RHTower

private theorem atom_pole_integral (a : SuzukiPositiveAperture) {n : ℕ} (hn : 2≤n) (s : ℝ) :
    inner ℂ (ccmPrimeTransportOperator a n (ccmPolarApertureVector a (1/2)))
      (ccmPolarApertureVector a s) =
      (∫ x in Icc (-a.1) (a.1-Real.log n), (Real.exp ((s+1/2)*x):ℂ)) +
      (1/(n:ℂ)) * ∫ x in Icc (Real.log n-a.1) a.1, (Real.exp ((s+1/2)*x):ℂ) := by
  have hlog : 0≤Real.log n := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
  have hcont : Continuous (fun x : ℝ => (Real.exp ((s+1/2)*x):ℂ)) := by fun_prop
  have hL := hcont.integrableOn_Icc (μ:=volume) (a := -a.1) (b := a.1-Real.log n)
  have hR := hcont.integrableOn_Icc (μ:=volume) (a := Real.log n-a.1) (b := a.1)
  change inner ℂ (ccmPrimeTransportOperator a n (ccmPolarApertureVector a (1/2)) : SoninL2)
    (ccmPolarL2Vector a s) = _
  rw [L2.inner_def, ← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc,
    ← integral_const_mul, ← integral_add (hL.integrable_indicator measurableSet_Icc)
      ((hR.integrable_indicator measurableSet_Icc).const_mul (1/(n:ℂ)))]
  apply integral_congr_ae
  filter_upwards [ccmPrimeTransport_polarPlus_coeFn a hn, ccmPolarL2Vector_coeFn a s] with x ha hp
  rw [ha,hp]
  have hLm : x ∈ Icc (-a.1) (a.1-Real.log n) ↔
      x ∈ centralInterval a.1 ∧ Real.log n≤a.1-x := by
    change (-a.1≤x ∧ x≤a.1-Real.log n) ↔ (-a.1≤x ∧ x≤a.1) ∧ _
    constructor <;> rintro ⟨h1,h2⟩
    · exact ⟨⟨h1,by linarith⟩,by linarith⟩
    · exact ⟨h1.1,by linarith⟩
  have hRm : x ∈ Icc (Real.log n-a.1) a.1 ↔
      x ∈ centralInterval a.1 ∧ Real.log n≤a.1+x := by
    change (Real.log n-a.1≤x ∧ x≤a.1) ↔ (-a.1≤x ∧ x≤a.1) ∧ _
    constructor <;> rintro ⟨h1,h2⟩
    · exact ⟨⟨by linarith,h2⟩,by linarith⟩
    · exact ⟨by linarith,h1.2⟩
  have hexp : (Real.exp (x/2):ℂ) * (Real.exp (s*x):ℂ) =
      (Real.exp ((s+1/2)*x):ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have hexpR : (Real.exp (s*x):ℂ) * (Real.exp (x/2):ℂ) =
      (Real.exp ((s+1/2)*x):ℂ) := by rw [mul_comm,hexp]
  by_cases hx : x ∈ centralInterval a.1
  · simp only [indicator, hLm, hRm, hx, true_and, ite_true, ccmPolarProfile]
    split_ifs <;> simp only [RCLike.inner_apply, map_add, map_div₀, map_zero,
      Complex.conj_ofReal, map_natCast, add_zero, zero_add, mul_zero]
    all_goals (simp only [mul_add, ← mul_div_assoc, hexpR] <;> ring)
  · simp only [indicator, hLm, hRm, hx, false_and,
      ite_false, inner_zero_left, mul_zero, add_zero]

/-- Exact positive-pole self entry of every visible literal prime atom. -/
theorem ccmPrimeTransport_polar_self (a : SuzukiPositiveAperture) {n : ℕ}
    (hn : 2≤n) (hvisible : Real.log n≤2*a.1) :
    inner ℂ (ccmPrimeTransportOperator a n (ccmPolarApertureVector a (1/2)))
      (ccmPolarApertureVector a (1/2)) =
      ((2*(Real.exp a.1/n-Real.exp (-a.1)):ℝ):ℂ) := by
  rw [atom_pole_integral a hn, show (1/2:ℝ)+1/2=1 by ring]
  simp only [one_mul, integral_complex_ofReal]
  have hl : -a.1≤a.1-Real.log n := by linarith
  have hr : Real.log n-a.1≤a.1 := by linarith
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hl, integral_exp,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr, integral_exp]
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  rw [Real.exp_sub, Real.exp_log hnR, show Real.log (n:ℝ)-a.1=Real.log n+ -a.1 by ring,
    Real.exp_add, Real.exp_log hnR]
  have hnC : (n:ℂ)≠0 := by exact_mod_cast hnR.ne'
  push_cast
  field_simp [hnC]
  ring

private theorem integral_one_Icc (l r : ℝ) (h : l≤r) :
    (∫ _x in Icc l r, (1:ℂ)) = ((r-l:ℝ):ℂ) := by
  simp only [setIntegral_const]
  rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr h),
    Complex.real_smul, mul_one]

/-- Exact opposite-pole entry of every visible literal prime atom. -/
theorem ccmPrimeTransport_polar_cross (a : SuzukiPositiveAperture) {n : ℕ}
    (hn : 2≤n) (hvisible : Real.log n≤2*a.1) :
    inner ℂ (ccmPrimeTransportOperator a n (ccmPolarApertureVector a (1/2)))
      (ccmPolarApertureVector a (-1/2)) =
      (((2*a.1-Real.log n)*(1+1/(n:ℝ)):ℝ):ℂ) := by
  rw [atom_pole_integral a hn, show (-1/2:ℝ)+1/2=0 by ring]
  simp only [zero_mul, Real.exp_zero, Complex.ofReal_one]
  rw [integral_one_Icc _ _ (by linarith), integral_one_Icc _ _ (by linarith)]
  push_cast
  ring

private theorem prime_visible (a : SuzukiPositiveAperture) {n : ℕ}
    (hn : n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊) : Real.log n≤2*a.1 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by have := (Finset.mem_Icc.mp hn).1; omega)
  exact (Real.log_le_iff_le_exp hnR).mpr
    ((Nat.le_floor_iff (Real.exp_pos _).le).mp (Finset.mem_Icc.mp hn).2)

private theorem psi_sum (X : ℝ) :
    Chebyshev.psi X = ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n := by
  rw [Chebyshev.psi_eq_sum_Icc]
  symm
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Finset.mem_Icc.mp hn).2⟩
  · intro n hn hnot
    simp only [Finset.mem_Icc] at hn hnot
    have hsmall : n=0 ∨ n=1 := by omega
    rcases hsmall with rfl | rfl <;> simp

/-- Actual positive-pole prime self energy reduces to two exact arithmetic cumulatives. -/
theorem ccmFinitePrimeOperator_polar_self (a : SuzukiPositiveAperture) :
    inner ℂ (ccmFinitePrimeOperator a (ccmPolarApertureVector a (1/2)))
      (ccmPolarApertureVector a (1/2)) =
      ((2*Real.exp a.1*ccmReciprocalMangoldtCumulative (Real.exp (2*a.1)) -
        2*Real.exp (-a.1)*Chebyshev.psi (Real.exp (2*a.1)):ℝ):ℂ) := by
  rw [inner_ccmFinitePrimeOperator, ccmReciprocalMangoldtCumulative, psi_sum]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [ccmPrimeTransport_polar_self a (Finset.mem_Icc.mp hn).1 (prime_visible a hn)]
  push_cast
  ring

/-- Exact moving-prime tent in the opposite-pole entry, including all prime powers. -/
def ccmPolarPrimeTent (a : SuzukiPositiveAperture) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
    ArithmeticFunction.vonMangoldt n * (1+1/(n:ℝ)) * (2*a.1-Real.log n)

/-- The opposite-pole prime pairing is the literal complete moving-prime tent. -/
theorem ccmFinitePrimeOperator_polar_cross (a : SuzukiPositiveAperture) :
    inner ℂ (ccmFinitePrimeOperator a (ccmPolarApertureVector a (1/2)))
      (ccmPolarApertureVector a (-1/2)) = (ccmPolarPrimeTent a:ℂ) := by
  rw [ccmFinitePrimeOperator, ccmPolarPrimeTent]
  simp only [sum_apply, sum_inner (𝕜:=ℂ), smul_apply,
    Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [inner_smul_left (ccmPrimeTransportOperator a n (ccmPolarApertureVector a (1/2)))
    (ccmPolarApertureVector a (-1/2)) (((ArithmeticFunction.vonMangoldt n:ℝ):ℂ)),
    Complex.conj_ofReal, ccmPrimeTransport_polar_cross a (Finset.mem_Icc.mp hn).1 (prime_visible a hn)]
  push_cast
  ring

/-- Each visible prime contributes nonnegatively to this exact cross-pole tent. -/
theorem ccmPolarPrimeTent_nonneg (a : SuzukiPositiveAperture) : 0≤ccmPolarPrimeTent a := by
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
    (sub_nonneg.mpr (prime_visible a hn))

end RHTower
