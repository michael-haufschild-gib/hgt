import GaloisForLFunctions.ThetaCuspSections.PowerPolynomialKernel
import GaloisForLFunctions.CompletedArithmeticForms.BesselGammaSpectralFloor

/-!
# A compact reserve cannot fund every Gamma polynomial direction

Normalized monomials have bounded energy in every fixed parabolic core.
Their Gamma energy on the outer annulus grows geometrically with degree.
This gives an explicit lower bound on the required payment constant and
excludes a degree-independent compact-core comparison.
-/

open Polynomial MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections
open GaloisForLFunctions.CompletedArithmeticForms

/-- A monomial normalized at the radius of the compact core. -/
def coreEscapePolynomial (R : ℝ) (n : ℕ) : ℝ[X] := (C R⁻¹ * X) ^ n

theorem coreEscapePolynomial_eval (R b : ℝ) (n : ℕ) :
    (coreEscapePolynomial R n).eval b = (b / R) ^ n := by
  simp only [coreEscapePolynomial, eval_pow, eval_mul, eval_C, eval_X, div_eq_mul_inv, mul_comm]

/-- Every normalized monomial has uniformly bounded compact-core energy. -/
theorem coreEscapePolynomial_core_le {R : ℝ} (hR : 0 < R) (m n : ℕ) :
    parabolicPowerEnergy R m (coreEscapePolynomial R n) ≤ 2 * R := by
  have hpoint (b : ℝ) (hb : b ∈ Icc (-R) R) :
      ((1 - b ^ 2 / R ^ 2) ^ m * (coreEscapePolynomial R n).eval b) ^ 2 ≤ 1 := by
    have hb2 : b ^ 2 ≤ R ^ 2 := by nlinarith only [hb.1, hb.2]
    have hratio : b ^ 2 / R ^ 2 ≤ 1 :=
      (div_le_iff₀ (sq_pos_of_pos hR)).mpr (by simpa only [one_mul] using hb2)
    have hr0 : 0 ≤ b ^ 2 / R ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hw0 : 0 ≤ 1 - b ^ 2 / R ^ 2 := sub_nonneg.mpr hratio
    have hw1 : 1 - b ^ 2 / R ^ 2 ≤ 1 := by linarith only [hr0]
    have hw : ((1 - b ^ 2 / R ^ 2) ^ m) ^ 2 ≤ 1 := by
      have h1 := pow_le_pow_left₀ hw0 hw1 m
      simp only [one_pow] at h1
      simpa only [one_pow] using pow_le_pow_left₀ (pow_nonneg hw0 m) h1 2
    have hP : (coreEscapePolynomial R n).eval b ^ 2 ≤ 1 := by
      rw [coreEscapePolynomial_eval, ← pow_mul, Nat.mul_comm n 2, pow_mul, div_pow]
      simpa only [one_pow] using pow_le_pow_left₀ hr0 hratio n
    rw [mul_pow]
    simpa only [one_mul] using mul_le_mul hw hP (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hi := intervalIntegral.integral_mono_on (by linarith only [hR] : -R ≤ R)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (continuous_const.intervalIntegrable (-R) R) hpoint
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hi
  exact hi.trans_eq (by ring)

/-- A fixed outer annulus already forces geometric growth of the Gamma energy. -/
theorem coreEscapePolynomial_gamma_ge {R : ℝ} (hR : 0 < R) (n : ℕ) :
    R * 4 ^ n / Real.cosh (3 * Real.pi * R / 2) ≤
      ∫ b : ℝ, (coreEscapePolynomial R n).eval b ^ 2 / Real.cosh (Real.pi * b / 2) := by
  let P := coreEscapePolynomial R n
  have hc : Continuous (fun b : ℝ => P.eval b ^ 2 / Real.cosh (Real.pi * b / 2)) :=
    Continuous.div (by fun_prop) (by fun_prop) (fun b => (Real.cosh_pos _).ne')
  have hpoint (b : ℝ) (hb : b ∈ Icc (2 * R) (3 * R)) :
      4 ^ n / Real.cosh (3 * Real.pi * R / 2) ≤ P.eval b ^ 2 / Real.cosh (Real.pi * b / 2) := by
    have hbr : 2 ≤ b / R := (le_div_iff₀ hR).mpr hb.1
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hbr n
    have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 ^ n) hpow 2
    have he : ((2 : ℝ) ^ n) ^ 2 = 4 ^ n := by
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
      norm_num
    rw [he, ← coreEscapePolynomial_eval] at hsq
    have hcosh : Real.cosh (Real.pi * b / 2) ≤ Real.cosh (3 * Real.pi * R / 2) := by
      apply Real.cosh_le_cosh.mpr
      rw [abs_of_nonneg (by positivity : 0 ≤ Real.pi * b / 2),
        abs_of_nonneg (by positivity : 0 ≤ 3 * Real.pi * R / 2)]
      nlinarith only [mul_le_mul_of_nonneg_left hb.2 Real.pi_pos.le]
    apply (div_le_div_iff₀ (Real.cosh_pos _) (Real.cosh_pos _)).mpr
    exact (mul_le_mul_of_nonneg_left hcosh (by positivity : (0 : ℝ) ≤ 4 ^ n)).trans
      (mul_le_mul_of_nonneg_right hsq (Real.cosh_pos _).le)
  have hab : 2 * R ≤ 3 * R := by linarith only [hR]
  have hi := intervalIntegral.integral_mono_on hab
    (continuous_const.intervalIntegrable (2 * R) (3 * R))
    (hc.intervalIntegrable _ _) hpoint
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  have hrest := setIntegral_le_integral (s := Ioc (2 * R) (3 * R))
    (integrable_polynomial_sq_sech P) (Eventually.of_forall fun b =>
      div_nonneg (sq_nonneg _) (Real.cosh_pos _).le)
  rw [← intervalIntegral.integral_of_le hab] at hrest
  calc
    _ = (3 * R - 2 * R) * (4 ^ n / Real.cosh (3 * Real.pi * R / 2)) := by ring
    _ ≤ _ := hi
    _ ≤ _ := hrest

/-- The required core-to-Gamma comparison constant grows at least geometrically. -/
theorem coreEscapePolynomial_gamma_core_ratio {R : ℝ} (hR : 0 < R) (m n : ℕ) :
    (4 ^ n / (2 * Real.cosh (3 * Real.pi * R / 2))) *
      parabolicPowerEnergy R m (coreEscapePolynomial R n) ≤
        ∫ b : ℝ, (coreEscapePolynomial R n).eval b ^ 2 / Real.cosh (Real.pi * b / 2) := by
  have hh := mul_le_mul_of_nonneg_left (coreEscapePolynomial_core_le hR m n)
    (by positivity : 0 ≤ 4 ^ n / (2 * Real.cosh (3 * Real.pi * R / 2)))
  calc
    _ ≤ _ := hh
    _ = R * 4 ^ n / Real.cosh (3 * Real.pi * R / 2) := by ring
    _ ≤ _ := coreEscapePolynomial_gamma_ge hR n

/-- No fixed compact power core dominates the Gamma norm in every polynomial degree. -/
theorem not_uniform_gamma_payment_from_compact_core {R : ℝ} (hR : 0 < R) (m : ℕ) :
    ¬ ∃ C : ℝ, ∀ P : ℝ[X],
      (∫ b : ℝ, P.eval b ^ 2 / Real.cosh (Real.pi * b / 2)) ≤
        C * parabolicPowerEnergy R m P := by
  rintro ⟨C, hC⟩
  let M := Real.cosh (3 * Real.pi * R / 2)
  have hM : 0 < M := Real.cosh_pos _
  have hlim := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_gt_atTop (2 * M * max C 0))).exists
  have hupper : (∫ b : ℝ, (coreEscapePolynomial R n).eval b ^ 2 /
      Real.cosh (Real.pi * b / 2)) ≤ max C 0 * (2 * R) := by
    calc
      _ ≤ _ := hC (coreEscapePolynomial R n)
      _ ≤ max C 0 * parabolicPowerEnergy R m (coreEscapePolynomial R n) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (parabolicPowerEnergy_nonneg hR.le m _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (coreEscapePolynomial_core_le hR m n) (le_max_right _ _)
  have hbound := (coreEscapePolynomial_gamma_ge hR n).trans hupper
  change R * 4 ^ n / M ≤ _ at hbound
  rw [div_le_iff₀ hM] at hbound
  have hstrict := mul_lt_mul_of_pos_left hn hR
  nlinarith only [hbound, hstrict]

#print axioms coreEscapePolynomial_gamma_core_ratio
#print axioms not_uniform_gamma_payment_from_compact_core

end GaloisForLFunctions.ThetaCuspSections
