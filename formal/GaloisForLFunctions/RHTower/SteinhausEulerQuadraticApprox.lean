import GaloisForLFunctions.RHTower.SteinhausModel
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.PSeries

/-!
# Uniform quadratic approximation of literal random Euler products

The cubic remainder of each logarithmic Euler factor is summable uniformly on
`Re(s) ≥ 1/2`. Thus one constant, independent of the finite prime set, phases,
and imaginary part, controls the error in retaining the first two prime-power terms.
The literal squared product norm is consequently bounded above and below by the
exponential of that quadratic field with a fixed additive error in the exponent.

This is the deterministic comparison used by the critical-mass approach to the
independent recurrence producer. No low-moment decay or recurrence is asserted.
-/

noncomputable section
open Filter Topology Finset Complex
namespace RHTower

/-- The literal prime argument of a finite random Euler factor. -/
def steinhausEulerPrimeTerm (s : ℂ) (omega : SteinhausModel.Omega) (p : ℕ) : ℂ :=
  SteinhausModel.X p omega * (p : ℂ) ^ (-s)

/-- The finite random Euler product on a specified prime set. -/
def steinhausFiniteEulerProduct (P : Finset ℕ) (s : ℂ) (omega : SteinhausModel.Omega) : ℂ :=
  ∏ p ∈ P, (1 - steinhausEulerPrimeTerm s omega p)⁻¹

/-- The first two prime-power terms of the literal Euler-product logarithm. -/
def steinhausQuadraticEulerLog (P : Finset ℕ) (s : ℂ) (omega : SteinhausModel.Omega) : ℂ :=
  ∑ p ∈ P, (steinhausEulerPrimeTerm s omega p + (steinhausEulerPrimeTerm s omega p) ^ 2 / 2)

private theorem norm_neg_log_sub_quadratic {z : ℂ} (hz : ‖z‖ < 1) :
    ‖-Complex.log (1 - z) - (z + z ^ 2 / 2)‖ ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3 := by
  have h := Complex.norm_log_sub_logTaylor_le 2 (z := -z) (by simpa using hz)
  have ht : Complex.logTaylor 3 (-z) = -z - z ^ 2 / 2 := by
    norm_num [Complex.logTaylor, Finset.sum_range_succ]
    ring
  rw [ht, norm_neg] at h
  have heq : -Complex.log (1 - z) - (z + z ^ 2 / 2) =
      -(Complex.log (1 + -z) - (-z - z ^ 2 / 2)) := by
    simp only [sub_eq_add_neg]
    ring
  rw [heq, norm_neg]
  convert h using 1; norm_num

/-- A literal Euler prime argument is uniformly inside the unit disc on the closed right half-plane. -/
theorem norm_steinhausEulerPrimeTerm_le {s : ℂ} (hs : 1 / 2 ≤ s.re)
    (omega : SteinhausModel.Omega) {p : ℕ} (hp : p.Prime) :
    ‖steinhausEulerPrimeTerm s omega p‖ ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) ∧
      (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  constructor
  · rw [steinhausEulerPrimeTerm, norm_mul, SteinhausModel.norm_X, one_mul,
      Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  · exact Real.rpow_le_rpow_of_nonpos (by norm_num) hpR (by norm_num)

private theorem eulerPrimeTerm_norm_lt_one {s : ℂ} (hs : 1 / 2 ≤ s.re)
    (omega : SteinhausModel.Omega) {p : ℕ} (hp : p.Prime) :
    ‖steinhausEulerPrimeTerm s omega p‖ < 1 := by
  obtain ⟨h1, h2⟩ := norm_steinhausEulerPrimeTerm_le hs omega hp
  exact (h1.trans h2).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))

/-- The literal finite product is the exponential of its sum of principal logarithms. -/
theorem steinhausFiniteEulerProduct_eq_exp
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {s : ℂ} (hs : 1 / 2 ≤ s.re)
    (omega : SteinhausModel.Omega) :
    steinhausFiniteEulerProduct P s omega =
      Complex.exp (∑ p ∈ P, -Complex.log (1 - steinhausEulerPrimeTerm s omega p)) := by
  have hne : ∀ p ∈ P, (1 : ℂ) - steinhausEulerPrimeTerm s omega p ≠ 0 := by
    intro p hp heq
    have he : steinhausEulerPrimeTerm s omega p = 1 := (sub_eq_zero.mp heq).symm
    have hh := eulerPrimeTerm_norm_lt_one hs omega (hP p hp)
    rw [he, norm_one] at hh
    exact (lt_irrefl _ hh)
  rw [Complex.exp_sum]
  apply prod_congr rfl
  intro p hp
  rw [Complex.exp_neg, Complex.exp_log (hne p hp)]

/-- The logarithm of the literal product norm is the real part of its finite logarithmic sum. -/
theorem log_norm_steinhausFiniteEulerProduct
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {s : ℂ} (hs : 1 / 2 ≤ s.re)
    (omega : SteinhausModel.Omega) :
    Real.log ‖steinhausFiniteEulerProduct P s omega‖ =
      (∑ p ∈ P, -Complex.log (1 - steinhausEulerPrimeTerm s omega p)).re := by
  rw [steinhausFiniteEulerProduct_eq_exp P hP hs omega, Complex.norm_exp, Real.log_exp]

/-- One cutoff-independent constant controls the quadratic logarithmic remainder everywhere
on the closed right half-plane, for every multiplicative phase. -/
theorem exists_steinhausEulerLog_quadratic_remainder_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ s : ℂ, 1 / 2 ≤ s.re → ∀ omega : SteinhausModel.Omega,
      ‖(∑ p ∈ P, -Complex.log (1 - steinhausEulerPrimeTerm s omega p)) -
        steinhausQuadraticEulerLog P s omega‖ ≤ C := by
  let rho : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))
  have hrho : rho < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  let A : ℝ := (1 - rho)⁻¹ / 3
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  refine ⟨A * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)), by positivity, ?_⟩
  intro P hP s hs omega
  have hterm : ∀ p ∈ P,
      ‖-Complex.log (1 - steinhausEulerPrimeTerm s omega p) -
        (steinhausEulerPrimeTerm s omega p + (steinhausEulerPrimeTerm s omega p) ^ 2 / 2)‖ ≤
      A * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro p hp
    obtain ⟨hpow, hr⟩ := norm_steinhausEulerPrimeTerm_le hs omega (hP p hp)
    have hzrho : ‖steinhausEulerPrimeTerm s omega p‖ ≤ rho := hpow.trans hr
    have hcube : ‖steinhausEulerPrimeTerm s omega p‖ ^ 3 ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
      calc
        _ ≤ ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hpow 3
        _ = _ := by rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]; norm_num
    have hinv : (1 - ‖steinhausEulerPrimeTerm s omega p‖)⁻¹ ≤ (1 - rho)⁻¹ :=
      inv_anti₀ (by linarith) (by linarith)
    calc
      _ ≤ ‖steinhausEulerPrimeTerm s omega p‖ ^ 3 *
          (1 - ‖steinhausEulerPrimeTerm s omega p‖)⁻¹ / 3 :=
        norm_neg_log_sub_quadratic (eulerPrimeTerm_norm_lt_one hs omega (hP p hp))
      _ ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) * (1 - rho)⁻¹ / 3 :=
        div_le_div_of_nonneg_right (mul_le_mul hcube hinv (inv_nonneg.mpr (by linarith)) (by positivity)) (by norm_num)
      _ = _ := by dsimp [A]; ring
  calc
    _ = ‖∑ p ∈ P, (-Complex.log (1 - steinhausEulerPrimeTerm s omega p) -
        (steinhausEulerPrimeTerm s omega p + (steinhausEulerPrimeTerm s omega p) ^ 2 / 2))‖ := by
      rw [steinhausQuadraticEulerLog, sum_sub_distrib]
    _ ≤ ∑ p ∈ P, ‖-Complex.log (1 - steinhausEulerPrimeTerm s omega p) -
        (steinhausEulerPrimeTerm s omega p + (steinhausEulerPrimeTerm s omega p) ^ 2 / 2)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ P, A * (p : ℝ) ^ (-(3 / 2 : ℝ)) := sum_le_sum hterm
    _ = A * ∑ p ∈ P, (p : ℝ) ^ (-(3 / 2 : ℝ)) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hsum.sum_le_tsum P (fun _ _ => by positivity)) hA

/-- Uniform real logarithmic comparison for the actual finite Euler product. -/
theorem exists_log_norm_steinhausFiniteEulerProduct_sub_quadratic_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ s : ℂ, 1 / 2 ≤ s.re → ∀ omega : SteinhausModel.Omega,
      |Real.log ‖steinhausFiniteEulerProduct P s omega‖ -
        (steinhausQuadraticEulerLog P s omega).re| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_steinhausEulerLog_quadratic_remainder_bound
  refine ⟨C, hC, ?_⟩
  intro P hP s hs omega
  rw [log_norm_steinhausFiniteEulerProduct P hP hs omega, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (hbound P hP s hs omega)

/-- The literal squared Euler-product norm is bounded on both sides by the exponential
of its quadratic prime field, with one error constant for all cutoffs, phases and heights. -/
theorem exists_steinhausFiniteEulerProduct_normSq_quadratic_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ s : ℂ, 1 / 2 ≤ s.re → ∀ omega : SteinhausModel.Omega,
      Real.exp (2 * (steinhausQuadraticEulerLog P s omega).re - C) ≤
        ‖steinhausFiniteEulerProduct P s omega‖ ^ 2 ∧
      ‖steinhausFiniteEulerProduct P s omega‖ ^ 2 ≤
        Real.exp (2 * (steinhausQuadraticEulerLog P s omega).re + C) := by
  obtain ⟨C, hC, hbound⟩ := exists_log_norm_steinhausFiniteEulerProduct_sub_quadratic_le
  refine ⟨2 * C, by positivity, ?_⟩
  intro P hP s hs omega
  have hh := abs_le.mp (hbound P hP s hs omega)
  have heq : ‖steinhausFiniteEulerProduct P s omega‖ ^ 2 =
      Real.exp (2 * Real.log ‖steinhausFiniteEulerProduct P s omega‖) := by
    rw [steinhausFiniteEulerProduct_eq_exp P hP hs omega, Complex.norm_exp, Real.log_exp,
      sq, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  constructor <;> apply Real.exp_le_exp.mpr <;> linarith [hh.1, hh.2]

end RHTower
