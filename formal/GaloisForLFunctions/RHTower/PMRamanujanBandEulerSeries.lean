import GaloisForLFunctions.RHTower.PMRamanujanBandEulerCorrection
import GaloisForLFunctions.RHTower.EisensteinHeckeCoefficient
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# The complete arithmetic Euler series of the moving Ramanujan band

The literal finite-primitive Mellin symbol is a Dirichlet convolution.
Its exact coprime factorization and an absolute L-series majorant justify
the complete Euler product in its initial convergence domain. The final
identity retains both zeta factors and every actual Ramanujan coefficient.
No moving-cutoff interchange, Hilbert escape or small-damping energy ceiling
is asserted here.
-/

open Complex ArithmeticFunction Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

/-- The actual divisor symbol as Dirichlet convolution, including the zero convention. -/
theorem pmRamanujanMellinSymbol_eq_convolution (q : ℕ) (s : ℂ) :
    pmRamanujanMellinSymbol q s =
      (cpowArithmetic (1-s) * ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) q := by
  rw [pmRamanujanMellinSymbol, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  rw [cpowArithmetic_apply _
    (Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)).ne']
  simp only [ArithmeticFunction.intCoe_apply]
  ring

theorem pmRamanujanMellinSymbol_mul_coprime (s : ℂ) {m n : ℕ}
    (hmn : m.Coprime n) :
    pmRamanujanMellinSymbol (m*n) s =
      pmRamanujanMellinSymbol m s * pmRamanujanMellinSymbol n s := by
  simp only [pmRamanujanMellinSymbol_eq_convolution]
  exact ((isMultiplicative_cpowArithmetic (1-s)).mul
    ArithmeticFunction.isMultiplicative_moebius.intCast).map_mul_of_coprime hmn

theorem pmPowerDampedRamanujanDenominator_mul_coprime (ε : ℝ) {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n) :
    pmPowerDampedRamanujanDenominator ε (m*n) =
      pmPowerDampedRamanujanDenominator ε m * pmPowerDampedRamanujanDenominator ε n := by
  simp only [pmPowerDampedRamanujanDenominator, Nat.primeFactors_mul hm hn,
    Finset.prod_union hmn.disjoint_primeFactors]

def pmRamanujanBandMellinCoefficient (ε : ℝ) (z s : ℂ) (q : ℕ) : ℂ :=
  (moebius q : ℂ)/(pmPowerDampedRamanujanDenominator ε q : ℂ) *
    pmRamanujanMellinSymbol q s * (q : ℂ)^((ε : ℂ)+s-z)

theorem pmRamanujanBandMellinCoefficient_mul_coprime (ε : ℝ) (z s : ℂ)
    {m n : ℕ} (hmn : m.Coprime n) :
    pmRamanujanBandMellinCoefficient ε z s (m*n) =
      pmRamanujanBandMellinCoefficient ε z s m *
        pmRamanujanBandMellinCoefficient ε z s n := by
  by_cases hm : m = 0
  · subst m
    simp [pmRamanujanBandMellinCoefficient]
  by_cases hn : n = 0
  · subst n
    simp [pmRamanujanBandMellinCoefficient]
  simp only [pmRamanujanBandMellinCoefficient,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn,
    pmPowerDampedRamanujanDenominator_mul_coprime ε hm hn hmn,
    pmRamanujanMellinSymbol_mul_coprime s hmn, Int.cast_mul, Complex.ofReal_mul,
    Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

theorem pmRamanujanBandMellinCoefficient_eq_actual {ε : ℝ} (hε : 0 < ε)
    (z s : ℂ) (q : ℕ) :
    pmPowerDampedDivisorDensity ε * pmRamanujanBandMellinCoefficient ε z s q =
      pmPowerDampedRamanujanWeight ε q * pmRamanujanMellinSymbol q s *
        (q : ℂ)^((ε : ℂ)+s-z) := by
  rw [pmPowerDampedRamanujanWeight_eq_euler ε hε]
  unfold pmRamanujanBandMellinCoefficient
  ring

theorem LSeriesSummable_pmRamanujanMellinSymbol {z s : ℂ}
    (hz : 1 < z.re) (hs : s.re < 1) :
    LSeriesSummable (fun q => pmRamanujanMellinSymbol q s) (1+z-s) := by
  have hp : LSeriesSummable (fun q => cpowArithmetic (1-s) q) (1+z-s) := by
    apply LSeriesSummable_of_le_const_mul_rpow (x := 2-s.re)
      (by simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; linarith)
    refine ⟨1, fun q hq => ?_⟩
    rw [cpowArithmetic_apply _ hq, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hq)]
    simp only [Complex.sub_re, Complex.one_re, one_mul]
    have he : 2-s.re-1 = 1-s.re := by ring
    rw [he]
  have hm : LSeriesSummable (fun q => (moebius q : ℂ)) (1+z-s) := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    · intro q _
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
    · simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
      linarith
  have hconv := ArithmeticFunction.LSeriesSummable_mul (f := cpowArithmetic (1-s))
    (g := ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) hp hm
  simpa only [pmRamanujanMellinSymbol_eq_convolution] using hconv

theorem norm_pmRamanujanBandMellinTerm_le {ε : ℝ} (hε : 0 < ε)
    (z s : ℂ) (q : ℕ) :
    ‖pmPowerDampedRamanujanWeight ε q * pmRamanujanMellinSymbol q s *
      (q : ℂ)^((ε : ℂ)+s-z)‖ ≤
        ‖LSeries.term (fun n => pmRamanujanMellinSymbol n s) (1+z-s) q‖ := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [pmPowerDampedRamanujanWeight_zero]
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hq,
    LSeries.term_of_ne_zero hq.ne', norm_div, Complex.norm_natCast_cpow_of_pos hq]
  calc
    _ ≤ (1/(q : ℝ)^(1+ε))*‖pmRamanujanMellinSymbol q s‖ *
        (q : ℝ)^(((ε : ℂ)+s-z).re) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (norm_pmPowerDampedRamanujanWeight_le hε hq)
          (norm_nonneg _)) (Real.rpow_nonneg hqR.le _)
    _ = _ := by
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.one_re,
        div_eq_mul_inv, one_mul]
      rw [← Real.rpow_neg hqR.le, ← Real.rpow_neg hqR.le]
      calc
        _ = ‖pmRamanujanMellinSymbol q s‖ *
            ((q : ℝ)^(-(1+ε))*(q : ℝ)^(ε+s.re-z.re)) := by ring
        _ = _ := by rw [← Real.rpow_add hqR]; congr 2; ring

theorem summable_norm_pmRamanujanBandMellinTerm {ε : ℝ} (hε : 0 < ε)
    {z s : ℂ} (hz : 1 < z.re) (hs : s.re < 1) :
    Summable (fun q => ‖pmPowerDampedRamanujanWeight ε q * pmRamanujanMellinSymbol q s *
      (q : ℂ)^((ε : ℂ)+s-z)‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_pmRamanujanBandMellinTerm_le hε z s)
    (LSeriesSummable_pmRamanujanMellinSymbol hz hs).norm

private theorem pmbs_density_ne_zero {ε : ℝ} (hε : 0 < ε) :
    pmPowerDampedDivisorDensity ε ≠ 0 := by
  intro he
  have h := pmPowerDampedDivisorDensity_re_pos hε
  simp only [he, Complex.zero_re, lt_self_iff_false] at h

theorem summable_norm_pmRamanujanBandMellinCoefficient {ε : ℝ} (hε : 0 < ε)
    {z s : ℂ} (hz : 1 < z.re) (hs : s.re < 1) :
    Summable (fun q => ‖pmRamanujanBandMellinCoefficient ε z s q‖) := by
  have he (q : ℕ) : pmRamanujanBandMellinCoefficient ε z s q =
      (pmPowerDampedDivisorDensity ε)⁻¹ *
        (pmPowerDampedRamanujanWeight ε q * pmRamanujanMellinSymbol q s *
          (q : ℂ)^((ε : ℂ)+s-z)) := by
    rw [← pmRamanujanBandMellinCoefficient_eq_actual hε z s q, ← mul_assoc,
      inv_mul_cancel₀ (pmbs_density_ne_zero hε), one_mul]
  simp_rw [he, norm_mul]
  simpa only [norm_mul] using
    (summable_norm_pmRamanujanBandMellinTerm hε hz hs).mul_left
      ‖(pmPowerDampedDivisorDensity ε)⁻¹‖

private theorem pmbs_coefficient_one (ε : ℝ) (z s : ℂ) :
    pmRamanujanBandMellinCoefficient ε z s 1 = 1 := by
  simp [pmRamanujanBandMellinCoefficient, pmRamanujanMellinSymbol,
    pmPowerDampedRamanujanDenominator]

theorem tsum_pmRamanujanBandMellinCoefficient_prime_pow (ε : ℝ) (z s : ℂ)
    {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, pmRamanujanBandMellinCoefficient ε z s (p^k)) =
      1+pmRamanujanBandMellinCoefficient ε z s p := by
  rw [tsum_eq_sum (s := ({0,1} : Finset ℕ))]
  · simp [pmbs_coefficient_one]
  · intro k hk
    have hk0 : k ≠ 0 := by simpa using fun h => hk (by simp [h])
    have hk1 : k ≠ 1 := by simpa using fun h => hk (by simp [h])
    simp [pmRamanujanBandMellinCoefficient, ArithmeticFunction.moebius_apply_prime_pow hp hk0,
      hk1]

theorem hasProd_pmRamanujanBandMellinCoefficient {ε : ℝ} (hε : 0 < ε)
    {z s : ℂ} (hz : 1 < z.re) (hs : s.re < 1) :
    HasProd (fun p : Nat.Primes => 1+pmRamanujanBandMellinCoefficient ε z s p)
      (∑' q : ℕ, pmRamanujanBandMellinCoefficient ε z s q) := by
  have h := EulerProduct.eulerProduct_hasProd (pmbs_coefficient_one ε z s)
    (fun {_ _} hmn => pmRamanujanBandMellinCoefficient_mul_coprime ε z s hmn)
    (summable_norm_pmRamanujanBandMellinCoefficient hε hz hs)
    (by simp [pmRamanujanBandMellinCoefficient])
  exact h.congr_fun (fun p =>
    (tsum_pmRamanujanBandMellinCoefficient_prime_pow ε z s p.property).symm)

private theorem pmbs_one_sub_cpow_ne_zero {p : ℕ} (hp : p.Prime)
    {v : ℂ} (hv : v.re < 0) : (1 : ℂ)-(p : ℂ)^v ≠ 0 := by
  have hn : ‖(p : ℂ)^v‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) hv
  intro he
  rw [← sub_eq_zero.mp he, norm_one] at hn
  exact lt_irrefl _ hn

/-- The infinite actual arithmetic series, with both zeta factors cleared. -/
theorem pmRamanujanBandMellinSeries_cleared_eq {ε : ℝ} (hε : 0 < ε)
    {z s : ℂ} (hz : 1 < z.re) (hs : s.re < 9/16) :
    riemannZeta z * (∑' q : ℕ, pmPowerDampedRamanujanWeight ε q *
      pmRamanujanMellinSymbol q s * (q : ℂ)^((ε : ℂ)+s-z)) =
      pmPowerDampedDivisorDensity ε * riemannZeta (1+z-s) *
        pmRamanujanBandEulerCorrection ε z s := by
  have hw : 1 < (1+z-s).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
    linarith
  have hloc (p : Nat.Primes) :
      (1+pmRamanujanBandMellinCoefficient ε z s p)*(1-(p : ℂ)^(-z))⁻¹ =
        pmRamanujanBandEulerFactor ε z s p * (1-(p : ℂ)^(-(1+z-s)))⁻¹ := by
    have hc := pmbs_one_sub_cpow_ne_zero p.property
      (v := -z) (by simp only [Complex.neg_re]; linarith)
    have hb := pmbs_one_sub_cpow_ne_zero p.property
      (v := s-z-1) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    have he := pmRamanujanBandEulerFactor_prime_identity hε p.property
      (by linarith : 0 < z.re) s
    rw [← pmRamanujanBandMellinCoefficient_eq_actual hε z s p] at he
    have he' : (1+pmRamanujanBandMellinCoefficient ε z s p)*(1-(p : ℂ)^(s-z-1)) =
        (1-(p : ℂ)^(-z))*pmRamanujanBandEulerFactor ε z s p := by
      apply mul_left_cancel₀ (pmbs_density_ne_zero hε)
      linear_combination he
    rw [show -(1+z-s) = s-z-1 by ring]
    field_simp
    linear_combination he'
  have hleft := (hasProd_pmRamanujanBandMellinCoefficient hε hz
    (show s.re < 1 by linarith)).mul
    (riemannZeta_eulerProduct_hasProd hz)
  have hcorr : HasProd (fun p : Nat.Primes => pmRamanujanBandEulerFactor ε z s p)
      (pmRamanujanBandEulerCorrection ε z s) :=
    (multipliable_pmRamanujanBandEulerFactor hε.le (by linarith) hs.le).hasProd
  have hright := hcorr.mul (riemannZeta_eulerProduct_hasProd hw)
  have hident := hleft.unique (hright.congr_fun hloc)
  have hseries : (∑' q : ℕ, pmPowerDampedRamanujanWeight ε q *
      pmRamanujanMellinSymbol q s * (q : ℂ)^((ε : ℂ)+s-z)) =
        pmPowerDampedDivisorDensity ε * ∑' q : ℕ, pmRamanujanBandMellinCoefficient ε z s q := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun q => (pmRamanujanBandMellinCoefficient_eq_actual hε z s q).symm)
  rw [hseries]
  linear_combination pmPowerDampedDivisorDensity ε * hident

end RHTower
