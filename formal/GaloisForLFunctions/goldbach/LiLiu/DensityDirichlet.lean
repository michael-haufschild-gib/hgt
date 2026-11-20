import GaloisForLFunctions.goldbach.LiLiu.DensityEuler
import GaloisForLFunctions.goldbach.LiLiu.SingularDensity
import GaloisForLFunctions.RHTower.EstermannExponentialMellin
import GaloisForLFunctions.RHTower.VerticalProgressionRatioForm
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-! # Euler factorization of the density series

The dilation coefficient is multiplicative. Its positive powers at a prime
all have the same weight, bounded by two. Thus its Dirichlet series is
dominated by the divisor series and its local sums are geometric.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open Finset _root_.Complex Filter
noncomputable section

private def primeWeight (N p : ℕ) : ℝ :=
  if 2 < p ∧ ¬p ∣ N then ((p : ℝ) - 1) / (p - 2) else 1

/-- The multiplicative coefficient S(kN)/S(N) at positive k. -/
def dilationCoeff (N : ℕ) : ArithmeticFunction ℝ := ArithmeticFunction.prodPrimeFactors (primeWeight N)

theorem singularSeries_mul_eq {N k : ℕ} (hN : N ≠ 0) (hk : k ≠ 0) :
    singularSeries (k * N) = singularSeries N * dilationCoeff N k := by
  rw [singularSeries_dilate hN hk, dilationCoeff, ArithmeticFunction.prodPrimeFactors_apply hk]
  congr 1
  simp only [primeWeight, ← Finset.prod_filter]
  congr 1
  ext p
  by_cases hp : p ∈ k.primeFactors
  · simp [oddFactors, hp, Nat.mem_primeFactors, hN, Nat.prime_of_mem_primeFactors hp]
    intro hp2
    simp [not_le.mpr hp2]
  · simp [oddFactors, hp]

private theorem abs_primeWeight_le (N p : ℕ) : |primeWeight N p| ≤ 2 := by
  unfold primeWeight
  split_ifs with h
  · have hp : (3 : ℝ) ≤ p := by exact_mod_cast h.1
    have hp2 : 0 < (p : ℝ) - 2 := by linarith only [hp]
    rw [abs_of_nonneg (div_nonneg (by linarith only [hp]) hp2.le), div_le_iff₀ hp2]
    linarith only [hp]
  · norm_num

theorem abs_dilationCoeff_le (N k : ℕ) : |dilationCoeff N k| ≤ k.divisors.card := by
  by_cases hk : k = 0
  · simp [hk]
  rw [dilationCoeff, ArithmeticFunction.prodPrimeFactors_apply hk, Finset.abs_prod]
  calc
    _ ≤ ∏ _p ∈ k.primeFactors, (2 : ℝ) :=
      Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun p _ => abs_primeWeight_le N p)
    _ ≤ _ := by
      rw [Finset.prod_const]
      exact_mod_cast _root_.RHTower.VerticalAP.two_pow_card_primeFactors_le_card_divisors hk

theorem dilationCoeff_summable (N : ℕ) {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (fun k => (dilationCoeff N k : ℂ)) w := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (_root_.RHTower.summable_divisorCount_rpow hw)
  intro k
  rw [LSeries.term_def₀ (by simp : (dilationCoeff N 0 : ℂ) = 0), norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rw [Complex.norm_natCast_cpow_of_pos hk, Complex.neg_re]
  exact mul_le_mul_of_nonneg_right (abs_dilationCoeff_le N k) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

private theorem primePower_cpow (p k : ℕ) (w : ℂ) :
    ((p ^ k : ℕ) : ℂ) ^ (-w) = ((p : ℂ) ^ (-w)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

private theorem hasProd_dilationSeries (N : ℕ) {w : ℂ} (hw : 1 < w.re) :
    HasProd (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-w))⁻¹ * (1 + densityIncrement N p w))
      (LSeries (fun k => (dilationCoeff N k : ℂ)) w) := by
  let f := LSeries.term (fun k => (dilationCoeff N k : ℂ)) w
  have hterm (k : ℕ) : f k = (dilationCoeff N k : ℂ) * (k : ℂ) ^ (-w) :=
    LSeries.term_def₀ (by simp) w k
  have hm := ArithmeticFunction.IsMultiplicative.prodPrimeFactors (primeWeight N)
  have h1 : f 1 = 1 := by rw [hterm, show dilationCoeff N 1 = 1 from hm.map_one]; simp
  have hmul {k l : ℕ} (hkl : k.Coprime l) : f (k * l) = f k * f l := by
    rw [hterm, show dilationCoeff N (k*l) = dilationCoeff N k * dilationCoeff N l from hm.map_mul_of_coprime hkl,
      Complex.ofReal_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, hterm, hterm]
    ring
  have hsum : Summable (fun k => ‖f k‖) := summable_norm_iff.mpr (dilationCoeff_summable N hw)
  apply (EulerProduct.eulerProduct_hasProd h1 hmul hsum (by simp [f])).congr_fun
  intro p
  symm
  let x : ℂ := (p : ℂ) ^ (-w)
  have hx : ‖x‖ < 1 := by
    rw [show ‖x‖ = (p : ℝ) ^ (-w.re) by rw [← Complex.neg_re, ← Complex.norm_natCast_cpow_of_pos p.prop.pos]]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith only [hw])
  have hd : 1 - x ≠ 0 := fun h => by rw [← sub_eq_zero.mp h, norm_one] at hx; exact lt_irrefl _ hx
  have hloc : Summable (fun k : ℕ => f ((p : ℕ) ^ k)) := (hsum.comp_injective (Nat.pow_right_injective p.prop.two_le)).of_norm
  rw [hloc.tsum_eq_zero_add, pow_zero, h1]
  have htail (k : ℕ) : f ((p : ℕ) ^ (k+1)) = ((primeWeight N p : ℂ) * x) * x ^ k := by
    rw [hterm, dilationCoeff, ArithmeticFunction.prodPrimeFactors_apply (pow_ne_zero _ p.prop.ne_zero),
      Nat.primeFactors_prime_pow (by omega) p.prop, Finset.prod_singleton, primePower_cpow, pow_succ]
    dsimp only [x]
    ring
  simp_rw [htail]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hx]
  change 1 + ((primeWeight N p : ℂ) * x) * (1 - x)⁻¹ = (1 - x)⁻¹ * (1 + densityIncrement N p w)
  unfold primeWeight densityIncrement
  split_ifs with he
  · have hp : (2 : ℝ) < p := by exact_mod_cast he.1
    have hp' : (p : ℂ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne')
    push_cast
    change 1 + ((((p : ℂ) - 1) / (p - 2)) * x) * (1 - x)⁻¹ = (1 - x)⁻¹ * (1 + x / (p - 2))
    field_simp [hd, hp']
    ring
  · push_cast
    field_simp [hd]
    ring

/-- On the half-plane of absolute convergence the Euler correction recovers
the original density coefficients at every positive dilation. -/
theorem densitySeries_kernel {N : ℕ} (hN : N ≠ 0) {w : ℂ} (hw : 1 < w.re) :
    LSeriesHasSum (fun k => (singularSeries (k*N) : ℂ)) w
      ((singularSeries N : ℂ) * riemannZeta w * densityEuler N w) := by
  have hd : HasProd (fun p => 1 + densityIncrement N p w) (densityEuler N w) :=
    (hasProdLocallyUniformlyOn_densityEuler N zero_lt_one).hasProd hw
  have he := (hasProd_dilationSeries N hw).unique ((riemannZeta_eulerProduct_hasProd hw).mul hd)
  have hs : HasSum (LSeries.term (fun k => (dilationCoeff N k : ℂ)) w)
      (LSeries (fun k => (dilationCoeff N k : ℂ)) w) := Summable.hasSum (dilationCoeff_summable N hw)
  rw [he] at hs
  have hs' := hs.mul_left (singularSeries N : ℂ)
  rw [mul_assoc]
  apply hs'.congr_fun
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · simp [LSeries.term_of_ne_zero hk.ne', singularSeries_mul_eq hN hk.ne', mul_div_assoc]

#print axioms densitySeries_kernel
end
end GaloisForLFunctions.Goldbach.LiLiu
