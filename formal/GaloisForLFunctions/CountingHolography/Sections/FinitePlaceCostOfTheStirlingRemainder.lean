import GaloisForLFunctions.CountingHolography.Sections.ThePrimeExponentsOnTheSquareDiagonal
import GaloisForLFunctions.CountingHolography.Sections.TheNumeratorAboveSquareRootMultiplicity

/-! # Finite-place cost of bisecting the factorial price

Twice a factorial entropy contributes a multiple of 2p to the p-coordinate.
The dyadic profile lies between −p and p at every prime for large square
conductors. Perturbing it by the actual rounding error loses at most twice
the absolute row error. Thus the whole original finite height survives
within a quadratic error, uniformly over the factorial coordinates.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology Finset ArithmeticWeightTheory ArithmeticFunction _root_.RHTower
open _root_.RHTower.WeilDeletion BiScaleUncertainty.ChebyshevGauge

/-- The total absolute valuation mass is the sum of the logarithms of the two
coprime parts of the rational section generator. -/
theorem ordinary_absolute_prime_mass {N : ℕ} (a : Fin N → ℤ) :
    let q := ordinaryPrimeGenerator a
    (∑ k ∈ ordinaryPrimeLags (3*windowEnd N), |(deningerRatExp q k:ℝ)| * vonMangoldt k) =
      Real.log q.num.natAbs+Real.log q.den := by
  dsimp only
  rw [log_ordinaryPrimeGenerator_den,ordinaryPrimeGenerator_num,log_ordinaryPrimeModulus,log_ordinaryPrimeGenerator,
    ← sum_sub_distrib,← sum_add_distrib]
  refine sum_congr rfl fun k hk => ?_
  rw [ordinaryPrimeGenerator_exponent,if_pos hk,← sub_mul,← add_mul]
  congr 1
  rw [← Int.floor_toNat]
  have hh (z : ℤ) : |z|=(z.toNat:ℤ)+((z.toNat:ℤ)-z) := by omega
  exact_mod_cast hh _

private theorem profile_small_relative_to_prime :
    ∀ᶠ n : ℕ in atTop, ∀ {p : ℕ}, p.Prime → |diagonalPrimeProfile n p| ≤ p := by
  have hkH : HasCompactSupport splineAutoCorr := by
    rw [show splineAutoCorr=upow 1 7 from funext splineAutoCorr_eq_eight_boxes]
    exact hasCompactSupport_upow 1 7
  obtain ⟨B,hB⟩ := hkH.exists_bound_of_continuous continuous_splineAutoCorr
  let d := Real.exp (-8)
  have hd : 0<d := Real.exp_pos _
  let C := 6*B/Real.sqrt d
  filter_upwards [eventually_ge_atTop 1,tendsto_natCast_atTop_atTop.eventually_ge_atTop (C/d)] with n hn hlarge
  intro p hp
  have hn' := Nat.cast_pos.mpr hn (α := ℝ)
  have hp' := Nat.cast_pos.mpr hp.pos (α := ℝ)
  let y := (p:ℝ)/(n:ℝ)^2
  have hy : 0<y := div_pos hp' (sq_pos_of_pos hn')
  rw [diagonalPrimeProfile_eq_dilate hn hp.pos]
  change |2*(n:ℝ)*(squareLogProfile (Real.log y)/Real.sqrt y)| ≤ _
  by_cases h : d ≤ y
  · have hs : |squareLogProfile (Real.log y)| ≤ 3*B := by
      have h₁ := hB (Real.log y)
      have h₂ := hB (Real.log y-Real.log 4)
      have h₃ := abs_sub (2*splineAutoCorr (Real.log y)) (splineAutoCorr (Real.log y-Real.log 4))
      rw [abs_mul,abs_two] at h₃
      change |2*splineAutoCorr (Real.log y)-splineAutoCorr (Real.log y-Real.log 4)| ≤ _
      simp only [Real.norm_eq_abs] at h₁ h₂
      linarith only [h₁,h₂,h₃]
    have hdiv := div_le_div₀ (show 0≤3*B from (abs_nonneg _).trans hs) hs (Real.sqrt_pos.mpr hd) (Real.sqrt_le_sqrt h)
    have hh := mul_le_mul_of_nonneg_left hdiv (show 0≤2*(n:ℝ) by positivity)
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*(n:ℝ)),abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
    have ht := (div_le_iff₀ hd).mp hlarge
    have hl := (le_div_iff₀ (sq_pos_of_pos hn')).mp h
    change 6*B/Real.sqrt d ≤ (n:ℝ)*d at ht
    calc _ ≤ 2*(n:ℝ)*(3*B/Real.sqrt d) := hh
      _ = (6*B/Real.sqrt d)*n := by ring
      _ ≤ ((n:ℝ)*d)*n := mul_le_mul_of_nonneg_right ht hn'.le
      _ ≤ _ := by linarith only [hl]
  · have hl := (Real.log_lt_iff_lt_exp hy).mpr (lt_of_not_ge h)
    have hd₄ := Real.log_nonneg (by norm_num : (1:ℝ)≤4)
    have h₁ : 8<|Real.log y| := by linarith only [hl,neg_abs_le (Real.log y)]
    have h₂ : 8<|Real.log y-Real.log 4| := by linarith only [hl,hd₄,neg_abs_le (Real.log y-Real.log 4)]
    simp [squareLogProfile,splineAutoCorr_zero_outside h₁,splineAutoCorr_zero_outside h₂]

/-- On the interval from −p to p, zero is a nearest point of the lattice
of multiples of 2p. -/
private theorem abs_le_even_prime_shift {x p : ℝ} (hx : |x| ≤ p) (j : ℤ) : |x| ≤ |x-2*p*j| := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  have hp := (abs_nonneg _).trans hx
  have hj' : (1:ℝ) ≤ |(j:ℝ)| := by exact_mod_cast (show (1:ℤ) ≤ |j| by omega)
  have h := abs_sub_le (2*p*j) x 0
  rw [sub_zero,sub_zero,abs_sub_comm (2*p*j) x,abs_mul,abs_of_nonneg (mul_nonneg two_pos.le hp)] at h
  linarith only [h,hx,le_mul_of_one_le_right (mul_nonneg two_pos.le hp) hj']

/-- Even if every multiple of 2p may be subtracted independently, the
logarithmic cost of the residual prime exponents loses at most O(n²)
from the original combined height of the reduced numerator and denominator. -/
theorem square_diagonal_finite_place_cost :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ b : ℕ → ℤ,
      let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
      Real.log q.num.natAbs+Real.log q.den-C*(n:ℝ)^2 ≤
        ∑ p ∈ ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1)),
          |(deningerRatExp q p:ℝ)-2*p*(b p:ℝ)| * vonMangoldt p := by
  obtain ⟨D,hD,hd⟩ := diagonal_prime_exponent_profile_error
  refine ⟨2*D,by positivity,?_⟩
  filter_upwards [profile_small_relative_to_prime,eventually_ge_atTop 1] with n hsmall hn
  intro b
  let a := n • successorSquareTriple n
  let q := ordinaryPrimeGenerator a
  let S := ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1))
  let e := fun p : ℕ => (deningerRatExp q p:ℝ)
  let f := diagonalPrimeProfile n
  have hrow (p : ℕ) (hp : p ∈ S) : |e p| ≤ |e p-2*p*(b p:ℝ)|+2*|e p-f p| := by
    have h₁ := abs_sub_le (e p) (f p) 0
    have h₂ := abs_sub_le (f p) (e p) (2*p*(b p:ℝ))
    rw [sub_zero,sub_zero] at h₁
    rw [abs_sub_comm (f p) (e p)] at h₂
    have h₃ := abs_le_even_prime_shift (hsmall (mem_filter.mp hp).2) (b p)
    change |f p| ≤ _ at h₃
    linarith only [h₁,h₂,h₃]
  have hh := sum_le_sum (s := S) fun p hp => mul_le_mul_of_nonneg_right (hrow p hp) (vonMangoldt_nonneg (n := p))
  simp only [add_mul,mul_assoc,sum_add_distrib,← mul_sum] at hh
  change Real.log q.num.natAbs+Real.log q.den-_ ≤ _
  rw [← ordinary_absolute_prime_mass a]
  change (∑ p ∈ S, |e p| * vonMangoldt p)-(2*D)*(n:ℝ)^2 ≤ _
  linarith only [hh,hd hn]

#print axioms ordinary_absolute_prime_mass
#print axioms square_diagonal_finite_place_cost

end GaloisForLFunctions.CountingHolography.Sections
