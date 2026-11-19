import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeMidpointInTwoAdjacentGcdHorizons
import GaloisForLFunctions.RHTower.RootOfUnityIntervalCompletion

/-!
# The odd Fourier modes of the sharp prime midpoint

The interval Fourier expansion in El Kaouni (arXiv:2610.42022, §3) can be
made exact on the moving cycle of length `2n`. The two half-intervals have
opposite signs, so even frequencies vanish. On odd frequencies the exact
multiplier is `4/(1-e(h/2n))`. The input is the ordinary-prime logarithm
on the actual integers `2n+1,…,4n`, including the three sharp endpoints.
-/

noncomputable section
open Finset Complex
open GaloisForLFunctions.RHTower.RootOfUnityCompletion
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.MidpointFourier

private def mass (m : ℕ) : ℝ := if m.Prime then Real.log m else 0

/-- A single period of the prime weights, starting immediately after `2n`. -/
def primeWindow (n : ℕ) (j : ZMod (2*n)) : ℂ := (mass (2*n+1+j.val) : ℝ)

/-- Difference of adjacent half-period sums, allowing the starting point to vary. -/
def halfDifference {n : ℕ} (A : ZMod (2*n) → ℂ) (x : ZMod (2*n)) : ℂ :=
  ∑ j ∈ range n, (A (x+j) - A (x+((j+n : ℕ) : ZMod (2*n))))

private theorem prime_mass_segment (a n : ℕ) :
    ∑ p ∈ (Ioc a (a+n)).filter Nat.Prime, Real.log p =
      ∑ j ∈ range n, mass (a+1+j) := by
  rw [sum_filter]
  apply sum_nbij' (fun p => p-(a+1)) (fun j => a+1+j)
  · intro p hp; simp only [mem_Ioc] at hp; simp only [mem_range]; omega
  · intro j hj; simp only [mem_range] at hj; simp only [mem_Ioc]; omega
  · intro p hp; simp only [mem_Ioc] at hp; omega
  · intro j _; omega
  · intro p hp
    simp only [mem_Ioc] at hp
    rw [show a+1+(p-(a+1)) = p by omega]
    rfl

/-- Exact identification of the two half-periods with the original price. -/
theorem price_eq_halfDifference (n : ℕ) :
    (primeMidpointPrice n : ℂ) = halfDifference (primeWindow n) 0 := by
  rw [primeMidpointPrice, show 4*n = 3*n+n by omega,
    prime_mass_segment, show 3*n = 2*n+n by omega, prime_mass_segment]
  push_cast
  rw [halfDifference, sum_sub_distrib]
  congr 1 <;> apply sum_congr rfl <;> intro j hj <;> have hj' := mem_range.mp hj
  · simp only [zero_add, primeWindow, ZMod.val_natCast_of_lt (by omega : j < 2*n)]
  · simp only [zero_add, primeWindow, ZMod.val_natCast_of_lt (by omega : j+n < 2*n)]
    rw [show 2*n+n+1+j = 2*n+1+(j+n) by omega]

variable {n : ℕ} [NeZero n]

private theorem half_turn : ZMod.stdAddChar (n : ZMod (2*n)) = -1 := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [show 2*(Real.pi : ℂ)*I*n/((2*n : ℕ) : ℂ) = Real.pi*I by
    push_cast; field_simp, Complex.exp_pi_mul_I]

private theorem half_turn_power (h : ZMod (2*n)) :
    ZMod.stdAddChar h ^ n = (-1 : ℂ)^h.val := by
  rw [← stdAddChar_mul_natCast_pow, mul_comm, ← half_turn (n := n),
    ← stdAddChar_mul_natCast_pow, ZMod.natCast_zmod_val]

/-- The half-period multiplier vanishes on even modes and has an explicit
Cauchy denominator on every odd mode. -/
theorem half_multiplier (h : ZMod (2*n)) :
    (1-ZMod.stdAddChar h^n)*(∑ j ∈ range n, ZMod.stdAddChar h^j) =
      if Odd h.val then 4/(1-ZMod.stdAddChar h) else 0 := by
  rw [half_turn_power]
  rcases Nat.even_or_odd h.val with he | ho
  · simp [he.neg_one_pow, Nat.not_odd_iff_even.mpr he]
  · rw [if_pos ho, ho.neg_one_pow]
    have hpow := (half_turn_power h).trans (ho.neg_one_pow (α := ℂ))
    have hne : ZMod.stdAddChar h ≠ 1 := by
      intro h1
      rw [h1, one_pow] at hpow
      norm_num at hpow
    apply (eq_div_iff (sub_ne_zero.mpr hne.symm)).mpr
    have hg := geom_sum_mul (ZMod.stdAddChar h) n
    rw [hpow] at hg
    linear_combination -2*hg

/-- Fourier inversion of every translate. The shared mean cancels exactly. -/
theorem halfDifference_spectrum (A : ZMod (2*n) → ℂ) (x : ZMod (2*n)) :
    halfDifference A x = ((2*n : ℕ) : ℂ)⁻¹ *
      ∑ h ∈ univ.filter (fun h : ZMod (2*n) => Odd h.val),
        zmodCoeff A h * ZMod.stdAddChar (h*x) * (4/(1-ZMod.stdAddChar h)) := by
  classical
  have hj (j : ℕ) : A (x+j) - A (x+((j+n : ℕ) : ZMod (2*n))) =
      ((2*n : ℕ) : ℂ)⁻¹ * ∑ h : ZMod (2*n),
        (zmodCoeff A h * ZMod.stdAddChar (h*x) * (1-ZMod.stdAddChar h^n)) *
          ZMod.stdAddChar h^j := by
    rw [fourier_inversion A (x+j), fourier_inversion A (x+((j+n : ℕ) : ZMod (2*n))),
      ← mul_sub, ← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro h _
    simp only [mul_add, AddChar.map_add_eq_mul, stdAddChar_mul_natCast_pow, pow_add]
    ring
  simp only [halfDifference, hj, ← mul_sum]
  congr 1
  rw [sum_comm, sum_filter]
  apply sum_congr rfl
  intro h _
  rw [← mul_sum, mul_assoc (zmodCoeff A h * _), half_multiplier]
  split_ifs <;> simp

/-- The literal sharp prime price only sees odd Fourier modes of the prime logarithm. -/
theorem prime_odd_spectrum :
    (primeMidpointPrice n : ℂ) = ((2*n : ℕ) : ℂ)⁻¹ *
      ∑ h ∈ univ.filter (fun h : ZMod (2*n) => Odd h.val),
        zmodCoeff (primeWindow n) h * (4/(1-ZMod.stdAddChar h)) := by
  simpa only [mul_zero, AddChar.map_zero_eq_one, mul_one] using
    (price_eq_halfDifference n).trans (halfDifference_spectrum (primeWindow n) 0)

/-- Odd Fourier coefficients, weighted by their exact distance from one, give
an upper bound for the absolute sharp midpoint discrepancy. -/
theorem abs_price_le_odd_spectrum :
    |primeMidpointPrice n| ≤ ((2*n : ℕ) : ℝ)⁻¹ *
      ∑ h ∈ univ.filter (fun h : ZMod (2*n) => Odd h.val),
        4 * ‖zmodCoeff (primeWindow n) h‖ / ‖1-ZMod.stdAddChar h‖ := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, prime_odd_spectrum, norm_mul,
    norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (norm_sum_le _ _).trans_eq (sum_congr rfl fun h _ => ?_)
  rw [norm_mul, norm_div]
  norm_num
  ring

private theorem nonzero_window_even {j : ZMod (2*n)} (hj : primeWindow n j ≠ 0) :
    Even j.val := by
  have hp : (2*n+1+j.val).Prime := by
    by_contra hn
    exact hj (by simp [primeWindow, mass, hn])
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  rcases hp.eq_two_or_odd with htwo | hodd
  · omega
  · exact Nat.even_iff.mpr (by have := Nat.odd_iff.mp hodd; omega)

/-- All sampled primes are odd. On their support the half-period
modulation is one, so the prime spectrum repeats after `n` frequencies. -/
theorem prime_spectrum_half_period (h : ZMod (2*n)) :
    zmodCoeff (primeWindow n) (h+n) = zmodCoeff (primeWindow n) h := by
  unfold zmodCoeff
  apply sum_congr rfl
  intro j _
  by_cases hj : primeWindow n j = 0
  · simp only [hj, zero_mul]
  obtain ⟨k,hk⟩ := nonzero_window_even hj
  have hzero : (n : ZMod (2*n))*j = 0 := by
    calc (n : ZMod (2*n))*j = ((n*j.val : ℕ) : ZMod (2*n)) := by simp
         _ = (((2*n)*k : ℕ) : ZMod (2*n)) := by rw [hk]; push_cast; ring
         _ = 0 := by rw [Nat.cast_mul, ZMod.natCast_self, zero_mul]
  rw [add_mul, hzero, add_zero]

/-- The Nyquist coefficient equals the whole prime mass, without oscillation. -/
theorem nyquist_prime_mass :
    zmodCoeff (primeWindow n) n =
      ((∑ p ∈ (Ioc (2*n) (4*n)).filter Nat.Prime, Real.log p : ℝ) : ℂ) := by
  rw [← zero_add (n : ZMod (2*n)), prime_spectrum_half_period]
  simp only [zmodCoeff, zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]
  rw [show 4*n = 2*n+2*n by omega, prime_mass_segment]
  push_cast
  apply sum_nbij' ZMod.val (fun k : ℕ => (k : ZMod (2*n)))
  · intro j _; exact mem_range.mpr j.val_lt
  · intro _ _; exact mem_univ _
  · intro j _; exact ZMod.natCast_zmod_val j
  · intro k hk; exact ZMod.val_natCast_of_lt (mem_range.mp hk)
  · intro _ _; rfl

/-- At odd centers the Nyquist contribution is a positive, explicit prime
mass. Every remaining contribution comes from a non-Nyquist odd mode. -/
theorem odd_center_price (hn : Odd n) :
    (primeMidpointPrice n : ℂ) =
      ((∑ p ∈ (Ioc (2*n) (4*n)).filter Nat.Prime, Real.log p : ℝ) : ℂ)/(n : ℂ) +
      ((2*n : ℕ) : ℂ)⁻¹ * ∑ h ∈ (univ.filter (fun h : ZMod (2*n) => Odd h.val)).erase n,
        zmodCoeff (primeWindow n) h * (4/(1-ZMod.stdAddChar h)) := by
  classical
  have hn0 := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmem : (n : ZMod (2*n)) ∈ univ.filter (fun h : ZMod (2*n) => Odd h.val) :=
    mem_filter.mpr ⟨mem_univ _, (ZMod.val_natCast_of_lt (by omega : n < 2*n)).symm ▸ hn⟩
  rw [prime_odd_spectrum, ← add_sum_erase _ _ hmem, mul_add, nyquist_prime_mass, half_turn]
  congr 1
  push_cast
  ring

private def halfSum (A : ZMod (2*n) → ℂ) (x : ZMod (2*n)) : ℂ :=
  ∑ j ∈ range n, A (x+j)

private theorem halfDifference_eq (A : ZMod (2*n) → ℂ) (x : ZMod (2*n)) :
    halfDifference A x = halfSum A x - halfSum A (x+n) := by
  rw [halfDifference, sum_sub_distrib, halfSum, halfSum]
  congr 1
  exact sum_congr rfl fun j _ => congrArg A (by push_cast; ring)

private theorem two_shifts (x : ZMod (2*n)) : x+n+n = x := by
  rw [add_assoc, ← Nat.cast_add, ← two_mul, ZMod.natCast_self, add_zero]

/-- Translation by half a period reverses the signed midpoint price. -/
theorem halfDifference_shift (A : ZMod (2*n) → ℂ) (x : ZMod (2*n)) :
    halfDifference A (x+n) = -halfDifference A x := by
  rw [halfDifference_eq, halfDifference_eq, two_shifts]
  ring

private theorem halfSum_step (A : ZMod (2*n) → ℂ) (x : ZMod (2*n)) :
    halfSum A (x+1) + A x = halfSum A x + A (x+n) := by
  have he := (sum_range_succ' (fun j : ℕ => A (x+j)) n).symm.trans
    (sum_range_succ (fun j : ℕ => A (x+j)) n)
  simpa only [halfSum, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero,
    add_right_comm x 1, add_assoc] using he

/-- One discrete derivative reads the difference between opposite entries.
Only the two moving endpoints survive. -/
theorem halfDifference_step (A : ZMod (2*n) → ℂ) (x : ZMod (2*n)) :
    halfDifference A (x+1) - halfDifference A x = 2*(A (x+n)-A x) := by
  rw [halfDifference_eq, halfDifference_eq, add_right_comm x 1 (n : ZMod (2*n))]
  have hs := halfSum_step A (x+n)
  rw [two_shifts] at hs
  linear_combination halfSum_step A x - hs

/-- The invisible inputs are exactly the half-periodic ones. -/
theorem all_halfDifferences_zero_iff (A : ZMod (2*n) → ℂ) :
    (∀ x, halfDifference A x = 0) ↔ ∀ x, A (x+n) = A x := by
  constructor
  · intro h x
    have he := halfDifference_step A x
    rw [h, h, sub_self] at he
    linear_combination -he/2
  · intro h x
    apply sum_eq_zero
    intro j _
    rw [Nat.cast_add, ← add_assoc, h, sub_self]

/-- At an odd center the two opposite samples have different parity.
Consequently the translated midpoint prices recover each ordinary-prime
weight individually from two consecutive measurements. -/
theorem recover_odd_center_prime_window (hn : Odd n) (x : ZMod (2*n)) :
    primeWindow n x = if Even x.val then
      (halfDifference (primeWindow n) x-halfDifference (primeWindow n) (x+1))/2 else 0 := by
  by_cases hx : Even x.val
  · rw [if_pos hx]
    have hn0 := Nat.pos_of_ne_zero (NeZero.ne n)
    have hxo : ¬Even (x+n).val := by
      rw [Nat.even_iff, ZMod.val_add, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 n),
        ZMod.val_natCast_of_lt (by omega : n < 2*n)]
      have h1 := Nat.even_iff.mp hx
      have h2 := Nat.odd_iff.mp hn
      omega
    have hw : primeWindow n (x+n) = 0 := not_ne_iff.mp (fun h => hxo (nonzero_window_even h))
    have he := halfDifference_step (primeWindow n) x
    rw [hw, zero_sub] at he
    linear_combination he/2
  · rw [if_neg hx]
    exact not_ne_iff.mp (fun h => hx (nonzero_window_even h))

#print axioms price_eq_halfDifference
#print axioms half_multiplier
#print axioms halfDifference_spectrum
#print axioms prime_odd_spectrum
#print axioms abs_price_le_odd_spectrum
#print axioms prime_spectrum_half_period
#print axioms nyquist_prime_mass
#print axioms odd_center_price
#print axioms halfDifference_shift
#print axioms halfDifference_step
#print axioms all_halfDifferences_zero_iff
#print axioms recover_odd_center_prime_window
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.MidpointFourier
