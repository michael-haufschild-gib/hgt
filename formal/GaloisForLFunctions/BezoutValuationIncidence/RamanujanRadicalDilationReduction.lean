import GaloisForLFunctions.BezoutValuationIncidence.DilationJumpValuationClock
import GaloisForLFunctions.BezoutValuationIncidence.TranslatedWindowStrideAnnihilationAndLcmReturnObservability

/-!
# Exact radical reduction of Ramanujan dilation profiles

The existing valuation-clock support and totient-quotient formula identify
all natural coefficients with the clock-dilated squarefree radical sequence.
Summing the existing jump stream transports this identity to primitives;
the original integer-cell Gram then transports it to every positive rational
dilation profile. If `s = primeRadical r` and `v = lagVisibilityClock r`, then
`Phi_r(p/q) = v * Phi_s(p/q)`. The last theorem has data parameters only.

This is an exact identity for the original carrier. It does not assert lag
composition or positivity of any signed sector, and it does not discard a
finite-cutoff correction when individual physical sectors are rescaled.
-/

open Finset RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section

private theorem radical_pos (r : ℕ) : 0 < primeRadical r :=
  prod_pos fun _ hp => (Nat.mem_primeFactors.mp hp).1.pos

private theorem radical_primeFactors (r : ℕ) :
    (primeRadical r).primeFactors = r.primeFactors := by
  by_cases hr : r = 0
  · simp [hr, primeRadical]
  · ext p
    constructor
    · intro hp
      obtain ⟨hpP, hpd, _⟩ := Nat.mem_primeFactors.mp hp
      exact Nat.mem_primeFactors.mpr
        ⟨hpP, hpd.trans (Nat.prod_primeFactors_dvd r), hr⟩
    · intro hp
      exact Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hp).1,
          dvd_prod_of_mem (fun x : ℕ => x) hp, (radical_pos r).ne'⟩

private theorem radical_mul_clock (r : ℕ) :
    primeRadical r * lagVisibilityClock r = r :=
  Nat.mul_div_cancel' (Nat.prod_primeFactors_dvd r)

private theorem clock_pos {r : ℕ} (hr : r ≠ 0) : 0 < lagVisibilityClock r :=
  Nat.pos_of_ne_zero fun hz => hr ((lagVisibilityClock_eq_zero_iff r).mp hz)

private theorem radical_one_lt {r : ℕ} (hr : 1 < r) : 1 < primeRadical r := by
  obtain ⟨p, hp, hpr⟩ := Nat.exists_prime_and_dvd (show r ≠ 1 by omega)
  have hmem : p ∈ r.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpr, by omega⟩
  have hdvd : p ∣ primeRadical r := dvd_prod_of_mem (fun x : ℕ => x) hmem
  have hle := Nat.le_of_dvd (radical_pos r) hdvd
  have := hp.two_le
  omega

private theorem totient_eq_clock_mul_radical_totient (r : ℕ) :
    r.totient = lagVisibilityClock r * (primeRadical r).totient := by
  have hs : (primeRadical r).totient = ∏ p ∈ r.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul, radical_primeFactors]
    change (primeRadical r / primeRadical r) * _ = _
    rw [Nat.div_self (radical_pos r), one_mul]
  rw [Nat.totient_eq_div_primeFactors_mul, hs]
  rfl

/-- The existing quotient formula rescales exactly on the visibility clock. -/
theorem ramanujanLagCoefficient_clock_mul (r n : ℕ) :
    ramanujanLagCoefficient r (lagVisibilityClock r * n) =
      (lagVisibilityClock r : ℝ) * ramanujanLagCoefficient (primeRadical r) n := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [ramanujanLagCoefficient, lagVisibilityClock]
  · let v := lagVisibilityClock r
    let s := primeRadical r
    have hv : 0 < v := clock_pos hr.ne'
    have hR : r = v * s := by
      simpa only [Nat.mul_comm] using (radical_mul_clock r).symm
    have hg : Nat.gcd r (v * n) = v * Nat.gcd s n := by
      calc
        _ = Nat.gcd (v * s) (v * n) := congrArg (fun x => Nat.gcd x (v * n)) hR
        _ = _ := Nat.gcd_mul_left v s n
    have hquot : r / Nat.gcd r (v * n) = s / Nat.gcd s n := by
      calc
        _ = (v * s) / (v * Nat.gcd s n) := congrArg₂ (fun x y : ℕ => x / y) hR hg
        _ = _ := Nat.mul_div_mul_left _ _ hv
    have hφ : (r.totient : ℝ) = (v : ℝ) * (s.totient : ℝ) := by
      exact_mod_cast totient_eq_clock_mul_radical_totient r
    change ramanujanLagCoefficient r (v * n) = (v : ℝ) * ramanujanLagCoefficient s n
    simp only [ramanujanLagCoefficient_eq_totient_mul,
      sieveLagMultiplier_eq_moebius_totient_quotient, hquot, hφ]
    ring

/-- Literal natural jump coefficients reduce to the squarefree core on their clock. -/
theorem ramanujanNaturalCoefficient_re_clock_mul (r n : ℕ) :
    (d4BMRamanujanNaturalCoefficient (lagVisibilityClock r * n) r).re =
      (lagVisibilityClock r : ℝ) *
        (d4BMRamanujanNaturalCoefficient n (primeRadical r)).re := by
  simp only [ramanujanNaturalCoefficient_re_eq_lagCoefficient]
  exact ramanujanLagCoefficient_clock_mul r n

/-- The complete coefficient sequence is the clock-dilated radical jump stream. -/
theorem ramanujanNaturalCoefficient_re_eq_clock_mul_jump (r n : ℕ) :
    (d4BMRamanujanNaturalCoefficient n r).re =
      (lagVisibilityClock r : ℝ) * ramanujanDilationJump (primeRadical r) (lagVisibilityClock r) n := by
  by_cases hn : lagVisibilityClock r ∣ n
  · rw [ramanujanDilationJump, if_pos hn]
    have he := ramanujanNaturalCoefficient_re_clock_mul r (n / lagVisibilityClock r)
    simpa only [Nat.mul_div_cancel' hn] using he
  · have hz : (d4BMRamanujanNaturalCoefficient n r).re = 0 := by
      by_contra h
      exact hn ((ramanujanNaturalCoefficient_re_ne_zero_iff_clock r n).mp h).2
    simp only [ramanujanDilationJump, if_neg hn, hz, mul_zero]

/-- Summation of the existing dilation jump stream gives exact primitive rescaling. -/
theorem pmRamanujanPrimitive_re_eq_clock_mul_radical (r N : ℕ) :
    (pmRamanujanPrimitive r N).re =
      (lagVisibilityClock r : ℝ) *
        (pmRamanujanPrimitive (primeRadical r) (N / lagVisibilityClock r)).re := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [pmRamanujanPrimitive, d4BMRamanujanNaturalCoefficient, lagVisibilityClock]
  · calc
      _ = ∑ n ∈ Icc 1 N, (d4BMRamanujanNaturalCoefficient n r).re := by
        simp only [pmRamanujanPrimitive, Complex.re_sum]
      _ = (lagVisibilityClock r : ℝ) *
          ∑ n ∈ Icc 1 N, ramanujanDilationJump (primeRadical r) (lagVisibilityClock r) n := by
        simp only [ramanujanNaturalCoefficient_re_eq_clock_mul_jump, mul_sum]
      _ = _ := by rw [sum_ramanujanDilationJump (clock_pos hr.ne')]

/-- The original integer-cell Gram retains the exact clock in both dilation scales. -/
theorem ramanujanIntegerDilationGram_eq_clock_sq_mul_radical (r p q : ℕ) :
    ramanujanIntegerDilationGram r p q =
      (lagVisibilityClock r : ℝ) ^ 2 *
        ramanujanIntegerDilationGram (primeRadical r)
          (lagVisibilityClock r * p) (lagVisibilityClock r * q) := by
  simp only [ramanujanIntegerDilationGram, pmRamanujanPrimitive_re_eq_clock_mul_radical r,
    Nat.div_div_eq_div_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [Nat.mul_comm p (lagVisibilityClock r), Nat.mul_comm q (lagVisibilityClock r)]
  ring

/-- Rational dilation profiles reduce exactly to the existing squarefree radical. -/
theorem pmRamanujanDilationProfile_eq_clock_mul_radical {r p q : ℕ}
    (hr : 1 < r) (hp : 0 < p) (hq : 0 < q) :
    pmRamanujanDilationProfile r hr ((p : ℝ) / q) =
      (lagVisibilityClock r : ℝ) *
        pmRamanujanDilationProfile (primeRadical r) (radical_one_lt hr) ((p : ℝ) / q) := by
  let v := lagVisibilityClock r
  have hv : 0 < v := clock_pos (by omega)
  have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hratio : (((v * p : ℕ) : ℝ) / (v * q : ℕ)) = (p : ℝ) / q := by
    push_cast
    field_simp [hv0]
  have hroot : Real.sqrt ((v * p : ℕ) : ℝ) * Real.sqrt ((v * q : ℕ) : ℝ) =
      (v : ℝ) * Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) := by
    simp only [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg v)]
    calc
      _ = (Real.sqrt (v : ℝ)) ^ 2 * (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg v)]; ring
  have hs := pmRamanujanDilationProfile_eq_integerDilationGram
    (radical_one_lt hr) (Nat.mul_pos hv hp) (Nat.mul_pos hv hq)
  rw [hratio, hroot] at hs
  rw [pmRamanujanDilationProfile_eq_integerDilationGram hr hp hq,
    ramanujanIntegerDilationGram_eq_clock_sq_mul_radical, hs]
  change Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
      ((v : ℝ) ^ 2 * ramanujanIntegerDilationGram (primeRadical r) (v * p) (v * q)) = _
  ring

/-- Unconditional radical reduction at every positive rational dilation. -/
theorem dilation_profile_radical_reduction (r p q : ℕ) :
    pmRamanujanDilationProfile (r + 2) (by omega) (((p + 1 : ℕ) : ℝ) / (q + 1 : ℕ)) =
      (lagVisibilityClock (r + 2) : ℝ) *
        pmRamanujanDilationProfile (primeRadical (r + 2)) (radical_one_lt (by omega))
          (((p + 1 : ℕ) : ℝ) / (q + 1 : ℕ)) :=
  pmRamanujanDilationProfile_eq_clock_mul_radical (by omega) (by omega) (by omega)

end
end GaloisForLFunctions.BezoutValuationIncidence
