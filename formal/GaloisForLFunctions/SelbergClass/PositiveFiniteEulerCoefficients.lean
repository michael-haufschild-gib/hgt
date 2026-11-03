import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-!
# Positive coefficients of a reciprocal finite Euler modification

Multiplying `ζ(s)` by `1 + A p⁻ˢ + p p⁻²ˢ` changes only the local
coefficients at the prime `p`. The resulting coefficients are bounded,
positive and multiplicative, and agree with those of zeta below `p`.
-/

noncomputable section
open Complex

namespace GaloisForLFunctions.SelbergClass.PositiveFiniteEuler

/-- The ordinary coefficients of the quadratic local modification. -/
def coeff (p : ℕ) (A : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else 1 + (if p ∣ n then A else 0) +
    (if p ^ 2 ∣ n then (p : ℝ) else 0)

@[simp] theorem coeff_zero (p : ℕ) (A : ℝ) : coeff p A 0 = 0 := rfl

/-- No changed coefficient occurs before the modifying prime. -/
theorem coeff_eq_one_of_lt {p n : ℕ} (hn : n ≠ 0)
    (hnp : n < p) (A : ℝ) : coeff p A n = 1 := by
  have hpd : ¬ p ∣ n := fun h => (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h).not_gt hnp
  have hp2d : ¬ p ^ 2 ∣ n := fun h => hpd (dvd_trans (dvd_pow_self p (by omega)) h)
  simp only [coeff, if_neg hn, if_neg hpd, if_neg hp2d, add_zero]

@[simp] theorem coeff_one {p : ℕ} (hp : p.Prime) (A : ℝ) : coeff p A 1 = 1 :=
  coeff_eq_one_of_lt (by omega) hp.one_lt A

/-- Uniform boundedness gives every Ramanujan power bound. -/
theorem coeff_bounds {p n : ℕ} {A : ℝ} (hA : 0 ≤ A) (hn : n ≠ 0) :
    1 ≤ coeff p A n ∧ coeff p A n ≤ 1 + A + p := by
  simp only [coeff, if_neg hn]
  split_ifs <;> constructor <;> linarith only [hA, Nat.cast_nonneg (α := ℝ) p]

private theorem coeff_mul_of_not_dvd {p m n : ℕ} (hp : p.Prime)
    (hm : m ≠ 0) (hn : n ≠ 0) (hpn : ¬ p ∣ n) (A : ℝ) :
    coeff p A (m * n) = coeff p A m := by
  have hn2 : ¬ p ^ 2 ∣ n := fun h => hpn (dvd_trans (dvd_pow_self p (by omega)) h)
  have hd1 : p ∣ m * n ↔ p ∣ m := by simp only [hp.dvd_mul, hpn, or_false]
  have hd2 : p ^ 2 ∣ m * n ↔ p ^ 2 ∣ m := by
    constructor
    · intro h
      apply hp.prime.pow_dvd_of_dvd_mul_left 2 hpn
      simpa only [mul_comm] using h
    · exact fun h => dvd_mul_of_dvd_left h n
  simp only [coeff, if_neg (mul_ne_zero hm hn), if_neg hm, hd1, hd2]

/-- A coprime product contains the modifying prime in at most one factor. -/
theorem coeff_mul {p m n : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : m.Coprime n) (A : ℝ) : coeff p A (m * n) = coeff p A m * coeff p A n := by
  have hnot : ¬ p ∣ m ∨ ¬ p ∣ n := by
    by_contra h
    push Not at h
    have hd : p ∣ Nat.gcd m n := Nat.dvd_gcd h.1 h.2
    rw [hcop] at hd
    exact hp.not_dvd_one hd
  have hone {k : ℕ} (hk : k ≠ 0) (hpk : ¬ p ∣ k) : coeff p A k = 1 := by
    have hpk2 : ¬ p ^ 2 ∣ k := fun h => hpk (dvd_trans (dvd_pow_self p (by omega)) h)
    simp only [coeff, if_neg hk, if_neg hpk, if_neg hpk2, add_zero]
  rcases hnot with hpm | hpn
  · rw [mul_comm m n, coeff_mul_of_not_dvd hp hn hm hpm, hone hm hpm, one_mul]
  · rw [coeff_mul_of_not_dvd hp hm hn hpn, hone hn hpn, mul_one]

/-- The coefficients packaged as a complex arithmetic function. -/
def arithmeticCoeffs (p : ℕ) (A : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => (coeff p A n : ℂ), by simp only [coeff_zero, Complex.ofReal_zero]⟩

@[simp] theorem arithmeticCoeffs_apply (p n : ℕ) (A : ℝ) :
    arithmeticCoeffs p A n = (coeff p A n : ℂ) := rfl

theorem arithmeticCoeffs_isMultiplicative {p : ℕ} (hp : p.Prime) (A : ℝ) :
    (arithmeticCoeffs p A).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨?_, fun {m n} hm hn hcop => ?_⟩
  · simp only [arithmeticCoeffs_apply, coeff_one hp, Complex.ofReal_one]
  · simp only [arithmeticCoeffs_apply, coeff_mul hp hm hn hcop, Complex.ofReal_mul]

/-- The local Dirichlet polynomial multiplying zeta. -/
def localFactor (p : ℕ) (A : ℝ) (s : ℂ) : ℂ :=
  1 + (A : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) * ((p : ℂ) ^ (-s)) ^ 2

private def singleCoeff (d : ℕ) (b : ℂ) (n : ℕ) : ℂ := if n = d then b else 0

private theorem hasSum_singleCoeff {d : ℕ} (hd : d ≠ 0) (b s : ℂ) :
    LSeriesHasSum (singleCoeff d b) s (b / (d : ℂ) ^ s) := by
  apply (hasSum_ite_eq d (b / (d : ℂ) ^ s)).congr_fun
  intro n
  by_cases hnd : n = d
  · subst n
    simp only [LSeries.term_of_ne_zero hd, singleCoeff, ite_true]
  · by_cases hn : n = 0
    · subst n
      simp only [LSeries.term_zero, if_neg hnd]
    · simp only [LSeries.term_of_ne_zero hn, singleCoeff, if_neg hnd, zero_div]

private def localCoeffs (p : ℕ) (A : ℝ) : ℕ → ℂ :=
  singleCoeff 1 1 + singleCoeff p A + singleCoeff (p ^ 2) p

private theorem hasSum_localCoeffs {p : ℕ} (hp : p ≠ 0) (A : ℝ) (s : ℂ) :
    LSeriesHasSum (localCoeffs p A) s (localFactor p A s) := by
  have h : LSeriesHasSum (localCoeffs p A) s
      (1 / (1 : ℂ) ^ s + (A : ℂ) / (p : ℂ) ^ s +
        (p : ℂ) / ((p ^ 2 : ℕ) : ℂ) ^ s) :=
    LSeriesHasSum.add (LSeriesHasSum.add
      (by simpa only [Nat.cast_one] using hasSum_singleCoeff one_ne_zero 1 s)
      (hasSum_singleCoeff hp A s)) (hasSum_singleCoeff (pow_ne_zero 2 hp) p s)
  have hpow : ((p ^ 2 : ℕ) : ℂ) ^ s = ((p : ℂ) ^ s) ^ 2 := by
    rw [show ((p ^ 2 : ℕ) : ℂ) = (p : ℂ) * p by push_cast; ring, pow_two]
    exact Complex.natCast_mul_natCast_cpow p p s
  simpa only [localFactor, one_cpow, div_one, hpow, cpow_neg, div_eq_mul_inv, inv_pow, inv_one, mul_one] using h

private theorem coeff_eq_convolution (p : ℕ) (A : ℝ) :
    (fun n => (coeff p A n : ℂ)) = LSeries.convolution (localCoeffs p A) 1 := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp only [coeff_zero, Complex.ofReal_zero, LSeries.convolution_map_zero]
  · simp only [LSeries.convolution_def, Pi.one_apply]
    rw [Nat.sum_divisorsAntidiagonal (fun i _ => localCoeffs p A i * (1 : ℂ))]
    simp only [mul_one, localCoeffs, Pi.add_apply, singleCoeff,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Nat.mem_divisors]
    by_cases hpn : p ∣ n <;> by_cases hp2n : p ^ 2 ∣ n <;>
      simp [coeff, hn, hpn, hp2n]


/-- The ordinary Dirichlet series equals the advertised finite modification of zeta. -/
theorem lSeriesHasSum {p : ℕ} (hp : p.Prime) (A : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (arithmeticCoeffs p A) s (localFactor p A s * riemannZeta s) := by
  have hz : LSeriesHasSum (1 : ℕ → ℂ) s (riemannZeta s) := by
    have hzeta := ArithmeticFunction.LSeriesHasSum_zeta hs
    apply hzeta.congr_fun
    intro n
    by_cases hn : n = 0
    · subst n
      simp only [LSeries.term_zero]
    · simp only [LSeries.term_of_ne_zero hn, Pi.one_apply,
        ArithmeticFunction.zeta_apply, if_neg hn, Nat.cast_one]
  change LSeriesHasSum (fun n => (coeff p A n : ℂ)) s _
  rw [coeff_eq_convolution]
  exact (hasSum_localCoeffs hp.ne_zero A s).convolution hz

/-- Every positive power bound holds with the same explicit coefficient constant. -/
theorem ramanujan {p : ℕ} {A : ℝ} (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hn : n ≠ 0) :
    ‖arithmeticCoeffs p A n‖ ≤ (1 + A + p) * (n : ℝ) ^ ε := by
  have hcoeff := coeff_bounds (p := p) hA hn
  rw [arithmeticCoeffs_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (zero_le_one.trans hcoeff.1)]
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  exact hcoeff.2.trans (le_mul_of_one_le_right (by positivity)
    (Real.one_le_rpow hn1 hε.le))

end GaloisForLFunctions.SelbergClass.PositiveFiniteEuler
