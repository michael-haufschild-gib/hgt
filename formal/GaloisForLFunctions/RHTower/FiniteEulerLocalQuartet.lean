import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Exponential
import GaloisForLFunctions.HTGeometry.KroneckerFlow
import GaloisForLFunctions.RHTower.PrimeCpowAbsoluteAbscissa

/-!
# Finite Euler local quartets

The finite Euler factor `1 - p⁻ˢ` is paired with its functional-equation
reflection.  The resulting local quartet is reflection-invariant and is a
strictly positive real number on the critical line.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Complex

/-- The entire finite Euler factor written in exponential coordinates. -/
def finiteEulerLocalFactor (p : ℕ) (s : ℂ) : ℂ :=
  1 - Complex.exp (-s * Real.log p)

/-- The functional-equation-symmetric local Euler quartet. -/
def finiteEulerLocalQuartet (p : ℕ) (s : ℂ) : ℂ :=
  finiteEulerLocalFactor p s * finiteEulerLocalFactor p (1 - s)

/-- Finite Euler local factors commute with complex conjugation. -/
theorem finiteEulerLocalFactor_conj (p : ℕ) (s : ℂ) :
    finiteEulerLocalFactor p (star s) = star (finiteEulerLocalFactor p s) := by
  unfold finiteEulerLocalFactor
  have hreal (x : ℝ) : star (x : ℂ) = (x : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have harg : -star s * (Real.log p : ℂ) =
      starRingEnd ℂ (-s * (Real.log p : ℂ)) := by
    calc
      -star s * (Real.log p : ℂ) = starRingEnd ℂ (-s) *
          starRingEnd ℂ (Real.log p : ℂ) := by
            change -star s * (Real.log p : ℂ) = star (-s) * star (Real.log p : ℂ)
            rw [star_neg, hreal]
      _ = starRingEnd ℂ (-s * (Real.log p : ℂ)) :=
        (map_mul (starRingEnd ℂ) (-s) (Real.log p : ℂ)).symm
  rw [harg, Complex.exp_conj]
  change 1 - star (Complex.exp (-s * (Real.log p : ℂ))) =
    star (1 - Complex.exp (-s * (Real.log p : ℂ)))
  simpa only [star_one] using
    (star_sub (1 : ℂ) (Complex.exp (-s * (Real.log p : ℂ)))).symm

/-- Exponential coordinates agree with the standard complex-power Euler factor. -/
theorem finiteEulerLocalFactor_eq_one_sub_natCast_cpow (p : Nat.Primes) (s : ℂ) :
    finiteEulerLocalFactor p s = 1 - ((p : ℕ) : ℂ) ^ (-s) := by
  unfold finiteEulerLocalFactor
  rw [Complex.cpow_def_of_ne_zero]
  · rw [← Complex.natCast_log]
    congr 2
    ring_nf
  · exact Nat.cast_ne_zero.mpr p.property.ne_zero

/-- Finite Euler factor perturbations have the sharp prime absolute-abscissa boundary. -/
theorem summable_norm_finiteEulerLocalFactor_sub_one_iff (s : ℂ) :
    Summable (fun p : Nat.Primes => ‖finiteEulerLocalFactor p s - 1‖) ↔ 1 < s.re := by
  have hnorm : (fun p : Nat.Primes => ‖finiteEulerLocalFactor p s - 1‖) =
      fun p : Nat.Primes => ‖((p : ℕ) : ℂ) ^ (-s)‖ := by
    funext p
    rw [finiteEulerLocalFactor_eq_one_sub_natCast_cpow]
    ring_nf
    exact norm_neg _
  rw [hnorm, summable_norm_primeCpow_neg_iff]

/-- A local Euler quartet is invariant under `s ↦ 1 - s`. -/
theorem finiteEulerLocalQuartet_reflection (p : ℕ) (s : ℂ) :
    finiteEulerLocalQuartet p (1 - s) = finiteEulerLocalQuartet p s := by
  unfold finiteEulerLocalQuartet
  ring_nf

/-- The exact imaginary part of a finite Euler quartet at `σ + it`. -/
theorem finiteEulerLocalQuartet_im (p : Nat.Primes) (sigma t : ℝ) :
    (finiteEulerLocalQuartet p ((sigma : ℂ) + (t : ℂ) * Complex.I)).im =
      (Real.exp (-sigma * Real.log p) - Real.exp ((sigma - 1) * Real.log p)) *
        Real.sin (t * Real.log p) := by
  have hfirst : Complex.exp (-((sigma : ℂ) + (t : ℂ) * Complex.I) * Real.log p) =
      (Real.exp (-sigma * Real.log p) : ℂ) *
        ((Real.cos (t * Real.log p) : ℂ) - (Real.sin (t * Real.log p) : ℂ) * Complex.I) := by
    rw [show -((sigma : ℂ) + (t : ℂ) * Complex.I) * Real.log p =
        ((-sigma * Real.log p : ℝ) : ℂ) +
          ((-(t * Real.log p) : ℝ) : ℂ) * Complex.I by
        push_cast
        ring,
      Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_ofReal_mul_I,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hsecond : Complex.exp (-(1 - ((sigma : ℂ) + (t : ℂ) * Complex.I)) * Real.log p) =
      (Real.exp ((sigma - 1) * Real.log p) : ℂ) *
        ((Real.cos (t * Real.log p) : ℂ) + (Real.sin (t * Real.log p) : ℂ) * Complex.I) := by
    rw [show -(1 - ((sigma : ℂ) + (t : ℂ) * Complex.I)) * Real.log p =
        (((sigma - 1) * Real.log p : ℝ) : ℂ) +
          ((t * Real.log p : ℝ) : ℂ) * Complex.I by
        push_cast
        ring,
      Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_ofReal_mul_I]
  unfold finiteEulerLocalQuartet finiteEulerLocalFactor
  rw [hfirst, hsecond]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, zero_mul, zero_sub]
  ring

/-- A real local Euler quartet is either on the critical line or at a resonant prime-log phase. -/
theorem finiteEulerLocalQuartet_im_eq_zero_iff (p : Nat.Primes) (sigma t : ℝ) :
    (finiteEulerLocalQuartet p ((sigma : ℂ) + (t : ℂ) * Complex.I)).im = 0 ↔
      sigma = 1 / 2 ∨ Real.sin (t * Real.log p) = 0 := by
  rw [finiteEulerLocalQuartet_im]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hfactor | hsin
    · left
      have harg : -sigma * Real.log p = (sigma - 1) * Real.log p :=
        Real.exp_injective (sub_eq_zero.mp hfactor)
      have hlog : 0 < Real.log (p : ℝ) :=
        Real.log_pos (by
          simpa using (Nat.cast_lt (α := ℝ)).mpr p.property.one_lt)
      have hmul : (2 * sigma - 1) * Real.log p = 0 := by
        calc
          (2 * sigma - 1) * Real.log p =
              -((-sigma * Real.log p) - (sigma - 1) * Real.log p) := by ring
          _ = 0 := by rw [harg]; ring
      have hlinear : 2 * sigma - 1 = 0 :=
        (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hlog)
      linarith
    · exact Or.inr hsin
  · rintro (hsigma | hsin)
    · rw [hsigma]
      ring_nf
    · rw [hsin, mul_zero]

/-- At nonzero height, simultaneous reality of quartets at two distinct primes
forces the critical line. -/
theorem finiteEulerLocalQuartet_two_prime_real_iff_criticalLine
    (p q : Nat.Primes) (hpq : p ≠ q) (sigma t : ℝ) (ht : t ≠ 0) :
    ((finiteEulerLocalQuartet p ((sigma : ℂ) + (t : ℂ) * Complex.I)).im = 0 ∧
      (finiteEulerLocalQuartet q ((sigma : ℂ) + (t : ℂ) * Complex.I)).im = 0) ↔
      sigma = 1 / 2 := by
  constructor
  · rintro ⟨hpim, hqim⟩
    rcases (finiteEulerLocalQuartet_im_eq_zero_iff p sigma t).mp hpim with hline | hpzero
    · exact hline
    rcases (finiteEulerLocalQuartet_im_eq_zero_iff q sigma t).mp hqim with hline | hqzero
    · exact hline
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hpzero
    obtain ⟨l, hl⟩ := Real.sin_eq_zero_iff.mp hqzero
    have hp_log_pos : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by
        simpa using (Nat.cast_lt (α := ℝ)).mpr p.property.one_lt)
    have hk_ne : k ≠ 0 := by
      intro hkzero
      have hzero : t * Real.log (p : ℝ) = 0 := by
        rw [← hk, hkzero]
        simp
      exact (mul_ne_zero ht (ne_of_gt hp_log_pos)) hzero
    let m : Nat.Primes →₀ ℤ := Finsupp.single p l + Finsupp.single q (-k)
    have hcross : (l : ℝ) * (t * Real.log (p : ℝ)) =
        (k : ℝ) * (t * Real.log (q : ℝ)) := by
      rw [← hk, ← hl]
      ring
    have hrelation : (l : ℝ) * Real.log (p : ℝ) +
        (-k : ℝ) * Real.log (q : ℝ) = 0 := by
      apply (mul_left_cancel₀ ht)
      rw [mul_zero]
      calc
        t * ((l : ℝ) * Real.log (p : ℝ) + (-k : ℝ) * Real.log (q : ℝ)) =
            (l : ℝ) * (t * Real.log (p : ℝ)) -
              (k : ℝ) * (t * Real.log (q : ℝ)) := by ring
        _ = 0 := sub_eq_zero.mpr hcross
    have hfrequency : GaloisForLFunctions.primeLogFrequency m = 0 := by
      unfold GaloisForLFunctions.primeLogFrequency
      dsimp [m]
      rw [Finsupp.sum_add_index]
      · rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
        simpa using hrelation
      · intro a ha
        simp
      · intro a ha b₁ b₂
        push_cast
        ring
    have hmzero : m = 0 :=
      (GaloisForLFunctions.primeLogFrequency_eq_zero_iff m).mp hfrequency
    have hkzero : k = 0 := by
      have hvalue := congrArg (fun f : Nat.Primes →₀ ℤ => f q) hmzero
      simpa [m, hpq] using hvalue
    exact (hk_ne hkzero).elim
  · intro hline
    subst sigma
    constructor <;> apply (finiteEulerLocalQuartet_im_eq_zero_iff _ _ _).mpr
    · exact Or.inl rfl
    · exact Or.inl rfl

/-- A prime Euler factor does not vanish on the critical line. -/
theorem finiteEulerLocalFactor_criticalLine_ne_zero (p : Nat.Primes) (t : ℝ) :
    finiteEulerLocalFactor p (1 / 2 + (t : ℂ) * Complex.I) ≠ 0 := by
  intro hzero
  have hfactor : Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p) = 1 := by
    simpa [finiteEulerLocalFactor] using (sub_eq_zero.mp hzero).symm
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by
      simpa using (Nat.cast_lt (α := ℝ)).mpr p.property.one_lt)
  set ell : ℝ := Real.log (p : ℝ)
  have hell : 0 < ell := hlog
  have hre : (-(1 / 2 + (t : ℂ) * Complex.I) * (ell : ℂ)).re =
      -(1 / 2 : ℝ) * ell := by
    simp [Complex.mul_re]
  have hlt : ‖Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)‖ < 1 := by
    change ‖Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * (ell : ℂ))‖ < 1
    rw [Complex.norm_exp, hre, Real.exp_lt_one_iff]
    nlinarith
  rw [hfactor, norm_one] at hlt
  exact lt_irrefl _ hlt

/-- On the critical line, a prime Euler quartet is the squared modulus of one local factor. -/
theorem finiteEulerLocalQuartet_criticalLine_eq_norm_sq (p : Nat.Primes) (t : ℝ) :
    finiteEulerLocalQuartet p (1 / 2 + (t : ℂ) * Complex.I) =
      (‖finiteEulerLocalFactor p (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2 : ℝ) := by
  rw [finiteEulerLocalQuartet]
  have hline : (1 - (1 / 2 + (t : ℂ) * Complex.I) : ℂ) =
      star (1 / 2 + (t : ℂ) * Complex.I) := by
    simp
    ring_nf
  rw [hline]
  change (1 - Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)) *
      (1 - Complex.exp (-(star (1 / 2 + (t : ℂ) * Complex.I)) * Real.log p)) =
      (‖1 - Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)‖ ^ 2 : ℝ)
  rw [show (1 - Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)) *
      (1 - Complex.exp (-(star (1 / 2 + (t : ℂ) * Complex.I)) * Real.log p)) =
      (1 - Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)) *
        star (1 - Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)) by
          rw [← finiteEulerLocalFactor]
          rw [finiteEulerLocalFactor]
          exact congrArg (fun z =>
            (1 - Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)) * z)
            (finiteEulerLocalFactor_conj p (1 / 2 + (t : ℂ) * Complex.I))]
  change (1 - Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)) *
      starRingEnd ℂ (1 - Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)) = _
  rw [Complex.mul_conj]
  rw [← Complex.sq_norm]

/-- The critical-line local Euler quartet has strictly positive real part. -/
theorem finiteEulerLocalQuartet_criticalLine_re_pos (p : Nat.Primes) (t : ℝ) :
    0 < (finiteEulerLocalQuartet p (1 / 2 + (t : ℂ) * Complex.I)).re := by
  rw [finiteEulerLocalQuartet_criticalLine_eq_norm_sq]
  simp only [ofReal_re]
  exact sq_pos_of_pos
    (norm_pos_iff.mpr (finiteEulerLocalFactor_criticalLine_ne_zero p t))

/-- At nonzero height, two distinct local quartets are both strictly positive
real numbers exactly on the critical line. -/
theorem finiteEulerLocalQuartet_two_prime_positive_real_iff_criticalLine
    (p q : Nat.Primes) (hpq : p ≠ q) (sigma t : ℝ) (ht : t ≠ 0) :
    (((finiteEulerLocalQuartet p ((sigma : ℂ) + (t : ℂ) * Complex.I)).im = 0 ∧
        0 < (finiteEulerLocalQuartet p ((sigma : ℂ) + (t : ℂ) * Complex.I)).re) ∧
      ((finiteEulerLocalQuartet q ((sigma : ℂ) + (t : ℂ) * Complex.I)).im = 0 ∧
        0 < (finiteEulerLocalQuartet q ((sigma : ℂ) + (t : ℂ) * Complex.I)).re)) ↔
      sigma = 1 / 2 := by
  constructor
  · rintro ⟨⟨hpim, _⟩, ⟨hqim, _⟩⟩
    exact (finiteEulerLocalQuartet_two_prime_real_iff_criticalLine p q hpq sigma t ht).mp
      ⟨hpim, hqim⟩
  · intro hline
    subst sigma
    constructor
    · refine ⟨?_, ?_⟩
      exact (finiteEulerLocalQuartet_im_eq_zero_iff p (1 / 2) t).mpr (Or.inl rfl)
      convert finiteEulerLocalQuartet_criticalLine_re_pos p t using 1
      norm_num
    · refine ⟨?_, ?_⟩
      exact (finiteEulerLocalQuartet_im_eq_zero_iff q (1 / 2) t).mpr (Or.inl rfl)
      convert finiteEulerLocalQuartet_criticalLine_re_pos q t using 1
      norm_num

end GaloisForLFunctions.RHTower

end
