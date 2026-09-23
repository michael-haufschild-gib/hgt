import GaloisForLFunctions.RHTower.CoshQuartetEnvelope
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Period classification for polynomially weighted cosh envelopes

Multiplying a displaced cosh quartet envelope by a nonconstant polynomial destroys every nonzero
period.  The proof is divisor-theoretic.  Along the orbit of an envelope zero, a polynomial can
absorb only finitely many translated zeros.  Three consecutive remaining envelope zeros force the
translation back into the exact period lattice `π i ℤ`; cancellation on the real axis then transfers
the period to the polynomial, whose period group is trivial.

The result supplies the aperiodicity component of finite quartet-passport realizations as a positive
classification of the complete period group.
-/

open Complex Polynomial Set

namespace RHTower

noncomputable section

/-- The real part of an envelope zero lies on one of the two displaced lines. -/
theorem coshQuartetEnvelope_zero_re_sq {a : ℝ} {z : ℂ}
    (hz : coshQuartetEnvelope a z = 0) :
    z.re ^ (2 : ℕ) = a ^ (2 : ℕ) := by
  rcases coshQuartetEnvelope_eq_zero_iff.mp hz with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hre := congrArg Complex.re hk
    simp at hre
    rw [hre]
  · have hre := congrArg Complex.re hk
    simp at hre
    rw [hre]
    ring

/-- Three equally spaced envelope zeros force the spacing into the complete envelope period
lattice. -/
theorem coshQuartetEnvelope_three_zeros_quantize_period
    {a : ℝ} (ha : a ≠ 0) {z h : ℂ}
    (hz0 : coshQuartetEnvelope a z = 0)
    (hz1 : coshQuartetEnvelope a (z + h) = 0)
    (hz2 : coshQuartetEnvelope a (z + 2 * h) = 0) :
    ∃ k : ℤ, h = (k : ℂ) * (Real.pi * I) := by
  have hsq0 := coshQuartetEnvelope_zero_re_sq hz0
  have hsq1 := coshQuartetEnvelope_zero_re_sq hz1
  have hsq2 := coshQuartetEnvelope_zero_re_sq hz2
  have hhRe : h.re = 0 := by
    change (z.re + h.re) ^ (2 : ℕ) = a ^ (2 : ℕ) at hsq1
    have htwo : (2 * h).re = 2 * h.re := by norm_num [Complex.mul_re]
    change (z.re + (2 * h).re) ^ (2 : ℕ) = a ^ (2 : ℕ) at hsq2
    rw [htwo] at hsq2
    nlinarith
  rcases coshQuartetEnvelope_eq_zero_iff.mp hz0 with ⟨k0, hk0⟩ | ⟨k0, hk0⟩ <;>
    rcases coshQuartetEnvelope_eq_zero_iff.mp hz1 with ⟨k1, hk1⟩ | ⟨k1, hk1⟩
  · refine ⟨k0 - k1, ?_⟩
    rw [hk0] at hk1
    calc
      h = (a : ℂ) - ((2 * k1 + 1 : ℂ) * Real.pi / 2) * I -
          ((a : ℂ) - ((2 * k0 + 1 : ℂ) * Real.pi / 2) * I) :=
        eq_sub_of_add_eq (by simpa [add_comm] using hk1)
      _ = ((k0 - k1 : ℤ) : ℂ) * (Real.pi * I) := by
        rw [Int.cast_sub]
        ring
  · have hre := congrArg Complex.re hk1
    rw [hk0] at hre
    simp [hhRe] at hre
    exact (ha (by linarith)).elim
  · have hre := congrArg Complex.re hk1
    rw [hk0] at hre
    simp [hhRe] at hre
    exact (ha (by linarith)).elim
  · refine ⟨k0 - k1, ?_⟩
    rw [hk0] at hk1
    calc
      h = (-(a : ℂ) - ((2 * k1 + 1 : ℂ) * Real.pi / 2) * I) -
          (-(a : ℂ) - ((2 * k0 + 1 : ℂ) * Real.pi / 2) * I) :=
        eq_sub_of_add_eq (by simpa [add_comm] using hk1)
      _ = ((k0 - k1 : ℤ) : ℂ) * (Real.pi * I) := by
        rw [Int.cast_sub]
        ring

/-- A nonconstant complex polynomial has only the zero additive period. -/
theorem polynomial_eval_periodic_eq_zero {P : Polynomial ℂ} {h : ℂ}
    (hdegree : 0 < P.degree)
    (hperiod : Function.Periodic P.eval h) :
    h = 0 := by
  obtain ⟨z0, hz0⟩ := Complex.exists_root hdegree
  by_contra hh
  let orbit : ℕ → ℂ := fun n => z0 + (n : ℂ) * h
  have horbit : Function.Injective orbit := by
    intro m n hmn
    apply Nat.cast_injective (R := ℂ)
    apply mul_right_cancel₀ hh
    dsimp [orbit] at hmn
    exact add_left_cancel hmn
  have hzero : ∀ n : ℕ, P.eval (orbit n) = 0 := by
    intro n
    have hn := (hperiod.nsmul n) z0
    simpa [orbit, nsmul_eq_mul, hz0.eq_zero] using hn
  have hinfinite : Set.Infinite {w : ℂ | P.eval w = (0 : Polynomial ℂ).eval w} := by
    apply (Set.infinite_range_of_injective horbit).mono
    rintro w ⟨n, rfl⟩
    simp [hzero]
  have hPzero : P = 0 := Polynomial.eq_of_infinite_eval_eq P 0 hinfinite
  rw [hPzero] at hdegree
  simp at hdegree

/-- A polynomially weighted displaced cosh quartet envelope has only the zero additive period. -/
theorem coshQuartetEnvelope_mul_polynomial_periodic_eq_zero
    (a : ℝ) (ha : a ≠ 0) (P : Polynomial ℂ) (hdegree : 0 < P.degree) {h : ℂ}
    (hperiod : Function.Periodic
      (fun z => coshQuartetEnvelope a z * P.eval z) h) :
    h = 0 := by
  by_contra hh
  let z0 : ℂ := (a : ℂ) - ((1 : ℂ) * Real.pi / 2) * I
  let orbit : ℕ → ℂ := fun n => z0 + (n : ℂ) * h
  have horbit : Function.Injective orbit := by
    intro m n hmn
    apply Nat.cast_injective (R := ℂ)
    apply mul_right_cancel₀ hh
    dsimp [orbit] at hmn
    exact add_left_cancel hmn
  have hPne : P ≠ 0 := by
    intro hzero
    rw [hzero] at hdegree
    simp at hdegree
  have hrootFinite : {w : ℂ | P.eval w = 0}.Finite := by
    by_contra hinf
    have hPzero : P = 0 := Polynomial.eq_of_infinite_eval_eq P 0 (by simpa using hinf)
    exact hPne hPzero
  have hbad : {n : ℕ | P.eval (orbit n) = 0}.Finite := by
    change (orbit ⁻¹' {w : ℂ | P.eval w = 0}).Finite
    exact hrootFinite.preimage horbit.injOn
  obtain ⟨B, hB⟩ := hbad.bddAbove
  let N := B + 1
  have hPgood : ∀ j : ℕ, P.eval (orbit (N + j)) ≠ 0 := by
    intro j hzero
    have hle := hB (show N + j ∈ {n : ℕ | P.eval (orbit n) = 0} from hzero)
    dsimp [N] at hle
    omega
  have hz0 : coshQuartetEnvelope a z0 = 0 := by
    rw [coshQuartetEnvelope_eq_zero_iff]
    left
    exact ⟨0, by simp [z0]⟩
  have hFzero : ∀ n : ℕ,
      coshQuartetEnvelope a (orbit n) * P.eval (orbit n) = 0 := by
    intro n
    have hn := (hperiod.nsmul n) z0
    simpa [orbit, nsmul_eq_mul, hz0] using hn
  have hAzero : ∀ j : ℕ, coshQuartetEnvelope a (orbit (N + j)) = 0 := by
    intro j
    exact (mul_eq_zero.mp (hFzero (N + j))).resolve_right (hPgood j)
  have hquant : ∃ k : ℤ, h = (k : ℂ) * (Real.pi * I) := by
    apply coshQuartetEnvelope_three_zeros_quantize_period ha (z := orbit N)
    · exact hAzero 0
    · have heq : orbit N + h = orbit (N + 1) := by
        simp only [orbit, Nat.cast_add, Nat.cast_one]
        ring
      rw [heq]
      exact hAzero 1
    · have heq : orbit N + 2 * h = orbit (N + 2) := by
        simp only [orbit, Nat.cast_add, Nat.cast_ofNat]
        ring
      rw [heq]
      exact hAzero 2
  have hAperiod : Function.Periodic (coshQuartetEnvelope a) h :=
    (coshQuartetEnvelope_periodic_iff a h).mpr hquant
  have hPperiod : Function.Periodic P.eval h := by
    have hAreal : ∀ x : ℝ, coshQuartetEnvelope a (x : ℂ) ≠ 0 := by
      intro x
      rw [coshQuartetEnvelope,
        ← Complex.ofReal_sub, ← Complex.ofReal_add,
        ← Complex.ofReal_cosh, ← Complex.ofReal_cosh]
      exact mul_ne_zero
        (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.cosh_pos (x - a))))
        (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.cosh_pos (x + a))))
    have hEvalReal : ∀ x : ℝ, P.eval ((x : ℂ) + h) = P.eval (x : ℂ) := by
      intro x
      have hprod := hperiod (x : ℂ)
      change coshQuartetEnvelope a ((x : ℂ) + h) * P.eval ((x : ℂ) + h) =
        coshQuartetEnvelope a (x : ℂ) * P.eval (x : ℂ) at hprod
      rw [hAperiod (x : ℂ)] at hprod
      exact mul_left_cancel₀ (hAreal x) hprod
    let Q : Polynomial ℂ := P.comp (X + C h)
    have hpoly : Q = P := by
      apply Polynomial.eq_of_infinite_eval_eq
      apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
      rintro z ⟨x, rfl⟩
      dsimp [Q]
      rw [eval_comp, eval_add, eval_X, eval_C]
      exact hEvalReal x
    intro z
    have heval := congrArg (Polynomial.eval z) hpoly
    simpa [Q, eval_comp] using heval
  exact hh (polynomial_eval_periodic_eq_zero hdegree hPperiod)

/-- **Complete period classification.** The period group of a polynomially weighted displaced cosh
quartet envelope is the trivial group. -/
theorem coshQuartetEnvelope_mul_polynomial_periodic_iff
    (a : ℝ) (ha : a ≠ 0) (P : Polynomial ℂ) (hdegree : 0 < P.degree) (h : ℂ) :
    Function.Periodic (fun z => coshQuartetEnvelope a z * P.eval z) h ↔ h = 0 := by
  constructor
  · exact coshQuartetEnvelope_mul_polynomial_periodic_eq_zero a ha P hdegree
  · rintro rfl z
    simp

end

end RHTower
