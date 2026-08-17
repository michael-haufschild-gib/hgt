import GaloisForLFunctions.RHTower.CoshPolynomialPeriodClassification

/-!
# The cosh quartet envelope has no nonzero quasi-period

`CoshPolynomialPeriodClassification` proves that the period group of `A · P` — the displaced cosh
quartet envelope times a nonconstant polynomial — is trivial.  The full-germ separation step of the
quartet-passport realization needs the *multiplicative* strengthening: a displacement `h` cannot be
absorbed even up to a nonzero constant factor,

`A(z+h) P(z+h) = C · A(z) P(z)` for all `z`, `C ≠ 0`  ⟹  `h = 0`.

The zero-orbit argument is unchanged — a quasi-period still maps zeros to zeros, because
`C ≠ 0` — so `h` is forced into the envelope's period lattice `πiℤ` exactly as before.  Cancelling
the envelope leaves `P(z+h) = C P(z)`, and comparing **leading coefficients** of
`P ∘ (X + h) = C · P` gives `C = 1`, which returns the additive case.
-/

noncomputable section

open Complex Polynomial

namespace RHTower



/-- **A nonconstant complex polynomial has no nonzero quasi-period.**  If
`P(z + h) = C · P(z)` identically with `C ≠ 0` and `deg P > 0`, then `C = 1` and `h = 0`. -/
theorem polynomial_eval_quasiPeriodic_eq_zero {P : Polynomial ℂ} {h C : ℂ}
    (hdegree : 0 < P.degree) (hC : C ≠ 0)
    (hq : ∀ z, P.eval (z + h) = C * P.eval z) :
    C = 1 ∧ h = 0 := by
  have hPne : P ≠ 0 := fun hzero => by rw [hzero] at hdegree; simp at hdegree
  -- the polynomial identity
  have hpoly : P.comp (X + Polynomial.C h) = Polynomial.C C * P := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine (Set.infinite_range_of_injective Complex.ofReal_injective).mono ?_
    rintro z ⟨x, rfl⟩
    simp only [Set.mem_setOf_eq, eval_comp, eval_add, eval_X, eval_C, eval_mul]
    exact hq (x : ℂ)
  have hnat : (X + Polynomial.C h).natDegree = 1 := Polynomial.natDegree_X_add_C h
  have hlead := congrArg Polynomial.leadingCoeff hpoly
  rw [Polynomial.leadingCoeff_comp (by rw [hnat]; norm_num)] at hlead
  have hmonic : (X + Polynomial.C h).leadingCoeff = 1 := (Polynomial.monic_X_add_C h)
  rw [hmonic, one_pow, mul_one, Polynomial.leadingCoeff_mul,
    Polynomial.leadingCoeff_C] at hlead
  have hCone : C = 1 := by
    have hne : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hPne
    have h1 : (1 : ℂ) * P.leadingCoeff = C * P.leadingCoeff := by rw [one_mul]; exact hlead
    exact (mul_right_cancel₀ hne h1).symm
  refine ⟨hCone, ?_⟩
  refine polynomial_eval_periodic_eq_zero hdegree (fun z => ?_)
  show P.eval (z + h) = P.eval z
  rw [hq z, hCone, one_mul]

/-- **The envelope has no nonzero quasi-period either.**  If
`A(z+h) P(z+h) = C · A(z) P(z)` identically with `C ≠ 0` and `deg P > 0`, then `h = 0`.
This is the full-germ separation step: a nonzero displacement cannot be absorbed by any
multiplicative constant. -/
theorem coshQuartetEnvelope_mul_polynomial_quasiPeriodic_eq_zero
    (a : ℝ) (ha : a ≠ 0) (P : Polynomial ℂ) (hdegree : 0 < P.degree) {h C : ℂ} (hC : C ≠ 0)
    (hq : ∀ z, coshQuartetEnvelope a (z + h) * P.eval (z + h)
        = C * (coshQuartetEnvelope a z * P.eval z)) :
    h = 0 := by
  by_contra hh
  set z0 : ℂ := (a : ℂ) - ((1 : ℂ) * Real.pi / 2) * I with hz0def
  set orbit : ℕ → ℂ := fun n => z0 + (n : ℂ) * h with horbitdef
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
  obtain ⟨Bd, hBd⟩ := hbad.bddAbove
  set N : ℕ := Bd + 1 with hNdef
  have hPgood : ∀ j : ℕ, P.eval (orbit (N + j)) ≠ 0 := by
    intro j hzero
    have hle := hBd (show N + j ∈ {n : ℕ | P.eval (orbit n) = 0} from hzero)
    dsimp [N] at hle
    omega
  have hz0 : coshQuartetEnvelope a z0 = 0 := by
    rw [coshQuartetEnvelope_eq_zero_iff]
    left
    exact ⟨0, by simp [hz0def]⟩
  have hFzero : ∀ n : ℕ,
      coshQuartetEnvelope a (orbit n) * P.eval (orbit n) = 0 := by
    intro n
    induction n with
    | zero => simp [horbitdef, hz0]
    | succ n ih =>
        have hstep := hq (orbit n)
        have heq : orbit n + h = orbit (n + 1) := by
          simp only [horbitdef, Nat.cast_add, Nat.cast_one]
          ring
        rw [heq] at hstep
        rw [hstep, ih, mul_zero]
  have hAzero : ∀ j : ℕ, coshQuartetEnvelope a (orbit (N + j)) = 0 := by
    intro j
    exact (mul_eq_zero.mp (hFzero (N + j))).resolve_right (hPgood j)
  have hquant : ∃ k : ℤ, h = (k : ℂ) * (Real.pi * I) := by
    apply coshQuartetEnvelope_three_zeros_quantize_period ha (z := orbit N)
    · exact hAzero 0
    · have heq : orbit N + h = orbit (N + 1) := by
        simp only [horbitdef, Nat.cast_add, Nat.cast_one]
        ring
      rw [heq]
      exact hAzero 1
    · have heq : orbit N + 2 * h = orbit (N + 2) := by
        simp only [horbitdef, Nat.cast_add, Nat.cast_ofNat]
        ring
      rw [heq]
      exact hAzero 2
  have hAperiod : Function.Periodic (coshQuartetEnvelope a) h :=
    (coshQuartetEnvelope_periodic_iff a h).mpr hquant
  have hAreal : ∀ x : ℝ, coshQuartetEnvelope a (x : ℂ) ≠ 0 := by
    intro x
    rw [coshQuartetEnvelope,
      ← Complex.ofReal_sub, ← Complex.ofReal_add,
      ← Complex.ofReal_cosh, ← Complex.ofReal_cosh]
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.cosh_pos (x - a))))
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.cosh_pos (x + a))))
  have hPquasi : ∀ z : ℂ, P.eval (z + h) = C * P.eval z := by
    have hEvalReal : ∀ x : ℝ, P.eval ((x : ℂ) + h) = C * P.eval (x : ℂ) := by
      intro x
      have hprod := hq (x : ℂ)
      rw [hAperiod (x : ℂ)] at hprod
      have hrw : coshQuartetEnvelope a (x : ℂ) * P.eval ((x : ℂ) + h)
          = coshQuartetEnvelope a (x : ℂ) * (C * P.eval (x : ℂ)) := by
        rw [hprod]; ring
      exact mul_left_cancel₀ (hAreal x) hrw
    have hpoly : P.comp (X + Polynomial.C h) = Polynomial.C C * P := by
      refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
      refine (Set.infinite_range_of_injective Complex.ofReal_injective).mono ?_
      rintro z ⟨x, rfl⟩
      simp only [Set.mem_setOf_eq, eval_comp, eval_add, eval_X, eval_C, eval_mul]
      exact hEvalReal x
    intro z
    have heval := congrArg (Polynomial.eval z) hpoly
    simpa [eval_comp] using heval
  exact hh (polynomial_eval_quasiPeriodic_eq_zero hdegree hC hPquasi).2


end RHTower

end
