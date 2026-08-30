import GaloisForLFunctions.HTGeometry.RittDichotomy

/-!
# The infinite-divisor obstruction to a rational Ritt cocycle

Written with cleared denominators, the Ritt cocycle `R'(t)^r A(t) = c · A(R t)` says that at every
non-critical point the numerator of `A` vanishes at `t` exactly when it vanishes at `R t`.  So a
zero of the numerator propagates backwards along any critical-free chain of preimages, and an
infinite such chain would give the numerator infinitely many roots.

That is the negative branch of the rational RG generation dichotomy: exhibiting one infinite
critical-free backward chain through a zero rules out the cocycle, and with it the order-one Ritt
relation, for that map.  It is the exact counterpart of the power-map computation, which realises
the positive branch.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Vanishing propagates across a non-critical point.**  In cleared form the cocycle makes the
numerator vanish at `t` exactly when it vanishes at `R t`. -/
theorem eval_eq_zero_iff_of_clearedCocycle {R : ℂ → ℂ} {P Q : Polynomial ℂ} {c : ℂ} {r : ℕ}
    (hc : c ≠ 0) {t : ℂ} (hR' : deriv R t ≠ 0) (hQ1 : Polynomial.eval t Q ≠ 0)
    (hQ2 : Polynomial.eval (R t) Q ≠ 0)
    (h : deriv R t ^ r * (Polynomial.eval t P * Polynomial.eval (R t) Q)
      = c * (Polynomial.eval (R t) P * Polynomial.eval t Q)) :
    Polynomial.eval t P = 0 ↔ Polynomial.eval (R t) P = 0 := by
  constructor
  · intro hz
    rw [hz, zero_mul, mul_zero] at h
    have := h.symm
    rcases mul_eq_zero.mp this with hcz | hprod
    · exact absurd hcz hc
    · rcases mul_eq_zero.mp hprod with hz2 | hq
      · exact hz2
      · exact absurd hq hQ1
  · intro hz
    rw [hz, zero_mul, mul_zero] at h
    rcases mul_eq_zero.mp h with hpow | hprod
    · exact absurd (pow_eq_zero_iff'.mp hpow).1 hR'
    · rcases mul_eq_zero.mp hprod with hz2 | hq
      · exact hz2
      · exact absurd hq hQ2

/-- **The infinite-divisor obstruction.**  A rational cocycle solution whose numerator vanishes at
the head of an infinite critical-free backward chain has zero numerator; so no such cocycle exists
with a nonzero numerator. -/
theorem not_clearedCocycle_of_infinite_backward_chain {R : ℂ → ℂ} {P Q : Polynomial ℂ} {c : ℂ}
    {r : ℕ} (hc : c ≠ 0) (hP : P ≠ 0) {t : ℕ → ℂ} (hinj : Function.Injective t)
    (hback : ∀ k : ℕ, R (t (k + 1)) = t k) (hR' : ∀ k : ℕ, deriv R (t (k + 1)) ≠ 0)
    (hQ : ∀ k : ℕ, Polynomial.eval (t k) Q ≠ 0)
    (hzero : Polynomial.eval (t 0) P = 0)
    (hcoc : ∀ s : ℂ, deriv R s ^ r * (Polynomial.eval s P * Polynomial.eval (R s) Q)
      = c * (Polynomial.eval (R s) P * Polynomial.eval s Q)) :
    False := by
  have hall : ∀ k : ℕ, Polynomial.eval (t k) P = 0 := by
    intro k
    induction k with
    | zero => exact hzero
    | succ k ih =>
        have hQ2 : Polynomial.eval (R (t (k + 1))) Q ≠ 0 := by
          rw [hback k]
          exact hQ k
        have hiff := eval_eq_zero_iff_of_clearedCocycle hc (hR' k) (hQ (k + 1)) hQ2
          (hcoc (t (k + 1)))
        rw [hback k] at hiff
        exact hiff.mpr ih
  have hinf : {z : ℂ | P.IsRoot z}.Infinite := by
    refine Set.Infinite.mono (s := Set.range t) ?_ (Set.infinite_range_of_injective hinj)
    rintro _ ⟨k, rfl⟩
    exact hall k
  exact hP (Polynomial.eq_zero_of_infinite_isRoot P hinf)

end

end GaloisForLFunctions.HTGeometry
