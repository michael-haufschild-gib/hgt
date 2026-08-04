import GaloisForLFunctions.HTGeometry.EntireOrderZeroTranscendence

/-!
# Exact differential order one

A transcendental entire function satisfying a first-order algebraic differential equation has exact
differential order one: the equation is the upper bound, and the absence of an order-zero equation is
the lower bound.

This is the length-one case of the cascade order theorem, and it is unconditional.  The exponential
is an explicit instance, so the statement is not vacuous.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- An entire function is *transcendental* when it is not given by a polynomial. -/
def TranscendentalEntire (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z

/-- **Exact order one.**  A transcendental entire function with an order-one equation has no
equation of lower order. -/
theorem exactDifferentialOrder_one_of_transcendental {f : ℂ → ℂ}
    (hf : TranscendentalEntire f) (hup : DifferentiallyAlgebraicOfOrder f 1) :
    ExactDifferentialOrder f 1 := by
  refine ⟨hup, ?_⟩
  intro m hm
  have hm0 : m = 0 := by omega
  rw [hm0]
  exact not_differentiallyAlgebraicOfOrder_zero_of_transcendental hf.1 hf.2

/-- **Exact order one from a first-order relation.**  The card's shape of a first-order equation,
`∑ a_p(z) f(z)^{p₁} f'(z)^{p₂} = 0`, fixes the order exactly. -/
theorem exactDifferentialOrder_one_of_relation {f : ℂ → ℂ} (hf : TranscendentalEntire f)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ}
    (hP0 : firstOrderMvPoly S A ≠ 0)
    (hrel : ∀ u : ℂ, ∑ p ∈ S, (A p).eval u * (f u) ^ p.1 * (deriv f u) ^ p.2 = 0) :
    ExactDifferentialOrder f 1 :=
  exactDifferentialOrder_one_of_transcendental hf
    (differentiallyAlgebraicOfOrder_one_of_relation hP0 hrel)

/-- A cascade of length one is its single constituent. -/
theorem entireCascade_one (f : ℕ → ℂ → ℂ) : entireCascade f 1 = f 0 := rfl

/-- **The cascade order theorem at length one.** -/
theorem exactDifferentialOrder_cascade_one {f : ℕ → ℂ → ℂ}
    (hf : TranscendentalEntire (f 0)) (hup : DifferentiallyAlgebraicOfOrder (f 0) 1) :
    ExactDifferentialOrder (entireCascade f 1) 1 := by
  rw [entireCascade_one]
  exact exactDifferentialOrder_one_of_transcendental hf hup

/-! ## The exponential

An explicit transcendental entire function of exact differential order one.  Its first-order equation
is `y' - y = 0`, and it is transcendental because a polynomial agreeing with it would have no roots,
hence be constant, hence have vanishing derivative — while the derivative of the exponential is the
exponential, which never vanishes. -/

/-- **The exponential is transcendental.** -/
theorem transcendentalEntire_exp : TranscendentalEntire Complex.exp := by
  refine ⟨Complex.differentiable_exp, ?_⟩
  rintro ⟨p, hp⟩
  have hroot : ∀ z : ℂ, p.eval z ≠ 0 := by
    intro z hz
    have hz0 : Complex.exp z = 0 := by rw [hp z, hz]
    simp [Complex.exp_ne_zero] at hz0
  have hdeg : p.degree ≤ 0 := by
    by_contra hcon
    obtain ⟨z, hz⟩ := Complex.exists_root (not_le.mp hcon)
    exact hroot z hz
  have hc : p = Polynomial.C (p.coeff 0) := Polynomial.degree_le_zero_iff.mp hdeg
  have hconst : Complex.exp = fun _ : ℂ => p.coeff 0 := by
    funext z
    have hz := hp z
    rw [hc] at hz
    simpa using hz
  have hd : deriv Complex.exp 0 = 0 := by
    rw [hconst]
    simp
  rw [Complex.deriv_exp] at hd
  simp at hd

/-- **The exponential satisfies a first-order equation.** -/
theorem differentiallyAlgebraicOfOrder_one_exp :
    DifferentiallyAlgebraicOfOrder Complex.exp 1 := by
  have hne : ((0 : ℕ), (1 : ℕ)) ≠ ((1 : ℕ), (0 : ℕ)) := by decide
  refine differentiallyAlgebraicOfOrder_one_of_relation
    (S := ({((0 : ℕ), (1 : ℕ)), ((1 : ℕ), (0 : ℕ))} : Finset (ℕ × ℕ)))
    (A := fun q => if q = ((0 : ℕ), (1 : ℕ)) then 1 else -1) ?_ ?_
  · intro hcon
    have hval : MvPolynomial.eval (fun j : Fin 3 => ![0, 0, 1] j)
        (firstOrderMvPoly ({((0 : ℕ), (1 : ℕ)), ((1 : ℕ), (0 : ℕ))} : Finset (ℕ × ℕ))
          (fun q => if q = ((0 : ℕ), (1 : ℕ)) then 1 else -1)) = 1 := by
      rw [eval_firstOrderMvPoly, Finset.sum_pair hne]
      norm_num
    rw [hcon] at hval
    simp at hval
  · intro u
    rw [Finset.sum_pair hne, Complex.deriv_exp]
    norm_num

/-- **The exponential has exact differential order one.** -/
theorem exactDifferentialOrder_exp_one : ExactDifferentialOrder Complex.exp 1 :=
  exactDifferentialOrder_one_of_transcendental transcendentalEntire_exp
    differentiallyAlgebraicOfOrder_one_exp

end GaloisForLFunctions.HTGeometry
