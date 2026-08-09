import GaloisForLFunctions.HTGeometry.PairCascadeOrder

/-!
# Instances of the linear first-order law

The polynomial-coefficient family `d + c·exp(A)` is the special case `b = −a·d` of
`h' = a(z)·h + b(z)`, so the two-coordinate law recovers it.  The general case is strictly larger:
`h' = h + z` has the entire solution `c·e^z − z − 1`, whose coefficient pair `(1, X)` is not
proportional, so it is not of the exponential shape.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-! ## The exponential family is the proportional case -/

/-- **The two-coordinate law recovers the polynomial-coefficient law.** -/
theorem exactDifferentialOrder_expPolyCascade_of_linear {A : ℕ → Polynomial ℂ} {c d : ℕ → ℂ}
    (hc : ∀ k, c k ≠ 0) (hA : ∀ k, 1 ≤ (A k).natDegree) (m : ℕ) :
    ExactDifferentialOrder (entireCascade (expPoly A c d) (m + 1)) (m + 1) :=
  exactDifferentialOrder_linearCascade
    (a := fun k => (A k).derivative)
    (b := fun k => -((A k).derivative * Polynomial.C (d k)))
    (fun k => transcendentalEntire_expPoly (hc k) (hA k))
    (fun k z => by
      rw [deriv_expPoly]
      simp only [Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_C]
      ring)
    (fun k => by
      intro h0
      rw [Polynomial.derivative_eq_zero] at h0
      have hk := hA k
      omega) m

/-! ## A solution outside the exponential family -/

theorem transcendentalEntire_sub_poly {f : ℂ → ℂ} (hf : TranscendentalEntire f)
    (q : Polynomial ℂ) : TranscendentalEntire (fun z => f z - q.eval z) := by
  refine ⟨hf.1.sub (fun z => (q.hasDerivAt z).differentiableAt), ?_⟩
  rintro ⟨r, hr⟩
  refine hf.2 ⟨r + q, fun z => ?_⟩
  have h := hr z
  rw [Polynomial.eval_add]
  linear_combination h

/-- The entire solution of `h' = h + z`. -/
noncomputable def linSol (c : ℂ) : ℂ → ℂ := fun z => c * Complex.exp z - z - 1

theorem linSol_eq (c : ℂ) :
    linSol c = fun z =>
      expPoly (fun _ => Polynomial.X) (fun _ => c) (fun _ => 0) 0 z
        - (Polynomial.X + 1 : Polynomial ℂ).eval z := by
  funext z
  simp only [linSol, expPoly, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_one,
    zero_add]
  ring

theorem transcendentalEntire_linSol {c : ℂ} (hc : c ≠ 0) : TranscendentalEntire (linSol c) := by
  rw [linSol_eq]
  exact transcendentalEntire_sub_poly
    (transcendentalEntire_expPoly (A := fun _ => Polynomial.X) (c := fun _ => c)
      (d := fun _ => 0) (k := 0) hc (by rw [Polynomial.natDegree_X])) _

/-- **The defining equation `h' = h + z`.** -/
theorem deriv_linSol (c : ℂ) (z : ℂ) :
    deriv (linSol c) z
      = (1 : Polynomial ℂ).eval z * linSol c z + (Polynomial.X : Polynomial ℂ).eval z := by
  have h1 : HasDerivAt (fun w : ℂ => c * Complex.exp w) (c * Complex.exp z) z :=
    (Complex.hasDerivAt_exp z).const_mul c
  have hid : HasDerivAt (fun w : ℂ => w) (1 : ℂ) z := hasDerivAt_id' z
  have h2 : HasDerivAt (fun w : ℂ => c * Complex.exp w - w) (c * Complex.exp z - 1) z :=
    h1.sub hid
  have h3 : HasDerivAt (linSol c) (c * Complex.exp z - 1) z := h2.sub_const 1
  rw [h3.deriv]
  simp only [linSol, Polynomial.eval_one, Polynomial.eval_X, one_mul]
  ring

/-- **The card's law for an explicit family outside the exponential one.** -/
theorem exactDifferentialOrder_linSolCascade {c : ℂ} (hc : c ≠ 0) (m : ℕ) :
    ExactDifferentialOrder (entireCascade (fun _ => linSol c) (m + 1)) (m + 1) :=
  exactDifferentialOrder_linearCascade
    (a := fun _ => 1) (b := fun _ => Polynomial.X)
    (fun _ => transcendentalEntire_linSol hc)
    (fun _ z => deriv_linSol c z)
    (fun _ => one_ne_zero) m

/-- **The coefficient pair of `h' = h + z` is not proportional**, so the equation is not of the
exponential shape `h' = a·(h − d)`. -/
theorem linSol_coefficients_not_proportional (d : ℂ) :
    (Polynomial.X : Polynomial ℂ) ≠ -((1 : Polynomial ℂ) * Polynomial.C d) := by
  intro h
  have hdeg := congrArg Polynomial.natDegree h
  rw [Polynomial.natDegree_X, one_mul] at hdeg
  simp at hdeg

end GaloisForLFunctions.HTGeometry
