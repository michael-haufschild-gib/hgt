/-
# The determinant-completion fibre in several variables, at every order

Along the family of parameters the completed character is the order-`p` determinant times the
exponential of a jet.  If the determinants converge and the jets converge pointwise, the limit has
the same shape, and the limit jet is again a polynomial of the same bounded degree because the
bounded-degree evaluation space is finite-dimensional, hence closed under pointwise limits.  The
constant coefficient is preserved because it is the value at the origin.

Main results:
* `exists_mvPoly_limit_of_tendsto_familyDet` — **the multivariable fibre statement at every
  order**.
* `exists_mvPoly_limit_of_tendsto_pencilDet` — the same for a linear operator pencil, with the
  parameter carried into the spectral variable.
* `exists_mvPoly_of_line_closures` — **the multivariable necessity from the one-variable closures
  along every line**.
-/
import GaloisForLFunctions.HTGeometry.BoundedDegreeMvPolynomialLimit
import GaloisForLFunctions.HTGeometry.OperatorDeterminantScaling
import GaloisForLFunctions.HTGeometry.PolynomialLineRestriction

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The multivariable determinant-completion fibre, at every order.** -/
theorem exists_mvPoly_limit_of_tendsto_familyDet {m d p : ℕ}
    {A : ℕ → (Fin m → ℂ) → (H →L[ℂ] H)} {B : (Fin m → ℂ) → (H →L[ℂ] H)}
    (hconv : ∀ v, Tendsto (fun n => opSchattenDet p (A n v) 1) atTop
      (nhds (opSchattenDet p (B v) 1)))
    {P : ℕ → MvPolynomial (Fin m) ℂ} (hdeg : ∀ n, (P n).totalDegree ≤ d)
    {g : (Fin m → ℂ) → ℂ}
    (hg : ∀ v, Tendsto (fun n => MvPolynomial.eval v (P n)) atTop (nhds (g v)))
    {F : (Fin m → ℂ) → ℂ}
    (hF : ∀ v, Tendsto (fun n => opSchattenDet p (A n v) 1
      * Complex.exp (MvPolynomial.eval v (P n))) atTop (nhds (F v))) :
    ∃ Q : MvPolynomial (Fin m) ℂ, Q.totalDegree ≤ d ∧
      (∀ v, MvPolynomial.eval v Q = g v) ∧
      ∀ v, F v = opSchattenDet p (B v) 1 * Complex.exp (MvPolynomial.eval v Q) := by
  obtain ⟨Q, hQdeg, hQeval⟩ := exists_mvPolynomial_of_tendsto_pointwise hdeg hg
  refine ⟨Q, hQdeg, hQeval, fun v => ?_⟩
  have hexp : Tendsto (fun n => Complex.exp (MvPolynomial.eval v (P n))) atTop
      (nhds (Complex.exp (g v))) :=
    (Complex.continuous_exp.continuousAt).tendsto.comp (hg v)
  have hprod := (hconv v).mul hexp
  have := tendsto_nhds_unique (hF v) hprod
  rw [this, hQeval v]

/-- The limit jet keeps a vanishing constant coefficient. -/
theorem eval_zero_eq_zero_of_tendsto {m : ℕ} {P : ℕ → MvPolynomial (Fin m) ℂ}
    (hP0 : ∀ n, MvPolynomial.eval (0 : Fin m → ℂ) (P n) = 0)
    {g : (Fin m → ℂ) → ℂ}
    (hg : ∀ v, Tendsto (fun n => MvPolynomial.eval v (P n)) atTop (nhds (g v))) :
    g 0 = 0 := by
  have h := hg 0
  simp only [hP0] at h
  exact (tendsto_nhds_unique tendsto_const_nhds h).symm

/-- **The multivariable fibre statement for a linear operator pencil.**  The parameter is carried
into the spectral variable by the line reduction. -/
theorem exists_mvPoly_limit_of_tendsto_pencilDet {m d p : ℕ}
    {A : ℕ → Fin m → (H →L[ℂ] H)} {B : Fin m → (H →L[ℂ] H)}
    (hconv : ∀ v, Tendsto (fun n => opSchattenDet p (pencilOperator (A n) v) 1) atTop
      (nhds (opSchattenDet p (pencilOperator B v) 1)))
    {P : ℕ → MvPolynomial (Fin m) ℂ} (hdeg : ∀ n, (P n).totalDegree ≤ d)
    (hP0 : ∀ n, MvPolynomial.eval (0 : Fin m → ℂ) (P n) = 0)
    {g : (Fin m → ℂ) → ℂ}
    (hg : ∀ v, Tendsto (fun n => MvPolynomial.eval v (P n)) atTop (nhds (g v)))
    {F : (Fin m → ℂ) → ℂ}
    (hF : ∀ v, Tendsto (fun n => opSchattenDet p (pencilOperator (A n) v) 1
      * Complex.exp (MvPolynomial.eval v (P n))) atTop (nhds (F v))) :
    ∃ Q : MvPolynomial (Fin m) ℂ, Q.totalDegree ≤ d ∧
      MvPolynomial.eval (0 : Fin m → ℂ) Q = 0 ∧
      ∀ v, F v = opSchattenDet p (pencilOperator B v) 1
        * Complex.exp (MvPolynomial.eval v Q) := by
  obtain ⟨Q, hQdeg, hQeval, hQ⟩ :=
    exists_mvPoly_limit_of_tendsto_familyDet hconv hdeg hg hF
  exact ⟨Q, hQdeg, by rw [hQeval 0]; exact eval_zero_eq_zero_of_tendsto hP0 hg, hQ⟩

/-- **Multivariable necessity from the one-variable closures along every line.**  Once the
one-variable completion law has produced a limit jet coefficientwise on each line through the
origin, the multivariable jet is again a polynomial of the same bounded degree with vanishing
constant term, and the limit character has the card's shape. -/
theorem exists_mvPoly_of_line_closures {m d p : ℕ}
    {A : ℕ → (Fin m → ℂ) → (H →L[ℂ] H)} {B : (Fin m → ℂ) → (H →L[ℂ] H)}
    {P : ℕ → MvPolynomial (Fin m) ℂ} (hdeg : ∀ n, (P n).totalDegree ≤ d)
    (hP0 : ∀ n, MvPolynomial.eval (0 : Fin m → ℂ) (P n) = 0)
    {Qline : (Fin m → ℂ) → Polynomial ℂ}
    (hQdeg : ∀ v, (Qline v).natDegree ≤ d)
    (hQc : ∀ v, ∀ h : ℕ, Tendsto (fun n => (lineRestrict v (P n)).coeff h) atTop
      (nhds ((Qline v).coeff h)))
    (hconv : ∀ v, Tendsto (fun n => opSchattenDet p (A n v) 1) atTop
      (nhds (opSchattenDet p (B v) 1)))
    {F : (Fin m → ℂ) → ℂ}
    (hF : ∀ v, Tendsto (fun n => opSchattenDet p (A n v) 1
      * Complex.exp (MvPolynomial.eval v (P n))) atTop (nhds (F v))) :
    ∃ Q : MvPolynomial (Fin m) ℂ, Q.totalDegree ≤ d ∧
      MvPolynomial.eval (0 : Fin m → ℂ) Q = 0 ∧
      ∀ v, F v = opSchattenDet p (B v) 1 * Complex.exp (MvPolynomial.eval v Q) := by
  have hg : ∀ v, Tendsto (fun n => MvPolynomial.eval v (P n)) atTop
      (nhds (Polynomial.eval 1 (Qline v))) :=
    fun v => tendsto_eval_of_line_coeff hdeg v (hQdeg v) (hQc v)
  obtain ⟨Q, hQdeg', hQeval, hQ⟩ :=
    exists_mvPoly_limit_of_tendsto_familyDet hconv hdeg hg hF
  refine ⟨Q, hQdeg', ?_, hQ⟩
  rw [hQeval 0]
  exact eval_zero_eq_zero_of_tendsto hP0 hg

end

end GaloisForLFunctions.HTGeometry
