import GaloisForLFunctions.HTGeometry.RittCocycle
import GaloisForLFunctions.HTGeometry.RGTowerCoherence
import GaloisForLFunctions.HTGeometry.AddPolynomialInvariance

/-!
# The rational RG generation dichotomy, differential-algebra side

The order-one Ritt relation `Q(σ) (σ')^r = a z^j P(σ)` is an algebraic differential equation, so it
makes the Poincaré germ differentially algebraic.  Differential algebraicity then passes back and
forth between the Poincaré germ, its local inverse and the exact beta field, and is invariant under
any locally invertible differentially algebraic coupling chart.

What is *not* proved here is the converse Ritt implication — that differential algebraicity forces
the order-one relation.  That is the external classification input of the dichotomy.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- A nonzero complex polynomial takes a nonzero value. -/
private theorem exists_polynomial_eval_ne_zero {Q : Polynomial ℂ} (hQ : Q ≠ 0) :
    ∃ t : ℂ, Polynomial.eval t Q ≠ 0 := by
  by_contra h
  push Not at h
  exact hQ (Polynomial.funext fun t => by rw [h t, Polynomial.eval_zero])

/-- **The Ritt form is an algebraic differential equation.**  A relation
`Q(σ) (σ')^r = a z^j P(σ)` with `Q ≠ 0` and `r ≥ 1` makes `σ` differentially algebraic. -/
theorem differentiallyAlgebraicOn_of_rittForm {U : Set ℂ} {sigma : ℂ → ℂ} {a : ℂ} {r j : ℕ}
    (hr : 0 < r) {P Q : Polynomial ℂ} (hQ : Q ≠ 0)
    (hrel : ∀ z ∈ U, Polynomial.eval (sigma z) Q * deriv sigma z ^ r
      = a * z ^ j * Polynomial.eval (sigma z) P) :
    DifferentiallyAlgebraicOn sigma U := by
  classical
  set F : MvPolynomial (Fin 3) ℂ :=
    Polynomial.aeval (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ) Q * MvPolynomial.X 2 ^ r
      - MvPolynomial.C a * MvPolynomial.X 0 ^ j
        * Polynomial.aeval (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ) P with hFdef
  have hFeval : ∀ v : Fin 3 → ℂ, MvPolynomial.eval v F
      = Polynomial.eval (v 1) Q * v 2 ^ r - a * v 0 ^ j * Polynomial.eval (v 1) P := by
    intro v
    rw [hFdef]
    simp only [map_sub, map_mul, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C,
      eval_aeval_X]
  refine ⟨1, F, ?_, fun z hz => ?_⟩
  · -- a witness point where `F` does not vanish
    obtain ⟨t₀, ht₀⟩ := exists_polynomial_eval_ne_zero hQ
    obtain ⟨s, hs⟩ : ∃ s : ℂ, Polynomial.eval t₀ Q * s ^ r - a * Polynomial.eval t₀ P ≠ 0 := by
      by_contra hall
      push Not at hall
      set G : Polynomial ℂ := Polynomial.C (Polynomial.eval t₀ Q) * Polynomial.X ^ r
        - Polynomial.C (a * Polynomial.eval t₀ P) with hG
      have hGzero : G = 0 := by
        refine Polynomial.funext fun s => ?_
        rw [hG]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
        exact hall s
      have hcoeff := congrArg (fun p => Polynomial.coeff p r) hGzero
      simp only [hG, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_C, Polynomial.coeff_zero, mul_one] at hcoeff
      rw [if_neg (by omega : ¬ r = 0)] at hcoeff
      simp at hcoeff
      exact ht₀ hcoeff
    intro h0
    apply hs
    have := hFeval ![1, t₀, s]
    rw [h0] at this
    simpa using this.symm
  · rw [show (Fin.cons z fun i : Fin 2 => iteratedDeriv (i : ℕ) sigma z)
        = ![z, sigma z, deriv sigma z] from ?_]
    · rw [hFeval]
      have := hrel z hz
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      show Polynomial.eval (sigma z) Q * deriv sigma z ^ r
        - a * z ^ j * Polynomial.eval (sigma z) P = 0
      rw [this, sub_self]
    · funext i
      fin_cases i
      · rfl
      · simp [iteratedDeriv_zero]
      · show iteratedDeriv 1 sigma z = deriv sigma z
        rw [iteratedDeriv_one]

/-- **The differential-algebra half of the dichotomy `(1) ⇔ (2) ⇔ (3)`.**  For a Poincaré germ and
its local inverse, differential algebraicity of the linearizing coordinate, of its inverse and of
the exact beta field are all equivalent. -/
theorem differentiallyAlgebraicOn_poincare_iff_rgBeta
    {U V : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    {Φ κ : ℂ → ℂ} (hΦ : AnalyticOnNhd ℂ Φ V) (hκ : AnalyticOnNhd ℂ κ U)
    (hκV : Set.MapsTo κ U V) (hΦU : Set.MapsTo Φ V U)
    (hΦκ : ∀ t ∈ U, Φ (κ t) = t) (hκΦ : ∀ z ∈ V, κ (Φ z) = z)
    (hκne : ∀ t ∈ U, κ t ≠ 0) (hκ'ne : ∀ t ∈ U, deriv κ t ≠ 0)
    {lamLog : ℂ} (hlamLog : lamLog ≠ 0) :
    (DifferentiallyAlgebraicOn Φ V ↔ DifferentiallyAlgebraicOn κ U) ∧
      (DifferentiallyAlgebraicOn κ U ↔ DifferentiallyAlgebraicOn (rgBeta lamLog κ) U) := by
  constructor
  · constructor
    · intro hΦDA
      exact differentiallyAlgebraicOn_of_localInverse hVo hVc hVne hVinf hκ hΦ hΦU hκV hκΦ hΦκ hΦDA
    · intro hκDA
      exact differentiallyAlgebraicOn_of_localInverse hUo hUc hUne hUinf hΦ hκ hκV hΦU hΦκ hκΦ hκDA
  · constructor
    · intro hκDA
      exact differentiallyAlgebraicOn_rgBeta hUo hUc hUne hUinf hκ hκne hκ'ne lamLog hκDA
    · intro hβ
      exact differentiallyAlgebraicOn_of_rgBeta hUo hUc hUne hUinf hκ hκne hκ'ne hlamLog hβ

end

end GaloisForLFunctions.HTGeometry
