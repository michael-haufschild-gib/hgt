import GaloisForLFunctions.HTGeometry.GammaFieldFinitePhaseRank
import GaloisForLFunctions.HTGeometry.GammaRationalWitness

/-!
# The Gamma-field law is not vacuous

A constant is the Gamma-field monomial with all data zero, so the relation `Φ' − μ Φ = 0` satisfied by
`e^{μ z}` has Gamma-field coefficients whose lexicographic dominance is the equality case.  The
exponential is entire, almost periodic on every vertical strip, and its restriction to the critical
line is a bounded continuous function with totally bounded orbit.

So the finite-phase law over `ℂ(s)⟨Γ⟩` applies on the critical line, and the frequency `μ` is a
frequency of the hull: the hypothesis class is inhabited by objects of nonzero rank.
-/

open Filter Topology Complex Polynomial

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- A constant is the Gamma-field monomial with all data zero. -/
theorem gammaFieldElt_const (m : ℕ) (c : ℂ) (t : ℝ) :
    gammaFieldElt m 0 (Polynomial.C c) (Polynomial.C 1) 0 t = c := by
  simp [gammaFieldElt]

/-- **The Gamma-field finite-phase law is not vacuous.**  The exponential `e^{μ z}` with a nonzero
real frequency satisfies every hypothesis on the critical line: it is entire and strip almost
periodic, its line restriction is a bounded continuous function with totally bounded orbit, and it
solves `Φ' − μ Φ = 0`, whose coefficients are Gamma-field monomials with all data zero, so the
lexicographic dominance is the equality case. -/
theorem rank_finite_expLine_gammaField (μ : ℝ) (hμ : μ ≠ 0) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies (expLineBC μ (1 / 2 + (0 : ℕ)))) ≤ (K : Cardinal) := by
  classical
  set f : ℝ →ᵇ ℂ := expLineBC μ (1 / 2 + (0 : ℕ)) with hfdef
  letI : MeasurableSpace (BohrHull f) := borel _
  haveI : BorelSpace (BohrHull f) := ⟨rfl⟩
  have hR : (0 : ℝ) < 1 := one_pos
  have hΦ : DifferentiableOn ℂ (expLine μ) (verticalStrip (1 / 2 + (0 : ℕ)) 1) :=
    (differentiable_expLine μ).differentiableOn
  have hap : IsStripAlmostPeriodic (expLine μ) (1 / 2 + (0 : ℕ)) 1 :=
    isStripAlmostPeriodic_expLine μ _ _
  set e : Fin 2 → Fin 2 → ℕ := ![![0, 1], ![1, 0]] with hedef
  set F : Fin 2 → ℂ → ℂ := ![fun _ => 1, fun _ => -(μ : ℂ)] with hFdef
  set p : Fin 2 → Polynomial ℂ := ![Polynomial.C 1, Polynomial.C (-(μ : ℂ))] with hpdef
  set q : Fin 2 → Polynomial ℂ := ![Polynomial.C 1, Polynomial.C 1] with hqdef
  have hp : ∀ α, p α ≠ 0 := by
    intro α
    fin_cases α <;> simp [hpdef, hμ]
  have hq : ∀ α, q α ≠ 0 := by
    intro α
    fin_cases α <;> simp [hqdef]
  have hF : ∀ (α : Fin 2) (t : ℝ),
      F α (((1 / 2 + (0 : ℕ) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        = gammaFieldElt 0 (0 : ℕ) (p α) (q α) 0 t := by
    intro α t
    fin_cases α <;> simp [hFdef, hpdef, hqdef, gammaFieldElt]
  have hrel : ∀ s : ℂ,
      ∑ α, F α s * ∏ i : Fin 2, (iteratedDeriv (i : ℕ) (expLine μ) s) ^ (e α i) = 0 := by
    intro s
    rw [Fin.sum_univ_two]
    simp only [hedef, hFdef, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      iteratedDeriv_expLine, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    ring
  have hlex : ∀ α : Fin 2, (0 : ℕ) < 0 ∨ ((0 : ℕ) = 0 ∧
      ((p α * q 0).natDegree < (q α * p 0).natDegree ∨
        ((p α * q 0).natDegree = (q α * p 0).natDegree ∧ (0 : ℕ) ≤ 0))) := by
    intro α
    exact Or.inr ⟨rfl, Or.inr ⟨by fin_cases α <;> simp [hpdef, hqdef],
      le_rfl⟩⟩
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hline : IsBohrAlmostPeriodic
      (fun t : ℝ => expLine μ (((1 / 2 + (0 : ℕ) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
    isBohrAlmostPeriodic_line hR hap
  have hf : ∀ x : ℝ, f x = expLine μ (((1 / 2 + (0 : ℕ) : ℝ) : ℂ) + (x : ℂ) * Complex.I) := by
    intro x
    rw [hfdef, expLineBC_apply]
  have hcont : Continuous (fun x : ℝ => f x) := by
    have hfun : (fun x : ℝ => f x)
        = fun t : ℝ => expLine μ (((1 / 2 + (0 : ℕ) : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
      funext x
      exact hf x
    rw [hfun]
    exact continuous_line_restriction hR hΦ
  have hapf : IsBohrAlmostPeriodic (fun x : ℝ => f x) := by
    have hfun : (fun x : ℝ => f x)
        = fun t : ℝ => expLine μ (((1 / 2 + (0 : ℕ) : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
      funext x
      exact hf x
    rw [hfun]
    exact hline
  exact rank_finite_of_gammaField_relation (r := 1/4) (ρ := 1/4) (by norm_num) (by norm_num)
    (by norm_num) hR hΦ hap e F (fun _ => 0) p q (fun _ => 0) 0 hp hq hF hrel hlex he hf
    (uniformContinuous_of_isBohrAlmostPeriodic hcont hapf)
    (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hcont hapf)

/-- **The Gamma-field law is inhabited by an object of nonzero rank on the critical line.** -/
theorem rank_expLine_gammaField_pos_and_finite (μ : ℝ) (hμ : μ ≠ 0) :
    ∃ K : ℕ,
      1 ≤ Module.rank ℤ (bohrHullFrequencies (expLineBC μ (1 / 2 + (0 : ℕ)))) ∧
        Module.rank ℤ (bohrHullFrequencies (expLineBC μ (1 / 2 + (0 : ℕ)))) ≤ (K : Cardinal) := by
  obtain ⟨K, hK⟩ := rank_finite_expLine_gammaField μ hμ
  exact ⟨K, one_le_rank_expLineBC μ hμ _, hK⟩

end GaloisForLFunctions
