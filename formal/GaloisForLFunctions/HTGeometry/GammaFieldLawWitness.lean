import GaloisForLFunctions.HTGeometry.GammaFieldFinitePhaseLaw
import GaloisForLFunctions.HTGeometry.GammaRationalWitness

/-!
# The law is inhabited on every vertical line

A constant is the Gamma-field monomial with all data zero, so `Φ′ − μΦ = 0` — the relation satisfied
by `e^{μz}` — has coefficients in the monomial normal form the law asks for, with the lexicographic
dominance in its equality case.

The exponential is entire and almost periodic on every vertical strip, and its restriction to any
vertical line is a bounded continuous function with totally bounded orbit, so the law applies for
every `σ > 0` and returns a rank between `1` and its finite bound.
-/

open Filter Topology Complex Polynomial

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- A constant is the full-tower monomial with all data zero. -/
theorem gammaJetEltG_const {σ : ℝ} (c : ℂ) (t : ℝ) :
    gammaJetEltG σ 0 (Polynomial.C c) (Polynomial.C 1) (fun _ : Fin 1 => 0) t = c := by
  simp [gammaJetEltG]

/-- **The finite-phase law over the Gamma field is not vacuous, on every vertical line.**  The
exponential `e^{μ z}` satisfies every hypothesis: it solves `Φ′ − μΦ = 0`, whose coefficients are the
Gamma-field monomials with all data zero. -/
theorem gammaField_finite_phase_law_expLine {σ : ℝ} (hσ : 0 < σ) (μ : ℝ) (hμ : μ ≠ 0) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies (expLineBC μ σ)) ≤ (K : Cardinal) := by
  classical
  set f : ℝ →ᵇ ℂ := expLineBC μ σ with hfdef
  letI : MeasurableSpace (BohrHull f) := borel _
  haveI : BorelSpace (BohrHull f) := ⟨rfl⟩
  have hR : (0 : ℝ) < 1 := one_pos
  have hΦ : DifferentiableOn ℂ (expLine μ) (verticalStrip σ 1) :=
    (differentiable_expLine μ).differentiableOn
  have hap : IsStripAlmostPeriodic (expLine μ) σ 1 := isStripAlmostPeriodic_expLine μ _ _
  set e : Fin 2 → Fin 2 → ℕ := ![![0, 1], ![1, 0]] with hedef
  set F : Fin 2 → ℂ → ℂ := ![fun _ => 1, fun _ => -(μ : ℂ)] with hFdef
  set p : Fin 2 → Fin 1 → Polynomial ℂ :=
    ![fun _ => Polynomial.C 1, fun _ => Polynomial.C (-(μ : ℂ))] with hpdef
  set q : Fin 2 → Fin 1 → Polynomial ℂ :=
    ![fun _ => Polynomial.C 1, fun _ => Polynomial.C 1] with hqdef
  have hp : ∀ a i, p a i ≠ 0 := by
    intro a i
    fin_cases a <;> simp [hpdef, hμ]
  have hq : ∀ a i, q a i ≠ 0 := by
    intro a i
    fin_cases a <;> simp [hqdef]
  have hdeg : ∀ (a : Fin 2) (i : Fin 1),
      (p a i * Polynomial.C 1).natDegree = (q a i * Polynomial.C 1).natDegree := by
    intro a i
    fin_cases a <;> simp [hpdef, hqdef]
  have hdom : ∀ (a : Fin 2) (i : Fin 1),
      GammaMonomialDominates 0 (p a i) (q a i) ((fun _ : Fin 1 => (0 : ℕ)) 0)
        0 (Polynomial.C 1) (Polynomial.C 1) 0 :=
    fun a i => Or.inr ⟨rfl, Or.inr ⟨hdeg a i, le_rfl⟩⟩
  have hc : (∑ i : Fin 1, gammaJetLimit 0 (p 0 i) (q 0 i) (fun _ : Fin 1 => (0 : ℕ))
      0 (Polynomial.C 1) (Polynomial.C 1) 0) ≠ 0 := by
    simp [gammaJetLimit, gammaMonomialLimit, hpdef, hqdef]
  have hF : ∀ (α : Fin 2) (t : ℝ),
      F α ((σ : ℂ) + (t : ℂ) * Complex.I)
        = ∑ i : Fin 1, gammaJetEltG σ 0 (p α i) (q α i) (fun _ : Fin 1 => (0 : ℕ)) t := by
    intro α t
    rw [Fin.sum_univ_one]
    fin_cases α <;> simp [hFdef, hpdef, hqdef, gammaJetEltG]
  have hrel : ∀ s : ℂ,
      ∑ α, F α s * ∏ i : Fin 2, (iteratedDeriv (i : ℕ) (expLine μ) s) ^ (e α i) = 0 := by
    intro s
    rw [Fin.sum_univ_two]
    simp only [hedef, hFdef, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      iteratedDeriv_expLine, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    ring
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hline : IsBohrAlmostPeriodic
      (fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    isBohrAlmostPeriodic_line hR hap
  have hf : ∀ x : ℝ, f x = expLine μ ((σ : ℂ) + (x : ℂ) * Complex.I) := by
    intro x
    rw [hfdef, expLineBC_apply]
  have hcont : Continuous (fun x : ℝ => f x) := by
    have hfun : (fun x : ℝ => f x)
        = fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I) := funext hf
    rw [hfun]
    exact continuous_line_restriction hR hΦ
  have hapf : IsBohrAlmostPeriodic (fun x : ℝ => f x) := by
    have hfun : (fun x : ℝ => f x)
        = fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I) := funext hf
    rw [hfun]
    exact hline
  obtain ⟨-, -, hrank⟩ := gammaField_finite_phase_law (rr := 1/4) (ρ := 1/4) hσ (by norm_num)
    (by norm_num)
    (by norm_num) hR hΦ hap e F (fun _ _ => 0) p q (fun _ _ => fun _ : Fin 1 => 0)
    0 (Polynomial.C 1) (Polynomial.C 1) 0 hq (by simp) (by simp) hdom 0 hc hF hrel he hf
    (uniformContinuous_of_isBohrAlmostPeriodic hcont hapf)
    (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hcont hapf)
  exact hrank

/-- **The law is inhabited on every vertical line by an object of nonzero rank.** -/
theorem gammaField_finite_phase_law_expLine_pos {σ : ℝ} (hσ : 0 < σ) (μ : ℝ) (hμ : μ ≠ 0) :
    ∃ K : ℕ, 1 ≤ Module.rank ℤ (bohrHullFrequencies (expLineBC μ σ)) ∧
      Module.rank ℤ (bohrHullFrequencies (expLineBC μ σ)) ≤ (K : Cardinal) := by
  obtain ⟨K, hK⟩ := gammaField_finite_phase_law_expLine hσ μ hμ
  exact ⟨K, one_le_rank_expLineBC μ hμ σ, hK⟩

end GaloisForLFunctions
