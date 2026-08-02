import GaloisForLFunctions.HTGeometry.GammaShiftClassLaw
import GaloisForLFunctions.HTGeometry.GammaRationalWitness

/-!
# The shifted law is inhabited

The exponential `e^{μ z}` solves `Γ(s+λ)·Φ′ − μΓ(s+λ)·Φ = 0`, a relation whose two coefficients are
shifted Gamma monomials with a genuinely nonzero shift.  Every hypothesis of the shifted finite
phase law is met, and the conclusion is a rank between `1` and a finite bound.

So the law of a finite real Gamma-shift field is a statement about a nonempty class, and the class
contains objects whose coefficients are not constants.
-/

open Filter Set Topology Function
open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The shifted finite phase law is inhabited.**  For every abscissa and every shift keeping the
translated line in the right half plane, the exponential satisfies a relation whose coefficients are
shifted Gamma monomials, and its rank is between `1` and a finite bound. -/
theorem gammaShift_law_witness {σ lam : ℝ} (hσ : 0 < σ) (hlam : 0 < σ + lam) (μ : ℝ)
    (hμ : μ ≠ 0) :
    ∃ K : ℕ, 1 ≤ Module.rank ℤ (bohrHullFrequencies (expLineBC μ σ))
      ∧ Module.rank ℤ (bohrHullFrequencies (expLineBC μ σ)) ≤ (K : Cardinal) := by
  classical
  set f : ℝ →ᵇ ℂ := expLineBC μ σ with hfdef
  have hR : (0 : ℝ) < 1 := one_pos
  have hΦ : DifferentiableOn ℂ (expLine μ) (verticalStrip σ 1) :=
    (differentiable_expLine μ).differentiableOn
  have hap : IsStripAlmostPeriodic (expLine μ) σ 1 := isStripAlmostPeriodic_expLine μ _ _
  set e : Fin 2 → Fin 2 → ℕ := ![![0, 1], ![1, 0]] with hedef
  have he : Function.Injective e := by
    intro α β hαβ
    fin_cases α <;> fin_cases β <;> simp_all
  -- the two coefficient functions
  set F : Fin 2 → ℂ → ℂ :=
    ![fun s => Complex.Gamma (s + (lam : ℂ)),
      fun s => -(μ : ℂ) * Complex.Gamma (s + (lam : ℂ))] with hFdef
  set lamf : Fin 1 → ℝ := ![lam] with hlamf
  set cc : Fin 2 → Fin 1 → ℂ := ![![1], ![-(μ : ℂ)]] with hccdef
  set ee : Fin 2 → Fin 1 → Fin 1 → ℕ := ![![![1]], ![![1]]] with heedef
  set ones : Fin 2 → Fin 1 → Polynomial ℂ := ![![1], ![1]] with honesdef
  set bb : Fin 2 → Fin 1 → ℤ := ![![0], ![0]] with hbbdef
  have hcases2 : ∀ α : Fin 2, α = 0 ∨ α = 1 := by decide
  have hcases1 : ∀ i : Fin 1, i = 0 := by decide
  have hlamk : ∀ k : Fin 1, 0 < σ + lamf k := by
    intro k
    rw [hcases1 k]
    simpa [hlamf] using hlam
  have hcc : ∀ (α : Fin 2) (i : Fin 1), cc α i ≠ 0 := by
    intro α i
    rw [hcases1 i]
    rcases hcases2 α with h | h <;> subst h <;> simp [hccdef, hμ]
  have hones : ∀ (α : Fin 2) (i : Fin 1), ones α i ≠ 0 := by
    intro α i
    rw [hcases1 i]
    rcases hcases2 α with h | h <;> subst h <;> simp [honesdef]
  -- the single monomial of each coefficient survives
  have hclass : ∀ (α : Fin 2) (β : Fin 1), (∀ i : Fin 1,
      (multiDegree (ee α i) = multiDegree (ee α β)
        ∧ multiExponent lamf (ee α i) (ones α i) (ones α i)
          = multiExponent lamf (ee α β) (ones α β) (ones α β)
        ∧ bb α i = bb α β)
      ∨ ShiftShapeDominates (multiDegree (ee α β))
          (multiExponent lamf (ee α β) (ones α β) (ones α β)) (bb α β)
          (multiDegree (ee α i)) (multiExponent lamf (ee α i) (ones α i) (ones α i)) (bb α i)) →
    (∑ i ∈ multiClass lamf (ee α) (ones α) (ones α) (bb α) β,
      cc α i * ((ones α i).leadingCoeff / (ones α i).leadingCoeff)) ≠ 0 := by
    intro α β _
    have hβ : β = 0 := hcases1 β
    subst hβ
    have hfilter : multiClass lamf (ee α) (ones α) (ones α) (bb α) 0 = {0} := by
      refine Finset.ext fun i => ?_
      rw [hcases1 i]
      simp [multiClass]
    rw [hfilter, Finset.sum_singleton]
    rcases hcases2 α with h | h <;> subst h <;>
      simp [hccdef, honesdef, hμ]
  -- the coefficients on the line
  have hF : ∀ (α : Fin 2) (t : ℝ), F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      = multiMonomialSum σ lamf (cc α) (ee α) (ones α) (ones α) (bb α) t := by
    intro α t
    have hval : ((σ : ℂ) + (t : ℂ) * Complex.I) + (lam : ℂ)
        = (((σ + lam : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by
      push_cast
      ring
    rcases hcases2 α with h | h <;> subst h <;>
      simp [hFdef, multiMonomialSum, hccdef, heedef, honesdef, hbbdef, hlamf, gammaLine,
        hval]
  -- the relation
  have hrel : ∀ s : ℂ, ∑ α, F α s
      * ∏ i : Fin 2, (iteratedDeriv (i : ℕ) (expLine μ) s) ^ (e α i) = 0 := by
    intro s
    rw [Fin.sum_univ_two]
    simp only [hedef, hFdef, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one,
      iteratedDeriv_expLine]
    ring
  -- the line restriction of the exponential
  have hf : ∀ x : ℝ, f x = expLine μ ((σ : ℂ) + (x : ℂ) * Complex.I) := by
    intro x
    rw [hfdef, expLineBC_apply]
  have hline : _root_.HTGeometry.IsBohrAlmostPeriodic
      (fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    isBohrAlmostPeriodic_line hR hap
  have hcont : Continuous fun x : ℝ => f x := by
    have hfun : (fun x : ℝ => f x)
        = fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I) := funext hf
    rw [hfun]
    exact continuous_line_restriction hR hΦ
  have hapf : _root_.HTGeometry.IsBohrAlmostPeriodic fun x : ℝ => f x := by
    have hfun : (fun x : ℝ => f x)
        = fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I) := funext hf
    rw [hfun]
    exact hline
  obtain ⟨K, hK⟩ := rank_finite_of_gammaShiftClass (rr := 1/4) (ρ := 1/4) hσ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hR hΦ hap e he F
    lamf hlamk cc hcc ee ones ones hones hones bb hclass hF hrel hf
    (uniformContinuous_of_isBohrAlmostPeriodic hcont hapf)
    (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hcont hapf)
  exact ⟨K, one_le_rank_expLineBC μ hμ σ, hK⟩

end

end GaloisForLFunctions.HTGeometry
