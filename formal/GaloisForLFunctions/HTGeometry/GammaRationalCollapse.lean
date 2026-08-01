import GaloisForLFunctions.HTGeometry.GammaTupleProjectiveBoundary
import GaloisForLFunctions.HTGeometry.RecurrenceCollapseAlmostPeriodic

/-!
# The recurrence collapse for Gamma-rational coefficients

A finite differential relation whose coefficients are Gamma-rational has, after normalizing by a
valuation-minimal coefficient, all coefficient ratios convergent: the vertical decay of `Γ` makes the
ratio of two such coefficients a power of a vanishing quantity times a ratio of polynomial values.
The monomials return to themselves along the Bohr return times of the solution, and the dominant
coefficient is eventually nonzero because its numerator and denominator polynomials do not vanish at
the origin.

So the relation collapses to a nontrivial constant-coefficient relation — eq. (27) → (29) — with no
analytic input left open on the coefficient side.  The limit coefficient vector is the explicit
residue vector `gammaRatioLimit`, which does not depend on the line on which the collapse is taken.
-/

open Filter Topology

namespace GaloisForLFunctions

open _root_.HTGeometry

variable {n : ℕ}

/-- The limit of the normalized coefficient vector of a Gamma-rational relation: the residue
quotient at the origin on the valuation-minimal indices, and zero elsewhere. -/
noncomputable def gammaRatioLimit (P Q : Fin n → Polynomial ℂ) (u v : Fin n → ℕ)
    (β : Fin n) : Fin n → ℂ := fun α =>
  if u α + v β = u β + v α then
    (P α).eval 0 * (Q β).eval 0 / ((Q α).eval 0 * (P β).eval 0)
  else 0


/-- The normalization of the limit vector at the valuation-minimal index. -/
theorem gammaRatioLimit_self (P Q : Fin n → Polynomial ℂ) (u v : Fin n → ℕ) (β : Fin n)
    (hP : (P β).eval 0 ≠ 0) (hQ : (Q β).eval 0 ≠ 0) : gammaRatioLimit P Q u v β β = 1 := by
  rw [gammaRatioLimit, if_pos rfl]
  field_simp

/-- **Eq. (27) → (29) for Gamma-rational coefficients, with the limit vector named.**  A finite
differential relation whose coefficients are Gamma-rational, normalized by a valuation-minimal
member, collapses along the Bohr return times to the autonomous relation with coefficient vector
`gammaRatioLimit`. -/
theorem recurrence_collapse_gamma_rational_explicit {σ : ℝ} (hσ : 0 < σ)
    (F M : Fin n → ℂ → ℂ) (P Q : Fin n → Polynomial ℂ) (u v : Fin n → ℕ) (β : Fin n)
    (hQ0 : ∀ α, (Q α).eval 0 ≠ 0) (hP0 : ∀ α, (P α).eval 0 ≠ 0)
    (hF : ∀ (α : Fin n) (t : ℝ),
      F α ((σ : ℂ) + (t : ℂ) * Complex.I)
        = ((Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (u α)
            * (P α).eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)))
          / ((Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (v α)
            * (Q α).eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))))
    (hrel : ∀ s : ℂ, ∑ α, F α s * M α s = 0)
    (hMcont : ∀ α, Continuous fun t : ℝ => M α ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hMap : ∀ α, IsBohrAlmostPeriodic fun t : ℝ => M α ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hmin : ∀ α, u β + v α ≤ u α + v β) :
    (∑ α, gammaRatioLimit P Q u v β α * M α (σ : ℂ) = 0) ∧ gammaRatioLimit P Q u v β β = 1 := by
  classical
  set γ : ℝ → ℂ := fun t => Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) with hγdef
  have hγ : Tendsto γ atTop (nhdsWithin 0 {(0 : ℂ)}ᶜ) := Gamma_vertical_tendsto_nhdsWithin_zero hσ
  have hcoeff : ∀ α : Fin n, Tendsto
      (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
        / F β ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds (gammaRatioLimit P Q u v β α)) := by
    intro α
    have hrw : (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
        / F β ((σ : ℂ) + (t : ℂ) * Complex.I))
        = fun t : ℝ => ((γ t) ^ (u α) * (P α).eval (γ t)) / ((γ t) ^ (v α) * (Q α).eval (γ t))
          / (((γ t) ^ (u β) * (P β).eval (γ t)) / ((γ t) ^ (v β) * (Q β).eval (γ t))) := by
      funext t
      rw [hF α t, hF β t]
    rw [hrw]
    simp only [gammaRatioLimit]
    by_cases heq : u α + v β = u β + v α
    · simp only [if_pos heq]
      exact ratio_tendsto_residue hγ (P α) (Q α) (P β) (Q β) (u α) (v α) (u β) (v β)
        (hQ0 α) (hP0 β) heq
    · simp only [if_neg heq]
      have hlt : u β + v α < u α + v β := lt_of_le_of_ne (hmin α) (fun h => heq h.symm)
      obtain ⟨k, hk⟩ : ∃ k : ℕ, u α + v β = u β + v α + k := ⟨u α + v β - (u β + v α), by omega⟩
      refine ratio_tendsto_zero hγ (P α) (Q α) (P β) (Q β) (u α) (v α) (u β) (v β) k
        (hQ0 α) (hP0 β) hk ?_
      omega
  have hFβ : ∀ᶠ t : ℝ in atTop, F β ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    have hne : ∀ᶠ t in atTop, γ t ≠ 0 := hγ.eventually self_mem_nhdsWithin
    have hR : Tendsto (fun t => (P β).eval (γ t)) atTop (nhds ((P β).eval 0)) :=
      eval_tendsto hγ (P β)
    have hRne : ∀ᶠ t in atTop, (P β).eval (γ t) ≠ 0 := hR.eventually_ne (hP0 β)
    have hS : Tendsto (fun t => (Q β).eval (γ t)) atTop (nhds ((Q β).eval 0)) :=
      eval_tendsto hγ (Q β)
    have hSne : ∀ᶠ t in atTop, (Q β).eval (γ t) ≠ 0 := hS.eventually_ne (hQ0 β)
    filter_upwards [hne, hRne, hSne] with t ht htR htS
    rw [hF β t]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ ht) htR)
      (mul_ne_zero (pow_ne_zero _ ht) htS)
  exact recurrence_collapse_of_bohr_return F M β (σ : ℂ) (gammaRatioLimit P Q u v β)
    hrel hMcont hMap hFβ hcoeff

/-- **Eq. (27) → (29) for Gamma-rational coefficients.**  A finite differential relation whose
coefficients are Gamma-rational, normalized by a valuation-minimal member, collapses along the Bohr
return times to an autonomous relation. -/
theorem recurrence_collapse_gamma_rational {σ : ℝ} (hσ : 0 < σ)
    (F M : Fin n → ℂ → ℂ) (R S : Fin n → Polynomial ℂ) (u v : Fin n → ℕ) (β : Fin n)
    (hS0 : ∀ α, (S α).eval 0 ≠ 0) (hR0 : ∀ α, (R α).eval 0 ≠ 0)
    (hF : ∀ (α : Fin n) (t : ℝ),
      F α ((σ : ℂ) + (t : ℂ) * Complex.I)
        = ((Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (u α)
            * (R α).eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)))
          / ((Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (v α)
            * (S α).eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))))
    (hrel : ∀ s : ℂ, ∑ α, F α s * M α s = 0)
    (hMcont : ∀ α, Continuous fun t : ℝ => M α ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hMap : ∀ α, IsBohrAlmostPeriodic fun t : ℝ => M α ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hmin : ∀ α, u β + v α ≤ u α + v β) :
    ∃ d : Fin n → ℂ, (∑ α, d α * M α (σ : ℂ) = 0) ∧ d β = 1 :=
  ⟨gammaRatioLimit R S u v β, recurrence_collapse_gamma_rational_explicit hσ F M R S u v β
    hS0 hR0 hF hrel hMcont hMap hmin⟩

end GaloisForLFunctions
