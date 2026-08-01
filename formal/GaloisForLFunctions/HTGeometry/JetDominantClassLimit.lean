import GaloisForLFunctions.HTGeometry.JetNormalizationDominance

/-!
# Only the dominant class survives the normalization

In a finite combination of jet monomials, each carrying its own normalization datum, dividing by the
dominant datum leaves the monomials of that datum untouched and sends every other one to zero.

So the normalized combination converges to the sum of the leading constants over the dominant class
— the last step of the algebraic-logarithmic residue: the limit is visible, and it vanishes exactly
when the leading constants of that class cancel.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- The normalization factor is eventually nonzero on a vertical line. -/
theorem eventually_jetNormFactor_ne_zero (_hσ : 0 < σ) (a b : ℕ) :
    ∀ᶠ t : ℝ in atTop, jetNormFactor σ a b t ≠ 0 := by
  filter_upwards [eventually_vertLog_ne_zero, eventually_vertical_ne_zero σ] with t hL hs
  rw [jetNormFactor]
  exact div_ne_zero (pow_ne_zero _ hL) (pow_ne_zero _ hs)

/-- **The dominant class carries the limit.**  In a finite combination of normalized jet monomials,
each rescaled by its own datum relative to the dominant one, the terms of the dominant class keep
their leading constants and all others vanish. -/
theorem tendsto_sum_normJet_dominant (hσ : 0 < σ) {n N : ℕ} (d : Fin N → ℂ)
    (e : Fin N → Fin (n + 1) → ℕ) (a b : Fin N → ℕ) (aβ bβ : ℕ)
    (hdom : ∀ α : Fin N, (a α = aβ ∧ b α = bβ) ∨ (bβ < b α ∨ (bβ = b α ∧ a α < aβ))) :
    Tendsto (fun t : ℝ => ∑ α : Fin N, d α * (∏ j : Fin (n + 1), (normJet σ (j : ℕ) t) ^ (e α j))
        * (jetNormFactor σ (a α) (b α) t / jetNormFactor σ aβ bβ t))
      atTop (nhds (∑ α ∈ Finset.univ.filter (fun α : Fin N => a α = aβ ∧ b α = bβ),
        d α * ∏ j : Fin (n + 1), (jetLeadingConst (j : ℕ)) ^ (e α j))) := by
  classical
  have hterm : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      d α * (∏ j : Fin (n + 1), (normJet σ (j : ℕ) t) ^ (e α j))
        * (jetNormFactor σ (a α) (b α) t / jetNormFactor σ aβ bβ t)) atTop
      (nhds (if (a α = aβ ∧ b α = bβ) then
        d α * ∏ j : Fin (n + 1), (jetLeadingConst (j : ℕ)) ^ (e α j) else 0)) := by
    intro α
    rcases hdom α with ⟨haa, hbb⟩ | hlt
    · rw [if_pos ⟨haa, hbb⟩]
      have hprod := (tendsto_prod_normJet hσ (e α)).const_mul (d α)
      refine hprod.congr' ?_
      filter_upwards [eventually_jetNormFactor_ne_zero hσ aβ bβ] with t ht
      rw [haa, hbb, div_self ht, mul_one]
    · rw [if_neg (by
        rintro ⟨haa, hbb⟩
        rcases hlt with h | ⟨h1, h2⟩
        · omega
        · omega)]
      have hratio := tendsto_jetNormFactor_ratio (σ := σ) hσ (a₁ := a α) (b₁ := b α)
        (a₂ := aβ) (b₂ := bβ) hlt
      have hprod := (tendsto_prod_normJet hσ (e α)).const_mul (d α)
      have := hprod.mul hratio
      rwa [mul_zero] at this
  rw [Finset.sum_filter]
  exact tendsto_finsetSum (Finset.univ : Finset (Fin N)) (fun α _ => hterm α)

end GaloisForLFunctions
