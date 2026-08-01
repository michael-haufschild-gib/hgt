import GaloisForLFunctions.HTGeometry.GammaJetDominantExists

/-!
# The ratio family of a finite Gamma-jet system

A ratio of jet shapes is a ratio of normalization factors with shifted argument degrees, so the
dominance limits of the digamma layer transfer verbatim: the ratio is `1` on equal data, and `0`
when the argument degree or the log degree is strictly dominated.

Together with the Gamma-exponent level and the existence of a dominant datum, a finite family of
Gamma-jet shapes has a dominant member and a full family of ratio limits — exactly the input of the
collapse from residues.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- A ratio of jet shapes is a ratio of normalization factors with shifted argument degrees. -/
theorem polyJetShape_ratio_eq (_hσ : 0 < σ) (a₁ dP₁ b₁ a₂ dP₂ b₂ : ℕ) :
    ∀ᶠ t : ℝ in atTop, polyJetShape σ a₁ dP₁ b₁ t / polyJetShape σ a₂ dP₂ b₂ t
      = jetNormFactor σ a₁ (dP₂ + b₁) t / jetNormFactor σ a₂ (dP₁ + b₂) t := by
  filter_upwards [eventually_vertLog_ne_zero, eventually_vertical_ne_zero σ] with t hL hs
  rw [polyJetShape, polyJetShape, jetNormFactor, jetNormFactor, pow_add, pow_add]
  field_simp

/-- Equal data give ratio `1`. -/
theorem tendsto_polyJetShape_ratio_one (hσ : 0 < σ) {a₁ dP₁ b₁ a₂ dP₂ b₂ : ℕ}
    (hdeg : dP₁ + b₂ = dP₂ + b₁) (hlog : a₁ = a₂) :
    Tendsto (fun t : ℝ => polyJetShape σ a₁ dP₁ b₁ t / polyJetShape σ a₂ dP₂ b₂ t)
      atTop (nhds 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [polyJetShape_ratio_eq hσ a₁ dP₁ b₁ a₂ dP₂ b₂,
    eventually_jetNormFactor_ne_zero hσ a₂ (dP₂ + b₁)] with t heq hne
  rw [heq, hlog, hdeg]
  exact (div_self hne).symm

/-- A strictly dominated argument degree gives ratio `0`. -/
theorem tendsto_polyJetShape_ratio_zero_of_deg (hσ : 0 < σ) {a₁ dP₁ b₁ a₂ dP₂ b₂ : ℕ}
    (hdeg : dP₁ + b₂ < dP₂ + b₁) :
    Tendsto (fun t : ℝ => polyJetShape σ a₁ dP₁ b₁ t / polyJetShape σ a₂ dP₂ b₂ t)
      atTop (nhds 0) := by
  refine (tendsto_jetNormFactor_ratio hσ (a₁ := a₁) (b₁ := dP₂ + b₁) (a₂ := a₂)
    (b₂ := dP₁ + b₂) (Or.inl hdeg)).congr' ?_
  filter_upwards [polyJetShape_ratio_eq hσ a₁ dP₁ b₁ a₂ dP₂ b₂] with t heq
  rw [heq]

/-- At equal argument degrees a strictly smaller log degree gives ratio `0`. -/
theorem tendsto_polyJetShape_ratio_zero_of_log (hσ : 0 < σ) {a₁ dP₁ b₁ a₂ dP₂ b₂ : ℕ}
    (hdeg : dP₁ + b₂ = dP₂ + b₁) (hlog : a₁ < a₂) :
    Tendsto (fun t : ℝ => polyJetShape σ a₁ dP₁ b₁ t / polyJetShape σ a₂ dP₂ b₂ t)
      atTop (nhds 0) := by
  refine (tendsto_jetNormFactor_ratio hσ (a₁ := a₁) (b₁ := dP₂ + b₁) (a₂ := a₂)
    (b₂ := dP₁ + b₂) (Or.inr ⟨hdeg, hlog⟩)).congr' ?_
  filter_upwards [polyJetShape_ratio_eq hσ a₁ dP₁ b₁ a₂ dP₂ b₂] with t heq
  rw [heq]

/-- **The ratio family of a finite Gamma-jet system.**  A finite nonempty family of Gamma-jet data
has a dominant member and a family of shape-ratio limits, equal to `1` at the dominant member. -/
theorem exists_dominant_with_shape_ratios (hσ : 0 < σ) {N : ℕ} (hN : 0 < N)
    (u a dP b : Fin N → ℕ) :
    ∃ (β : Fin N) (r : Fin N → ℂ),
      (∀ α : Fin N, Tendsto (fun t : ℝ =>
        gammaJetShape σ (u α) (a α) (dP α) (b α) t
          / gammaJetShape σ (u β) (a β) (dP β) (b β) t) atTop (nhds (r α)))
        ∧ r β = 1 := by
  classical
  obtain ⟨β, hβ⟩ := exists_dominant_gammaJet_index hN u a dP b
  refine ⟨β, fun α => if (u α = u β ∧ dP α + b β = dP β + b α ∧ a α = a β) then 1 else 0,
    fun α => ?_, ?_⟩
  · show Tendsto (fun t : ℝ => gammaJetShape σ (u α) (a α) (dP α) (b α) t
        / gammaJetShape σ (u β) (a β) (dP β) (b β) t) atTop
      (nhds (if (u α = u β ∧ dP α + b β = dP β + b α ∧ a α = a β) then 1 else 0))
    rcases hβ α with ⟨hu, hdeg, hlog⟩ | hγ | ⟨hu, hdeg⟩ | ⟨hu, hdeg, hlog⟩
    · rw [if_pos ⟨hu, hdeg, hlog⟩, hu]
      exact tendsto_gammaJetShape_ratio_of_gamma_eq hσ
        (tendsto_polyJetShape_ratio_one hσ hdeg hlog)
    · rw [if_neg (by rintro ⟨hu, -, -⟩; omega)]
      exact tendsto_gammaJetShape_ratio_of_gamma_lt hσ hγ
    · rw [if_neg (by rintro ⟨-, hd, -⟩; omega), hu]
      exact tendsto_gammaJetShape_ratio_of_gamma_eq hσ
        (tendsto_polyJetShape_ratio_zero_of_deg hσ hdeg)
    · rw [if_neg (by rintro ⟨-, -, hl⟩; omega), hu]
      exact tendsto_gammaJetShape_ratio_of_gamma_eq hσ
        (tendsto_polyJetShape_ratio_zero_of_log hσ hdeg hlog)
  · show (if (u β = u β ∧ dP β + b β = dP β + b β ∧ a β = a β) then (1 : ℂ) else 0) = 1
    rw [if_pos ⟨rfl, rfl, rfl⟩]

end GaloisForLFunctions
