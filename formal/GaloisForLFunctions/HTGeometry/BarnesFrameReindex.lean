import GaloisForLFunctions.HTGeometry.BarnesSourceMero

/-!
# The Barnes source does not see the labelling of the frame

Reindexing the periods along a bijection of index types permutes the cone, and the cone product is a
product over the whole cone, so the product — and with it the entire germ, the field element and the
source — is unchanged.

This is what lets a ladder step, stated for an index type and its one-point deletion, be iterated
through subframes: the nested subtypes produced by repeated deletion are reindexed to a single-level
subtype without changing the object.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

open Bottcher

noncomputable section

attribute [local instance] barnesUnivDomain

local instance barnesReindexDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

variable {ι ι' : Type} [Fintype ι] [Nonempty ι] [Fintype ι'] [Nonempty ι']

omit [Nonempty ι] [Nonempty ι'] in
/-- Reindexing the frame reindexes the cone period. -/
theorem conePeriod_comp_equiv (e : ι' ≃ ι) (ω : ι → ℂ) (n : ι' → ℕ) :
    conePeriod (ω ∘ e) n = conePeriod ω (n ∘ e.symm) := by
  rw [conePeriod, conePeriod]
  refine Fintype.sum_equiv e _ _ fun i' => ?_
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

omit [Nonempty ι] [Nonempty ι'] in
/-- Reindexing the frame reindexes the cone factors. -/
theorem barnesConeFactor_comp_equiv (e : ι' ≃ ι) (ω : ι → ℂ) (n : ι' → ℕ) (z : ℂ) :
    barnesConeFactor (ω ∘ e) n z = barnesConeFactor ω (n ∘ e.symm) z := by
  have hcard : Fintype.card ι' = Fintype.card ι := Fintype.card_congr e
  have hzero : n = 0 ↔ n ∘ e.symm = 0 := by
    constructor
    · intro h
      funext i
      simp only [Function.comp_apply, h, Pi.zero_apply]
    · intro h
      funext i'
      have hi := congrFun h (e i')
      simpa using hi
  rw [barnesConeFactor, barnesConeFactor, conePeriod_comp_equiv, hcard]
  by_cases hn : n = 0
  · rw [if_pos hn, if_pos (hzero.mp hn)]
  · rw [if_neg hn, if_neg fun hc => hn (hzero.mpr hc)]

omit [Nonempty ι] [Nonempty ι'] in
/-- **The cone product does not see the labelling of the frame.** -/
theorem barnesConeProduct_comp_equiv (e : ι' ≃ ι) (ω : ι → ℂ) (z : ℂ) :
    barnesConeProduct (ω ∘ e) z = barnesConeProduct ω z := by
  have hEapply : ∀ n : ι' → ℕ, (Equiv.arrowCongr e (Equiv.refl ℕ)) n = n ∘ e.symm := fun _ => rfl
  calc barnesConeProduct (ω ∘ e) z
      = ∏' n : ι' → ℕ, barnesConeFactor ω ((Equiv.arrowCongr e (Equiv.refl ℕ)) n) z := by
        refine tprod_congr fun n => ?_
        rw [hEapply n]
        exact barnesConeFactor_comp_equiv e ω n z
    _ = ∏' m : ι → ℕ, barnesConeFactor ω m z :=
        (Equiv.arrowCongr e (Equiv.refl ℕ)).tprod_eq
          (fun m : ι → ℕ => barnesConeFactor ω m z)

/-- **The entire germ does not see the labelling of the frame.** -/
theorem barnesConeAnalytic_comp_equiv (e : ι' ≃ ι) (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (hω' : ∀ i', 0 < ((ω ∘ e) i').im) :
    barnesConeAnalytic (ω ∘ e) hω' = barnesConeAnalytic ω hω := by
  apply Subtype.ext
  show Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) (barnesConeProduct (ω ∘ e))
      = Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) (barnesConeProduct ω)
  rw [funext fun z => barnesConeProduct_comp_equiv e ω z]

/-- The source depends on the frame only, not on the chosen positivity proof. -/
theorem barnesSourceLogDerivMero_congr {ω₁ ω₂ : ι → ℂ} (h : ω₁ = ω₂)
    (h₁ : ∀ i, 0 < (ω₁ i).im) (h₂ : ∀ i, 0 < (ω₂ i).im) :
    barnesSourceLogDerivMero ω₁ h₁ = barnesSourceLogDerivMero ω₂ h₂ := by
  subst h
  rfl

/-- **The Barnes source does not see the labelling of the frame.** -/
theorem barnesSourceLogDerivMero_comp_equiv (e : ι' ≃ ι) (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (hω' : ∀ i', 0 < ((ω ∘ e) i').im) :
    barnesSourceLogDerivMero (ω ∘ e) hω' = barnesSourceLogDerivMero ω hω := by
  have hmero : barnesConeMero (ω ∘ e) hω' = barnesConeMero ω hω := by
    rw [barnesConeMero, barnesConeMero, barnesConeAnalytic_comp_equiv e ω hω hω']
  show Differential.logDeriv (barnesConeMero (ω ∘ e) hω')
      = Differential.logDeriv (barnesConeMero ω hω)
  rw [hmero]

end

end GaloisForLFunctions
