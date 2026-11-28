import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.ParamsHeightRankConstant

/-! Family closure permits a smaller exponent range and allows
the current family-class membership in the closed conclusion. -/

noncomputable section

namespace WindowedLandauTheory.MainNotions

open WindowedLandauTheory.BasicNotions

theorem closed_eps_le_one (𝒞 : FamClass) : Closed 𝒞 fun {eps} _ _ => eps ≤ 1 :=
  ⟨1, one_pos, fun _ _ hle => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => hle⟩⟩

theorem closed_of_mem {𝒞 : FamClass} {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop}
    (h : Closed 𝒞 fun Fm CH => 𝒞 Fm → P Fm CH) : Closed 𝒞 P := by
  obtain ⟨ε, hε, h⟩ := h
  refine ⟨ε, hε, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := h e he hle
  exact ⟨K, fun Fm CH hc hL => hK Fm CH hc hL hc⟩

end WindowedLandauTheory.MainNotions

#print axioms WindowedLandauTheory.MainNotions.closed_eps_le_one
#print axioms WindowedLandauTheory.MainNotions.closed_of_mem
