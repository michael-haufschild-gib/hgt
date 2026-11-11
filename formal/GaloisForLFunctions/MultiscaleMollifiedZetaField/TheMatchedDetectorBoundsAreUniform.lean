import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheMatchedDetectorHasItsBlockBounds

/-!
# One bound for every admissible block

Apply the block estimates to the filter of all admissible quadruples
`(U,a,v,d)`, ordered only by the upper height `U`. Its eventual bounds
therefore have one constant and one height threshold for every block
and every displacement in the gate strip.
-/

open Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- One linear energy bound holds simultaneously on every block above the low-height split. -/
theorem exists_uniform_matchedDetectorBlockEnergy_bound :
    ∃ C > 0, ∀ᶠ U : ℝ in atTop, ∀ a v d : ℝ,
      U ^ (53 / 100 : ℝ) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
      13 / 10 ≤ d * Real.log U → d * Real.log (U - 1) ≤ 13 / 10 →
      matchedDetectorBlockEnergy (shortLevinsonCutoff U) d (1 / Real.log U) a v ≤ C * a := by
  let B := {x : ℝ × ℝ × ℝ × ℝ //
    1 < x.1 ∧ (x.1 ^ (53 / 100 : ℝ) ≤ x.2.1 ∧ x.2.1 ≤ x.2.2.1 ∧
      x.2.2.1 ≤ 2 * x.2.1 ∧ x.2.2.1 ≤ x.1) ∧
    (13 / 10 ≤ x.2.2.2 * Real.log x.1 ∧ x.2.2.2 * Real.log (x.1 - 1) ≤ 13 / 10)}
  let U : B → ℝ := fun b => b.1.1
  let a : B → ℝ := fun b => b.1.2.1
  let v : B → ℝ := fun b => b.1.2.2.1
  let d : B → ℝ := fun b => b.1.2.2.2
  let l : Filter B := Filter.comap U atTop
  have hU : Tendsto U l atTop := Filter.tendsto_comap
  have hblock : ∀ᶠ b in l, U b ^ (53 / 100 : ℝ) ≤ a b ∧ a b ≤ v b ∧
      v b ≤ 2 * a b ∧ v b ≤ U b := Filter.Eventually.of_forall (fun b => b.2.2.1)
  have hgate : ∀ᶠ b in l, 13 / 10 ≤ d b * Real.log (U b) ∧
      d b * Real.log (U b - 1) ≤ 13 / 10 := Filter.Eventually.of_forall (fun b => b.2.2.2)
  obtain ⟨C, hC, hb⟩ := exists_eventually_matchedDetectorBlockEnergy_le hU hblock hgate
  have he : ∀ᶠ X : ℝ in atTop, ∀ b : B, U b = X →
      matchedDetectorBlockEnergy (shortLevinsonCutoff (U b)) (d b)
        (1 / Real.log (U b)) (a b) (v b) ≤ C * a b := Filter.eventually_comap.mp hb
  refine ⟨C, hC, ?_⟩
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with X hX hX1
  intro A V D hlow hAV hV2 hVX hg0 hg1
  exact hX ⟨(X, A, V, D), hX1, ⟨hlow, hAV, hV2, hVX⟩, hg0, hg1⟩ rfl

/-- The sharp high-block estimate is uniform in the gate displacement and both endpoints. -/
theorem eventually_uniform_matchedDetectorBlockEnergy_high_bound {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ U : ℝ in atTop, ∀ a v d : ℝ,
      U ^ (53 / 100 : ℝ) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
      13 / 10 ≤ d * Real.log U → d * Real.log (U - 1) ≤ 13 / 10 →
      δ * U / Real.log U ≤ a →
      matchedDetectorBlockEnergy (shortLevinsonCutoff U) d (1 / Real.log U) a v ≤
        (18 / 5) * (v - a) + ε * a := by
  let B := {x : ℝ × ℝ × ℝ × ℝ //
    1 < x.1 ∧ (x.1 ^ (53 / 100 : ℝ) ≤ x.2.1 ∧ x.2.1 ≤ x.2.2.1 ∧
      x.2.2.1 ≤ 2 * x.2.1 ∧ x.2.2.1 ≤ x.1) ∧
    (13 / 10 ≤ x.2.2.2 * Real.log x.1 ∧ x.2.2.2 * Real.log (x.1 - 1) ≤ 13 / 10) ∧
    δ * x.1 / Real.log x.1 ≤ x.2.1}
  let U : B → ℝ := fun b => b.1.1
  let a : B → ℝ := fun b => b.1.2.1
  let v : B → ℝ := fun b => b.1.2.2.1
  let d : B → ℝ := fun b => b.1.2.2.2
  let l : Filter B := Filter.comap U atTop
  have hU : Tendsto U l atTop := Filter.tendsto_comap
  have hblock : ∀ᶠ b in l, U b ^ (53 / 100 : ℝ) ≤ a b ∧ a b ≤ v b ∧
      v b ≤ 2 * a b ∧ v b ≤ U b := Filter.Eventually.of_forall (fun b => b.2.2.1)
  have hgate : ∀ᶠ b in l, 13 / 10 ≤ d b * Real.log (U b) ∧
      d b * Real.log (U b - 1) ≤ 13 / 10 := Filter.Eventually.of_forall (fun b => b.2.2.2.1)
  have hhigh : ∀ᶠ b in l, δ * U b / Real.log (U b) ≤ a b :=
    Filter.Eventually.of_forall (fun b => b.2.2.2.2)
  have hb := eventually_matchedDetectorBlockEnergy_high_le hU hblock hgate hδ hhigh hε
  have he : ∀ᶠ X : ℝ in atTop, ∀ b : B, U b = X →
      matchedDetectorBlockEnergy (shortLevinsonCutoff (U b)) (d b)
        (1 / Real.log (U b)) (a b) (v b) ≤ (18 / 5) * (v b - a b) + ε * a b :=
    Filter.eventually_comap.mp hb
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with X hX hX1
  intro A V D hlow hAV hV2 hVX hg0 hg1 hhigh
  exact hX ⟨(X, A, V, D), hX1, ⟨hlow, hAV, hV2, hVX⟩, ⟨hg0, hg1⟩, hhigh⟩ rfl

end GaloisForLFunctions.MultiscaleMollifiedZetaField
