import GaloisForLFunctions.ArithmeticIndexDescent.ArithmeticSectionsHaveOnlyPresentationRadicals

/-!
# Orthogonal removal of a narrow arithmetic section space

Every ambient real test has a unique actual section in a prescribed finite narrow
section span with the same mixed Weil pairings. Redundant coefficients do not
affect this section. Subtracting it is orthogonal removal inside the original
completed Weil form, and its residual Gram is the exact Schur complement.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri

variable {ι : Type*} [Fintype ι] {N : ℕ} (hN : 1 ≤ N)
  {w : ℝ} (hw0 : 0 < w) (hw : w ≤ fullSectionRatio * atomSpacing N)
  (f : ι → arithmeticSectionTests N w)

/-- A finite narrow section span has a unique actual Weil-orthogonal projection of every test. -/
theorem arithmeticSection_exists_unique_projection (g : realTests) :
    ∃! p : realTests,
      (∃ c : ι → ℝ, p = realTestSynthesis (fun i => (f i).1) c) ∧
        ∀ i, realWeilForm (f i).1 (g - p) = 0 := by
  obtain ⟨c, hc⟩ := arithmeticSection_exists_mixed_lift hN hw0 hw f g
  let p := realTestSynthesis (fun i => (f i).1) c
  have hp (i : ι) : realWeilForm (f i).1 (g - p) = 0 := by
    rw [map_sub, ← realWeilMixed_mulVec]
    exact sub_eq_zero.mpr (congrFun hc i).symm
  refine ⟨p, ⟨⟨c, rfl⟩, hp⟩, ?_⟩
  rintro q ⟨⟨d, rfl⟩, hq⟩
  apply arithmeticSection_lift_unique_test hN hw0 hw f
  funext i
  have hd := hq i
  rw [map_sub, ← realWeilMixed_mulVec] at hd
  exact (sub_eq_zero.mp hd).symm.trans (congrFun hc i).symm

/-- The actual projected section, independent of any nonunique coefficient lift. -/
def arithmeticSectionProjection (g : realTests) : realTests :=
  Classical.choose (arithmeticSection_exists_unique_projection hN hw0 hw f g)

theorem arithmeticSectionProjection_spec (g : realTests) :
    (∃ c : ι → ℝ,
      arithmeticSectionProjection hN hw0 hw f g = realTestSynthesis (fun i => (f i).1) c) ∧
    ∀ i, realWeilForm (f i).1 (g - arithmeticSectionProjection hN hw0 hw f g) = 0 :=
  (Classical.choose_spec (arithmeticSection_exists_unique_projection hN hw0 hw f g)).1

theorem arithmeticSectionProjection_unique (g p : realTests)
    (hp : ∃ c : ι → ℝ, p = realTestSynthesis (fun i => (f i).1) c)
    (horth : ∀ i, realWeilForm (f i).1 (g - p) = 0) :
    p = arithmeticSectionProjection hN hw0 hw f g :=
  (Classical.choose_spec (arithmeticSection_exists_unique_projection hN hw0 hw f g)).2
    p ⟨hp, horth⟩

/-- Every old section combination annihilates the new residual. -/
theorem arithmeticSectionProjection_orthogonal (c : ι → ℝ) (g : realTests) :
    realWeilForm (realTestSynthesis (fun i => (f i).1) c)
      (g - arithmeticSectionProjection hN hw0 hw f g) = 0 := by
  rw [realWeilForm_synthesis_left]
  simp only [(arithmeticSectionProjection_spec hN hw0 hw f g).2,
    mul_zero, Finset.sum_const_zero]

theorem arithmeticSectionProjection_reproduces (c : ι → ℝ) :
    arithmeticSectionProjection hN hw0 hw f (realTestSynthesis (fun i => (f i).1) c) =
      realTestSynthesis (fun i => (f i).1) c := by
  symm
  apply arithmeticSectionProjection_unique hN hw0 hw f _ _ ⟨c, rfl⟩
  intro i
  rw [sub_self, map_zero]

theorem arithmeticSectionProjection_idempotent (g : realTests) :
    arithmeticSectionProjection hN hw0 hw f (arithmeticSectionProjection hN hw0 hw f g) =
      arithmeticSectionProjection hN hw0 hw f g := by
  obtain ⟨c, hc⟩ := (arithmeticSectionProjection_spec hN hw0 hw f g).1
  rw [hc, arithmeticSectionProjection_reproduces]

/-- The residual identity retains the entire completed form, with both pole moments. -/
theorem arithmeticSectionProjection_residual_pair (g h : realTests) :
    realWeilForm (g - arithmeticSectionProjection hN hw0 hw f g)
      (h - arithmeticSectionProjection hN hw0 hw f h) =
    realWeilForm g h - realWeilForm (arithmeticSectionProjection hN hw0 hw f g)
      (arithmeticSectionProjection hN hw0 hw f h) := by
  obtain ⟨c, hc⟩ := (arithmeticSectionProjection_spec hN hw0 hw f g).1
  obtain ⟨d, hd⟩ := (arithmeticSectionProjection_spec hN hw0 hw f h).1
  have hleft := arithmeticSectionProjection_orthogonal hN hw0 hw f c h
  have hright := arithmeticSectionProjection_orthogonal hN hw0 hw f d g
  rw [← hc, map_sub] at hleft
  rw [← hd, map_sub, realWeilForm_symm _ g,
    realWeilForm_symm _ (arithmeticSectionProjection hN hw0 hw f g)] at hright
  simp only [map_sub, LinearMap.sub_apply]
  linarith only [hleft, hright]

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.arithmeticSection_exists_unique_projection
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.arithmeticSectionProjection_residual_pair
