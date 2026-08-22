import GaloisForLFunctions.HTGeometry.Octonion.Sylvester

namespace GaloisForLFunctions.HTGeometry.Octonion.RealOctonion

noncomputable section

/-- Three copies of the one-dimensional octonion module. -/
structure ThreeOctonions where
  first : RealOctonion
  second : RealOctonion
  third : RealOctonion

@[ext] theorem ThreeOctonions.ext {x y : ThreeOctonions}
    (hfirst : x.first = y.first) (hsecond : x.second = y.second)
    (hthird : x.third = y.third) : x = y := by
  cases x
  cases y
  cases hfirst
  cases hsecond
  cases hthird
  rfl

/-- The real block-diagonal resolvent with three left-multiplication blocks. -/
def diagonalThreeResolvent (s q₁ q₂ q₃ : RealOctonion) :
    ThreeOctonions → ThreeOctonions := fun x =>
  ⟨resolventDifference s q₁ x.first,
    resolventDifference s q₂ x.second,
    resolventDifference s q₃ x.third⟩

/-- A three-block diagonal resolvent is bijective precisely when every block is. -/
theorem diagonalThreeResolvent_bijective_iff
    (s q₁ q₂ q₃ : RealOctonion) :
    Function.Bijective (diagonalThreeResolvent s q₁ q₂ q₃) ↔
      Function.Bijective (sylvesterDifferenceLinear s q₁) ∧
      Function.Bijective (sylvesterDifferenceLinear s q₂) ∧
      Function.Bijective (sylvesterDifferenceLinear s q₃) := by
  constructor
  · intro h
    constructor
    · constructor
      · intro x y hxy
        change resolventDifference s q₁ x = resolventDifference s q₁ y at hxy
        have hblock : diagonalThreeResolvent s q₁ q₂ q₃ ⟨x, 0, 0⟩ =
            diagonalThreeResolvent s q₁ q₂ q₃ ⟨y, 0, 0⟩ := by
          apply ThreeOctonions.ext
          · exact hxy
          · simp [diagonalThreeResolvent]
          · simp [diagonalThreeResolvent]
        exact congrArg ThreeOctonions.first (h.1 hblock)
      · intro y
        obtain ⟨x, hx⟩ := h.2 ⟨y, 0, 0⟩
        have hfirst := congrArg ThreeOctonions.first hx
        change (sylvesterDifferenceLinear s q₁) x.first = y at hfirst
        exact ⟨x.first, hfirst⟩
    constructor
    · constructor
      · intro x y hxy
        change resolventDifference s q₂ x = resolventDifference s q₂ y at hxy
        have hblock : diagonalThreeResolvent s q₁ q₂ q₃ ⟨0, x, 0⟩ =
            diagonalThreeResolvent s q₁ q₂ q₃ ⟨0, y, 0⟩ := by
          apply ThreeOctonions.ext
          · simp [diagonalThreeResolvent]
          · exact hxy
          · simp [diagonalThreeResolvent]
        exact congrArg ThreeOctonions.second (h.1 hblock)
      · intro y
        obtain ⟨x, hx⟩ := h.2 ⟨0, y, 0⟩
        have hsecond := congrArg ThreeOctonions.second hx
        change (sylvesterDifferenceLinear s q₂) x.second = y at hsecond
        exact ⟨x.second, hsecond⟩
    · constructor
      · intro x y hxy
        change resolventDifference s q₃ x = resolventDifference s q₃ y at hxy
        have hblock : diagonalThreeResolvent s q₁ q₂ q₃ ⟨0, 0, x⟩ =
            diagonalThreeResolvent s q₁ q₂ q₃ ⟨0, 0, y⟩ := by
          apply ThreeOctonions.ext
          · simp [diagonalThreeResolvent]
          · simp [diagonalThreeResolvent]
          · exact hxy
        exact congrArg ThreeOctonions.third (h.1 hblock)
      · intro y
        obtain ⟨x, hx⟩ := h.2 ⟨0, 0, y⟩
        have hthird := congrArg ThreeOctonions.third hx
        change (sylvesterDifferenceLinear s q₃) x.third = y at hthird
        exact ⟨x.third, hthird⟩
  · rintro ⟨h₁, h₂, h₃⟩
    constructor
    · intro x y hxy
      apply ThreeOctonions.ext
      · apply h₁.1
        change resolventDifference s q₁ x.first = resolventDifference s q₁ y.first
        exact congrArg ThreeOctonions.first hxy
      · apply h₂.1
        change resolventDifference s q₂ x.second = resolventDifference s q₂ y.second
        exact congrArg ThreeOctonions.second hxy
      · apply h₃.1
        change resolventDifference s q₃ x.third = resolventDifference s q₃ y.third
        exact congrArg ThreeOctonions.third hxy
    · intro y
      obtain ⟨x₁, hx₁⟩ := h₁.2 y.first
      obtain ⟨x₂, hx₂⟩ := h₂.2 y.second
      obtain ⟨x₃, hx₃⟩ := h₃.2 y.third
      refine ⟨⟨x₁, x₂, x₃⟩, ?_⟩
      apply ThreeOctonions.ext
      · change resolventDifference s q₁ x₁ = y.first
        exact hx₁
      · change resolventDifference s q₂ x₂ = y.second
        exact hx₂
      · change resolventDifference s q₃ x₃ = y.third
        exact hx₃

/-- The real spectrum of a three-block diagonal left-multiplication operator. -/
def diagonalThreeRealSpectrum (q₁ q₂ q₃ : RealOctonion) : Set RealOctonion :=
  {s | ¬ Function.Bijective (diagonalThreeResolvent s q₁ q₂ q₃)}

/-- The three-block real spectrum is the union of the three source conjugacy spheres.
This is the structural content of Example 8.9. -/
theorem diagonalThreeRealSpectrum_eq_union_conjugacySphere
    (q₁ q₂ q₃ : RealOctonion) :
    diagonalThreeRealSpectrum q₁ q₂ q₃ =
      conjugacySphere q₁ ∪ conjugacySphere q₂ ∪ conjugacySphere q₃ := by
  ext s
  unfold diagonalThreeRealSpectrum
  simp only [Set.mem_setOf_eq, Set.mem_union]
  rw [diagonalThreeResolvent_bijective_iff,
    sylvesterDifferenceLinear_bijective_iff_not_mem_conjugacySphere,
    sylvesterDifferenceLinear_bijective_iff_not_mem_conjugacySphere,
    sylvesterDifferenceLinear_bijective_iff_not_mem_conjugacySphere]
  tauto

end
end GaloisForLFunctions.HTGeometry.Octonion.RealOctonion
