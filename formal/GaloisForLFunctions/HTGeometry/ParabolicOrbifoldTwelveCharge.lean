import GaloisForLFunctions.HTGeometry.NonautonomousFirstOrderTailSymbol

/-!
# The universal twelve-charge of scalar parabolic orbifold tails

The complete scalar-tail classification leaves exactly the six parabolic orbifold
signatures on the sphere.  Their finite cone holonomy orders divide `12`.  Consequently the
translation-invariant current on the affine universal cover always has a rational twelfth tensor
power downstairs, independently of which parabolic signature occurs at a phase.

There is also a sharper protocol-specific law.  Orbifold-cover descent injects the rotational
holonomy at one phase into the next, so its order forms a divisibility chain in
`{1, 2, 3, 4, 6}`.  Such a chain eventually freezes.  The stable order itself is a fixed tensor
charge for the whole tower and is at most `6`; `12` is only the least charge chosen uniformly
before the tower is known.

This file records the classification surface and its universal charge without introducing a flow
or a numerical experiment.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Every finite rotational order occurring in a parabolic orbifold divides the universal tensor
charge `12`.  Explicit witnesses are used rather than a numerical search. -/
theorem parabolicHolonomyOrder_dvd_twelve (order : ℕ)
    (horder : order = 1 ∨ order = 2 ∨ order = 3 ∨ order = 4 ∨ order = 6) :
    order ∣ 12 := by
  rcases horder with h | h | h | h | h
  · subst order
    exact ⟨12, rfl⟩
  · subst order
    exact ⟨6, rfl⟩
  · subst order
    exact ⟨4, rfl⟩
  · subst order
    exact ⟨3, rfl⟩
  · subst order
    exact ⟨2, rfl⟩

/-- The six zero-Euler orbifold signatures with underlying Riemann sphere. -/
inductive ParabolicSphereSignature where
  | twoCusps
  | twoTwosCusp
  | fourTwos
  | twoThreeSix
  | twoFourFour
  | threeThrees
  deriving DecidableEq

/-- Finite cone orders of a parabolic sphere signature; cusps are recorded separately. -/
def ParabolicSphereSignature.finiteConeOrders : ParabolicSphereSignature → List ℕ
  | .twoCusps => []
  | .twoTwosCusp => [2, 2]
  | .fourTwos => [2, 2, 2, 2]
  | .twoThreeSix => [2, 3, 6]
  | .twoFourFour => [2, 4, 4]
  | .threeThrees => [3, 3, 3]

/-- Number of punctures of a parabolic sphere signature. -/
def ParabolicSphereSignature.cuspCount : ParabolicSphereSignature → ℕ
  | .twoCusps => 2
  | .twoTwosCusp => 1
  | .fourTwos | .twoThreeSix | .twoFourFour | .threeThrees => 0

/-- Order of the rotational holonomy acting on the translation-invariant current upstairs. -/
def ParabolicSphereSignature.holonomyOrder : ParabolicSphereSignature → ℕ
  | .twoCusps => 1
  | .twoTwosCusp | .fourTwos => 2
  | .threeThrees => 3
  | .twoFourFour => 4
  | .twoThreeSix => 6

/-- Whether the Euclidean universal cover has a lattice of rank two rather than a cusp. -/
def ParabolicSphereSignature.isCompact : ParabolicSphereSignature → Bool
  | .twoCusps | .twoTwosCusp => false
  | .fourTwos | .twoThreeSix | .twoFourFour | .threeThrees => true

theorem ParabolicSphereSignature.holonomyOrder_mem
    (signature : ParabolicSphereSignature) :
    signature.holonomyOrder = 1 ∨ signature.holonomyOrder = 2 ∨
      signature.holonomyOrder = 3 ∨ signature.holonomyOrder = 4 ∨
      signature.holonomyOrder = 6 := by
  cases signature <;> simp [ParabolicSphereSignature.holonomyOrder]

theorem ParabolicSphereSignature.holonomyOrder_pos
    (signature : ParabolicSphereSignature) : 0 < signature.holonomyOrder := by
  cases signature <;> simp [ParabolicSphereSignature.holonomyOrder]

theorem ParabolicSphereSignature.holonomyOrder_le_six
    (signature : ParabolicSphereSignature) : signature.holonomyOrder ≤ 6 := by
  cases signature <;> simp [ParabolicSphereSignature.holonomyOrder]

/-- Rotational order and compact/cuspidal type jointly determine a parabolic sphere signature. -/
theorem ParabolicSphereSignature.eq_of_holonomyOrder_eq_isCompact_eq
    {source target : ParabolicSphereSignature}
    (hholonomy : source.holonomyOrder = target.holonomyOrder)
    (hcompact : source.isCompact = target.isCompact) :
    source = target := by
  cases source <;> cases target <;>
    simp [ParabolicSphereSignature.holonomyOrder,
      ParabolicSphereSignature.isCompact] at hholonomy hcompact ⊢

/-- Within a fixed compact or cuspidal type, the divisibility poset of Euclidean rotational
holonomy has height two.  Consequently a compatible parabolic tower cannot undergo two strict
holonomy enlargements. -/
theorem parabolicHolonomyOrder_no_two_strict_enlargements
    (s₀ s₁ s₂ : ParabolicSphereSignature)
    (hcompact₀₁ : s₀.isCompact = s₁.isCompact)
    (hcompact₁₂ : s₁.isCompact = s₂.isCompact)
    (hdiv₀₁ : s₀.holonomyOrder ∣ s₁.holonomyOrder)
    (hdiv₁₂ : s₁.holonomyOrder ∣ s₂.holonomyOrder) :
    s₀.holonomyOrder = s₁.holonomyOrder ∨
      s₁.holonomyOrder = s₂.holonomyOrder := by
  cases s₀ <;> cases s₁ <;> cases s₂ <;>
    simp [ParabolicSphereSignature.holonomyOrder,
      ParabolicSphereSignature.isCompact] at hcompact₀₁ hcompact₁₂ hdiv₀₁ hdiv₁₂ ⊢

/-- Every finite local holonomy order on a parabolic sphere divides the universal charge `12`. -/
theorem ParabolicSphereSignature.coneOrder_dvd_twelve
    (signature : ParabolicSphereSignature) (order : ℕ)
    (horder : order ∈ signature.finiteConeOrders) :
    order ∣ 12 := by
  apply parabolicHolonomyOrder_dvd_twelve
  cases signature <;> simp [ParabolicSphereSignature.finiteConeOrders] at horder ⊢
  all_goals omega

/-- A single tensor charge works simultaneously for any phasewise choice of parabolic signature. -/
theorem parabolicSphereTower_has_universal_twelve_charge
    (signature : ℕ → ParabolicSphereSignature) :
    ∀ i order, order ∈ (signature i).finiteConeOrders → order ∣ 12 := by
  intro i order horder
  exact (signature i).coneOrder_dvd_twelve order horder

/-- A phasewise holonomy inclusion composes through every finite interval of the tower. -/
theorem dvd_holonomyOrder_of_le
    (signature : ℕ → ParabolicSphereSignature)
    (hdiv : ∀ i, (signature i).holonomyOrder ∣ (signature (i + 1)).holonomyOrder)
    {i j : ℕ} (hij : i ≤ j) :
    (signature i).holonomyOrder ∣ (signature j).holonomyOrder := by
  induction j, hij using Nat.le_induction with
  | base => exact dvd_rfl
  | succ j _ ih => exact ih.trans (hdiv j)

/-- Rotational holonomy can increase only through divisibility and therefore freezes after a
finite prefix.  This is the finite-poset core of topological phase freezing. -/
theorem parabolicHolonomyOrder_eventually_constant
    (signature : ℕ → ParabolicSphereSignature)
    (hdiv : ∀ i, (signature i).holonomyOrder ∣ (signature (i + 1)).holonomyOrder) :
    ∃ N, ∀ n, N ≤ n →
      (signature n).holonomyOrder = (signature N).holonomyOrder := by
  let h : ℕ → ℕ := fun i => (signature i).holonomyOrder
  have hmono : Monotone h := by
    apply monotone_nat_of_le_succ
    intro i
    exact Nat.le_of_dvd (ParabolicSphereSignature.holonomyOrder_pos _) (hdiv i)
  have hanti : Antitone (fun i => 6 - h i) := by
    intro i j hij
    exact Nat.sub_le_sub_left (hmono hij) 6
  obtain ⟨N, hN⟩ := WellFoundedLT.antitone_chain_condition hanti
  refine ⟨N, fun n hn => ?_⟩
  have heq : 6 - h n = 6 - h N := (hN n hn).symm
  have hnle : h n ≤ 6 := ParabolicSphereSignature.holonomyOrder_le_six _
  have hNle : h N ≤ 6 := ParabolicSphereSignature.holonomyOrder_le_six _
  have : h n = h N := by omega
  simpa [h] using this

/-- Every compatible parabolic tower has a protocol-specific fixed charge in
`{1, 2, 3, 4, 6}`.  This improves the universal but non-sharp charge `12` once the tower is known. -/
theorem parabolicSphereTower_has_protocol_charge
    (signature : ℕ → ParabolicSphereSignature)
    (hdiv : ∀ i, (signature i).holonomyOrder ∣ (signature (i + 1)).holonomyOrder) :
    ∃ N charge,
      charge = (signature N).holonomyOrder ∧
      charge ≤ 6 ∧ charge ∣ 12 ∧
      (∀ i, (signature i).holonomyOrder ∣ charge) ∧
      ∀ n, N ≤ n → (signature n).holonomyOrder = charge := by
  obtain ⟨N, hN⟩ := parabolicHolonomyOrder_eventually_constant signature hdiv
  refine ⟨N, (signature N).holonomyOrder, rfl,
    ParabolicSphereSignature.holonomyOrder_le_six _, ?_, ?_, hN⟩
  · exact parabolicHolonomyOrder_dvd_twelve _
      (ParabolicSphereSignature.holonomyOrder_mem _)
  · intro i
    by_cases hi : i ≤ N
    · exact dvd_holonomyOrder_of_le signature hdiv hi
    · rw [hN i (by omega)]

/-- If an orbifold covering preserves compact versus cuspidal type, stabilization of rotational
holonomy freezes the complete parabolic signature. -/
theorem parabolicSphereSignature_eventually_constant
    (signature : ℕ → ParabolicSphereSignature)
    (hdiv : ∀ i, (signature i).holonomyOrder ∣ (signature (i + 1)).holonomyOrder)
    (hcompact : ∀ i, (signature i).isCompact = (signature (i + 1)).isCompact) :
    ∃ N, ∀ n, N ≤ n → signature n = signature N := by
  obtain ⟨N, hN⟩ := parabolicHolonomyOrder_eventually_constant signature hdiv
  refine ⟨N, fun n hn => ParabolicSphereSignature.eq_of_holonomyOrder_eq_isCompact_eq
    (hN n hn) ?_⟩
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n _ ih => exact (hcompact n).symm.trans ih

end GaloisForLFunctions.HTGeometry
