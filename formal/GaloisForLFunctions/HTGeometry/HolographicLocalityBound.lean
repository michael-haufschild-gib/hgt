import GaloisForLFunctions.HTGeometry.LinearWidthThreeStepDetector
import Mathlib.Data.Set.PowersetCard

/-!
# Holographic compression versus membrane locality

A membrane channel with support `S` can mediate only the law pairs contained in `S`.  If every
two-plane must be visible and every membrane has valence at most `Δ`, double counting gives

`choose n 2 ≤ m * choose Δ 2`.

In particular, binary-local membranes require at least `choose n 2` channels.  The single-membrane
linear-width detector evades this bound only by giving its membrane valence `n`.  This formalizes
the exact locality cost hidden by the holographic compression.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I H : Type*} [Fintype I] [Fintype H]

/-- Every unordered law pair lies in the support of at least one membrane channel. -/
def MembranePairComplete (support : H → Finset I) : Prop :=
  ∀ s ∈ (Finset.univ : Finset I).powersetCard 2,
    ∃ h : H, s ⊆ support h

/-- Every membrane channel meets at most `Δ` law directions. -/
def MembraneValenceAtMost (support : H → Finset I) (Δ : ℕ) : Prop :=
  ∀ h : H, (support h).card ≤ Δ

/-- A principal bracket can be nonzero only if some membrane meets both of its directions. -/
def MembraneLocalPrincipalBrackets
    {K M : Type*} [Field K] [CharZero K]
    [AddCommGroup M] [Module K M] [LinearOrder I]
    (symbol : (I → K) →ₗ[K] Module.End K M)
    (support : H → Finset I) : Prop :=
  ∀ p : QuantumLawPair I,
    (¬ ∃ h : H, p.lower ∈ support h ∧ p.upper ∈ support h) →
      principalBracketPair symbol p = 0

/-- Independent coordinate brackets force pair completeness under a membrane-local support law. -/
theorem membranePairComplete_of_principalBracketPair_linearIndependent
    {K M : Type*} [Field K] [CharZero K]
    [AddCommGroup M] [Module K M] [LinearOrder I]
    (symbol : (I → K) →ₗ[K] Module.End K M)
    (support : H → Finset I)
    (hmembrane : MembraneLocalPrincipalBrackets symbol support)
    (hLI : LinearIndependent K (principalBracketPair symbol)) :
    MembranePairComplete support := by
  classical
  intro s hs
  have hcard : s.card = 2 := (Finset.mem_powersetCard.mp hs).2
  let e : Fin 2 ↪o I := s.orderEmbOfFin hcard
  have he : e 0 < e 1 := e.strictMono Fin.zero_lt_one
  let p : QuantumLawPair I := ⟨e 0, e 1, he⟩
  have hpresent : ∃ h : H, p.lower ∈ support h ∧ p.upper ∈ support h := by
    by_contra hnone
    exact hLI.ne_zero p (hmembrane p hnone)
  obtain ⟨h, hlower, hupper⟩ := hpresent
  refine ⟨h, ?_⟩
  intro i hi
  have hirange : i ∈ Set.range e := by
    rw [show Set.range e = s from Finset.range_orderEmbOfFin s hcard]
    exact hi
  obtain ⟨j, rfl⟩ := hirange
  fin_cases j
  · exact hlower
  · exact hupper

/-- **Holographic locality bound.**  Pair completeness and valence `Δ` force enough membrane
channels to cover all law-space two-planes. -/
theorem holographicLocality_choose_bound
    (support : H → Finset I) (Δ : ℕ)
    (hcomplete : MembranePairComplete support)
    (hlocal : MembraneValenceAtMost support Δ) :
    Nat.choose (Fintype.card I) 2 ≤
      Fintype.card H * Nat.choose Δ 2 := by
  classical
  let pairs : H → Finset (Finset I) := fun h ↦ (support h).powersetCard 2
  have hcover :
      (Finset.univ : Finset I).powersetCard 2 ⊆
        (Finset.univ : Finset H).biUnion pairs := by
    intro s hs
    obtain ⟨h, hsub⟩ := hcomplete s hs
    apply Finset.mem_biUnion.mpr
    refine ⟨h, Finset.mem_univ h, ?_⟩
    exact Finset.mem_powersetCard.mpr ⟨hsub, (Finset.mem_powersetCard.mp hs).2⟩
  calc
    Nat.choose (Fintype.card I) 2 =
        ((Finset.univ : Finset I).powersetCard 2).card := by
      rw [Finset.card_powersetCard, Finset.card_univ]
    _ ≤ ((Finset.univ : Finset H).biUnion pairs).card :=
      Finset.card_le_card hcover
    _ ≤ Fintype.card H * Nat.choose Δ 2 := by
      simpa [pairs] using
        (Finset.card_biUnion_le_card_mul
          (Finset.univ : Finset H) pairs (Nat.choose Δ 2) (by
            intro h _hh
            rw [Finset.card_powersetCard]
            exact Nat.choose_le_choose 2 (hlocal h)))

/-- **Local faithful-principal-symbol bound.**  A membrane-local detector with independent
coordinate brackets obeys the same compression/locality inequality. -/
theorem localFaithfulPrincipalSymbol_choose_bound
    {K M : Type*} [Field K] [CharZero K]
    [AddCommGroup M] [Module K M] [LinearOrder I]
    (symbol : (I → K) →ₗ[K] Module.End K M)
    (support : H → Finset I) (Δ : ℕ)
    (hmembrane : MembraneLocalPrincipalBrackets symbol support)
    (hLI : LinearIndependent K (principalBracketPair symbol))
    (hlocal : MembraneValenceAtMost support Δ) :
    Nat.choose (Fintype.card I) 2 ≤
      Fintype.card H * Nat.choose Δ 2 :=
  holographicLocality_choose_bound support Δ
    (membranePairComplete_of_principalBracketPair_linearIndependent
      symbol support hmembrane hLI)
    hlocal

/-- **Binary-local horizon bound.**  If every membrane sees at most two directions, one distinct
membrane channel per law pair is unavoidable. -/
theorem binaryLocal_holographic_membrane_lower_bound
    (support : H → Finset I)
    (hcomplete : MembranePairComplete support)
    (hlocal : MembraneValenceAtMost support 2) :
    Nat.choose (Fintype.card I) 2 ≤ Fintype.card H := by
  simpa using holographicLocality_choose_bound support 2 hcomplete hlocal

/-- Including lower and upper boundary copies, binary locality forces quadratic total coordinate
width. -/
theorem binaryLocal_holographic_total_width_lower_bound
    (support : H → Finset I)
    (hcomplete : MembranePairComplete support)
    (hlocal : MembraneValenceAtMost support 2) :
    2 * Fintype.card I + Nat.choose (Fintype.card I) 2 ≤
      2 * Fintype.card I + Fintype.card H :=
  Nat.add_le_add_left
    (binaryLocal_holographic_membrane_lower_bound support hcomplete hlocal)
    (2 * Fintype.card I)

/-- The sharp binary-local construction uses one membrane indexed by each two-element subset. -/
def completeBinaryMembraneSupport
    (h : Set.powersetCard I 2) : Finset I :=
  h

omit [Fintype I] in
theorem completeBinaryMembraneSupport_valence :
    MembraneValenceAtMost (completeBinaryMembraneSupport (I := I)) 2 := by
  intro h
  simp [completeBinaryMembraneSupport]

theorem completeBinaryMembraneSupport_pairComplete :
    MembranePairComplete (completeBinaryMembraneSupport (I := I)) := by
  classical
  intro s hs
  exact ⟨⟨s, (Finset.mem_powersetCard.mp hs).2⟩, Finset.Subset.rfl⟩

/-- The number of channels in the sharp binary-local construction is exactly `choose n 2`. -/
theorem completeBinaryMembrane_card :
    Fintype.card (Set.powersetCard I 2) = Nat.choose (Fintype.card I) 2 := by
  simpa only [Nat.card_eq_fintype_card] using
    (Set.powersetCard.card I 2)

end

end GaloisForLFunctions.HTGeometry
