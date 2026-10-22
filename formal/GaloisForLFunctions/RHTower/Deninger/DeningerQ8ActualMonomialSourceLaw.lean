import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualArtinEulerProduct
import GaloisForLFunctions.RHTower.SerreQ8MonomialSourceLaw

/-!
# The source-selected monomial law for the root-number-minus-one Q8 field

The documented field
`ℚ(√5, √41, √((5 + √5) * (41 + 6 * √41)))` is the field whose Artin sign is
reported as `-1` in Shankar--Södergren--Templier.  Its literal `√41` carrier
selects an index-two quartic Galois subgroup.  This file proves, without an
epsilon-factor assertion, that the actual two-dimensional Artin representation
is induction of the primitive order-four character of that stabilizer and that
the complementary Galois orientation exchanges the two channels.

This is the exact algebraic input required before an Artin-to-Hecke local
epsilon calculation can be attached to the source-selected field.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions

local notation "K3" => deningerQ8RootNumberNegOneTopField

noncomputable local instance deningerQ8ActualMonomialGalFintype : Fintype Gal(K3/ℚ) :=
  Fintype.ofEquiv _ deningerQ8RootNumberNegOne_galoisEquivQ8.toEquiv.symm

/-- The literal quartic source subgroup of the documented Q8 field. -/
def deningerQ8ActualCyclicSubgroup : Subgroup Gal(K3/ℚ) :=
  q8CyclicSubgroup.comap deningerQ8RootNumberNegOne_galoisEquivQ8.toMonoidHom

/-- Transport of the literal `C₄` subgroup through the actual field's Galois equivalence. -/
noncomputable def deningerQ8ActualCyclicSubgroupEquiv :
    deningerQ8ActualCyclicSubgroup ≃* q8CyclicSubgroup where
  toFun g := ⟨deningerQ8RootNumberNegOne_galoisEquivQ8 g, g.2⟩
  invFun h := ⟨deningerQ8RootNumberNegOne_galoisEquivQ8.symm h, by
    change deningerQ8RootNumberNegOne_galoisEquivQ8
      (deningerQ8RootNumberNegOne_galoisEquivQ8.symm h) ∈ q8CyclicSubgroup
    simpa using h.2⟩
  left_inv g := by
    apply Subtype.ext
    simp
  right_inv h := by
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul _ _ _

/-- The primitive quartic character on the actual source-selected Galois subgroup. -/
def deningerQ8ActualCyclicSubgroupCharacter :
    LinearCharacter deningerQ8ActualCyclicSubgroup :=
  q8CyclicSubgroupCharacter.comp deningerQ8ActualCyclicSubgroupEquiv.toMonoidHom

noncomputable local instance deningerQ8ActualInducedFiniteDimensional :
    FiniteDimensional ℂ (Representation.IndV deningerQ8ActualCyclicSubgroup.subtype
      (linearCharacterRepresentation deningerQ8ActualCyclicSubgroupCharacter)) :=
  by infer_instance

theorem deningerQ8ActualCyclicSubgroup_index : deningerQ8ActualCyclicSubgroup.index = 2 := by
  have hcard := deningerQ8ActualCyclicSubgroup.card_mul_index
  have hsubcard : Nat.card deningerQ8ActualCyclicSubgroup = 4 := by
    calc
      Nat.card deningerQ8ActualCyclicSubgroup = Nat.card q8CyclicSubgroup :=
        Nat.card_congr deningerQ8ActualCyclicSubgroupEquiv.toEquiv
      _ = 4 := q8CyclicSubgroup_card
  rw [hsubcard] at hcard
  have hgalcard : Nat.card Gal(K3/ℚ) = 8 := by
    calc
      Nat.card Gal(K3/ℚ) = Nat.card (QuaternionGroup 2) :=
        Nat.card_congr deningerQ8RootNumberNegOne_galoisEquivQ8.toEquiv
      _ = 8 := by
        rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [hgalcard] at hcard
  omega

/-- `√41` literally selects the quartic source: its stabilizer is neither an abstract subgroup
nor a choice of orientation. -/
theorem deningerQ8ActualCyclicSubgroup_eq_stabilizer_topY :
    deningerQ8ActualCyclicSubgroup =
      MulAction.stabilizer (Gal(K3/ℚ)) deningerQ8RootNumberNegOneTopY := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    rw [MulAction.mem_stabilizer_iff]
    change g deningerQ8RootNumberNegOneTopY = deningerQ8RootNumberNegOneTopY
    change deningerQ8RootNumberNegOne_galoisEquivQ8 g ∈ q8CyclicSubgroup at hg
    rcases hg with ⟨i, hi⟩
    have hgi : g = deningerQ8RootNumberNegOne_galoisEquivQ8.symm (q8CyclicEmbedding i) := by
      apply deningerQ8RootNumberNegOne_galoisEquivQ8.injective
      simpa using hi.symm
    rw [hgi]
    change q8IAlgPow (Multiplicative.toAdd i) deningerQ8RootNumberNegOneTopY =
      deningerQ8RootNumberNegOneTopY
    exact q8IAlgPow_topY _
  · intro hg
    rw [MulAction.mem_stabilizer_iff] at hg
    change g deningerQ8RootNumberNegOneTopY = deningerQ8RootNumberNegOneTopY at hg
    change deningerQ8RootNumberNegOne_galoisEquivQ8 g ∈ q8CyclicSubgroup
    rcases hq : deningerQ8RootNumberNegOne_galoisEquivQ8 g with i | i
    · refine ⟨Multiplicative.ofAdd i, ?_⟩
      change q8CyclicEmbedding (Multiplicative.ofAdd i) = QuaternionGroup.a i
      rfl
    · exfalso
      have hg' := hg
      rw [← deningerQ8RootNumberNegOne_galoisEquivQ8.symm_apply_apply g, hq] at hg'
      change q8JAlgEquiv (q8IAlgPow i deningerQ8RootNumberNegOneTopY) =
        deningerQ8RootNumberNegOneTopY at hg'
      rw [q8IAlgPow_topY, q8JAlgEquiv_apply, q8J_topY] at hg'
      apply q8TopY_ne_zero
      rw [eq_comm] at hg'
      have hsum : deningerQ8RootNumberNegOneTopY + deningerQ8RootNumberNegOneTopY = 0 :=
        eq_neg_iff_add_eq_zero.mp hg'
      have htwice : (2 : K3) * deningerQ8RootNumberNegOneTopY = 0 := by
        rw [two_mul]
        exact hsum
      exact (mul_eq_zero.mp htwice).resolve_left (by
        letI : CharZero K3 :=
          charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
        norm_num)

/-- The actual source carrier has exactly the two reflected Galois orientations. -/
theorem deningerQ8ActualTopY_orbit_eq_two_point :
    MulAction.orbit (Gal(K3/ℚ)) deningerQ8RootNumberNegOneTopY =
      ({deningerQ8RootNumberNegOneTopY, -deningerQ8RootNumberNegOneTopY} : Set K3) := by
  ext z
  constructor
  · rintro ⟨g, rfl⟩
    change g deningerQ8RootNumberNegOneTopY ∈
      ({deningerQ8RootNumberNegOneTopY, -deningerQ8RootNumberNegOneTopY} : Set K3)
    rcases hq : deningerQ8RootNumberNegOne_galoisEquivQ8 g with i | i
    · left
      rw [← deningerQ8RootNumberNegOne_galoisEquivQ8.symm_apply_apply g, hq]
      change q8IAlgPow i deningerQ8RootNumberNegOneTopY = deningerQ8RootNumberNegOneTopY
      exact q8IAlgPow_topY _
    · right
      rw [← deningerQ8RootNumberNegOne_galoisEquivQ8.symm_apply_apply g, hq]
      change q8JAlgEquiv (q8IAlgPow i deningerQ8RootNumberNegOneTopY) =
        -deningerQ8RootNumberNegOneTopY
      rw [q8IAlgPow_topY, q8JAlgEquiv_apply, q8J_topY]
  · intro hz
    rcases hz with rfl | rfl
    · exact ⟨1, by simp⟩
    · refine ⟨deningerQ8RootNumberNegOne_galoisEquivQ8.symm (QuaternionGroup.xa 0), ?_⟩
      change q8JAlgEquiv (q8IAlgPow (0 : ZMod 4) deningerQ8RootNumberNegOneTopY) =
        -deningerQ8RootNumberNegOneTopY
      rw [q8IAlgPow_topY, q8JAlgEquiv_apply, q8J_topY]

/-- First-channel intertwining for the actual field's source-selected subgroup. -/
def deningerQ8ActualFirstChannelIntertwining :
    (linearCharacterRepresentation deningerQ8ActualCyclicSubgroupCharacter).IntertwiningMap
      ((deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8).comp
        deningerQ8ActualCyclicSubgroup.subtype) where
  toLinearMap := q8FirstChannelLinear
  isIntertwining' h := by
    apply LinearMap.ext
    intro z
    change q8FirstChannelLinear ((deningerQ8ActualCyclicSubgroupCharacter h : ℂ) * z) =
      deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8 h
        (q8FirstChannelLinear z)
    change q8FirstChannelLinear
        ((q8CyclicSubgroupCharacter (deningerQ8ActualCyclicSubgroupEquiv h) : ℂ) * z) =
      deningerQ8Representation (deningerQ8ActualCyclicSubgroupEquiv h) (q8FirstChannelLinear z)
    exact LinearMap.congr_fun
      (q8FirstChannelIntertwining.isIntertwining'
        (deningerQ8ActualCyclicSubgroupEquiv h)) z

noncomputable def deningerQ8ActualMonomialToArtin :
    Rep.ind deningerQ8ActualCyclicSubgroup.subtype
      (Rep.of (linearCharacterRepresentation deningerQ8ActualCyclicSubgroupCharacter)) ⟶
        Rep.of (deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8) :=
  (Rep.indResHomEquiv deningerQ8ActualCyclicSubgroup.subtype
    (Rep.of (linearCharacterRepresentation deningerQ8ActualCyclicSubgroupCharacter))
    (Rep.of (deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8))).symm
      (Rep.ofHom deningerQ8ActualFirstChannelIntertwining)

theorem deningerQ8ActualMonomialToArtin_mk_one (z : ℂ) :
    deningerQ8ActualMonomialToArtin.hom
      (Representation.IndV.mk deningerQ8ActualCyclicSubgroup.subtype
        (linearCharacterRepresentation deningerQ8ActualCyclicSubgroupCharacter) 1 z) =
      (z, 0) := by
  have h := (Rep.indResHomEquiv deningerQ8ActualCyclicSubgroup.subtype
    (Rep.of (linearCharacterRepresentation deningerQ8ActualCyclicSubgroupCharacter))
    (Rep.of (deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8))).apply_symm_apply
      (Rep.ofHom deningerQ8ActualFirstChannelIntertwining)
  have hz := congrArg (fun f => f.hom z) h
  simpa [deningerQ8ActualMonomialToArtin, Rep.indResHomEquiv,
    deningerQ8ActualFirstChannelIntertwining, q8FirstChannelLinear] using hz

theorem deningerQ8ActualMonomialToArtin_surjective :
    Function.Surjective deningerQ8ActualMonomialToArtin.hom := by
  intro v
  rcases v with ⟨x, y⟩
  let e : Representation.IndV deningerQ8ActualCyclicSubgroup.subtype
      (linearCharacterRepresentation deningerQ8ActualCyclicSubgroupCharacter) :=
    Representation.IndV.mk deningerQ8ActualCyclicSubgroup.subtype
      (linearCharacterRepresentation deningerQ8ActualCyclicSubgroupCharacter) 1 1
  let g0 : Gal(K3/ℚ) := deningerQ8RootNumberNegOne_galoisEquivQ8.symm (QuaternionGroup.xa 0)
  let xe := (Rep.ind deningerQ8ActualCyclicSubgroup.subtype
      (Rep.of (linearCharacterRepresentation deningerQ8ActualCyclicSubgroupCharacter))).ρ g0 e
  refine ⟨x • e + y • xe, ?_⟩
  rw [map_add, map_smul, map_smul]
  have he : deningerQ8ActualMonomialToArtin.hom e = (1, 0) := by
    exact deningerQ8ActualMonomialToArtin_mk_one 1
  have hxe := Rep.hom_comm_apply deningerQ8ActualMonomialToArtin g0 e
  change deningerQ8ActualMonomialToArtin.hom xe =
    deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8 g0
      (deningerQ8ActualMonomialToArtin.hom e) at hxe
  rw [he, deningerQ8ArtinRepresentation_apply] at hxe
  change deningerQ8ActualMonomialToArtin.hom xe = deningerQ8Representation
    (deningerQ8RootNumberNegOne_galoisEquivQ8
      (deningerQ8RootNumberNegOne_galoisEquivQ8.symm (QuaternionGroup.xa 0))) (1, 0) at hxe
  rw [deningerQ8RootNumberNegOne_galoisEquivQ8.apply_symm_apply,
    deningerQ8Representation_xa_zero_apply] at hxe
  have hxe' : deningerQ8ActualMonomialToArtin.hom xe = (0, 1) := by
    simpa [deningerQuaternionTransitionK] using hxe
  rw [he, hxe']
  ext <;> simp

theorem deningerQ8ActualCyclicSubgroup_induced_finrank :
    Module.finrank ℂ (Representation.IndV deningerQ8ActualCyclicSubgroup.subtype
      (linearCharacterRepresentation deningerQ8ActualCyclicSubgroupCharacter)) = 2 := by
  rw [induced_finrank_eq_index_mul, deningerQ8ActualCyclicSubgroup_index]
  norm_num

theorem deningerQ8ActualMonomialToArtin_injective :
    Function.Injective deningerQ8ActualMonomialToArtin.hom := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr
    deningerQ8ActualMonomialToArtin_surjective
  calc
    Module.finrank ℂ (Representation.IndV deningerQ8ActualCyclicSubgroup.subtype
        (linearCharacterRepresentation deningerQ8ActualCyclicSubgroupCharacter)) = 2 :=
      deningerQ8ActualCyclicSubgroup_induced_finrank
    _ = Module.finrank ℂ Q8Carrier := deningerQ8ArtinRepresentation_finrank.symm

/-- Exact induction identity on the source-authenticated Q8 Galois group. -/
noncomputable def deningerQ8ActualInducedRepresentationEquiv :
    (Representation.ind deningerQ8ActualCyclicSubgroup.subtype
      (linearCharacterRepresentation deningerQ8ActualCyclicSubgroupCharacter)).Equiv
        (deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8) :=
  Representation.Equiv.mk
    (LinearEquiv.ofBijective deningerQ8ActualMonomialToArtin.hom
      ⟨deningerQ8ActualMonomialToArtin_injective, deningerQ8ActualMonomialToArtin_surjective⟩)
    (by
      intro g
      apply LinearMap.ext
      intro v
      exact Rep.hom_comm_apply deningerQ8ActualMonomialToArtin g v)

/-- **Actual-field monomial source law.** The documented field's symplectic Artin
representation is induced from a degree-one order-four character of the literal stabilizer of
`√41`; the nontrivial orbit point is `-√41`. -/
theorem deningerQ8ActualArtinRepresentation_exists_induced_from_topY_stabilizer :
    ∃ ψ : LinearCharacter (MulAction.stabilizer (Gal(K3/ℚ)) deningerQ8RootNumberNegOneTopY),
      Nonempty ((Representation.ind
        (MulAction.stabilizer (Gal(K3/ℚ)) deningerQ8RootNumberNegOneTopY).subtype
        (linearCharacterRepresentation ψ)).Equiv
        (deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8)) := by
  rw [← deningerQ8ActualCyclicSubgroup_eq_stabilizer_topY]
  exact ⟨deningerQ8ActualCyclicSubgroupCharacter, ⟨deningerQ8ActualInducedRepresentationEquiv⟩⟩

/-- The literal cyclic orientation acts by the primitive quartic character and its inverse. -/
theorem deningerQ8ActualArtinRepresentation_cyclic_source_law
    (i : ZMod 4) (x y : ℂ) :
    deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8
      (deningerQ8RootNumberNegOne_galoisEquivQ8.symm (QuaternionGroup.a i)) (x, y) =
      ((q8OrderFourCharacter (Multiplicative.ofAdd i) : ℂ) * x,
        (q8OrderFourCharacter (Multiplicative.ofAdd (-i)) : ℂ) * y) := by
  rw [deningerQ8ArtinRepresentation_apply,
    deningerQ8RootNumberNegOne_galoisEquivQ8.apply_symm_apply]
  change deningerQ8RepresentationLinear (QuaternionGroup.a i) (x, y) = _
  rw [deningerQ8RepresentationLinear_apply]
  change q8Ipow i (x, y) = _
  ext <;> simp only [q8Ipow]
  · rw [q8OrderFourCharacter_apply]
  · rw [q8OrderFourCharacter_neg_apply]

/-- The other Galois orientation exchanges the two literal quartic channels. -/
theorem deningerQ8ActualArtinRepresentation_reflection_source_law
    (i : ZMod 4) (x y : ℂ) :
    deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8
      (deningerQ8RootNumberNegOne_galoisEquivQ8.symm (QuaternionGroup.xa i)) (x, y) =
      (-((q8OrderFourCharacter (Multiplicative.ofAdd (-i)) : ℂ) * y),
        (q8OrderFourCharacter (Multiplicative.ofAdd i) : ℂ) * x) := by
  rw [deningerQ8ArtinRepresentation_apply,
    deningerQ8RootNumberNegOne_galoisEquivQ8.apply_symm_apply]
  change deningerQ8RepresentationLinear (QuaternionGroup.xa i) (x, y) = _
  rw [deningerQ8RepresentationLinear_apply]
  change deningerQuaternionTransitionK (q8Ipow i (x, y)) = _
  ext <;> simp only [q8Ipow, deningerQuaternionTransitionK]
  · rw [q8OrderFourCharacter_neg_apply]
  · rw [q8OrderFourCharacter_apply]

end

end RHTower
