import GaloisForLFunctions.RHTower.SerreQ8ArtinGaloisRealization
import GaloisForLFunctions.RHTower.ArtinInducedDegree

/-!
# The literal monomial source law for Serre's `Q₈` Artin representation

Serre's two-dimensional symplectic representation is not merely labelled by a quaternionic
group.  On its literal cyclic `C₄` source it is the pair of an order-four character and its
inverse, and the complementary quaternionic coset exchanges those two channels.  The leaf also
proves that this is the standard induction from that literal `C₄` source, rather than merely an
eigenvalue decomposition, first for `Q₈` and then on Serre's actual Galois group.  This is the
source-level reduction required before any Artin-to-Hecke epsilon-factor transport can be stated.

The leaf deliberately proves no root-number assertion: local epsilon-factor theory remains the
unpaid arithmetic input.
-/

namespace RHTower

noncomputable section

/-- The unit `i`, viewed as the generator of the literal order-four source character. -/
def q8IUnit : ℂˣ := Units.mk0 Complex.I (by norm_num)

/-- The primitive order-four character of the cyclic source `C₄`. -/
def q8OrderFourCharacter : Multiplicative (ZMod 4) →* ℂˣ where
  toFun i := q8IUnit ^ (Multiplicative.toAdd i).val
  map_one' := by
    apply Units.ext
    simp [q8IUnit]
  map_mul' i j := by
    apply Units.ext
    change Complex.I ^ ((Multiplicative.toAdd (i * j)).val) =
      Complex.I ^ (Multiplicative.toAdd i).val *
        Complex.I ^ (Multiplicative.toAdd j).val
    let a : ZMod 4 := Multiplicative.toAdd i
    let b : ZMod 4 := Multiplicative.toAdd j
    have h := congrArg Prod.fst (q8Ipow_add a b (1, 0))
    change Complex.I ^ (a + b).val * 1 =
      Complex.I ^ a.val * (Complex.I ^ b.val * 1) at h
    simpa [a, b] using h

theorem q8OrderFourCharacter_apply (i : ZMod 4) :
    (q8OrderFourCharacter (Multiplicative.ofAdd i) : ℂ) = Complex.I ^ i.val := by
  rfl

/-- The actual cyclic order-four subgroup embedded into `Q₈`. -/
def q8CyclicEmbedding : Multiplicative (ZMod 4) →* QuaternionGroup 2 where
  toFun i := QuaternionGroup.a (Multiplicative.toAdd i)
  map_one' := by rfl
  map_mul' i j := by rfl

theorem q8CyclicEmbedding_apply (i : ZMod 4) :
    q8CyclicEmbedding (Multiplicative.ofAdd i) = QuaternionGroup.a i := rfl

/-- The displayed `C₄` source is genuinely embedded in the actual quaternionic Galois group. -/
theorem q8CyclicEmbedding_injective : Function.Injective q8CyclicEmbedding := by
  intro i j hij
  change @QuaternionGroup.a 2 (Multiplicative.toAdd i) =
    @QuaternionGroup.a 2 (Multiplicative.toAdd j) at hij
  injection hij

/-- The actual cyclic source subgroup of the Serre `Q₈` Galois group. -/
def q8CyclicSubgroup : Subgroup (QuaternionGroup 2) := q8CyclicEmbedding.range

/-- The displayed source is isomorphic to `C₄`; no abstract cyclic subgroup is substituted in. -/
noncomputable def q8CyclicSourceEquiv :
    Multiplicative (ZMod 4) ≃* q8CyclicSubgroup :=
  MulEquiv.ofBijective q8CyclicEmbedding.rangeRestrict ⟨by
    intro x y h
    apply q8CyclicEmbedding_injective
    exact congrArg Subtype.val h, by
    intro x
    rcases x.2 with ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩⟩

theorem q8CyclicSubgroup_card : Nat.card q8CyclicSubgroup = 4 := by
  calc
    Nat.card q8CyclicSubgroup = Nat.card (Multiplicative (ZMod 4)) :=
      Nat.card_congr q8CyclicSourceEquiv.toEquiv.symm
    _ = Nat.card (ZMod 4) := Nat.card_congr (Equiv.refl _)
    _ = 4 := Nat.card_zmod 4

/-- The source has index two, the degree required for the Artin induction step. -/
theorem q8CyclicSubgroup_index : q8CyclicSubgroup.index = 2 := by
  have hcard := q8CyclicSubgroup.card_mul_index
  rw [q8CyclicSubgroup_card] at hcard
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card] at hcard
  omega

/-- The degree-one character on the actual source subgroup, transported through its literal
`C₄` parametrization. -/
def q8CyclicSubgroupCharacter : GaloisForLFunctions.LinearCharacter q8CyclicSubgroup :=
  q8OrderFourCharacter.comp q8CyclicSourceEquiv.symm.toMonoidHom

theorem q8CyclicSourceEquiv_apply (i : ZMod 4) :
    q8CyclicSourceEquiv (Multiplicative.ofAdd i) =
      ⟨QuaternionGroup.a i, ⟨_, rfl⟩⟩ := rfl

theorem q8CyclicSubgroupCharacter_apply (i : ZMod 4) :
    q8CyclicSubgroupCharacter ⟨QuaternionGroup.a i, ⟨_, rfl⟩⟩ =
      q8OrderFourCharacter (Multiplicative.ofAdd i) := by
  unfold q8CyclicSubgroupCharacter
  rw [← q8CyclicSourceEquiv_apply]
  simp

/-- Induction of the literal quartic source character has the same degree as Serre's Artin
carrier.  This is the finite source gate needed to turn the channel law into an Artin-induction
comparison. -/
theorem q8CyclicSubgroup_monomial_degree :
    (GaloisForLFunctions.monomialGenuineCharacter (QuaternionGroup 2) q8CyclicSubgroup
      q8CyclicSubgroupCharacter).val 1 = 2 := by
  rw [GaloisForLFunctions.monomialGenuineCharacter_one_eq_index, q8CyclicSubgroup_index]
  norm_num

/-- Inclusion of the first literal source channel. -/
def q8FirstChannelLinear : ℂ →ₗ[ℂ] Q8Carrier where
  toFun z := (z, 0)
  map_add' z w := by ext <;> simp
  map_smul' a z := by ext <;> simp

/-- The first source channel intertwines its literal quartic character with the restricted
quaternionic representation. -/
def q8FirstChannelIntertwining :
    (GaloisForLFunctions.linearCharacterRepresentation q8CyclicSubgroupCharacter).IntertwiningMap
      (deningerQ8Representation.comp q8CyclicSubgroup.subtype) where
  toLinearMap := q8FirstChannelLinear
  isIntertwining' h := by
    apply LinearMap.ext
    intro z
    let i : ZMod 4 := Multiplicative.toAdd (q8CyclicSourceEquiv.symm h)
    have hh : h = q8CyclicSourceEquiv (Multiplicative.ofAdd i) := by
      dsimp [i]
      simpa using (q8CyclicSourceEquiv.apply_symm_apply h).symm
    rw [hh, q8CyclicSourceEquiv_apply]
    change q8FirstChannelLinear ((q8CyclicSubgroupCharacter
        ⟨QuaternionGroup.a i, ⟨_, rfl⟩⟩ : ℂ) * z) =
      deningerQ8Representation (QuaternionGroup.a i) (q8FirstChannelLinear z)
    rw [q8CyclicSubgroupCharacter_apply]
    change ((q8OrderFourCharacter (Multiplicative.ofAdd i) : ℂ) * z, 0) = _
    change ((q8OrderFourCharacter (Multiplicative.ofAdd i) : ℂ) * z, 0) =
      q8Ipow i (z, 0)
    ext
    · rw [q8OrderFourCharacter_apply]
      simp [q8Ipow]
    · simp [q8Ipow]

/-- The actual morphism from the induced quartic source representation to the literal
quaternionic representation. -/
noncomputable def q8MonomialToDeninger :
    Rep.ind q8CyclicSubgroup.subtype
      (Rep.of (GaloisForLFunctions.linearCharacterRepresentation q8CyclicSubgroupCharacter)) ⟶
        Rep.of deningerQ8Representation :=
  (Rep.indResHomEquiv q8CyclicSubgroup.subtype
    (Rep.of (GaloisForLFunctions.linearCharacterRepresentation q8CyclicSubgroupCharacter))
    (Rep.of deningerQ8Representation)).symm (Rep.ofHom q8FirstChannelIntertwining)

theorem q8MonomialToDeninger_mk_one (z : ℂ) :
    q8MonomialToDeninger.hom
      (Representation.IndV.mk q8CyclicSubgroup.subtype
        (GaloisForLFunctions.linearCharacterRepresentation q8CyclicSubgroupCharacter) 1 z) =
      (z, 0) := by
  have h := (Rep.indResHomEquiv q8CyclicSubgroup.subtype
    (Rep.of (GaloisForLFunctions.linearCharacterRepresentation q8CyclicSubgroupCharacter))
    (Rep.of deningerQ8Representation)).apply_symm_apply
      (Rep.ofHom q8FirstChannelIntertwining)
  have hz := congrArg (fun f => f.hom z) h
  simpa [q8MonomialToDeninger, Rep.indResHomEquiv,
    q8FirstChannelIntertwining, q8FirstChannelLinear] using hz

theorem q8MonomialToDeninger_surjective : Function.Surjective q8MonomialToDeninger.hom := by
  intro v
  rcases v with ⟨x, y⟩
  let e : Representation.IndV q8CyclicSubgroup.subtype
      (GaloisForLFunctions.linearCharacterRepresentation q8CyclicSubgroupCharacter) :=
    Representation.IndV.mk q8CyclicSubgroup.subtype
      (GaloisForLFunctions.linearCharacterRepresentation q8CyclicSubgroupCharacter) 1 1
  let xe := (Rep.ind q8CyclicSubgroup.subtype
      (Rep.of (GaloisForLFunctions.linearCharacterRepresentation q8CyclicSubgroupCharacter))).ρ
        (QuaternionGroup.xa 0) e
  refine ⟨x • e + y • xe, ?_⟩
  rw [map_add, map_smul, map_smul]
  have he : q8MonomialToDeninger.hom e = (1, 0) := by
    exact q8MonomialToDeninger_mk_one 1
  have hxe := Rep.hom_comm_apply q8MonomialToDeninger (QuaternionGroup.xa 0) e
  change q8MonomialToDeninger.hom xe =
    deningerQ8Representation (QuaternionGroup.xa 0) (q8MonomialToDeninger.hom e) at hxe
  rw [he, deningerQ8Representation_xa_zero_apply] at hxe
  have hxe' : q8MonomialToDeninger.hom xe = (0, 1) := by
    simpa [deningerQuaternionTransitionK] using hxe
  rw [he, hxe']
  ext <;> simp

theorem q8CyclicSubgroup_induced_finrank :
    Module.finrank ℂ (Representation.IndV q8CyclicSubgroup.subtype
      (GaloisForLFunctions.linearCharacterRepresentation q8CyclicSubgroupCharacter)) = 2 := by
  rw [GaloisForLFunctions.induced_finrank_eq_index_mul,
    q8CyclicSubgroup_index]
  norm_num

theorem q8MonomialToDeninger_injective : Function.Injective q8MonomialToDeninger.hom := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr
    q8MonomialToDeninger_surjective
  calc
    Module.finrank ℂ (Representation.IndV q8CyclicSubgroup.subtype
        (GaloisForLFunctions.linearCharacterRepresentation q8CyclicSubgroupCharacter)) = 2 :=
      q8CyclicSubgroup_induced_finrank
    _ = Module.finrank ℂ Q8Carrier := deningerQ8ArtinRepresentation_finrank.symm

/-- Exact standard induction identity for the literal two-dimensional quaternionic
representation. -/
noncomputable def q8InducedRepresentationEquiv :
    (Representation.ind q8CyclicSubgroup.subtype
      (GaloisForLFunctions.linearCharacterRepresentation q8CyclicSubgroupCharacter)).Equiv
        deningerQ8Representation :=
  Representation.Equiv.mk
    (LinearEquiv.ofBijective q8MonomialToDeninger.hom
      ⟨q8MonomialToDeninger_injective, q8MonomialToDeninger_surjective⟩)
    (by
      intro g
      apply LinearMap.ext
      intro v
      exact Rep.hom_comm_apply q8MonomialToDeninger g v)

local notation "K3" => SerreQ8TopField

noncomputable local instance serreQ8GalFintype : Fintype Gal(K3/ℚ) :=
  Fintype.ofEquiv _ serreQ8_galoisEquivQ8.toEquiv.symm

/-- The actual index-two `C₄` source subgroup inside the Galois group of Serre's displayed
number field. -/
def serreQ8CyclicSubgroup : Subgroup Gal(K3/ℚ) :=
  q8CyclicSubgroup.comap serreQ8_galoisEquivQ8.toMonoidHom

noncomputable def serreQ8CyclicSubgroupEquiv :
    serreQ8CyclicSubgroup ≃* q8CyclicSubgroup where
  toFun g := ⟨serreQ8_galoisEquivQ8 g, g.2⟩
  invFun h := ⟨serreQ8_galoisEquivQ8.symm h, by
    change serreQ8_galoisEquivQ8 (serreQ8_galoisEquivQ8.symm h) ∈ q8CyclicSubgroup
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

/-- The actual degree-one source character on Serre's Galois subgroup. -/
def serreQ8CyclicSubgroupCharacter :
    GaloisForLFunctions.LinearCharacter serreQ8CyclicSubgroup :=
  q8CyclicSubgroupCharacter.comp serreQ8CyclicSubgroupEquiv.toMonoidHom

noncomputable local instance serreQ8InducedFiniteDimensional :
    FiniteDimensional ℂ (Representation.IndV serreQ8CyclicSubgroup.subtype
      (GaloisForLFunctions.linearCharacterRepresentation serreQ8CyclicSubgroupCharacter)) :=
  by infer_instance

theorem serreQ8CyclicSubgroup_index : serreQ8CyclicSubgroup.index = 2 := by
  have hcard := serreQ8CyclicSubgroup.card_mul_index
  have hsubcard : Nat.card serreQ8CyclicSubgroup = 4 := by
    calc
      Nat.card serreQ8CyclicSubgroup = Nat.card q8CyclicSubgroup :=
        Nat.card_congr serreQ8CyclicSubgroupEquiv.toEquiv
      _ = 4 := q8CyclicSubgroup_card
  rw [hsubcard] at hcard
  have hgalcard : Nat.card Gal(K3/ℚ) = 8 := by
    calc
      Nat.card Gal(K3/ℚ) = Nat.card (QuaternionGroup 2) :=
        Nat.card_congr serreQ8_galoisEquivQ8.toEquiv
      _ = 8 := by
        rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [hgalcard] at hcard
  omega

/-- The quartic source is selected by the literal arithmetic carrier `√41`: it is exactly
the subgroup fixing that carrier, not a freely chosen cyclic subgroup of `Q₈`. -/
theorem serreQ8CyclicSubgroup_eq_stabilizer_topY :
    serreQ8CyclicSubgroup =
      MulAction.stabilizer (Gal(K3/ℚ)) serreQ8TopY := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    rw [MulAction.mem_stabilizer_iff]
    change g serreQ8TopY = serreQ8TopY
    change serreQ8_galoisEquivQ8 g ∈ q8CyclicSubgroup at hg
    rcases hg with ⟨i, hi⟩
    have hgi : g = serreQ8_galoisEquivQ8.symm (q8CyclicEmbedding i) := by
      apply serreQ8_galoisEquivQ8.injective
      simpa using hi.symm
    rw [hgi]
    change serreQ8IAlgPow (Multiplicative.toAdd i) serreQ8TopY = serreQ8TopY
    exact serreQ8IAlgPow_topY _
  · intro hg
    rw [MulAction.mem_stabilizer_iff] at hg
    change g serreQ8TopY = serreQ8TopY at hg
    change serreQ8_galoisEquivQ8 g ∈ q8CyclicSubgroup
    rcases hq : serreQ8_galoisEquivQ8 g with i | i
    · refine ⟨Multiplicative.ofAdd i, ?_⟩
      change q8CyclicEmbedding (Multiplicative.ofAdd i) = QuaternionGroup.a i
      rfl
    · exfalso
      have hg' := hg
      rw [← serreQ8_galoisEquivQ8.symm_apply_apply g, hq] at hg'
      change serreQ8JAlgEquiv (serreQ8IAlgPow i serreQ8TopY) = serreQ8TopY at hg'
      rw [serreQ8IAlgPow_topY, serreQ8JAlgEquiv_apply, serreQ8J_topY] at hg'
      apply serreQ8TopY_ne_zero
      rw [eq_comm] at hg'
      have hsum : serreQ8TopY + serreQ8TopY = 0 :=
        eq_neg_iff_add_eq_zero.mp hg'
      have htwice : (2 : K3) * serreQ8TopY = 0 := by
        rw [two_mul]
        exact hsum
      exact (mul_eq_zero.mp htwice).resolve_left (by
        letI : CharZero K3 :=
          charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
        norm_num)

/-- The arithmetic carrier `√41` has the two-point Galois orbit `{√41, -√41}`.
Together with `serreQ8CyclicSubgroup_eq_stabilizer_topY`, this makes both the cyclic
source and its nontrivial reflection orientation source-selected. -/
theorem serreQ8TopY_orbit_eq_two_point :
    MulAction.orbit (Gal(K3/ℚ)) serreQ8TopY =
      ({serreQ8TopY, -serreQ8TopY} : Set K3) := by
  ext z
  constructor
  · rintro ⟨g, rfl⟩
    change g serreQ8TopY ∈ ({serreQ8TopY, -serreQ8TopY} : Set K3)
    rcases hq : serreQ8_galoisEquivQ8 g with i | i
    · left
      rw [← serreQ8_galoisEquivQ8.symm_apply_apply g, hq]
      change serreQ8IAlgPow i serreQ8TopY = serreQ8TopY
      exact serreQ8IAlgPow_topY _
    · right
      rw [← serreQ8_galoisEquivQ8.symm_apply_apply g, hq]
      change serreQ8JAlgEquiv (serreQ8IAlgPow i serreQ8TopY) = -serreQ8TopY
      rw [serreQ8IAlgPow_topY, serreQ8JAlgEquiv_apply, serreQ8J_topY]
  · intro hz
    rcases hz with rfl | rfl
    · exact ⟨1, by simp⟩
    · refine ⟨serreQ8_galoisEquivQ8.symm (QuaternionGroup.xa 0), ?_⟩
      change serreQ8JAlgEquiv (serreQ8IAlgPow (0 : ZMod 4) serreQ8TopY) = -serreQ8TopY
      rw [serreQ8IAlgPow_topY, serreQ8JAlgEquiv_apply, serreQ8J_topY]

/-- First channel intertwining on the actual Galois subgroup. -/
def serreQ8FirstChannelIntertwining :
    (GaloisForLFunctions.linearCharacterRepresentation serreQ8CyclicSubgroupCharacter).IntertwiningMap
      (serreQ8ArtinRepresentation.comp serreQ8CyclicSubgroup.subtype) where
  toLinearMap := q8FirstChannelLinear
  isIntertwining' h := by
    apply LinearMap.ext
    intro z
    change q8FirstChannelLinear ((serreQ8CyclicSubgroupCharacter h : ℂ) * z) =
      serreQ8ArtinRepresentation h (q8FirstChannelLinear z)
    change q8FirstChannelLinear
        ((q8CyclicSubgroupCharacter (serreQ8CyclicSubgroupEquiv h) : ℂ) * z) =
      deningerQ8Representation (serreQ8CyclicSubgroupEquiv h) (q8FirstChannelLinear z)
    exact LinearMap.congr_fun
      (q8FirstChannelIntertwining.isIntertwining' (serreQ8CyclicSubgroupEquiv h)) z

noncomputable def serreQ8MonomialToArtin :
    Rep.ind serreQ8CyclicSubgroup.subtype
      (Rep.of (GaloisForLFunctions.linearCharacterRepresentation serreQ8CyclicSubgroupCharacter)) ⟶
        Rep.of serreQ8ArtinRepresentation :=
  (Rep.indResHomEquiv serreQ8CyclicSubgroup.subtype
    (Rep.of (GaloisForLFunctions.linearCharacterRepresentation serreQ8CyclicSubgroupCharacter))
    (Rep.of serreQ8ArtinRepresentation)).symm (Rep.ofHom serreQ8FirstChannelIntertwining)

theorem serreQ8MonomialToArtin_mk_one (z : ℂ) :
    serreQ8MonomialToArtin.hom
      (Representation.IndV.mk serreQ8CyclicSubgroup.subtype
        (GaloisForLFunctions.linearCharacterRepresentation serreQ8CyclicSubgroupCharacter) 1 z) =
      (z, 0) := by
  have h := (Rep.indResHomEquiv serreQ8CyclicSubgroup.subtype
    (Rep.of (GaloisForLFunctions.linearCharacterRepresentation serreQ8CyclicSubgroupCharacter))
    (Rep.of serreQ8ArtinRepresentation)).apply_symm_apply
      (Rep.ofHom serreQ8FirstChannelIntertwining)
  have hz := congrArg (fun f => f.hom z) h
  simpa [serreQ8MonomialToArtin, Rep.indResHomEquiv,
    serreQ8FirstChannelIntertwining, q8FirstChannelLinear] using hz

theorem serreQ8MonomialToArtin_surjective : Function.Surjective serreQ8MonomialToArtin.hom := by
  intro v
  rcases v with ⟨x, y⟩
  let e : Representation.IndV serreQ8CyclicSubgroup.subtype
      (GaloisForLFunctions.linearCharacterRepresentation serreQ8CyclicSubgroupCharacter) :=
    Representation.IndV.mk serreQ8CyclicSubgroup.subtype
      (GaloisForLFunctions.linearCharacterRepresentation serreQ8CyclicSubgroupCharacter) 1 1
  let g0 : Gal(K3/ℚ) := serreQ8_galoisEquivQ8.symm (QuaternionGroup.xa 0)
  let xe := (Rep.ind serreQ8CyclicSubgroup.subtype
      (Rep.of (GaloisForLFunctions.linearCharacterRepresentation serreQ8CyclicSubgroupCharacter))).ρ g0 e
  refine ⟨x • e + y • xe, ?_⟩
  rw [map_add, map_smul, map_smul]
  have he : serreQ8MonomialToArtin.hom e = (1, 0) := by
    exact serreQ8MonomialToArtin_mk_one 1
  have hxe := Rep.hom_comm_apply serreQ8MonomialToArtin g0 e
  change serreQ8MonomialToArtin.hom xe =
    serreQ8ArtinRepresentation g0 (serreQ8MonomialToArtin.hom e) at hxe
  rw [he, serreQ8ArtinRepresentation_apply] at hxe
  change serreQ8MonomialToArtin.hom xe =
    deningerQ8Representation
      (serreQ8_galoisEquivQ8 (serreQ8_galoisEquivQ8.symm (QuaternionGroup.xa 0))) (1, 0) at hxe
  rw [serreQ8_galoisEquivQ8.apply_symm_apply,
    deningerQ8Representation_xa_zero_apply] at hxe
  have hxe' : serreQ8MonomialToArtin.hom xe = (0, 1) := by
    simpa [deningerQuaternionTransitionK] using hxe
  rw [he, hxe']
  ext <;> simp

theorem serreQ8CyclicSubgroup_induced_finrank :
    Module.finrank ℂ (Representation.IndV serreQ8CyclicSubgroup.subtype
      (GaloisForLFunctions.linearCharacterRepresentation serreQ8CyclicSubgroupCharacter)) = 2 := by
  rw [GaloisForLFunctions.induced_finrank_eq_index_mul,
    serreQ8CyclicSubgroup_index]
  norm_num

theorem serreQ8MonomialToArtin_injective : Function.Injective serreQ8MonomialToArtin.hom := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr
    serreQ8MonomialToArtin_surjective
  calc
    Module.finrank ℂ (Representation.IndV serreQ8CyclicSubgroup.subtype
        (GaloisForLFunctions.linearCharacterRepresentation serreQ8CyclicSubgroupCharacter)) = 2 :=
      serreQ8CyclicSubgroup_induced_finrank
    _ = Module.finrank ℂ Q8Carrier := serreQ8ArtinRepresentation_finrank.symm

/-- Exact Artin induction identity on Serre's literal Galois group and literal index-two
quartic source subgroup. -/
noncomputable def serreQ8InducedRepresentationEquiv :
    (Representation.ind serreQ8CyclicSubgroup.subtype
      (GaloisForLFunctions.linearCharacterRepresentation serreQ8CyclicSubgroupCharacter)).Equiv
        serreQ8ArtinRepresentation :=
  Representation.Equiv.mk
    (LinearEquiv.ofBijective serreQ8MonomialToArtin.hom
      ⟨serreQ8MonomialToArtin_injective, serreQ8MonomialToArtin_surjective⟩)
    (by
      intro g
      apply LinearMap.ext
      intro v
      exact Rep.hom_comm_apply serreQ8MonomialToArtin g v)

/-- **Field-selected monomial source law.**  The literal Artin representation of Serre's field
is induced from a degree-one character of the stabilizer of the literal carrier `√41`; the
same carrier has precisely the two reflected values `±√41`.  Thus field realization, source
selection, quartic induction, and the two quotient orientations are one source statement. -/
theorem serreQ8ArtinRepresentation_exists_induced_from_topY_stabilizer :
    ∃ ψ : GaloisForLFunctions.LinearCharacter
      (MulAction.stabilizer (Gal(K3/ℚ)) serreQ8TopY),
      Nonempty ((Representation.ind
        (MulAction.stabilizer (Gal(K3/ℚ)) serreQ8TopY).subtype
        (GaloisForLFunctions.linearCharacterRepresentation ψ)).Equiv
        serreQ8ArtinRepresentation) := by
  rw [← serreQ8CyclicSubgroup_eq_stabilizer_topY]
  exact ⟨serreQ8CyclicSubgroupCharacter, ⟨serreQ8InducedRepresentationEquiv⟩⟩

/-- The reflected source channel is the inverse order-four character. -/
theorem q8OrderFourCharacter_neg_apply (i : ZMod 4) :
    (q8OrderFourCharacter (Multiplicative.ofAdd (-i)) : ℂ) =
      (-Complex.I) ^ i.val := by
  have h := congrArg Prod.snd (q8Ipow_apply_K i (1, 0))
  change (-Complex.I) ^ i.val * 1 = Complex.I ^ (-i).val * 1 at h
  rw [q8OrderFourCharacter_apply]
  simpa using h.symm

theorem q8OrderFourCharacter_neg_eq_inv (i : ZMod 4) :
    q8OrderFourCharacter (Multiplicative.ofAdd (-i)) =
      (q8OrderFourCharacter (Multiplicative.ofAdd i))⁻¹ := by
  rw [← map_inv]
  rfl

/-- The source character is genuinely quartic, so its two channels cannot collapse to a quadratic
or scalar source. -/
theorem q8OrderFourCharacter_generator_sq_eq_neg_one :
    q8OrderFourCharacter (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 = -1 := by
  apply Units.ext
  have hone : (1 : ZMod 4).val = 1 := ZMod.val_cast_of_lt (by norm_num)
  norm_num [q8OrderFourCharacter, q8IUnit, hone, pow_succ, Complex.I_mul_I]

theorem q8OrderFourCharacter_generator_sq_ne_one :
    q8OrderFourCharacter (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 ≠ 1 := by
  rw [q8OrderFourCharacter_generator_sq_eq_neg_one]
  norm_num

theorem q8OrderFourCharacter_generator_fourth_eq_one :
    q8OrderFourCharacter (Multiplicative.ofAdd (1 : ZMod 4)) ^ 4 = 1 := by
  apply Units.ext
  have hone : (1 : ZMod 4).val = 1 := ZMod.val_cast_of_lt (by norm_num)
  norm_num [q8OrderFourCharacter, q8IUnit, hone, pow_succ, Complex.I_mul_I]

theorem q8_orderOf_source_character_generator :
    orderOf (q8OrderFourCharacter (Multiplicative.ofAdd (1 : ZMod 4))) = 4 := by
  change orderOf (q8OrderFourCharacter (Multiplicative.ofAdd (1 : ZMod 4))) = 2 ^ 2
  apply orderOf_eq_prime_pow
  · simpa using q8OrderFourCharacter_generator_sq_ne_one
  · simpa using q8OrderFourCharacter_generator_fourth_eq_one

/-- The literal Serre action restricts to the source character and its inverse on the two
coefficient-faithful channels. -/
theorem serreQ8ArtinRepresentation_cyclic_source_law
    (i : ZMod 4) (x y : ℂ) :
    serreQ8ArtinRepresentation
        (serreQ8_galoisEquivQ8.symm (q8CyclicEmbedding (Multiplicative.ofAdd i))) (x, y) =
      ((q8OrderFourCharacter (Multiplicative.ofAdd i) : ℂ) * x,
        (q8OrderFourCharacter (Multiplicative.ofAdd (-i)) : ℂ) * y) := by
  rw [q8CyclicEmbedding_apply, serreQ8ArtinRepresentation_apply]
  rw [serreQ8_galoisEquivQ8.apply_symm_apply]
  change deningerQ8RepresentationLinear (QuaternionGroup.a i) (x, y) = _
  rw [deningerQ8RepresentationLinear_apply]
  change q8Ipow i (x, y) = _
  ext <;> simp only [q8Ipow]
  · rw [q8OrderFourCharacter_apply]
  · rw [q8OrderFourCharacter_neg_apply]

/-- The other quaternionic coset exchanges the two source channels, without changing their
coefficients. -/
theorem serreQ8ArtinRepresentation_reflection_source_law
    (i : ZMod 4) (x y : ℂ) :
    serreQ8ArtinRepresentation
        (serreQ8_galoisEquivQ8.symm (QuaternionGroup.xa i)) (x, y) =
      (-((q8OrderFourCharacter (Multiplicative.ofAdd (-i)) : ℂ) * y),
        (q8OrderFourCharacter (Multiplicative.ofAdd i) : ℂ) * x) := by
  rw [serreQ8ArtinRepresentation_apply]
  rw [serreQ8_galoisEquivQ8.apply_symm_apply]
  change deningerQ8RepresentationLinear (QuaternionGroup.xa i) (x, y) = _
  rw [deningerQ8RepresentationLinear_apply]
  change deningerQuaternionTransitionK (q8Ipow i (x, y)) = _
  ext <;> simp only [q8Ipow, deningerQuaternionTransitionK]
  · rw [q8OrderFourCharacter_neg_apply]
  · rw [q8OrderFourCharacter_apply]

/-- One source law discharging both retained gates: the cyclic carrier is the primitive quartic
character and its inverse, while the other quaternionic orientation exchanges those exact two
channels. -/
theorem serreQ8ArtinRepresentation_monomial_source_law
    (i : ZMod 4) (x y : ℂ) :
    serreQ8ArtinRepresentation
        (serreQ8_galoisEquivQ8.symm (q8CyclicEmbedding (Multiplicative.ofAdd i))) (x, y) =
      ((q8OrderFourCharacter (Multiplicative.ofAdd i) : ℂ) * x,
        ((q8OrderFourCharacter (Multiplicative.ofAdd i))⁻¹ : ℂ) * y) ∧
    serreQ8ArtinRepresentation
        (serreQ8_galoisEquivQ8.symm (QuaternionGroup.xa i)) (x, y) =
      (-((q8OrderFourCharacter (Multiplicative.ofAdd (-i)) : ℂ) * y),
        (q8OrderFourCharacter (Multiplicative.ofAdd i) : ℂ) * x) := by
  constructor
  · rw [serreQ8ArtinRepresentation_cyclic_source_law,
      q8OrderFourCharacter_neg_eq_inv]
    simp
  · exact serreQ8ArtinRepresentation_reflection_source_law i x y

end

end RHTower
