import GaloisForLFunctions.RHTower.DeningerQ8FortyOneResidueQuarticNoGo
import GaloisForLFunctions.RHTower.DeningerQ8ActualFortyOneInertiaCarrier

/-!
# Actual forty-one-adic source dual and Tate epsilon pair

The direct map from the literal `C₄` source into residue units cannot carry a
quartic residue character: its pullback is always at most quadratic.  This
leaf constructs the forced reverse arrow.  The cyclic group of residue units
maps surjectively to `C₄`, then to the literal `J`-generated inertia subgroup
selected by `√5`.

The construction is coefficient-faithful: the actual Artin representation
restricts on this inertia to the source character and its inverse on two
explicit eigenlines.  Both orientations have exact conductor `41`, satisfy
the field-one Tate functional equation, and their local epsilon phases multiply
to `+1`.
-/

namespace RHTower

noncomputable section

open scoped NumberField Pointwise
open GaloisForLFunctions.RHTower

local instance q8FortyOneDualFactPrimeFortyOne : Fact (Nat.Prime 41) := ⟨by norm_num⟩

def zmodFortyToFour : Multiplicative (ZMod 40) →* Multiplicative (ZMod 4) :=
  (ZMod.castHom (by norm_num : 4 ∣ 40) (ZMod 4)).toAddMonoidHom.toMultiplicative

theorem zmodFortyToFour_surjective : Function.Surjective zmodFortyToFour := by
  exact ZMod.castHom_surjective (by norm_num : 4 ∣ 40)

noncomputable def zmodFortyOneUnitsCyclicEquiv :
    Multiplicative (ZMod 40) ≃* (ZMod 41)ˣ := by
  letI : IsCyclic (ZMod 41)ˣ := ZMod.isCyclic_units_prime (by norm_num)
  exact mulEquivOfCyclicCardEq (by
    norm_num [Nat.card_eq_fintype_card, Nat.totient_prime (by norm_num : Nat.Prime 41)])

noncomputable def zmodFortyOneQuarticQuotient :
    (ZMod 41)ˣ →* Multiplicative (ZMod 4) :=
  zmodFortyToFour.comp zmodFortyOneUnitsCyclicEquiv.symm.toMonoidHom

theorem zmodFortyOneQuarticQuotient_surjective :
    Function.Surjective zmodFortyOneQuarticQuotient := by
  exact zmodFortyToFour_surjective.comp zmodFortyOneUnitsCyclicEquiv.symm.surjective

def q8JCyclicEmbedding : Multiplicative (ZMod 4) →* QuaternionGroup 2 where
  toFun i := (@QuaternionGroup.xa 2 (0 : ZMod 4)) ^ (Multiplicative.toAdd i).val
  map_one' := by simp
  map_mul' i j := by
    change (@QuaternionGroup.xa 2 (0 : ZMod 4)) ^ (Multiplicative.toAdd (i * j)).val =
      (@QuaternionGroup.xa 2 (0 : ZMod 4)) ^ (Multiplicative.toAdd i).val *
        (@QuaternionGroup.xa 2 (0 : ZMod 4)) ^ (Multiplicative.toAdd j).val
    rw [toAdd_mul, ← pow_add, ZMod.val_add]
    apply pow_eq_pow_of_modEq (n := 4)
    · simp [Nat.ModEq]
    · exact QuaternionGroup.xa_pow_four (n := 2) 0

theorem q8JCyclicEmbedding_injective : Function.Injective q8JCyclicEmbedding := by
  intro i j hij
  change (@QuaternionGroup.xa 2 (0 : ZMod 4)) ^ (Multiplicative.toAdd i).val =
    (@QuaternionGroup.xa 2 (0 : ZMod 4)) ^ (Multiplicative.toAdd j).val at hij
  have hmod : (Multiplicative.toAdd i).val ≡ (Multiplicative.toAdd j).val [MOD 4] := by
    have h := pow_eq_pow_iff_modEq.mp hij
    simpa using h
  apply Multiplicative.toAdd.injective
  calc
    Multiplicative.toAdd i = ((Multiplicative.toAdd i).val : ZMod 4) := by simp
    _ = ((Multiplicative.toAdd j).val : ZMod 4) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    _ = Multiplicative.toAdd j := by simp

theorem deningerQ8Representation_Jpow_positiveChannel (n : ℕ) (z : ℂ) :
    deningerQ8Representation ((@QuaternionGroup.xa 2 (0 : ZMod 4)) ^ n)
        (Complex.I * z, z) =
      (Complex.I ^ n) • (Complex.I * z, z) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', map_mul, Module.End.mul_apply, ih,
        deningerQ8Representation_xa_zero_apply]
      ext
      · simp [deningerQuaternionTransitionK, pow_succ]
        calc
          -(Complex.I ^ n * z) = Complex.I ^ n * (-1) * z := by ring
          _ = Complex.I ^ n * (Complex.I * Complex.I) * z := by
            rw [Complex.I_mul_I]
          _ = Complex.I ^ n * Complex.I * (Complex.I * z) := by ring
      · simp [deningerQuaternionTransitionK, pow_succ]
        ring

theorem deningerQ8Representation_Jpow_negativeChannel (n : ℕ) (z : ℂ) :
    deningerQ8Representation ((@QuaternionGroup.xa 2 (0 : ZMod 4)) ^ n)
        (-Complex.I * z, z) =
      ((-Complex.I) ^ n) • (-Complex.I * z, z) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', map_mul, Module.End.mul_apply, ih,
        deningerQ8Representation_xa_zero_apply]
      ext
      · simp [deningerQuaternionTransitionK, pow_succ]
        calc
          -((-Complex.I) ^ n * z) = (-Complex.I) ^ n * (-1) * z := by ring
          _ = (-Complex.I) ^ n * (Complex.I * Complex.I) * z := by
            rw [Complex.I_mul_I]
          _ = (-Complex.I) ^ n * Complex.I * (Complex.I * z) := by ring
      · simp [deningerQuaternionTransitionK, pow_succ]
        ring

theorem deningerQ8Representation_J_source_law
    (i : Multiplicative (ZMod 4)) (z : ℂ) :
    deningerQ8Representation (q8JCyclicEmbedding i) (Complex.I * z, z) =
        (q8OrderFourCharacter i : ℂ) • (Complex.I * z, z) ∧
      deningerQ8Representation (q8JCyclicEmbedding i) (-Complex.I * z, z) =
        (q8OrderFourCharacter i⁻¹ : ℂ) • (-Complex.I * z, z) := by
  let j := Multiplicative.toAdd i
  constructor
  · change deningerQ8Representation
        ((@QuaternionGroup.xa 2 (0 : ZMod 4)) ^ j.val) (Complex.I * z, z) = _
    rw [deningerQ8Representation_Jpow_positiveChannel]
    change (Complex.I ^ j.val) • (Complex.I * z, z) = _
    rw [show i = Multiplicative.ofAdd j by rfl, q8OrderFourCharacter_apply]
  · change deningerQ8Representation
        ((@QuaternionGroup.xa 2 (0 : ZMod 4)) ^ j.val) (-Complex.I * z, z) = _
    rw [deningerQ8Representation_Jpow_negativeChannel]
    change ((-Complex.I) ^ j.val) • (-Complex.I * z, z) = _
    rw [← q8OrderFourCharacter_neg_apply j]
    congr 2

local notation "K3" => deningerQ8RootNumberNegOneTopField
local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField

local instance q8FortyOneDualCharZeroK3 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
noncomputable local instance q8FortyOneDualFiniteDimensionalRatK1 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance q8FortyOneDualFiniteDimensionalK1K2 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance q8FortyOneDualFiniteDimensionalRatK2 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance q8FortyOneDualFiniteDimensionalK2K3 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance q8FortyOneDualFiniteDimensionalRatK3 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance q8FortyOneDualNumberFieldK3 : NumberField K3 := NumberField.mk
noncomputable local instance q8FortyOneDualIsGaloisRatK3 : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois

noncomputable local instance q8FortyOneDualFintypeGalK3Rat : Fintype Gal(K3/ℚ) :=
  Fintype.ofEquiv _ deningerQ8RootNumberNegOne_galoisEquivQ8.toEquiv.symm

example : deningerQ8RootNumberNegOne_galoisEquivQ8.symm
    (@QuaternionGroup.xa 2 (0 : ZMod 4)) = q8JAlgEquiv := by
  rfl

theorem deningerQ8ActualJPower_fixes_topX (n : ℕ) :
    (deningerQ8RootNumberNegOne_galoisEquivQ8.symm
      ((@QuaternionGroup.xa 2 (0 : ZMod 4)) ^ n))
        deningerQ8RootNumberNegOneTopX = deningerQ8RootNumberNegOneTopX := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, map_mul]
      change (deningerQ8RootNumberNegOne_galoisEquivQ8.symm
          ((@QuaternionGroup.xa 2 (0 : ZMod 4)) ^ n))
        (q8JAlgEquiv deningerQ8RootNumberNegOneTopX) = _
      rw [q8JAlgEquiv_apply, q8J_topX, ih]

def q8JCyclicSubgroup : Subgroup (QuaternionGroup 2) := q8JCyclicEmbedding.range

noncomputable def q8JCyclicSourceEquiv :
    Multiplicative (ZMod 4) ≃* q8JCyclicSubgroup :=
  MulEquiv.ofBijective q8JCyclicEmbedding.rangeRestrict
    ⟨by
      intro x y h
      apply q8JCyclicEmbedding_injective
      exact congrArg Subtype.val h,
    by
      intro x
      rcases x.2 with ⟨y, hy⟩
      exact ⟨y, Subtype.ext hy⟩⟩

theorem q8JCyclicSourceEquiv_apply (i : Multiplicative (ZMod 4)) :
    q8JCyclicSourceEquiv i = ⟨q8JCyclicEmbedding i, ⟨i, rfl⟩⟩ := rfl

def deningerQ8ActualJCyclicSubgroup : Subgroup Gal(K3/ℚ) :=
  q8JCyclicSubgroup.comap deningerQ8RootNumberNegOne_galoisEquivQ8.toMonoidHom

noncomputable def deningerQ8ActualJCyclicSubgroupEquiv :
    deningerQ8ActualJCyclicSubgroup ≃* q8JCyclicSubgroup where
  toFun g := ⟨deningerQ8RootNumberNegOne_galoisEquivQ8 g.1, g.2⟩
  invFun h := ⟨deningerQ8RootNumberNegOne_galoisEquivQ8.symm h.1, by
    change deningerQ8RootNumberNegOne_galoisEquivQ8
      (deningerQ8RootNumberNegOne_galoisEquivQ8.symm h) ∈ q8JCyclicSubgroup
    rw [deningerQ8RootNumberNegOne_galoisEquivQ8.apply_symm_apply]
    exact h.2⟩
  left_inv g := by apply Subtype.ext; simp
  right_inv h := by apply Subtype.ext; simp
  map_mul' g h := by apply Subtype.ext; exact map_mul _ _ _

theorem deningerQ8ActualJCyclicSubgroup_eq_stabilizer_topX :
    deningerQ8ActualJCyclicSubgroup =
      MulAction.stabilizer Gal(K3/ℚ) deningerQ8RootNumberNegOneTopX := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro g hg
    rw [MulAction.mem_stabilizer_iff]
    change g deningerQ8RootNumberNegOneTopX = deningerQ8RootNumberNegOneTopX
    rcases hg with ⟨i, hi⟩
    have hgi : g = deningerQ8RootNumberNegOne_galoisEquivQ8.symm
        (q8JCyclicEmbedding i) :=
      (deningerQ8RootNumberNegOne_galoisEquivQ8.symm_apply_apply g).symm.trans
        (congrArg deningerQ8RootNumberNegOne_galoisEquivQ8.symm hi.symm)
    rw [hgi]
    exact deningerQ8ActualJPower_fixes_topX (Multiplicative.toAdd i).val
  · have hcard : Nat.card deningerQ8ActualJCyclicSubgroup = 4 := by
      calc
        Nat.card deningerQ8ActualJCyclicSubgroup = Nat.card q8JCyclicSubgroup := by
          exact Nat.card_congr deningerQ8ActualJCyclicSubgroupEquiv.toEquiv
        _ = Nat.card (Multiplicative (ZMod 4)) :=
          Nat.card_congr q8JCyclicSourceEquiv.toEquiv.symm
        _ = 4 := Nat.card_zmod 4
    rw [hcard]
    exact q8Actual_topX_stabilizer_natCard_le_four

theorem deningerQ8ActualArtinRepresentation_J_source_law
    (i : Multiplicative (ZMod 4)) (z : ℂ) :
    deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8
        (deningerQ8RootNumberNegOne_galoisEquivQ8.symm (q8JCyclicEmbedding i))
        (Complex.I * z, z) =
      (q8OrderFourCharacter i : ℂ) • (Complex.I * z, z) ∧
    deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8
        (deningerQ8RootNumberNegOne_galoisEquivQ8.symm (q8JCyclicEmbedding i))
        (-Complex.I * z, z) =
      (q8OrderFourCharacter i⁻¹ : ℂ) • (-Complex.I * z, z) := by
  simpa [deningerQ8ArtinRepresentation_apply] using
    deningerQ8Representation_J_source_law i z

noncomputable def deningerQ8ActualJSourceEquiv :
    deningerQ8ActualJCyclicSubgroup ≃* Multiplicative (ZMod 4) :=
  deningerQ8ActualJCyclicSubgroupEquiv.trans q8JCyclicSourceEquiv.symm

theorem q8Actual_fortyOne_inertia_eq_JSource
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    P.inertia Gal(K3/ℚ) = deningerQ8ActualJCyclicSubgroup := by
  rw [q8Actual_fortyOne_inertia_eq_topXStabilizer P hPover,
    ← deningerQ8ActualJCyclicSubgroup_eq_stabilizer_topX]

noncomputable def q8ActualFortyOneInertiaSourceEquiv
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    P.inertia Gal(K3/ℚ) ≃* Multiplicative (ZMod 4) :=
  (MulEquiv.subgroupCongr (q8Actual_fortyOne_inertia_eq_JSource P hPover)).trans
    deningerQ8ActualJSourceEquiv

def q8ActualFortyOneInertiaSourceCharacter
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    GaloisForLFunctions.LinearCharacter (P.inertia Gal(K3/ℚ)) :=
  q8OrderFourCharacter.comp
    (q8ActualFortyOneInertiaSourceEquiv P hPover).toMonoidHom

theorem q8ActualFortyOneInertiaSourceCharacter_artin_channels
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)}))
    (g : P.inertia Gal(K3/ℚ)) (z : ℂ) :
    deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8 g.1
        (Complex.I * z, z) =
      (q8ActualFortyOneInertiaSourceCharacter P hPover g : ℂ) •
        (Complex.I * z, z) ∧
    deningerQ8ArtinRepresentation deningerQ8RootNumberNegOne_galoisEquivQ8 g.1
        (-Complex.I * z, z) =
      ((q8ActualFortyOneInertiaSourceCharacter P hPover g)⁻¹ : ℂ) •
        (-Complex.I * z, z) := by
  let h : deningerQ8ActualJCyclicSubgroup :=
    MulEquiv.subgroupCongr (q8Actual_fortyOne_inertia_eq_JSource P hPover) g
  let i : Multiplicative (ZMod 4) := deningerQ8ActualJSourceEquiv h
  have hi : q8JCyclicEmbedding i =
      deningerQ8RootNumberNegOne_galoisEquivQ8 g.1 := by
    have heq := q8JCyclicSourceEquiv.apply_symm_apply
      (deningerQ8ActualJCyclicSubgroupEquiv h)
    exact congrArg Subtype.val heq
  have hg : g.1 = deningerQ8RootNumberNegOne_galoisEquivQ8.symm
      (q8JCyclicEmbedding i) :=
    (deningerQ8RootNumberNegOne_galoisEquivQ8.symm_apply_apply g.1).symm.trans
      (congrArg deningerQ8RootNumberNegOne_galoisEquivQ8.symm hi.symm)
  have hchi : q8ActualFortyOneInertiaSourceCharacter P hPover g =
      q8OrderFourCharacter i := by rfl
  rw [hg, hchi]
  simpa using deningerQ8ActualArtinRepresentation_J_source_law i z

theorem q8ActualFortyOneInertiaSourceCharacter_orderOf
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    orderOf (q8ActualFortyOneInertiaSourceCharacter P hPover) = 4 := by
  unfold q8ActualFortyOneInertiaSourceCharacter
  exact (orderOf_monoidHom_comp_mulEquiv_symm q8OrderFourCharacter
    (q8ActualFortyOneInertiaSourceEquiv P hPover).symm).trans
      q8OrderFourCharacter_orderOf

noncomputable def q8ActualFortyOneResidueToInertiaHom
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    (ZMod 41)ˣ →* P.inertia Gal(K3/ℚ) :=
  (q8ActualFortyOneInertiaSourceEquiv P hPover).symm.toMonoidHom.comp
    zmodFortyOneQuarticQuotient

theorem q8ActualFortyOneResidueToInertiaHom_surjective
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    Function.Surjective (q8ActualFortyOneResidueToInertiaHom P hPover) :=
  (q8ActualFortyOneInertiaSourceEquiv P hPover).symm.surjective.comp
    zmodFortyOneQuarticQuotient_surjective

noncomputable def q8ActualFortyOneZModSourceCharacter
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    MulChar (ZMod 41) ℂ :=
  MulChar.ofUnitHom ((q8ActualFortyOneInertiaSourceCharacter P hPover).comp
    (q8ActualFortyOneResidueToInertiaHom P hPover))

theorem q8ActualFortyOneZModSourceCharacter_pullback
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    (q8ActualFortyOneZModSourceCharacter P hPover).toUnitHom =
      (q8ActualFortyOneInertiaSourceCharacter P hPover).comp
        (q8ActualFortyOneResidueToInertiaHom P hPover) := by
  simp [q8ActualFortyOneZModSourceCharacter, MulChar.toUnitHom_eq]

theorem orderOf_monoidHom_comp_of_surjective
    {G H A : Type*} [Group G] [Group H] [CommGroup A]
    (chi : H →* A) (f : G →* H) (hf : Function.Surjective f) :
    orderOf (chi.comp f) = orderOf chi := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  constructor
  · intro h
    apply MonoidHom.ext
    intro x
    obtain ⟨y, rfl⟩ := hf x
    have hy := congrArg (fun g : G →* A => g y) h
    simpa [MonoidHom.comp_apply] using hy
  · intro h
    apply MonoidHom.ext
    intro x
    have hx := congrArg (fun g : H →* A => g (f x)) h
    simpa [MonoidHom.comp_apply, MonoidHom.pow_apply] using hx

theorem q8ActualFortyOneZModSourceCharacter_orderOf
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    orderOf (q8ActualFortyOneZModSourceCharacter P hPover) = 4 := by
  rw [q8ActualFortyOneZModSourceCharacter,
    orderOf_mulChar_ofUnitHom,
    orderOf_monoidHom_comp_of_surjective _ _
      (q8ActualFortyOneResidueToInertiaHom_surjective P hPover),
    q8ActualFortyOneInertiaSourceCharacter_orderOf P hPover]

theorem q8ActualFortyOneZModSourceCharacter_isPrimitive
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    DirichletCharacter.IsPrimitive
      (q8ActualFortyOneZModSourceCharacter P hPover : DirichletCharacter ℂ 41) :=
  zmodFortyOne_orderFourMulChar_isPrimitive
    (q8ActualFortyOneZModSourceCharacter P hPover)
    (q8ActualFortyOneZModSourceCharacter_orderOf P hPover)

noncomputable def q8ActualFortyOnePrimitiveTateCharacter
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    GaloisForLFunctions.RHTower.FieldOnePadicPrimitiveAngularCharacter 41 1 :=
  ⟨q8ActualFortyOneZModSourceCharacter P hPover,
    by simpa using q8ActualFortyOneZModSourceCharacter_isPrimitive P hPover⟩

noncomputable def q8ActualFortyOneLocalTateEpsilon
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) : ℂ :=
  GaloisForLFunctions.RHTower.fieldOnePadicRamifiedTatePhase 41 1
    (q8ActualFortyOnePrimitiveTateCharacter P hPover) 1

noncomputable def q8ActualFortyOneInverseLocalTateEpsilon
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) : ℂ :=
  GaloisForLFunctions.RHTower.fieldOnePadicRamifiedTatePhase 41 1
    (GaloisForLFunctions.RHTower.fieldOnePadicPrimitiveAngularCharacterInv 41 1
      (q8ActualFortyOnePrimitiveTateCharacter P hPover)) 1

theorem q8ActualFortyOneLocalTateEpsilon_norms
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    ‖q8ActualFortyOneLocalTateEpsilon P hPover‖ = 1 ∧
      ‖q8ActualFortyOneInverseLocalTateEpsilon P hPover‖ = 1 := by
  constructor
  · exact GaloisForLFunctions.RHTower.norm_fieldOnePadicRamifiedTatePhase 41 1 _ 1
  · exact GaloisForLFunctions.RHTower.norm_fieldOnePadicRamifiedTatePhase 41 1 _ 1

theorem q8ActualFortyOneLocalTateEpsilon_mul_inverse_eq_one
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    q8ActualFortyOneLocalTateEpsilon P hPover *
      q8ActualFortyOneInverseLocalTateEpsilon P hPover = 1 := by
  rw [q8ActualFortyOneLocalTateEpsilon,
    q8ActualFortyOneInverseLocalTateEpsilon,
    fieldOnePadicPrimeRamifiedTatePhase_mul_inverse_eq_gaussianPhase]
  change (41 : ℂ)⁻¹ *
    (gaussSum (q8ActualFortyOneZModSourceCharacter P hPover) ZMod.stdAddChar *
      gaussSum (q8ActualFortyOneZModSourceCharacter P hPover)⁻¹ ZMod.stdAddChar) = 1
  rw [zmodFortyOne_quarticSameAdditiveGaussProduct_eq_fortyOne _
    (q8ActualFortyOneZModSourceCharacter_orderOf P hPover)]
  norm_num

theorem q8ActualFortyOneLocalTateEquation258
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)}))
    (f : compactlySupportedLocallyConstant ℚ_[41]) :
    (∫ a : ℚ_[41]ˣ,
        GaloisForLFunctions.RHTower.fieldOnePadicBruhatFourier 41 f (a : ℚ_[41]) *
          (GaloisForLFunctions.RHTower.fieldOnePadicRamifiedCriticalCharacter 41 1
            (q8ActualFortyOnePrimitiveTateCharacter P hPover) 1 a)⁻¹ *
          (Real.sqrt ‖(a : ℚ_[41])‖ : ℂ)
        ∂GaloisForLFunctions.RHTower.fieldOnePadicMultiplicativeHaar 41) =
      q8ActualFortyOneLocalTateEpsilon P hPover *
        (∫ a : ℚ_[41]ˣ,
          f.1 (a : ℚ_[41]) *
            GaloisForLFunctions.RHTower.fieldOnePadicRamifiedCriticalCharacter 41 1
              (q8ActualFortyOnePrimitiveTateCharacter P hPover) 1 a *
            (Real.sqrt ‖(a : ℚ_[41])‖ : ℂ)
          ∂GaloisForLFunctions.RHTower.fieldOnePadicMultiplicativeHaar 41) := by
  exact GaloisForLFunctions.RHTower.fieldOnePadicRamifiedTateEquation258 41 1
    (q8ActualFortyOnePrimitiveTateCharacter P hPover) 1 f

theorem q8ActualFortyOneInverseLocalTateEquation258
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)}))
    (f : compactlySupportedLocallyConstant ℚ_[41]) :
    (∫ a : ℚ_[41]ˣ,
        GaloisForLFunctions.RHTower.fieldOnePadicBruhatFourier 41 f (a : ℚ_[41]) *
          (GaloisForLFunctions.RHTower.fieldOnePadicRamifiedCriticalCharacter 41 1
            (GaloisForLFunctions.RHTower.fieldOnePadicPrimitiveAngularCharacterInv 41 1
              (q8ActualFortyOnePrimitiveTateCharacter P hPover)) 1 a)⁻¹ *
          (Real.sqrt ‖(a : ℚ_[41])‖ : ℂ)
        ∂GaloisForLFunctions.RHTower.fieldOnePadicMultiplicativeHaar 41) =
      q8ActualFortyOneInverseLocalTateEpsilon P hPover *
        (∫ a : ℚ_[41]ˣ,
          f.1 (a : ℚ_[41]) *
            GaloisForLFunctions.RHTower.fieldOnePadicRamifiedCriticalCharacter 41 1
              (GaloisForLFunctions.RHTower.fieldOnePadicPrimitiveAngularCharacterInv 41 1
                (q8ActualFortyOnePrimitiveTateCharacter P hPover)) 1 a *
            (Real.sqrt ‖(a : ℚ_[41])‖ : ℂ)
          ∂GaloisForLFunctions.RHTower.fieldOnePadicMultiplicativeHaar 41) := by
  exact GaloisForLFunctions.RHTower.fieldOnePadicRamifiedTateEquation258 41 1
    (GaloisForLFunctions.RHTower.fieldOnePadicPrimitiveAngularCharacterInv 41 1
      (q8ActualFortyOnePrimitiveTateCharacter P hPover)) 1 f

end
end RHTower
