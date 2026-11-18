import GaloisForLFunctions.HeckeLFunctions.Characters.RestrictionFibers
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysPointedMultiplicativeRoot

/-!
# Values of Hecke character extensions at one or more ideals

Molla's extension count refines to a distribution. At an element of order
e in the quotient, all e possible roots of the prescribed value on its
e-th power occur, each with the same multiplicity. Prescribing values on
a larger subgroup of test ideals also leaves a uniform fiber.
-/

noncomputable section
namespace GaloisForLFunctions.HeckeLFunctions.CharacterExtensions
variable {G : Type*} [CommGroup G]

abbrev Extensions (H : Subgroup G) (ψ : H →* ℂˣ) :=
  {χ : G →* ℂˣ // χ.comp H.subtype=ψ}

/-- Fixing a base extension makes twisting by quotient characters explicit on values. -/
def twistEquiv (H : Subgroup G) (ψ : H →* ℂˣ) (base : Extensions H ψ) :
    (G ⧸ H →* ℂˣ) ≃ Extensions H ψ where
  toFun η := ⟨base.val*η.comp (QuotientGroup.mk' H),by
    ext x
    have hb := DFunLike.congr_fun base.property x
    change base.val x * η ((QuotientGroup.mk' H) x) = ψ x
    rw [(QuotientGroup.eq_one_iff _).2 x.property,map_one,mul_one]
    exact hb⟩
  invFun χ := QuotientGroup.lift H (χ.val/base.val) (by
    intro g hg
    have he := (DFunLike.congr_fun χ.property ⟨g,hg⟩).trans
      (DFunLike.congr_fun base.property ⟨g,hg⟩).symm
    change χ.val g/base.val g=1
    rw [show χ.val g=base.val g from he,div_self])
  left_inv η := by
    ext y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective H y
    change (base.val x*η ((QuotientGroup.mk' H) x))/base.val x=_
    group
  right_inv χ := by
    apply Subtype.ext
    ext x
    change base.val x*(χ.val x/base.val x)=_
    group

theorem twist_value (H : Subgroup G) (ψ : H →* ℂˣ) (base : Extensions H ψ)
    (η : G ⧸ H →* ℂˣ) (x : G) :
    ((twistEquiv H ψ base η).val x) = base.val x * η ((QuotientGroup.mk' H) x) := rfl

/-- Evaluation as a homomorphism from the full character group. -/
def evaluation (x : G) : (G →* ℂˣ) →* ℂˣ where
  toFun χ := χ x
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem eval_in_roots (x : G) :
    (evaluation x).range ≤ rootsOfUnity (orderOf x) ℂ := by
  rintro _ ⟨χ,rfl⟩
  rw [mem_rootsOfUnity]
  change (χ x)^(orderOf x)=1
  rw [← map_pow,pow_orderOf_eq_one,map_one]

/-- Character values at an element of order e form a group of exactly e elements. -/
theorem count_values [Finite G] (x : G) : Nat.card (evaluation x).range = orderOf x := by
  haveI : Finite (G →* ℂˣ) := _root_.RHTower.deningerCharacterGroup_finite
  let J := (evaluation x).range
  haveI : NeZero (orderOf x) := ⟨(orderOf_pos x).ne'⟩
  have upper := Nat.card_le_card_of_injective (Subgroup.inclusion (eval_in_roots x))
    (Subgroup.inclusion_injective _)
  have hd : orderOf x ∣ Nat.card J := by
    apply orderOf_dvd_of_pow_eq_one
    apply (CommGroup.forall_apply_eq_apply_iff G (M := ℂ)).1
    intro χ
    rw [map_pow,map_one]
    let u : J := ⟨χ x,χ,rfl⟩
    exact congrArg (fun t : J => t.val) (pow_card_eq_one' (x := u))
  exact le_antisymm (upper.trans (card_rootsOfUnity ℂ _)) (Nat.le_of_dvd Nat.card_pos hd)

/-- Every root of the right order occurs, even in a noncyclic quotient. -/
theorem evaluation_range [Finite G] (x : G) :
    (evaluation x).range = rootsOfUnity (orderOf x) ℂ := by
  haveI : Finite (G →* ℂˣ) := _root_.RHTower.deningerCharacterGroup_finite
  rw [← count_values x]
  exact _root_.RHTower.deningerFiniteSubgroupUnits_eq_rootsOfUnity _

/-- The number of characters taking an attainable value, times its order
bound, is the group cardinality. -/
theorem evaluation_multiplicity [Finite G] (x : G) (z : ℂˣ) (hz : z^(orderOf x)=1) :
    Nat.card {χ : G →* ℂˣ // χ x=z} * orderOf x = Nat.card G := by
  have hex : z ∈ (evaluation x).range := by rw [evaluation_range,mem_rootsOfUnity]; exact hz
  obtain ⟨χ,rfl⟩ := hex
  have he := Nat.card_congr ((evaluation x).fiberEquivKer χ)
  have hc := (evaluation x).ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (evaluation x)).toEquiv,
    count_values,_root_.RHTower.deningerCharacter_card] at hc
  change Nat.card {η : G →* ℂˣ // evaluation x η=evaluation x χ} * _=_
  rw [he,mul_comm]
  exact hc.symm

variable (H : Subgroup G) (ψ : H →* ℂˣ)

/-- The smallest power whose value is prescribed by the subgroup. -/
abbrev relativeOrder (x : G) := orderOf ((QuotientGroup.mk' H) x)

def prescribedPower (x : G) : H :=
  ⟨x^(relativeOrder H x),(QuotientGroup.eq_one_iff _).1 (by
    change (QuotientGroup.mk' H) (x^(relativeOrder H x))=1
    rw [map_pow,pow_orderOf_eq_one])⟩

theorem power_value (χ : Extensions H ψ) (x : G) :
    (χ.val x)^(relativeOrder H x) = ψ (prescribedPower H x) := by
  rw [← map_pow]
  exact DFunLike.congr_fun χ.property (prescribedPower H x)

/-- Exact support of the evaluation of a restriction fiber. -/
theorem value_occurs_iff [Finite (G ⧸ H)] (x : G) (z : ℂˣ) :
    (∃ χ : Extensions H ψ, χ.val x=z) ↔ z^(relativeOrder H x)=ψ (prescribedPower H x) := by
  constructor
  · rintro ⟨χ,rfl⟩
    exact power_value H ψ χ x
  · intro hz
    let b := (extensions_nonempty H ψ).some
    have he : z/b.val x ∈ (evaluation ((QuotientGroup.mk' H) x)).range := by
      rw [evaluation_range,mem_rootsOfUnity,div_pow]
      change z^(relativeOrder H x)/(b.val x)^(relativeOrder H x)=1
      rw [hz,power_value H ψ b x,div_self]
    obtain ⟨η,hη⟩ := he
    refine ⟨twistEquiv H ψ b η,?_⟩
    rw [twist_value,show η ((QuotientGroup.mk' H) x)=z/b.val x from hη]
    group

/-- Every admissible value has exactly [G:H]/e extensions. The product
form retains divisibility of the index as part of the conclusion. -/
theorem value_multiplicity [Finite (G ⧸ H)] (x : G) (z : ℂˣ)
    (hz : z^(relativeOrder H x)=ψ (prescribedPower H x)) :
    Nat.card {χ : Extensions H ψ // χ.val x=z} * relativeOrder H x = Nat.card (G ⧸ H) := by
  obtain ⟨b,hb⟩ := (value_occurs_iff H ψ x z).2 hz
  let q := (QuotientGroup.mk' H) x
  have e := (twistEquiv H ψ b).subtypeEquiv (p := fun η => η q=1)
    (q := fun χ => χ.val x=z) (fun η => by rw [twist_value,hb]; simp [q])
  rw [← Nat.card_congr e]
  exact evaluation_multiplicity q 1 (one_pow _)

/-- Joint conditioning on any intermediate subgroup has a uniform remaining
multiplicity, including an infinite ambient group with finite quotient. -/
theorem joint_multiplicity (J : Subgroup G) (hHJ : H ≤ J) [Finite (G ⧸ J)]
    (φ : J →* ℂˣ) (hφ : φ.comp (Subgroup.inclusion hHJ)=ψ) :
    Nat.card {χ : Extensions H ψ // χ.val.comp J.subtype=φ} = Nat.card (G ⧸ J) := by
  let e : {χ : Extensions H ψ // χ.val.comp J.subtype=φ} ≃ Extensions J φ :=
    { toFun := fun χ => ⟨χ.val.val,χ.property⟩
      invFun := fun χ => ⟨⟨χ.val,by
        ext s
        exact (DFunLike.congr_fun χ.property ((Subgroup.inclusion hHJ) s)).trans
          (DFunLike.congr_fun hφ s)⟩,χ.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (card_extensions J φ)

end GaloisForLFunctions.HeckeLFunctions.CharacterExtensions
