import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! Quasi-finite maps preserve strict specialization. A finite endomorphism with a
fixed point on an irreducible locally Noetherian scheme is surjective. -/

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FiniteEndFlat

private theorem strictMono_of_locallyQuasiFinite {X Y : Scheme.{0}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] : StrictMono (f : X → Y) := by
  intro x y hxy
  have h : y ⤳ x := hxy.le
  refine lt_of_le_not_ge (show f y ⤳ f x from h.map f.continuous) fun h' => hxy.not_ge ?_
  have e : f y = f x := ((h.map f.continuous).antisymm h').eq
  haveI := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have h₂ : (⟨y, e⟩ : f ⁻¹' {f x}) ⤳ ⟨x, rfl⟩ := (subtype_specializes_iff _ _).mpr h
  have hyx : y = x := congrArg Subtype.val h₂.eq
  exact hyx.le

/-- Height in the specialization interval above a fixed point forces the generic point
to map to itself. -/
theorem apply_genericPoint {X : Scheme.{0}} [IrreducibleSpace X] [IsLocallyNoetherian X]
    (f : X ⟶ X) [LocallyQuasiFinite f] {o : X} (ho : f o = o) :
    f (genericPoint X) = genericPoint X := by
  have hs := strictMono_of_locallyQuasiFinite f
  let g : Set.Ici o → Set.Ici o := fun x =>
    ⟨f x, ho.ge.trans (show f x ⤳ f o from Specializes.map (show x.1 ⤳ o from x.2) f.continuous)⟩
  have hg : StrictMono g := fun x y h => hs h
  let ξ : Set.Ici o := ⟨genericPoint X, genericPoint_specializes o⟩
  have hfin : Order.height (g ξ) < ⊤ := by
    have h := Order.height_le_krullDim (g ξ)
    rw [← Order.coheight_eq_krullDim_Ici, ← ringKrullDim_stalk_eq_coheight] at h
    exact WithBot.coe_lt_coe.mp (h.trans_lt ringKrullDim_lt_top)
  have hle : g ξ ≤ ξ := genericPoint_specializes (f (genericPoint X))
  have hge : ξ ≤ g ξ := by
    by_contra h
    exact (Order.height_strictMono (lt_of_le_not_ge hle h) hfin).not_ge
      (Order.height_le_height_apply_of_strictMono g hg ξ)
  exact (Specializes.antisymm (show f (genericPoint X) ⤳ genericPoint X from hge)
    (genericPoint_specializes _)).eq

/-- A finite endomorphism fixing a point has closed image containing the generic point. -/
theorem surjective_of_isFinite_of_fixed_point {X : Scheme.{0}}
    [IrreducibleSpace X] [IsLocallyNoetherian X] (f : X ⟶ X)
    [IsFinite f] {o : X} (ho : f o = o) : Surjective f :=
  ⟨fun y => (genericPoint_specializes y).mem_closed f.isClosedMap.isClosed_range
    ⟨genericPoint X, apply_genericPoint f ho⟩⟩

end GlobalTheory.FiniteEndFlat
