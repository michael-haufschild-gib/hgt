import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysClosureFractionField

/-!
# The `𝒪`-valued points described on the local ring at the specialisation

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 13.4
(`t44`), the equivalence of the descriptions by `P_y` and by `P'_y`.

A pointed multiplicative map `P_y : 𝒪_{X,y} → 𝒪` whose value depends only on the value at the
generisation `x` factors through `𝒪_{closure {x} , y}`, because two germs have the same value at
`x` exactly when they differ by an element of the prime cutting out the closure of `x`.  Under this
factorization Deninger's conditions 1) and 3) become 1') and 3'), so the two descriptions of the
`𝒪`-valued points agree.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory HTGeometry

noncomputable section

universe u

variable {X : Scheme.{u}} {x y : X}

/-- Two germs at `y` have the same class in `𝒪_{closure {x} , y}` exactly when they have the same
value at `x`. -/
theorem deningerClosureMk_eq_iff (h : x ⤳ y) (a b : X.presheaf.stalk y) :
    DeningerClosureLocalRing.mk h a = DeningerClosureLocalRing.mk h b ↔
      stalkValue h a = stalkValue h b := by
  have key : DeningerClosureLocalRing.mk h a = DeningerClosureLocalRing.mk h b ↔
      a - b ∈ deningerClosureIdeal h := Ideal.Quotient.mk_eq_mk_iff_sub_mem a b
  rw [key]
  show a - b ∈ RingHom.ker (stalkValueHom h) ↔ _
  rw [RingHom.mem_ker, map_sub, sub_eq_zero]
  exact Iff.rfl

theorem deningerClosureMk_eq_zero_iff (h : x ⤳ y) (a : X.presheaf.stalk y) :
    DeningerClosureLocalRing.mk h a = 0 ↔ stalkValue h a = 0 := by
  have h0 : (0 : DeningerClosureLocalRing h) = DeningerClosureLocalRing.mk h 0 :=
    (map_zero _).symm
  rw [h0, deningerClosureMk_eq_iff, stalkValue_zero]

/-- **Deninger, Proposition 13.4 (`t44`).**  An `𝒪`-valued point of `W_rat (X)` described by a
pointed multiplicative map on the local ring at the specialisation. -/
structure DeningerValuedLocalTriple (X : Scheme.{u}) (O : Type u) [CommRing O]
    [IsLocalRing O] where
  /-- The generic point. -/
  gen : X
  /-- The specialisation. -/
  spec : X
  /-- `spec` lies in the closure of `gen`. -/
  specializes : gen ⤳ spec
  /-- The pointed multiplicative map on `𝒪_{X , spec}`. -/
  map : X.presheaf.stalk spec →*₀ O
  /-- Condition 1): a germ not vanishing at `gen` has nonzero value. -/
  map_ne_zero : ∀ f : X.presheaf.stalk spec, stalkValue specializes f ≠ 0 → map f ≠ 0
  /-- Condition 2): the value depends only on the value at `gen`. -/
  map_congr : ∀ f g : X.presheaf.stalk spec,
    stalkValue specializes f = stalkValue specializes g → map f = map g
  /-- Condition 3): the residue of the value depends only on the value at `spec`. -/
  map_residue : ∀ f g : X.presheaf.stalk spec,
    (X.residue spec).hom f = (X.residue spec).hom g → map f - map g ∈ IsLocalRing.maximalIdeal O

variable {O : Type u} [CommRing O] [IsLocalRing O]

theorem DeningerValuedTriple.ext' {T U : DeningerValuedTriple X O} (hg : T.gen = U.gen)
    (hs : T.spec = U.spec) (hm : HEq T.map U.map) : T = U := by
  obtain ⟨g, s, hsp, m, p1, p2⟩ := T
  obtain ⟨g', s', hsp', m', p1', p2'⟩ := U
  cases hg
  cases hs
  cases hm
  rfl

theorem DeningerValuedLocalTriple.ext' {T U : DeningerValuedLocalTriple X O} (hg : T.gen = U.gen)
    (hs : T.spec = U.spec) (hm : HEq T.map U.map) : T = U := by
  obtain ⟨g, s, hsp, m, p1, p2, p3⟩ := T
  obtain ⟨g', s', hsp', m', p1', p2', p3'⟩ := U
  cases hg
  cases hs
  cases hm
  rfl

/-- The factorization of `P_y` through `𝒪_{closure {gen} , spec}`. -/
def DeningerValuedLocalTriple.closureMap (T : DeningerValuedLocalTriple X O) :
    DeningerClosureLocalRing T.specializes →*₀ O where
  toFun d := T.map (Function.surjInv (DeningerClosureLocalRing.mk_surjective T.specializes) d)
  map_zero' := by
    have h := Function.surjInv_eq (DeningerClosureLocalRing.mk_surjective T.specializes)
      (0 : DeningerClosureLocalRing T.specializes)
    refine (T.map_congr _ 0 ?_).trans (map_zero T.map)
    rw [stalkValue_zero, ← deningerClosureMk_eq_zero_iff, h]
  map_one' := by
    have h := Function.surjInv_eq (DeningerClosureLocalRing.mk_surjective T.specializes)
      (1 : DeningerClosureLocalRing T.specializes)
    refine (T.map_congr _ 1 ?_).trans (map_one T.map)
    rw [← deningerClosureMk_eq_iff, h, map_one]
  map_mul' d e := by
    set a := Function.surjInv (DeningerClosureLocalRing.mk_surjective T.specializes) d with ha
    set b := Function.surjInv (DeningerClosureLocalRing.mk_surjective T.specializes) e with hb
    set c := Function.surjInv (DeningerClosureLocalRing.mk_surjective T.specializes) (d * e)
      with hc
    have hda := Function.surjInv_eq (DeningerClosureLocalRing.mk_surjective T.specializes) d
    have heb := Function.surjInv_eq (DeningerClosureLocalRing.mk_surjective T.specializes) e
    have hce := Function.surjInv_eq (DeningerClosureLocalRing.mk_surjective T.specializes) (d * e)
    have : DeningerClosureLocalRing.mk T.specializes c
        = DeningerClosureLocalRing.mk T.specializes (a * b) := by
      rw [hce, map_mul, hda, heb]
    rw [(T.map_congr c (a * b) ((deningerClosureMk_eq_iff _ _ _).1 this)), map_mul]

@[simp] theorem DeningerValuedLocalTriple.closureMap_mk (T : DeningerValuedLocalTriple X O)
    (a : X.presheaf.stalk T.spec) :
    T.closureMap (DeningerClosureLocalRing.mk T.specializes a) = T.map a := by
  refine T.map_congr _ a ?_
  rw [← deningerClosureMk_eq_iff]
  exact Function.surjInv_eq (DeningerClosureLocalRing.mk_surjective T.specializes) _

/-- **Deninger, Proposition 13.4 (`t44`).**  The description by `P_y` passes to the description
by `P'_y`. -/
@[reducible] def DeningerValuedLocalTriple.toValuedTriple (T : DeningerValuedLocalTriple X O) :
    DeningerValuedTriple X O where
  gen := T.gen
  spec := T.spec
  specializes := T.specializes
  map := T.closureMap
  map_ne_zero := by
    intro d hd
    obtain ⟨a, rfl⟩ := DeningerClosureLocalRing.mk_surjective T.specializes d
    rw [T.closureMap_mk]
    exact T.map_ne_zero a (fun hc => hd ((deningerClosureMk_eq_zero_iff _ _).2 hc))
  map_residue := by
    intro d e hde
    obtain ⟨a, rfl⟩ := DeningerClosureLocalRing.mk_surjective T.specializes d
    obtain ⟨b, rfl⟩ := DeningerClosureLocalRing.mk_surjective T.specializes e
    rw [T.closureMap_mk, T.closureMap_mk]
    exact T.map_residue a b hde

/-- **Deninger, Proposition 13.4 (`t44`).**  The description by `P'_y` passes to the description
by `P_y`. -/
@[reducible] def DeningerValuedTriple.toLocalTriple (T : DeningerValuedTriple X O) :
    DeningerValuedLocalTriple X O where
  gen := T.gen
  spec := T.spec
  specializes := T.specializes
  map := T.map.comp (DeningerClosureLocalRing.mk T.specializes : _ →+* _).toMonoidWithZeroHom
  map_ne_zero := by
    intro f hf
    exact T.map_ne_zero (DeningerClosureLocalRing.mk T.specializes f)
      (fun hc => hf ((deningerClosureMk_eq_zero_iff _ _).1 hc))
  map_congr := by
    intro f g hfg
    show T.map (DeningerClosureLocalRing.mk T.specializes f)
      = T.map (DeningerClosureLocalRing.mk T.specializes g)
    rw [(deningerClosureMk_eq_iff T.specializes f g).2 hfg]
  map_residue := by
    intro f g hfg
    refine T.map_residue (DeningerClosureLocalRing.mk T.specializes f)
      (DeningerClosureLocalRing.mk T.specializes g) ?_
    rw [deningerClosureResidue_mk, deningerClosureResidue_mk, hfg]

/-- **Deninger, Proposition 13.4 (`t44`).**  The two descriptions of the `𝒪`-valued points of
`W_rat (X)`, by a pointed multiplicative map on `𝒪_{X,y}` satisfying 1), 2), 3) and by one on
`𝒪_{closure {x} , y}` satisfying 1'), 3'), are the same. -/
def deningerValuedLocalTripleEquiv :
    DeningerValuedLocalTriple X O ≃ DeningerValuedTriple X O where
  toFun := DeningerValuedLocalTriple.toValuedTriple
  invFun := DeningerValuedTriple.toLocalTriple
  left_inv T := by
    refine DeningerValuedLocalTriple.ext' rfl rfl (heq_of_eq ?_)
    refine MonoidWithZeroHom.ext fun a => ?_
    show T.closureMap (DeningerClosureLocalRing.mk T.specializes a) = T.map a
    exact T.closureMap_mk a
  right_inv T := by
    refine DeningerValuedTriple.ext' rfl rfl (heq_of_eq ?_)
    refine MonoidWithZeroHom.ext fun d => ?_
    obtain ⟨a, rfl⟩ := DeningerClosureLocalRing.mk_surjective T.specializes d
    exact (T.toLocalTriple).closureMap_mk a

end

end RHTower
