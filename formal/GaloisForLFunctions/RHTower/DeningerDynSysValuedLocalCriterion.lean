import GaloisForLFunctions.RHTower.DeningerDynSysValuedLocalTriple
import GaloisForLFunctions.RHTower.DeningerDynSysValuedPointsAffine

/-!
# A pointwise criterion for the `𝒪`-valued points

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 13.5 (`t45`),
the translation between conditions a'), b') and Deninger's conditions 1), 2), 3).

Deninger's three conditions on `P_y : 𝒪_{X,y} → 𝒪` say that `P_y` is unchanged by adding an
element of its zero set, that it is additive modulo `𝔪` there, and that its zero set and the
preimage of `𝔪` are the kernels of evaluation at `x` and at `y`.  Conversely those four statements
rebuild the three conditions, because evaluation at a point is additive: two germs with the same
value differ by one of value zero.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory HTGeometry IsLocalRing

noncomputable section

universe u

variable {X : Scheme.{u}} {x y : X} {O : Type u} [CommRing O] [IsLocalRing O]

/-- **Deninger, Corollary 13.5 (`t45`).**  The pointwise conditions build an `𝒪`-valued point. -/
def deningerValuedLocalTripleOfConditions (h : x ⤳ y) (P : X.presheaf.stalk y →*₀ O)
    (hA : DeningerAdditiveOnZeros P) (hB : DeningerAdditiveModMax P)
    (hZ : ∀ f, P f = 0 ↔ stalkValue h f = 0)
    (hM : ∀ f, P f ∈ maximalIdeal O ↔ (X.residue y).hom f = 0) :
    DeningerValuedLocalTriple X O where
  gen := x
  spec := y
  specializes := h
  map := P
  map_ne_zero := fun f hf hc => hf ((hZ f).1 hc)
  map_congr := by
    intro f g hfg
    have h0 : P (f - g) = 0 := by
      refine (hZ (f - g)).2 ?_
      rw [stalkValue_sub, hfg, sub_self]
    have := hA g (f - g) h0
    rwa [add_sub_cancel] at this
  map_residue := by
    intro f g hfg
    have h0 : P (f - g) ∈ maximalIdeal O := by
      refine (hM (f - g)).2 ?_
      rw [map_sub, hfg, sub_self]
    have := hB g (f - g) h0
    rwa [add_sub_cancel] at this

variable (T : DeningerValuedLocalTriple X O)

theorem DeningerValuedLocalTriple.map_eq_zero_iff (f : X.presheaf.stalk T.spec) :
    T.map f = 0 ↔ stalkValue T.specializes f = 0 := by
  constructor
  · intro hf
    by_contra hc
    exact T.map_ne_zero f hc hf
  · intro hf
    have := T.map_congr f 0 (by rw [hf, stalkValue_zero])
    rw [this, map_zero]

theorem DeningerValuedLocalTriple.map_mem_maximalIdeal_iff (f : X.presheaf.stalk T.spec) :
    T.map f ∈ maximalIdeal O ↔ (X.residue T.spec).hom f = 0 := by
  constructor
  · intro hf
    by_contra hc
    obtain ⟨g, hg⟩ := X.residue_surjective T.spec ((X.residue T.spec).hom f)⁻¹
    have hone : (X.residue T.spec).hom (f * g) = (X.residue T.spec).hom 1 := by
      rw [map_mul, hg, map_one, mul_inv_cancel₀ hc]
    have hmem := T.map_residue (f * g) 1 hone
    rw [map_mul, map_one] at hmem
    have hprod : T.map f * T.map g ∈ maximalIdeal O := Ideal.mul_mem_right _ _ hf
    have : (1 : O) ∈ maximalIdeal O := by
      have := Ideal.sub_mem _ hprod hmem
      rwa [sub_sub_cancel] at this
    exact (maximalIdeal.isMaximal O).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  · intro hf
    have := T.map_residue f 0 (by rw [hf, map_zero])
    rw [map_zero, sub_zero] at this
    exact this

theorem DeningerValuedLocalTriple.additiveOnZeros : DeningerAdditiveOnZeros T.map := by
  intro f f' hf'
  refine T.map_congr (f + f') f ?_
  rw [stalkValue_add, (T.map_eq_zero_iff f').1 hf', add_zero]

theorem DeningerValuedLocalTriple.additiveModMax : DeningerAdditiveModMax T.map := by
  intro f f' hf'
  refine T.map_residue (f + f') f ?_
  rw [map_add, (T.map_mem_maximalIdeal_iff f').1 hf', add_zero]

end

end RHTower
