import GaloisForLFunctions.HTGeometry.SchemeOrderSupportFinite
import GaloisForLFunctions.HTGeometry.LocalRamificationOrderLaw

/-!
# The pullback law for orders of vanishing on a scheme

At a codimension-one point whose local ring is a discrete valuation ring, the order of vanishing
of a rational function is the additive valuation of the local ring.  A homomorphism of the local
rings compatible with a homomorphism of the function field therefore scales the order of every
rational function by its ramification index:

`ord (pullback of f) at z = e * ord f at w`.

This is the scheme-level form of the divisor pullback formula.  mathlib defines the order of
vanishing at a codimension-one point but provides no pullback law for it.
-/

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry Order IsDiscreteValuationRing

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

omit [IsLocallyNoetherian X] in
theorem algebraMap_stalk_ne_zero {z : X} {s : X.presheaf.stalk z} (hs : s ≠ 0) :
    algebraMap (X.presheaf.stalk z) X.functionField s ≠ 0 := fun h =>
  hs (IsFractionRing.injective (X.presheaf.stalk z) X.functionField (by rw [h, map_zero]))

/-- **The order of vanishing is the additive valuation of the local ring.** -/
theorem ord_algebraMap_stalk_eq_addVal {z : X} (hz : coheight z = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk z)]
    {s : X.presheaf.stalk z} (hs : s ≠ 0) {n : ℕ}
    (hn : addVal (X.presheaf.stalk z) s = (n : ℕ∞)) :
    Scheme.ord (algebraMap (X.presheaf.stalk z) X.functionField s) z = (n : ℤ) := by
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  rw [Scheme.ord_eq_iff hz (algebraMap_stalk_ne_zero hs)]
  show Ring.ordFrac (X.presheaf.stalk z)
    (algebraMap (X.presheaf.stalk z) X.functionField s) = _
  rw [Ring.ordFrac_eq_ord (R := X.presheaf.stalk z) (K := X.functionField) hs]
  exact Ring.ordMonoidWithZeroHom_eq_coe (R := X.presheaf.stalk z)
    (mem_nonZeroDivisors_of_ne_zero hs) (by rw [Ring.ord_eq_addVal, hn])

omit [IsLocallyNoetherian X] in
theorem exists_natCast_addVal {z : X} [IsDiscreteValuationRing (X.presheaf.stalk z)]
    {s : X.presheaf.stalk z} (hs : s ≠ 0) :
    ∃ n : ℕ, addVal (X.presheaf.stalk z) s = (n : ℕ∞) := by
  refine ⟨(addVal (X.presheaf.stalk z) s).toNat, (ENat.coe_toNat ?_).symm⟩
  rw [Ne, addVal_eq_top_iff]
  exact hs

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]

/-- **The order of a pullback scales by the ramification index.**  The data is a homomorphism `ψ`
of the local rings at two codimension-one points together with a homomorphism `Φ` of the function
fields extending it, which is exactly what a morphism of schemes carrying one point to the other
supplies. -/
theorem ord_pullback_eq_mul_ramification
    {z : X} {w : Y} (hz : coheight z = 1) (hw : coheight w = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk z)]
    [IsDiscreteValuationRing (Y.presheaf.stalk w)]
    (ψ : Y.presheaf.stalk w →+* X.presheaf.stalk z)
    (Φ : Y.functionField →+* X.functionField)
    (hcomp : ∀ s : Y.presheaf.stalk w,
      Φ (algebraMap (Y.presheaf.stalk w) Y.functionField s) =
        algebraMap (X.presheaf.stalk z) X.functionField (ψ s))
    {π : Y.presheaf.stalk w} (hπ : Irreducible π) (e : ℕ)
    (he : addVal (X.presheaf.stalk z) (ψ π) = (e : ℕ∞))
    {f : Y.functionField} (hf : f ≠ 0) :
    Scheme.ord (Φ f) z = (e : ℤ) * Scheme.ord f w := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Y.presheaf.stalk w) f
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hbne : algebraMap (Y.presheaf.stalk w) Y.functionField b ≠ 0 :=
    algebraMap_stalk_ne_zero hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact hf hab.symm
  have hfrac : f * algebraMap (Y.presheaf.stalk w) Y.functionField b =
      algebraMap (Y.presheaf.stalk w) Y.functionField a := by
    rw [← hab]
    exact div_mul_cancel₀ _ hbne
  obtain ⟨na, hna⟩ := exists_natCast_addVal ha0
  obtain ⟨nb, hnb⟩ := exists_natCast_addVal hb0
  have hpa : addVal (X.presheaf.stalk z) (ψ a) = ((e * na : ℕ) : ℕ∞) := by
    rw [addVal_map_eq_mul_ramification ψ hπ e he a ha0, hna, Nat.cast_mul]
  have hpb : addVal (X.presheaf.stalk z) (ψ b) = ((e * nb : ℕ) : ℕ∞) := by
    rw [addVal_map_eq_mul_ramification ψ hπ e he b hb0, hnb, Nat.cast_mul]
  have hψa : ψ a ≠ 0 := by
    intro h
    rw [h, AddValuation.map_zero] at hpa
    exact (ENat.top_ne_coe _) hpa
  have hψb : ψ b ≠ 0 := by
    intro h
    rw [h, AddValuation.map_zero] at hpb
    exact (ENat.top_ne_coe _) hpb
  have horda : Scheme.ord (algebraMap (Y.presheaf.stalk w) Y.functionField a) w = (na : ℤ) :=
    ord_algebraMap_stalk_eq_addVal hw ha0 hna
  have hordb : Scheme.ord (algebraMap (Y.presheaf.stalk w) Y.functionField b) w = (nb : ℤ) :=
    ord_algebraMap_stalk_eq_addVal hw hb0 hnb
  have hdown : Scheme.ord f w = (na : ℤ) - (nb : ℤ) := by
    have := Scheme.ord_mul (x := w) hf hbne
    rw [hfrac, horda, hordb] at this
    omega
  have hupfrac : Φ f * algebraMap (X.presheaf.stalk z) X.functionField (ψ b) =
      algebraMap (X.presheaf.stalk z) X.functionField (ψ a) := by
    rw [← hcomp a, ← hcomp b, ← map_mul, hfrac]
  have horda' : Scheme.ord (algebraMap (X.presheaf.stalk z) X.functionField (ψ a)) z =
      ((e * na : ℕ) : ℤ) := ord_algebraMap_stalk_eq_addVal hz hψa hpa
  have hordb' : Scheme.ord (algebraMap (X.presheaf.stalk z) X.functionField (ψ b)) z =
      ((e * nb : ℕ) : ℤ) := ord_algebraMap_stalk_eq_addVal hz hψb hpb
  have hΦf : Φ f ≠ 0 := fun h => hf (Φ.injective (by rw [h, map_zero]))
  have hup : Scheme.ord (Φ f) z = ((e * na : ℕ) : ℤ) - ((e * nb : ℕ) : ℤ) := by
    have := Scheme.ord_mul (x := z) hΦf (algebraMap_stalk_ne_zero hψb)
    rw [hupfrac, horda', hordb'] at this
    omega
  rw [hup, hdown]
  push_cast
  ring

end GaloisForLFunctions.HTGeometry
