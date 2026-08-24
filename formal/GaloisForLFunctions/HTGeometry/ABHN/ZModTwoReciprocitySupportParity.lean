import GaloisForLFunctions.HTGeometry.ABHN.FinsuppReciprocitySupportCardinality
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2CarryReciprocityProfile
import Mathlib.Data.ZMod.Basic

/-!
# Parity of order-two reciprocity support

For `ℤ/2ℤ`-valued local invariants, zero-sum reciprocity is exactly even support cardinality.
The result transports across any additive equivalence with `ℤ/2ℤ` and specializes to
quadratic cyclic `H²` carry packets. This is the abstract parity law behind the classical fact
that quaternion ramification occurs at an even number of places.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v

/-- Over `ℤ/2ℤ`, a finite profile sums to the parity of its support cardinality. -/
theorem finsuppZModTwo_natCast_support_card_eq_sum
    {ι : Type u} [DecidableEq ι] (f : ι →₀ ZMod 2) :
    (f.support.card : ZMod 2) = f.sum (fun _ x => x) := by
  have hval : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  change (f.support.card : ZMod 2) = ∑ i ∈ f.support, f i
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.cast_one]
  exact (hval (f i) (Finsupp.mem_support_iff.mp hi)).symm

/-- A `ℤ/2ℤ` profile has zero sum exactly when its support cardinality is even. -/
theorem finsuppZModTwo_sum_eq_zero_iff_even_support_card
    {ι : Type u} [DecidableEq ι] (f : ι →₀ ZMod 2) :
    f.sum (fun _ x => x) = 0 ↔ Even f.support.card := by
  rw [← finsuppZModTwo_natCast_support_card_eq_sum,
    ZMod.natCast_eq_zero_iff_even]

/-- Zero-sum reciprocity in any group equivalent to `ℤ/2ℤ` is exactly even support. -/
theorem finsuppAddEquivZModTwo_sum_eq_zero_iff_even_support_card
    {ι : Type u} [DecidableEq ι]
    {A : Type v} [AddCommGroup A] (e : A ≃+ ZMod 2) (f : ι →₀ A) :
    f.sum (fun _ x => e x) = 0 ↔ Even f.support.card := by
  let g : ι →₀ ZMod 2 :=
    Finsupp.mapRange.addMonoidHom e.toAddMonoidHom f
  have hsum : g.sum (fun _ x => x) = f.sum (fun _ x => e x) := by
    dsimp [g]
    change (Finsupp.mapRange (fun x => e x) e.map_zero f).sum (fun _ x => x) = _
    rw [Finsupp.sum_mapRange_index]
    intro i
    rfl
  have hsupp : g.support = f.support := by
    ext i
    simp [g]
  rw [← hsum, finsuppZModTwo_sum_eq_zero_iff_even_support_card, hsupp]

/-- Quadratic cyclic carry `H²`, expressed directly in its `ℤ/2ℤ` coordinate. -/
noncomputable def cyclicGaloisCarryH2ZModTwoEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod 2) :
    cyclicGaloisH2 K L ≃+ ZMod 2 :=
  (cyclicGaloisCarryH2TorsionEquiv K L 2 (by decide) qEquiv).trans
    (zmodRatModIntAddEquivNTorsion 2 (by decide)).symm

/-- A quadratic cyclic carry profile has zero invariant sum exactly when its support is even. -/
theorem cyclicGaloisCarryH2Profile_sum_eq_zero_iff_even_support_card
    {ι : Type u} [DecidableEq ι]
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod 2)
    (f : ι →₀ cyclicGaloisH2 K L) :
    cyclicGaloisCarryH2ProfileInvariantSumAddHom ι K L 2 (by decide) qEquiv f = 0 ↔
      Even f.support.card := by
  let eT := cyclicGaloisCarryH2TorsionEquiv K L 2 (by decide) qEquiv
  let d := (zmodRatModIntAddEquivNTorsion 2 (by decide)).symm
  rw [← finsuppAddEquivZModTwo_sum_eq_zero_iff_even_support_card
    (eT.trans d) f]
  change f.sum (fun _ x => eT x) = 0 ↔ f.sum (fun _ x => d (eT x)) = 0
  constructor
  · intro h
    have hmap := congrArg d h
    rw [map_zero, map_finsuppSum] at hmap
    exact hmap
  · intro h
    apply d.injective
    rw [map_zero, map_finsuppSum]
    exact h

/-- Product-one reciprocity for quadratic cyclic carry classes is exactly even support. -/
theorem cyclicGaloisCarryH2Profile_product_eq_one_iff_even_support_card
    {ι : Type u} [DecidableEq ι]
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod 2)
    (f : ι →₀ cyclicGaloisH2 K L) :
    f.prod (fun _ z => cyclicGaloisCarryH2TorsionStdAddChar
      K L 2 (by decide) qEquiv z) = 1 ↔ Even f.support.card :=
  (cyclicGaloisCarryH2Profile_product_eq_one_iff_sum_eq_zero
      ι K L 2 (by decide) qEquiv f).trans
    (cyclicGaloisCarryH2Profile_sum_eq_zero_iff_even_support_card K L qEquiv f)

end GaloisForLFunctions.HTGeometry.ABHN
