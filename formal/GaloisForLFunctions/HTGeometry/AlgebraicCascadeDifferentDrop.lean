import GaloisForLFunctions.HTGeometry.AlgebraicCascadePlace
import GaloisForLFunctions.HTGeometry.TopDegreeSharpDrop
import GaloisForLFunctions.HTGeometry.IntegralGeneratorDerivationClearing
import GaloisForLFunctions.HTGeometry.PlaceDerivationValuationDrop
import GaloisForLFunctions.HTGeometry.DedekindOrderMonogenic
import GaloisForLFunctions.HTGeometry.KummerDedekindDifferentOrder

/-!
# The extended derivation drops every place of the cascade model boundedly

The derivation `∂/∂u` at the uniformiser of the degree at infinity preserves the valuation ring of
the coordinate field.  On the algebraic model its extension need not preserve the integral closure,
but the closure is monogenic over the valuation ring, and the derivative of the generator's minimal
polynomial clears the extended derivation.  Feeding that clearing element into the adic-valuation
drop gives: at every place `Q` of the integral closure there is a positive integer `e` with

`v_Q(δ f) ≤ v_Q(f) · exp e`  for every `f` in the model,

and when `Q` lies over the maximal ideal with Kummer–Dedekind multiplicity `e`, that multiplicity
itself works — the tame bound `ord_Q(𝔡) ≤ e − 1` of the different.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Polynomial IsDedekindDomain IsLocalRing

variable (m : ℕ) (p : Polynomial CascadeField) [Fact (Irreducible p)]

/-! ## Constants of the valuation ring -/

theorem natCast_topOrd_eq_zero {n : ℕ} (hn : n ≠ 0) :
    topOrd m ((n : ℕ) : CascadeField) = (0 : ℤ) := by
  have hcast : ((n : ℕ) : CascadeField)
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField ((n : ℕ) : MvPolynomial ℕ ℂ) := by
    rw [map_natCast]
  have hne : ((n : ℕ) : MvPolynomial ℕ ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [hcast, topOrd_algebraMap m hne]
  have hdeg : MvPolynomial.degreeOf m ((n : ℕ) : MvPolynomial ℕ ℂ) = 0 := by
    have hC : ((n : ℕ) : MvPolynomial ℕ ℂ) = MvPolynomial.C ((n : ℕ) : ℂ) := by
      rw [map_natCast]
    rw [hC, MvPolynomial.degreeOf_C]
  rw [hdeg]
  norm_num

theorem isUnit_natCast_topInt {n : ℕ} (hn : n ≠ 0) : IsUnit ((n : ℕ) : topInt m) := by
  have hne : ((n : ℕ) : CascadeField) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hinv_ne : ((n : ℕ) : CascadeField)⁻¹ ≠ 0 := inv_ne_zero hne
  have hordn : topOrd m ((n : ℕ) : CascadeField) = (0 : ℤ) := natCast_topOrd_eq_zero m hn
  have hordinv : topOrd m ((n : ℕ) : CascadeField)⁻¹ = (0 : ℤ) := by
    have hmul := topOrd_mul m ((n : ℕ) : CascadeField) ((n : ℕ) : CascadeField)⁻¹
    rw [mul_inv_cancel₀ hne, topOrd_one, hordn] at hmul
    have := hmul.symm
    rwa [show ((0 : ℤ) : WithTop ℤ) + topOrd m ((n : ℕ) : CascadeField)⁻¹
        = topOrd m ((n : ℕ) : CascadeField)⁻¹ from zero_add _] at this
  have hmemn : ((n : ℕ) : CascadeField) ∈ topInt m := by
    rw [mem_topInt, hordn]
    exact le_rfl
  have hmeminv : ((n : ℕ) : CascadeField)⁻¹ ∈ topInt m := by
    rw [mem_topInt, hordinv]
    exact le_rfl
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmeminv⟩, ?_⟩
  have hval : (((n : ℕ) : topInt m) : CascadeField) = ((n : ℕ) : CascadeField) := by
    push_cast
    rfl
  ext
  push_cast [hval]
  exact mul_inv_cancel₀ hne

instance charZero_residueField_topInt : CharZero (ResidueField (topInt m)) := by
  refine ⟨fun a b hab => ?_⟩
  by_contra hne
  rcases Nat.lt_or_ge a b with hlt | hge
  · have hdiff : ((b - a : ℕ) : ResidueField (topInt m)) = 0 := by
      push_cast [Nat.cast_sub hlt.le]
      rw [← hab]
      ring
    have hd0 : b - a ≠ 0 := by omega
    have hunit := (isUnit_natCast_topInt m hd0).map (residue (topInt m))
    rw [show (residue (topInt m)) (((b - a : ℕ) : topInt m))
        = ((b - a : ℕ) : ResidueField (topInt m)) from map_natCast _ _] at hunit
    rw [hdiff] at hunit
    exact hunit.ne_zero rfl
  · rcases Nat.lt_or_ge b a with hlt' | hge'
    · have hdiff : ((a - b : ℕ) : ResidueField (topInt m)) = 0 := by
        push_cast [Nat.cast_sub hlt'.le]
        rw [hab]
        ring
      have hd0 : a - b ≠ 0 := by omega
      have hunit := (isUnit_natCast_topInt m hd0).map (residue (topInt m))
      rw [show (residue (topInt m)) (((a - b : ℕ) : topInt m))
          = ((a - b : ℕ) : ResidueField (topInt m)) from map_natCast _ _] at hunit
      rw [hdiff] at hunit
      exact hunit.ne_zero rfl
    · exact hne (by omega)

end GaloisForLFunctions.HTGeometry
