import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteExponentWeilCharacter
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.SmoothWeilAction

/-! An unramified twist makes a smooth Weil character finite-exponent.
The kernel of the global abelianization map has degree zero, so this
twist is trivial there. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GaloisForLFunctions.HTGeometry

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}

theorem deg_eq_zero_of_toMaxAb_eq_one (h : IsPlaceOver A v) (s : Weil h)
    (hs : toMaxAb K Ω s.val = 1) : deg s = 0 := by
  obtain ⟨a, hca, ha, -⟩ := exists_global_idelic_artin K Ω
  obtain ⟨b, -, hd, hb⟩ := exists_inverse_arithmeticArtin_on_Weil K Ω a hca ha h
  have h1 : b s = 1 := by
    apply globalArtin_injective_finiteEmbedding a hca ha v
    change a (toCompactIdeleClassQuotient K (finiteEmbedding v (b s))) =
      a (toCompactIdeleClassQuotient K (finiteEmbedding v 1))
    rw [hb, hs, map_one, map_one, map_one]
  have he := hd s
  rw [h1, map_one] at he
  exact Multiplicative.ofAdd.injective he.symm

theorem smooth_weilCharacter_eq_one_of_toMaxAb_eq_one
    (h : IsPlaceOver A v) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ)
    (s : Weil h) (hs : toMaxAb K Ω s.val = 1) : ξ s = 1 := by
  let φ := frob h
  let τ := ξ * unrChar h ((ξ φ)⁻¹)
  have hτ (x : Weil h) : τ x = ξ x * (ξ φ)⁻¹ ^ deg x := rfl
  have he (x : Ine (F := K) A) : τ (ineIncl h x) = ξ (ineIncl h x) := by
    rw [hτ, deg_ineIncl, zpow_zero, mul_one]
  have hτs : IsSmooth τ := by
    change IsOpen {x : Ine (F := K) A | τ (ineIncl h x) = 1}
    simp only [he]
    exact hξ
  have hφ : τ φ = 1 := by rw [hτ, deg_frob, zpow_one, mul_inv_cancel]
  let I := (ξ.comp (ineIncl h)).range
  letI : Finite I := hξ.finite_range.to_subtype
  let n := Nat.card I
  letI : NeZero n := ⟨Nat.card_pos.ne'⟩
  have hp (x : Weil h) : τ x ^ n = 1 := by
    obtain ⟨y, hy⟩ := exists_eq_zpow_mul (deg_frob (h := h)) x
    have hprod := congrArg τ hy
    rw [map_mul, map_zpow, hφ, one_zpow, one_mul, he] at hprod
    rw [hprod]
    let Y : I := ⟨ξ (ineIncl h y), ⟨y, rfl⟩⟩
    exact congrArg Subtype.val (pow_card_eq_one' (x := Y))
  have h1 := finite_exponent_weilCharacter_eq_one_of_toMaxAb_eq_one K Ω h τ hp hτs hs
  rw [hτ, deg_eq_zero_of_toMaxAb_eq_one K Ω h s hs, zpow_zero, mul_one] at h1
  exact h1

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.smooth_weilCharacter_eq_one_of_toMaxAb_eq_one
