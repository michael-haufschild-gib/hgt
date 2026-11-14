import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerUnramifiedResidues

/-!
# Complete splitting of nonzero soluble Kummer fibers

Reducing a nonzero radical root gives a constant unit residue. Every
decomposition automorphism therefore has trivial radical character.
Faithfulness makes the decomposition group trivial and the residue degree one.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- A nonzero constant radical root forces every decomposition character to be trivial. -/
theorem squareKummer_unramified_decomposition_character
    (a β : SquareConstantField p s) (hβ : β ≠ 0)
    (hpow : β ^ (p ^ (s + 1) + 1) = (kummerBranch c b R).eval a)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})]
    (g : (w.valuation (SquareKummerField p s c b R)).valuationSubring.decompositionSubgroup
      (FractionRing (SquareConstantField p s)[X])) :
    ((((squareKummerAutEquiv p s c b R).symm g : rootsOfUnity (p ^ (s + 1) + 1)
      (SquareConstantField p s)) : (SquareConstantField p s)ˣ) : SquareConstantField p s) = 1 := by
  let L := SquareKummerField p s c b R
  let σ : L ≃ₐ[FractionRing (SquareConstantField p s)[X]] L := g
  let ζ := (squareKummerAutEquiv p s c b R).symm σ
  let u := kummerPlaceRadical p s c b R w
  let f := kummerPlaceConstantHom p s c b R w
  obtain ⟨t, ht⟩ := kummerPlaceRadical_residue_constant p s c b R a β hβ hpow w
  have hfix : g • f t = f t := by
    apply Subtype.ext
    change σ (f t : L) = (f t : L)
    rw [kummerPlaceConstantHom_coe, IsScalarTower.algebraMap_apply (SquareConstantField p s)
      (FractionRing (SquareConstantField p s)[X]) L, σ.commutes]
  have ha : (kummerBranch c b R).eval a ≠ 0 := by
    rw [← hpow]
    exact pow_ne_zero _ hβ
  have hunit : w.valuation L (u : L) = 1 :=
    squareKummer_root_valuation_one p s c b R a ha w
  apply decomposition_unit_character_eq_one (w.valuation L) f
    (fun x hx => by rw [kummerPlaceConstantHom_coe]; exact heightOne_valuation_constant w x hx)
    g hunit ht.symm hfix
  apply Subtype.ext
  have hz := squareKummerAutEquiv_root p s c b R ζ
  rw [MulEquiv.apply_symm_apply, ← IsScalarTower.algebraMap_apply] at hz
  change σ (AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1)))) =
    (f (((ζ : (SquareConstantField p s)ˣ) : SquareConstantField p s)) : L) *
      AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1)))
  rw [kummerPlaceConstantHom_coe]
  exact hz

/-- A nonzero constant root splits the decomposition group completely. -/
theorem squareKummer_unramified_decomposition_card
    (a β : SquareConstantField p s) (hβ : β ≠ 0)
    (hpow : β ^ (p ^ (s + 1) + 1) = (kummerBranch c b R).eval a)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    Nat.card ((w.valuation (SquareKummerField p s c b R)).valuationSubring.decompositionSubgroup
      (FractionRing (SquareConstantField p s)[X])) = 1 := by
  let G := (w.valuation (SquareKummerField p s c b R)).valuationSubring.decompositionSubgroup
    (FractionRing (SquareConstantField p s)[X])
  have hg : ∀ g : G, g = 1 := by
    intro g
    apply Subtype.ext
    apply (squareKummerAutEquiv p s c b R).symm.injective
    change (squareKummerAutEquiv p s c b R).symm (g : _ ≃ₐ[_] _) =
      (squareKummerAutEquiv p s c b R).symm 1
    rw [map_one]
    apply Subtype.ext
    apply Units.ext
    exact squareKummer_unramified_decomposition_character p s c b R a β hβ hpow w g
  letI : Unique G := { default := 1, uniq := hg }
  exact Nat.card_unique

/-- Every prime in a nonzero soluble fiber has residue degree one. -/
theorem squareKummer_unramified_split_inertia
    (a β : SquareConstantField p s) (hβ : β ≠ 0)
    (hpow : β ^ (p ^ (s + 1) + 1) = (kummerBranch c b R).eval a)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    (Ideal.span {X - C a}).inertiaDeg' w.asIdeal = 1 := by
  have h := squareKummer_unramified_decomposition_card p s c b R a β hβ hpow w
  rw [squareKummer_decomposition_card p s c b R a w,
    squareKummer_nonbranch_ramification p s c b R a (by rw [← hpow]; exact pow_ne_zero _ hβ) w,
    one_mul] at h
  exact h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
