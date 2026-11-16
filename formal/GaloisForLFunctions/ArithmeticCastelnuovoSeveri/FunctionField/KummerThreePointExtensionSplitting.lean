import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionResidues
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.AdicDecompositionCardinality
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalPlaceValuations

/-!
# Complete splitting over extended constants

A constant nonzero radical root makes the radical residue constant.
Every decomposition automorphism then has trivial radical character,
so the decomposition group is trivial. Its order is the product of
ramification and residue degrees; both degrees are therefore one.
The degree identity counts every prime in the fiber. Conversely a
rational residue field provides a constant radical root.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (d n : ℕ)
    (E : Type*) [Field E] [Finite E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E]
    (c : Eˣ) (a : ℕ)
local notation "M" => primePowerKummerCyclicDegree p d n
local notation "N" => M - 1 + 1
local notation "L" => PrimePowerThreePointExtensionField p d n E c a
local notation "B" => PrimePowerThreePointExtensionNormalization p d n E c a
local notation "F" => FractionRing E[X]

private theorem factors_of_product_one (u v : ℕ) (h : u * v = 1) : u = 1 ∧ v = 1 := by
  have hu : 0 < u := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0, zero_mul] at h
    exact Nat.zero_ne_one h)
  have hv : 0 < v := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0, mul_zero] at h
    exact Nat.zero_ne_one h)
  constructor
  · have hle := Nat.le_mul_of_pos_right u hv
    rw [h] at hle
    exact Nat.le_antisymm hle hu
  · have hle := Nat.le_mul_of_pos_right v hu
    rw [Nat.mul_comm v u, h] at hle
    exact Nat.le_antisymm hle hv

/-- At a rational base point, decomposition order equals ramification times residue degree. -/
theorem primePowerThreePointExtension_decomposition_card (x : E) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver (Ideal.span {X - C x})] :
    Nat.card ((w.valuation L).valuationSubring.decompositionSubgroup F) =
      (Ideal.span {X - C x}).ramificationIdx' w.asIdeal *
        (Ideal.span {X - C x}).inertiaDeg' w.asIdeal := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C x)
  letI := primePowerThreePointExtension_isGalois p d n E c a
  letI : (Ideal.span {X - C x}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {X - C x})
    infer_instance
  letI : Finite (Ideal.ResidueField (Ideal.span {X - C x})) :=
    polynomial_irreduciblePlace_finite_residue (irreducible_X_sub_C x)
  letI : PerfectField v.asIdeal.ResidueField := by
    change PerfectField (Ideal.ResidueField (Ideal.span {X - C x}))
    infer_instance
  exact heightOne_decomposition_card (K := F) («L» := L) v w

/-- A nonzero constant radical root forces the decomposition character to be trivial. -/
theorem primePowerThreePointExtension_split_character
    (x β : E) (hβ : β ≠ 0) (hpow : β ^ N = (kummerBranch c 0 a).eval x)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C x})]
    (g : (w.valuation L).valuationSubring.decompositionSubgroup F) :
    (((primePowerThreePointExtensionAutEquiv p d n E c a).symm g : Eˣ) : E) = 1 := by
  let σ : L ≃ₐ[F] L := g
  let ζ := (primePowerThreePointExtensionAutEquiv p d n E c a).symm σ
  let u := primePowerThreePointExtensionPlaceRadical p d n E c a w
  let f := heightOnePolynomialConstantHom (K := E) («L» := L) w
  obtain ⟨t, ht⟩ := primePowerThreePointExtension_radical_residue_constant
    p d n E c a x β hβ hpow w
  have hfix : g • f t = f t := by
    apply Subtype.ext
    change σ (f t : L) = (f t : L)
    rw [heightOnePolynomialConstantHom_coe, IsScalarTower.algebraMap_apply E F L, σ.commutes]
  have hx : (kummerBranch c 0 a).eval x ≠ 0 := by
    rw [← hpow]
    exact pow_ne_zero _ hβ
  have hunit : w.valuation L (u : L) = 1 :=
    primePowerThreePointExtension_root_valuation_one p d n E c a x hx w
  apply decomposition_unit_character_eq_one (w.valuation L) f
    (fun t ht => by rw [heightOnePolynomialConstantHom_coe]; exact heightOne_valuation_constant w t ht)
    g hunit ht.symm hfix
  apply Subtype.ext
  have hz := primePowerThreePointExtensionAutEquiv_root p d n E c a ζ
  rw [MulEquiv.apply_symm_apply] at hz
  change σ (AdjoinRoot.root (kummerBranchFieldPolynomial c 0 a (M - 1))) =
    (f ((ζ : Eˣ) : E) : L) * AdjoinRoot.root (kummerBranchFieldPolynomial c 0 a (M - 1))
  rw [heightOnePolynomialConstantHom_coe]
  exact hz

/-- Every nonzero soluble fiber has trivial decomposition group at each of its primes. -/
theorem primePowerThreePointExtension_split_decomposition_card
    (x β : E) (hβ : β ≠ 0) (hpow : β ^ N = (kummerBranch c 0 a).eval x)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C x})] :
    Nat.card ((w.valuation L).valuationSubring.decompositionSubgroup F) = 1 := by
  let G := (w.valuation L).valuationSubring.decompositionSubgroup F
  have hg : ∀ g : G, g = 1 := by
    intro g
    apply Subtype.ext
    apply (primePowerThreePointExtensionAutEquiv p d n E c a).symm.injective
    change (primePowerThreePointExtensionAutEquiv p d n E c a).symm (g : L ≃ₐ[F] L) =
      (primePowerThreePointExtensionAutEquiv p d n E c a).symm 1
    rw [map_one]
    apply Subtype.ext
    apply Units.ext
    exact primePowerThreePointExtension_split_character p d n E c a x β hβ hpow w g
  letI : Unique G := { default := 1, uniq := hg }
  exact Nat.card_unique

/-- Complete splitting forces both ramification and residue degrees to equal one. -/
theorem primePowerThreePointExtension_split_indices
    (x β : E) (hβ : β ≠ 0) (hpow : β ^ N = (kummerBranch c 0 a).eval x)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C x})] :
    (Ideal.span {X - C x}).ramificationIdx' w.asIdeal = 1 ∧
      (Ideal.span {X - C x}).inertiaDeg' w.asIdeal = 1 := by
  have h := primePowerThreePointExtension_split_decomposition_card p d n E c a x β hβ hpow w
  rw [primePowerThreePointExtension_decomposition_card p d n E c a x w] at h
  exact factors_of_product_one _ _ h

/-- A soluble nonzero fiber contains exactly the unchanged covering degree many normalization primes. -/
theorem primePowerThreePointExtension_split_primes_card
    (x β : E) (hβ : β ≠ 0) (hpow : β ^ N = (kummerBranch c 0 a).eval x) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {X - C x}) B).card = M := by
  classical
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C x)
  letI : (Ideal.span {X - C x}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hv0 : (Ideal.span {X - C x}) ≠ ⊥ := v.ne_bot
  have hsum := Ideal.sum_ramification_inertia B F L hv0
  rw [primePowerThreePointExtension_finrank] at hsum
  rw [Finset.card_eq_sum_ones]
  refine (Finset.sum_congr rfl fun P hP => ?_).trans hsum
  obtain ⟨hprime, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hv0 B).mp hP
  letI := hprime
  letI := hover
  let w : HeightOneSpectrum B := ⟨P, hprime, Ideal.ne_bot_of_liesOver_of_ne_bot hv0 P⟩
  obtain ⟨he, hf⟩ := primePowerThreePointExtension_split_indices p d n E c a x β hβ hpow w
  change (Ideal.span {X - C x}).ramificationIdx' P = 1 at he
  change (Ideal.span {X - C x}).inertiaDeg' P = 1 at hf
  rw [he, hf, one_mul]

omit [Finite E] in
/-- A residue-degree-one prime has only residues in the extended constant field. -/
theorem primePowerThreePointExtension_rational_residue_surjective
    (x : E) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C x})]
    (hf : (Ideal.span {X - C x}).inertiaDeg' w.asIdeal = 1) :
    Function.Surjective (algebraMap E (B ⧸ w.asIdeal)) := by
  exact heightOne_linearPrime_constant_residue_surjective w x hf

omit [Finite E] in
/-- Every rational normalization prime gives a radical root in the extended constant field. -/
theorem primePowerThreePointExtension_rationalPlace_has_root
    (x : E) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C x})]
    (hf : (Ideal.span {X - C x}).inertiaDeg' w.asIdeal = 1) :
    ∃ β : E, β ^ N = (kummerBranch c 0 a).eval x := by
  letI : w.asIdeal.IsPrime := w.isPrime
  exact primePowerThreePointExtension_rationalPrime_root p d n E c a x w.asIdeal
    (primePowerThreePointExtension_rational_residue_surjective p d n E c a x w hf)

/-- Rationality above a nonzero defining value is equivalent to a radical root in the extended constants. -/
theorem primePowerThreePointExtension_nonzero_fiber_rational_iff
    (x : E) (hx : (kummerBranch c 0 a).eval x ≠ 0) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver (Ideal.span {X - C x})] :
    (Ideal.span {X - C x}).inertiaDeg' w.asIdeal = 1 ↔
      ∃ β : E, β ^ N = (kummerBranch c 0 a).eval x := by
  constructor
  · exact primePowerThreePointExtension_rationalPlace_has_root p d n E c a x w
  · rintro ⟨β, hβ⟩
    have hβ0 : β ≠ 0 := by
      intro h
      rw [h, zero_pow (Nat.succ_ne_zero _)] at hβ
      exact hx hβ.symm
    exact (primePowerThreePointExtension_split_indices p d n E c a x β hβ0 hβ w).2

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
