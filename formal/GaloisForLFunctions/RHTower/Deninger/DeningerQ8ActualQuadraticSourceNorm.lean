import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualTwoAdicTotalNorm
import Mathlib.RingTheory.Norm.Basic

/-!
# Actual quadratic-source norm in the SST quaternion field

Inside `K2 = ℚ(√5, √41)`, let `S = ℚ(√41)` and
`u = (1 + √5) / 2`.  The first conjugation fixes `S`, sends `u` to `1-u`,
and therefore gives the literal source norm `N_{K2/S}(u) = -1`.

The proof below identifies the relative minimal polynomial as `X²-X-1`; it does
not infer the field norm from a proxy involution product.
-/

namespace RHTower

noncomputable section

open Polynomial
open scoped NumberField

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField

local instance deningerQ8ActualQuadraticSourceNormLocalInst1 : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective
noncomputable local instance deningerQ8ActualQuadraticSourceNormLocalInst2 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance deningerQ8ActualQuadraticSourceNormLocalInst3 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance deningerQ8ActualQuadraticSourceNormLocalInst4 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis

/-- Literal copy of `ℚ(√41)` inside the actual biquadratic field. -/
abbrev q8BiquadQuadraticSourceField : IntermediateField ℚ K2 :=
  IntermediateField.adjoin ℚ
    {deningerQ8RootNumberNegOneSecondQuadraticRoot}

theorem q8SecondQuadraticRoot_not_mem_rat :
    deningerQ8RootNumberNegOneSecondQuadraticRoot ∉
      (⊥ : IntermediateField ℚ K2) := by
  intro h
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp h
  apply deningerQ8RootNumberNegOne_fortyOne_not_square q
  have hs := congrArg (fun x : K2 => x ^ (2 : ℕ)) hq
  rw [deningerQ8RootNumberNegOneSecondQuadraticRoot_sq] at hs
  exact (algebraMap ℚ K2).injective (by simpa using hs)

theorem q8BiquadQuadraticSourceField_finrank :
    Module.finrank ℚ q8BiquadQuadraticSourceField = 2 := by
  apply GaloisForLFunctions.HTGeometry.finrank_adjoin_eq_two
  · rw [← pow_two, deningerQ8RootNumberNegOneSecondQuadraticRoot_sq]
    exact (map_natCast (algebraMap ℚ K2) 41).symm
  · exact q8SecondQuadraticRoot_not_mem_rat

theorem q8FirstConjugationSecond_fixed_quadraticSource
    (x : q8BiquadQuadraticSourceField) :
    q8FirstConjugationSecond x = x := by
  refine IntermediateField.adjoin_induction ℚ
    (p := fun y _ => q8FirstConjugationSecond y = y) ?_ ?_ ?_ ?_ ?_ x.2
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy, q8FirstConjugationSecond_root]
  · intro q
    change q8FirstConjugationSecond (algebraMap ℚ K2 q) = algebraMap ℚ K2 q
    change q8FirstConjugationSecond
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
        (algebraMap ℚ K1 q)) = _
    rw [q8FirstConjugationSecond_of]
    change AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
      (q8FirstConjugation (algebraMap ℚ K1 q)) = _
    rw [show algebraMap ℚ K1 q = (q : K1) by rfl,
      q8FirstConjugation_rat]
    exact (IsScalarTower.algebraMap_apply ℚ K1 K2 q).symm
  · intro a b _ _ ha hb
    rw [map_add, ha, hb]
  · intro a _ ha
    rw [map_inv₀, ha]
  · intro a b _ _ ha hb
    rw [map_mul, ha, hb]

theorem q8BiquadTwoAdicU_ne_one_sub :
    (q8BiquadTwoAdicU : K2) ≠ 1 - (q8BiquadTwoAdicU : K2) := by
  intro h
  have hu := congrArg (fun x : 𝓞 K2 => (x : K2)) q8BiquadTwoAdicU_sq
  change (q8BiquadTwoAdicU : K2) ^ (2 : ℕ) = (q8BiquadTwoAdicU : K2) + 1 at hu
  have hv : (q8BiquadTwoAdicU : K2) = 1 / 2 := by
    apply (eq_div_iff (by norm_num : (2 : K2) ≠ 0)).2
    linear_combination h
  rw [hv] at hu
  norm_num at hu

theorem q8BiquadTwoAdicU_not_mem_quadraticSource :
    (q8BiquadTwoAdicU : K2) ∉ q8BiquadQuadraticSourceField := by
  intro h
  have hfix := q8FirstConjugationSecond_fixed_quadraticSource
    ⟨(q8BiquadTwoAdicU : K2), h⟩
  rw [q8FirstConjugationSecond_q8BiquadTwoAdicU] at hfix
  exact q8BiquadTwoAdicU_ne_one_sub hfix.symm

theorem q8BiquadQuadraticSourceField_top_finrank :
    Module.finrank q8BiquadQuadraticSourceField K2 = 2 := by
  have htower := Module.finrank_mul_finrank ℚ
    q8BiquadQuadraticSourceField K2
  rw [q8BiquadQuadraticSourceField_finrank,
    deningerQ8RootNumberNegOneSecondQuadraticField_finrank_over_rat] at htower
  omega

local notation "S" => q8BiquadQuadraticSourceField

/-- Relative polynomial of the dyadic source unit over the literal quadratic source. -/
def q8BiquadTwoAdicUMinpolyCandidate : S[X] :=
  X ^ (2 : ℕ) - C 1 * X + C (-1)

theorem q8BiquadTwoAdicUMinpolyCandidate_isMonicOfDegree :
    q8BiquadTwoAdicUMinpolyCandidate.IsMonicOfDegree 2 := by
  exact Polynomial.isMonicOfDegree_sub_add_two 1 (-1)

theorem q8BiquadTwoAdicUMinpolyCandidate_monic :
    q8BiquadTwoAdicUMinpolyCandidate.Monic :=
  q8BiquadTwoAdicUMinpolyCandidate_isMonicOfDegree.monic

theorem q8BiquadTwoAdicUMinpolyCandidate_natDegree :
    q8BiquadTwoAdicUMinpolyCandidate.natDegree = 2 :=
  q8BiquadTwoAdicUMinpolyCandidate_isMonicOfDegree.natDegree_eq

theorem q8BiquadTwoAdicUMinpolyCandidate_aeval :
    Polynomial.aeval (q8BiquadTwoAdicU : K2)
      q8BiquadTwoAdicUMinpolyCandidate = 0 := by
  have hu := congrArg (fun x : 𝓞 K2 => (x : K2)) q8BiquadTwoAdicU_sq
  change (q8BiquadTwoAdicU : K2) ^ (2 : ℕ) = (q8BiquadTwoAdicU : K2) + 1 at hu
  simp only [q8BiquadTwoAdicUMinpolyCandidate, map_add, map_sub, map_mul,
    map_neg, map_pow, aeval_X, map_one]
  rw [hu]
  ring

theorem q8BiquadTwoAdicU_isIntegral_quadraticSource :
    IsIntegral S (q8BiquadTwoAdicU : K2) :=
  ⟨q8BiquadTwoAdicUMinpolyCandidate,
    q8BiquadTwoAdicUMinpolyCandidate_monic,
    q8BiquadTwoAdicUMinpolyCandidate_aeval⟩

theorem q8BiquadTwoAdicU_minpoly_natDegree_quadraticSource :
    (minpoly S (q8BiquadTwoAdicU : K2)).natDegree = 2 := by
  let p := q8BiquadTwoAdicUMinpolyCandidate
  have hp0 : p ≠ 0 := q8BiquadTwoAdicUMinpolyCandidate_monic.ne_zero
  have hroot : Polynomial.aeval (q8BiquadTwoAdicU : K2) p = 0 :=
    q8BiquadTwoAdicUMinpolyCandidate_aeval
  have hdiv : minpoly S (q8BiquadTwoAdicU : K2) ∣ p := minpoly.dvd S _ hroot
  have hle : (minpoly S (q8BiquadTwoAdicU : K2)).natDegree ≤ 2 := by
    calc
      (minpoly S (q8BiquadTwoAdicU : K2)).natDegree ≤ p.natDegree :=
        Polynomial.natDegree_le_of_dvd hdiv hp0
      _ = 2 := q8BiquadTwoAdicUMinpolyCandidate_natDegree
  have hpos : 0 < (minpoly S (q8BiquadTwoAdicU : K2)).natDegree :=
    minpoly.natDegree_pos q8BiquadTwoAdicU_isIntegral_quadraticSource
  have hneone : (minpoly S (q8BiquadTwoAdicU : K2)).natDegree ≠ 1 := by
    intro hdeg
    have hrange := minpoly.natDegree_eq_one_iff.mp hdeg
    rcases hrange with ⟨s, hs⟩
    exact q8BiquadTwoAdicU_not_mem_quadraticSource (hs ▸ s.2)
  omega

theorem q8BiquadTwoAdicU_minpoly_quadraticSource :
    minpoly S (q8BiquadTwoAdicU : K2) =
      q8BiquadTwoAdicUMinpolyCandidate := by
  have hdiv : minpoly S (q8BiquadTwoAdicU : K2) ∣
      q8BiquadTwoAdicUMinpolyCandidate :=
    minpoly.dvd S _ q8BiquadTwoAdicUMinpolyCandidate_aeval
  have hdeg : q8BiquadTwoAdicUMinpolyCandidate.natDegree ≤
      (minpoly S (q8BiquadTwoAdicU : K2)).natDegree := by
    rw [q8BiquadTwoAdicUMinpolyCandidate_natDegree,
      q8BiquadTwoAdicU_minpoly_natDegree_quadraticSource]
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic q8BiquadTwoAdicU_isIntegral_quadraticSource)
    q8BiquadTwoAdicUMinpolyCandidate_monic hdiv hdeg).symm

theorem q8BiquadTwoAdicU_adjoin_top_finrank_quadraticSource :
    Module.finrank
      (IntermediateField.adjoin S {(q8BiquadTwoAdicU : K2)}) K2 = 1 := by
  have htower := Module.finrank_mul_finrank S
    (IntermediateField.adjoin S {(q8BiquadTwoAdicU : K2)}) K2
  rw [IntermediateField.adjoin.finrank q8BiquadTwoAdicU_isIntegral_quadraticSource,
    q8BiquadTwoAdicU_minpoly_natDegree_quadraticSource,
    q8BiquadQuadraticSourceField_top_finrank] at htower
  omega

theorem q8BiquadTwoAdicU_adjoin_norm_quadraticSource :
    Algebra.norm S
      (IntermediateField.AdjoinSimple.gen S (q8BiquadTwoAdicU : K2)) = -1 := by
  rw [← IntermediateField.adjoin.powerBasis_gen
    q8BiquadTwoAdicU_isIntegral_quadraticSource]
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
  rw [IntermediateField.adjoin.powerBasis_dim,
    IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen,
    q8BiquadTwoAdicU_minpoly_quadraticSource,
    q8BiquadTwoAdicUMinpolyCandidate_natDegree]
  simp [q8BiquadTwoAdicUMinpolyCandidate]

/-- Exact relative norm from `ℚ(√5,√41)` to the inducing quadratic source
`S = ℚ(√41)`.  This is the global input for finite-place Artin norm--restriction. -/
theorem q8BiquadTwoAdicU_quadraticSource_norm :
    Algebra.norm S (q8BiquadTwoAdicU : K2) = -1 := by
  rw [Algebra.norm_eq_norm_adjoin]
  rw [q8BiquadTwoAdicU_adjoin_norm_quadraticSource,
    q8BiquadTwoAdicU_adjoin_top_finrank_quadraticSource, pow_one]

end

end RHTower
