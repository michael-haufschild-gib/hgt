/-
Natural row sources adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.LogDyadicAnnuliAndZeroEnergy
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.DetectorProfilesAndCutoffs

/-!
# Natural row sources

Natural rows and their fixed conductor factors, excluded primes and natural slots; fixed row
masks; uniform reflection profiles, scales and independent choices of the detector source.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFixedRowMask
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CanonicalRowCompletion
open CanonicalQuadraticSieve 
local notation "O" => Eisenstein.O

theorem row_mask_mul (η : Character) (m r A z n : O)
    (hmLam : lambda ∣ m) (hm2 : (2:O) ∣ m) :
    rowTwist (elementHom η) (m*r) 1 (A*z) n =
      if IsCoprime n r then rowTwist (elementHom η) m 1 (A*z) n else 0 := by
  by_cases hs : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ _ _ _ _ ((supported_iff_native _).mp hs),
      rowTwist_extract_sixth_mask _ _ _ _ _ ((supported_iff_native _).mp hs)]
    change elementHom η n * (if IsCoprime (m*r) n then (1:ℂ) else 0) * _ = _
    rw [IsCoprime.mul_left_iff]
    by_cases hm : IsCoprime m n <;> by_cases hr : IsCoprime n r <;>
      simp [coprimalityMask,hm,hr,show IsCoprime r n ↔ IsCoprime n r from isCoprime_comm]
  · rw [rowTwist_zero_of_not_supported _ _ _ _ _
        (hmLam.trans (dvd_mul_right _ _)) (hm2.trans (dvd_mul_right _ _)) ((supported_iff_native _).not.mp hs),
      rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 ((supported_iff_native _).not.mp hs)]
    split_ifs <;> rfl

theorem fixedInducingRow_mul_mask_iff (η : Character) (Q : Ideal O)
    (m r A z : O) (hm : m ≠ 0) (hr : r ≠ 0) (hA : A ≠ 0) (hz : z ≠ 0)
    (hmLam : lambda ∣ m) (hm2 : (2:O) ∣ m) :
    FixedInducingRow η Q (m*r) A z ↔ FixedInducingRow η Q m A z := by
  obtain ⟨χ,hχ⟩ := exists_row_character η m 1 (A*z) hm one_ne_zero
    (mul_ne_zero hA hz) hmLam hm2
  obtain ⟨χ',hχ'⟩ := exists_row_character η (m*r) 1 (A*z) (mul_ne_zero hm hr)
    one_ne_zero (mul_ne_zero hA hz) (hmLam.trans (dvd_mul_right _ _))
      (hm2.trans (dvd_mul_right _ _))
  have hmask (n : O) : elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0 := by
    rw [hχ' n,hχ n,row_mask_mul η m r A z n hmLam hm2]
  have transport (ρ : Character) (mask : O)
      (hρ : ∀ n,elementCoeff ρ n=rowTwist (elementHom η) mask 1 (A*z) n) :
      FixedInducingRow η Q mask A z ↔
        ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
          Q ≤ ψ.modulus ∧ InducedBy ρ ψ := by
    constructor
    · rintro ⟨ρ₀,ψ,hprim,hind,hQ,hρ₀⟩
      exact ⟨ψ,hprim,hQ,CenteredMomentHeckeVolume.inducedBy_of_elementCoeff_eq
        ρ₀ ρ ψ (fun n => (hρ n).trans (hρ₀ n).symm) hind⟩
    · rintro ⟨ψ,hprim,hQ,hind⟩
      exact ⟨ρ,ψ,hprim,hind,hQ,hρ⟩
  rw [transport χ' (m*r) hχ',transport χ m hχ]
  exact HeckeMaskDescent.fixed_inducing_mask_iff χ χ' r hr hmask Q
end CenteredMomentFixedRowMask

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondSixthReduction
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondMovingSupport CenteredMomentFixedRowMask
open CenteredExceptionalProfile CenteredMomentSupportedCorrelation
local notation "O" => Eisenstein.O

def reducedNumerator (C D : Ideal O) (U : Finset (CommonIndex C D)) : O :=
  ∏ P : CommonIndex C D,commonPrime C D P^(fixedExponent C D U P%6)

def sixthFactor (C D : Ideal O) (U : Finset (CommonIndex C D)) : O :=
  ∏ P : CommonIndex C D,commonPrime C D P^(fixedExponent C D U P/6)

theorem fixed_numerator_product (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U=
      ∏ P : CommonIndex C D,commonPrime C D P^fixedExponent C D U P := by
  have hv : nonunitFrequencyGenerator C D U=
      ∏ P : CommonIndex C D,if P∈nonunitPartitionSet C D U then commonPrime C D P else 1 := by
    simp only [nonunitFrequencyGenerator,Finset.prod_ite_mem,Finset.univ_inter]
  rw [commonFrequencyGenerator,hv,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [fixedExponent,pow_add]
  split_ifs <;> simp

theorem fixed_sixth_factorization (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U=
      reducedNumerator C D U*(sixthFactor C D U)^6 := by
  rw [fixed_numerator_product,reducedNumerator,sixthFactor,←Finset.prod_pow,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  rw [←pow_mul,←pow_add]
  congr 1
  omega

theorem reducedNumerator_ne_zero (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    reducedNumerator C D U≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=> pow_ne_zero _
    (supported_element_ne_zero _ (commonPrime_supported C D hC P)))

theorem sixthFactor_ne_zero (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    sixthFactor C D U≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=> pow_ne_zero _
    (supported_element_ne_zero _ (commonPrime_supported C D hC P)))

theorem fixed_sixth_row (η : Character) (m h n : O) (C D : Ideal O)
    (U : Finset (CommonIndex C D)) :
    rowTwist (elementHom η) m 1
      ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h) n=
    rowTwist (elementHom η) (m*sixthFactor C D U) 1 (reducedNumerator C D U*h) n := by
  rw [fixed_sixth_factorization]
  have he : m ^ 6 * 1 ^ 4 * ((reducedNumerator C D U * sixthFactor C D U ^ 6) * h) =
      (m * sixthFactor C D U) ^ 6 * 1 ^ 4 * (reducedNumerator C D U * h) := by ring
  exact congrArg
    (fun x => elementHom η n * idealRowHom x (Ideal.span {n})) he

theorem fixed_sixth_inducing_iff (η : Character) (Q : Ideal O) (m h : O)
    (hm : m≠0) (hh : h≠0) (hmLam : lambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    FixedInducingRow η Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) h ↔
      FixedInducingRow η Q m (reducedNumerator C D U) h := by
  have he : FixedInducingRow η Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) h ↔
      FixedInducingRow η Q (m*sixthFactor C D U) (reducedNumerator C D U) h := by
    unfold FixedInducingRow
    simp only [fixed_sixth_row]
  exact he.trans (fixedInducingRow_mul_mask_iff η Q m (sixthFactor C D U)
    (reducedNumerator C D U) h hm (sixthFactor_ne_zero C D hC U)
    (reducedNumerator_ne_zero C D hC U) hh hmLam hm2)

end CenteredMomentSecondSixthReduction

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondSixthSource
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction
open CenteredMomentCanonicalFirst
local notation "O" => Eisenstein.O

theorem sixthFactor_span_dvd (C D : Ideal O) (hC : Supported C)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    Ideal.span {sixthFactor C D U}∣C := by
  conv_rhs => rw [←left_ideal_product C D hC hCD]
  simp only [sixthFactor,span_finset_product,←Ideal.span_singleton_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  apply pow_dvd_pow
  have hc := leftExponent_pos C D P
  have hm : min (leftExponent C D P) (rightExponent C D P)≤ leftExponent C D P := min_le_left _ _
  unfold fixedExponent
  split_ifs <;> omega

theorem fixed_sixth_coefficient (C D : Ideal O) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I*
        (if IsCoprime I (Ideal.span {sixthFactor C D U}) then 1 else 0) := by
  rw [fixed_sixth_factorization,idealRowHom_argument_mul,idealRowHom_sixth_mask _ I ((supported_iff_native _).mp hI)]

theorem residual_sixth_coefficient (C D : Ideal O) (hC : Supported C)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) (hcop : IsCoprime C I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I := by
  rw [fixed_sixth_coefficient C D U I hI,if_pos
    (hcop.symm.of_isCoprime_of_dvd_right (sixthFactor_span_dvd C D hC hCD U)),mul_one]

abbrev ActiveIndex (C D : Ideal O) (U : Finset (CommonIndex C D)) := ↥(fixedActiveSet C D U)

def activePrime (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : O := commonPrime C D P.val

def activeExponent (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : ℕ := fixedExponent C D U P.val%6

theorem activeExponent_pos (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : 0< activeExponent C D U P := by
  have hp : ¬6∣fixedExponent C D U P.val := (Finset.mem_filter.mp P.property).2
  exact Nat.pos_of_ne_zero (fun h=> hp (Nat.dvd_of_mod_eq_zero h))

theorem activeExponent_lt (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : activeExponent C D U P<6 := Nat.mod_lt _ (by norm_num)

theorem reducedNumerator_active_product (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    reducedNumerator C D U=∏ P : ActiveIndex C D U,activePrime C D U P^activeExponent C D U P := by
  simp only [activePrime,activeExponent]
  rw [Finset.prod_coe_sort (fixedActiveSet C D U)
    (fun P : CommonIndex C D=> commonPrime C D P^(fixedExponent C D U P%6))]
  unfold reducedNumerator
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro P hP hn
  have hp : 6∣fixedExponent C D U P := by
    simpa only [fixedActiveSet,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hn
  simp only [Nat.mod_eq_zero_of_dvd hp,pow_zero]

end CenteredMomentSecondSixthSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondRadicalFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst (CommonIndex)
open CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource
open CenteredMomentRadicalFamily CenteredMomentSecondHeightFamily CenteredMomentSecondChildProfile
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentCommonSupport RayFourExpansion
local notation "O" => Eisenstein.O

theorem active_radical_product (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) :
    (∏ P : ActiveIndex C D U,Ideal.span {activePrime C D U P})=
      ∏ P∈fixedActiveSet C D U,P.val := by
  simp only [activePrime,commonPrime_span C D hC]
  exact Finset.prod_coe_sort _ (fun P : CommonIndex C D=> P.val)

theorem exists_second_radical_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      τ.modulus.absNorm≤(childCharacter η χ).modulus.absNorm*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (∏P∈fixedActiveSet C D U,P.val).absNorm ∧
      (∀n:O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
        fixedBadMask 1 (reducedNumerator C D U) n) ∧
      ∀I:Ideal O,Supported I → ∀t:ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom (reducedNumerator C D U) I*
          rayMonoid χ (primaryIdealGenerator I) := by
  obtain ⟨τ,hM,hN,hτ⟩ := exists_radical_row_presentation (childCharacter η χ) fixedBadMask
    fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
    (activePrime C D U) (fun P=> commonPrime_supported C D hC P.val)
    (activeExponent C D U) (activeExponent_pos C D U)
  have he (n:O) : elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n := by
    rw [reducedNumerator_active_product]
    exact hτ n
  refine ⟨τ,?_,he,?_⟩
  · rw [←map_prod,active_radical_product C D hC U] at hN
    exact hN
  · intro I hI t
    have ht := idealCoeff_eq_row (childCharacter η χ) τ fixedBadMask 1
      (reducedNumerator C D U) he I
    change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=_
    rw [ht,child_ideal_primary η χ I hI,idealRowHom_argument_mul]
    simp only [one_pow,mul_one]
    rw [heightCoeff_eq_fixed_rowWeight η t I hI]
    simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk]
    ring_nf

end CenteredMomentSecondRadicalFamily

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondRadicalColumns
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction
open CenteredMomentSecondSixthSource CenteredMomentSecondRadicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
open CenteredMomentCanonicalFirst
local notation "O" => Eisenstein.O

theorem sixthFactor_span_dvd_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    Ideal.span {sixthFactor C D U}∣D := by
  conv_rhs => rw [←right_ideal_product C D hC hD hCD]
  simp only [sixthFactor,span_finset_product,←Ideal.span_singleton_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  apply pow_dvd_pow
  have hd := rightExponent_pos C D P
  have hm : min (leftExponent C D P) (rightExponent C D P)≤ rightExponent C D P := min_le_right _ _
  unfold fixedExponent
  split_ifs <;> omega

theorem residual_sixth_coefficient_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) (hcop : IsCoprime D I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I := by
  rw [fixed_sixth_coefficient C D U I hI,if_pos
    (hcop.symm.of_isCoprime_of_dvd_right (sixthFactor_span_dvd_right C D hC hD hCD U)),mul_one]

theorem exists_actual_masked_radical_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      τ.modulus.absNorm≤(childCharacter η χ).modulus.absNorm*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (∏P∈fixedActiveSet C D U,P.val).absNorm ∧
      ∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀t:ℝ,
        heightCoeff τ t I=heightCoeff η t I*
          idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
          rayMonoid χ (primaryIdealGenerator I) := by
  obtain ⟨τ,hN,he,hτ⟩ := exists_second_radical_family η χ C D hC U
  refine ⟨τ,hN,?_⟩
  intro I hI hi t
  rw [hτ I hI t]
  rcases hi with hi|hi
  · rw [residual_sixth_coefficient C D hC hCD U I hI hi]
  · rw [residual_sixth_coefficient_right C D hC hD hCD U I hI hi]

end CenteredMomentSecondRadicalColumns

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open TruncatedPrincipalPoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondReducedPredicate
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredExceptionalProfile CenteredMomentFixedRowMask CenteredMomentRestrictedEnergy
open CenteredMomentSecondFamilyTransport CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSixthReduction CenteredMomentCanonicalFirst RayFourExpansion
local notation "O" => Eisenstein.O

theorem fixed_mask_change (η : Character) (Q : Ideal O) (m n A z : O)
    (hm:m≠0) (hn:n≠0) (hA:A≠0) (hz:z≠0)
    (hmLam:lambda∣m) (hm2:(2:O)∣m)
    (hnLam:lambda∣n) (hn2:(2:O)∣n) :
    FixedInducingRow η Q m A z ↔ FixedInducingRow η Q n A z := by
  have h1:=fixedInducingRow_mul_mask_iff η Q m n A z hm hn hA hz hmLam hm2
  have h2:=fixedInducingRow_mul_mask_iff η Q n m A z hn hm hA hz hnLam hn2
  rw [mul_comm n m] at h2
  exact h1.symm.trans h2

theorem actual_reduced_inducing_iff (η τ : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D))
    (hτ:∀n:O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n)
    (Q:Ideal O) (m z:O) (hm:m≠0) (hz:z≠0)
    (hmLam:lambda∣m) (hm2:(2:O)∣m) :
    FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      FixedInducingRow τ Q fixedBadMask 1 z := by
  rw [fixed_sixth_inducing_iff _ Q m z hm hz hmLam hm2 C D hC U]
  exact (fixed_mask_change (childCharacter η χ) Q m fixedBadMask (reducedNumerator C D U) z
    hm fixedBadMask_ne_zero (reducedNumerator_ne_zero C D hC U) hz hmLam hm2
    (dvd_mul_right _ _) (dvd_mul_left _ _)).trans
      (fixedInducingRow_transport η τ χ _ hτ Q z).symm

theorem actual_nonexceptional_iff (η τ : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D))
    (hτ:∀n:O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n)
    (Q:Ideal O) (m z:O) (hm:m≠0)
    (hmLam:lambda∣m) (hm2:(2:O)∣m) :
    nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      z≠0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z := by
  unfold nonexceptional
  by_cases hz:z=0
  · simp only [hz,ne_eq,not_true_eq_false,false_and]
  · rw [actual_reduced_inducing_iff η τ χ C D hC U hτ Q m z hm hz hmLam hm2]

end CenteredMomentSecondReducedPredicate

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentRayNonprincipal
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CanonicalRowCompletion HeckePrimeRay
local notation "O" => Eisenstein.O

theorem product_principal_descent (χ θ:Character)
    (hp:(χ.product θ).residue=1) :
    FiniteConductor.FactorsThroughIdeal χ.residue
      (θ.modulus.map (Ideal.Quotient.mk χ.modulus)) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  rw [FiniteConductor.factorsThroughIdeal_iff]
  intro u hu
  obtain ⟨q,hq,hqu⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk χ.modulus) Ideal.Quotient.mk_surjective).mp hu
  let a:O := 1+q
  have ha:Ideal.Quotient.mk χ.modulus a=(u:O⧸χ.modulus) := by
    dsimp [a]; rw [map_add,map_one,hqu]; ring
  have hθa:Ideal.Quotient.mk θ.modulus a=1 := by
    simp only [a,map_add,map_one,Ideal.Quotient.eq_zero_iff_mem.mpr hq,add_zero]
  have hcχ:IsCoprime (Ideal.span {a}) χ.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (ha ▸ u.isUnit)
  have hcθ:IsCoprime (Ideal.span {a}) θ.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hθa ▸ isUnit_one)
  have hcp:IsCoprime (Ideal.span {a}) (χ.product θ).modulus :=
    (hcχ.mul_right hcθ).of_isCoprime_of_dvd_right
      (Ideal.dvd_iff_le.mpr Ideal.mul_le_inf)
  have hv:elementCoeff (χ.product θ) a=1 := by
    change (χ.product θ).residue _=1
    rw [hp]
    exact MulChar.one_apply ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hcp)
  rw [elementCoeff_product] at hv
  change χ.residue (Ideal.Quotient.mk χ.modulus a)*
    θ.residue (Ideal.Quotient.mk θ.modulus a)=1 at hv
  simpa only [ha,hθa,map_one,mul_one] using hv

theorem product_principal_inducing (χ θ:Character)
    (hp:(χ.product θ).residue=1) :
    ∃ψ:Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      θ.modulus≤ψ.modulus ∧ InducedBy χ ψ :=
  HeckeMaskDescent.exists_primitive_above χ θ.modulus
    (product_principal_descent χ θ hp)

theorem actual_row_twist_nonprincipal (η χ θ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hQ:Q≤θ.modulus) (hex:¬FixedInducingRow η Q m A z) :
    (χ.product θ).residue≠1 := by
  intro hp
  obtain ⟨ψ,hψ,hmod,hind⟩ := product_principal_inducing χ θ hp
  exact hex ⟨χ,ψ,hψ,hind,hQ.trans hmod,hrow⟩

variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤ H)

theorem all_ray_twists_nonprincipal (η χ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hQ:Q≤ M) (hex:¬FixedInducingRow η Q m A z) :
    ∀θ:RayQuotient.Characters M H, (twistedFamily M H hH χ θ).residue≠1 := by
  intro θ
  exact actual_row_twist_nonprincipal η χ (HeckeRayQuotient.character M H hH θ)
    Q m A z hrow hQ hex

end CenteredMomentRayNonprincipal

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentCommonMaskExpansion
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open UniqueFactorizationMonoid
local notation "O" => Eisenstein.O

def naturalSlot (χ : Character) (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) : ℂ :=
  (Real.sqrt P:ℂ)⁻¹ * ∑ I∈pool,idealCoeff χ I*β I

def profileSlot (χ : Character) (pool : Finset (Ideal O))
    (ν : Ideal O→ℂ) (W : ℝ→ℂ) (P : ℝ) : ℂ :=
  naturalSlot χ pool (fun I=>ν I*W ((I.absNorm:ℝ)/P)) P

lemma outside_prime (R : Finset (Ideal O)) (hR : ∀ I∈R,Prime I)
    (I : Ideal O) (hI : Prime I) : outside R I ↔ I∉R := by
  constructor
  · intro h hi
    exact h I hi dvd_rfl
  · intro h J hj hd
    have he : J=I := (prime_dvd_prime_iff_eq (hR J hj) hI).mp hd
    exact h (he ▸ hj)

lemma deleted_prime (χ : Character) (R : Finset (Ideal O)) (hR : ∀ I∈R,Prime I)
    (I : Ideal O) (hI : Prime I) :
    idealCoeff (χ.excludePrimes R hR) I = if I∈R then 0 else idealCoeff χ I := by
  have h:=deleted_coefficient χ R hR ⟨I,hI.ne_zero⟩
  simpa only [outside_prime R hR I hI,ite_not] using h

theorem naturalSlot_delete (χ : Character) (R : Finset (Ideal O)) (hR : ∀ I∈R,Prime I)
    (pool : Finset (Ideal O)) (hp : ∀ I∈pool,Prime I) (β : Ideal O→ℂ) (P : ℝ) :
    naturalSlot (χ.excludePrimes R hR) pool β P =
      naturalSlot χ pool β P - naturalSlot χ (pool∩R) β P := by
  unfold naturalSlot
  have hinter : pool∩R=pool.filter (fun I=> I∈R) := by ext I;simp
  rw [←mul_sub,hinter,Finset.sum_filter,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro I hi
  rw [deleted_prime χ R hR I (hp I hi)]
  by_cases h:I∈R <;> simp [h]

lemma prod_sub_expansion {α : Type*} [DecidableEq α] (F : Finset α) (a b : α→ℂ) :
    (∏i∈F,(a i-b i))=∑J∈F.powerset,(-1:ℂ)^J.card*(∏i∈J,b i)*(∏i∈F\J,a i) := by
  have he : (∏i∈F,(a i-b i))=∏i∈F,((-b i)+a i) := by
    apply Finset.prod_congr rfl
    intro i hi
    ring
  rw [he,Finset.prod_add]
  simp only [Finset.prod_neg]

def plainCoefficient (χ : Character) (D : Finset (Ideal O)) : ℂ :=
  (moebius (∏I∈D,I):ℂ)*(idealCoeff χ (∏I∈D,I)/(Real.sqrt (Ideal.absNorm (∏I∈D,I):ℝ):ℂ))

variable {α : Type*} [DecidableEq α]

def signedCoefficient (χ : Character) (R D₁ D₂ : Finset (Ideal O))
    (J : Finset α) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) : ℂ :=
  plainCoefficient χ D₁*plainCoefficient χ D₂*(-1:ℂ)^J.card*
    ∏i∈J,naturalSlot χ (pool i∩R) (β i) (P i)

theorem simultaneous_deletion (χ : Character) (R : Finset (Ideal O))
    (hR : ∀ I∈R,Prime I) (W₁ W₂ : 𝓢(ℝ,ℂ)) (X₁ X₂ : ℝ)
    (hX₁ : 0< X₁) (hX₂ : 0< X₂) (F : Finset α)
    (pool : α→Finset (Ideal O)) (hp : ∀i∈F,∀I∈pool i,Prime I)
    (β : α→Ideal O→ℂ) (P : α→ℝ) :
    HeckeDyadic.polynomial (χ.excludePrimes R hR) false W₁ X₁ 0 0 *
      HeckeDyadic.polynomial (χ.excludePrimes R hR) false W₂ X₂ 0 0 *
      (∏i∈F,naturalSlot (χ.excludePrimes R hR) (pool i) (β i) (P i)) =
    ∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
      signedCoefficient χ R D₁ D₂ J pool β P *
        (HeckeDyadic.polynomial χ false W₁ (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
         HeckeDyadic.polynomial χ false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
         ∏i∈F\J,naturalSlot χ (pool i) (β i) (P i)) := by
  have hs : (∏i∈F,naturalSlot (χ.excludePrimes R hR) (pool i) (β i) (P i))=
      ∑J∈F.powerset,(-1:ℂ)^J.card*(∏i∈J,naturalSlot χ (pool i∩R) (β i) (P i))*
        (∏i∈F\J,naturalSlot χ (pool i) (β i) (P i)) := by
    have hh:=prod_sub_expansion F (fun i=> naturalSlot χ (pool i) (β i) (P i))
      (fun i=> naturalSlot χ (pool i∩R) (β i) (P i))
    exact (Finset.prod_congr rfl (fun i hi=> naturalSlot_delete χ R hR (pool i) (hp i hi) (β i) (P i))).trans hh
  rw [normalized_finite_deletion_moebius χ R hR W₁ (schwartz_decayTwo W₁) X₁ hX₁,
    normalized_finite_deletion_moebius χ R hR W₂ (schwartz_decayTwo W₂) X₂ hX₂,hs]
  rw [Finset.sum_mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro D₁ hD₁
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro D₂ hD₂
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  dsimp only [signedCoefficient,plainCoefficient]
  ring

def slotMass (R pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) : ℝ :=
  (Real.sqrt P)⁻¹ * ∑I∈pool∩R,‖β I‖

lemma slotMass_nonneg (R pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) :
    0≤ slotMass R pool β P := by unfold slotMass;positivity

lemma naturalSlot_norm (χ : Character) (R pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) :
    ‖naturalSlot χ (pool∩R) β P‖≤ slotMass R pool β P := by
  rw [naturalSlot,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hi
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)

lemma plainCoefficient_norm (χ : Character) (D : Finset (Ideal O))
    (hD : ∀I∈D,Prime I) : ‖plainCoefficient χ D‖≤ weight (∏I∈D,I) := by
  rw [plainCoefficient,subset_product_moebius D hD]
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_div_of_nonneg_right (idealCoeff_norm_le_one χ _) (Real.sqrt_nonneg _)).trans_eq
    (by simp only [weight,one_div])

lemma slot_point_mass (I : Ideal O) (hI : Prime I) (β : Ideal O→ℂ)
    (P b M : ℝ) (hP : 0< P) (hM : 0≤ M) (hβ : ‖β I‖≤ M)
    (hs : β I≠0 → (I.absNorm:ℝ)≤ b*P) :
    (Real.sqrt P)⁻¹*‖β I‖≤(Real.sqrt (max 1 b)*M)*weight I := by
  by_cases hz : β I=0
  · simp only [hz,norm_zero,mul_zero]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hM) (weight_nonneg _)
  have hN : (0:ℝ)< I.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI.ne_zero)
  have hB : 0≤ max 1 b := le_trans zero_le_one (le_max_left _ _)
  have hsqrt : Real.sqrt (I.absNorm:ℝ)≤ Real.sqrt (max 1 b)*Real.sqrt P := by
    rw [←Real.sqrt_mul hB]
    exact Real.sqrt_le_sqrt ((hs hz).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hP.le))
  have hi : (Real.sqrt P)⁻¹≤ Real.sqrt (max 1 b)*weight I := by
    rw [weight,←div_eq_mul_inv,inv_eq_one_div,
      div_le_div_iff₀ (Real.sqrt_pos.mpr hP) (Real.sqrt_pos.mpr hN)]
    simpa using hsqrt
  calc
    _≤(Real.sqrt (max 1 b)*weight I)*M :=
      mul_le_mul hi hβ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (weight_nonneg _))
    _=_ := by ring

lemma slotMass_bound (R pool : Finset (Ideal O)) (hp : ∀I∈pool,Prime I)
    (β : Ideal O→ℂ) (P b M : ℝ) (hP : 0< P) (hM : 0≤ M)
    (hβ : ∀I∈pool,‖β I‖≤ M) (hs : ∀I∈pool,β I≠0 → (I.absNorm:ℝ)≤ b*P) :
    slotMass R pool β P≤(Real.sqrt (max 1 b)*M)*∑I∈R,weight I := by
  unfold slotMass
  rw [Finset.mul_sum]
  calc
    _≤∑I∈pool∩R,(Real.sqrt (max 1 b)*M)*weight I :=
      Finset.sum_le_sum (fun I hi=> slot_point_mass I (hp I (Finset.mem_inter.mp hi).1)
        β P b M hP hM (hβ I (Finset.mem_inter.mp hi).1) (hs I (Finset.mem_inter.mp hi).1))
    _=(Real.sqrt (max 1 b)*M)*∑I∈pool∩R,weight I := (Finset.mul_sum _ _ _).symm
    _≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun I hi hn=> weight_nonneg I))
      (mul_nonneg (Real.sqrt_nonneg _) hM)

lemma one_add_sum_weight (R : Finset (Ideal O)) :
    1+∑I∈R,weight I≤∏I∈R,(1+weight I) := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert I R hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi]
    have hw:=weight_nonneg I
    have hs:0≤∑J∈R,weight J:=Finset.sum_nonneg (fun J _=> weight_nonneg J)
    nlinarith

lemma deletion_le_euler (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I) :
    (∏I∈R,(1+weight I))≤∏I∈R,localMass I := by
  apply Finset.prod_le_prod (fun I hi=> by linarith [weight_nonneg I])
  intro I hi
  apply (le_div_iff₀ (sub_pos.mpr (prime_weight_lt_one I (hR I hi)))).mpr
  have h:=weight_nonneg I
  nlinarith

lemma euler_ge_one (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I) :
    1≤∏I∈R,localMass I :=
  (show 1≤∏I∈R,(1+weight I) by
    linarith [Finset.sum_nonneg (s:=R) (fun I _=> weight_nonneg I),one_add_sum_weight R]).trans
    (deletion_le_euler R hR)

lemma one_add_slotMass (R pool : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (hp : ∀I∈pool,Prime I) (β : Ideal O→ℂ) (P b M : ℝ) (hP : 0< P) (hM : 0≤ M)
    (hβ : ∀I∈pool,‖β I‖≤ M) (hs : ∀I∈pool,β I≠0 → (I.absNorm:ℝ)≤ b*P) :
    1+slotMass R pool β P≤ max 1 (Real.sqrt (max 1 b)*M)*(∏I∈R,localMass I) := by
  have ha:=slotMass_bound R pool hp β P b M hP hM hβ hs
  have hb:1+∑I∈R,weight I≤∏I∈R,localMass I:=
    (one_add_sum_weight R).trans (deletion_le_euler R hR)
  have hc:=le_max_left 1 (Real.sqrt (max 1 b)*M)
  have hd:=le_max_right 1 (Real.sqrt (max 1 b)*M)
  have he:0≤∑I∈R,weight I:=Finset.sum_nonneg (fun I _=> weight_nonneg I)
  nlinarith

def coefficientMajorant (R D₁ D₂ : Finset (Ideal O)) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) : ℝ :=
  weight (∏I∈D₁,I)*weight (∏I∈D₂,I)*∏i∈J,slotMass R (pool i) (β i) (P i)

omit [DecidableEq α] in
lemma signedCoefficient_norm (χ : Character) (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : D₁⊆R) (hD₂ : D₂⊆R) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) :
    ‖signedCoefficient χ R D₁ D₂ J pool β P‖≤ coefficientMajorant R D₁ D₂ J pool β P := by
  simp only [signedCoefficient,norm_mul,norm_pow,norm_neg,norm_one,one_pow,mul_one,norm_prod]
  apply mul_le_mul
  · exact mul_le_mul (plainCoefficient_norm χ D₁ (fun I hi=> hR I (hD₁ hi)))
      (plainCoefficient_norm χ D₂ (fun I hi=> hR I (hD₂ hi))) (norm_nonneg _) (weight_nonneg _)
  · exact Finset.prod_le_prod (fun i _=> norm_nonneg _) (fun i _=> naturalSlot_norm χ R (pool i) (β i) (P i))
  · positivity
  · exact mul_nonneg (weight_nonneg _) (weight_nonneg _)

omit [DecidableEq α] in
lemma majorant_mass (R : Finset (Ideal O)) (F : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) :
    (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
      coefficientMajorant R D₁ D₂ J pool β P)=
      (∏I∈R,(1+weight I))^2*(∏i∈F,(1+slotMass R (pool i) (β i) (P i))) := by
  simp only [coefficientMajorant,←Finset.mul_sum]
  rw [←Finset.prod_one_add]
  simp only [←Finset.sum_mul]
  rw [←Finset.sum_mul_sum,deletion_mass]
  ring

def uniformMajorant (R D₁ D₂ : Finset (Ideal O)) (J : Finset α) (b M : α→ℝ) : ℝ :=
  weight (∏I∈D₁,I)*weight (∏I∈D₂,I)*
    ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)

omit [DecidableEq α] in
lemma uniformMajorant_nonneg (R D₁ D₂ : Finset (Ideal O)) (J : Finset α)
    (b M : α→ℝ) (hM : ∀i∈J,0≤ M i) :
    0≤ uniformMajorant R D₁ D₂ J b M := by
  apply mul_nonneg (mul_nonneg (weight_nonneg _) (weight_nonneg _))
  exact Finset.prod_nonneg (fun i hi=> mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
    (Finset.sum_nonneg (fun I _=> weight_nonneg I)))

omit [DecidableEq α] in
lemma signedCoefficient_uniform (χ : Character) (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : D₁⊆R) (hD₂ : D₂⊆R) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P b M : α→ℝ)
    (hp : ∀i∈J,∀I∈pool i,Prime I) (hP : ∀i∈J,0< P i) (hM : ∀i∈J,0≤ M i)
    (hβ : ∀i∈J,∀I∈pool i,‖β i I‖≤ M i)
    (hs : ∀i∈J,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤ b i*P i) :
    ‖signedCoefficient χ R D₁ D₂ J pool β P‖≤ uniformMajorant R D₁ D₂ J b M := by
  apply (signedCoefficient_norm χ R hR D₁ D₂ hD₁ hD₂ J pool β P).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (weight_nonneg _) (weight_nonneg _))
  exact Finset.prod_le_prod (fun i _=> slotMass_nonneg _ _ _ _)
    (fun i hi=> slotMass_bound R (pool i) (hp i hi) (β i) (P i) (b i) (M i)
      (hP i hi) (hM i hi) (hβ i hi) (hs i hi))

omit [DecidableEq α] in
lemma uniformMajorant_mass (R : Finset (Ideal O)) (F : Finset α) (b M : α→ℝ) :
    (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,uniformMajorant R D₁ D₂ J b M)=
      (∏I∈R,(1+weight I))^2*
        ∏i∈F,(1+(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)) := by
  simp only [uniformMajorant,←Finset.mul_sum]
  rw [←Finset.prod_one_add]
  simp only [←Finset.sum_mul]
  rw [←Finset.sum_mul_sum,deletion_mass]
  ring

omit [DecidableEq α] in
lemma uniformMajorant_mass_le (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (F : Finset α) (b M : α→ℝ) (hM : ∀i∈F,0≤ M i) :
    (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,uniformMajorant R D₁ D₂ J b M)≤
      (∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)) * (∏I∈R,localMass I)^(2+F.card) := by
  rw [uniformMajorant_mass]
  have hE:=euler_ge_one R hR
  have hp (i : α) (hi : i∈F) :
      1+(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)≤
        max 1 (Real.sqrt (max 1 (b i))*M i)*(∏I∈R,localMass I) := by
    have ha:1+∑I∈R,weight I≤∏I∈R,localMass I:=(one_add_sum_weight R).trans (deletion_le_euler R hR)
    have hb:=le_max_left 1 (Real.sqrt (max 1 (b i))*M i)
    have hc:=le_max_right 1 (Real.sqrt (max 1 (b i))*M i)
    have hs:0≤∑I∈R,weight I:=Finset.sum_nonneg (fun I _=> weight_nonneg I)
    nlinarith
  calc
    _≤(∏I∈R,localMass I)^2*
        ∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)*(∏I∈R,localMass I) := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (Finset.prod_nonneg (fun I _=> by linarith [weight_nonneg I]))
          (deletion_le_euler R hR) 2
      · exact Finset.prod_le_prod (fun i hi=> add_nonneg zero_le_one
          (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
            (Finset.sum_nonneg (fun I _=> weight_nonneg I)))) hp
      · exact Finset.prod_nonneg (fun i hi=> add_nonneg zero_le_one
          (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
            (Finset.sum_nonneg (fun I _=> weight_nonneg I))))
      · exact sq_nonneg _
    _=_ := by rw [Finset.prod_mul_distrib,Finset.prod_const,pow_add];ring

omit [DecidableEq α] in

theorem uniform_mass_subpower (F : Finset α) (b M : α→ℝ) (hM : ∀i∈F,0≤ M i)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ (R : Finset (Ideal O)) (_hR : ∀I∈R,Prime I),
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,uniformMajorant R D₁ D₂ J b M)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
  let n:ℕ:=2+F.card
  have hn:(0:ℝ)< n:=by dsimp [n];positivity
  let δ:ℝ:=ε/n
  have hδ:0<δ:=div_pos hε hn
  obtain ⟨C₀,hC₀,hbound⟩:=euler_mass_subpower δ hδ
  let A:ℝ:=∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)
  have hA:0< A:=Finset.prod_pos (fun i _=> lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  refine ⟨A*C₀^n,mul_pos hA (pow_pos hC₀ n),?_⟩
  intro R hR
  have he:0≤∏I∈R,localMass I:=(euler_ge_one R hR).trans' zero_le_one
  have hr:0≤(Ideal.absNorm (∏I∈R,I):ℝ):=Nat.cast_nonneg _
  have hpow:((Ideal.absNorm (∏I∈R,I):ℝ)^δ)^n=(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr]
    congr 1
    dsimp [δ]
    exact div_mul_cancel₀ _ hn.ne'
  calc
    _≤ A*(∏I∈R,localMass I)^n:=uniformMajorant_mass_le R hR F b M hM
    _≤ A*(C₀*(Ideal.absNorm (∏I∈R,I):ℝ)^δ)^n:=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he (hbound R hR) n) hA.le
    _=_:=by rw [mul_pow,hpow];ring

omit [DecidableEq α] in

theorem signed_mass_subpower (F : Finset α) (b M : α→ℝ) (hM : ∀i∈F,0≤ M i)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ (R : Finset (Ideal O)) (_hR : ∀I∈R,Prime I)
      (χ : Character) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ),
      (∀i∈F,∀I∈pool i,Prime I) → (∀i∈F,0< P i) →
      (∀i∈F,∀I∈pool i,‖β i I‖≤ M i) →
      (∀i∈F,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤ b i*P i) →
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
        ‖signedCoefficient χ R D₁ D₂ J pool β P‖)≤ C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩:=uniform_mass_subpower F b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro R hR χ pool β P hp hP hβ hs
  apply le_trans _ (hbound R hR)
  apply Finset.sum_le_sum
  intro D₁ hD₁
  apply Finset.sum_le_sum
  intro D₂ hD₂
  apply Finset.sum_le_sum
  intro J hJ
  have hj:=Finset.mem_powerset.mp hJ
  exact signedCoefficient_uniform χ R hR D₁ D₂ (Finset.mem_powerset.mp hD₁)
    (Finset.mem_powerset.mp hD₂) J pool β P b M
    (fun i hi=> hp i (hj hi)) (fun i hi=> hP i (hj hi)) (fun i hi=> hM i (hj hi))
    (fun i hi=> hβ i (hj hi)) (fun i hi=> hs i (hj hi))

lemma profile_bounds (pool : Finset (Ideal O)) (ν : Ideal O→ℂ) (W : ℝ→ℂ)
    (P b M : ℝ) (hP : 0< P) (hν : ∀I∈pool,‖ν I‖≤1)
    (hW : ∀x,‖W x‖≤ M) (hs : Function.support W⊆Set.Iic b) :
    (∀I∈pool,‖ν I*W ((I.absNorm:ℝ)/P)‖≤ M) ∧
      (∀I∈pool,ν I*W ((I.absNorm:ℝ)/P)≠0 → (I.absNorm:ℝ)≤ b*P) := by
  constructor
  · intro I hi
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hν I hi)).trans (hW _)
  · intro I hi hn
    exact (div_le_iff₀ hP).mp (hs (right_ne_zero_of_mul hn))

omit [DecidableEq α] in

theorem profile_signed_mass_subpower (F : Finset α) (b M : α→ℝ)
    (hM : ∀i∈F,0≤ M i) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0< C ∧ ∀ (R : Finset (Ideal O)) (_hR : ∀I∈R,Prime I)
      (χ : Character) (pool : α→Finset (Ideal O)) (ν : α→Ideal O→ℂ)
      (W : α→ℝ→ℂ) (P : α→ℝ),
      (∀i∈F,∀I∈pool i,Prime I) → (∀i∈F,0< P i) →
      (∀i∈F,∀I∈pool i,‖ν i I‖≤1) → (∀i∈F,∀x,‖W i x‖≤ M i) →
      (∀i∈F,Function.support (W i)⊆Set.Iic (b i)) →
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
        ‖signedCoefficient χ R D₁ D₂ J pool
          (fun i I=>ν i I*W i ((I.absNorm:ℝ)/P i)) P‖)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩:=signed_mass_subpower F b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro R hR χ pool ν W P hp hP hν hW hs
  exact hbound R hR χ pool (fun i I=>ν i I*W i ((I.absNorm:ℝ)/P i)) P hp hP
    (fun i hi=>(profile_bounds (pool i) (ν i) (W i) (P i) (b i) (M i)
      (hP i hi) (hν i hi) (hW i hi) (hs i hi)).1)
    (fun i hi=>(profile_bounds (pool i) (ν i) (W i) (P i) (b i) (M i)
      (hP i hi) (hν i hi) (hW i hi) (hs i hi)).2)

end CenteredMomentCommonMaskExpansion

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentNaturalRowSource
open HeckeFamily CompletedGauss UniqueFactorizationMonoid 
local notation "O" => Eisenstein.O

lemma support_prime (R P : Ideal O) (hP : P∈primeSupport R) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

lemma coprime_support_iff (I R : Ideal O) (hR : R≠0) :
    (∀P∈primeSupport R,IsCoprime I P) ↔ IsCoprime I R := by
  constructor
  · intro h
    have aux : ∀s : Multiset (Ideal O),(∀P∈s,IsCoprime I P)→IsCoprime I s.prod := by
      intro s
      induction s using Multiset.induction_on with
      | empty => intro _; simpa using (isCoprime_one_right : IsCoprime I 1)
      | @cons a s ih =>
        intro hs
        rw [Multiset.prod_cons]
        exact (hs a (Multiset.mem_cons_self _ _)).mul_right
          (ih (fun P hP=> hs P (Multiset.mem_cons_of_mem hP)))
    rw [←Ideal.prod_normalizedFactors_eq_self hR]
    exact aux _ (fun P hP=> h P (Multiset.mem_toFinset.mpr hP))
  · intro h P hP
    exact h.of_isCoprime_of_dvd_right (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP))

def excluded (χ : Character) (R : Ideal O) : Character :=
  χ.excludePrimes (primeSupport R) (support_prime R)

lemma excluded_ideal (χ : Character) (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    idealCoeff (excluded χ R) I=if IsCoprime I R then idealCoeff χ I else 0 := by
  simp only [excluded,idealCoeff_excludePrimes,coprime_support_iff I R hR]

lemma excluded_element (χ : Character) (hχ0 : elementCoeff χ 0=0)
    (R : Ideal O) (hR : R≠0) (n : O) :
    elementCoeff (excluded χ R) n=
      if IsCoprime (Ideal.span {n}) R then elementCoeff χ n else 0 := by
  by_cases hn : n=0
  · subst n
    have hh : elementCoeff (excluded χ R) 0=0 := by
      rw [excluded,Character.excludePrimes,elementCoeff_refineModulus,hχ0]
      split_ifs <;> rfl
    rw [hh,hχ0]
    split_ifs <;> rfl
  · rw [←idealCoeff_span _ hn,excluded_ideal χ R hR,idealCoeff_span χ hn]

lemma excluded_element_generator (χ : Character) (hχ0 : elementCoeff χ 0=0)
    (R : Ideal O) (hR : R≠0) (n : O) :
    elementCoeff (excluded χ R) n=
      if IsCoprime n (cubicIdealGenerator R) then elementCoeff χ n else 0 := by
  rw [excluded_element χ hχ0 R hR]
  conv_lhs => rw [←span_cubicIdealGenerator R,Ideal.isCoprime_span_singleton_iff]

end CenteredMomentNaturalRowSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentNaturalRowSource
open HeckeFamily HeckeRowClosure CanonicalRowCompletion 
open CenteredMomentSecondHeightFamily CenteredMomentFixedRowMask CenteredExceptionalProfile
local notation "O" => Eisenstein.O

structure NaturalRow (η : Character) (z : O) where
  character : Character
  modulus_bound : character.modulus.absNorm≤ rowConductorBound η fixedBadMask 1 z
  element : ∀n,elementCoeff character n=rowTwist (elementHom η) fixedBadMask 1 z n

def naturalRow (η : Character) (z : O) (hz : z≠0) : NaturalRow η z := by
  let e:=exists_row_character_with_conductor η fixedBadMask 1 z
    fixedBadMask_ne_zero one_ne_zero hz (dvd_mul_right _ _) (dvd_mul_left _ _)
  exact ⟨Classical.choose e,(Classical.choose_spec e).1,(Classical.choose_spec e).2⟩

lemma NaturalRow.ideal {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O) :
    idealCoeff F.character I=idealCoeff η I*idealRowHom (fixedBadMask^6*z) I := by
  simpa only [one_pow,mul_one] using idealCoeff_eq_row η F.character fixedBadMask 1 z F.element I

lemma NaturalRow.element_zero {η : Character} {z : O} (F : NaturalRow η z) :
    elementCoeff F.character 0=0 := by
  rw [F.element]
  change elementHom η 0*idealRowHom (fixedBadMask^6*1^4*z) (Ideal.span {(0:O)})=0
  rw [Ideal.span_singleton_zero]
  change elementHom η 0*idealRowHom (fixedBadMask^6*1^4*z) (0:Ideal O)=0
  rw [(idealRowHom (fixedBadMask^6*1^4*z)).map_zero,mul_zero]

lemma NaturalRow.masked_element {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (n : O) :
    elementCoeff (excluded F.character R) n=
      rowTwist (elementHom η) (fixedBadMask*cubicIdealGenerator R) 1 z n := by
  rw [excluded_element_generator F.character F.element_zero R hR,F.element]
  simpa only [one_mul] using
    (row_mask_mul η fixedBadMask (cubicIdealGenerator R) 1 z n
      (dvd_mul_right _ _) (dvd_mul_left _ _)).symm

lemma NaturalRow.masked_ideal {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    idealCoeff (excluded F.character R) I=
      idealCoeff η I*idealRowHom ((fixedBadMask*cubicIdealGenerator R)^6*z) I := by
  simpa only [one_pow,mul_one] using idealCoeff_eq_row η (excluded F.character R)
    (fixedBadMask*cubicIdealGenerator R) 1 z (F.masked_element R hR) I

lemma NaturalRow.masked_element_span {η : Character} {z : O} (F : NaturalRow η z)
    (r : O) (hr : r≠0) (n : O) :
    elementCoeff (excluded F.character (Ideal.span {r})) n=
      rowTwist (elementHom η) (fixedBadMask*r) 1 z n := by
  rw [excluded_element F.character F.element_zero (Ideal.span {r})
    (Ideal.span_singleton_eq_bot.not.mpr hr),Ideal.isCoprime_span_singleton_iff,F.element]
  simpa only [one_mul] using
    (row_mask_mul η fixedBadMask r 1 z n (dvd_mul_right _ _) (dvd_mul_left _ _)).symm

theorem NaturalRow.nonprincipal {η : Character} {z : O} (F : NaturalRow η z)
    (hz : z≠0) (Q R : Ideal O) (hR : R≠0)
    (hex : ¬FixedInducingRow η Q (fixedBadMask*cubicIdealGenerator R) 1 z) :
    F.character.residue≠1 := by
  have hbase : ¬FixedInducingRow η Q fixedBadMask 1 z := by
    intro h
    exact hex ((fixedInducingRow_mul_mask_iff η Q fixedBadMask (cubicIdealGenerator R) 1 z
      fixedBadMask_ne_zero (cubicIdealGenerator_ne_zero R hR) one_ne_zero hz
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr h)
  exact CenteredMomentNonprincipalGate.actual_row_nonprincipal η F.character Q fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) hbase

def fixedConductorFactor : ℕ := (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm

lemma NaturalRow.natural_modulus_bound {η : Character} {z : O} (F : NaturalRow η z) :
    F.character.modulus.absNorm≤η.modulus.absNorm*fixedConductorFactor*(Ideal.span {z}).absNorm := by
  have hh:=F.modulus_bound
  simpa [rowConductorBound,fixedConductorFactor,Ideal.span_singleton_one,mul_assoc] using hh

theorem NaturalRow.modulus_power_bound {η : Character} {z : O} (F : NaturalRow η z)
    (Z m q Cz : ℝ) (hZ : 0< Z) (_hCz : 0≤ Cz)
    (hη : (η.modulus.absNorm:ℝ)≤ Z^m)
    (hz : ((Ideal.span {z}).absNorm:ℝ)≤ Cz*Z^q) :
    (F.character.modulus.absNorm:ℝ)≤(fixedConductorFactor:ℝ)*Cz*Z^(m+q) := by
  have hb : (F.character.modulus.absNorm:ℝ)≤
      (η.modulus.absNorm:ℝ)*(fixedConductorFactor:ℝ)*((Ideal.span {z}).absNorm:ℝ) :=
    by exact_mod_cast F.natural_modulus_bound
  apply hb.trans
  calc
    _≤(Z^m*(fixedConductorFactor:ℝ))*(Cz*Z^q) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _)) hz
        (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg hZ.le _) (Nat.cast_nonneg _))
    _=(fixedConductorFactor:ℝ)*Cz*Z^(m+q) := by rw [Real.rpow_add hZ]; ring

end CenteredMomentNaturalRowSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentNaturalRowSource
open HeckeFamily CenteredMomentSecondHeightFamily 
open CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
local notation "O" => Eisenstein.O

lemma NaturalRow.masked_plain {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (W : ℝ→ℂ) (t X : ℝ) :
    rowTwistedSum η (fixedBadMask*cubicIdealGenerator R) 1 z W t X=
      twistedIdealSum (excluded F.character R) W t X := by
  exact rowTwistedSum_eq η (excluded F.character R) (fixedBadMask*cubicIdealGenerator R) 1 z
    (by simpa only [one_mul] using F.masked_element R hR) W t X

lemma NaturalRow.masked_slot {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (S : Finset (Ideal O)) (β : Ideal O→ℂ) (t : ℝ) :
    rowSlot η (fixedBadMask*cubicIdealGenerator R) 1 z S β t=
      ∑I∈S,β I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t) := by
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro I hI
  rw [F.masked_ideal R hR I,one_mul]

theorem NaturalRow.masked_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ)
    (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    positiveSlotRow η (fixedBadMask*cubicIdealGenerator R) 1 z W₁ W₂ S β P t X₁ X₂=
      (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹*
        ((twistedIdealSum (excluded F.character R) W₁ t X₁*
          twistedIdealSum (excluded F.character R) W₂ t X₂)*
          ∏i,∑I∈S i,β i I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t)) := by
  simp only [positiveSlotRow,F.masked_plain R hR,F.masked_slot R hR]

theorem NaturalRow.masked_retained {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ)
    (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    retainedPositiveRow η (fixedBadMask*cubicIdealGenerator R) 1 z W₁ W₂ S β P t X₁ X₂=
      (Real.sqrt (clippedScale X₁*clippedScale X₂*∏i,P i):ℂ)⁻¹*
        ((twistedIdealSum (excluded F.character R) (dilated W₁ (clipDilation X₁)) t (clippedScale X₁)*
          twistedIdealSum (excluded F.character R) (dilated W₂ (clipDilation X₂)) t (clippedScale X₂))*
          ∏i,∑I∈S i,β i I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t)) := by
  exact F.masked_positive R hR _ _ S β P t _ _

end CenteredMomentNaturalRowSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace CenteredMomentCommonMaskEnergy
open HeckeFamily CenteredMomentCommonMaskExpansion CenteredMomentNaturalRowSource
open CenteredMomentHeckeTwist CenteredMomentHeckeVolume CenteredMomentHeckeCancellation CenteredMomentLattice
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
local notation "O" => Eisenstein.O

theorem finite_shared_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a f : ι→κ→ℂ) (ρ : κ→ℝ) (hρ : ∀j,0≤ρ j)
    (ha : ∀i j,‖a i j‖≤ρ j) (E : ℝ) (hE : 0≤ E)
    (hf : ∀j,(∑i,‖f i j‖^2)≤ E) :
    (∑i,‖∑j,a i j*f i j‖^2)≤(∑j,ρ j)^2*E := by
  have hb (j : κ) : (∑i,‖a i j*f i j‖^2)≤(ρ j*Real.sqrt E)^2 := by
    calc
      _≤∑i,(ρ j)^2*‖f i j‖^2 := Finset.sum_le_sum (fun i _=> by
        rw [norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha i j) 2) (sq_nonneg _))
      _=(ρ j)^2*(∑i,‖f i j‖^2) := (Finset.mul_sum _ _ _).symm
      _≤(ρ j)^2*E := mul_le_mul_of_nonneg_left (hf j) (sq_nonneg _)
      _=_ := by rw [mul_pow,Real.sq_sqrt hE]
  have hh := CompletedGauss.finite_tsum_energy_bound
    (fun j i=> a i j*f i j) (fun j=>ρ j*Real.sqrt E)
    (fun j=> mul_nonneg (hρ j) (Real.sqrt_nonneg _)) (summable_of_hasFiniteSupport (Set.toFinite _)) hb
  simpa only [tsum_fintype,←Finset.sum_mul,mul_pow,Real.sq_sqrt hE] using hh.2

lemma triple_sum {τ : Type*} {υ : Type*} {ξ : Type*} {A : Type*} [AddCommMonoid A]
    (S : Finset τ) (T : Finset υ) (U : Finset ξ)
    [Fintype ({x // x∈S}×{x // x∈T}×{x // x∈U})]
    (g : τ→υ→ξ→A) :
    (∑j : {x // x∈S}×{x // x∈T}×{x // x∈U},g j.1.val j.2.1.val j.2.2.val)=
      ∑x∈S,∑y∈T,∑z∈U,g x y z := by
  have hh : (∑j : {x // x∈S}×{x // x∈T}×{x // x∈U},g j.1.val j.2.1.val j.2.2.val)=
      ∑j∈S×ˢ(T×ˢU),g j.1 j.2.1 j.2.2 := by
    apply Finset.sum_bij (fun j _=>(j.1.val,j.2.1.val,j.2.2.val))
    · intro j _
      exact Finset.mem_product.mpr ⟨j.1.property,Finset.mem_product.mpr ⟨j.2.1.property,j.2.2.property⟩⟩
    · intro i _ j _ h
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst h)
      · apply Prod.ext
        · exact Subtype.ext (congrArg (fun x=> x.2.1) h)
        · exact Subtype.ext (congrArg (fun x=> x.2.2) h)
    · intro j hj
      obtain ⟨h1,h23⟩:=Finset.mem_product.mp hj
      obtain ⟨h2,h3⟩:=Finset.mem_product.mp h23
      exact ⟨(⟨j.1,h1⟩,⟨j.2.1,h2⟩,⟨j.2.2,h3⟩),Finset.mem_univ _,rfl⟩
    · intro j _
      rfl
  simpa only [Finset.sum_product] using hh

theorem actual_shared_energy {α : Type*} [DecidableEq α]
    (F : Finset α) (b M : α→ℝ) (hM : ∀j∈F,0≤ M j) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)(χ : ι→Character)
        (W₁ W₂ : ι→𝓢(ℝ,ℂ))(X₁ X₂ : ι→ℝ)
        (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ),
      (∀i,0< X₁ i) → (∀i,0< X₂ i) →
      (∀i j,j∈F → ∀I∈pool i j,Prime I) → (∀i j,j∈F → 0< P i j) →
      (∀i j,j∈F → ∀I∈pool i j,‖β i j I‖≤ M j) →
      (∀i j,j∈F → ∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤ b j*P i j) →
      ∀E : ℝ,0≤ E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        (∑i,‖HeckeDyadic.polynomial (χ i) false (W₁ i)
          (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          HeckeDyadic.polynomial (χ i) false (W₂ i)
          (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ i) (pool i j) (β i j) (P i j)‖^2)≤ E) →
      (∑i,‖HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₁ i) (X₁ i) 0 0 *
        HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₂ i) (X₂ i) 0 0 *
        ∏j∈F,naturalSlot ((χ i).excludePrimes R hR) (pool i j) (β i j) (P i j)‖^2)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E := by
  obtain ⟨C,hC,hmass⟩:=uniform_mass_subpower F b M hM (ε/2) (by positivity)
  refine ⟨C ^ 2,sq_pos_of_pos hC,?_⟩
  intro ι _ R hR χ W₁ W₂ X₁ X₂ pool β P hX₁ hX₂ hp hP hβ hs E hE he
  let κ := {D : Finset (Ideal O) // D∈R.powerset} ×
    {D : Finset (Ideal O) // D∈R.powerset} × {J : Finset α // J∈F.powerset}
  let a (i : ι) (j : κ) := signedCoefficient (χ i) R j.1.val j.2.1.val j.2.2.val (pool i) (β i) (P i)
  let f (i : ι) (j : κ) := HeckeDyadic.polynomial (χ i) false (W₁ i)
    (X₁ i/(Ideal.absNorm (∏I∈j.1.val,I):ℝ)) 0 0 *
    HeckeDyadic.polynomial (χ i) false (W₂ i)
    (X₂ i/(Ideal.absNorm (∏I∈j.2.1.val,I):ℝ)) 0 0 *
    ∏k∈F\j.2.2.val,naturalSlot (χ i) (pool i k) (β i k) (P i k)
  let ρ (j : κ) := uniformMajorant R j.1.val j.2.1.val j.2.2.val b M
  have hρ (j : κ) : 0≤ρ j := uniformMajorant_nonneg _ _ _ _ _ _
    (fun k hk=> hM k (Finset.mem_powerset.mp j.2.2.property hk))
  have ha (i : ι) (j : κ) : ‖a i j‖≤ρ j := by
    exact signedCoefficient_uniform (χ i) R hR _ _
      (Finset.mem_powerset.mp j.1.property) (Finset.mem_powerset.mp j.2.1.property)
      _ (pool i) (β i) (P i) b M
      (fun k hk=> hp i k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=> hP i k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=> hM k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=> hβ i k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=> hs i k (Finset.mem_powerset.mp j.2.2.property hk))
  have hh:=finite_shared_energy a f ρ hρ ha E hE
    (fun j=> he j.1.val j.1.property j.2.1.val j.2.1.property j.2.2.val j.2.2.property)
  have hid (i : ι) : (∑j,a i j*f i j)=
      HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₁ i) (X₁ i) 0 0 *
      HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₂ i) (X₂ i) 0 0 *
      ∏j∈F,naturalSlot ((χ i).excludePrimes R hR) (pool i j) (β i j) (P i j) := by
    exact (triple_sum R.powerset R.powerset F.powerset
      (fun D₁ D₂ J=> signedCoefficient (χ i) R D₁ D₂ J (pool i) (β i) (P i)*
        (HeckeDyadic.polynomial (χ i) false (W₁ i) (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
         HeckeDyadic.polynomial (χ i) false (W₂ i) (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
         ∏k∈F\J,naturalSlot (χ i) (pool i k) (β i k) (P i k)))).trans
      (simultaneous_deletion (χ i) R hR (W₁ i) (W₂ i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i)
        F (pool i) (hp i) (β i) (P i)).symm
  have hm : (∑j,ρ j)≤ C*(Ideal.absNorm (∏I∈R,I):ℝ)^(ε/2) := by
    exact (triple_sum R.powerset R.powerset F.powerset
      (fun D₁ D₂ J=> uniformMajorant R D₁ D₂ J b M)).trans_le (hmass R hR)
  have hr : ((Ideal.absNorm (∏I∈R,I):ℝ)^(ε/2))^2=(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  simp_rw [hid] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun j _=> hρ j)) hm 2) hE).trans_eq
      (by rw [mul_pow,hr]))

lemma sqrt_inverse_cpow (X : ℝ) (hX : 0< X) :
    (Real.sqrt X:ℂ)⁻¹=(X:ℂ)^(-(1/2:ℂ)) := by
  rw [Complex.cpow_neg,Real.sqrt_eq_rpow]
  congr 1
  simpa using (Complex.ofReal_cpow hX.le (1/2:ℝ))

lemma plain_zero_height (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0< X) :
    HeckeDyadic.polynomial χ false W X 0 0=(Real.sqrt X:ℂ)⁻¹*idealSum χ W X := by
  rw [sqrt_inverse_cpow X hX]
  unfold HeckeDyadic.polynomial idealSum
  congr 1
  have he:=tsum_subtype_eq_of_support_subset
    (s:={I : Ideal O | I≠0}) (f:=fun I : Ideal O=> idealCoeff χ I*W ((I.absNorm:ℝ)/X))
    (by intro I hI hi;subst I;exact hI (by simp only [map_zero,zero_mul]))
  change (∑' I : HeckeDyadic.NonzeroIdeal,idealCoeff χ I.val*W ((I.val.absNorm:ℝ)/X))=_ at he
  simpa only [HeckeDyadic.summand,HeckeDyadic.coefficient,Bool.false_eq_true,ite_false,
    HeckeDyadic.norm,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,mul_zero,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,HeckeDyadic.NonzeroIdeal,CubicEisenstein.NonzeroIdeal] using he

def heightCoefficient (β : Ideal O→ℂ) (t : ℝ) (I : Ideal O) : ℂ :=
  β I*(I.absNorm:ℂ)^(Complex.I*t)

lemma heightCoefficient_norm (β : Ideal O→ℂ) (t : ℝ) (I : Ideal O) (hI : I≠0) :
    ‖heightCoefficient β t I‖=‖β I‖ := by
  have hn : (0:ℝ)< I.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  rw [heightCoefficient,norm_mul]
  have hp : ‖(I.absNorm:ℂ)^(Complex.I*t)‖=1 := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hn (Complex.I*t)
  rw [hp,mul_one]

lemma normalized_twisted_plain (χ : Character) (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0< X) :
    (Real.sqrt X:ℂ)⁻¹*twistedIdealSum χ W t X=
      (X:ℂ)^(Complex.I*t)*HeckeDyadic.polynomial χ false
        (normPowerProfile W a b ha hs hW t) X 0 0 := by
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX,plain_zero_height _ _ X hX]
  ring

theorem original_positive_normalized {α : Type*} [Fintype α] [DecidableEq α]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (hP : ∀i,0< P i) (t X₁ X₂ : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂) :
    positiveSlotRow η (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded F.character R) false
          (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) X₁ 0 0 *
         HeckeDyadic.polynomial (excluded F.character R) false
          (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t) X₂ 0 0 *
         ∏i,naturalSlot (excluded F.character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  rw [F.masked_positive R hR,twistedIdealSum_scale _ W₁ a₁ b₁ ha₁ hs₁ hW₁ t X₁ hX₁,
    twistedIdealSum_scale _ W₂ a₂ b₂ ha₂ hs₂ hW₂ t X₂ hX₂,
    plain_zero_height _ _ X₁ hX₁,plain_zero_height _ _ X₂ hX₂]
  have hn : (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹=
      (Real.sqrt X₁:ℂ)⁻¹*(Real.sqrt X₂:ℂ)⁻¹*∏i,(Real.sqrt (P i):ℂ)⁻¹ := by
    rw [Real.sqrt_mul (mul_pos hX₁ hX₂).le,Real.sqrt_mul hX₁.le,
      Real.sqrt_prod _ (fun i _=>(hP i).le),Complex.ofReal_mul,Complex.ofReal_mul,
      Complex.ofReal_prod,mul_inv_rev,mul_inv_rev,Finset.prod_inv_distrib]
    ring
  have hc (i : α) : (∑I∈pool i,β i I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t))=
      ∑I∈pool i,idealCoeff (excluded F.character R) I*heightCoefficient (β i) t I := by
    apply Finset.sum_congr rfl
    intro I hI
    unfold heightCoefficient
    ring
  simp_rw [hc]
  simp only [naturalSlot,Finset.prod_mul_distrib]
  rw [hn]
  ring

lemma deleted_height_phase (X N t : ℝ) (hX : 0< X) (hN : 0< N) :
    (X:ℂ)^(Complex.I*t)=(N:ℂ)^(Complex.I*t)*((X/N:ℝ):ℂ)^(Complex.I*t) := by
  have hh:=Complex.mul_cpow_ofReal_nonneg hN.le (div_nonneg hX.le hN.le) (Complex.I*t)
  rw [←Complex.ofReal_mul,show N*(X/N)=X by field_simp] at hh
  exact hh

lemma positive_height_phase_norm (X t : ℝ) (hX : 0< X) : ‖(X:ℂ)^(Complex.I*t)‖=1 := by
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos hX (Complex.I*t)

lemma deleted_normalized_twisted_plain (χ : Character) (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X N : ℝ) (hX : 0< X) (hN : 0< N) :
    (X:ℂ)^(Complex.I*t)*HeckeDyadic.polynomial χ false
      (normPowerProfile W a b ha hs hW t) (X/N) 0 0=
      (N:ℂ)^(Complex.I*t)*((Real.sqrt (X/N):ℂ)⁻¹*twistedIdealSum χ W t (X/N)) := by
  rw [normalized_twisted_plain χ W a b ha hs hW t (X/N) (div_pos hX hN),
    deleted_height_phase X N t hX hN]
  ring

theorem original_positive_deletion {α : Type*} [Fintype α] [DecidableEq α]
    (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (hp : ∀i,∀I∈pool i,Prime I)
    (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0< P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂) :
    let χ:=(naturalRow η z hz).character
    let S:=primeSupport R
    positiveSlotRow η (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        ∑D₁∈S.powerset,∑D₂∈S.powerset,∑J∈(Finset.univ : Finset α).powerset,
          signedCoefficient χ S D₁ D₂ J pool (fun i=> heightCoefficient (β i) t) P *
          (HeckeDyadic.polynomial χ false (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t)
            (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
           HeckeDyadic.polynomial χ false (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
            (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
           ∏i∈Finset.univ\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)) := by
  dsimp only
  rw [original_positive_normalized (naturalRow η z hz) R hR W₁ W₂ a₁ b₁ a₂ b₂
    ha₁ ha₂ hs₁ hs₂ hW₁ hW₂ pool β P hP t X₁ X₂ hX₁ hX₂]
  congr 1
  exact simultaneous_deletion (naturalRow η z hz).character (primeSupport R)
    (fun _ h => support_prime h) (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t)
    (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t) X₁ X₂ hX₁ hX₂ Finset.univ pool
    (fun i _=> hp i) (fun i=> heightCoefficient (β i) t) P

theorem original_retained_normalized {α : Type*} [Fintype α] [DecidableEq α]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0< P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂) (hr₁ : 1≤ X₁*b₁) (hr₂ : 1≤ X₂*b₂) :
    retainedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      (((clippedScale X₁):ℂ)^(Complex.I*t)*((clippedScale X₂):ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded F.character R) false
          (retainedProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ X₁ hX₁ hr₁ t) (clippedScale X₁) 0 0 *
         HeckeDyadic.polynomial (excluded F.character R) false
          (retainedProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ X₂ hX₂ hr₂ t) (clippedScale X₂) 0 0 *
         ∏i,naturalSlot (excluded F.character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  exact original_positive_normalized F R hR (dilated W₁ (clipDilation X₁))
    (dilated W₂ (clipDilation X₂)) (a₁/max 1 b₁) b₁ (a₂/max 1 b₂) b₂
    (div_pos ha₁ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (div_pos ha₂ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (dilated_support W₁ a₁ b₁ (max 1 b₁) (clipDilation X₁) ha₁ (le_max_left _ _)
      (clipDilation_ge_one X₁ hX₁) (clipDilation_le b₁ X₁ hX₁ hr₁) hs₁)
    (dilated_support W₂ a₂ b₂ (max 1 b₂) (clipDilation X₂) ha₂ (le_max_left _ _)
      (clipDilation_ge_one X₂ hX₂) (clipDilation_le b₂ X₂ hX₂ hr₂) hs₂)
    (dilated_contDiff W₁ hW₁ _) (dilated_contDiff W₂ hW₂ _) pool β P hP t
    _ _ (by unfold clippedScale;positivity) (by unfold clippedScale;positivity)

theorem original_retained_zero {α : Type*} [Fintype α]
    (η : Character) (m A z : O) (W₁ W₂ : ℝ→ℂ) (b₁ b₂ : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂)
    (hz : X₁*b₁<1 ∨ X₂*b₂<1) :
    retainedPositiveRow η m A z W₁ W₂ pool β P t X₁ X₂=0 := by
  unfold retainedPositiveRow positiveSlotRow
  rw [←clipped_rowTwistedSum η m A z W₁ t X₁ hX₁,
    ←clipped_rowTwistedSum η m A z W₂ t X₂ hX₂]
  rcases hz with h|h
  · rw [strict_subunit_rowTwistedSum_zero η m A z W₁ b₁ t X₁ hX₁ hs₁ h]
    simp
  · rw [strict_subunit_rowTwistedSum_zero η m A z W₂ b₂ t X₂ hX₂ hs₂ h]
    simp

theorem original_positive_energy {α : Type*} [Fintype α] [DecidableEq α]
    (b M : α→ℝ) (hM : ∀j,0≤ M j) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(η : ι→Character)(z : ι→O)(hz : ∀i,z i≠0)(R : Ideal O),R≠0 →
      ∀(W₁ W₂ : ι→ℝ→ℂ)(a₁ b₁ a₂ b₂ : ι→ℝ)
        (ha₁ : ∀i,0< a₁ i)(ha₂ : ∀i,0< a₂ i)
        (hs₁ : ∀i,Function.support (W₁ i)⊆Set.Icc (a₁ i) (b₁ i))
        (hs₂ : ∀i,Function.support (W₂ i)⊆Set.Icc (a₂ i) (b₂ i))
        (hW₁ : ∀i,ContDiff ℝ ∞ (W₁ i))(hW₂ : ∀i,ContDiff ℝ ∞ (W₂ i))
        (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ)
        (t X₁ X₂ : ι→ℝ),
      (∀i,0< X₁ i) → (∀i,0< X₂ i) →
      (∀i j,∀I∈pool i j,Prime I) → (∀i j,0< P i j) →
      (∀i j,∀I∈pool i j,‖β i j I‖≤ M j) →
      (∀i j,∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤ b j*P i j) →
      ∀E : ℝ,0≤ E →
      let χ:=fun i=>(naturalRow (η i) (z i) (hz i)).character
      let S:=primeSupport R
      (∀D₁∈S.powerset,∀D₂∈S.powerset,∀J∈(Finset.univ : Finset α).powerset,
        (∑i,‖HeckeDyadic.polynomial (χ i) false
          (normPowerProfile (W₁ i) (a₁ i) (b₁ i) (ha₁ i) (hs₁ i) (hW₁ i) (t i))
          (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          HeckeDyadic.polynomial (χ i) false
          (normPowerProfile (W₂ i) (a₂ i) (b₂ i) (ha₂ i) (hs₂ i) (hW₂ i) (t i))
          (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈Finset.univ\J,naturalSlot (χ i) (pool i j) (heightCoefficient (β i j) (t i)) (P i j)‖^2)≤ E) →
      (∑i,‖positiveSlotRow (η i)
        (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator R)
        1 (z i) (W₁ i) (W₂ i) (pool i) (β i) (P i) (t i) (X₁ i) (X₂ i)‖^2)≤
        C*(Ideal.absNorm (∏I∈S,I):ℝ)^ε*E := by
  obtain ⟨C,hC,hbound⟩:=actual_shared_energy (Finset.univ : Finset α) b M (fun j _=> hM j) ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ η z hz R hR W₁ W₂ a₁ b₁ a₂ b₂ ha₁ ha₂ hs₁ hs₂ hW₁ hW₂ pool β P t X₁ X₂
    hX₁ hX₂ hp hP hβ hs E hE
  dsimp only
  intro hchild
  have hh:=hbound (primeSupport R) (fun _ h => support_prime h)
    (fun i=>(naturalRow (η i) (z i) (hz i)).character)
    (fun i=> normPowerProfile (W₁ i) (a₁ i) (b₁ i) (ha₁ i) (hs₁ i) (hW₁ i) (t i))
    (fun i=> normPowerProfile (W₂ i) (a₂ i) (b₂ i) (ha₂ i) (hs₂ i) (hW₂ i) (t i))
    X₁ X₂ pool (fun i j=> heightCoefficient (β i j) (t i)) P hX₁ hX₂
    (fun i j _=> hp i j) (fun i j _=> hP i j)
    (fun i j _ I hi=> by rw [heightCoefficient_norm _ _ _ (hp i j I hi).ne_zero];exact hβ i j I hi)
    (fun i j _ I hi hn=> hs i j I hi (left_ne_zero_of_mul hn)) E hE hchild
  have he (i : ι) := original_positive_normalized (naturalRow (η i) (z i) (hz i)) R hR
    (W₁ i) (W₂ i) (a₁ i) (b₁ i) (a₂ i) (b₂ i) (ha₁ i) (ha₂ i) (hs₁ i) (hs₂ i)
    (hW₁ i) (hW₂ i) (pool i) (β i) (P i) (hP i) (t i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i)
  simp_rw [he,norm_mul,positive_height_phase_norm _ _ (hX₁ _),
    positive_height_phase_norm _ _ (hX₂ _),one_mul]
  simpa only [excluded,norm_mul] using hh

theorem original_positive_deletion_height {α : Type*} [Fintype α] [DecidableEq α]
    (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (hp : ∀i,∀I∈pool i,Prime I)
    (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0< P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂) :
    let χ:=(naturalRow η z hz).character
    let S:=primeSupport R
    positiveSlotRow η (CenteredMomentSecondHeightFamily.fixedBadMask*cubicIdealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      ∑D₁∈S.powerset,∑D₂∈S.powerset,∑J∈(Finset.univ : Finset α).powerset,
        (signedCoefficient χ S D₁ D₂ J pool (fun i=> heightCoefficient (β i) t) P *
          ((Ideal.absNorm (∏I∈D₁,I):ℂ)^(Complex.I*t)*
           (Ideal.absNorm (∏I∈D₂,I):ℂ)^(Complex.I*t))) *
        (((Real.sqrt (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)):ℂ)⁻¹ *
          twistedIdealSum χ W₁ t (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ))) *
         ((Real.sqrt (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)):ℂ)⁻¹ *
          twistedIdealSum χ W₂ t (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ))) *
         ∏i∈Finset.univ\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)) := by
  dsimp only
  rw [original_positive_deletion η z hz R hR W₁ W₂ a₁ b₁ a₂ b₂ ha₁ ha₂ hs₁ hs₂ hW₁ hW₂
    pool hp β P hP t X₁ X₂ hX₁ hX₂]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D₁ hD₁
  apply Finset.sum_congr rfl
  intro D₂ hD₂
  apply Finset.sum_congr rfl
  intro J hJ
  have hN₁:=CenteredMomentReflectionDeletion.subset_product_norm_pos D₁
    (fun I hi=> support_prime (Finset.mem_powerset.mp hD₁ hi))
  have hN₂:=CenteredMomentReflectionDeletion.subset_product_norm_pos D₂
    (fun I hi=> support_prime (Finset.mem_powerset.mp hD₂ hi))
  have h1:=deleted_normalized_twisted_plain (naturalRow η z hz).character W₁ a₁ b₁ ha₁ hs₁ hW₁
    t X₁ (Ideal.absNorm (∏I∈D₁,I):ℝ) hX₁ hN₁
  have h2:=deleted_normalized_twisted_plain (naturalRow η z hz).character W₂ a₂ b₂ ha₂ hs₂ hW₂
    t X₂ (Ideal.absNorm (∏I∈D₂,I):ℝ) hX₂ hN₂
  convert congrArg (fun q : ℂ=>
    signedCoefficient (naturalRow η z hz).character (primeSupport R) D₁ D₂ J pool
      (fun i=> heightCoefficient (β i) t) P * q *
      ∏i∈Finset.univ\J,naturalSlot (naturalRow η z hz).character (pool i) (heightCoefficient (β i) t) (P i))
    (congrArg₂ (fun x y : ℂ=> x*y) h1 h2) using 1 <;> push_cast <;> ring

end CenteredMomentCommonMaskEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff ComplexConjugate
namespace CenteredMomentDetectorDictionary
open HeckeFamily HeckeInverseAmplification HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles

lemma logTest_eq_iterate (W : ℝ→ℂ) (n : ℕ) : logTest W n=(logProfile^[n]) W := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [logTest,Function.iterate_succ_apply',ih]

lemma oriented_logTest (reverse : Bool) (W : ℝ→ℂ) (n : ℕ) :
    orientedProfile reverse ((logProfile^[n]) W)=logTest (orientedProfile reverse W) n := by
  rw [←logTest_eq_iterate]
  cases reverse
  · rfl
  · induction n with
    | zero => rfl
    | succ n ih =>
      simp only [logTest,orientedProfile,ite_true] at ih ⊢
      funext x
      rw [←logProfile_conjugate]
      exact congrArg (fun f : ℝ→ℂ=> logProfile f x) ih

theorem detector_profile_support (reverse : Bool) (n : ℕ) (σ t : ℝ) :
    Function.support (twistProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) σ t)
      ⊆Set.Icc (1/4) (9/4) := by
  apply (oriented_twist_support reverse _ σ t).trans
  rw [←logTest_eq_iterate]
  exact (logTest_support positiveAnnular n).trans positiveAnnular_support

theorem detector_profile_smooth (reverse : Bool) (n : ℕ) (σ t : ℝ) :
    ContDiff ℝ ∞ (twistProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) σ t) := by
  apply twistProfile_smooth _ σ t (1/4) (9/4) (by norm_num)
  · cases reverse <;> simp only [orientedProfile,ite_true]
    · rw [←logTest_eq_iterate]
      exact (logTest_support positiveAnnular n).trans positiveAnnular_support
    · rw [conjugate_profile_support,←logTest_eq_iterate]
      exact (logTest_support positiveAnnular n).trans positiveAnnular_support
  · have hw := logTest_smooth positiveAnnular n (1/4) (9/4) (by norm_num)
      positiveAnnular_support positiveAnnular_smooth
    rw [logTest_eq_iterate] at hw
    cases reverse
    · exact hw
    · exact conjugate_profile_smooth _ hw

end CenteredMomentDetectorDictionary

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles

lemma twistProfile_zero (W : ℝ→ℂ) : twistProfile W 0 0=W := by
  funext x
  simp [twistProfile,HeckeDyadic.shift]

lemma oriented_detector_log_support (reverse : Bool) (n : ℕ) :
    Function.support (orientedProfile reverse ((logProfile^[n]) positiveAnnular))⊆Icc (1/4) (9/4) := by
  simpa only [twistProfile_zero] using detector_profile_support reverse n 0 0

lemma oriented_detector_log_smooth (reverse : Bool) (n : ℕ) :
    ContDiff ℝ ∞ (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) := by
  simpa only [twistProfile_zero] using detector_profile_smooth reverse n 0 0

def detectorSchwartz (reverse : Bool) (n : ℕ) (σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  interpolatedProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) (1/4) (9/4)
    (by norm_num) (oriented_detector_log_support reverse n) (oriented_detector_log_smooth reverse n) σ
      (orientedFrequency reverse t)

lemma detectorSchwartz_apply (reverse : Bool) (n : ℕ) (σ t x : ℝ) :
    detectorSchwartz reverse n σ t x=
      twistProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) σ (orientedFrequency reverse t) x :=
  interpolatedProfile_apply _ _ _ _ _ _ _ _ _

theorem detectorSchwartz_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0< C ∧ ∀reverse : Bool,∀n : ℕ,n≤2→∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (detectorSchwartz reverse n σ t)≤ C*(1+‖t‖)^J := by
  choose degree C hC hb using fun q : Bool×Fin 3=> interpolatedProfile_uniform
    (orientedProfile q.1 ((logProfile^[q.2.val]) positiveAnnular)) (1/4) (9/4)
    (by norm_num) (oriented_detector_log_support q.1 q.2.val) (oriented_detector_log_smooth q.1 q.2.val) S
  let J := (Finset.univ : Finset (Bool×Fin 3)).sup degree
  have hsum : 0≤∑q : Bool×Fin 3,C q := Finset.sum_nonneg (fun q _=>(hC q).le)
  refine ⟨J,1+∑q : Bool×Fin 3,C q,by linarith,?_⟩
  intro reverse n hn σ hσ t
  let q : Bool×Fin 3 := (reverse,⟨n,by omega⟩)
  have hCq : C q≤1+∑q : Bool×Fin 3,C q := by
    have hh := Finset.single_le_sum (fun q (_ : q∈(Finset.univ : Finset (Bool×Fin 3)))=>(hC q).le) (Finset.mem_univ q)
    linarith
  have hdegree : degree q≤ J := Finset.le_sup (Finset.mem_univ q)
  have he := hb q σ hσ (orientedFrequency reverse t)
  have hnorm : ‖orientedFrequency reverse t‖=‖t‖ := by cases reverse <;> simp [orientedFrequency]
  rw [hnorm] at he
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (detectorSchwartz reverse n σ t)≤ _ at he
  exact he.trans (mul_le_mul hCq (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree)
    (by positivity) (by linarith))

end CenteredMomentDetectorDictionary

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open MeasureTheory
namespace CenteredMomentUniformReflectionProfile
open HeckeFamily JointLogSeparation SchwartzPlanePoisson
open CenteredMomentReflectedProfileMeasure CenteredMomentReflectedPairEnergy
open CenteredMomentReflectedUniformPair CenteredMomentOneReflectionEnergy

theorem source_separation (V : ℝ→ℂ) (M : ℝ) (hM : 0≤ M)
    (hV : ∀y,V y≠0 → |y|≤ M) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀G : 𝓢(ℝ,ℂ),∀D : ℝ,0< D →
      H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤ D → ∀s : ℝ,0< s →
      ∃density : 𝓢(ℝ,ℂ),
        (∀y : ℝ,V y*paperRadialFourier G (s*Real.exp y)=
          ∫v : ℝ,(V y*kernelLogPhase v y)*density v) ∧
        Integrable (fun v : ℝ=>(1+‖v‖)^J*‖density v‖) ∧
        (1+s)^A*(∫v : ℝ,(1+‖v‖)^J*‖density v‖)≤ C*D ∧
        (∀v : ℝ,(1+s)^A*(1+‖v‖)^J*‖density v‖≤ C*D) := by
  obtain ⟨C,hC,hsep⟩ := LocalLogFourier.coupled_positive_log_separation_linear_constant
    (fun _ : Unit=> V) (fun _=>1) (fun _=> M) (fun _=> hM) (fun _=> hV) A J
  obtain ⟨H,K,hK,hEuler⟩ := paperRadialFourier_euler_source_weighted_bound
    A (J+(volume : Measure ℝ).integrablePower)
  refine ⟨H,(C+1)*K,by positivity,?_⟩
  intro G D hD hGD s hs
  obtain ⟨density,hid,hi,hm,hp⟩ := hsep (paperRadialFourier G)
    (paperRadialFourier_contDiffOn G) (K*D) (by positivity)
    (fun j hj x hx=>(hEuler G j hj x hx.le).trans
      (mul_le_mul_of_nonneg_left hGD hK.le)) s hs
  have hconst : C*(K*D)≤((C+1)*K)*D := by nlinarith [mul_pos hK hD]
  exact ⟨density,(fun y=> by simpa using hid (fun _ : Unit=> y)),hi,
    hm.trans hconst,fun v=>(hp v).trans hconst⟩

theorem actual_one_uniform (V : ℝ→ℂ) (M : ℝ) (hM : 0≤ M)
    (hV : ∀y,V y≠0 → |y|≤ M) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀{ι : Type} [Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)(s X : ι→ℝ),
      (∀i,0< s i) → (∀i,0< X i) → ∀D E : ℝ,0< D → 0≤ E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤ D) →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*P i‖^2)
        ≤ E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i) false
        (fun x=> logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
          (X i) 0 0*P i‖^2)≤ C*D^2*E := by
  obtain ⟨H,K,hK,hb⟩ := source_separation V M hM hV A (J+2)
  refine ⟨H,(K*Real.pi)^2,by positivity,?_⟩
  intro ι _ G χ P s X hs hX D E hD hE hGD henergy
  choose d hid hi hm hp using fun i=> hb (G i) D hD (hGD i) (s i) (hs i)
  let e (i : ι) : ℂ := (1+s i)^A
  let F (i : ι) (x : ℝ) := e i*paperRadialFourier (G i) x
  let φ (i : ι) (v : ℝ) := HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*P i
  have hsep (i : ι) (y : ℝ) : V y*F i (s i*Real.exp y)=
      ∫v : ℝ,(V y*kernelLogPhase v y)*(e i • d i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V y*kernelLogPhase v y)*(e i*d i v))=
        (fun v=> e i*((V y*kernelLogPhase v y)*d i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid i y]
    dsimp [F]
    ring
  have hsource (i : ι) : HeckeDyadic.polynomial (χ i) false
      (fun x=> logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
        (X i) 0 0*P i=∫v : ℝ,(e i • d i) v*φ i v := by
    have hf : (fun x=> logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))=
        (fun x=> logWindow V x*F i (s i*x)) := by funext x;dsimp [F,e];ring
    rw [hf,plain_annular_separation V (F i) M (s i) (X i) (hX i) hV (e i • d i) (hsep i),
      ←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hint (i : ι) : Integrable (fun v : ℝ=>(e i • d i) v*φ i v) := by
    have hh := (plain_density_integrable V M (X i) (hX i) hV (χ i) (e i • d i)).mul_const (P i)
    apply hh.congr
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hpoint (i : ι) : ∀v,‖(e i • d i) v‖≤ envelope (K*D) J v := by
    have hh := normalized_density_bound A 0 J (s i) 0 (K*D) (hs i) (d i)
      (by simpa using hp i)
    simpa [heightScale,e] using hh
  have hh := row_density_energy (fun i=>(e i • d i:𝓢(ℝ,ℂ))) φ (envelope (K*D) J)
    (fun v=>(1+‖v‖)^J) (envelope_pos (K*D) (mul_pos hK hD) J)
    (by intro v;positivity) hpoint hint (envelope_integrable (K*D) J) E hE henergy
  rw [envelope_integral] at hh
  simp_rw [←hsource] at hh
  convert hh using 1
  ring

lemma inverse_annular_frequency (χ : Character) (V : ℝ→ℂ)
    (hreal : ∀y,conj (V y)=V y) (X v : ℝ) (hX : 0< X) :
    HeckeDyadic.polynomial χ.inverse false (logWindow V) X 0 (2*Real.pi*v)=
      conj (HeckeDyadic.polynomial χ false (logWindow V) X 0 (-2*Real.pi*v)) := by
  have hr (x : ℝ) : conj (logWindow V x)=logWindow V x := by
    unfold logWindow
    split_ifs <;> simp [hreal]
  have ht : (fun x=> conj (CompletedHeight.normTwistedSource (logWindow V) v x))=
      CompletedHeight.normTwistedSource (logWindow V) (-v) := by
    funext x
    simp only [CompletedHeight.normTwistedSource,map_mul,hr]
    exact congrArg (fun z=> z*logWindow V x) (JointLogSeparation.kernelLogPhase_conjugate v _)
  rw [CenteredMomentTwistedReflection.polynomial_twisted_source χ.inverse _ X v hX,
    polynomial_inverse_plain χ _ X hX,ht,
    ←CenteredMomentTwistedReflection.polynomial_twisted_source χ _ X (-v) hX]
  congr 2
  ring

theorem actual_inverse_uniform (V : ℝ→ℂ) (M : ℝ) (hM : 0≤ M)
    (hV : ∀y,V y≠0 → |y|≤ M) (hreal : ∀y,conj (V y)=V y) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀{ι : Type} [Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)(s X : ι→ℝ),
      (∀i,0< s i) → (∀i,0< X i) → ∀D E : ℝ,0< D → 0≤ E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤ D) →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (-2*Real.pi*v)*P i‖^2)
        ≤ E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i).inverse false
        (fun x=> logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
          (X i) 0 0*P i‖^2)≤ C*D^2*E := by
  obtain ⟨H,C,hC,hbound⟩ := actual_one_uniform V M hM hV A J
  refine ⟨H,C,hC,?_⟩
  intro ι _ G χ P s X hs hX D E hD hE hGD henergy
  apply hbound G (fun i=>(χ i).inverse) P s X hs hX D E hD hE hGD
  intro v
  have he (i : ι) :
      ‖HeckeDyadic.polynomial (χ i).inverse false (logWindow V) (X i) 0 (2*Real.pi*v)*P i‖=
      ‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (-2*Real.pi*v)*P i‖ := by
    rw [inverse_annular_frequency (χ i) V hreal (X i) v (hX i),norm_mul,
      Complex.norm_conj,←norm_mul]
  simpa only [he] using henergy v

lemma paperRadialFourier_real_smul (c : ℝ) (G : 𝓢(ℝ,ℂ)) (x : ℝ) :
    paperRadialFourier (c • G : 𝓢(ℝ,ℂ)) x=(c:ℂ)*paperRadialFourier G x := by
  rw [paperRadialFourier_eq_ray,paperRadialFourier_eq_ray]
  simp only [map_smul,smul_apply,Complex.real_smul]

lemma polynomial_const_mul (χ : Character) (W : ℝ→ℂ) (X σ omega : ℝ) (c : ℂ) :
    HeckeDyadic.polynomial χ false (fun x=> c*W x) X σ omega=
      c*HeckeDyadic.polynomial χ false W X σ omega := by
  unfold HeckeDyadic.polynomial
  have he : (fun I : HeckeDyadic.NonzeroIdeal=>
      HeckeDyadic.summand χ false (fun x=> c*W x) X σ omega I)=
      (fun I=> c*HeckeDyadic.summand χ false W X σ omega I) := by
    funext I
    unfold HeckeDyadic.summand
    ring
  rw [he,tsum_mul_left]
  ring

lemma reflected_polynomial_real_smul (χ : Character) (V : ℝ→ℂ)
    (G : 𝓢(ℝ,ℂ)) (s X c : ℝ) (A : ℕ) :
    HeckeDyadic.polynomial χ false
      (fun x=> logWindow V x*((1+s)^A:ℂ)*paperRadialFourier (c • G : 𝓢(ℝ,ℂ)) (s*x)) X 0 0=
      (c:ℂ)*HeckeDyadic.polynomial χ false
        (fun x=> logWindow V x*((1+s)^A:ℂ)*paperRadialFourier G (s*x)) X 0 0 := by
  simp_rw [paperRadialFourier_real_smul]
  have he : (fun x=> logWindow V x*((1+s)^A:ℂ)*((c:ℂ)*paperRadialFourier G (s*x)))=
      (fun x=>(c:ℂ)*(logWindow V x*((1+s)^A:ℂ)*paperRadialFourier G (s*x))) := by
    funext x
    ring
  rw [he,polynomial_const_mul]

theorem detector_source_control (H : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∃D : ℝ,0< D ∧ ∀reverse : Bool,∀k : ℕ,k≤2→
      ∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
      H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (((1+‖t‖)^n)⁻¹ • CenteredMomentDetectorDictionary.detectorSchwartz reverse k σ t)≤ D := by
  obtain ⟨n,D,hD,hb⟩ := CenteredMomentDetectorDictionary.detectorSchwartz_uniform H
  refine ⟨n,D,hD,?_⟩
  intro reverse k hk σ hσ t
  rw [map_smul_eq_mul,Real.norm_of_nonneg (by positivity : 0≤((1+‖t‖)^n)⁻¹)]
  exact (inv_mul_le_iff₀ (by positivity : 0<(1+‖t‖)^n)).mpr
    (by simpa only [mul_comm] using hb reverse k hk σ hσ t)

theorem detector_inverse_uniform (V : ℝ→ℂ) (M : ℝ) (hM : 0≤ M)
    (hV : ∀y,V y≠0 → |y|≤ M) (hreal : ∀y,conj (V y)=V y) (A J : ℕ) :
    ∃n : ℕ,∃C : ℝ,0< C ∧ ∀{ι : Type} [Fintype ι],
      ∀(reverse : ι→Bool)(k : ι→ℕ)(σ t : ι→ℝ),
      (∀i,k i≤2) → (∀i,σ i∈Set.Icc (0:ℝ) 1) →
      ∀(χ : ι→Character)(P : ι→ℂ)(s X : ι→ℝ),
      (∀i,0< s i) → (∀i,0< X i) → ∀E : ℝ,0≤ E →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (-2*Real.pi*v)*
        (((1+‖t i‖)^n:ℝ):ℂ)*P i‖^2)≤ E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i).inverse false
        (fun x=> logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier
          (CenteredMomentDetectorDictionary.detectorSchwartz (reverse i) (k i) (σ i) (t i)) (s i*x))
        (X i) 0 0*P i‖^2)≤ C*E := by
  obtain ⟨H,C,hC,hb⟩ := actual_inverse_uniform V M hM hV hreal A J
  obtain ⟨n,D,hD,hcontrol⟩ := detector_source_control H
  refine ⟨n,C*D^2,by positivity,?_⟩
  intro ι _ reverse k σ t hk hσ χ P s X hs hX E hE henergy
  let G (i : ι) := CenteredMomentDetectorDictionary.detectorSchwartz (reverse i) (k i) (σ i) (t i)
  let w (i : ι) : ℝ := (1+‖t i‖)^n
  have hw (i : ι) : 0< w i := by dsimp [w];positivity
  have hh := hb (fun i=>(w i)⁻¹ • G i) χ (fun i=>(w i:ℂ)*P i) s X hs hX D E hD hE
    (fun i=> hcontrol (reverse i) (k i) (hk i) (σ i) (hσ i) (t i))
    (by intro v;simpa only [w,mul_assoc] using henergy v)
  have he (i : ι) : HeckeDyadic.polynomial (χ i).inverse false
      (fun x=> logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier ((w i)⁻¹ • G i : 𝓢(ℝ,ℂ)) (s i*x))
      (X i) 0 0*((w i:ℂ)*P i)=
      HeckeDyadic.polynomial (χ i).inverse false
      (fun x=> logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x)) (X i) 0 0*P i := by
    rw [reflected_polynomial_real_smul,Complex.ofReal_inv]
    have hne : (w i:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hw i).ne'
    rw [mul_mul_mul_comm,inv_mul_cancel₀ hne,one_mul]
  simp_rw [he] at hh
  simpa only [G] using hh

end CenteredMomentUniformReflectionProfile

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace CenteredMomentUniformReflectionScale
open HeckeFamily HeckeDyadic SchwartzPlanePoisson
open CenteredMomentSectorLocalization CenteredMomentScaleSupremum
open CenteredMomentOneReflectionScaleEnergy CenteredMomentUniformReflectionProfile
open CenteredMomentReflectedNormalization

theorem actual_rowwise_scales (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀{ι : Type}[Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)
      (s lx ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high D E : ℝ),
      0≤ d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤ hi → low≤ high → (∀i,lx i∈Set.Icc lo hi) → (∀i,ly i∈Set.Icc low high) →
      (∀i,0< s i) → 0< D → 0≤ E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤ D) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤ E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i).inverse false
        (fun x=>(annulus x:ℂ)*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
        (Real.exp (lx i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  have hlog : 0≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hwindow : ∀y,CenteredMomentReflectedAnnuli.logWindow y≠0 → |y|≤ Real.log 4 := by
    intro y hy
    have hh := CenteredMomentReflectedAnnuli.logWindow_support hy
    exact abs_le.mpr ⟨hh.1,hh.2.trans hlog⟩
  have hreal : ∀y,conj (CenteredMomentReflectedAnnuli.logWindow y)=
      CenteredMomentReflectedAnnuli.logWindow y := by
    intro y
    exact Complex.conj_ofReal _
  obtain ⟨H,C,hC,hbound⟩:=actual_inverse_uniform
    CenteredMomentReflectedAnnuli.logWindow (Real.log 4) hlog hwindow hreal A J
  refine ⟨H,C,hC,?_⟩
  intro ι _ G χ P s lx ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hlx hly hspos hD hE hGD henergy
  have hdx : 0≤1+2*(hi-lo) := by linarith
  have hdy : 0≤1+2*(high-low) := by linarith
  have hfixed (v : ℝ) :
      (∑i,‖polynomial (χ i) false
        (CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow)
        (Real.exp (lx i)) 0 (-2*Real.pi*v)*
        (polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i)‖^2)≤
      ((1+2*(hi-lo))*((1+2*(high-low))*E))*((1+‖v‖)^J)^2 := by
    have hh := CenteredMomentFrequencyScaleSupremum.paired_rowwise_scales Finset.univ
      χ χ (fun _=>-2*Real.pi*v) omega P (fun z : ℝ=>(annulus z:ℂ)) Wshort
      (1/4) 1 c d (by norm_num) hd annulus_complex_support hshort annulus_complex_smooth hshortsmooth
      lo hi low high (E*(1+‖v‖)^(2*J)) hlh hlw lx ly
      (fun i _=> hlx i) (fun i _=> hly i) (henergy v)
    rw [actual_log_window]
    simp only [←mul_assoc]
    have hp : ((1+‖v‖)^J)^2=(1+‖v‖)^(2*J) := by rw [←pow_mul,Nat.mul_comm J 2]
    apply hh.trans_eq
    rw [hp]
    ring
  have hh:=hbound G χ (fun i=> polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i)
    s (fun i=> Real.exp (lx i)) hspos (fun i=> Real.exp_pos _) D
    ((1+2*(hi-lo))*((1+2*(high-low))*E)) hD (mul_nonneg hdx (mul_nonneg hdy hE)) hGD hfixed
  simp only [actual_log_window,←mul_assoc] at hh
  convert hh using 1

end CenteredMomentUniformReflectionScale

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace CenteredMomentUniformReflectionChoices
open HeckeFamily HeckeDyadic SchwartzPlanePoisson
open CenteredMomentSectorLocalization CenteredMomentScaleSupremum
open CenteredMomentUniformReflectionScale

theorem actual_independent_choices (B J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀{ι : Type}[Fintype ι],∀{α : ι→Type},
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)(s X : ∀i,α i→ℝ)(keep : ∀i,α i→Prop)
        (ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high D E : ℝ),
      0≤ d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤ hi → low≤ high → (∀i,ly i∈Set.Icc low high) →
      (∀i u,0< s i u) → (∀i u,keep i u → 0< X i u ∧ Real.log (X i u)∈Set.Icc lo hi) → 0< D → 0≤ E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤ D) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤ E*(1+‖v‖)^(2*J)) →
      ∀u : ∀i,α i,
      (∑i,‖if keep i (u i) then polynomial (χ i).inverse false
        (fun x=>(annulus x:ℂ)*((1+s i (u i))^B:ℂ)*paperRadialFourier (G i) (s i (u i)*x))
        (X i (u i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i else 0‖^2)≤
        C*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨H,C,hC,hb⟩ := actual_rowwise_scales B J
  refine ⟨H,C,hC,?_⟩
  intro ι _ α G χ P s X keep ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hly hspos hgeom hD hE hGD henergy u
  let lx (i : ι) := if keep i (u i) then Real.log (X i (u i)) else lo
  let P' (i : ι) := if keep i (u i) then P i else 0
  have hlx (i : ι) : lx i∈Set.Icc lo hi := by
    dsimp [lx]
    split_ifs with hk
    · exact (hgeom i (u i) hk).2
    · exact ⟨le_rfl,hlh⟩
  have he (v : ℝ) (j k : Fin 2) (x : ℝ) (hx : x∈Set.Icc lo hi)
      (y : ℝ) (hy : y∈Set.Icc low high) :
      (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
        (Real.exp x) 0 (-2*Real.pi*v)*
        polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P' i‖^2)
        ≤ E*(1+‖v‖)^(2*J) := by
    apply (Finset.sum_le_sum (fun i _=>?_)).trans (henergy v j k x hx y hy)
    dsimp only [P']
    split_ifs
    · exact le_rfl
    · simp only [mul_zero,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
      exact sq_nonneg _
  have hh := hb G χ P' (fun i=> s i (u i)) lx ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hlx hly (fun i=> hspos i (u i)) hD hE hGD he
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [lx,P']
  split_ifs with hk
  · rw [Real.exp_log (hgeom i (u i) hk).1]
  · simp

end CenteredMomentUniformReflectionChoices

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
