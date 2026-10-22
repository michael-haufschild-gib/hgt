import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualRamifiedPrimeSupport
import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualTwoAdicTateEpsilon
import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualFiveTateEpsilon
import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualFortyOneDualTateEpsilon
import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualTotallyReal
import GaloisForLFunctions.RHTower.Deninger.DeningerQ8FroehlichTheoremSixApplicability

/-!
# Global Artin epsilon assembly for the literal Q8 field

This file gives the specialized global root-number definition for the literal
two-dimensional Q8 Artin representation.  It multiplies analytic Tate epsilon
pairs on the actual source and inverse channels.  The finite support is proved
to be contained in `{2, 5, 41}`.  At two, the pair is independent of the
unramified radial lift; at five and forty-one, the decomposition group equals
inertia and the concrete quartic residue channels compute the factors.  Total
realness supplies the unit archimedean factor.

Thus the final `-1` is derived from independently defined local analytic
factors.  Fröhlich's finite residue sign is only identified afterwards.
-/

namespace RHTower

open scoped BigOperators NumberField

noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField
local notation "S" => q8BiquadQuadraticSourceField

local instance q8GlobalEpsilonCharZeroK3 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
noncomputable local instance q8GlobalEpsilonFiniteDimensionalRatK1 :
    FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance q8GlobalEpsilonFiniteDimensionalK1K2 :
    FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance q8GlobalEpsilonFiniteDimensionalRatK2 :
    FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance q8GlobalEpsilonFiniteDimensionalK2K3 :
    FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance q8GlobalEpsilonFiniteDimensionalRatK3 :
    FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance q8GlobalEpsilonNumberFieldK3 : NumberField K3 :=
  NumberField.mk
local instance q8GlobalEpsilonFactPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance q8GlobalEpsilonFactPrimeFortyOne : Fact (Nat.Prime 41) := ⟨by norm_num⟩

/-- Canonical dyadic source-channel epsilon pair. -/
noncomputable def deningerQ8ActualTwoArtinLocalEpsilon : ℂ :=
  GaloisForLFunctions.RHTower.fieldOnePadicRamifiedTatePhase 2 3
      GaloisForLFunctions.RHTower.q8TwoAdicEvenPrimitiveTateCharacter 1 *
    GaloisForLFunctions.RHTower.fieldOnePadicRamifiedTatePhase 2 3
      (GaloisForLFunctions.RHTower.fieldOnePadicPrimitiveAngularCharacterInv 2 3
        GaloisForLFunctions.RHTower.q8TwoAdicEvenPrimitiveTateCharacter) 1

theorem deningerQ8ActualTwoArtinLocalEpsilon_eq_one :
    deningerQ8ActualTwoArtinLocalEpsilon = 1 := by
  simpa [deningerQ8ActualTwoArtinLocalEpsilon] using
    (GaloisForLFunctions.RHTower.q8TwoAdicEvenTatePhase_pair_eq_one 1)

/-- Every unramified radial lift of the actual dyadic angular source gives
the same two-channel local factor. -/
theorem deningerQ8ActualTwoArtinLocalEpsilon_eq_radialPair (ρ : Circle) :
    deningerQ8ActualTwoArtinLocalEpsilon =
      GaloisForLFunctions.RHTower.fieldOnePadicRamifiedTatePhase 2 3
          GaloisForLFunctions.RHTower.q8TwoAdicEvenPrimitiveTateCharacter ρ *
        GaloisForLFunctions.RHTower.fieldOnePadicRamifiedTatePhase 2 3
          (GaloisForLFunctions.RHTower.fieldOnePadicPrimitiveAngularCharacterInv 2 3
            GaloisForLFunctions.RHTower.q8TwoAdicEvenPrimitiveTateCharacter) ρ⁻¹ := by
  rw [deningerQ8ActualTwoArtinLocalEpsilon_eq_one,
    GaloisForLFunctions.RHTower.q8TwoAdicEvenTatePhase_pair_eq_one]

/-- Every actual dyadic source place computes the same local factor. -/
theorem deningerQ8ActualTwoArtinLocalEpsilon_eq_sourcePair
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    deningerQ8ActualTwoArtinLocalEpsilon =
      q8ActualTwoLocalTateEpsilon v hv *
        q8ActualTwoInverseLocalTateEpsilon v hv := by
  rw [deningerQ8ActualTwoArtinLocalEpsilon_eq_one,
    q8ActualTwoLocalTateEpsilon_mul_inverse_eq_one]

/-- Exact conductor of the fixed coefficient-faithful residue source at five. -/
theorem deningerQ8FiveResidueQuarticChar_isPrimitive :
    DirichletCharacter.IsPrimitive
      (deningerQ8FiveResidueQuarticChar : DirichletCharacter ℂ 5) := by
  rw [DirichletCharacter.isPrimitive_def]
  have hdiv : DirichletCharacter.conductor
      (deningerQ8FiveResidueQuarticChar : DirichletCharacter ℂ 5) ∣ 5 :=
    DirichletCharacter.conductor_dvd_level
      (deningerQ8FiveResidueQuarticChar : DirichletCharacter ℂ 5)
  rcases (Nat.dvd_prime Nat.prime_five).mp hdiv with h | h
  · exact (deningerQ8FiveResidueQuarticChar_ne_one
      ((DirichletCharacter.eq_one_iff_conductor_eq_one
        (χ := (deningerQ8FiveResidueQuarticChar : DirichletCharacter ℂ 5))).mpr h)).elim
  · exact h

/-- Fixed source character at five, packaged at its exact Tate conductor. -/
noncomputable def deningerQ8FiveSourcePrimitiveTateCharacter :
    GaloisForLFunctions.RHTower.FieldOnePadicPrimitiveAngularCharacter 5 1 :=
  ⟨deningerQ8FiveResidueQuarticChar,
    by simpa using deningerQ8FiveResidueQuarticChar_isPrimitive⟩

/-- Canonical actual source factor at five, defined as a Tate epsilon pair. -/
noncomputable def deningerQ8ActualFiveArtinLocalEpsilon : ℂ :=
  GaloisForLFunctions.RHTower.fieldOnePadicRamifiedTatePhase 5 1
      deningerQ8FiveSourcePrimitiveTateCharacter 1 *
    GaloisForLFunctions.RHTower.fieldOnePadicRamifiedTatePhase 5 1
      (GaloisForLFunctions.RHTower.fieldOnePadicPrimitiveAngularCharacterInv 5 1
        deningerQ8FiveSourcePrimitiveTateCharacter) 1

theorem deningerQ8ActualFiveArtinLocalEpsilon_eq_froehlichGaussian :
    deningerQ8ActualFiveArtinLocalEpsilon =
      deningerQ8FroehlichSplitFiveSameAdditiveGaussianPair := by
  rw [deningerQ8ActualFiveArtinLocalEpsilon,
    GaloisForLFunctions.RHTower.fieldOnePadicFiveRamifiedTatePhase_mul_inverse_eq_gaussianPhase]
  rfl

theorem deningerQ8ActualFiveArtinLocalEpsilon_eq_neg_one :
    deningerQ8ActualFiveArtinLocalEpsilon = -1 := by
  rw [deningerQ8ActualFiveArtinLocalEpsilon_eq_froehlichGaussian,
    deningerQ8FroehlichSplitFiveSameAdditiveGaussianPair_eq_neg_one]

/-- Every source-compatible tame realization at five computes the canonical
local factor. -/
theorem deningerQ8ActualFiveArtinLocalEpsilon_eq_sourcePair
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)}))
    (W : ValuationSubring K3) (dvr : IsDiscreteValuationRing W)
    (finiteRes : Finite (IsLocalRing.ResidueField W))
    (π : W) (hπ : Irreducible π)
    (eI : P.inertia Gal(K3/ℚ) ≃* W.inertiaSubgroup ℚ)
    (hResidueCard : Nat.card (IsLocalRing.ResidueField W) = 5)
    (hRatioBij : Function.Bijective
      (GaloisForLFunctions.HTGeometry.residueRatioHom hπ
        (fun (g : W.inertiaSubgroup ℚ) (y : W) =>
          GaloisForLFunctions.HTGeometry.ValuationInertia.smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup
            W g.property y)).toHomUnits) :
    deningerQ8ActualFiveArtinLocalEpsilon =
      q8ActualFiveLocalTateEpsilon P hPover W dvr finiteRes π hπ eI
          hResidueCard hRatioBij *
        q8ActualFiveInverseLocalTateEpsilon P hPover W dvr finiteRes π hπ eI
          hResidueCard hRatioBij := by
  rw [deningerQ8ActualFiveArtinLocalEpsilon_eq_neg_one,
    q8ActualFiveLocalTateEpsilon_mul_inverse_eq_neg_one]

/-- Concrete quartic residue source obtained from the literal Q8 coefficient
character and the canonical cyclic quotient at forty-one. -/
noncomputable def deningerQ8FortyOneResidueQuarticChar : MulChar (ZMod 41) ℂ :=
  MulChar.ofUnitHom (q8OrderFourCharacter.comp zmodFortyOneQuarticQuotient)

theorem deningerQ8FortyOneResidueQuarticChar_orderOf :
    orderOf deningerQ8FortyOneResidueQuarticChar = 4 := by
  rw [deningerQ8FortyOneResidueQuarticChar, orderOf_mulChar_ofUnitHom]
  exact (orderOf_monoidHom_comp_of_surjective q8OrderFourCharacter
    zmodFortyOneQuarticQuotient zmodFortyOneQuarticQuotient_surjective).trans
      q8OrderFourCharacter_orderOf

theorem deningerQ8FortyOneResidueQuarticChar_isPrimitive :
    DirichletCharacter.IsPrimitive
      (deningerQ8FortyOneResidueQuarticChar : DirichletCharacter ℂ 41) :=
  zmodFortyOne_orderFourMulChar_isPrimitive
    deningerQ8FortyOneResidueQuarticChar
    deningerQ8FortyOneResidueQuarticChar_orderOf

noncomputable def deningerQ8FortyOneSourcePrimitiveTateCharacter :
    GaloisForLFunctions.RHTower.FieldOnePadicPrimitiveAngularCharacter 41 1 :=
  ⟨deningerQ8FortyOneResidueQuarticChar,
    by simpa using deningerQ8FortyOneResidueQuarticChar_isPrimitive⟩

/-- Canonical actual source factor at forty-one, defined as a Tate epsilon pair. -/
noncomputable def deningerQ8ActualFortyOneArtinLocalEpsilon : ℂ :=
  GaloisForLFunctions.RHTower.fieldOnePadicRamifiedTatePhase 41 1
      deningerQ8FortyOneSourcePrimitiveTateCharacter 1 *
    GaloisForLFunctions.RHTower.fieldOnePadicRamifiedTatePhase 41 1
      (GaloisForLFunctions.RHTower.fieldOnePadicPrimitiveAngularCharacterInv 41 1
        deningerQ8FortyOneSourcePrimitiveTateCharacter) 1

theorem deningerQ8ActualFortyOneArtinLocalEpsilon_eq_one :
    deningerQ8ActualFortyOneArtinLocalEpsilon = 1 := by
  simpa [deningerQ8ActualFortyOneArtinLocalEpsilon,
    deningerQ8FortyOneSourcePrimitiveTateCharacter,
    zmodFortyOneQuarticTateCharacter] using
      (fieldOnePadicFortyOneQuarticTatePhasePair_eq_one
        deningerQ8FortyOneResidueQuarticChar
        deningerQ8FortyOneResidueQuarticChar_orderOf)

/-- Every prime above forty-one computes the canonical local factor on the
literal source and inverse Artin channels. -/
theorem deningerQ8ActualFortyOneArtinLocalEpsilon_eq_sourcePair
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    deningerQ8ActualFortyOneArtinLocalEpsilon =
      q8ActualFortyOneLocalTateEpsilon P hPover *
        q8ActualFortyOneInverseLocalTateEpsilon P hPover := by
  rw [deningerQ8ActualFortyOneArtinLocalEpsilon_eq_one,
    q8ActualFortyOneLocalTateEpsilon_mul_inverse_eq_one]

/-- Local epsilon function, normalized to one away from the proved ramified support. -/
noncomputable def deningerQ8ActualArtinLocalEpsilon (p : ℕ) : ℂ :=
  if p = 2 then deningerQ8ActualTwoArtinLocalEpsilon
  else if p = 5 then deningerQ8ActualFiveArtinLocalEpsilon
  else if p = 41 then deningerQ8ActualFortyOneArtinLocalEpsilon
  else 1

def deningerQ8ActualRamifiedPrimeSupport : Finset ℕ := {2, 5, 41}

/-- Finite-place epsilon product over the exact possible ramified support. -/
noncomputable def deningerQ8ActualFiniteArtinEpsilon : ℂ :=
  ∏ p ∈ deningerQ8ActualRamifiedPrimeSupport,
    deningerQ8ActualArtinLocalEpsilon p

/-- Totally-real archimedean epsilon of the even two-dimensional representation. -/
def deningerQ8ActualArchimedeanArtinEpsilon : ℂ := 1

/-- Independently assembled global Artin epsilon product. -/
noncomputable def deningerQ8ActualGlobalArtinEpsilon : ℂ :=
  deningerQ8ActualArchimedeanArtinEpsilon * deningerQ8ActualFiniteArtinEpsilon

/-- Root number of the literal Q8 Artin representation: its specialized
global epsilon product. -/
noncomputable def deningerQ8ActualArtinRootNumber : ℂ :=
  deningerQ8ActualGlobalArtinEpsilon

theorem deningerQ8ActualArtinLocalEpsilon_eq_one_of_not_mem
    (p : ℕ) (hp : p ∉ deningerQ8ActualRamifiedPrimeSupport) :
    deningerQ8ActualArtinLocalEpsilon p = 1 := by
  simp only [deningerQ8ActualRamifiedPrimeSupport, Finset.mem_insert,
    Finset.mem_singleton, not_or] at hp
  simp [deningerQ8ActualArtinLocalEpsilon, hp.1, hp.2.1, hp.2.2]

theorem deningerQ8ActualFiniteArtinEpsilon_eq_neg_one :
    deningerQ8ActualFiniteArtinEpsilon = -1 := by
  simp [deningerQ8ActualFiniteArtinEpsilon, deningerQ8ActualRamifiedPrimeSupport,
    deningerQ8ActualArtinLocalEpsilon,
    deningerQ8ActualTwoArtinLocalEpsilon_eq_one,
    deningerQ8ActualFiveArtinLocalEpsilon_eq_neg_one,
    deningerQ8ActualFortyOneArtinLocalEpsilon_eq_one]

theorem deningerQ8ActualGlobalArtinEpsilon_eq_neg_one :
    deningerQ8ActualGlobalArtinEpsilon = -1 := by
  rw [deningerQ8ActualGlobalArtinEpsilon,
    deningerQ8ActualArchimedeanArtinEpsilon,
    deningerQ8ActualFiniteArtinEpsilon_eq_neg_one]
  norm_num

theorem deningerQ8ActualArtinRootNumber_eq_neg_one :
    deningerQ8ActualArtinRootNumber = -1 := by
  exact deningerQ8ActualGlobalArtinEpsilon_eq_neg_one

theorem norm_deningerQ8ActualArtinRootNumber :
    ‖deningerQ8ActualArtinRootNumber‖ = 1 := by
  rw [deningerQ8ActualArtinRootNumber_eq_neg_one]
  norm_num

theorem deningerQ8ActualGlobalArtinEpsilon_eq_froehlichFiniteSign :
    deningerQ8ActualGlobalArtinEpsilon = deningerQ8FroehlichFiniteSign := by
  rw [deningerQ8ActualGlobalArtinEpsilon_eq_neg_one,
    deningerQ8FroehlichFiniteSign_eq_neg_one]
  norm_num

theorem deningerQ8ActualGlobalArtinEpsilon_support :
    ∀ (p : ℕ), p.Prime → ∀ (P : Ideal (𝓞 K3)), [P.IsPrime] →
      P.LiesOver (Ideal.span {(p : ℤ)}) →
      ¬ Algebra.IsUnramifiedAt ℤ P →
      p ∈ deningerQ8ActualRamifiedPrimeSupport := by
  intro p hp P hPPrime hPover hram
  letI : P.IsPrime := hPPrime
  rcases q8Literal_absolute_ramified_prime_support p hp P hPover hram with h2 | h5 | h41
  · simp [deningerQ8ActualRamifiedPrimeSupport, h2]
  · simp [deningerQ8ActualRamifiedPrimeSupport, h5]
  · simp [deningerQ8ActualRamifiedPrimeSupport, h41]

theorem deningerQ8ActualArchimedeanArtinEpsilon_source :
    NumberField.IsTotallyReal K3 ∧ deningerQ8ActualArchimedeanArtinEpsilon = 1 :=
  ⟨deningerQ8RootNumberNegOne_isTotallyReal, rfl⟩

end


end RHTower
