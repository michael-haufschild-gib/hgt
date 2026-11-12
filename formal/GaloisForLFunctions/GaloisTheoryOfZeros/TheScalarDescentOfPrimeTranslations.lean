import GaloisForLFunctions.GaloisTheoryOfZeros.TheCentralizerOfPrimeTranslations

/-!
# Scalar descent of prime translations

Every rational-algebra endomorphism commuting with the prime translations at
two and three is injective. Its unique coordinates are a scalar embedding
preserving the actual joint exponential spectrum and a character multiplying
the basis coefficients. The spectrum uniquely determines the injective additive
map on the full integer zero group.

Preserving the augmentation ideal removes exactly the character coordinate.
A scalar embedding extends to a unique pointed commuting endomorphism precisely
when it preserves the spectrum. For scalar automorphisms, the exact extension
condition is preservation in both directions. Fixing a ground subfield is
exactly fixing that field in the induced scalar action.

The proof uses joint eigenspaces, difference simplicity, and the universal maps
of the full group algebra. It makes no continuity, independence, or algebraicity
assumption on the actual zeros. The arithmetic spectral stabilizer is not
determined by these extension criteria.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- Rational-algebra commutation leaves the scalar action free. -/
def RationalCommutesWithPrimeTranslations
    (F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra) : Prop :=
  (∀ f, F (zeroMotivePrimeTranslation 2 f) = zeroMotivePrimeTranslation 2 (F f)) ∧
  (∀ f, F (zeroMotivePrimeTranslation 3 f) = zeroMotivePrimeTranslation 3 (F f))

/-- The identity point is specified by its augmentation ideal. -/
def RationalPreservesZeroMotiveIdentity
    (F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra) : Prop :=
  ∀ f, zeroMotiveEvaluation 0 f = 0 → zeroMotiveEvaluation 0 (F f) = 0

/-- The induced scalar action, read by augmentation. -/
def zeroMotiveRationalScalarAction
    (F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra) : ℂ →ₐ[ℚ] ℂ :=
  ((zeroMotiveEvaluation 0).restrictScalars ℚ).comp (F.comp AddMonoidAlgebra.singleZeroAlgHom)

private theorem rationalZeroAlgHom_ext {B : Type*} [Semiring B] [Algebra ℚ B]
    {F G : ZeroMotiveAlgebra →ₐ[ℚ] B}
    (h : ∀ z : rawZeroRelationGroup, ∀ a : ℂ,
      F (AddMonoidAlgebra.single z a) = G (AddMonoidAlgebra.single z a)) : F = G := by
  apply AddMonoidAlgebra.algHom_ext
  · intro z
    exact h z 1
  · apply AlgHom.ext
    intro a
    exact h 0 a

private theorem primeEigenvalue_zero (p : ℕ) : zeroPrimeEigenvalue p 0 = 1 := by
  change Complex.exp ((Real.log p : ℂ)*0) = 1
  rw [mul_zero,Complex.exp_zero]

private theorem primeEigenvalue_add (p : ℕ) (z w : rawZeroRelationGroup) :
    zeroPrimeEigenvalue p (z+w) = zeroPrimeEigenvalue p z*zeroPrimeEigenvalue p w := by
  change Complex.exp ((Real.log p : ℂ)*((z : ℂ)+(w : ℂ))) = _
  rw [mul_add,Complex.exp_add]
  rfl

private theorem primeTranslation_constant (p : ℕ) (a : ℂ) :
    zeroMotivePrimeTranslation p (AddMonoidAlgebra.single 0 a) = AddMonoidAlgebra.single 0 a := by
  rw [zeroMotivePrimeTranslation,zeroMotiveTranslation_single,map_zero (rawZeroMotiveFlow (Real.log p))]
  change AddMonoidAlgebra.single (0 : rawZeroRelationGroup) (a*1) = AddMonoidAlgebra.single 0 a
  rw [mul_one]

/-- Two-prime commutation alone forces preservation of the coefficient field. -/
theorem rationalPrimeCommutant_constant
    (F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalCommutesWithPrimeTranslations F) (a : ℂ) :
    F (AddMonoidAlgebra.single 0 a) =
      AddMonoidAlgebra.single 0 (zeroMotiveRationalScalarAction F a) := by
  have h₂ : zeroMotivePrimeTranslation 2 (F (AddMonoidAlgebra.single 0 a)) =
      zeroPrimeEigenvalue 2 0 • F (AddMonoidAlgebra.single 0 a) := by
    rw [primeEigenvalue_zero,one_smul]
    exact (hF.1 _).symm.trans (congrArg F (primeTranslation_constant 2 a))
  have h₃ : zeroMotivePrimeTranslation 3 (F (AddMonoidAlgebra.single 0 a)) =
      zeroPrimeEigenvalue 3 0 • F (AddMonoidAlgebra.single 0 a) := by
    rw [primeEigenvalue_zero,one_smul]
    exact (hF.2 _).symm.trans (congrArg F (primeTranslation_constant 3 a))
  have he := zeroMotive_joint_eigenvector 0 (F (AddMonoidAlgebra.single 0 a)) h₂ h₃
  have ha : zeroMotiveRationalScalarAction F a = (F (AddMonoidAlgebra.single 0 a)).coeff 0 := by
    change zeroMotiveEvaluation 0 (F (AddMonoidAlgebra.single 0 a)) = _
    conv_lhs => rw [he]
    rw [zeroMotiveEvaluation_single,zero_mul,Complex.exp_zero,mul_one]
  rw [ha]
  exact he

/-- Commuting maps are semilinear for their induced scalar embedding. -/
theorem rationalPrimeCommutant_smul
    (F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalCommutesWithPrimeTranslations F) (a : ℂ) (f : ZeroMotiveAlgebra) :
    F (a • f) = zeroMotiveRationalScalarAction F a • F f := by
  rw [Algebra.smul_def,map_mul,Algebra.smul_def]
  change F (AddMonoidAlgebra.single 0 a)*F f = _
  rw [rationalPrimeCommutant_constant F hF]
  rfl

/-- The joint spectrum of the full integer zero group. -/
def primeZeroSpectrum : Set (ℂ × ℂ) :=
  Set.range fun z : rawZeroRelationGroup => (zeroPrimeEigenvalue 2 z,zeroPrimeEigenvalue 3 z)

/-- Spectral preservation is an explicit condition on the scalar embedding. -/
def PreservesPrimeZeroSpectrum (σ : ℂ →ₐ[ℚ] ℂ) : Prop :=
  ∀ z : rawZeroRelationGroup, ∃ w : rawZeroRelationGroup,
    zeroPrimeEigenvalue 2 w = σ (zeroPrimeEigenvalue 2 z) ∧
    zeroPrimeEigenvalue 3 w = σ (zeroPrimeEigenvalue 3 z)

/-- The exponent selected by a scalar embedding preserving the joint spectrum. -/
def primeSpectrumExponent (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ)
    (z : rawZeroRelationGroup) : rawZeroRelationGroup := (hσ z).choose

theorem primeSpectrumExponent_pair (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ)
    (z : rawZeroRelationGroup) :
    zeroPrimeEigenvalue 2 (primeSpectrumExponent σ hσ z) = σ (zeroPrimeEigenvalue 2 z) ∧
    zeroPrimeEigenvalue 3 (primeSpectrumExponent σ hσ z) = σ (zeroPrimeEigenvalue 3 z) :=
  (hσ z).choose_spec

/-- Multiplication in the joint spectrum recovers the entire additive zero group. -/
def primeSpectrumExponentHom (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ) :
    rawZeroRelationGroup →+ rawZeroRelationGroup where
  toFun := primeSpectrumExponent σ hσ
  map_zero' := by
    apply zeroPrimeEigenvalue_pair_injective
    apply Prod.ext
    · change zeroPrimeEigenvalue 2 (primeSpectrumExponent σ hσ 0) = zeroPrimeEigenvalue 2 0
      simp only [(primeSpectrumExponent_pair σ hσ 0).1,primeEigenvalue_zero,map_one]
    · change zeroPrimeEigenvalue 3 (primeSpectrumExponent σ hσ 0) = zeroPrimeEigenvalue 3 0
      simp only [(primeSpectrumExponent_pair σ hσ 0).2,primeEigenvalue_zero,map_one]
  map_add' z w := by
    apply zeroPrimeEigenvalue_pair_injective
    apply Prod.ext
    · change zeroPrimeEigenvalue 2 (primeSpectrumExponent σ hσ (z+w)) =
        zeroPrimeEigenvalue 2 (primeSpectrumExponent σ hσ z+primeSpectrumExponent σ hσ w)
      rw [(primeSpectrumExponent_pair σ hσ (z+w)).1,primeEigenvalue_add,primeEigenvalue_add,
        map_mul,(primeSpectrumExponent_pair σ hσ z).1,(primeSpectrumExponent_pair σ hσ w).1]
    · change zeroPrimeEigenvalue 3 (primeSpectrumExponent σ hσ (z+w)) =
        zeroPrimeEigenvalue 3 (primeSpectrumExponent σ hσ z+primeSpectrumExponent σ hσ w)
      rw [(primeSpectrumExponent_pair σ hσ (z+w)).2,primeEigenvalue_add,primeEigenvalue_add,
        map_mul,(primeSpectrumExponent_pair σ hσ z).2,(primeSpectrumExponent_pair σ hσ w).2]

/-- No exponent is lost under a spectrally preserving scalar embedding. -/
theorem primeSpectrumExponentHom_injective
    (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ) :
    Function.Injective (primeSpectrumExponentHom σ hσ) := by
  intro z w h
  apply zeroPrimeEigenvalue_pair_injective
  apply Prod.ext
  · apply σ.injective
    change σ (zeroPrimeEigenvalue 2 z) = σ (zeroPrimeEigenvalue 2 w)
    rw [← (primeSpectrumExponent_pair σ hσ z).1,← (primeSpectrumExponent_pair σ hσ w).1]
    exact congrArg (zeroPrimeEigenvalue 2) h
  · apply σ.injective
    change σ (zeroPrimeEigenvalue 3 z) = σ (zeroPrimeEigenvalue 3 w)
    rw [← (primeSpectrumExponent_pair σ hσ z).2,← (primeSpectrumExponent_pair σ hσ w).2]
    exact congrArg (zeroPrimeEigenvalue 3) h

/-- A nonzero joint eigenvector selects an actual exponent, with no prescribed eigenvalue. -/
private theorem nonzero_joint_eigenvector_spectrum (f : ZeroMotiveAlgebra) (hf : f ≠ 0)
    (a b : ℂ)
    (h₂ : zeroMotivePrimeTranslation 2 f = a • f)
    (h₃ : zeroMotivePrimeTranslation 3 f = b • f) :
    ∃ w : rawZeroRelationGroup, zeroPrimeEigenvalue 2 w = a ∧
      zeroPrimeEigenvalue 3 w = b ∧ f = AddMonoidAlgebra.single w (f.coeff w) := by
  have hex : ∃ w : rawZeroRelationGroup, f.coeff w ≠ 0 := by
    by_contra! h
    apply hf
    apply AddMonoidAlgebra.coeff_injective
    exact Finsupp.ext h
  obtain ⟨w,hw⟩ := hex
  have he₂ := congrArg (fun g : ZeroMotiveAlgebra => g.coeff w) h₂
  have he₃ := congrArg (fun g : ZeroMotiveAlgebra => g.coeff w) h₃
  rw [zeroMotivePrimeTranslation_coeff] at he₂ he₃
  change zeroPrimeEigenvalue 2 w*f.coeff w = a*f.coeff w at he₂
  change zeroPrimeEigenvalue 3 w*f.coeff w = b*f.coeff w at he₃
  have ha := mul_right_cancel₀ hw he₂
  have hb := mul_right_cancel₀ hw he₃
  refine ⟨w,ha,hb,zeroMotive_joint_eigenvector w f ?_ ?_⟩
  · rwa [ha]
  · rwa [hb]

private theorem rationalPointed_basis_evaluation
    (F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalPreservesZeroMotiveIdentity F) (z : rawZeroRelationGroup) :
    zeroMotiveEvaluation 0 (F (AddMonoidAlgebra.single z 1)) = 1 := by
  have hz : zeroMotiveEvaluation 0 (AddMonoidAlgebra.single z 1-1) = 0 := by
    rw [map_sub,zeroMotiveEvaluation_single,zero_mul,Complex.exp_zero,one_mul,map_one,sub_self]
  have he := hF _ hz
  rw [map_sub,map_one,map_sub,map_one] at he
  exact sub_eq_zero.mp he

/-- A pointed prime-compatible map sends each character to a uniquely selected character. -/
theorem rationalPointedPrime_basis
    (F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalCommutesWithPrimeTranslations F)
    (hpoint : RationalPreservesZeroMotiveIdentity F) (z : rawZeroRelationGroup) :
    ∃ w : rawZeroRelationGroup,
      zeroPrimeEigenvalue 2 w = zeroMotiveRationalScalarAction F (zeroPrimeEigenvalue 2 z) ∧
      zeroPrimeEigenvalue 3 w = zeroMotiveRationalScalarAction F (zeroPrimeEigenvalue 3 z) ∧
      F (AddMonoidAlgebra.single z 1) = AddMonoidAlgebra.single w 1 := by
  have heval := rationalPointed_basis_evaluation F hpoint z
  have hn : F (AddMonoidAlgebra.single z 1) ≠ 0 := by
    intro he
    rw [he,map_zero] at heval
    exact zero_ne_one heval
  have h₂ : zeroMotivePrimeTranslation 2 (F (AddMonoidAlgebra.single z 1)) =
      zeroMotiveRationalScalarAction F (zeroPrimeEigenvalue 2 z) •
        F (AddMonoidAlgebra.single z 1) := by
    rw [← hF.1,zeroMotivePrimeTranslation_basis,rationalPrimeCommutant_smul F hF]
  have h₃ : zeroMotivePrimeTranslation 3 (F (AddMonoidAlgebra.single z 1)) =
      zeroMotiveRationalScalarAction F (zeroPrimeEigenvalue 3 z) •
        F (AddMonoidAlgebra.single z 1) := by
    rw [← hF.2,zeroMotivePrimeTranslation_basis,rationalPrimeCommutant_smul F hF]
  obtain ⟨w,ha,hb,hw⟩ := nonzero_joint_eigenvector_spectrum _ hn _ _ h₂ h₃
  have hc := congrArg (zeroMotiveEvaluation 0) hw
  rw [heval,zeroMotiveEvaluation_single,zero_mul,Complex.exp_zero,mul_one] at hc
  exact ⟨w,ha,hb,by rw [hw,← hc]⟩

/-- Every pointed commuting map induces a scalar embedding preserving the actual joint spectrum. -/
theorem rationalPointedPrime_scalar_preserves_spectrum
    (F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalCommutesWithPrimeTranslations F)
    (hpoint : RationalPreservesZeroMotiveIdentity F) :
    PreservesPrimeZeroSpectrum (zeroMotiveRationalScalarAction F) := by
  intro z
  obtain ⟨w,ha,hb,_⟩ := rationalPointedPrime_basis F hF hpoint z
  exact ⟨w,ha,hb⟩

/-- The action on the coefficient field determines every pointed prime-compatible symmetry. -/
theorem rationalPointedPrime_scalar_faithful
    (F G : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalCommutesWithPrimeTranslations F)
    (hG : RationalCommutesWithPrimeTranslations G)
    (hpF : RationalPreservesZeroMotiveIdentity F)
    (hpG : RationalPreservesZeroMotiveIdentity G)
    (hσ : zeroMotiveRationalScalarAction F = zeroMotiveRationalScalarAction G) : F = G := by
  apply rationalZeroAlgHom_ext
  intro z a
  obtain ⟨w,hw₂,hw₃,hw⟩ := rationalPointedPrime_basis F hF hpF z
  obtain ⟨v,hv₂,hv₃,hv⟩ := rationalPointedPrime_basis G hG hpG z
  have hwv : w = v := by
    apply zeroPrimeEigenvalue_pair_injective
    exact Prod.ext ((hw₂.trans (DFunLike.congr_fun hσ _)).trans hv₂.symm)
      ((hw₃.trans (DFunLike.congr_fun hσ _)).trans hv₃.symm)
  have hs : AddMonoidAlgebra.single z a = a • AddMonoidAlgebra.single z 1 := by
    rw [AddMonoidAlgebra.smul_single,smul_eq_mul,mul_one]
  rw [hs,rationalPrimeCommutant_smul F hF,rationalPrimeCommutant_smul G hG,
    hw,hv,hwv,hσ]

/-- Lift a spectrum-preserving scalar embedding to the full zero algebra. -/
def zeroMotiveScalarLift (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ) :
    ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra :=
  (AddMonoidAlgebra.mapAlgHom rawZeroRelationGroup σ).comp
    (AddMonoidAlgebra.mapDomainAlgHom ℚ ℂ (primeSpectrumExponentHom σ hσ))

/-- The lift transforms coefficients and transports exponents through the joint spectrum. -/
theorem zeroMotiveScalarLift_single (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ)
    (z : rawZeroRelationGroup) (a : ℂ) :
    zeroMotiveScalarLift σ hσ (AddMonoidAlgebra.single z a) =
      AddMonoidAlgebra.single (primeSpectrumExponentHom σ hσ z) (σ a) := by
  simp only [zeroMotiveScalarLift,AlgHom.comp_apply,AddMonoidAlgebra.mapDomainAlgHom_apply,
    AddMonoidAlgebra.mapDomain_single,AddMonoidAlgebra.mapAlgHom_single]

private theorem primeTranslation_single (p : ℕ) (z : rawZeroRelationGroup) (a : ℂ) :
    zeroMotivePrimeTranslation p (AddMonoidAlgebra.single z a) =
      AddMonoidAlgebra.single z (a*zeroPrimeEigenvalue p z) := by
  rw [zeroMotivePrimeTranslation,zeroMotiveTranslation_single]
  rfl

private theorem zeroMotiveScalarLift_prime (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ)
    (p : ℕ) (hp : ∀ z, zeroPrimeEigenvalue p (primeSpectrumExponentHom σ hσ z) =
      σ (zeroPrimeEigenvalue p z)) (f : ZeroMotiveAlgebra) :
    zeroMotiveScalarLift σ hσ (zeroMotivePrimeTranslation p f) =
      zeroMotivePrimeTranslation p (zeroMotiveScalarLift σ hσ f) := by
  have he : (zeroMotiveScalarLift σ hσ).comp ((zeroMotivePrimeTranslation p).restrictScalars ℚ) =
      ((zeroMotivePrimeTranslation p).restrictScalars ℚ).comp (zeroMotiveScalarLift σ hσ) := by
    apply rationalZeroAlgHom_ext
    intro z a
    change zeroMotiveScalarLift σ hσ (zeroMotivePrimeTranslation p (AddMonoidAlgebra.single z a)) =
      zeroMotivePrimeTranslation p (zeroMotiveScalarLift σ hσ (AddMonoidAlgebra.single z a))
    rw [primeTranslation_single,zeroMotiveScalarLift_single,zeroMotiveScalarLift_single,
      primeTranslation_single,map_mul,hp]
  exact DFunLike.congr_fun he f

/-- Spectral preservation gives genuine commutation with both prime translations. -/
theorem zeroMotiveScalarLift_commutes (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ) :
    RationalCommutesWithPrimeTranslations (zeroMotiveScalarLift σ hσ) :=
  ⟨zeroMotiveScalarLift_prime σ hσ 2 (fun z => (primeSpectrumExponent_pair σ hσ z).1),
    zeroMotiveScalarLift_prime σ hσ 3 (fun z => (primeSpectrumExponent_pair σ hσ z).2)⟩

/-- Augmentation intertwines the lifted action with its scalar embedding. -/
theorem zeroMotiveScalarLift_augmentation (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ)
    (f : ZeroMotiveAlgebra) :
    zeroMotiveEvaluation 0 (zeroMotiveScalarLift σ hσ f) = σ (zeroMotiveEvaluation 0 f) := by
  have he : ((zeroMotiveEvaluation 0).restrictScalars ℚ).comp (zeroMotiveScalarLift σ hσ) =
      σ.comp ((zeroMotiveEvaluation 0).restrictScalars ℚ) := by
    apply rationalZeroAlgHom_ext
    intro z a
    change zeroMotiveEvaluation 0 (zeroMotiveScalarLift σ hσ (AddMonoidAlgebra.single z a)) =
      σ (zeroMotiveEvaluation 0 (AddMonoidAlgebra.single z a))
    rw [zeroMotiveScalarLift_single,zeroMotiveEvaluation_single,zeroMotiveEvaluation_single,
      zero_mul,zero_mul,Complex.exp_zero,mul_one,mul_one]
  exact DFunLike.congr_fun he f

/-- The canonical scalar lift preserves the identity ideal. -/
theorem zeroMotiveScalarLift_pointed (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ) :
    RationalPreservesZeroMotiveIdentity (zeroMotiveScalarLift σ hσ) := by
  intro f hf
  rw [zeroMotiveScalarLift_augmentation,hf,map_zero]

/-- Restriction to the constant field recovers the original scalar embedding. -/
theorem zeroMotiveScalarLift_scalar (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ) :
    zeroMotiveRationalScalarAction (zeroMotiveScalarLift σ hσ) = σ := by
  apply AlgHom.ext
  intro a
  change zeroMotiveEvaluation 0 (zeroMotiveScalarLift σ hσ (AddMonoidAlgebra.single 0 a)) = σ a
  rw [zeroMotiveScalarLift_single,zeroMotiveEvaluation_single,zero_mul,Complex.exp_zero,mul_one]

/-- Exact scalar extension criterion, with uniqueness on the full infinite coordinate algebra. -/
theorem primeSpectrum_scalar_extension_iff (σ : ℂ →ₐ[ℚ] ℂ) :
    PreservesPrimeZeroSpectrum σ ↔
      ∃! F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra,
        RationalCommutesWithPrimeTranslations F ∧ RationalPreservesZeroMotiveIdentity F ∧
          zeroMotiveRationalScalarAction F = σ := by
  constructor
  · intro hσ
    refine ⟨zeroMotiveScalarLift σ hσ,
      ⟨zeroMotiveScalarLift_commutes σ hσ,zeroMotiveScalarLift_pointed σ hσ,
        zeroMotiveScalarLift_scalar σ hσ⟩,?_⟩
    intro F hF
    exact rationalPointedPrime_scalar_faithful F _ hF.1 (zeroMotiveScalarLift_commutes σ hσ)
      hF.2.1 (zeroMotiveScalarLift_pointed σ hσ)
      (hF.2.2.trans (zeroMotiveScalarLift_scalar σ hσ).symm)
  · rintro ⟨F,⟨hF,hpoint,hscalar⟩,_⟩
    rw [← hscalar]
    exact rationalPointedPrime_scalar_preserves_spectrum F hF hpoint

/-- Difference simplicity forces every rational prime-compatible endomorphism to be injective. -/
theorem rationalPrimeCommutant_injective
    (F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalCommutesWithPrimeTranslations F) : Function.Injective F := by
  apply (RingHom.injective_iff_ker_eq_bot F).mpr
  have hs : PrimeTranslationStable (RingHom.ker F) := by
    intro f hf
    change F f = 0 at hf
    constructor
    · change F (zeroMotivePrimeTranslation 2 f) = 0
      rw [hF.1,hf,map_zero]
    · change F (zeroMotivePrimeTranslation 3 f) = 0
      rw [hF.2,hf,map_zero]
  exact ((primeTranslation_stable_ideal_iff _).mp hs).resolve_right (RingHom.ker_ne_top F)

/-- The extension criterion is precisely forward invariance of the explicitly defined spectrum. -/
theorem preservesPrimeZeroSpectrum_iff_mapsTo (σ : ℂ →ₐ[ℚ] ℂ) :
    PreservesPrimeZeroSpectrum σ ↔ Set.MapsTo (Prod.map σ σ) primeZeroSpectrum primeZeroSpectrum := by
  constructor
  · intro hσ x hx
    obtain ⟨z,rfl⟩ := hx
    obtain ⟨w,hw₂,hw₃⟩ := hσ z
    exact ⟨w,Prod.ext hw₂ hw₃⟩
  · intro h z
    obtain ⟨w,hw⟩ := h (Set.mem_range_self z)
    exact ⟨w,congrArg Prod.fst hw,congrArg Prod.snd hw⟩

private theorem rationalPrimeCommutant_comp
    (F G : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalCommutesWithPrimeTranslations F)
    (hG : RationalCommutesWithPrimeTranslations G) :
    RationalCommutesWithPrimeTranslations (F.comp G) := by
  constructor
  · intro f
    change F (G (zeroMotivePrimeTranslation 2 f)) = _
    rw [hG.1,hF.1]
    rfl
  · intro f
    change F (G (zeroMotivePrimeTranslation 3 f)) = _
    rw [hG.2,hF.2]
    rfl

private theorem rationalPointed_comp
    (F G : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalPreservesZeroMotiveIdentity F)
    (hG : RationalPreservesZeroMotiveIdentity G) :
    RationalPreservesZeroMotiveIdentity (F.comp G) :=
  fun f hf => hF (G f) (hG f hf)

/-- Restriction to scalars respects composition of prime-compatible maps. -/
theorem zeroMotiveRationalScalarAction_comp
    (F G : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra)
    (hG : RationalCommutesWithPrimeTranslations G) :
    zeroMotiveRationalScalarAction (F.comp G) =
      (zeroMotiveRationalScalarAction F).comp (zeroMotiveRationalScalarAction G) := by
  apply AlgHom.ext
  intro a
  change zeroMotiveEvaluation 0 (F (G (AddMonoidAlgebra.single 0 a))) = _
  rw [rationalPrimeCommutant_constant G hG]
  rfl

private theorem zeroMotiveRationalScalarAction_id :
    zeroMotiveRationalScalarAction (AlgHom.id ℚ ZeroMotiveAlgebra) = AlgHom.id ℚ ℂ := by
  apply AlgHom.ext
  intro a
  change zeroMotiveEvaluation 0 (AddMonoidAlgebra.single 0 a) = a
  rw [zeroMotiveEvaluation_single,zero_mul,Complex.exp_zero,mul_one]

private theorem scalarLift_comp_eq_id
    (σ τ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ)
    (hτ : PreservesPrimeZeroSpectrum τ) (hστ : σ.comp τ = AlgHom.id ℚ ℂ) :
    (zeroMotiveScalarLift σ hσ).comp (zeroMotiveScalarLift τ hτ) =
      AlgHom.id ℚ ZeroMotiveAlgebra := by
  apply rationalPointedPrime_scalar_faithful
  · exact rationalPrimeCommutant_comp _ _ (zeroMotiveScalarLift_commutes σ hσ)
      (zeroMotiveScalarLift_commutes τ hτ)
  · exact ⟨fun _ => rfl,fun _ => rfl⟩
  · exact rationalPointed_comp _ _ (zeroMotiveScalarLift_pointed σ hσ)
      (zeroMotiveScalarLift_pointed τ hτ)
  · exact fun _ hf => hf
  · rw [zeroMotiveRationalScalarAction_comp _ _ (zeroMotiveScalarLift_commutes τ hτ),
      zeroMotiveScalarLift_scalar,zeroMotiveScalarLift_scalar,zeroMotiveRationalScalarAction_id,hστ]

/-- A scalar automorphism preserving the spectrum in both directions lifts canonically. -/
def zeroMotiveScalarEquiv (σ : ℂ ≃ₐ[ℚ] ℂ)
    (hσ : PreservesPrimeZeroSpectrum σ.toAlgHom)
    (hσinv : PreservesPrimeZeroSpectrum σ.symm.toAlgHom) :
    ZeroMotiveAlgebra ≃ₐ[ℚ] ZeroMotiveAlgebra where
  __ := zeroMotiveScalarLift σ.toAlgHom hσ
  invFun := zeroMotiveScalarLift σ.symm.toAlgHom hσinv
  left_inv f := by
    have he := scalarLift_comp_eq_id σ.symm.toAlgHom σ.toAlgHom hσinv hσ (by
      apply AlgHom.ext
      intro a
      exact σ.symm_apply_apply a)
    exact DFunLike.congr_fun he f
  right_inv f := by
    have he := scalarLift_comp_eq_id σ.toAlgHom σ.symm.toAlgHom hσ hσinv (by
      apply AlgHom.ext
      intro a
      exact σ.apply_symm_apply a)
    exact DFunLike.congr_fun he f

/-- For every ground subfield, fixing its constants is exactly fixing it in the scalar action. -/
theorem rationalPrimeCommutant_fixes_subfield
    (F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalCommutesWithPrimeTranslations F) (K : Subfield ℂ) :
    (∀ a ∈ K, F (AddMonoidAlgebra.single 0 a) = AddMonoidAlgebra.single 0 a) ↔
      ∀ a ∈ K, zeroMotiveRationalScalarAction F a = a := by
  constructor
  · intro h a ha
    have he := h a ha
    rw [rationalPrimeCommutant_constant F hF] at he
    have hc := congrArg (fun f : ZeroMotiveAlgebra => f.coeff 0) he
    simpa only [AddMonoidAlgebra.coeff_single,Finsupp.single_eq_same] using hc
  · intro h a ha
    rw [rationalPrimeCommutant_constant F hF,h a ha]

private def rationalEvaluationCharacter (f : ZeroMotiveAlgebra →ₐ[ℚ] ℂ) : RawZeroMotivePoint where
  toFun z := Additive.ofMul {
    val := f (AddMonoidAlgebra.single z 1)
    inv := f (AddMonoidAlgebra.single (-z) 1)
    val_inv := by
      rw [← map_mul,AddMonoidAlgebra.single_mul_single,add_neg_cancel,one_mul]
      exact map_one f
    inv_val := by
      rw [← map_mul,AddMonoidAlgebra.single_mul_single,neg_add_cancel,one_mul]
      exact map_one f }
  map_zero' := by
    apply Additive.toMul.injective
    apply Units.ext
    exact map_one f
  map_add' z w := by
    apply Additive.toMul.injective
    apply Units.ext
    change f (AddMonoidAlgebra.single (z+w) 1) =
      f (AddMonoidAlgebra.single z 1)*f (AddMonoidAlgebra.single w 1)
    rw [← map_mul,AddMonoidAlgebra.single_mul_single,one_mul]

/-- Evaluating the image of each character extracts its nonzero coefficient. -/
def zeroMotiveRationalCharacter (F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra) : RawZeroMotivePoint :=
  rationalEvaluationCharacter (((zeroMotiveEvaluation 0).restrictScalars ℚ).comp F)

theorem zeroMotiveRationalCharacter_value
    (F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra) (z : rawZeroRelationGroup) :
    ((zeroMotiveRationalCharacter F z).toMul : ℂ) =
      zeroMotiveEvaluation 0 (F (AddMonoidAlgebra.single z 1)) := rfl

/-- Every prime-compatible map has a single-character image on each basis character. -/
theorem rationalPrimeCommutant_basis
    (F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalCommutesWithPrimeTranslations F) (z : rawZeroRelationGroup) :
    ∃ w : rawZeroRelationGroup,
      zeroPrimeEigenvalue 2 w = zeroMotiveRationalScalarAction F (zeroPrimeEigenvalue 2 z) ∧
      zeroPrimeEigenvalue 3 w = zeroMotiveRationalScalarAction F (zeroPrimeEigenvalue 3 z) ∧
      F (AddMonoidAlgebra.single z 1) =
        AddMonoidAlgebra.single w ((zeroMotiveRationalCharacter F z).toMul : ℂ) := by
  have hn : F (AddMonoidAlgebra.single z 1) ≠ 0 := by
    intro h
    have he : AddMonoidAlgebra.single z (1 : ℂ) = 0 :=
      rationalPrimeCommutant_injective F hF (h.trans (map_zero F).symm)
    have hc := congrArg (zeroMotiveEvaluation 0) he
    rw [zeroMotiveEvaluation_single,zero_mul,Complex.exp_zero,one_mul,map_zero] at hc
    exact one_ne_zero hc
  have h₂ : zeroMotivePrimeTranslation 2 (F (AddMonoidAlgebra.single z 1)) =
      zeroMotiveRationalScalarAction F (zeroPrimeEigenvalue 2 z) •
        F (AddMonoidAlgebra.single z 1) := by
    rw [← hF.1,zeroMotivePrimeTranslation_basis,rationalPrimeCommutant_smul F hF]
  have h₃ : zeroMotivePrimeTranslation 3 (F (AddMonoidAlgebra.single z 1)) =
      zeroMotiveRationalScalarAction F (zeroPrimeEigenvalue 3 z) •
        F (AddMonoidAlgebra.single z 1) := by
    rw [← hF.2,zeroMotivePrimeTranslation_basis,rationalPrimeCommutant_smul F hF]
  obtain ⟨w,ha,hb,hw⟩ := nonzero_joint_eigenvector_spectrum _ hn _ _ h₂ h₃
  have hc : ((zeroMotiveRationalCharacter F z).toMul : ℂ) =
      (F (AddMonoidAlgebra.single z 1)).coeff w := by
    rw [zeroMotiveRationalCharacter_value,hw,zeroMotiveEvaluation_single,
      zero_mul,Complex.exp_zero,mul_one,AddMonoidAlgebra.coeff_single,Finsupp.single_eq_same]
  exact ⟨w,ha,hb,by rw [hc]; exact hw⟩

/-- Even without a marked identity point, every scalar action preserves the actual spectrum. -/
theorem rationalPrimeCommutant_scalar_preserves_spectrum
    (F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalCommutesWithPrimeTranslations F) :
    PreservesPrimeZeroSpectrum (zeroMotiveRationalScalarAction F) := by
  intro z
  obtain ⟨w,ha,hb,_⟩ := rationalPrimeCommutant_basis F hF z
  exact ⟨w,ha,hb⟩

/-- An arbitrary character supplies the coefficient freedom in a semilinear prime-compatible map. -/
def zeroMotiveSemilinearLift (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ)
    (χ : RawZeroMotivePoint) : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra :=
  (AddMonoidAlgebra.mapDomainAlgHom ℚ ℂ (primeSpectrumExponentHom σ hσ)).comp
    (((zeroMotiveTranslation χ).restrictScalars ℚ).comp
      (AddMonoidAlgebra.mapAlgHom rawZeroRelationGroup σ))

theorem zeroMotiveSemilinearLift_single (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ)
    (χ : RawZeroMotivePoint) (z : rawZeroRelationGroup) (a : ℂ) :
    zeroMotiveSemilinearLift σ hσ χ (AddMonoidAlgebra.single z a) =
      AddMonoidAlgebra.single (primeSpectrumExponentHom σ hσ z) (σ a*((χ z).toMul : ℂ)) := by
  change AddMonoidAlgebra.mapDomain (primeSpectrumExponentHom σ hσ)
    (zeroMotiveTranslation χ (AddMonoidAlgebra.mapAlgHom rawZeroRelationGroup σ
      (AddMonoidAlgebra.single z a))) = _
  rw [AddMonoidAlgebra.mapAlgHom_single,zeroMotiveTranslation_single,AddMonoidAlgebra.mapDomain_single]

private theorem zeroMotiveSemilinearLift_prime
    (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ) (χ : RawZeroMotivePoint)
    (p : ℕ) (hp : ∀ z, zeroPrimeEigenvalue p (primeSpectrumExponentHom σ hσ z) =
      σ (zeroPrimeEigenvalue p z)) (f : ZeroMotiveAlgebra) :
    zeroMotiveSemilinearLift σ hσ χ (zeroMotivePrimeTranslation p f) =
      zeroMotivePrimeTranslation p (zeroMotiveSemilinearLift σ hσ χ f) := by
  have he : (zeroMotiveSemilinearLift σ hσ χ).comp
      ((zeroMotivePrimeTranslation p).restrictScalars ℚ) =
      ((zeroMotivePrimeTranslation p).restrictScalars ℚ).comp (zeroMotiveSemilinearLift σ hσ χ) := by
    apply rationalZeroAlgHom_ext
    intro z a
    change zeroMotiveSemilinearLift σ hσ χ (zeroMotivePrimeTranslation p (AddMonoidAlgebra.single z a)) =
      zeroMotivePrimeTranslation p (zeroMotiveSemilinearLift σ hσ χ (AddMonoidAlgebra.single z a))
    rw [primeTranslation_single,zeroMotiveSemilinearLift_single,zeroMotiveSemilinearLift_single,
      primeTranslation_single,map_mul,hp]
    congr 1
    ring
  exact DFunLike.congr_fun he f

/-- Every pair of a spectrum-preserving scalar embedding and a character gives a commuting map. -/
theorem zeroMotiveSemilinearLift_commutes
    (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ) (χ : RawZeroMotivePoint) :
    RationalCommutesWithPrimeTranslations (zeroMotiveSemilinearLift σ hσ χ) :=
  ⟨zeroMotiveSemilinearLift_prime σ hσ χ 2 (fun z => (primeSpectrumExponent_pair σ hσ z).1),
    zeroMotiveSemilinearLift_prime σ hσ χ 3 (fun z => (primeSpectrumExponent_pair σ hσ z).2)⟩

theorem zeroMotiveSemilinearLift_scalar
    (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ) (χ : RawZeroMotivePoint) :
    zeroMotiveRationalScalarAction (zeroMotiveSemilinearLift σ hσ χ) = σ := by
  apply AlgHom.ext
  intro a
  change zeroMotiveEvaluation 0 (zeroMotiveSemilinearLift σ hσ χ (AddMonoidAlgebra.single 0 a)) = σ a
  rw [zeroMotiveSemilinearLift_single,zeroMotiveEvaluation_single,zero_mul,Complex.exp_zero,mul_one,
    map_zero χ]
  change σ a*1 = σ a
  exact mul_one _

theorem zeroMotiveSemilinearLift_character
    (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ) (χ : RawZeroMotivePoint) :
    zeroMotiveRationalCharacter (zeroMotiveSemilinearLift σ hσ χ) = χ := by
  apply AddMonoidHom.ext
  intro z
  apply Additive.toMul.injective
  apply Units.ext
  rw [zeroMotiveRationalCharacter_value,zeroMotiveSemilinearLift_single,
    zeroMotiveEvaluation_single,zero_mul,Complex.exp_zero,mul_one,map_one,one_mul]

/-- The scalar embedding and the character extracted from a commuting map reconstruct it exactly. -/
theorem rationalPrimeCommutant_normal_form
    (F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalCommutesWithPrimeTranslations F) :
    F = zeroMotiveSemilinearLift (zeroMotiveRationalScalarAction F)
      (rationalPrimeCommutant_scalar_preserves_spectrum F hF) (zeroMotiveRationalCharacter F) := by
  apply rationalZeroAlgHom_ext
  intro z a
  obtain ⟨w,hw₂,hw₃,hw⟩ := rationalPrimeCommutant_basis F hF z
  let hσ := rationalPrimeCommutant_scalar_preserves_spectrum F hF
  have hwφ : w = primeSpectrumExponentHom (zeroMotiveRationalScalarAction F) hσ z := by
    apply zeroPrimeEigenvalue_pair_injective
    exact Prod.ext (hw₂.trans (primeSpectrumExponent_pair _ hσ z).1.symm)
      (hw₃.trans (primeSpectrumExponent_pair _ hσ z).2.symm)
  have hs : AddMonoidAlgebra.single z a = a • AddMonoidAlgebra.single z 1 := by
    rw [AddMonoidAlgebra.smul_single,smul_eq_mul,mul_one]
  rw [zeroMotiveSemilinearLift_single,hs,rationalPrimeCommutant_smul F hF,hw,hwφ,
    AddMonoidAlgebra.smul_single,smul_eq_mul]

/-- The full rational-algebra centralizer has exactly the stated semilinear form. -/
theorem primeTranslation_rational_algebra_centralizer
    (F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra) :
    RationalCommutesWithPrimeTranslations F ↔
      ∃ (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ) (χ : RawZeroMotivePoint),
        F = zeroMotiveSemilinearLift σ hσ χ := by
  constructor
  · intro hF
    exact ⟨zeroMotiveRationalScalarAction F,rationalPrimeCommutant_scalar_preserves_spectrum F hF,
      zeroMotiveRationalCharacter F,rationalPrimeCommutant_normal_form F hF⟩
  · rintro ⟨σ,hσ,χ,rfl⟩
    exact zeroMotiveSemilinearLift_commutes σ hσ χ

/-- Both coordinates in the semilinear classification are unique. -/
theorem zeroMotiveSemilinearLift_coordinates_injective
    (σ τ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ) (hτ : PreservesPrimeZeroSpectrum τ)
    (χ ψ : RawZeroMotivePoint)
    (he : zeroMotiveSemilinearLift σ hσ χ = zeroMotiveSemilinearLift τ hτ ψ) : σ = τ ∧ χ = ψ := by
  constructor
  · have h := congrArg zeroMotiveRationalScalarAction he
    simpa only [zeroMotiveSemilinearLift_scalar] using h
  · have h := congrArg zeroMotiveRationalCharacter he
    simpa only [zeroMotiveSemilinearLift_character] using h

/-- Pointed prime-compatible maps intertwine augmentation with their scalar action. -/
theorem rationalPointedPrime_augmentation
    (F : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalCommutesWithPrimeTranslations F)
    (hpoint : RationalPreservesZeroMotiveIdentity F) (f : ZeroMotiveAlgebra) :
    zeroMotiveEvaluation 0 (F f) = zeroMotiveRationalScalarAction F (zeroMotiveEvaluation 0 f) := by
  let hσ := rationalPointedPrime_scalar_preserves_spectrum F hF hpoint
  have he : F = zeroMotiveScalarLift (zeroMotiveRationalScalarAction F) hσ := by
    apply rationalPointedPrime_scalar_faithful F _ hF (zeroMotiveScalarLift_commutes _ hσ)
      hpoint (zeroMotiveScalarLift_pointed _ hσ)
    exact (zeroMotiveScalarLift_scalar _ hσ).symm
  calc
    zeroMotiveEvaluation 0 (F f) =
        zeroMotiveEvaluation 0 (zeroMotiveScalarLift (zeroMotiveRationalScalarAction F) hσ f) :=
      congrArg (fun H : ZeroMotiveAlgebra →ₐ[ℚ] ZeroMotiveAlgebra => zeroMotiveEvaluation 0 (H f)) he
    _ = _ := zeroMotiveScalarLift_augmentation _ hσ f

private theorem rationalPrimeCommutant_inverse
    (F : ZeroMotiveAlgebra ≃ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalCommutesWithPrimeTranslations F.toAlgHom) :
    RationalCommutesWithPrimeTranslations F.symm.toAlgHom := by
  constructor
  · intro f
    apply F.injective
    change F (F.symm (zeroMotivePrimeTranslation 2 f)) = F (zeroMotivePrimeTranslation 2 (F.symm f))
    rw [F.apply_symm_apply]
    exact (congrArg (zeroMotivePrimeTranslation 2) (F.apply_symm_apply f).symm).trans
      (hF.1 (F.symm f)).symm
  · intro f
    apply F.injective
    change F (F.symm (zeroMotivePrimeTranslation 3 f)) = F (zeroMotivePrimeTranslation 3 (F.symm f))
    rw [F.apply_symm_apply]
    exact (congrArg (zeroMotivePrimeTranslation 3) (F.apply_symm_apply f).symm).trans
      (hF.2 (F.symm f)).symm

private theorem rationalPointedPrime_inverse
    (F : ZeroMotiveAlgebra ≃ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalCommutesWithPrimeTranslations F.toAlgHom)
    (hpoint : RationalPreservesZeroMotiveIdentity F.toAlgHom) :
    RationalPreservesZeroMotiveIdentity F.symm.toAlgHom := by
  intro f hf
  have he := rationalPointedPrime_augmentation F.toAlgHom hF hpoint (F.symm f)
  change zeroMotiveEvaluation 0 (F (F.symm f)) =
    zeroMotiveRationalScalarAction F.toAlgHom (zeroMotiveEvaluation 0 (F.symm f)) at he
  rw [F.apply_symm_apply,hf] at he
  apply (zeroMotiveRationalScalarAction F.toAlgHom).injective
  change zeroMotiveRationalScalarAction F.toAlgHom (zeroMotiveEvaluation 0 (F.symm f)) =
    zeroMotiveRationalScalarAction F.toAlgHom 0
  rw [map_zero]
  exact he.symm

private theorem rationalPrime_inverse_scalar
    (F : ZeroMotiveAlgebra ≃ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalCommutesWithPrimeTranslations F.toAlgHom)
    (σ : ℂ ≃ₐ[ℚ] ℂ) (hσ : zeroMotiveRationalScalarAction F.toAlgHom = σ.toAlgHom) :
    zeroMotiveRationalScalarAction F.symm.toAlgHom = σ.symm.toAlgHom := by
  have hcomp := zeroMotiveRationalScalarAction_comp F.toAlgHom F.symm.toAlgHom
    (rationalPrimeCommutant_inverse F hF)
  have hid : F.toAlgHom.comp F.symm.toAlgHom = AlgHom.id ℚ ZeroMotiveAlgebra := by
    apply AlgHom.ext
    intro f
    exact F.apply_symm_apply f
  rw [hid,zeroMotiveRationalScalarAction_id,hσ] at hcomp
  apply AlgHom.ext
  intro a
  apply σ.injective
  change σ (zeroMotiveRationalScalarAction F.symm.toAlgHom a) = σ (σ.symm a)
  rw [σ.apply_symm_apply]
  exact (DFunLike.congr_fun hcomp a).symm

/-- Pointed arithmetic automorphisms correspond exactly to scalar automorphisms preserving the
joint prime spectrum in both directions. -/
theorem primeSpectrum_scalar_automorphism_extension_iff (σ : ℂ ≃ₐ[ℚ] ℂ) :
    (PreservesPrimeZeroSpectrum σ.toAlgHom ∧ PreservesPrimeZeroSpectrum σ.symm.toAlgHom) ↔
      ∃! F : ZeroMotiveAlgebra ≃ₐ[ℚ] ZeroMotiveAlgebra,
        RationalCommutesWithPrimeTranslations F.toAlgHom ∧
          RationalPreservesZeroMotiveIdentity F.toAlgHom ∧
          zeroMotiveRationalScalarAction F.toAlgHom = σ.toAlgHom := by
  constructor
  · rintro ⟨hσ,hinv⟩
    refine ⟨zeroMotiveScalarEquiv σ hσ hinv,
      ⟨zeroMotiveScalarLift_commutes _ hσ,zeroMotiveScalarLift_pointed _ hσ,
        zeroMotiveScalarLift_scalar _ hσ⟩,?_⟩
    intro F hF
    have he := rationalPointedPrime_scalar_faithful F.toAlgHom
      (zeroMotiveScalarEquiv σ hσ hinv).toAlgHom hF.1 (zeroMotiveScalarLift_commutes _ hσ)
      hF.2.1 (zeroMotiveScalarLift_pointed _ hσ)
      (hF.2.2.trans (zeroMotiveScalarLift_scalar _ hσ).symm)
    apply AlgEquiv.ext
    intro f
    exact DFunLike.congr_fun he f
  · rintro ⟨F,⟨hF,hpoint,hscalar⟩,_⟩
    constructor
    · rw [← hscalar]
      exact rationalPointedPrime_scalar_preserves_spectrum F.toAlgHom hF hpoint
    · rw [← rationalPrime_inverse_scalar F hF σ hscalar]
      exact rationalPointedPrime_scalar_preserves_spectrum F.symm.toAlgHom
        (rationalPrimeCommutant_inverse F hF) (rationalPointedPrime_inverse F hF hpoint)

private theorem zeroMotiveSemilinearLift_zero
    (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ) :
    zeroMotiveSemilinearLift σ hσ 0 = zeroMotiveScalarLift σ hσ := by
  apply rationalZeroAlgHom_ext
  intro z a
  rw [zeroMotiveSemilinearLift_single,zeroMotiveScalarLift_single]
  change AddMonoidAlgebra.single _ (σ a*1) = AddMonoidAlgebra.single _ (σ a)
  rw [mul_one]

/-- Marking the identity removes exactly the character coordinate of the full centralizer. -/
theorem zeroMotiveSemilinearLift_pointed_iff
    (σ : ℂ →ₐ[ℚ] ℂ) (hσ : PreservesPrimeZeroSpectrum σ) (χ : RawZeroMotivePoint) :
    RationalPreservesZeroMotiveIdentity (zeroMotiveSemilinearLift σ hσ χ) ↔ χ = 0 := by
  constructor
  · intro hp
    apply AddMonoidHom.ext
    intro z
    apply Additive.toMul.injective
    apply Units.ext
    change ((χ z).toMul : ℂ) = 1
    have he := rationalPointed_basis_evaluation _ hp z
    rw [zeroMotiveSemilinearLift_single,zeroMotiveEvaluation_single,zero_mul,
      Complex.exp_zero,mul_one,map_one,one_mul] at he
    exact he
  · rintro rfl
    rw [zeroMotiveSemilinearLift_zero]
    exact zeroMotiveScalarLift_pointed σ hσ

/-- A commuting algebra automorphism restricts to an actual automorphism of the coefficient field. -/
def zeroMotiveRationalScalarEquiv (F : ZeroMotiveAlgebra ≃ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalCommutesWithPrimeTranslations F.toAlgHom) : ℂ ≃ₐ[ℚ] ℂ where
  __ := zeroMotiveRationalScalarAction F.toAlgHom
  invFun := zeroMotiveRationalScalarAction F.symm.toAlgHom
  left_inv a := by
    have he := zeroMotiveRationalScalarAction_comp F.symm.toAlgHom F.toAlgHom hF
    have hid : F.symm.toAlgHom.comp F.toAlgHom = AlgHom.id ℚ ZeroMotiveAlgebra := by
      apply AlgHom.ext
      intro f
      exact F.symm_apply_apply f
    rw [hid,zeroMotiveRationalScalarAction_id] at he
    exact (DFunLike.congr_fun he a).symm
  right_inv a := by
    have he := zeroMotiveRationalScalarAction_comp F.toAlgHom F.symm.toAlgHom
      (rationalPrimeCommutant_inverse F hF)
    have hid : F.toAlgHom.comp F.symm.toAlgHom = AlgHom.id ℚ ZeroMotiveAlgebra := by
      apply AlgHom.ext
      intro f
      exact F.apply_symm_apply f
    rw [hid,zeroMotiveRationalScalarAction_id] at he
    exact (DFunLike.congr_fun he a).symm

/-- Both directions of spectral invariance are forced by a pointed automorphism. -/
theorem rationalPointedPrime_scalarEquiv_preserves_spectrum
    (F : ZeroMotiveAlgebra ≃ₐ[ℚ] ZeroMotiveAlgebra)
    (hF : RationalCommutesWithPrimeTranslations F.toAlgHom)
    (hpoint : RationalPreservesZeroMotiveIdentity F.toAlgHom) :
    PreservesPrimeZeroSpectrum (zeroMotiveRationalScalarEquiv F hF).toAlgHom ∧
      PreservesPrimeZeroSpectrum (zeroMotiveRationalScalarEquiv F hF).symm.toAlgHom :=
  ⟨rationalPointedPrime_scalar_preserves_spectrum F.toAlgHom hF hpoint,
    rationalPointedPrime_scalar_preserves_spectrum F.symm.toAlgHom
      (rationalPrimeCommutant_inverse F hF) (rationalPointedPrime_inverse F hF hpoint)⟩

end GaloisForLFunctions.GaloisTheoryOfZeros
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeCommutant_constant
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeSpectrumExponentHom_injective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPointedPrime_scalar_faithful
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeSpectrum_scalar_extension_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeCommutant_injective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.preservesPrimeZeroSpectrum_iff_mapsTo
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveScalarEquiv
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeCommutant_fixes_subfield
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeCommutant_basis
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeCommutant_scalar_preserves_spectrum
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeCommutant_normal_form
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTranslation_rational_algebra_centralizer
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveSemilinearLift_coordinates_injective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPointedPrime_augmentation
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeSpectrum_scalar_automorphism_extension_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveSemilinearLift_pointed_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zeroMotiveRationalScalarEquiv
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPointedPrime_scalarEquiv_preserves_spectrum
