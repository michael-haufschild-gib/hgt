import GaloisForLFunctions.HTGeometry.MultipleSineAnnihilatorExact
import GaloisForLFunctions.HTGeometry.MultipleGammaMultiplicativeAnnihilator

/-!
# The multiplicative classification for the multiple sine

The multiple sine of a frame is the Barnes cone product against its reflection, so its logarithmic
derivative is the reflected Barnes source — the multiple-sine coordinate.  A finite product of
integer powers of structurally translated multiple sines therefore has the exponent operator applied
to that coordinate as its logarithmic derivative, and such a product is differentially algebraic
exactly when its exponent operator lies in the squarefree Veronese ideal `I_{N-1}`.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher VeroneseIdeal

noncomputable section

noncomputable local instance msmaDecidableEq :
    DecidableEq (meroField (Set.univ : Set ℂ)) := Classical.decEq _

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

attribute [local instance] relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential
  relativeGaugeDifferentialAlgebra relativeGaugeCharZeroBase

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### The multiple sine as a meromorphic germ -/

/-- The multiple sine of a frame: the Barnes cone product against its reflection. -/
def frameSineMero (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (S : Finset ι) (hS : S.Nonempty) :
    meroField (Set.univ : Set ℂ) :=
  haveI : Nonempty {i : ι // i ∈ S} := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  barnesConeMero (subframe ω S) (subframe_im_pos hω S) *
    (complexReflectionMeroEquiv (frameReflectionPoint ω S)
      (barnesConeMero (subframe ω S) (subframe_im_pos hω S))) ^ (frameSignZ S)

omit [Fintype ι] [DecidableEq ι] in
theorem frameSineMero_ne_zero (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (S : Finset ι)
    (hS : S.Nonempty) : frameSineMero ω hω S hS ≠ 0 := by
  haveI : Nonempty {i : ι // i ∈ S} := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  refine mul_ne_zero (barnesConeMero_ne_zero _ _) (zpow_ne_zero _ ?_)
  exact (map_ne_zero_iff _ (complexReflectionMeroEquiv
    (frameReflectionPoint ω S)).injective).mpr (barnesConeMero_ne_zero _ _)

/-- The logarithmic derivative of a reflection is minus the reflection of the logarithmic
derivative. -/
theorem logDeriv_complexReflectionMeroEquiv (c : ℂ) (y : meroField (Set.univ : Set ℂ)) :
    Differential.logDeriv (complexReflectionMeroEquiv c y)
      = -(complexReflectionMeroEquiv c (Differential.logDeriv y)) := by
  have hd : ((complexReflectionMeroEquiv c y)′) = -(complexReflectionMeroEquiv c (y′)) := by
    rw [complexReflectionMeroEquiv_deriv c y]
    ring
  rw [Differential.logDeriv, Differential.logDeriv, hd, map_div₀, neg_div]

omit [Fintype ι] [DecidableEq ι] in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **The multiple sine has the multiple-sine coordinate as logarithmic derivative.** -/
theorem logDeriv_frameSineMero (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (S : Finset ι)
    (hS : S.Nonempty) :
    Differential.logDeriv (frameSineMero ω hω S hS) = frameSourceMero ω hω S hS := by
  haveI : Nonempty {i : ι // i ∈ S} := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  have hne := barnesConeMero_ne_zero (subframe ω S) (subframe_im_pos hω S)
  have hrefl : complexReflectionMeroEquiv (frameReflectionPoint ω S)
      (barnesConeMero (subframe ω S) (subframe_im_pos hω S)) ≠ 0 :=
    (map_ne_zero_iff _ (complexReflectionMeroEquiv
      (frameReflectionPoint ω S)).injective).mpr hne
  rw [frameSineMero, Differential.logDeriv_mul _ _ hne (zpow_ne_zero _ hrefl),
    differential_logDeriv_zpow _ hrefl, logDeriv_complexReflectionMeroEquiv,
    frameSourceMero_eq, multipleSineSourceMero, meroReflectedSource, barnesSourceLogDerivMero]
  ring

/-! ### Translated factors and finite products -/

/-- The multiple sine of the full frame, translated by an exponent vector. -/
def translateSine (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (hne : (Finset.univ : Finset ι).Nonempty) (n : ι →₀ ℕ) :
    meroField (Set.univ : Set ℂ) :=
  addTranslationMeroEquiv (natShift ω n) (frameSineMero ω hω Finset.univ hne)

omit [DecidableEq ι] in
theorem translateSine_ne_zero (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (hne : (Finset.univ : Finset ι).Nonempty) (n : ι →₀ ℕ) :
    translateSine ω hω hne n ≠ 0 := by
  intro hzero
  refine frameSineMero_ne_zero ω hω Finset.univ hne ?_
  have h := congrArg (addTranslationMeroEquiv (-(natShift ω n))) hzero
  rw [translateSine, addTranslationMeroEquiv_add, neg_add_cancel,
    addTranslationMeroEquiv_zero_apply, map_zero] at h
  exact h

omit [DecidableEq ι] in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Translation commutes with logarithmic differentiation. -/
theorem logDeriv_translateSine (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (hne : (Finset.univ : Finset ι).Nonempty) (n : ι →₀ ℕ) :
    Differential.logDeriv (translateSine ω hω hne n)
      = addTranslationMeroEquiv (natShift ω n) (frameSourceMero ω hω Finset.univ hne) := by
  rw [translateSine, Differential.logDeriv, ← logDeriv_frameSineMero ω hω Finset.univ hne,
    Differential.logDeriv, ← addTranslationMeroEquiv_deriv, ← map_div₀]

/-- A finite product of integer powers of structurally translated multiple sines. -/
def translateSineProduct (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (hne : (Finset.univ : Finset ι).Nonempty) (c : (ι →₀ ℕ) →₀ ℤ) :
    meroField (Set.univ : Set ℂ) :=
  ∏ n ∈ c.support, translateSine ω hω hne n ^ (c n)

omit [DecidableEq ι] in
theorem translateSineProduct_ne_zero (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (hne : (Finset.univ : Finset ι).Nonempty) (c : (ι →₀ ℕ) →₀ ℤ) :
    translateSineProduct ω hω hne c ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun n _ => zpow_ne_zero _ (translateSine_ne_zero ω hω hne n)

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Logarithmic derivative of a translate product.**  It is the exponent operator applied to the
multiple-sine coordinate. -/
theorem logDeriv_translateSineProduct (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (hne : (Finset.univ : Finset ι).Nonempty) (c : (ι →₀ ℕ) →₀ ℤ) :
    Differential.logDeriv (translateSineProduct ω hω hne c) =
      xApply ω (translateProductOperator c) (sineFaceCoord ω hω ∅) := by
  classical
  have hcoord : sineFaceCoord ω hω (∅ : Finset ι)
      = frameSourceMero ω hω Finset.univ hne := by
    have hcompl : ((∅ : Finset ι)ᶜ : Finset ι) = Finset.univ := by simp
    have hne' : ((∅ : Finset ι)ᶜ : Finset ι).Nonempty := by rw [hcompl]; exact hne
    rw [sineFaceCoord_eq ω hω hne', frameSourceMero_congr ω hω hcompl hne' hne]
  rw [translateSineProduct,
    Differential.logDeriv_prod _ c.support _
      (fun n _ => zpow_ne_zero _ (translateSine_ne_zero ω hω hne n)),
    translateProductOperator, xApply_finsetSum, hcoord]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [differential_logDeriv_zpow _ (translateSine_ne_zero ω hω hne n),
    logDeriv_translateSine ω hω hne n, MvPolynomial.C_apply, xApply_monomial_mul,
    xMonomialApply_zero, xApply_translationMonomial, map_intCast]

/-! ### The multiplicative classification -/

set_option synthInstance.maxHeartbeats 1200000 in
/-- **Multiplicative classification.**  A finite product of integer powers of structurally
translated multiple sines is differentially algebraic exactly when its exponent operator lies in the
squarefree Veronese ideal `I_{N-1}`. -/
theorem differentialAlgebraicOver_translateSineProduct_iff_mem_veroneseIdeal
    {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im) (r : ℕ) (hcard : Fintype.card ι = r + 1)
    (hne : (Finset.univ : Finset ι).Nonempty) (c : (ι →₀ ℕ) →₀ ℤ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (translateSineProduct (fun k => μ * (rad k : ℂ)) hω hne c) ↔
      translateProductOperator c ∈ veroneseIdeal ℂ ι r := by
  rw [← differentialAlgebraicOver_xApply_multipleSine_iff_mem_veroneseIdeal hrad hind hω r hcard,
    ← logDeriv_translateSineProduct (fun k => μ * (rad k : ℂ)) hω hne]
  constructor
  · intro hDA
    exact differentialAlgebraicOver_deriv_div_self hDA
  · intro hDA
    by_contra hnot
    exact (hypertranscendentalOver_deriv_div_self_iff
      (translateSineProduct (fun k => μ * (rad k : ℂ)) hω hne c)).mpr hnot hDA

end

end GaloisForLFunctions.HTGeometry
