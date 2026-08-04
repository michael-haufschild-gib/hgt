import GaloisForLFunctions.HTGeometry.ProductMeromorphicPullback
import GaloisForLFunctions.HTGeometry.FiniteShadowCapacitySpectrum

/-!
# Capacity realization inside the meromorphic field of a product domain

All the pieces of a finite-shadow capacity argument now live in one place.  On a product domain the
meromorphic field carries the second-factor derivation; the meromorphic field of the first factor
embeds in it as differential constants; an observation matrix of first-factor germs which is the
identity at one point of the first factor has nonzero determinant; and an invertible observation
matrix transfers every direction of a differentially independent palette.

This file assembles them: an interpolating observation packet on the first factor turns a palette of
`n` differentially independent second-factor functions into `n` differentially independent
observations, and no packet of `n + 1` observations built from that palette is ever differentially
independent.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open Matrix GaloisForLFunctions

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The determinant of an observation matrix of analytic germs which is the identity at one point of
the domain is nonzero in the meromorphic field. -/
theorem det_algebraMap_ne_zero_of_eval_eq_one {U : Set E}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {x₀ : E} (hx₀ : x₀ ∈ U) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (analyticGermSubringOn U))
    (hA : A.map (analyticGermEval hx₀) = 1) :
    letI := isDomain_analyticGermSubringOn U hUo hUc hUne
    (A.map (algebraMap (analyticGermSubringOn U) (dirMeroField U))).det ≠ 0 := by
  letI := isDomain_analyticGermSubringOn U hUo hUc hUne
  have hdet : A.det ≠ 0 := det_ne_zero_of_map_eq_one A (analyticGermEval hx₀) hA
  have hmap : (A.map (algebraMap (analyticGermSubringOn U) (dirMeroField U))).det
      = algebraMap (analyticGermSubringOn U) (dirMeroField U) A.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  rw [hmap]
  intro hzero
  exact hdet (IsFractionRing.injective (analyticGermSubringOn U) (dirMeroField U)
    (by simpa using hzero))

/-- **Capacity realization on a product domain.**  An interpolating observation packet on the first
factor carries a differentially independent palette of the product field to `n` differentially
independent observations, over the meromorphic field of the first factor. -/
theorem productCapacity_realization {U : Set E} {V : Set F}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty)
    (v : F) {x₀ : E} (hx₀ : x₀ ∈ U) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (analyticGermSubringOn U))
    (hA : A.map (analyticGermEval hx₀) = 1) :
    letI := isDomain_analyticGermSubringOn U hUo hUc hUne
    letI := isDomain_analyticGermSubringOn (U ×ˢ V) (hUo.prod hVo) (hUc.prod hVc)
      (hUne.prod hVne)
    letI := dirMeroFieldDifferential (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne) ((0 : E), v)
    letI : Algebra (dirMeroField U) (dirMeroField (U ×ˢ V)) :=
      (meroPullbackFst hUo hUc hUne (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne) hVne).toAlgebra
    ∀ y : Fin n → dirMeroField (U ×ˢ V),
      DifferentialIndependent (dirMeroField U) y →
      DifferentialIndependent (dirMeroField U)
        (matrixLinearForms (A.map (algebraMap (analyticGermSubringOn U) (dirMeroField U))) y) := by
  letI := isDomain_analyticGermSubringOn U hUo hUc hUne
  letI := isDomain_analyticGermSubringOn (U ×ˢ V) (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne)
  letI := dirMeroFieldDifferential (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne) ((0 : E), v)
  letI : Algebra (dirMeroField U) (dirMeroField (U ×ˢ V)) :=
    (meroPullbackFst hUo hUc hUne (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne) hVne).toAlgebra
  intro y hy
  refine finiteShadow_fullRank_realizes_capacity n _
    (det_algebraMap_ne_zero_of_eval_eq_one hUo hUc hUne hx₀ A hA) (fun i j => ?_) y hy
  -- the coefficients are differential constants: they are pulled back from the first factor
  have hcoeff : algebraMap (dirMeroField U) (dirMeroField (U ×ˢ V))
      ((A.map (algebraMap (analyticGermSubringOn U) (dirMeroField U))) i j)
      = algebraMap (analyticGermSubringOn (U ×ˢ V)) (dirMeroField (U ×ˢ V))
        (analyticGermPullbackFst U V (A i j)) := by
    show meroPullbackFst hUo hUc hUne (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne) hVne
        (algebraMap (analyticGermSubringOn U) (dirMeroField U) (A i j)) = _
    exact meroPullbackFst_algebraMap hUo hUc hUne (hUo.prod hVo) (hUc.prod hVc)
      (hUne.prod hVne) hVne (A i j)
  rw [hcoeff, dirMeroFieldDifferential_algebraMap (hUo.prod hVo) (hUc.prod hVc)
    (hUne.prod hVne) ((0 : E), v),
    dirSubringDeriv_analyticGermPullbackFst (hUo.prod hVo) v (A i j), map_zero]

/-- **Nonconcentration on a product domain.**  No packet of `n + 1` observations mixed from an
`n`-element palette is differentially independent, whatever the coefficients. -/
theorem productCapacity_nonconcentration {U : Set E} {V : Set F}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty)
    (v : F) {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin n) (analyticGermSubringOn U)) :
    letI := isDomain_analyticGermSubringOn U hUo hUc hUne
    letI := isDomain_analyticGermSubringOn (U ×ˢ V) (hUo.prod hVo) (hUc.prod hVc)
      (hUne.prod hVne)
    letI := dirMeroFieldDifferential (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne) ((0 : E), v)
    letI : Algebra (dirMeroField U) (dirMeroField (U ×ˢ V)) :=
      (meroPullbackFst hUo hUc hUne (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne) hVne).toAlgebra
    ∀ y : Fin n → dirMeroField (U ×ˢ V),
      DifferentialIndependent (dirMeroField U) y →
      ¬ DifferentialIndependent (dirMeroField U)
        (matrixLinearForms (A.map (algebraMap (analyticGermSubringOn U) (dirMeroField U))) y) := by
  letI := isDomain_analyticGermSubringOn U hUo hUc hUne
  letI := isDomain_analyticGermSubringOn (U ×ˢ V) (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne)
  letI := dirMeroFieldDifferential (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne) ((0 : E), v)
  letI : Algebra (dirMeroField U) (dirMeroField (U ×ˢ V)) :=
    (meroPullbackFst hUo hUc hUne (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne) hVne).toAlgebra
  intro y hy
  refine finiteShadow_moreObservablesThanSources_not_differentialIndependent n _
    (fun i j => ?_) y hy
  have hcoeff : algebraMap (dirMeroField U) (dirMeroField (U ×ˢ V))
      ((A.map (algebraMap (analyticGermSubringOn U) (dirMeroField U))) i j)
      = algebraMap (analyticGermSubringOn (U ×ˢ V)) (dirMeroField (U ×ˢ V))
        (analyticGermPullbackFst U V (A i j)) := by
    show meroPullbackFst hUo hUc hUne (hUo.prod hVo) (hUc.prod hVc) (hUne.prod hVne) hVne
        (algebraMap (analyticGermSubringOn U) (dirMeroField U) (A i j)) = _
    exact meroPullbackFst_algebraMap hUo hUc hUne (hUo.prod hVo) (hUc.prod hVc)
      (hUne.prod hVne) hVne (A i j)
  rw [hcoeff, dirMeroFieldDifferential_algebraMap (hUo.prod hVo) (hUc.prod hVc)
    (hUne.prod hVne) ((0 : E), v),
    dirSubringDeriv_analyticGermPullbackFst (hUo.prod hVo) v (A i j), map_zero]

end

end GaloisForLFunctions.HTGeometry
