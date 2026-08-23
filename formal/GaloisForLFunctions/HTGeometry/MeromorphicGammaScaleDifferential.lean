import GaloisForLFunctions.HTGeometry.MeromorphicGammaOrbitQuotient
import GaloisForLFunctions.HTGeometry.MeromorphicGammaComplexScale
import GaloisForLFunctions.HTGeometry.MobiusJetTransfer

/-!
# Meromorphic Gamma coordinate-scale differential transport

Coordinate dilation is promoted to a rescaled differential automorphism of the global
meromorphic field over `ℂ(X)`.  This gives exact preservation of differential algebraicity and
identifies natural-scale Gamma elements with their arbitrary common-unit rescalings.
-/

namespace GaloisForLFunctions.HTGeometry

open Bottcher Filter Set Topology Function Complex
open _root_.HTGeometry
open scoped BigOperators Differential

noncomputable section

local instance gammaCommonUnitDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance gammaCommonUnitComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance gammaCommonUnitComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance gammaCommonUnitDifferential : Differential (meroField Set.univ) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance gammaCommonUnitRatFuncAlgebra : Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance gammaCommonUnitRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance gammaCommonUnitDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance gammaCommonUnitCharZero : CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

theorem gammaNatScaleMero_eq_gammaScaleShiftMero
    {n : ℕ} (hn : 0 < n) (a : ℂ) :
    gammaNatScaleMero n a = gammaScaleShiftMero (n : ℂ)
      (Nat.cast_ne_zero.mpr hn.ne') a := by
  rw [gammaNatScaleMero, gammaScaleShiftMero_eq]
  congr 2

theorem complexScaleMeroEquiv_gammaScaleShiftMero
    (delta : ℂ) (hdelta : delta ≠ 0) (scale : ℂ) (hscale : scale ≠ 0) (a : ℂ) :
    complexScaleMeroEquiv delta hdelta (gammaScaleShiftMero scale hscale a) =
      gammaScaleShiftMero (scale * delta) (mul_ne_zero hscale hdelta) a := by
  rw [gammaScaleShiftMero_eq, gammaScaleShiftMero_eq, map_inv₀,
    complexScaleMeroEquiv_algebraMap]
  congr 2
  apply Subtype.ext
  apply univGerm_ext
  intro z
  rw [univGermEval_complexScaleAnalyticEquiv,
    univGermEval_reciprocalGammaScaleShiftAnalytic,
    univGermEval_reciprocalGammaScaleShiftAnalytic]
  congr 1
  ring

/-- Chain rule for coordinate dilation on analytic germs. -/
theorem complexScaleAnalyticEquiv_deriv
    (delta : ℂ) (hdelta : delta ≠ 0) (a : analyticSubring (Set.univ : Set ℂ)) :
    analyticSubringDeriv isOpen_univ (complexScaleAnalyticEquiv delta hdelta a) =
      constToAnalytic Set.univ delta *
        complexScaleAnalyticEquiv delta hdelta
          (analyticSubringDeriv isOpen_univ a) := by
  obtain ⟨f, hf, hfa⟩ := a.2
  apply Subtype.ext
  let htr : Tendsto (complexScale delta) (Filter.principal Set.univ)
      (Filter.principal Set.univ) :=
    tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)
  change analyticGermDeriv isOpen_univ
      ((a : Germ (Filter.principal Set.univ) ℂ).compTendsto (complexScale delta) htr) =
    (delta : Germ (Filter.principal Set.univ) ℂ) *
      (analyticGermDeriv isOpen_univ
        (a : Germ (Filter.principal Set.univ) ℂ)).compTendsto (complexScale delta) htr
  rw [← hfa]
  change Germ.ofFun (l := Filter.principal Set.univ)
      (deriv (fun z => f (delta * z))) =
    Germ.ofFun (l := Filter.principal Set.univ) (fun _ => delta) *
      Germ.ofFun (l := Filter.principal Set.univ) (fun z => deriv f (delta * z))
  rw [← Germ.coe_mul, Germ.coe_eq]
  exact eventually_principal.mpr fun z _ => by
    simp only [Pi.mul_apply]
    exact deriv_comp_mul_left delta f z

/-- Chain rule for coordinate dilation on the global meromorphic field. -/
theorem complexScaleMeroEquiv_deriv
    (delta : ℂ) (hdelta : delta ≠ 0) (x : meroField (Set.univ : Set ℂ)) :
    letI := meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty
    (complexScaleMeroEquiv delta hdelta x)′ =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (constToAnalytic Set.univ delta) *
        complexScaleMeroEquiv delta hdelta (x′) := by
  let A := analyticSubring (Set.univ : Set ℂ)
  let F := meroField (Set.univ : Set ℂ)
  letI hdom := Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty
  letI : Algebra ℤ A := Ring.toIntAlgebra _
  letI : Algebra ℤ F := Ring.toIntAlgebra _
  letI hdiff := meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty
  let sigmaA : A ≃+* A := complexScaleAnalyticEquiv delta hdelta
  let sigmaF : F ≃+* F := complexScaleMeroEquiv delta hdelta
  let w : F := algebraMap A F (constToAnalytic Set.univ delta)
  have hDc : (Differential.equiv sigmaF : Differential F).deriv =
      (sigmaF.symm w) • (Differential.deriv : Derivation ℤ F F) := by
    apply fractionRing_derivation_ext (A := A) (F := F)
    intro a
    change sigmaF.symm (Differential.deriv (sigmaF (algebraMap A F a))) =
      sigmaF.symm w * Differential.deriv (algebraMap A F a)
    have hsigma : sigmaF (algebraMap A F a) = algebraMap A F (sigmaA a) :=
      complexScaleMeroEquiv_algebraMap delta hdelta a
    rw [hsigma, meroFieldDifferential_algebraMap, meroFieldDifferential_algebraMap,
      complexScaleAnalyticEquiv_deriv delta hdelta a, map_mul]
    have hback : sigmaF (algebraMap A F (analyticSubringDeriv isOpen_univ a)) =
        algebraMap A F (sigmaA (analyticSubringDeriv isOpen_univ a)) :=
      complexScaleMeroEquiv_algebraMap delta hdelta _
    rw [← hback, map_mul, RingEquiv.symm_apply_apply]
  have hx := Derivation.congr_fun hDc x
  change sigmaF.symm (Differential.deriv (sigmaF x)) =
    sigmaF.symm w * Differential.deriv x at hx
  have h := congrArg sigmaF hx
  rw [RingEquiv.apply_symm_apply, map_mul, RingEquiv.apply_symm_apply] at h
  exact h

theorem ratScaleBy_comp_inv (delta : ℂ) (hdelta : delta ≠ 0) :
    (ratScaleBy delta hdelta).comp
        (ratScaleBy delta⁻¹ (inv_ne_zero hdelta)) = RingHom.id (RatFunc ℂ) := by
  apply IsFractionRing.ringHom_ext (A := Polynomial ℂ)
  intro p
  rw [RingHom.comp_apply, RingHom.id_apply, ratScaleBy_algebraMap,
    ratScaleBy_algebraMap]
  congr 1
  rw [Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.X_comp]
  have hX : Polynomial.C delta⁻¹ * (Polynomial.C delta * Polynomial.X) =
      Polynomial.X := by
    rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hdelta,
      Polynomial.C_1, one_mul]
  rw [hX, Polynomial.comp_X]

theorem ratScaleBy_inv_comp (delta : ℂ) (hdelta : delta ≠ 0) :
    (ratScaleBy delta⁻¹ (inv_ne_zero hdelta)).comp
        (ratScaleBy delta hdelta) = RingHom.id (RatFunc ℂ) := by
  apply IsFractionRing.ringHom_ext (A := Polynomial ℂ)
  intro p
  rw [RingHom.comp_apply, RingHom.id_apply, ratScaleBy_algebraMap,
    ratScaleBy_algebraMap]
  congr 1
  rw [Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.X_comp]
  have hX : Polynomial.C delta * (Polynomial.C delta⁻¹ * Polynomial.X) =
      Polynomial.X := by
    rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hdelta,
      Polynomial.C_1, one_mul]
  rw [hX, Polynomial.comp_X]

noncomputable def ratScaleEquiv (delta : ℂ) (hdelta : delta ≠ 0) :
    RatFunc ℂ ≃+* RatFunc ℂ where
  toFun := ratScaleBy delta hdelta
  invFun := ratScaleBy delta⁻¹ (inv_ne_zero hdelta)
  left_inv := fun r => RingHom.congr_fun (ratScaleBy_inv_comp delta hdelta) r
  right_inv := fun r => RingHom.congr_fun (ratScaleBy_comp_inv delta hdelta) r
  map_add' := map_add _
  map_mul' := map_mul _

/-- Coordinate dilation as a rescaled differential automorphism over `ℂ(X)`. -/
noncomputable def complexScaleDifferentialRescaledEquiv
    (delta : ℂ) (hdelta : delta ≠ 0) :
    DifferentialRescaledEquiv (RatFunc ℂ) (meroField Set.univ) where
  baseEquiv := ratScaleEquiv delta hdelta
  ambientEquiv := complexScaleMeroEquiv delta hdelta
  factor := RatFunc.C delta
  factor_ne_zero := by simpa using hdelta
  map_algebraMap' := fun r => complexScaleMeroEquiv_ratfuncToMero delta hdelta r
  map_deriv' := by
    intro x
    rw [complexScaleMeroEquiv_deriv delta hdelta x,
      ratFuncC_toMero_eq_complex_natScale]
    change algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ delta) * complexScaleMeroEquiv delta hdelta x′ =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ delta) * complexScaleMeroEquiv delta hdelta x′
    rfl

/-- Differential algebraicity over the rational coordinate field is invariant under every
nonzero complex coordinate dilation. -/
theorem differentialAlgebraicOver_complexScaleMeroEquiv_iff
    (delta : ℂ) (hdelta : delta ≠ 0) (x : meroField Set.univ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (complexScaleMeroEquiv delta hdelta x) ↔
      DifferentialAlgebraicOver (RatFunc ℂ) x :=
  (complexScaleDifferentialRescaledEquiv delta hdelta).differentialAlgebraicOver_map_iff x

end
end GaloisForLFunctions.HTGeometry
