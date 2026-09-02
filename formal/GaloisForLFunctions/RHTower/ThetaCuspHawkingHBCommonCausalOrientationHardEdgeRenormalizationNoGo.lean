import GaloisForLFunctions.RHTower.ThetaCuspHawkingHBPeierlsStationaryChannelElimination
import GaloisForLFunctions.HTGeometry.PointSupportStructure

/-!
# HB common-causal-orientation hard-edge renormalization no-go

The exact nonlinear Einstein--Teukolsky Peierls cut depends only on retarded-minus-advanced
response maps.  This file classifies the effect of arbitrary additive response renormalizations:
their contribution is exactly the difference between their two causal orientations.  Hence any
correction used identically in the retarded and advanced problems cancels before cokernel
projection.  It cannot create, remove, or tune an HB causal-cut zero.

The singular hard-edge survivor has an equally sharp local form.  An order-one distribution
supported at the hard edge sees only the value and first derivative of a Schwartz test.  Under
causal reflection `x ↦ -x`, the value term is even and the derivative term is odd.  Its causal jump
is therefore exactly twice the derivative-delta charge; the delta charge is invisible.

Together these kill the route

`common local/distributional hard-edge renormalization → radiative ++ extinction → RH`.

The positive survivor is exact: a local scaling-degree-two completion must derive an
orientation-odd boundary first jet from the physical source.  Otherwise it must leave this class
through nonlocal, sheet-changing, or more singular dynamics.

`[NEW] [HB] [PEIERLS] [DISTRIBUTIONS] [ROUTE KILL] [LEAN-PROVED]`
-/

open Complex Set SchwartzMap

namespace RHTower

noncomputable section

variable {X Y : Type*}
  [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

/-- Exact change of the nonlinear causal cut under independently renormalized retarded and
advanced response maps.  Only the orientation-odd correction differences survive. -/
theorem d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_correction_sub_eq_orientationOdd
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X)
    (KppRet KpmRet KppAdv KpmAdv : Y →ₗ[ℂ] X) (p m : X) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut
        B C (RppRet + KppRet) (RpmRet + KpmRet)
          (RppAdv + KppAdv) (RpmAdv + KpmAdv) p m -
      d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut
        B C RppRet RpmRet RppAdv RpmAdv p m =
      B p ((KpmRet - KpmAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m)) +
      B m ((KppRet - KppAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p)) := by
  have hpm : (RpmRet + KpmRet) - (RpmAdv + KpmAdv) =
      (RpmRet - RpmAdv) + (KpmRet - KpmAdv) := by module
  have hpp : (RppRet + KppRet) - (RppAdv + KppAdv) =
      (RppRet - RppAdv) + (KppRet - KppAdv) := by module
  have hpmApply :
      B p (((RpmRet + KpmRet) - (RpmAdv + KpmAdv))
          (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m)) =
        B p ((RpmRet - RpmAdv)
          (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m)) +
        B p ((KpmRet - KpmAdv)
          (d4GaugeFixedTeukolskyQuadraticPlusMinusResidual B p m)) := by
    rw [hpm]
    exact map_add (B p) _ _
  have hppApply :
      B m (((RppRet + KppRet) - (RppAdv + KppAdv))
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p)) =
        B m ((RppRet - RppAdv)
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p)) +
        B m ((KppRet - KppAdv)
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p)) := by
    rw [hpp]
    exact map_add (B m) _ _
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_eq_resolventJump,
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_eq_resolventJump,
    hpmApply, hppApply]
  abel

/-- A response correction common to both causal orientations is invisible to the full nonlinear
Einstein--Teukolsky causal cut. -/
theorem d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_invariant_commonResponseCorrection
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv Kpp Kpm : Y →ₗ[ℂ] X) (p m : X) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut
        B C (RppRet + Kpp) (RpmRet + Kpm) (RppAdv + Kpp) (RpmAdv + Kpm) p m =
      d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut
        B C RppRet RpmRet RppAdv RpmAdv p m := by
  have hpm : (RpmRet + Kpm) - (RpmAdv + Kpm) = RpmRet - RpmAdv := by module
  have hpp : (RppRet + Kpp) - (RppAdv + Kpp) = RppRet - RppAdv := by module
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_eq_resolventJump,
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_eq_resolventJump,
    hpm, hpp]

/-- Common response renormalization is also invisible after left-cokernel projection. -/
theorem
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_invariant_commonResponseCorrection
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv Kpp Kpm : Y →ₗ[ℂ] X) (p m : X) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        ell B C (RppRet + Kpp) (RpmRet + Kpm) (RppAdv + Kpp) (RpmAdv + Kpm) p m =
      d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        ell B C RppRet RpmRet RppAdv RpmAdv p m := by
  unfold d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_invariant_commonResponseCorrection]

/-- No common response counterterm can tune a projected causal-cut zero. -/
theorem
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_commonCorrection_eq_zero_iff
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (RppRet RpmRet RppAdv RpmAdv Kpp Kpm : Y →ₗ[ℂ] X) (p m : X) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        ell B C (RppRet + Kpp) (RpmRet + Kpm) (RppAdv + Kpp) (RpmAdv + Kpm) p m = 0 ↔
      d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        ell B C RppRet RpmRet RppAdv RpmAdv p m = 0 := by
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_invariant_commonResponseCorrection]

/-- In a physical Peierls realization every admissible mixed-channel correction is again a causal
self-pairing and disappears.  The corrected cut sees exactly the orientation-odd radiative `++`
correction. -/
theorem
    d4GaugeFixedTeukolskyRenormalizedCokernelCausalCut_eq_radiativeOrientationOdd_of_Peierls
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Delta : Y →ₗ[ℂ] X)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X)
    (KppRet KpmRet KppAdv KpmAdv : Y →ₗ[ℂ] X) (p m : X)
    (hB : ∀ x y, B x y = B y x)
    (hcyclic : ∀ x y z, pairing x (B y z) = pairing z (B x y))
    (hRpm : (RpmRet + KpmRet) - (RpmAdv + KpmAdv) = Delta)
    (hskew : ∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        (pairing m) B C (RppRet + KppRet) (RpmRet + KpmRet)
          (RppAdv + KppAdv) (RpmAdv + KpmAdv) p m =
      pairing m (B m ((RppRet - RppAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p))) +
      pairing m (B m ((KppRet - KppAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p))) := by
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq_radiative_of_Peierls
    pairing B C Delta (RppRet + KppRet) (RpmRet + KpmRet)
      (RppAdv + KppAdv) (RpmAdv + KpmAdv) p m hB hcyclic hRpm hskew]
  have hpp : (RppRet + KppRet) - (RppAdv + KppAdv) =
      (RppRet - RppAdv) + (KppRet - KppAdv) := by module
  rw [hpp]
  change pairing m (B m
      ((RppRet - RppAdv) (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p) +
        (KppRet - KppAdv) (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p))) = _
  rw [map_add (B m), map_add (pairing m)]

/-- Closed Peierls classification: after stationary-channel elimination the full renormalization
freedom is the orientation-odd radiative `++` correction. -/
def D4HBPeierlsResponseCorrectionOrientationOddClassified : Prop :=
  ∀ (X Y : Type) [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Delta : Y →ₗ[ℂ] X)
    (RppRet RpmRet RppAdv RpmAdv : Y →ₗ[ℂ] X)
    (KppRet KpmRet KppAdv KpmAdv : Y →ₗ[ℂ] X) (p m : X),
    (∀ x y, B x y = B y x) →
    (∀ x y z, pairing x (B y z) = pairing z (B x y)) →
    (RpmRet + KpmRet) - (RpmAdv + KpmAdv) = Delta →
    (∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f) →
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        (pairing m) B C (RppRet + KppRet) (RpmRet + KpmRet)
          (RppAdv + KppAdv) (RpmAdv + KpmAdv) p m =
      pairing m (B m ((RppRet - RppAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p))) +
      pairing m (B m ((KppRet - KppAdv)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual B p)))

/-- Premise-free certificate of the exact Peierls response-renormalization classification. -/
theorem d4HBPeierlsResponseCorrectionOrientationOddClassified :
    D4HBPeierlsResponseCorrectionOrientationOddClassified := by
  intro X Y _ _ _ _ pairing B C Delta RppRet RpmRet RppAdv RpmAdv
    KppRet KpmRet KppAdv KpmAdv p m hB hcyclic hRpm hskew
  exact
    d4GaugeFixedTeukolskyRenormalizedCokernelCausalCut_eq_radiativeOrientationOdd_of_Peierls
      pairing B C Delta RppRet RpmRet RppAdv RpmAdv
        KppRet KpmRet KppAdv KpmAdv p m hB hcyclic hRpm hskew

/-- Reflection of a Schwartz test through the hard edge. -/
def d4HBHardEdgeCausalReflect (φ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv) φ

@[simp] theorem d4HBHardEdgeCausalReflect_apply (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    d4HBHardEdgeCausalReflect φ x = φ (-x) := rfl

/-- The first boundary jet is odd under causal reflection. -/
theorem iteratedDeriv_one_d4HBHardEdgeCausalReflect_zero (φ : SchwartzMap ℝ ℂ) :
    iteratedDeriv 1 (d4HBHardEdgeCausalReflect φ : ℝ → ℂ) 0 =
      -iteratedDeriv 1 (φ : ℝ → ℂ) 0 := by
  simp only [iteratedDeriv_succ', iteratedDeriv_zero]
  have hfun : (d4HBHardEdgeCausalReflect φ : ℝ → ℂ) =
      fun x : ℝ => (φ : ℝ → ℂ) (-x) := by
    funext x
    exact d4HBHardEdgeCausalReflect_apply φ x
  rw [hfun]
  simpa using deriv_comp_neg (φ : ℝ → ℂ) 0

/-- Order-one point-supported hard-edge distributions see only the boundary value and first
derivative.  This is the one-dimensional scaling-degree-two ambiguity class. -/
def D4HBHardEdgePointSupportedOrderOne
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (u : SchwartzMap ℝ ℂ →L[ℂ] Z) : Prop :=
  ∀ φ : SchwartzMap ℝ ℂ,
    (φ : ℝ → ℂ) 0 = 0 →
    iteratedDeriv 1 (φ : ℝ → ℂ) 0 = 0 →
    u φ = 0

/-- Exact delta/delta-derivative representation of an order-one hard-edge correction. -/
theorem d4HBHardEdgePointSupportedOrderOne_apply_eq_boundaryJets
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (u : SchwartzMap ℝ ℂ →L[ℂ] Z) (hu : D4HBHardEdgePointSupportedOrderOne u)
    (φ : SchwartzMap ℝ ℂ) :
    u φ = ((φ : ℝ → ℂ) 0) • u (GaloisForLFunctions.HTGeometry.jetTest 0) +
      (iteratedDeriv 1 (φ : ℝ → ℂ) 0) •
        u (GaloisForLFunctions.HTGeometry.jetTest 1) := by
  open GaloisForLFunctions.HTGeometry in
    let a : ℂ := (φ : ℝ → ℂ) 0
    let b : ℂ := iteratedDeriv 1 (φ : ℝ → ℂ) 0
    let ψ : SchwartzMap ℝ ℂ := φ - a • jetTest 0 - b • jetTest 1
    have hj00 : (jetTest 0 : ℝ → ℂ) 0 = 1 := by
      simpa [iteratedDeriv_zero] using iteratedDeriv_jetTest_zero 0 0
    have hj10 : (jetTest 1 : ℝ → ℂ) 0 = 0 := by
      simpa [iteratedDeriv_zero] using iteratedDeriv_jetTest_zero 0 1
    have hψ0 : (ψ : ℝ → ℂ) 0 = 0 := by
      change (φ : ℝ → ℂ) 0 - a * (jetTest 0 : ℝ → ℂ) 0 -
        b * (jetTest 1 : ℝ → ℂ) 0 = 0
      rw [hj00, hj10]
      simp [a]
    have hφcd : ContDiffAt ℝ (1 : ℕ∞) (φ : ℝ → ℂ) 0 :=
      ((φ.smooth').of_le (by exact_mod_cast le_top)).contDiffAt
    have hjcd : ∀ j : ℕ, ContDiffAt ℝ (1 : ℕ∞) (jetTest j : ℝ → ℂ) 0 := fun j =>
      (((jetTest j).smooth').of_le (by exact_mod_cast le_top)).contDiffAt
    have hψ1 : iteratedDeriv 1 (ψ : ℝ → ℂ) 0 = 0 := by
      have hcoe : (ψ : ℝ → ℂ) =
          ((φ : ℝ → ℂ) - a • (jetTest 0 : ℝ → ℂ) - b • (jetTest 1 : ℝ → ℂ)) := by
        funext x
        simp [ψ]
      rw [hcoe]
      simp only [iteratedDeriv_succ', iteratedDeriv_zero]
      have hφd : DifferentiableAt ℝ (φ : ℝ → ℂ) 0 :=
        hφcd.differentiableAt (by norm_num)
      have hjd : ∀ j : ℕ, DifferentiableAt ℝ (jetTest j : ℝ → ℂ) 0 := fun j =>
        (hjcd j).differentiableAt (by norm_num)
      rw [deriv_sub (hφd.sub ((hjd 0).const_smul a)) ((hjd 1).const_smul b),
        deriv_sub hφd ((hjd 0).const_smul a),
        deriv_const_smul a (hjd 0), deriv_const_smul b (hjd 1)]
      have hj01 : deriv (jetTest 0 : ℝ → ℂ) 0 = 0 := by
        simpa [iteratedDeriv_succ', iteratedDeriv_zero] using
          iteratedDeriv_jetTest_zero 1 0
      have hj11 : deriv (jetTest 1 : ℝ → ℂ) 0 = 1 := by
        simpa [iteratedDeriv_succ', iteratedDeriv_zero] using
          iteratedDeriv_jetTest_zero 1 1
      rw [hj01, hj11]
      simp [b, iteratedDeriv_succ', iteratedDeriv_zero]
    have hzero := hu ψ hψ0 hψ1
    have hmap : u ψ = u φ - a • u (jetTest 0) - b • u (jetTest 1) := by
      simp [ψ]
    rw [hmap] at hzero
    change u φ = a • u (jetTest 0) + b • u (jetTest 1)
    have hfirst : u φ - a • u (jetTest 0) = b • u (jetTest 1) :=
      sub_eq_zero.mp hzero
    calc
      u φ = (u φ - a • u (jetTest 0)) + a • u (jetTest 0) := by abel
      _ = b • u (jetTest 1) + a • u (jetTest 0) := by rw [hfirst]
      _ = a • u (jetTest 0) + b • u (jetTest 1) := by abel

/-- Sharp local survivor: causal reflection kills the delta charge and extracts exactly twice the
derivative-delta boundary charge. -/
theorem d4HBHardEdgePointSupportedOrderOne_causalReflectionJump_eq_two_derivativeCharge
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (u : SchwartzMap ℝ ℂ →L[ℂ] Z) (hu : D4HBHardEdgePointSupportedOrderOne u)
    (φ : SchwartzMap ℝ ℂ) :
    u φ - u (d4HBHardEdgeCausalReflect φ) =
      (2 * iteratedDeriv 1 (φ : ℝ → ℂ) 0) •
        u (GaloisForLFunctions.HTGeometry.jetTest 1) := by
  open GaloisForLFunctions.HTGeometry in
    rw [d4HBHardEdgePointSupportedOrderOne_apply_eq_boundaryJets u hu φ,
      d4HBHardEdgePointSupportedOrderOne_apply_eq_boundaryJets
        u hu (d4HBHardEdgeCausalReflect φ)]
    rw [iteratedDeriv_one_d4HBHardEdgeCausalReflect_zero]
    simp only [d4HBHardEdgeCausalReflect_apply, neg_zero]
    module

/-- Closed route class: neither a common retarded/advanced response correction nor its even
point-supported hard-edge charge can tune the nonlinear HB causal cut. -/
def D4HBCommonCausalOrientationHardEdgeRenormalizationRouteKilled : Prop :=
  D4HBPeierlsResponseCorrectionOrientationOddClassified ∧
  (∀ (X Y : Type) [AddCommGroup X] [Module ℂ X]
      [AddCommGroup Y] [Module ℂ Y]
      (ell : Y →ₗ[ℂ] ℂ)
      (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
      (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
      (RppRet RpmRet RppAdv RpmAdv Kpp Kpm : Y →ₗ[ℂ] X) (p m : X),
      d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
          ell B C (RppRet + Kpp) (RpmRet + Kpm) (RppAdv + Kpp) (RpmAdv + Kpm) p m = 0 ↔
        d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
          ell B C RppRet RpmRet RppAdv RpmAdv p m = 0) ∧
    (∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℂ Z]
      (u : SchwartzMap ℝ ℂ →L[ℂ] Z),
      D4HBHardEdgePointSupportedOrderOne u →
      ∀ φ : SchwartzMap ℝ ℂ,
        u φ - u (d4HBHardEdgeCausalReflect φ) =
          (2 * iteratedDeriv 1 (φ : ℝ → ℂ) 0) •
            u (GaloisForLFunctions.HTGeometry.jetTest 1))

/-- Premise-free certificate killing common-causal-orientation local/distributional hard-edge
renormalization as the missing HB producer. -/
theorem d4HBCommonCausalOrientationHardEdgeRenormalizationRouteKilled :
    D4HBCommonCausalOrientationHardEdgeRenormalizationRouteKilled := by
  constructor
  · exact d4HBPeierlsResponseCorrectionOrientationOddClassified
  · constructor
    · intro X Y _ _ _ _ ell B C RppRet RpmRet RppAdv RpmAdv Kpp Kpm p m
      exact
        d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_commonCorrection_eq_zero_iff
          ell B C RppRet RpmRet RppAdv RpmAdv Kpp Kpm p m
    · intro Z _ _ u hu φ
      exact d4HBHardEdgePointSupportedOrderOne_causalReflectionJump_eq_two_derivativeCharge
        u hu φ

end

end RHTower
