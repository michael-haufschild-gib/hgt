import GaloisForLFunctions.RHTower.SuzukiVolterraCartesianPhaseDefect

/-!
# Source-germ rigidity for Suzuki's relative Volterra phase route

The finite Volterra boundary data contribute an analytic local correction to the exterior Weyl
quotient.  The global Xi logarithmic derivative is the only off-real pole carrier.  Consequently
one analytic upper-half-plane pointed germ for the Euler defect exists exactly when RH holds.
-/

open Complex Filter Set Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Exact source-transparency normal form -/

/-- Away from the sewn characteristic divisor, the actual exterior Weyl quotient is an analytic
local correction minus the universal zero-shift Xi multiplier. -/
theorem suzukiAffineSewnExteriorWeylQuotient_eq_localCorrection_sub_xiMultiplier
    (alpha beta : ℂ)
    (WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ) {z : ℂ}
    (hP : suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z ≠ 0) :
    suzukiAffineSewnExteriorWeylQuotient alpha beta
        WAlpha WBeta rightAlpha rightBeta z =
      suzukiReflectionOddPart
          (suzukiAffineSewnIntervalPart alpha beta 0
            WAlpha WBeta rightAlpha rightBeta) z /
          suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z -
        suzukiShiftedXiMultiplier 0 z := by
  simp only [suzukiAffineSewnExteriorWeylQuotient,
    suzukiAffineSewnOddCarlemanPoleCarrier, suzukiExteriorWeylQuotient,
    suzukiOddCarlemanPoleCarrier]
  field_simp [hP]
  ring

/-! ## RH supplies the analytic source package -/

/-- Under RH, the Euler defect of every admissible affine-sewn exterior Weyl quotient is analytic
at each nonreal point.  This is the reverse half missing from the earlier one-way connector. -/
theorem analyticAt_suzukiAffineSewnExteriorWeylEulerDefect_of_riemannHypothesis
    {alpha beta : ℂ}
    {WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ}
    (hab : alpha ≠ beta)
    (hWAlpha : ∀ w, AnalyticAt ℂ WAlpha w)
    (hWBeta : ∀ w, AnalyticAt ℂ WBeta w)
    (hRAlpha : ∀ w, AnalyticAt ℂ rightAlpha w)
    (hRBeta : ∀ w, AnalyticAt ℂ rightBeta w)
    (hrealAlpha : ∀ w, WAlpha w = 0 → w.im = 0)
    (hrealBeta : ∀ w, WBeta w = 0 → w.im = 0)
    (hRH : RiemannHypothesis) {z : ℂ} (hz : z.im ≠ 0) :
    AnalyticAt ℂ
      (GaloisForLFunctions.RHTower.suzukiEulerDefect
        (suzukiAffineSewnExteriorWeylQuotient alpha beta
          WAlpha WBeta rightAlpha rightBeta)) z := by
  let P : ℂ → ℂ := suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta
  let right : ℂ → ℂ :=
    suzukiAffineSewnIntervalPart alpha beta 0 WAlpha WBeta rightAlpha rightBeta
  let C : ℂ → ℂ :=
    suzukiAffineSewnOddCarlemanPoleCarrier alpha beta
      WAlpha WBeta rightAlpha rightBeta
  let m : ℂ → ℂ :=
    suzukiAffineSewnExteriorWeylQuotient alpha beta
      WAlpha WBeta rightAlpha rightBeta
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    exact hz (by simp)
  have hXi : XiC z ≠ 0 := by
    intro hzero
    exact hz
      ((SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero.mp hRH)
        z hzero)
  have hM : AnalyticAt ℂ (suzukiShiftedXiMultiplier 0) z :=
    analyticAt_suzukiShiftedXiMultiplier_of_XiC_ne_zero hz0 hXi
  have hP : AnalyticAt ℂ P z :=
    analyticAt_suzukiAffineSewnCharacteristic (hWAlpha z) (hWBeta z)
  have hP0 : P z ≠ 0 := by
    exact suzukiAffineSewnCharacteristic_ne_zero_of_im_ne_zero
      hab hrealAlpha hrealBeta hz
  have hright : ∀ w, AnalyticAt ℂ right w := fun w =>
    analyticAt_suzukiAffineSewnIntervalPart
      (hWAlpha w) (hWBeta w) (hRAlpha w) (hRBeta w)
  have hodd : AnalyticAt ℂ (suzukiReflectionOddPart right) z :=
    analyticAt_suzukiReflectionOddPart hright z
  have hC : AnalyticAt ℂ C z := by
    change AnalyticAt ℂ
      (fun w => suzukiShiftedXiMultiplier 0 w * P w -
        suzukiReflectionOddPart right w) z
    exact (hM.mul hP).sub hodd
  have hm : AnalyticAt ℂ m z := by
    change AnalyticAt ℂ (fun w => -C w / P w) z
    exact hC.neg.div hP hP0
  change AnalyticAt ℂ (fun w => w * deriv m w - m w) z
  exact (analyticAt_id.mul hm.deriv).sub hm

/-- Under RH the actual exterior Euler defect is analytic on the whole upper half-plane. -/
theorem analyticOnNhd_suzukiAffineSewnExteriorWeylEulerDefect_of_riemannHypothesis
    {alpha beta : ℂ}
    {WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ}
    (hab : alpha ≠ beta)
    (hWAlpha : ∀ w, AnalyticAt ℂ WAlpha w)
    (hWBeta : ∀ w, AnalyticAt ℂ WBeta w)
    (hRAlpha : ∀ w, AnalyticAt ℂ rightAlpha w)
    (hRBeta : ∀ w, AnalyticAt ℂ rightBeta w)
    (hrealAlpha : ∀ w, WAlpha w = 0 → w.im = 0)
    (hrealBeta : ∀ w, WBeta w = 0 → w.im = 0)
    (hRH : RiemannHypothesis) :
    AnalyticOnNhd ℂ
      (GaloisForLFunctions.RHTower.suzukiEulerDefect
        (suzukiAffineSewnExteriorWeylQuotient alpha beta
          WAlpha WBeta rightAlpha rightBeta))
      UpperHalfPlane.upperHalfPlaneSet := by
  intro z hz
  apply analyticAt_suzukiAffineSewnExteriorWeylEulerDefect_of_riemannHypothesis
    hab hWAlpha hWBeta hRAlpha hRBeta hrealAlpha hrealBeta hRH
  have hzpos : 0 < z.im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using hz
  exact ne_of_gt hzpos

/-! ## Exact pointed-germ classification -/

/-- **Source-germ rigidity.** For every admissible boundary package, existence of one analytic
upper-half-plane source with one pointed germ equal to the actual Euler defect is equivalent to RH.
The reverse implication is exact pole tomography; the forward witness is the analytic defect
itself under RH. -/
theorem riemannHypothesis_iff_exists_suzukiAffineSewnExteriorWeylEulerDefect_source_germ_weld
    {alpha beta : ℂ}
    {WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ}
    (hab : alpha ≠ beta)
    (hWAlpha : ∀ w, AnalyticAt ℂ WAlpha w)
    (hWBeta : ∀ w, AnalyticAt ℂ WBeta w)
    (hRAlpha : ∀ w, AnalyticAt ℂ rightAlpha w)
    (hRBeta : ∀ w, AnalyticAt ℂ rightBeta w)
    (hrealAlpha : ∀ w, WAlpha w = 0 → w.im = 0)
    (hrealBeta : ∀ w, WBeta w = 0 → w.im = 0) :
    RiemannHypothesis ↔
      ∃ (D : ℂ → ℂ) (u : ℂ),
        AnalyticOnNhd ℂ D UpperHalfPlane.upperHalfPlaneSet ∧
        u ∈ UpperHalfPlane.upperHalfPlaneSet ∧
        GaloisForLFunctions.RHTower.suzukiEulerDefect
            (suzukiAffineSewnExteriorWeylQuotient alpha beta
              WAlpha WBeta rightAlpha rightBeta) =ᶠ[𝓝[≠] u] D := by
  constructor
  · intro hRH
    let m : ℂ → ℂ :=
      suzukiAffineSewnExteriorWeylQuotient alpha beta
        WAlpha WBeta rightAlpha rightBeta
    let D : ℂ → ℂ := GaloisForLFunctions.RHTower.suzukiEulerDefect m
    refine ⟨D, Complex.I, ?_, ?_, ?_⟩
    · dsimp only [D, m]
      exact analyticOnNhd_suzukiAffineSewnExteriorWeylEulerDefect_of_riemannHypothesis
        hab hWAlpha hWBeta hRAlpha hRBeta hrealAlpha hrealBeta hRH
    · simp [UpperHalfPlane.upperHalfPlaneSet]
    · exact Filter.EventuallyEq.rfl
  · rintro ⟨D, u, hD, hu, hseed⟩
    exact riemannHypothesis_of_suzukiAffineSewnExteriorWeylEulerDefect_source_germ_weld
      hab hWAlpha hWBeta hRAlpha hRBeta hrealAlpha hrealBeta hD hu hseed

/-- **Route G2 closure.** After substituting the actual relative-Volterra phase boundary
responses, the proposed analytic source-germ package is exactly equivalent to RH. Thus the phase
algebra is unconditional, but constructing its missing source germ is the RH-bearing theorem
rather than routine Volterra infrastructure. -/
theorem riemannHypothesis_iff_exists_suzukiVolterraPhaseEulerDefect_source_germ_weld
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {alpha beta : ℂ}
    {WAlpha WBeta : ℂ → ℂ}
    (rightEuler rightNeumann : ℂ → V →ₗ[ℂ] ℂ)
    (uAlpha uBeta : V)
    (hab : alpha ≠ beta)
    (hWAlpha : ∀ z, AnalyticAt ℂ WAlpha z)
    (hWBeta : ∀ z, AnalyticAt ℂ WBeta z)
    (hRightAlpha : ∀ z, AnalyticAt ℂ
      (suzukiXiRealRightVolterraBoundaryResponse
        rightEuler rightNeumann alpha uAlpha) z)
    (hRightBeta : ∀ z, AnalyticAt ℂ
      (suzukiXiRealRightVolterraBoundaryResponse
        rightEuler rightNeumann beta uBeta) z)
    (hrealAlpha : ∀ z, WAlpha z = 0 → z.im = 0)
    (hrealBeta : ∀ z, WBeta z = 0 → z.im = 0) :
    RiemannHypothesis ↔
      ∃ (DSource : ℂ → ℂ) (seed : ℂ),
        AnalyticOnNhd ℂ DSource UpperHalfPlane.upperHalfPlaneSet ∧
        seed ∈ UpperHalfPlane.upperHalfPlaneSet ∧
        GaloisForLFunctions.RHTower.suzukiEulerDefect
            (suzukiAffineSewnExteriorWeylQuotient alpha beta
              WAlpha WBeta
              (suzukiXiRealRightVolterraBoundaryResponse
                rightEuler rightNeumann alpha uAlpha)
              (suzukiXiRealRightVolterraBoundaryResponse
                rightEuler rightNeumann beta uBeta)) =ᶠ[𝓝[≠] seed] DSource := by
  exact riemannHypothesis_iff_exists_suzukiAffineSewnExteriorWeylEulerDefect_source_germ_weld
    hab hWAlpha hWBeta hRightAlpha hRightBeta hrealAlpha hrealBeta

end
end RHTower

