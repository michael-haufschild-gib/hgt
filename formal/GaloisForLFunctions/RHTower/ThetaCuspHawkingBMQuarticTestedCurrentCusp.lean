import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticResponseWork
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalAngularCutoffCalibration
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspMeanDerivative
import GaloisForLFunctions.HTGeometry.ComplexCoordinateDerivativeRules

/-!
# Physical-clock cusp balance of the complete tested incoming radial current

The original two-response angular current and source-contact current retain the
physical scalar test, its differentiated work, and the local half-square squared.
Literal modular side matching and finite-cusp Stokes retain both vertical
endpoints. The original common-clock translation moment then equals the exact
boundary-minus-work balance, with arbitrary original scalar amplitudes.

The result is a finite identity for the incoming radial sector. It does not
assign zero to the boundary or source work, pass to an infinite-height finite
part, or assert complete physical-action extinction. Frequencies are unchanged.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff MatrixGroups
namespace RHTower.D4BMQuarticTestedCurrentCusp
open D4BMModularCore D4BMGlobalAngularResponse D4BMJointSource D4BMCuspResponse
open D4BMQuarticResponseWork D4BMIncomingClockTranslation D4BMFullIncomingCurrent
open D4BMAngularSeries D4BMHorizon
noncomputable section
set_option autoImplicit false

/-- Both original angular currents, with the unchanged physical coefficients. -/
def completeCurrent (q : XiZeroCopy) (j : Fin 2) (w : Fin 2 → ℝ) : ℂ :=
  -(D4BMModularCore.physicalRate q true*D4BMModularCore.physicalRate q false/3)*
    angularResponseGreen q j w+reducedSourceCurrent q j w

/-- The physical scalar test multiplies the entire original angular current. -/
def testedCurrent (q : XiZeroCopy) (j : Fin 2) (w : Fin 2 → ℝ) : ℂ :=
  scalar (physicalAngularParameter q) w*completeCurrent q j w

/-- Work caused by differentiating the original physical scalar test. -/
def testDerivativeWork (q : XiZeroCopy) (w : Fin 2 → ℝ) : ℂ :=
  ∑ j : Fin 2, coordDeriv j (scalar (physicalAngularParameter q)) w*completeCurrent q j w

private theorem scalar_smooth (u : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (scalar u) z :=
  (cuspLeg_contDiffOn .scalar u).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)

private theorem square_smooth (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (fullSquarePotential q) z := by
  exact contDiffAt_const.mul ((scalar_smooth (center q) z hz).mul (scalar_smooth (center q) z hz))

private theorem current_parts_smooth (q : XiZeroCopy) (j : Fin 2) (z : Fin 2 → ℝ)
    (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (angularResponseGreen q j) z ∧
      ContDiffAt ℝ ∞ (reducedSourceCurrent q j) z := by
  have hH := fullAngularField_smooth q true z hz
  have hK := fullAngularField_smooth q false z hz
  have hQ := square_smooth q z hz
  have dH := ScalarTwoJet.coordDeriv_contDiffAt hH (by simp : (∞:ℕ∞ω)+1≤∞) j
  have dK := ScalarTwoJet.coordDeriv_contDiffAt hK (by simp : (∞:ℕ∞ω)+1≤∞) j
  have dQ := ScalarTwoJet.coordDeriv_contDiffAt hQ (by simp : (∞:ℕ∞ω)+1≤∞) j
  constructor
  · exact ((contDiffAt_const.mul dH).mul (hK.add hQ)).sub
      ((contDiffAt_const.mul dK).mul (hH.add hQ))
  · exact hQ.mul (((contDiffAt_const.mul dH).add
      (contDiffAt_const.mul dK)).add (contDiffAt_const.mul dQ))

private theorem completeCurrent_smooth (q : XiZeroCopy) (j : Fin 2) (z : Fin 2 → ℝ)
    (hz : 0 < z 1) : ContDiffAt ℝ ∞ (completeCurrent q j) z :=
  (contDiffAt_const.mul (current_parts_smooth q j z hz).1).add (current_parts_smooth q j z hz).2

private theorem testedCurrent_smooth (q : XiZeroCopy) (j : Fin 2) (z : Fin 2 → ℝ)
    (hz : 0 < z 1) : ContDiffAt ℝ ∞ (testedCurrent q j) z :=
  (scalar_smooth (physicalAngularParameter q) z hz).mul (completeCurrent_smooth q j z hz)

private theorem complete_divergence (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    (∑ j : Fin 2, coordDeriv j (completeCurrent q j) z) =
      -(D4BMModularCore.physicalRate q true*D4BMModularCore.physicalRate q false/3)*
        (∑ j : Fin 2, coordDeriv j (angularResponseGreen q j) z)+
        ∑ j : Fin 2, coordDeriv j (reducedSourceCurrent q j) z := by
  have he (j : Fin 2) : coordDeriv j (completeCurrent q j) z =
      -(D4BMModularCore.physicalRate q true*D4BMModularCore.physicalRate q false/3)*
        coordDeriv j (angularResponseGreen q j) z+coordDeriv j (reducedSourceCurrent q j) z := by
    have hG := ((current_parts_smooth q j z hz).1.differentiableAt (by simp)).hasFDerivAt
    have hS := ((current_parts_smooth q j z hz).2.differentiableAt (by simp)).hasFDerivAt
    have h := (hG.const_mul (-(D4BMModularCore.physicalRate q true*D4BMModularCore.physicalRate q false/3))).add hS
    change HasFDerivAt (completeCurrent q j) _ z at h
    rw [coordDeriv,h.fderiv]
    rfl
  simp only [he,Finset.sum_add_distrib,Finset.mul_sum]

/-- Testing the complete current retains the physical test's differentiated contribution. -/
theorem testedCurrent_divergence (q : XiZeroCopy) (z : UpperHalfPlane) :
    (∑ j : Fin 2, coordDeriv j (testedCurrent q j) (coordinates z)) =
      testDerivativeWork q (coordinates z)+scalar (physicalAngularParameter q) (coordinates z)*
        (∑ j : Fin 2, coordDeriv j (completeCurrent q j) (coordinates z)) := by
  have hT := (scalar_smooth (physicalAngularParameter q) (coordinates z) z.im_pos).differentiableAt (by simp)
  have hC (j : Fin 2) := (completeCurrent_smooth q j (coordinates z) z.im_pos).differentiableAt (by simp)
  have he (j : Fin 2) : coordDeriv j (testedCurrent q j) (coordinates z)=
      coordDeriv j (scalar (physicalAngularParameter q)) (coordinates z)*completeCurrent q j (coordinates z)+
        scalar (physicalAngularParameter q) (coordinates z)*coordDeriv j (completeCurrent q j) (coordinates z) :=
    ScalarTwoJet.coordDeriv_mul hT (hC j) j
  simp only [he,testDerivativeWork,Finset.sum_add_distrib,Finset.mul_sum]

/-- Exact physical radial balance after testing; the complete local and response source work remains. -/
theorem tested_radial_balance (q : XiZeroCopy) (a b : ℂ) (z : UpperHalfPlane) :
    scalar (physicalAngularParameter q) (coordinates z)*clockCoefficients q a b (coordinates z) 1 0 =
      4*(a^2*b^2/64)*((∑ j : Fin 2, coordDeriv j (testedCurrent q j) (coordinates z))-
        testDerivativeWork q (coordinates z)-
        scalar (physicalAngularParameter q) (coordinates z)*reducedSourceWork q (coordinates z)/(z.im:ℂ)^2) := by
  have he := incoming_radial_mass_reduced_source_work q a b z
  dsimp only at he
  rw [show coordinates z 1=z.im from rfl] at he
  have he' : (z.im:ℂ)^2*clockCoefficients q a b (coordinates z) 1 0=
      4*(a^2*b^2/64)*((z.im:ℂ)^2*(∑ j : Fin 2,
        coordDeriv j (completeCurrent q j) (coordinates z))-reducedSourceWork q (coordinates z)) := by
    rw [complete_divergence q (coordinates z) z.im_pos]
    linear_combination he
  rw [testedCurrent_divergence]
  have hz : (z.im:ℂ)≠0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
  apply (mul_right_inj' (pow_ne_zero 2 hz)).mp
  field_simp [hz] at he' ⊢
  linear_combination scalar (physicalAngularParameter q) (coordinates z)*he'


private theorem periodic_coordDeriv {f : (Fin 2 → ℝ) → ℂ}
    (hf : Function.Periodic f ![1,0]) (i : Fin 2) : Function.Periodic (coordDeriv i f) ![1,0] := by
  intro z
  have he : (fun w => f (w+![1,0]))=f := funext hf
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := z) ![1,0]
  rw [he] at hd
  exact congrArg (fun L => L (Pi.single i 1)) hd.symm

private theorem scalar_periodic (u : ℂ) : Function.Periodic (scalar u) ![1,0] := by
  intro z
  simpa [scalar,Pi.add_apply] using d4BM_completedEisensteinCuspLeg_scalar_periodic u (z 1) (z 0)

private theorem response_periodic (q : XiZeroCopy) (b : Bool) :
    Function.Periodic (fullAngularField q b) ![1,0] := by
  intro z
  have him (w : Fin 2 → ℝ) : (angularCoordinates.symm w).im=w 1 := by
    change ((w 0:ℂ)+(w 1:ℂ)*Complex.I).im=w 1
    simp
  have hre (w : Fin 2 → ℝ) : (angularCoordinates.symm w).re=w 0 := by
    change ((w 0:ℂ)+(w 1:ℂ)*Complex.I).re=w 0
    simp
  by_cases hz : 0 < z 1
  · have hp : 0 < (angularCoordinates.symm z).im := by rw [him]; exact hz
    have hp' : 0 < (angularCoordinates.symm (z+![1,0])).im := by simpa only [him,Pi.add_apply,Matrix.cons_val_one,Matrix.cons_val_fin_one,add_zero] using hz
    have ht : ofComplex (angularCoordinates.symm (z+![1,0]))=T • ofComplex (angularCoordinates.symm z) := by
      rw [ofComplex_apply_of_im_pos hp,ofComplex_apply_of_im_pos hp']
      apply UpperHalfPlane.ext_re_im
      · rw [ModularGroup.re_T_smul]
        change (angularCoordinates.symm (z+![1,0])).re=(angularCoordinates.symm z).re+1
        rw [hre,hre]
        rfl
      · rw [ModularGroup.im_T_smul]
        change (angularCoordinates.symm (z+![1,0])).im=(angularCoordinates.symm z).im
        rw [him,him]
        change z 1+0=z 1
        exact add_zero _
    have hi := fullAngular_invariant q b (QuotientGroup.mk T) (ofComplex (angularCoordinates.symm z))
    simpa only [fullAngularField,ht,PSL2Z_mk_smul] using hi
  · have hp : (angularCoordinates.symm z).im≤0 := by rw [him]; exact le_of_not_gt hz
    have hp' : (angularCoordinates.symm (z+![1,0])).im≤0 := by simpa only [him,Pi.add_apply,Matrix.cons_val_one,Matrix.cons_val_fin_one,add_zero] using le_of_not_gt hz
    exact congrArg (fullAngular q b) (ofComplex_apply_eq_of_im_nonpos hp' hp)

/-- The entire physical tested current, including source contacts, matches across the cusp sides. -/
theorem testedCurrent_periodic (q : XiZeroCopy) (j : Fin 2) :
    Function.Periodic (testedCurrent q j) ![1,0] := by
  have hH := response_periodic q true
  have hK := response_periodic q false
  have hQ : Function.Periodic (fullSquarePotential q) ![1,0] := by
    intro z
    change (1/2:ℂ)*(scalar (center q) (z+![1,0])*scalar (center q) (z+![1,0]))=_
    rw [scalar_periodic (center q) z]
    rfl
  have dH := periodic_coordDeriv hH j
  have dK := periodic_coordDeriv hK j
  have dQ := periodic_coordDeriv hQ j
  intro z
  change scalar (physicalAngularParameter q) (z+![1,0])*
    (_*(parameter q false*coordDeriv j (fullAngularField q true) (z+![1,0])*
      (fullAngularField q false (z+![1,0])+fullSquarePotential q (z+![1,0]))-
      parameter q true*coordDeriv j (fullAngularField q false) (z+![1,0])*
      (fullAngularField q true (z+![1,0])+fullSquarePotential q (z+![1,0])))+
      fullSquarePotential q (z+![1,0])*(_*coordDeriv j (fullAngularField q true) (z+![1,0])+
      _*coordDeriv j (fullAngularField q false) (z+![1,0])+_*coordDeriv j (fullSquarePotential q) (z+![1,0])))=_
  rw [scalar_periodic (physicalAngularParameter q) z,hH z,hK z,hQ z,dH z,dK z,dQ z]
  rfl

private def planarCurrent (q : XiZeroCopy) (j : Fin 2) : ℂ → ℂ :=
  testedCurrent q j ∘ angularCoordinates

private theorem planarCurrent_smooth (q : XiZeroCopy) (j : Fin 2) :
    ContDiffOn ℝ ∞ (planarCurrent q j) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact ((testedCurrent_smooth q j (angularCoordinates z) hz).comp z
    angularCoordinates.contDiff.contDiffAt).contDiffWithinAt

private def divergenceField (q : XiZeroCopy) (z : ℂ) : ℂ :=
  horizontal (planarCurrent q 0) z+vertical (planarCurrent q 1) z

private theorem divergenceField_eq (q : XiZeroCopy) (z : ℂ) :
    divergenceField q z=∑ j : Fin 2,coordDeriv j (testedCurrent q j) (angularCoordinates z) := by
  have h0 := angularCoordinates_derivative (testedCurrent q 0) 0 z
  have h1 := angularCoordinates_derivative (testedCurrent q 1) 1 z
  rw [Fin.sum_univ_two]
  exact congrArg₂ (·+·) h0 h1

private theorem divergenceField_smooth (q : XiZeroCopy) :
    ContDiffOn ℝ ∞ (divergenceField q) {z : ℂ | 0 < z.im} :=
  (planar_derivative_contDiffOn (planarCurrent_smooth q 0) (1:ℂ)).add
    (planar_derivative_contDiffOn (planarCurrent_smooth q 1) Complex.I)

/-- Original physical tested vertical current on a full width-one cusp section. -/
def cuspBoundary (q : XiZeroCopy) : ℝ → ℂ := D4BMCuspResponse.average (planarCurrent q 1)

/-- Mean of the full tested-current divergence in the original planar chart. -/
def cuspDivergenceDensity (q : XiZeroCopy) : ℝ → ℂ := D4BMCuspResponse.average (divergenceField q)

private theorem horizontal_current_mean_zero (q : XiZeroCopy) {y : ℝ} (hy : 0 < y) :
    D4BMCuspResponse.average (horizontal (planarCurrent q 0)) y=0 := by
  have hs := planarCurrent_smooth q 0
  have hd := planar_derivative_contDiffOn hs (1:ℂ)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (-1/2:ℝ)) (b := (1/2:ℝ))
    (fun x _ => slice_horizontal_derivative (planarCurrent q 0) hs y hy x)
    ((slice_continuous (horizontal (planarCurrent q 0)) hd hy).intervalIntegrable _ _)
  rw [intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2)] at he
  change D4BMCuspResponse.average (horizontal (planarCurrent q 0)) y=_ at he
  rw [he]
  have hp := testedCurrent_periodic q 0 (angularCoordinates (point (-1/2) y))
  have hc : angularCoordinates (point (1/2) y)=angularCoordinates (point (-1/2) y)+![1,0] := by
    ext i
    fin_cases i <;> norm_num [angularCoordinates,point,Pi.add_apply]
  exact sub_eq_zero.mpr (by change testedCurrent q 0 _=testedCurrent q 0 _; rw [hc]; exact hp)

/-- Cusp differentiation cancels exactly the periodic horizontal side current. -/
theorem cuspBoundary_hasDerivAt (q : XiZeroCopy) (y : Ioi (0:ℝ)) :
    HasDerivAt (cuspBoundary q) (cuspDivergenceDensity q y) y := by
  have hv := average_hasDerivAt (planarCurrent q 1) (planarCurrent_smooth q 1) y.2
  have h0 := (slice_continuous (horizontal (planarCurrent q 0))
    (planar_derivative_contDiffOn (planarCurrent_smooth q 0) (1:ℂ)) y.2).integrableOn_Ioc (μ := (volume : Measure ℝ)) (a := (-1/2:ℝ)) (b := (1/2:ℝ))
  have h1 := (slice_continuous (vertical (planarCurrent q 1))
    (planar_derivative_contDiffOn (planarCurrent_smooth q 1) Complex.I) y.2).integrableOn_Ioc (μ := (volume : Measure ℝ)) (a := (-1/2:ℝ)) (b := (1/2:ℝ))
  have he : cuspDivergenceDensity q y=D4BMCuspResponse.average (vertical (planarCurrent q 1)) y := by
    change (∫ x in Ioc (-1/2:ℝ) (1/2),
      horizontal (planarCurrent q 0) (point x y)+vertical (planarCurrent q 1) (point x y))=_
    rw [integral_add h0 h1]
    change D4BMCuspResponse.average (horizontal (planarCurrent q 0)) y+_=_
    rw [horizontal_current_mean_zero q y.2,zero_add]
    rfl
  exact hv.congr_deriv he.symm

private theorem divergence_intervalIntegrable (q : XiZeroCopy) (a c : Ioi (0:ℝ)) :
    IntervalIntegrable (cuspDivergenceDensity q) volume (a:ℝ) c := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  exact (average_hasDerivAt (divergenceField q) (divergenceField_smooth q)
    ((lt_min a.2 c.2).trans_le hy.1)).continuousAt.continuousWithinAt

/-- Finite-cusp Stokes for the actual tested current retains both vertical endpoints. -/
theorem testedCurrent_finite_cusp_stokes (q : XiZeroCopy) (a c : Ioi (0:ℝ)) :
    (∫ y in (a:ℝ)..c, cuspDivergenceDensity q y)=cuspBoundary q c-cuspBoundary q a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => cuspBoundary_hasDerivAt q ⟨y,(lt_min a.2 c.2).trans_le hy.1⟩)
    (divergence_intervalIntegrable q a c)

private def workField (q : XiZeroCopy) (w : Fin 2 → ℝ) : ℂ :=
  testDerivativeWork q w+scalar (physicalAngularParameter q) w*reducedSourceWork q w/(w 1:ℂ)^2

private theorem workField_smooth (q : XiZeroCopy) (w : Fin 2 → ℝ) (hw : 0 < w 1) :
    ContDiffAt ℝ ∞ (workField q) w := by
  have hQ := square_smooth q w hw
  have hH := fullAngularField_smooth q true w hw
  have hK := fullAngularField_smooth q false w hw
  have hT := scalar_smooth (physicalAngularParameter q) w hw
  have hW : ContDiffAt ℝ ∞ (reducedSourceWork q) w :=
    (((contDiffAt_const.mul hQ).mul hH).add
      ((contDiffAt_const.mul hQ).mul hK)).add
      (contDiffAt_const.mul (hQ.pow 2))
  have hD : ContDiffAt ℝ ∞ (testDerivativeWork q) w := by
    change ContDiffAt ℝ ∞ (fun z => ∑ j : Fin 2,
      coordDeriv j (scalar (physicalAngularParameter q)) z*completeCurrent q j z) w
    simp only [Fin.sum_univ_two]
    exact ((ScalarTwoJet.coordDeriv_contDiffAt hT (by simp : (∞:ℕ∞ω)+1≤∞) 0).mul
      (completeCurrent_smooth q 0 w hw)).add
      ((ScalarTwoJet.coordDeriv_contDiffAt hT (by simp : (∞:ℕ∞ω)+1≤∞) 1).mul
        (completeCurrent_smooth q 1 w hw))
  have hh : ContDiffAt ℝ ∞ (fun z : Fin 2 → ℝ => (z 1:ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w (contDiff_apply ℝ ℝ (1:Fin 2)).contDiffAt
  have hd := hh.pow 2
  change ContDiffAt ℝ ∞ (fun z => testDerivativeWork q z+
    scalar (physicalAngularParameter q) z*reducedSourceWork q z/(z 1:ℂ)^2) w
  simpa only [div_eq_mul_inv] using
    hD.add ((hT.mul hW).mul (hd.fun_inv (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hw.ne'))))

private theorem planarWork_smooth (q : XiZeroCopy) :
    ContDiffOn ℝ ∞ (workField q ∘ angularCoordinates) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact ((workField_smooth q (angularCoordinates z) hz).comp z
    angularCoordinates.contDiff.contDiffAt).contDiffWithinAt

/-- All test-derivative work and the full two-response/local-square source work. -/
def completeTestedWorkDensity (q : XiZeroCopy) : ℝ → ℂ :=
  D4BMCuspResponse.average (workField q ∘ angularCoordinates)

/-- The actual physical scalar test applied to the original radial clock-mass coefficient. -/
def radialTestDensity (q : XiZeroCopy) (a b : ℂ) : ℝ → ℂ :=
  D4BMCuspResponse.average (fun z => scalar (physicalAngularParameter q) (angularCoordinates z)*
    clockCoefficients q a b (angularCoordinates z) 1 0)

/-- Mean physical radial law with the entire differentiated test and source work. -/
theorem radialTestDensity_eq (q : XiZeroCopy) (a b : ℂ) (y : Ioi (0:ℝ)) :
    radialTestDensity q a b y=4*(a^2*b^2/64)*
      (cuspDivergenceDensity q y-completeTestedWorkDensity q y) := by
  have hD := (slice_continuous (divergenceField q) (divergenceField_smooth q) y.2).integrableOn_Ioc (μ := (volume : Measure ℝ)) (a := (-1/2:ℝ)) (b := (1/2:ℝ))
  have hW := (slice_continuous (workField q ∘ angularCoordinates) (planarWork_smooth q) y.2).integrableOn_Ioc (μ := (volume : Measure ℝ)) (a := (-1/2:ℝ)) (b := (1/2:ℝ))
  dsimp only [Function.comp_apply] at hW
  calc
    _ = D4BMCuspResponse.average (fun z => 4*(a^2*b^2/64)*
        (divergenceField q z-workField q (angularCoordinates z))) y := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x _
      have hp : 0 < (point x y).im := by
        rw [show (point x (y:ℝ)).im=(y:ℝ) by simp [point]]
        exact y.2
      have h := tested_radial_balance q a b ⟨point x y,hp⟩
      dsimp only [workField]
      rw [divergenceField_eq]
      change scalar (physicalAngularParameter q) (angularCoordinates (point x y))*
        clockCoefficients q a b (angularCoordinates (point x y)) 1 0=
          4*(a^2*b^2/64)*((∑ j : Fin 2, coordDeriv j (testedCurrent q j) (angularCoordinates (point x y)))-
            testDerivativeWork q (angularCoordinates (point x y))-
            scalar (physicalAngularParameter q) (angularCoordinates (point x y))*
              reducedSourceWork q (angularCoordinates (point x y))/(angularCoordinates (point x y) 1:ℂ)^2) at h
      linear_combination h
    _ = _ := by
      change (∫ x in Ioc (-1/2:ℝ) (1/2), 4*(a^2*b^2/64)*
        (divergenceField q (point x y)-workField q (angularCoordinates (point x y))))=_
      rw [integral_const_mul,integral_sub hD hW]
      rfl

/-- Full finite-cusp physical radial balance, including both endpoints and every source-work term. -/
theorem physical_radial_finite_cusp_balance (q : XiZeroCopy) (a b : ℂ) (l r : Ioi (0:ℝ)) :
    (∫ y in (l:ℝ)..r, radialTestDensity q a b y)=4*(a^2*b^2/64)*
      (cuspBoundary q r-cuspBoundary q l-
        ∫ y in (l:ℝ)..r, completeTestedWorkDensity q y) := by
  have hw : IntervalIntegrable (completeTestedWorkDensity q) volume (l:ℝ) r := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    exact (average_hasDerivAt (workField q ∘ angularCoordinates) (planarWork_smooth q)
      ((lt_min l.2 r.2).trans_le hy.1)).continuousAt.continuousWithinAt
  calc
    _ = ∫ y in (l:ℝ)..r, 4*(a^2*b^2/64)*
        (cuspDivergenceDensity q y-completeTestedWorkDensity q y) := by
      apply intervalIntegral.integral_congr
      intro y hy
      exact radialTestDensity_eq q a b ⟨y,(lt_min l.2 r.2).trans_le hy.1⟩
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (divergence_intervalIntegrable q l r) hw,
        testedCurrent_finite_cusp_stokes]


open D4BMSourceClockTranslation

/-- Finite translation moment of the original physical incoming radial current at its common clock. -/
def physicalClockDensity (q : XiZeroCopy) (a b : ℂ) (h : NNReal) : ℝ → ℂ :=
  D4BMCuspResponse.average (fun z => scalar (physicalAngularParameter q) (angularCoordinates z)*
    clockMoment (-6) h (fun u => incomingCurrent q a b 1 u (angularCoordinates z) 1))

/-- The common-clock moment selects the original radial coefficient without changing any source frequency. -/
theorem physicalClockDensity_eq (q : XiZeroCopy) (a b : ℂ) (h : NNReal) (y : ℝ) :
    physicalClockDensity q a b h y=(h:ℂ)*Complex.exp (-6*(h:ℂ))*radialTestDensity q a b y := by
  change (∫ x in Ioc (-1/2:ℝ) (1/2), scalar (physicalAngularParameter q) (angularCoordinates (point x y))*
    clockMoment (-6) h (fun u => incomingCurrent q a b 1 u (angularCoordinates (point x y)) 1))=
      (h:ℂ)*Complex.exp (-6*(h:ℂ))*(∫ x in Ioc (-1/2:ℝ) (1/2),
        scalar (physicalAngularParameter q) (angularCoordinates (point x y))*
          clockCoefficients q a b (angularCoordinates (point x y)) 1 0)
  simp_rw [incomingCurrent_horizon_clockMoment]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  ring

/-- Exact finite physical-clock cusp balance retains both tested endpoints and complete source work. -/
theorem physical_clock_finite_cusp_balance (q : XiZeroCopy) (a b : ℂ) (h : NNReal)
    (l r : Ioi (0:ℝ)) :
    (∫ y in (l:ℝ)..r, physicalClockDensity q a b h y)=
      (h:ℂ)*Complex.exp (-6*(h:ℂ))*4*(a^2*b^2/64)*
        (cuspBoundary q r-cuspBoundary q l-
          ∫ y in (l:ℝ)..r, completeTestedWorkDensity q y) := by
  simp_rw [physicalClockDensity_eq]
  rw [intervalIntegral.integral_const_mul,physical_radial_finite_cusp_balance]
  ring


end
end RHTower.D4BMQuarticTestedCurrentCusp
