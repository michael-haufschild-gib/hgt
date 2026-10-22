import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMModeActionReconstruction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMTemporalOppositeCurrentProfile
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMTemporalCurrentHorizonRestoration

/-!
# Original mixed correction and the incoming temporal QNM action

Identify the original mixed Einstein correction's metric and complete first jet, derive its
source-envelope radial derivative, and evaluate its temporal action against an independent left
stream. The incoming horizon density has a uniform quadratic jet and an analytic restored value
at every physical fundamental QNM. Subtracting this finite part preserves the original incoming
temporal pole coefficient exactly. Its finite value and both cutoff counterterms are retained.

This concerns the incoming temporal contribution. It does not identify the complete raw-source
Peierls pairing, join the opposite/radial/angular/outer faces, prove Hawking-clock extinction, or
prove RH. No source covariance or incidence conclusion is assumed.
-/

namespace RHTower.D4BMCorrectionAction
open Complex Set Filter Topology Metric MeasureTheory
open GaloisForLFunctions.HTGeometry D4BMMixedActionCurrent D4BMPhysicalModeAction
open D4BMJointSource D4BMLaplaceRadial D4BMModularCore D4BMJointWave
noncomputable section
set_option autoImplicit false

/-- The time-angular correction's first jet, with arbitrary retained angular derivatives. -/
def temporalMetricJet (w c cr : ℂ) (J : Fin 2 → ScalarTwoJet (Fin 2) ℂ) :
    CoordinateMetricTwoJet 4 ℂ :=
  mixedJet (fun a => c * (J a).value) (fun _ => 0)
    (fun k a => ![w*c*(J a).value, cr*(J a).value, c*(J a).first 0,
      c*(J a).first 1] k) (fun _ _ => 0)

/-- Both original angular covectors remain in the correction/left-mode pairing. -/
def angularPair (J K : Fin 2 → ScalarTwoJet (Fin 2) ℂ) : ℂ :=
  ∑ a : Fin 2, (J a).value * (K a).value

/-- Exact temporal Einstein density of the correction against the left stream. -/
theorem temporal_action (p : D4BMBackground.ExteriorPoint)
    (w c cr d dr drr : ℂ) (J K : Fin 2 → ScalarTwoJet (Fin 2) ℂ) :
    (p.val 1:ℂ)^(2 : ℕ)/(p.val 3:ℂ)^(2 : ℕ) * actionSymplectic
      (D4BMBackground.jet (p.val 1) (p.val 3))
      (temporalMetricJet w c cr J)
      (streamMetricJet (p.val 1) (fun a => staticStreamJet (-w) d dr drr (K a))) 0 =
      w*d/((p.val 1:ℂ)^(2 : ℕ)-1) * (cr-2*c/(p.val 1:ℂ)) * angularPair J K := by
  unfold temporalMetricJet streamMetricJet
  rw [mixed_complete_action_current]
  simp [completeCurrentDensity, staticStreamJet, angularPair, Fin.sum_univ_succ]
  ring

/-- The literal correction coefficient after retaining the original onset transform. -/
def correctionRadial (s w a T : ℂ) (r : ℝ) : ℂ :=
  s*(s+1)/2 * sourceAmplitude s w a T (D4BMIngoingCoordinates.tortoise r) *
    ((r:ℂ)^(2 : ℕ)-1)/(r:ℂ)^(3 : ℕ)

/-- The exact radial derivative minus the temporal curvature term in the Einstein current. -/
def correctionReducedDerivative (s w a T : ℂ) (r : ℝ) : ℂ :=
  s*(s+1)/2 * sourceAmplitude s w a T (D4BMIngoingCoordinates.tortoise r) *
    ((w-2*s)/(r:ℂ)^(3 : ℕ)-3/(r:ℂ)^(2 : ℕ)+(5+2*s)/(r:ℂ)^(4 : ℕ))

/-- Differentiate the actual source envelope at the original exterior radius. -/
theorem correctionRadial_hasDerivAt (s w a T : ℂ) (t : ℝ) (ht : t < 0) :
    HasDerivAt (correctionRadial s w a T)
      (correctionReducedDerivative s w a T (tortoiseRadius t) +
        2 * correctionRadial s w a T (tortoiseRadius t) / (tortoiseRadius t:ℂ))
      (tortoiseRadius t) := by
  let r := tortoiseRadius t
  have hr : 1 < r := tortoiseRadius_exterior t ht
  have h0 : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hF : (r:ℂ)^(2 : ℕ)-1 ≠ 0 := by exact_mod_cast (show r^(2 : ℕ)-1 ≠ 0 by nlinarith)
  have hR := (hasDerivAt_id r).ofReal_comp
  have hA := (sourceAmplitude_hasDerivAt s w a T (D4BMIngoingCoordinates.tortoise r)).scomp r
    (D4BMIngoingCoordinates.tortoise_hasDerivAt r hr)
  apply (((hA.const_mul (s*(s+1)/2)).mul ((hR.pow 2).sub_const 1)).div (hR.pow 3)
    (pow_ne_zero 3 h0)).congr_deriv
  simp only [correctionReducedDerivative, correctionRadial, Complex.real_smul,
    Function.comp_apply, Pi.pow_apply, Pi.mul_apply, id_eq]
  rw [show D4BMIngoingCoordinates.tortoise r = t from tortoise_original_inverse t ht]
  rw [amplitudeRate, radialUnit_inverse_radius]
  change _ = s*(s+1)/2*sourceAmplitude s w a T t*
    ((w-2*s)/(r:ℂ)^(3 : ℕ)-3/(r:ℂ)^(2 : ℕ)+(5+2*s)/(r:ℂ)^(4 : ℕ)) +
    2*(s*(s+1)/2*sourceAmplitude s w a T t*((r:ℂ)^(2 : ℕ)-1)/(r:ℂ)^(3 : ℕ))/(r:ℂ)
  push_cast
  simp only [show tortoiseRadius t = r from rfl]
  field_simp
  ring

/-- The correction's incoming temporal profile, with the original onset transform. -/
def temporalProfile (q : XiZeroCopy) (branch : Bool) (a angular : ℂ) (w : ℂ) (z : ℝ) : ℂ :=
  w * (physicalRate q branch * (physicalRate q branch+1) / 2) * angular / 2 *
    amplitudeProfile (physicalRate q branch) a (continuedOnset (physicalRate q branch)) w z *
    gaussProfile q w z *
    ((w-2*physicalRate q branch)*(Real.sqrt (1-z):ℂ)-3+
      (5+2*physicalRate q branch)*(Real.sqrt (1-z):ℂ)^(2 : ℕ))

/-- Quadratic horizon control is derived from the literal amplitude and left Gauss mode. -/
theorem temporalProfile_germ (q : XiZeroCopy) (branch side : Bool) (a angular : ℂ) :
    AnalyticJet2At (physicalFundamentalFrequency q side) (temporalProfile q branch a angular) := by
  let w₀ := physicalFundamentalFrequency q side
  let s := physicalRate q branch
  have hs : w₀ - 2*s ≠ 0 := physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  have hA := amplitudeProfile_germ s a (continuedOnset s) (continuedOnset_analyticAt s w₀ hs)
  have hU := AnalyticJet2At.sqrt_one_sub w₀
  have hP := (((hU.const_mul (k := fun w => w-2*s)
    (analyticAt_id.sub analyticAt_const)).sub
    (AnalyticJet2At.const (k := fun _ => (3:ℂ)) analyticAt_const)).add
    ((hU.pow 2).const_mul (k := fun _ => 5+2*s) analyticAt_const))
  exact (((hA.mul (gaussProfile_germ q side)).mul hP).const_mul
    (k := fun w => w*(s*(s+1)/2)*angular/2)
    (((analyticAt_id.mul analyticAt_const).mul analyticAt_const).div_const)).congr
      (fun w z => by dsimp [temporalProfile, s]; ring)

/-- Spatial continuity of the actual correction horizon profile. -/
theorem temporalProfile_continuousAt (q : XiZeroCopy) (branch : Bool) (a angular w : ℂ)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    ContinuousAt (temporalProfile q branch a angular w) z := by
  have hA := amplitudeProfile_continuousAt (physicalRate q branch) a
    (continuedOnset (physicalRate q branch)) w z
  have hG := gaussProfile_continuousAt q w hz
  have hU : ContinuousAt (fun x : ℝ => (Real.sqrt (1-x):ℂ)) z := by fun_prop
  exact ((continuousAt_const.mul hA).mul hG).mul
    (((continuousAt_const.mul hU).sub continuousAt_const).add
      (continuousAt_const.mul (hU.pow 2)))

/-- Frequency analyticity includes the fixed source onset, with its pole kept separate. -/
theorem temporalProfile_analyticAt (q : XiZeroCopy) (branch : Bool) (a angular w : ℂ)
    (hw : w.im ≠ 0) (hs : w-2*physicalRate q branch ≠ 0)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    AnalyticAt ℂ (fun u => temporalProfile q branch a angular u z) w := by
  have hbase : ((1+Real.sqrt (1-z):ℝ):ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1+Real.sqrt (1-z) by positivity))
  have hpow : AnalyticAt ℂ (fun u : ℂ =>
      ((1+Real.sqrt (1-z):ℝ):ℂ)^(2*physicalRate q branch-u)) w :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      ((differentiable_const _ |>.sub differentiable_id).const_cpow (Or.inl hbase))) w (mem_univ _)
  have hA : AnalyticAt ℂ (fun u => amplitudeProfile (physicalRate q branch) a
      (continuedOnset (physicalRate q branch)) u z) w :=
    hpow.mul (analyticAt_const.mul (continuedOnset_analyticAt _ _ hs))
  exact (((((analyticAt_id.mul analyticAt_const).mul analyticAt_const).div_const).mul hA).mul
    (gaussProfile_analyticAt q w hw hz)).mul
    ((((analyticAt_id.sub analyticAt_const).mul analyticAt_const).sub analyticAt_const).add
      analyticAt_const)

/-- Radial Jacobian applied to the correction/ingoing-left temporal Einstein density. -/
def incomingTemporalDensity (q : XiZeroCopy) (branch : Bool) (a angular w : ℂ) (z : ℝ) : ℂ :=
  w*(tortoiseRadius (tortoiseOf z):ℂ)*horizon w (physicalRadialFrequency q) z *
    correctionReducedDerivative (physicalRate q branch) w a
      (continuedOnset (physicalRate q branch) w) (tortoiseRadius (tortoiseOf z)) * angular /
    (2*(z:ℂ)*(Real.sqrt (1-z):ℂ))

/-- The restored integrand is identified with the original radius and literal source amplitude. -/
theorem incomingTemporalDensity_eq (q : XiZeroCopy) (branch : Bool) (a angular w : ℂ)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    incomingTemporalDensity q branch a angular w z =
      (z:ℂ)^(w-1)*temporalProfile q branch a angular w z := by
  let t := tortoiseOf z
  let r := tortoiseRadius t
  have ht : t < 0 := tortoiseOf_neg hz
  have hr : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (lt_trans (by norm_num) (tortoiseRadius_exterior t ht)))
  have hz0 : (z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.1.ne'
  have hU : (Real.sqrt (1-z):ℂ) = (r:ℂ)⁻¹ := by
    have h := (radialUnit_eq_sqrt t ht).symm
    rw [horizonCoordinate_tortoiseOf hz, radialUnit_inverse_radius] at h
    exact_mod_cast h
  have hp : (z:ℂ)^(w/2)*(z:ℂ)^(w/2) = (z:ℂ)^(w-1)*(z:ℂ) := by
    calc
      _ = (z:ℂ)^(w/2+w/2) := (Complex.cpow_add _ _ hz0).symm
      _ = (z:ℂ)^(w-1+1) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ hz0, Complex.cpow_one]
  unfold incomingTemporalDensity correctionReducedDerivative
  rw [tortoise_original_inverse t ht, sourceAmplitude_eq_profile _ _ _ w t ht,
    horizonCoordinate_tortoiseOf hz, horizon_eq_pow_mul]
  unfold temporalProfile gaussProfile
  rw [hU]
  dsimp only [r, t] at hr ⊢
  let C := w*(tortoiseRadius (tortoiseOf z):ℂ)*
    gaussFactor w (physicalRadialFrequency q) false (z:ℂ)*
    (physicalRate q branch*(physicalRate q branch+1)/2)*
    amplitudeProfile (physicalRate q branch) a (continuedOnset (physicalRate q branch)) w z *
    ((w-2*physicalRate q branch)/(tortoiseRadius (tortoiseOf z):ℂ)^(3 : ℕ)-
      3/(tortoiseRadius (tortoiseOf z):ℂ)^(2 : ℕ)+
      (5+2*physicalRate q branch)/(tortoiseRadius (tortoiseOf z):ℂ)^(4 : ℕ))*angular /
    (2*(z:ℂ)*(tortoiseRadius (tortoiseOf z):ℂ)⁻¹)
  calc
    _ = ((z:ℂ)^(w/2)*(z:ℂ)^(w/2))*C := by dsimp [C]; ring
    _ = ((z:ℂ)^(w-1)*(z:ℂ))*C := by rw [hp]
    _ = _ := by dsimp [C]; field_simp


/-- The correction's horizon contribution has an analytic restored value, not an assumed zero
value. Both power counterterms remain in the original cutoff limit. -/
theorem temporalProfile_restoration (q : XiZeroCopy) (branch side : Bool) (a angular : ℂ) :
    ∃ R B : ℝ, ∃ c₀ c₁ : ℂ → ℂ, 0 < R ∧ 0 < B ∧ B ≤ 1/2 ∧
      ∀ b : ℝ, 0 < b → b ≤ B →
        AnalyticAt ℂ (QuadraticEndpointMellin.finitePart
          (temporalProfile q branch a angular) c₀ c₁ b) (physicalFundamentalFrequency q side) ∧
        Tendsto (fun w => (w-physicalFundamentalFrequency q side) *
          QuadraticEndpointMellin.finitePart (temporalProfile q branch a angular) c₀ c₁ b w)
          (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 0) ∧
        ∀ w ∈ ball (physicalFundamentalFrequency q side) R,
          Tendsto (fun e : ℝ =>
            (∫ z in e..b, (z:ℂ)^(w-1)*temporalProfile q branch a angular w z) +
              c₀ w*(e:ℂ)^w/w+c₁ w*(e:ℂ)^(w+1)/(w+1))
            (𝓝[>] (0:ℝ))
            (𝓝 (QuadraticEndpointMellin.finitePart (temporalProfile q branch a angular) c₀ c₁ b w)) := by
  let w₀ := physicalFundamentalFrequency q side
  have hw : w₀.im ≠ 0 := (physicalFundamentalFrequency_strip q side).1
  have hwr : -2 < w₀.re := (abs_lt.mp (physicalFundamentalFrequency_strip q side).2).1
  have hs : w₀-2*physicalRate q branch ≠ 0 :=
    physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  obtain ⟨RJ, B, hRJ, hB, hBh, c₀, c₁, C, hC, ha₀, ha₁, hjet⟩ :=
    temporalProfile_germ q branch side a angular
  let β := (w₀.re-2)/2
  have hβ : -2 < β := by dsimp [β]; linarith
  have hr : ∀ᶠ u : ℂ in 𝓝 w₀, β < u.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt
      (by dsimp [β]; linarith)
  have hsource : ∀ᶠ u : ℂ in 𝓝 w₀, u-2*physicalRate q branch ≠ 0 :=
    (continuousAt_id.sub continuousAt_const).eventually_ne hs
  obtain ⟨RA, hRA, hdata⟩ := Metric.eventually_nhds_iff.mp
    ((Complex.continuous_im.continuousAt.eventually_ne hw).and
      (hr.and (hsource.and (ha₀.eventually_analyticAt.and ha₁.eventually_analyticAt))))
  let R := min RJ RA
  have hR : 0 < R := lt_min hRJ hRA
  have hd (u : ℂ) (hu : u ∈ ball w₀ R) :=
    hdata (mem_ball.mp (ball_subset_ball (min_le_right RJ RA) hu))
  have hJ (u : ℂ) (hu : u ∈ ball w₀ R) : u ∈ closedBall w₀ RJ :=
    ball_subset_closedBall (ball_subset_ball (min_le_left RJ RA) hu)
  refine ⟨R, B, c₀, c₁, hR, hB, hBh, ?_⟩
  intro b hb hbB
  have hb1 : b < 1 := by linarith
  have hsp (u : ℂ) (_hu : u ∈ ball w₀ R) :
      ContinuousOn (temporalProfile q branch a angular u) (Ioc (0:ℝ) b) := by
    intro z hz
    exact (temporalProfile_continuousAt q branch a angular u
      ⟨hz.1, hz.2.trans_lt hb1⟩).continuousWithinAt
  have hbound (u : ℂ) (hu : u ∈ ball w₀ R) (z : ℝ) (hz : z ∈ Ioc (0:ℝ) b) :=
    hjet u (hJ u hu) z ⟨hz.1, hz.2.trans hbB⟩
  have hnonzero (u : ℂ) (hui : u.im ≠ 0) : u ≠ 0 ∧ u+1 ≠ 0 := by
    constructor
    · intro h; apply hui; simp [h]
    · intro h; apply hui; have := congrArg Complex.im h; simpa using this
  have hA : AnalyticAt ℂ (QuadraticEndpointMellin.finitePart
      (temporalProfile q branch a angular) c₀ c₁ b) w₀ :=
    QuadraticEndpointMellin.finitePart_analyticAt hb hb1.le hR hC hβ
      (hnonzero w₀ hw).1 (hnonzero w₀ hw).2
      (fun u hu => (hd u hu).2.1.le) hsp
      (fun u hu => (hd u hu).2.2.2)
      (fun z hz u hu => temporalProfile_analyticAt q branch a angular u (hd u hu).1
        (hd u hu).2.2.1 ⟨hz.1, hz.2.trans_lt hb1⟩) hbound
  refine ⟨hA, ?_, ?_⟩
  · have hx : Tendsto (fun u : ℂ => u-w₀) (𝓝[≠] w₀) (𝓝 0) := by
      have hi : Tendsto (fun u : ℂ => u) (𝓝[≠] w₀) (𝓝 w₀) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [sub_self] using hi.sub_const w₀
    simpa only [zero_mul] using hx.mul (hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  intro u hu
  simpa only [add_assoc] using QuadraticEndpointMellin.cutoff_tendsto hb
    (hβ.trans (hd u hu).2.1) (hnonzero u (hd u hu).1).1 (hnonzero u (hd u hu).1).2
    (hsp u hu) (hbound u hu)

/-- An Einstein action current depends only on the metric and its first coordinate jet. -/
theorem actionSymplectic_congr_first {d : ℕ} (J H H' K : CoordinateMetricTwoJet d ℂ)
    (hm : H.metric = H'.metric) (hf : H.first = H'.first) (i : Fin d) :
    actionSymplectic J H K i = actionSymplectic J H' K i := by
  have hleft : actionCurrentPath J H K i = actionCurrentPath J H' K i := by
    funext t
    simp only [actionCurrentPath, EinsteinActionBoundary.current,
      CoordinateMetricTwoJet.Linearization.connection, CoordinateMetricTwoJet.Linearization.inverse,
      CoordinateMetricTwoJet.Linearization.affine, hm, hf]
  have hright : actionCurrentPath J K H i = actionCurrentPath J K H' i := by
    funext t
    simp only [actionCurrentPath, EinsteinActionBoundary.current,
      CoordinateMetricTwoJet.Linearization.connection, CoordinateMetricTwoJet.Linearization.inverse,
      CoordinateMetricTwoJet.Linearization.affine, hm, hf]
  unfold actionSymplectic
  rw [hleft, hright]

/-- The original scalar/coexact-vector product, retaining its complete angular first jet. -/
def originalAngularJet (s y S Sx Sy Sxx Sxy : ℂ) : Fin 2 → ScalarTwoJet (Fin 2) ℂ :=
  ![⟨S*Sy, ![Sx*Sy+S*Sxy, Sy^(2 : ℕ)+S*((s+1)*(s+2)*S/y^(2 : ℕ)-Sxx)], fun _ _ => 0⟩,
    ⟨-S*Sx, ![-Sx^(2 : ℕ)-S*Sxx, -Sy*Sx-S*Sxy], fun _ _ => 0⟩]

def originalRadial (s r B : ℂ) : ℂ := s*(s+1)/2*B^(2 : ℕ)*(r^(2 : ℕ)-1)/r^(3 : ℕ)

def originalRadialFirst (s r B : ℂ) : ℂ := s*(s+1)/2*B^(2 : ℕ)*(-1/r^(2 : ℕ)+(2*s+3)/r^(4 : ℕ))


private def originalRadialJet (s r B : ℂ) : ScalarTwoJet (Fin 4) ℂ :=
  let R := D4BMScalarLinearEquation.coord r 1
  let F := (R.mul R).add (ScalarTwoJet.constant (-1))
  (((ScalarTwoJet.constant (s*(s+1)/2)).mul
    (D4BMScalarLinearEquation.temporalRadial (2*s) r (B^(2 : ℕ)))).mul F).mul
      ((R.inv.mul R.inv).mul R.inv)

private theorem originalRadialJet_value (s r B : ℂ) :
    (originalRadialJet s r B).value = originalRadial s r B := by
  simp [originalRadialJet, originalRadial, D4BMScalarLinearEquation.coord,
    D4BMScalarLinearEquation.temporalRadial, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.constant, ScalarTwoJet.inv]
  ring

private theorem originalRadialJet_first (s r B : ℂ) (hr : r ≠ 0) (hF : r^(2 : ℕ)-1 ≠ 0) :
    (originalRadialJet s r B).first =
      ![2*s*originalRadial s r B, originalRadialFirst s r B, 0, 0] := by
  ext k
  fin_cases k <;>
    simp [originalRadialJet, originalRadial, originalRadialFirst, D4BMScalarLinearEquation.coord,
      D4BMScalarLinearEquation.temporalRadial, ScalarTwoJet.mul, ScalarTwoJet.add,
      ScalarTwoJet.constant, ScalarTwoJet.inv] <;> field_simp [hr,hF] <;> ring

private theorem product_first (R U V : ScalarTwoJet (Fin 4) ℂ) (k : Fin 4) :
    ((R.mul U).mul V).first k = R.first k*(U.value*V.value)+
      R.value*(U.first k*V.value+U.value*V.first k) := by
  simp only [ScalarTwoJet.mul]
  ring

/-- The original mixed correction and its separated representation have identical metric values. -/
theorem originalCorrection_metric (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) :
    (D4BMQuadraticMixedSource.correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).metric =
      (temporalMetricJet (2*s) (originalRadial s r B) (originalRadialFirst s r B)
        (originalAngularJet s y S Sx Sy Sxx Sxy)).metric := by
  let H := D4BMQuadraticMixedSource.correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy
  have hm : H.metric = mixedMatrix ![H.metric 0 2, H.metric 0 3] (fun _ => 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hm]
  dsimp only [temporalMetricJet, mixedJet]
  congr 1
  funext a
  fin_cases a <;>
    simp [H, D4BMQuadraticMixedSource.correctionJet,
      originalRadial, originalAngularJet, D4BMScalarLinearEquation.coord,
      D4BMScalarLinearEquation.angular, D4BMScalarLinearEquation.temporalRadial,
      D4BMVectorLinearEquation.angular0, D4BMVectorLinearEquation.angular1,
      ScalarTwoJet.constant, ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.inv] <;> ring

private theorem originalCorrection_first_2 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hF : r^(2 : ℕ)-1 ≠ 0) (k : Fin 4) :
    (D4BMQuadraticMixedSource.correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).first k 0 2 =
      (temporalMetricJet (2*s) (originalRadial s r B) (originalRadialFirst s r B)
        (originalAngularJet s y S Sx Sy Sxx Sxy)).first k 0 2 := by
  change (((originalRadialJet s r B).mul
    (D4BMScalarLinearEquation.angular s y S Sx Sy Sxx Sxy)).mul
      (D4BMVectorLinearEquation.angular0 s y Sy Sxy
        ((s+1)*(s+2)*S/y^(2 : ℕ)-Sxx) (-Sxx) Sxxy ((s+1)*(s+2)*Sx/y^(2 : ℕ)-Sxxx))).first k = _
  rw [product_first, originalRadialJet_first s r B hr hF, originalRadialJet_value]
  fin_cases k <;>
    simp [temporalMetricJet, mixedJet, mixedMatrix, originalAngularJet,
      D4BMScalarLinearEquation.angular, D4BMVectorLinearEquation.angular0]
  ring_nf
  simp

private theorem originalCorrection_first_3 (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hF : r^(2 : ℕ)-1 ≠ 0) (k : Fin 4) :
    (D4BMQuadraticMixedSource.correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).first k 0 3 =
      (temporalMetricJet (2*s) (originalRadial s r B) (originalRadialFirst s r B)
        (originalAngularJet s y S Sx Sy Sxx Sxy)).first k 0 3 := by
  change (((originalRadialJet s r B).mul
    (D4BMScalarLinearEquation.angular s y S Sx Sy Sxx Sxy)).mul
      (D4BMVectorLinearEquation.angular1 s y (-Sx) Sxy (-Sxx)
        Sxxy ((s+1)*(s+2)*Sx/y^(2 : ℕ)-Sxxx))).first k = _
  rw [product_first, originalRadialJet_first s r B hr hF, originalRadialJet_value]
  fin_cases k <;>
    simp [temporalMetricJet, mixedJet, mixedMatrix, originalAngularJet,
      D4BMScalarLinearEquation.angular, D4BMVectorLinearEquation.angular1] <;> ring_nf <;> simp

/-- Every first derivative of the original correction is retained. The two nonzero columns
are checked once, then assembled using the metric's sparse symmetry. -/
theorem originalCorrection_first (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hF : r^(2 : ℕ)-1 ≠ 0) :
    (D4BMQuadraticMixedSource.correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy).first =
      (temporalMetricJet (2*s) (originalRadial s r B) (originalRadialFirst s r B)
        (originalAngularJet s y S Sx Sy Sxx Sxy)).first := by
  let H := D4BMQuadraticMixedSource.correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy
  let K := temporalMetricJet (2*s) (originalRadial s r B) (originalRadialFirst s r B)
    (originalAngularJet s y S Sx Sy Sxx Sxy)
  funext k
  have hm : H.first k = mixedMatrix ![H.first k 0 2, H.first k 0 3] (fun _ => 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hk : K.first k = mixedMatrix ![K.first k 0 2, K.first k 0 3] (fun _ => 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hm, hk, originalCorrection_first_2 _ _ _ _ _ _ _ _ _ _ _ hr hF k,
    originalCorrection_first_3 _ _ _ _ _ _ _ _ _ _ _ hr hF k]

/-- Literal correction/left-mode Einstein action, with the original angular product retained. -/
theorem originalCorrection_temporal_action (p : D4BMBackground.ExteriorPoint)
    (s B S Sx Sy Sxx Sxy Sxxx Sxxy d dr drr : ℂ)
    (K : Fin 2 → ScalarTwoJet (Fin 2) ℂ) :
    let r : ℂ := p.val 1
    let y : ℂ := p.val 3
    r^(2 : ℕ)/y^(2 : ℕ) * actionSymplectic (D4BMBackground.jet r y)
      (D4BMQuadraticMixedSource.correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy)
      (streamMetricJet r (fun a => staticStreamJet (-2*s) d dr drr (K a))) 0 =
      (2*s)*d/(r^(2 : ℕ)-1) * (s*(s+1)/2*B^(2 : ℕ)*((2*s+5)/r^(4 : ℕ)-3/r^(2 : ℕ))) *
        angularPair (originalAngularJet s y S Sx Sy Sxx Sxy) K := by
  have hr : (p.val 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [p.property.1])
  have hF : (p.val 1:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (show (p.val 1)^(2 : ℕ)-1 ≠ 0 by nlinarith [p.property.1])
  dsimp only
  rw [actionSymplectic_congr_first _ _ _ _ (originalCorrection_metric ..)
    (originalCorrection_first _ _ _ _ _ _ _ _ _ _ _ hr hF)]
  have he : -2*s = -(2*s) := by ring
  rw [he, temporal_action]
  unfold originalRadial originalRadialFirst
  field_simp
  ring

/-- The incoming correction density is the actual Einstein current with its radial Jacobian.
The radial derivative is obtained by differentiating the source envelope. -/
theorem incomingTemporalDensity_action (q : XiZeroCopy) (branch : Bool) (a w dr drr : ℂ)
    (J K : Fin 2 → ScalarTwoJet (Fin 2) ℂ) (zang : D4BMHorizon.Point)
    (hy : 0 < zang 1) {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    let p := modePoint ⟨tortoiseOf z, tortoiseOf_neg hz⟩ zang hy
    let r : ℂ := p.val 1
    let c := correctionRadial (physicalRate q branch) w a
      (continuedOnset (physicalRate q branch) w)
    (r^(2 : ℕ)-1) * (r^(2 : ℕ)/(p.val 3:ℂ)^(2 : ℕ) * actionSymplectic
      (D4BMBackground.jet r (p.val 3))
      (temporalMetricJet w (c (p.val 1)) (deriv c (p.val 1)) J)
      (streamMetricJet r (fun j => staticStreamJet (-w)
        (r*horizon w (physicalRadialFrequency q) z) dr drr (K j))) 0) /
      (2*(z:ℂ)*(Real.sqrt (1-z):ℂ)) =
      incomingTemporalDensity q branch a (angularPair J K) w z := by
  dsimp only
  rw [temporal_action]
  change (((tortoiseRadius (tortoiseOf z):ℂ)^(2 : ℕ)-1) *
    (w*((tortoiseRadius (tortoiseOf z):ℂ)*horizon w (physicalRadialFrequency q) z)/
      ((tortoiseRadius (tortoiseOf z):ℂ)^(2 : ℕ)-1) *
      (deriv (correctionRadial (physicalRate q branch) w a
        (continuedOnset (physicalRate q branch) w)) (tortoiseRadius (tortoiseOf z))-
      2*correctionRadial (physicalRate q branch) w a
        (continuedOnset (physicalRate q branch) w) (tortoiseRadius (tortoiseOf z))/
        (tortoiseRadius (tortoiseOf z):ℂ)) * angularPair J K)) / _ = _
  rw [(correctionRadial_hasDerivAt _ _ _ _ _ (tortoiseOf_neg hz)).deriv]
  have hF : (tortoiseRadius (tortoiseOf z):ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (show (tortoiseRadius (tortoiseOf z))^(2 : ℕ)-1 ≠ 0 by
      nlinarith [tortoiseRadius_exterior (tortoiseOf z) (tortoiseOf_neg hz)])
  unfold incomingTemporalDensity
  field_simp
  ring

/-- Common-cutoff restoration applies to the original correction density, retaining its finite value. -/
theorem incomingTemporalDensity_restoration (q : XiZeroCopy) (branch side : Bool)
    (a angular : ℂ) :
    ∃ R B : ℝ, ∃ c₀ c₁ : ℂ → ℂ, 0 < R ∧ 0 < B ∧ B ≤ 1/2 ∧
      ∀ b : ℝ, 0 < b → b ≤ B →
        AnalyticAt ℂ (QuadraticEndpointMellin.finitePart
          (temporalProfile q branch a angular) c₀ c₁ b) (physicalFundamentalFrequency q side) ∧
        Tendsto (fun w => (w-physicalFundamentalFrequency q side) *
          QuadraticEndpointMellin.finitePart (temporalProfile q branch a angular) c₀ c₁ b w)
          (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 0) ∧
        ∀ w ∈ ball (physicalFundamentalFrequency q side) R,
          Tendsto (fun e : ℝ => (∫ z in e..b, incomingTemporalDensity q branch a angular w z) +
              c₀ w*(e:ℂ)^w/w+c₁ w*(e:ℂ)^(w+1)/(w+1))
            (𝓝[>] (0:ℝ))
            (𝓝 (QuadraticEndpointMellin.finitePart (temporalProfile q branch a angular) c₀ c₁ b w)) := by
  obtain ⟨R, B, c₀, c₁, hR, hB, hBh, h⟩ := temporalProfile_restoration q branch side a angular
  refine ⟨R, B, c₀, c₁, hR, hB, hBh, ?_⟩
  intro b hb hbB
  obtain ⟨hA, hres, hcut⟩ := h b hb hbB
  refine ⟨hA, hres, ?_⟩
  intro w hw
  apply (hcut w hw).congr'
  have heb : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e < b :=
    (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, heb] with e he heb
  have hi : (∫ z in e..b, incomingTemporalDensity q branch a angular w z) =
      ∫ z in e..b, (z:ℂ)^(w-1)*temporalProfile q branch a angular w z := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le heb.le] at hz
    exact incomingTemporalDensity_eq q branch a angular w
      ⟨he.trans_le hz.1, lt_of_le_of_lt hz.2 (by linarith)⟩
  rw [hi]

/-- Subtracting the restored incoming correction preserves the original temporal pole coefficient.
The correction finite part is retained; no vanishing value or incidence premise is assumed. -/
theorem incoming_corrected_residue (q : XiZeroCopy) (branch side : Bool) (a angular : ℂ)
    (zang : D4BMHorizon.Point) :
    ∃ B : ℝ, ∃ c₀ c₁ d₀ d₁ : ℂ → ℂ, 0 < B ∧ B ≤ 1/2 ∧
      ∀ b : ℝ, 0 < b → b ≤ B →
        Tendsto (fun w => (w-physicalFundamentalFrequency q side) *
          (QuadraticEndpointMellin.finitePart (clearedDensityProfile q branch a zang) c₀ c₁ b w /
            reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch) -
          QuadraticEndpointMellin.finitePart (temporalProfile q branch a angular) d₀ d₁ b w))
          (𝓝[≠] physicalFundamentalFrequency q side)
          (𝓝 (QuadraticEndpointMellin.finitePart (clearedDensityProfile q branch a zang) c₀ c₁ b
            (physicalFundamentalFrequency q side) / physicalFundamentalDenominatorSlope q branch side)) := by
  obtain ⟨R, B, c₀, c₁, _, hB, hBh, _, hmain⟩ :=
    physicalTemporalCurrent_horizon_restoration_data q branch side a zang
  obtain ⟨S, C, d₀, d₁, _, hC, _, hcorrection⟩ :=
    incomingTemporalDensity_restoration q branch side a angular
  refine ⟨min B C, c₀, c₁, d₀, d₁, lt_min hB hC, (min_le_left B C).trans hBh, ?_⟩
  intro b hb hbBC
  have hm := (hmain b hb (hbBC.trans (min_le_left B C))).2.1
  have hc := (hcorrection b hb (hbBC.trans (min_le_right B C))).2.1
  simpa only [sub_zero, mul_sub] using hm.sub hc

end
end RHTower.D4BMCorrectionAction
