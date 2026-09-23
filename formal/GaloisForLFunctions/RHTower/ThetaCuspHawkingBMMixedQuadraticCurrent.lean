import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedQuadraticClosure
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLeftQNMMetricEquation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMActionSymplecticForm

/-!
# Contact-inclusive mixed correction and original left-QNM current

The actual particular mixed correction and independently continued original left
metric yield an exact volume-weighted Einstein current. Its radial component
retains the contact and both angular overlaps. The literal source equations give
an angular Green divergence and reduce this component to one square/reader
pairing plus its boundary flux, including the resonant case.

This does not identify the switched causal correction, assemble the independent
scalar/scalar and vector/vector channels, or prove fixed-clock extinction.
-/

open Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMMixedQuadraticCurrent
open D4BMHorizon D4BMModularCore D4BMMetricReconstruction D4BMFundamentalScalarMetric
open D4BMMixedActionCurrent D4BMPhysicalModeAction
open CoordinateMetricTwoJet.Linearization D4BMActionSymplecticForm
noncomputable section
set_option autoImplicit false

private abbrev Jet := CoordinateMetricTwoJet 4 ℂ
/-- Angular coordinate slot in the original four-dimensional metric. -/
abbrev angularIndex (a : Fin 2) : Fin 4 := a.castAdd 2 + 2

def timeBlock (H : Jet) (a : Fin 2) : ℂ := H.metric 0 (angularIndex a)
def radiusBlock (H : Jet) (a : Fin 2) : ℂ := H.metric 1 (angularIndex a)
def radialCurl (H : Jet) (a : Fin 2) : ℂ :=
  H.first 0 1 (angularIndex a)-H.first 1 0 (angularIndex a)

private def Mixed (H : Jet) : Prop :=
  H.metric = mixedMatrix (timeBlock H) (radiusBlock H) ∧
  H.first = fun k => mixedMatrix (fun a => H.first k 0 (angularIndex a))
    (fun a => H.first k 1 (angularIndex a))

private theorem action_first_congr (J H H' K K' : Jet) (hJ : J.metric.det ≠ 0)
    (hm : H.metric = H'.metric) (hf : H.first = H'.first)
    (km : K.metric = K'.metric) (kf : K.first = K'.first) (j : Fin 4) :
    actionSymplectic J H K j = actionSymplectic J H' K' j := by
  simp only [actionSymplectic_eq_form _ _ _ hJ, weightedInverse, inverse, connection,
    hm, hf, km, kf]

private theorem exterior_det (p : D4BMBackground.ExteriorPoint) :
    (D4BMBackground.jet (p.val 1) (p.val 3)).metric.det ≠ 0 := by
  have hr : (p.val 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [p.property.1])
  have hy : (p.val 3:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
  have hF : (p.val 1:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (show (p.val 1)^(2 : ℕ)-1 ≠ 0 by nlinarith [p.property.1])
  change (D4BMBackground.metric (p.val 1) (p.val 3)).det ≠ 0
  rw [D4BMBackground.metric_det _ _ hF]
  exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 4 hr) (pow_ne_zero 4 (inv_ne_zero hy)))

private theorem mixed_current (p : D4BMBackground.ExteriorPoint) (H K : Jet)
    (hH : Mixed H) (hK : Mixed K) :
    (p.val 1:ℂ)^(2 : ℕ)/(p.val 3:ℂ)^(2 : ℕ) *
      actionSymplectic (D4BMBackground.jet (p.val 1) (p.val 3)) H K 1 =
      ∑ a : Fin 2, (timeBlock H a * radialCurl K a-timeBlock K a * radialCurl H a) := by
  rw [action_first_congr _ H
    (mixedJet (timeBlock H) (radiusBlock H) (fun k a => H.first k 0 (angularIndex a))
      (fun k a => H.first k 1 (angularIndex a))) K
    (mixedJet (timeBlock K) (radiusBlock K) (fun k a => K.first k 0 (angularIndex a))
      (fun k a => K.first k 1 (angularIndex a)))
    (exterior_det p) hH.1 hH.2 hK.1 hK.2,
    mixed_radial_action_current]
  rfl

private theorem mixed_combination (c : ℂ) (H K : Jet) (hH : Mixed H) (hK : Mixed K) :
    Mixed (metricJetCombination c H K) := by
  rcases hH with ⟨hm,hf⟩
  rcases hK with ⟨km,kf⟩
  constructor
  · change (fun i j => H.metric i j-c*K.metric i j) = _
    rw [hm,km]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mixedMatrix,timeBlock,radiusBlock,metricJetCombination,
      ComplexCoordinateMetricTwoJet.ofSpace,ComplexCoordinateMetricTwoJet.toSpace,angularIndex]
  · change (fun k i j => H.first k i j-c*K.first k i j) = _
    rw [hf,kf]
    ext k i j
    fin_cases i <;> fin_cases j <;> simp [mixedMatrix,metricJetCombination,
      ComplexCoordinateMetricTwoJet.ofSpace,ComplexCoordinateMetricTwoJet.toSpace,angularIndex]
    all_goals rfl

private theorem stream_mixed (w r h h1 h2 h3 A C P Q R U V W Z : ℂ) :
    Mixed (D4BMVectorStream.metricJet w r h h1 h2 h3 A C P Q R U V W Z) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · ext k i j
    fin_cases i <;> fin_cases j <;> rfl

private theorem contact_mixed (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) :
    Mixed (D4BMQuadraticMixedSource.correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · ext k i j
    fin_cases i <;> fin_cases j <;> rfl

private theorem stream_orbit_values (w r h h1 h2 h3 A C P Q R U V W Z : ℂ) (a : Fin 2) :
    let H := D4BMVectorStream.metricJet w r h h1 h2 h3 A C P Q R U V W Z
    timeBlock H a = (r^(2 : ℕ)-1)*h1*(![A,C] a) ∧
    radialCurl H a = (w^(2 : ℕ)*h/(r^(2 : ℕ)-1)-2*r*h1-(r^(2 : ℕ)-1)*h2)*(![A,C] a) := by
  fin_cases a <;> constructor
  all_goals dsimp [timeBlock,radialCurl,angularIndex,D4BMVectorStream.metricJet,
    D4BMVectorStream.radialJet,D4BMVectorStream.covector0,D4BMVectorStream.covector1,
    D4BMScalarLinearEquation.coord,ScalarTwoJet.mul,ScalarTwoJet.add,ScalarTwoJet.inv,
    ScalarTwoJet.constant]
  all_goals ring

private theorem contact_orbit_values (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hF : r^(2 : ℕ)-1 ≠ 0) (a : Fin 2) :
    let H := D4BMQuadraticMixedSource.correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy
    timeBlock H a = s*(s+1)/2*B^(2 : ℕ)*(r^(2 : ℕ)-1)/r^(3 : ℕ)*(![S*Sy,-S*Sx] a) ∧
    radialCurl H a = s*(s+1)/2*B^(2 : ℕ)*(1/r^(2 : ℕ)-(2*s+3)/r^(4 : ℕ))*(![S*Sy,-S*Sx] a) := by
  fin_cases a <;> constructor
  all_goals dsimp [timeBlock,radialCurl,angularIndex,D4BMQuadraticMixedSource.correctionJet,
    D4BMScalarLinearEquation.coord,D4BMScalarLinearEquation.temporalRadial,
    D4BMScalarLinearEquation.angular,D4BMVectorLinearEquation.angular0,
    D4BMVectorLinearEquation.angular1,ScalarTwoJet.mul,ScalarTwoJet.add,ScalarTwoJet.inv,
    ScalarTwoJet.constant]
  all_goals field_simp
  all_goals ring

private def assembledJet (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) : Jet :=
  metricJetCombination (-1)
    (metricJetCombination (physicalRate q branch*(physicalRate q branch-1)/4)
      (streamActualMetricJet (2*physicalRate q branch) (p.val 1)
        (envelope (2*physicalRate q branch) (a^(2 : ℕ)) p.val) false
        (fullAngularCovector q branch) (angularPoint p.val))
      (streamActualMetricJet (2*physicalRate q branch) (p.val 1)
        (envelope (2*physicalRate q branch) (a^(2 : ℕ)) p.val) true
        (fullSquareCovector q) (angularPoint p.val)))
    (D4BMMixedQuadraticClosure.contactJet q branch a p)

private theorem actual_jet (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) :
    ofMetricField (D4BMMixedQuadraticClosure.mixedField q branch a) p.val =
      assembledJet q branch a p := by
  have hA (k : Fin 2) : ContDiffAt ℝ 2 (fullAngularCovector q branch k) (angularPoint p.val) := by
    have h := (contDiffAt_infty.mp (fullAngularCovector_smooth q branch
      (angularPoint p.val) p.property.2 k)) 2
    norm_num at h
    exact h
  have hS (k : Fin 2) := fullSquareCovector_smooth q (angularPoint p.val) p.property.2 2 k
  unfold D4BMMixedQuadraticClosure.mixedField
  rw [ofMetricField_combination (-1) _ _ p.val
    (forcedMetricField_smooth q branch a p) (D4BMMixedQuadraticClosure.contactField_smooth q branch a p),
    D4BMMixedQuadraticClosure.contactField_jet]
  unfold forcedMetricField
  rw [ofMetricField_combination _ _ _ p.val
    (streamMetricField_smooth _ _ false _ p hA) (streamMetricField_smooth _ _ true _ p hS),
    streamMetricField_jet _ _ false _ p hA (fullAngularCovector_divergence q branch),
    streamMetricField_jet _ _ true _ p hS (fullSquareCovector_divergence q)]
  rfl

private theorem actual_mixed (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) :
    Mixed (ofMetricField (D4BMMixedQuadraticClosure.mixedField q branch a) p.val) := by
  rw [actual_jet]
  exact mixed_combination _ _ _
    (mixed_combination _ _ _ (stream_mixed ..) (stream_mixed ..)) (contact_mixed ..)

/-- Actual source-derived temporal block, after adding the differentiated contact. -/
def sourceTime (s r E A J : ℂ) : ℂ :=
  E/r*(2*s*A+s^(2 : ℕ)*(1-(s+1)/(2*r^(2 : ℕ)))*J)

/-- Actual radial curl of the complete mixed particular correction. -/
def sourceCurl (s r E A J : ℂ) : ℂ :=
  E/r^(2 : ℕ)*(2*s*(2*s+1)*A+s^(2 : ℕ)*(1-(s+1)*(2*s+3)/(2*r^(2 : ℕ)))*J)

private theorem combination_orbit (c : ℂ) (H K : Jet) (a : Fin 2) :
    timeBlock (metricJetCombination c H K) a = timeBlock H a-c*timeBlock K a ∧
    radialCurl (metricJetCombination c H K) a = radialCurl H a-c*radialCurl K a := by
  constructor
  · rfl
  · change H.first 0 1 _-c*K.first 0 1 _-(H.first 1 0 _-c*K.first 1 0 _) = _
    unfold radialCurl
    ring

private theorem streamActual_orbit (w r E : ℂ) (sq : Bool) (V : D4BMHorizon.Covector)
    (z : Point) (a : Fin 2) :
    timeBlock (streamActualMetricJet w r E sq V z) a =
      (r^(2 : ℕ)-1)*streamRadialFirst w r E sq*V a z ∧
    radialCurl (streamActualMetricJet w r E sq V z) a =
      (w^(2 : ℕ)*streamRadialValue w r E sq/(r^(2 : ℕ)-1)-
        2*r*streamRadialFirst w r E sq-(r^(2 : ℕ)-1)*streamRadialSecond w r E sq)*V a z := by
  have h := stream_orbit_values w r (streamRadialValue w r E sq)
    (streamRadialFirst w r E sq) (streamRadialSecond w r E sq) (streamRadialThird w r E sq)
    (V 0 z) (V 1 z) (coordDeriv 0 (V 0) z) (coordDeriv 1 (V 0) z) (coordDeriv 0 (V 1) z)
    (coordDeriv 0 (coordDeriv 0 (V 0)) z) (coordDeriv 0 (coordDeriv 1 (V 0)) z)
    (coordDeriv 0 (coordDeriv 0 (V 1)) z) (coordDeriv 1 (coordDeriv 1 (V 0)) z) a
  have he : ![V 0 z,V 1 z] a = V a z := by fin_cases a <;> rfl
  simpa only [streamActualMetricJet,he] using h

private theorem contact_actual_orbit (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (k : Fin 2) :
    let s := physicalRate q branch
    let r := (p.val 1:ℂ)
    let E := envelope (2*s) (a^(2 : ℕ)) p.val
    let J := fullSquareCovector q k (angularPoint p.val)
    let H := D4BMMixedQuadraticClosure.contactJet q branch a p
    timeBlock H k = s*(s+1)/2*E*(r^(2 : ℕ)-1)/r^(3 : ℕ)*J ∧
    radialCurl H k = s*(s+1)/2*E*(1/r^(2 : ℕ)-(2*s+3)/r^(4 : ℕ))*J := by
  have hr : (p.val 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [p.property.1])
  have hF : (p.val 1:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (show (p.val 1)^(2 : ℕ)-1 ≠ 0 by nlinarith [p.property.1])
  let S := D4BMAngularTwoTensor.source q
  let z := angularPoint p.val
  have he : ![S z*coordDeriv 1 S z,-S z*coordDeriv 0 S z] k = fullSquareCovector q k z := by
    fin_cases k
    · rfl
    · change -S z*coordDeriv 0 S z = S z*(-coordDeriv 0 S z)
      ring
  have h := contact_orbit_values (physicalRate q branch) (p.val 1) (p.val 3)
    (envelope (physicalRate q branch) a p.val) (S z) (coordDeriv 0 S z) (coordDeriv 1 S z)
    (coordDeriv 0 (coordDeriv 0 S) z) (coordDeriv 0 (coordDeriv 1 S) z)
    (coordDeriv 0 (coordDeriv 0 (coordDeriv 0 S)) z)
    (coordDeriv 0 (coordDeriv 0 (coordDeriv 1 S)) z) hr hF k
  dsimp only at h ⊢
  rw [he,← envelope_double] at h
  exact h

/-- Both original metric values and actual coordinate curls of the mixed correction.
No source equation, covariance, or boundary cancellation is supplied as a premise. -/
theorem mixedField_orbit (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (k : Fin 2) :
    let H := ofMetricField (D4BMMixedQuadraticClosure.mixedField q branch a) p.val
    let s := physicalRate q branch
    let r := (p.val 1:ℂ)
    let E := envelope (2*s) (a^(2 : ℕ)) p.val
    let A := fullAngularCovector q branch k (angularPoint p.val)
    let J := fullSquareCovector q k (angularPoint p.val)
    timeBlock H k = sourceTime s r E A J ∧ radialCurl H k = sourceCurl s r E A J := by
  have hr : (p.val 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [p.property.1])
  have hF : (p.val 1:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (show (p.val 1)^(2 : ℕ)-1 ≠ 0 by nlinarith [p.property.1])
  dsimp only
  rw [actual_jet]
  constructor
  · unfold assembledJet
    rw [(combination_orbit _ _ _ _).1,(combination_orbit _ _ _ _).1,
      (streamActual_orbit _ _ _ false _ _ _).1,(streamActual_orbit _ _ _ true _ _ _).1,
      (contact_actual_orbit q branch a p k).1]
    simp only [streamRadialFirst,sourceTime,Bool.false_eq_true,↓reduceIte]
    field_simp
    ring
  · unfold assembledJet
    rw [(combination_orbit _ _ _ _).2,(combination_orbit _ _ _ _).2,
      (streamActual_orbit _ _ _ false _ _ _).2,(streamActual_orbit _ _ _ true _ _ _).2,
      (contact_actual_orbit q branch a p k).2]
    simp only [streamRadialValue,streamRadialFirst,streamRadialSecond,sourceCurl,Bool.false_eq_true,↓reduceIte]
    field_simp
    ring

/-- Original left-mode temporal block after the unchanged tortoise-to-radius lift. -/
def leftTime (r g dg : ℂ) : ℂ := (r^(2 : ℕ)-1)*g+r*dg

/-- Original left-mode curl, using its actual continued radial equation. -/
def leftCurl (r lam g dg : ℂ) : ℂ := lam*g/r-2*r*g-2*dg

private theorem left_actual_orbit (q : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ))
    (z : {z : Point // 0 < z 1}) (k : Fin 2) :
    let H := ofMetricField (D4BMLeftModeRadialEquation.metricField q side outer)
      (modePoint t z.val z.property).val
    let r := (D4BMJointWave.tortoiseRadius t:ℂ)
    let g := D4BMLeftModeRadialEquation.profile q side outer t
    let dg := D4BMLeftModeRadialEquation.profileFirst q side outer t
    let V := D4BMLiteralCusp.vector (D4BMJointSource.physicalAngularParameter q) k z.val
    timeBlock H k = leftTime r g dg*V ∧
    radialCurl H k = leftCurl r (D4BMLeftModeRadialEquation.eigenvalue q) g dg*V := by
  have hr : (D4BMJointWave.tortoiseRadius t:ℂ) ≠ 0 := by
    exact_mod_cast (show D4BMJointWave.tortoiseRadius t ≠ 0 by
      linarith [D4BMJointWave.tortoiseRadius_exterior t t.property])
  have hF : (D4BMJointWave.tortoiseRadius t:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (show (D4BMJointWave.tortoiseRadius t)^(2 : ℕ)-1 ≠ 0 by
      nlinarith [D4BMJointWave.tortoiseRadius_exterior t t.property])
  dsimp only
  rw [D4BMLeftModeRadialEquation.metricField_jet]
  unfold D4BMLeftModeRadialEquation.fullMetricJet
  rw [(stream_orbit_values ..).1,(stream_orbit_values ..).2]
  have hv : ![D4BMLiteralCusp.vector (D4BMJointSource.physicalAngularParameter q) 0 z.val,
    D4BMLiteralCusp.vector (D4BMJointSource.physicalAngularParameter q) 1 z.val] k =
      D4BMLiteralCusp.vector (D4BMJointSource.physicalAngularParameter q) k z.val := by
    fin_cases k <;> rfl
  rw [hv]
  dsimp only [radiusLift,radiusLiftFirst,radiusLiftSecond,D4BMLeftModeRadialEquation.profileSecond,
    D4BMLeftModeRadialEquation.potential,leftTime,leftCurl]
  rw [D4BMJointWave.tortoise_original_inverse t t.property]
  simp only [D4BMJointSource.horizonCoordinate,D4BMJointSource.radialUnit_inverse_radius]
  push_cast
  constructor <;> field_simp
  all_goals ring

private theorem left_actual_mixed (q : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ))
    (z : {z : Point // 0 < z 1}) :
    Mixed (ofMetricField (D4BMLeftModeRadialEquation.metricField q side outer)
      (modePoint t z.val z.property).val) := by
  rw [D4BMLeftModeRadialEquation.metricField_jet]
  exact stream_mixed ..

/-- Actual volume-weighted Einstein current of the mixed particular correction
against the original independent left QNM, at its original physical frequency. -/
def current (q : XiZeroCopy) (branch : Bool) (a : ℂ) (reader : XiZeroCopy)
    (side outer : Bool) (t : Iio (0:ℝ)) (z : {z : Point // 0 < z 1}) (j : Fin 4) : ℂ :=
  let p := modePoint t z.val z.property
  (p.val 1:ℂ)^(2 : ℕ)/(p.val 3:ℂ)^(2 : ℕ) * actionSymplectic
    (D4BMBackground.jet (p.val 1) (p.val 3))
    (ofMetricField (D4BMMixedQuadraticClosure.mixedField q branch a) p.val)
    (ofMetricField (D4BMLeftModeRadialEquation.metricField reader side outer) p.val) j

/-- The radial current with the contact and both independent angular overlaps retained. -/
theorem radial_current (q : XiZeroCopy) (branch : Bool) (a : ℂ) (reader : XiZeroCopy)
    (side outer : Bool) (t : Iio (0:ℝ)) (z : {z : Point // 0 < z 1}) :
    let p := modePoint t z.val z.property
    let s := physicalRate q branch
    let r := (p.val 1:ℂ)
    let E := envelope (2*s) (a^(2 : ℕ)) p.val
    let g := D4BMLeftModeRadialEquation.profile reader side outer t
    let dg := D4BMLeftModeRadialEquation.profileFirst reader side outer t
    current q branch a reader side outer t z 1 =
      ∑ k : Fin 2,
        (sourceTime s r E (fullAngularCovector q branch k (angularPoint p.val))
            (fullSquareCovector q k (angularPoint p.val))*
          leftCurl r (D4BMLeftModeRadialEquation.eigenvalue reader) g dg-
          leftTime r g dg*sourceCurl s r E
            (fullAngularCovector q branch k (angularPoint p.val))
            (fullSquareCovector q k (angularPoint p.val)))*
        D4BMLiteralCusp.vector (D4BMJointSource.physicalAngularParameter reader) k z.val := by
  dsimp only
  unfold current
  rw [mixed_current _ _ _ (actual_mixed ..) (left_actual_mixed ..)]
  apply Finset.sum_congr rfl
  intro k _
  rw [(mixedField_orbit ..).1,(mixedField_orbit ..).2,
    (left_actual_orbit ..).1,(left_actual_orbit ..).2]
  simp only [show (modePoint t z.val z.property).val 1 =
    D4BMJointWave.tortoiseRadius t from rfl]
  ring

/-- All four original fluxes, including the temporal curvature and both angular curls.
This identity discards no horizon, characteristic, or cusp face. -/
theorem complete_current (q : XiZeroCopy) (branch : Bool) (a : ℂ) (reader : XiZeroCopy)
    (side outer : Bool) (t : Iio (0:ℝ)) (z : {z : Point // 0 < z 1}) (j : Fin 4) :
    let p := modePoint t z.val z.property
    let H := ofMetricField (D4BMMixedQuadraticClosure.mixedField q branch a) p.val
    let K := ofMetricField (D4BMLeftModeRadialEquation.metricField reader side outer) p.val
    current q branch a reader side outer t z j =
      completeCurrentDensity (p.val 1) (p.val 3)
        (timeBlock H) (radiusBlock H) (timeBlock K) (radiusBlock K)
        (fun l k => H.first l 0 (angularIndex k)) (fun l k => H.first l 1 (angularIndex k))
        (fun l k => K.first l 0 (angularIndex k)) (fun l k => K.first l 1 (angularIndex k)) j := by
  intro p H K
  have hH : Mixed H := actual_mixed ..
  have hK : Mixed K := left_actual_mixed ..
  change (p.val 1:ℂ)^(2 : ℕ)/(p.val 3:ℂ)^(2 : ℕ) *
    actionSymplectic (D4BMBackground.jet (p.val 1) (p.val 3)) H K j = _
  rw [action_first_congr _ H
    (mixedJet (timeBlock H) (radiusBlock H) (fun k a => H.first k 0 (angularIndex a))
      (fun k a => H.first k 1 (angularIndex a))) K
    (mixedJet (timeBlock K) (radiusBlock K) (fun k a => K.first k 0 (angularIndex a))
      (fun k a => K.first k 1 (angularIndex a)))
    (exterior_det p) hH.1 hH.2 hK.1 hK.2,
    mixed_complete_action_current]

/-- The source-contact contribution required in the original radial boundary pairing. -/
def contactRadialCoefficient (s r E lam g dg : ℂ) : ℂ :=
  s*(s+1)/2*E/r^(4 : ℕ)*((r^(2 : ℕ)-1)*(lam-3*r^(2 : ℕ)+2*s+3)*g+r*(2*s+5-3*r^(2 : ℕ))*dg)

/-- The actual contact alone has this radial pairing with the original left mode.
It cannot be dropped merely because its temporal metric entry vanishes at the horizon. -/
theorem contact_radial_current (q : XiZeroCopy) (branch : Bool) (a : ℂ) (reader : XiZeroCopy)
    (side outer : Bool) (t : Iio (0:ℝ)) (z : {z : Point // 0 < z 1}) :
    let p := modePoint t z.val z.property
    let s := physicalRate q branch
    let r := (p.val 1:ℂ)
    let E := envelope (2*s) (a^(2 : ℕ)) p.val
    (p.val 1:ℂ)^(2 : ℕ)/(p.val 3:ℂ)^(2 : ℕ) * actionSymplectic
      (D4BMBackground.jet (p.val 1) (p.val 3))
      (ofMetricField (D4BMMixedQuadraticClosure.contactField q branch a) p.val)
      (ofMetricField (D4BMLeftModeRadialEquation.metricField reader side outer) p.val) 1 =
      contactRadialCoefficient s r E (D4BMLeftModeRadialEquation.eigenvalue reader)
        (D4BMLeftModeRadialEquation.profile reader side outer t)
        (D4BMLeftModeRadialEquation.profileFirst reader side outer t)*
      ∑ k : Fin 2, fullSquareCovector q k (angularPoint p.val)*
        D4BMLiteralCusp.vector (D4BMJointSource.physicalAngularParameter reader) k z.val := by
  intro p s r E
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [p.property.1])
  have hH : Mixed (ofMetricField (D4BMMixedQuadraticClosure.contactField q branch a) p.val) := by
    rw [D4BMMixedQuadraticClosure.contactField_jet]
    exact contact_mixed ..
  rw [mixed_current p _ _ hH (left_actual_mixed ..),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [D4BMMixedQuadraticClosure.contactField_jet,
    (contact_actual_orbit ..).1,(contact_actual_orbit ..).2,
    (left_actual_orbit ..).1,(left_actual_orbit ..).2]
  change _ = contactRadialCoefficient s r E _ _ _*(_*_)
  rw [show (D4BMJointWave.tortoiseRadius t:ℂ) = r from rfl]
  dsimp only [leftTime,leftCurl,contactRadialCoefficient]
  change (s*(s+1)/2*E*(r^(2 : ℕ)-1)/r^(3 : ℕ)*_)*(_*_)-(_*_)*(s*(s+1)/2*E*(1/r^(2 : ℕ)-(2*s+3)/r^(4 : ℕ))*_) = _
  field_simp
  ring

/-- The original left mode and the damped opposite source branch have a strict
real-rate gap, for independent Xi occurrences. This keeps their boundary laws distinct. -/
theorem original_left_source_rate_gap (q reader : XiZeroCopy) (branch side : Bool) :
    2 < (-D4BMLeftModeRadialEquation.frequency reader side-(-3-physicalRate q branch)).re ∧
    (-D4BMLeftModeRadialEquation.frequency reader side-(-3-physicalRate q branch)).re < 4 := by
  have hq := xi_divisor_support_re_mem_open_unit q.1
  have hr := xi_divisor_support_re_mem_open_unit reader.1
  simp only [D4BMLeftModeRadialEquation.frequency,D4BMJointSource.physicalFundamentalFrequency_eq]
  cases branch <;> cases side
  all_goals norm_num [physicalRate,Complex.sub_re,Complex.neg_re,Complex.div_re]
  all_goals constructor <;> linarith [hq.1,hq.2,hr.1,hr.2]

/-- The damped `−3−s` test in the older odd-sector formula cannot be identified
with the original left QNM by retaining its time rate. -/
theorem original_left_ne_damped_source (q reader : XiZeroCopy) (branch side : Bool) :
    -D4BMLeftModeRadialEquation.frequency reader side ≠ -3-physicalRate q branch := by
  intro h
  have hg := (original_left_source_rate_gap q reader branch side).1
  rw [h,sub_self,Complex.zero_re] at hg
  linarith

/-- Source-derived angular Green current controlling the two actual covector overlaps. -/
def angularGreenCurrent (q : XiZeroCopy) (branch : Bool) (reader : XiZeroCopy)
    (j : Fin 2) (z : Point) : ℂ :=
  let H := fullAngularField q branch
  let S := D4BMAngularTwoTensor.source q
  let R := D4BMLiteralCusp.scalar (D4BMJointSource.physicalAngularParameter reader)
  D4BMLeftModeRadialEquation.eigenvalue reader*R z*coordDeriv j H z-
    D4BMGlobalAngularResponse.parameter q branch*(H z+S z^(2 : ℕ)/2)*coordDeriv j R z

/-- The literal source and reader equations give an exact overlap identity.
Its right side is a divergence, whose boundary flux still has to be retained. -/
theorem angular_overlap_divergence (q : XiZeroCopy) (branch : Bool) (reader : XiZeroCopy)
    (z : {z : Point // 0 < z 1}) :
    (∑ j : Fin 2, coordDeriv j (angularGreenCurrent q branch reader j) z.val) =
      (D4BMLeftModeRadialEquation.eigenvalue reader-D4BMGlobalAngularResponse.parameter q branch)*
        (∑ j : Fin 2, fullAngularCovector q branch j z.val*
          D4BMLiteralCusp.vector (D4BMJointSource.physicalAngularParameter reader) j z.val)-
      D4BMGlobalAngularResponse.parameter q branch*
        (∑ j : Fin 2, fullSquareCovector q j z.val*
          D4BMLiteralCusp.vector (D4BMJointSource.physicalAngularParameter reader) j z.val) := by
  let H := fullAngularField q branch
  let S := D4BMAngularTwoTensor.source q
  let R := D4BMLiteralCusp.scalar (D4BMJointSource.physicalAngularParameter reader)
  let lam := D4BMLeftModeRadialEquation.eigenvalue reader
  let mu := D4BMGlobalAngularResponse.parameter q branch
  have hH : ContDiffAt ℝ 2 H z.val := by
    have h := (contDiffAt_infty.mp (fullAngularField_smooth q branch z.val z.property)) 2
    norm_num at h
    exact h
  have hS : ContDiffAt ℝ 2 S z.val :=
    D4BMLiteralCusp.scalar_contDiffAt (D4BMGlobalAngularResponse.center q) 2 z.val z.property
  have hR : ContDiffAt ℝ 2 R z.val :=
    D4BMLiteralCusp.scalar_contDiffAt (D4BMJointSource.physicalAngularParameter reader) 2 z.val z.property
  have dH := (hH.differentiableAt (by norm_num)).hasFDerivAt
  have dS := (hS.differentiableAt (by norm_num)).hasFDerivAt
  have dR := (hR.differentiableAt (by norm_num)).hasFDerivAt
  have hd (j : Fin 2) : coordDeriv j (angularGreenCurrent q branch reader j) z.val =
      lam*(coordDeriv j R z.val*coordDeriv j H z.val+R z.val*coordDeriv j (coordDeriv j H) z.val)-
      mu*((coordDeriv j H z.val+S z.val*coordDeriv j S z.val)*coordDeriv j R z.val+
        (H z.val+S z.val^(2 : ℕ)/2)*coordDeriv j (coordDeriv j R) z.val) := by
    have dh := (ScalarTwoJet.coordDeriv_hasFDerivAt hH j).differentiableAt.hasFDerivAt
    have dr := (ScalarTwoJet.coordDeriv_hasFDerivAt hR j).differentiableAt.hasFDerivAt
    have hh := ((dR.const_mul lam).mul dh).sub
      (((dH.add ((dS.pow 2).mul_const (2:ℂ)⁻¹)).const_mul mu).mul dr)
    change HasFDerivAt (angularGreenCurrent q branch reader j) _ z.val at hh
    simp only [coordDeriv,hh.fderiv,add_apply,sub_apply,smul_apply,Pi.add_apply,
      smul_eq_mul,nsmul_eq_mul]
    ring
  have heH := fullAngularField_equation q branch z.val z.property
  rw [scalarLaplacian_eq _ z.val z.property] at heH
  change (z.val 1:ℂ)^(2 : ℕ)*(coordDeriv 0 (coordDeriv 0 H) z.val+
    coordDeriv 1 (coordDeriv 1 H) z.val) = mu*H z.val+(mu/2)*S z.val^(2 : ℕ) at heH
  have heR := D4BMLiteralCusp.scalar_equation
    (D4BMJointSource.physicalAngularParameter reader) z.val z.property
  rw [scalarLaplacian_eq _ z.val z.property] at heR
  have heR' : (z.val 1:ℂ)^(2 : ℕ)*(coordDeriv 0 (coordDeriv 0 R) z.val+
      coordDeriv 1 (coordDeriv 1 R) z.val) = lam*R z.val := by
    dsimp only [R,lam,D4BMLeftModeRadialEquation.eigenvalue,D4BMLiteralCusp.scalarQ] at heR ⊢
    linear_combination heR
  change (∑ j : Fin 2, coordDeriv j (angularGreenCurrent q branch reader j) z.val) =
    (lam-mu)*(∑ j : Fin 2, coexact H j z.val*coexact R j z.val)-
      mu*(∑ j : Fin 2, S z.val*coexact S j z.val*coexact R j z.val)
  have hy : (z.val 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.property.ne'
  apply (mul_left_cancel₀ (pow_ne_zero 2 hy))
  simp only [Fin.sum_univ_two,hd,coexact,Matrix.cons_val_zero,Matrix.cons_val_one]
  linear_combination (lam*R z.val)*heH-(mu*(H z.val+S z.val^(2 : ℕ)/2))*heR'

/-- Coefficient of one actual angular overlap in the radial Einstein current. -/
def radialPairCoefficient (s r E lam g dg A J : ℂ) : ℂ :=
  sourceTime s r E A J*leftCurl r lam g dg-leftTime r g dg*sourceCurl s r E A J

/-- Source-derived decomposition of the actual radial left-QNM current into
one square/reader overlap and the full angular Green divergence. Multiplying
by the eigenvalue difference keeps the identity valid at resonance as well. -/
theorem radial_current_angular_decomposition (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (reader : XiZeroCopy) (side outer : Bool) (t : Iio (0:ℝ))
    (z : {z : Point // 0 < z 1}) :
    let p := modePoint t z.val z.property
    let s := physicalRate q branch
    let r := (p.val 1:ℂ)
    let E := envelope (2*s) (a^(2 : ℕ)) p.val
    let lam := D4BMLeftModeRadialEquation.eigenvalue reader
    let mu := D4BMGlobalAngularResponse.parameter q branch
    let g := D4BMLeftModeRadialEquation.profile reader side outer t
    let dg := D4BMLeftModeRadialEquation.profileFirst reader side outer t
    let C := radialPairCoefficient s r E lam g dg 1 0
    let D := radialPairCoefficient s r E lam g dg 0 1
    (lam-mu)*current q branch a reader side outer t z 1 =
      C*(∑ j : Fin 2, coordDeriv j (angularGreenCurrent q branch reader j) z.val)+
      ((lam-mu)*D+mu*C)*(∑ j : Fin 2, fullSquareCovector q j z.val*
        D4BMLiteralCusp.vector (D4BMJointSource.physicalAngularParameter reader) j z.val) := by
  dsimp only
  rw [radial_current,angular_overlap_divergence]
  have hz : angularPoint (modePoint t z.val z.property).val = z.val := by
    ext j
    fin_cases j <;> rfl
  rw [hz]
  simp only [Fin.sum_univ_two,radialPairCoefficient,sourceTime,sourceCurl]
  ring

end
end RHTower.D4BMMixedQuadraticCurrent
