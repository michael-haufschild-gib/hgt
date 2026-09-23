import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStreamFrequencyTensor

/-! The literal source-pole cochain exposed by the off-frequency Einstein defect. -/

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet

namespace RHTower.D4BMModularCore

open D4BMHorizon D4BMScalarLinearEquation D4BMVectorStream D4BMQuadraticMixedSource
  D4BMMetricReconstruction
open ComplexCoordinateMetricTwoJet

set_option autoImplicit false
noncomputable section

private def defectMatrix (T R : Fin 2 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, T 0, T 1;
    0, 0, R 0, R 1;
    T 0, R 0, 0, 0;
    T 1, R 1, 0, 0]

private def frequencyMetricJetCombination (c : ℂ)
    (K L : CoordinateMetricTwoJet 4 ℂ) : CoordinateMetricTwoJet 4 ℂ :=
  ofSpace (toSpace K - c • toSpace L)

private theorem cosmological_frequencyMetricJetCombination
    (J K L : CoordinateMetricTwoJet 4 ℂ) (hJ : J.metric.det ≠ 0)
    (c Λ : ℂ) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological J
      (frequencyMetricJetCombination c K L) Λ i j =
      CoordinateMetricTwoJet.Linearization.cosmological J K Λ i j -
        c * CoordinateMetricTwoJet.Linearization.cosmological J L Λ i j := by
  simp only [CoordinateMetricTwoJet.Linearization.cosmological,
    CoordinateMetricTwoJet.Linearization.einstein_eq_fderiv _ _ hJ,
    frequencyMetricJetCombination, toSpace_ofSpace, map_sub, map_smul]
  change _ + Λ * (K.metric i j - c * L.metric i j) = _
  simp only [smul_eq_mul]
  ring

/-- A literal field combination realizes the complete combined jet in this frequency module. -/
private theorem frequency_ofMetricField_combination (c : ℂ)
    (F G : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) (x : Fin 4 → ℝ)
    (hF : ∀ i j, ContDiffAt ℝ 2 (fun y => F y i j) x)
    (hG : ∀ i j, ContDiffAt ℝ 2 (fun y => G y i j) x) :
    ofMetricField (fun y i j => F y i j - c * G y i j) x =
      frequencyMetricJetCombination c (ofMetricField F x) (ofMetricField G x) := by
  have hj (i j : Fin 4) : ofField (fun y => F y i j - c * G y i j) x =
      (ofField (fun y => F y i j) x).add
        ((constant (-c)).mul (ofField (fun y => G y i j) x)) := by
    have he : (fun y => F y i j - c * G y i j) =
        (fun y => F y i j + (-c) * G y i j) := by
      funext y
      ring
    rw [he, ofField_add (hF i j) (contDiffAt_const.mul (hG i j)),
      ofField_mul contDiffAt_const (hG i j), ofField_constant]
  have hs : toSpace (ofMetricField (fun y i j => F y i j - c * G y i j) x) =
      toSpace (frequencyMetricJetCombination c (ofMetricField F x) (ofMetricField G x)) := by
    apply Prod.ext
    · rfl
    apply Prod.ext
    · funext k i j
      have h := congrArg (fun a => a.first k) (hj i j)
      change coordDeriv k (fun y => F y i j - c * G y i j) x =
        coordDeriv k (fun y => F y i j) x - c * coordDeriv k (fun y => G y i j) x
      simpa [ofField, ScalarTwoJet.add, ScalarTwoJet.mul, constant, sub_eq_add_neg] using h
    · funext k l i j
      have h := congrArg (fun a => a.second k l) (hj i j)
      change coordDeriv k (coordDeriv l (fun y => F y i j - c * G y i j)) x =
        coordDeriv k (coordDeriv l (fun y => F y i j)) x -
          c * coordDeriv k (coordDeriv l (fun y => G y i j)) x
      simpa [ofField, ScalarTwoJet.add, ScalarTwoJet.mul, constant, sub_eq_add_neg] using h
  exact congrArg ofSpace hs

/-- The exact quotient of the off-frequency defect by its source-pole factor.
Its radial entries retain the original mixed source current. -/
def frequencyDefectCochain (q : XiZeroCopy) (branch : Bool) (w r B : ℂ)
    (z : Point) : Matrix (Fin 4) (Fin 4) ℂ :=
  let v := 2 * physicalRate q branch
  let f := r ^ (2 : ℕ) - 1
  let P := forcedStreamValue q branch r B
  let P1 := forcedStreamFirst q branch r B
  let C := fun k => current (physicalRate q branch) r B
    (fullSquareCovector q k z) (fullGradientCovector q branch k z)
  let T := fun k => f / (2 * r ^ (2 : ℕ)) * (w + v) *
    (r ^ (2 : ℕ) / f * P1 k z - 2 * r / f ^ (2 : ℕ) * P k z)
  let R := fun k => -C k / (r ^ (2 : ℕ) * f) +
    w / (2 * r ^ (2 : ℕ) * f) * (w + v) * r ^ (2 : ℕ) / f * P k z
  defectMatrix T R

/-- The full mixed frozen metric pencil at fixed radial profile frequency. -/
def frozenMixedMetricJet (q : XiZeroCopy) (branch : Bool) (w r B : ℂ)
    (z : Point) : CoordinateMetricTwoJet 4 ℂ :=
  frequencyMetricJetCombination (physicalRate q branch * (physicalRate q branch - 1) / 4)
    (frozenStreamMetricJet w (2 * physicalRate q branch) r (B ^ (2 : ℕ)) false
      (fullAngularCovector q branch) z)
    (frozenStreamMetricJet w (2 * physicalRate q branch) r (B ^ (2 : ℕ)) true
      (fullSquareCovector q) z)

/-- Literal metric realization of the scaled source-pole defect: the difference
between the frequency-`w` frozen pencil and its physical-frequency value. -/
def frozenMixedDifferenceJet (q : XiZeroCopy) (branch : Bool) (w r B : ℂ)
    (z : Point) : CoordinateMetricTwoJet 4 ℂ :=
  frequencyMetricJetCombination 1 (frozenMixedMetricJet q branch w r B z)
    (frozenMixedMetricJet q branch (2 * physicalRate q branch) r B z)

private theorem time_factor (v w r P P1 : ℂ) :
    (r ^ (2 : ℕ) - 1) / (2 * r ^ (2 : ℕ)) * (w ^ (2 : ℕ) - v ^ (2 : ℕ)) *
        (r ^ (2 : ℕ) / (r ^ (2 : ℕ) - 1) * P1 - 2 * r / (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * P) =
      (w - v) * ((r ^ (2 : ℕ) - 1) / (2 * r ^ (2 : ℕ)) * (w + v) *
        (r ^ (2 : ℕ) / (r ^ (2 : ℕ) - 1) * P1 - 2 * r / (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * P)) := by
  ring

private theorem radial_factor (v w r P C : ℂ) :
    -(w - v) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * C +
        w / (2 * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * (w ^ (2 : ℕ) - v ^ (2 : ℕ)) * r ^ (2 : ℕ) /
          (r ^ (2 : ℕ) - 1) * P =
      (w - v) * (-C / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) +
        w / (2 * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * (w + v) * r ^ (2 : ℕ) /
          (r ^ (2 : ℕ) - 1) * P) := by
  ring

private theorem defectMatrix_factor (a : ℂ) (T R T' R' : Fin 2 → ℂ)
    (hT : ∀ k, T k = a * T' k) (hR : ∀ k, R k = a * R' k) :
    defectMatrix T R = a • defectMatrix T' R' := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals dsimp only [defectMatrix, Matrix.smul_apply, smul_eq_mul]
  all_goals first | exact hT 0 | exact hT 1 | exact hR 0 | exact hR 1 | norm_num

/-- The full off-frequency Einstein defect has precisely one source-pole factor. -/
theorem frequencyDefectTensor_factor (q : XiZeroCopy) (branch : Bool) (w r B : ℂ)
    (z : Point) :
    frequencyDefectTensor q branch w r B z =
      (w - 2 * physicalRate q branch) • frequencyDefectCochain q branch w r B z := by
  let v := 2 * physicalRate q branch
  let P := forcedStreamValue q branch r B
  let P1 := forcedStreamFirst q branch r B
  let C := fun k => current (physicalRate q branch) r B
    (fullSquareCovector q k z) (fullGradientCovector q branch k z)
  let T := fun k => (r ^ (2 : ℕ) - 1) / (2 * r ^ (2 : ℕ)) * (w ^ (2 : ℕ) - v ^ (2 : ℕ)) *
    (r ^ (2 : ℕ) / (r ^ (2 : ℕ) - 1) * P1 k z - 2 * r / (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * P k z)
  let R := fun k => -(w - v) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * C k +
    w / (2 * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * (w ^ (2 : ℕ) - v ^ (2 : ℕ)) * r ^ (2 : ℕ) /
      (r ^ (2 : ℕ) - 1) * P k z
  let T' := fun k => (r ^ (2 : ℕ) - 1) / (2 * r ^ (2 : ℕ)) * (w + v) *
    (r ^ (2 : ℕ) / (r ^ (2 : ℕ) - 1) * P1 k z - 2 * r / (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * P k z)
  let R' := fun k => -C k / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) +
    w / (2 * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * (w + v) * r ^ (2 : ℕ) /
      (r ^ (2 : ℕ) - 1) * P k z
  have htime (k : Fin 2) :
      T k = (w - v) * T' k := by
    exact time_factor v w r (P k z) (P1 k z)
  have hradius (k : Fin 2) :
      R k = (w - v) * R' k := by
    exact radial_factor v w r (P k z) (C k)
  change defectMatrix T R = (w - v) • defectMatrix T' R'
  exact defectMatrix_factor (w - v) T R T' R' htime hradius

/-- The literal frozen Einstein pencil plus complete mixed source equals the source-pole factor
times the residue cochain. -/
theorem frozen_stream_cosmological_source_factor (q : XiZeroCopy) (branch : Bool)
    (p : D4BMBackground.ExteriorPoint) (B w : ℂ) (i j : Fin 4) :
    let s := physicalRate q branch
    let r := (p.val 1 : ℂ)
    let z := angularPoint p.val
    let E := fun K => CoordinateMetricTwoJet.Linearization.cosmological
      (D4BMBackground.jet r (p.val 3)) K (-3) i j
    E (frozenStreamMetricJet w (2 * s) r (B ^ (2 : ℕ)) false (fullAngularCovector q branch) z) -
      (s * (s - 1) / 4) *
        E (frozenStreamMetricJet w (2 * s) r (B ^ (2 : ℕ)) true (fullSquareCovector q) z) +
      literalMixedSource q branch r B z i j =
      (w - 2 * s) * frequencyDefectCochain q branch w r B z i j := by
  dsimp only
  rw [frozen_stream_cosmological_source]
  have h := congrFun (congrFun (frequencyDefectTensor_factor q branch w (p.val 1) B
    (angularPoint p.val)) i) j
  simpa only [Matrix.smul_apply, smul_eq_mul] using h

/-- The scaled defect cochain is the exact cosmological Einstein residual of a
literal difference of complete frozen metric two-jets. No causal inverse or
endpoint condition is used. -/
theorem frozenMixedDifferenceJet_cosmological (q : XiZeroCopy) (branch : Bool)
    (p : D4BMBackground.ExteriorPoint) (B w : ℂ) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological
      (D4BMBackground.jet (p.val 1) (p.val 3))
      (frozenMixedDifferenceJet q branch w (p.val 1) B (angularPoint p.val)) (-3) i j =
      (w - 2 * physicalRate q branch) *
        frequencyDefectCochain q branch w (p.val 1) B (angularPoint p.val) i j := by
  have hdet : (D4BMBackground.jet (p.val 1) (p.val 3)).metric.det ≠ 0 := by
    have hr : (p.val 1 : ℂ) ≠ 0 := by
      exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
    have hy : (p.val 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
    have hf : (p.val 1 : ℂ) ^ (2 : ℕ) - 1 ≠ 0 := by
      exact_mod_cast (by nlinarith [p.property.1] : (p.val 1) ^ (2 : ℕ) - 1 ≠ 0)
    change (D4BMBackground.metric (p.val 1) (p.val 3)).det ≠ 0
    rw [D4BMBackground.metric_det _ _ hf]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ (inv_ne_zero hy)))
  have hw := frozen_stream_cosmological_source_factor q branch p B w i j
  have hv := frozen_stream_cosmological_source_factor q branch p B
    (2 * physicalRate q branch) i j
  dsimp only at hw hv
  unfold frozenMixedDifferenceJet
  rw [cosmological_frequencyMetricJetCombination _ _ _ hdet]
  unfold frozenMixedMetricJet
  rw [cosmological_frequencyMetricJetCombination _ _ _ hdet,
    cosmological_frequencyMetricJetCombination _ _ _ hdet]
  linear_combination hw - hv

open scoped ContDiff
open D4BMFundamentalScalarMetric

/-- Pure time factor used to separate the temporal frequency from a radial profile. -/
def frequencyPhase (u : ℂ) (x : Fin 4 → ℝ) : ℂ :=
  Complex.exp (u * (x 0 : ℂ))

/-- A literal separated factor with time frequency `w` and radial profile frequency `v`. -/
def frequencyEnvelope (w v a : ℂ) (x : Fin 4 → ℝ) : ℂ :=
  frequencyPhase (w - v) x * envelope v a x

private def frequencyPhaseJet (u t : ℂ) : ScalarTwoJet (Fin 4) ℂ where
  value := Complex.exp (u * t)
  first := ![u * Complex.exp (u * t), 0, 0, 0]
  second := !![u ^ (2 : ℕ) * Complex.exp (u * t), 0, 0, 0;
    0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

/-- Complete jet of a factor with independent temporal and radial frequencies. -/
def frequencyEnvelopeJet (w v r B : ℂ) : ScalarTwoJet (Fin 4) ℂ where
  value := B
  first := ![w * B, v * B / (r * (r ^ (2 : ℕ) - 1)), 0, 0]
  second := !![w ^ (2 : ℕ) * B, w * v * B / (r * (r ^ (2 : ℕ) - 1)), 0, 0;
    w * v * B / (r * (r ^ (2 : ℕ) - 1)),
      B * (v ^ (2 : ℕ) - v * (3 * r ^ (2 : ℕ) - 1)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)), 0, 0;
    0, 0, 0, 0; 0, 0, 0, 0]

private theorem frequencyPhase_smooth (u : ℂ) (p : D4BMBackground.ExteriorPoint)
    (m : WithTop ℕ∞) : ContDiffAt ℝ m (frequencyPhase u) p.val := by
  unfold frequencyPhase
  apply Complex.contDiff_exp.contDiffAt.comp p.val
  exact (contDiffAt_const.mul
    ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)).contDiffAt))

private theorem frequencyPhase_jet (u : ℂ) (p : D4BMBackground.ExteriorPoint) :
    ofField (frequencyPhase u) p.val = frequencyPhaseJet u (p.val 0) := by
  let Q : (Fin 4 → ℝ) → ℂ := fun x => u * (x 0 : ℂ)
  have hQ : ContDiffAt ℝ 2 Q p.val :=
    contDiffAt_const.mul ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)).contDiffAt)
  have hQJ : ofField Q p.val =
      (constant u).mul (coordinateJet (p.val 0) 0) := by
    change ofField (fun x => u * (x 0 : ℂ)) p.val = _
    have h := ScalarTwoJet.ofField_mul (x := p.val) (f := fun _ : Fin 4 → ℝ => u)
      (g := fun x : Fin 4 → ℝ => (x 0 : ℂ)) (contDiffAt_const (x := p.val))
        ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)).contDiffAt (x := p.val))
    rw [ScalarTwoJet.ofField_constant, coordinate_jet] at h
    exact h
  change ofField (fun x => Complex.exp (Q x)) p.val = _
  rw [ScalarTwoJet.ofField_comp Complex.contDiff_exp.contDiffAt hQ, Complex.deriv_exp, hQJ]
  ext i j
  · rfl
  · fin_cases i <;>
      simp [frequencyPhaseJet, coordinateJet, ScalarTwoJet.compose, ScalarTwoJet.mul,
        ScalarTwoJet.constant] <;> ring
  · fin_cases i <;> fin_cases j <;>
      simp [frequencyPhaseJet, coordinateJet, ScalarTwoJet.compose, ScalarTwoJet.mul,
        ScalarTwoJet.constant] <;> ring

/-- The independent-frequency factor has the displayed genuine coordinate jet. -/
theorem frequencyEnvelope_jet (w v a : ℂ) (p : D4BMBackground.ExteriorPoint) :
    ofField (frequencyEnvelope w v a) p.val =
      frequencyEnvelopeJet w v (p.val 1) (frequencyEnvelope w v a p.val) := by
  have hp : ContDiffAt ℝ 2 (frequencyPhase (w - v)) p.val :=
    frequencyPhase_smooth (w - v) p 2
  have he : ContDiffAt ℝ 2 (envelope v a) p.val := envelope_contDiffAt v a p 2
  unfold frequencyEnvelope
  rw [ScalarTwoJet.ofField_mul hp he, frequencyPhase_jet, envelope_jet]
  apply ScalarTwoJet.ext
  · rfl
  · funext i
    fin_cases i <;>
      simp [frequencyEnvelopeJet, frequencyPhaseJet, envelopeJet, ScalarTwoJet.mul,
        frequencyPhase] <;> ring
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp [frequencyEnvelopeJet, frequencyPhaseJet, envelopeJet, ScalarTwoJet.mul,
        frequencyPhase] <;> ring

/-- On the physical diagonal the two-rate factor is the original literal envelope. -/
theorem frequencyEnvelope_diagonal (v a : ℂ) (x : Fin 4 → ℝ) :
    frequencyEnvelope v v a x = envelope v a x := by
  simp [frequencyEnvelope, frequencyPhase]

/-- The quadratic off-frequency stream is the square of its primary two-rate factor. -/
theorem frequencyEnvelope_square (w s a : ℂ) (x : Fin 4 → ℝ) :
    frequencyEnvelope (w / 2) s a x ^ (2 : ℕ) =
      frequencyEnvelope w (2 * s) (a ^ (2 : ℕ)) x := by
  rw [frequencyEnvelope, frequencyEnvelope, envelope_double]
  unfold frequencyPhase
  have hfactor : Complex.exp ((w / 2 - s) * (x 0 : ℂ)) * envelope s a x *
      (Complex.exp ((w / 2 - s) * (x 0 : ℂ)) * envelope s a x) =
      (Complex.exp ((w / 2 - s) * (x 0 : ℂ)) *
        Complex.exp ((w / 2 - s) * (x 0 : ℂ))) * (envelope s a x ^ (2 : ℕ)) := by ring
  rw [pow_two, hfactor, ← Complex.exp_add]
  congr 2
  ring

/-- Product of two primary legs is the stream-rate envelope with their paired amplitude. -/
theorem frequencyEnvelope_mul (w s a d : ℂ) (x : Fin 4 → ℝ) :
    frequencyEnvelope (w / 2) s a x * frequencyEnvelope (w / 2) s d x =
      frequencyEnvelope w (2 * s) (a * d) x := by
  rw [frequencyEnvelope, frequencyEnvelope, frequencyEnvelope,
    envelope_eq_exp, envelope_eq_exp, envelope_eq_exp]
  unfold frequencyPhase
  have hfactor : Complex.exp ((w / 2 - s) * (x 0 : ℂ)) *
      (a * Complex.exp (s * (x 0 : ℂ) + (s / 2) * Complex.log (bmCoordinate x))) *
      (Complex.exp ((w / 2 - s) * (x 0 : ℂ)) *
        (d * Complex.exp (s * (x 0 : ℂ) + (s / 2) * Complex.log (bmCoordinate x)))) =
      (Complex.exp ((w / 2 - s) * (x 0 : ℂ)) *
        Complex.exp ((w / 2 - s) * (x 0 : ℂ))) *
        ((a * d) *
          (Complex.exp (s * (x 0 : ℂ) + (s / 2) * Complex.log (bmCoordinate x)) *
            Complex.exp (s * (x 0 : ℂ) + (s / 2) * Complex.log (bmCoordinate x)))) := by
    ring
  rw [hfactor, ← Complex.exp_add, ← Complex.exp_add]
  congr 2 <;> ring

/-- Literal radial profile with temporal frequency \`w\` and radial rate \`v\`. -/
def frequencyRadialField (w v a : ℂ) (square : Bool) (x : Fin 4 → ℝ) : ℂ :=
  frequencyPhase (w - v) x * streamRadialField v a square x

/-- Its actual radial derivative; the pure time phase has no radial derivative. -/
def frequencyRadialDerivative (w v a : ℂ) (square : Bool) (x : Fin 4 → ℝ) : ℂ :=
  frequencyPhase (w - v) x * streamRadialDerivative v a square x

private theorem frequencyRadialFields_smooth (w v a : ℂ) (square : Bool)
    (p : D4BMBackground.ExteriorPoint) (m : WithTop ℕ∞) :
    ContDiffAt ℝ m (frequencyRadialField w v a square) p.val ∧
      ContDiffAt ℝ m (frequencyRadialDerivative w v a square) p.val := by
  have hP : ContDiffAt ℝ m (frequencyPhase (w - v)) p.val :=
    frequencyPhase_smooth (w - v) p m
  have hR := streamRadialFields_smooth v a square p m
  exact ⟨hP.mul hR.1, hP.mul hR.2⟩

private theorem frequencyPhase_mul_radialJet (u v t H H1 H2 : ℂ) :
    (frequencyPhaseJet u t).mul (radialJet v H H1 H2) =
      radialJet (u + v) (Complex.exp (u * t) * H)
        (Complex.exp (u * t) * H1) (Complex.exp (u * t) * H2) := by
  apply ScalarTwoJet.ext
  · rfl
  · funext i
    fin_cases i <;>
      simp [frequencyPhaseJet, radialJet, ScalarTwoJet.mul] <;> ring
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp [frequencyPhaseJet, radialJet, ScalarTwoJet.mul] <;> ring

private theorem streamRadialValue_phase (v r B P : ℂ) (square : Bool) :
    P * streamRadialValue v r B square = streamRadialValue v r (P * B) square := by
  cases square <;> simp [streamRadialValue] <;> ring

private theorem streamRadialFirst_phase (v r B P : ℂ) (square : Bool) :
    P * streamRadialFirst v r B square = streamRadialFirst v r (P * B) square := by
  cases square <;> simp [streamRadialFirst] <;> ring

private theorem streamRadialSecond_phase (v r B P : ℂ) (square : Bool) :
    P * streamRadialSecond v r B square = streamRadialSecond v r (P * B) square := by
  cases square <;> simp [streamRadialSecond] <;> ring

private theorem streamRadialThird_phase (v r B P : ℂ) (square : Bool) :
    P * streamRadialThird v r B square = streamRadialThird v r (P * B) square := by
  cases square <;> simp [streamRadialThird] <;> ring

/-- The literal radial factor has the exact off-frequency jet used by the cochain. -/
theorem frequencyRadialField_jet (w v a : ℂ) (square : Bool) (p : D4BMBackground.ExteriorPoint) :
    ofField (frequencyRadialField w v a square) p.val =
      radialJet w (streamRadialValue v (p.val 1) (frequencyEnvelope w v a p.val) square)
        (streamRadialFirst v (p.val 1) (frequencyEnvelope w v a p.val) square)
        (streamRadialSecond v (p.val 1) (frequencyEnvelope w v a p.val) square) := by
  have hP : ContDiffAt ℝ 2 (frequencyPhase (w - v)) p.val :=
    frequencyPhase_smooth (w - v) p 2
  have hR := streamRadialFields_smooth v a square p 2
  unfold frequencyRadialField
  rw [ScalarTwoJet.ofField_mul hP hR.1, frequencyPhase_jet, streamRadialField_jet,
    frequencyPhase_mul_radialJet]
  have hrate : w - v + v = w := by ring
  rw [hrate, streamRadialValue_phase, streamRadialFirst_phase, streamRadialSecond_phase]
  rfl

/-- The displayed radial derivative is an actual derivative field with its full off-frequency jet. -/
theorem frequencyRadialDerivative_jet (w v a : ℂ) (square : Bool)
    (p : D4BMBackground.ExteriorPoint) :
    ofField (frequencyRadialDerivative w v a square) p.val =
      radialJet w (streamRadialFirst v (p.val 1) (frequencyEnvelope w v a p.val) square)
        (streamRadialSecond v (p.val 1) (frequencyEnvelope w v a p.val) square)
        (streamRadialThird v (p.val 1) (frequencyEnvelope w v a p.val) square) := by
  have hP : ContDiffAt ℝ 2 (frequencyPhase (w - v)) p.val :=
    frequencyPhase_smooth (w - v) p 2
  have hR := streamRadialFields_smooth v a square p 2
  unfold frequencyRadialDerivative
  rw [ScalarTwoJet.ofField_mul hP hR.2, frequencyPhase_jet, streamRadialDerivative_jet,
    frequencyPhase_mul_radialJet]
  have hrate : w - v + v = w := by ring
  rw [hrate, streamRadialFirst_phase, streamRadialSecond_phase, streamRadialThird_phase]
  rfl

/-- Time component of the off-frequency stream. -/
def frequencyStreamTimeBlock (w v a : ℂ) (square : Bool) (x : Fin 4 → ℝ) : ℂ :=
  ((x 1 : ℂ) * (x 1 : ℂ) + (-1)) * frequencyRadialDerivative w v a square x

/-- Radial component of the off-frequency stream. -/
def frequencyStreamRadiusBlock (w v a : ℂ) (square : Bool) (x : Fin 4 → ℝ) : ℂ :=
  (w * frequencyRadialField w v a square x) * ((x 1 : ℂ) * (x 1 : ℂ) + (-1))⁻¹

/-- Complete actual stream metric with independent time and radial-profile frequencies. -/
def frequencyStreamMetricField (w v a : ℂ) (square : Bool) (V : Covector)
    (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let T := frequencyStreamTimeBlock w v a square x
  let R := frequencyStreamRadiusBlock w v a square x
  let A := V 0 (angularPoint x)
  let C := V 1 (angularPoint x)
  !![0, 0, T * A, T * C; 0, 0, R * A, R * C;
    T * A, R * A, 0, 0; T * C, R * C, 0, 0]

private theorem frequency_block_smooth (w v a : ℂ) (square : Bool)
    (p : D4BMBackground.ExteriorPoint) :
    ContDiffAt ℝ 2 (frequencyStreamTimeBlock w v a square) p.val ∧
      ContDiffAt ℝ 2 (frequencyStreamRadiusBlock w v a square) p.val := by
  have hR : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ)) p.val :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt
  have hF : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ) * (x 1 : ℂ) + (-1)) p.val :=
    (hR.mul hR).add contDiffAt_const
  have hF0 : (p.val 1 : ℂ) * (p.val 1 : ℂ) + (-1) ≠ 0 := by
    have h : (p.val 1 : ℂ) ^ (2 : ℕ) - 1 ≠ 0 := by
      exact_mod_cast (by nlinarith [p.property.1] : (p.val 1) ^ (2 : ℕ) - 1 ≠ 0)
    simpa only [← pow_two, ← sub_eq_add_neg] using h
  exact ⟨hF.mul (frequencyRadialFields_smooth w v a square p 2).2,
    (contDiffAt_const.mul (frequencyRadialFields_smooth w v a square p 2).1).mul
      (hF.inv hF0)⟩

private theorem frequency_block_jets (w v a : ℂ) (square : Bool)
    (p : D4BMBackground.ExteriorPoint) :
    let r := (p.val 1 : ℂ)
    let B := frequencyEnvelope w v a p.val
    let R := coord r 1
    let F := (R.mul R).add (constant (-1))
    ofField (frequencyStreamTimeBlock w v a square) p.val =
      F.mul (radialJet w (streamRadialFirst v r B square)
        (streamRadialSecond v r B square) (streamRadialThird v r B square)) ∧
    ofField (frequencyStreamRadiusBlock w v a square) p.val =
      ((constant w).mul (radialJet w (streamRadialValue v r B square)
        (streamRadialFirst v r B square) (streamRadialSecond v r B square))).mul F.inv := by
  have hR : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ)) p.val :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt
  have hF : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ) * (x 1 : ℂ) + (-1)) p.val :=
    (hR.mul hR).add contDiffAt_const
  have hF0 : (p.val 1 : ℂ) * (p.val 1 : ℂ) + (-1) ≠ 0 := by
    have h : (p.val 1 : ℂ) ^ (2 : ℕ) - 1 ≠ 0 := by
      exact_mod_cast (by nlinarith [p.property.1] : (p.val 1) ^ (2 : ℕ) - 1 ≠ 0)
    simpa only [← pow_two, ← sub_eq_add_neg] using h
  have hJF : ofField (fun x : Fin 4 → ℝ => (x 1 : ℂ) * (x 1 : ℂ) + (-1)) p.val =
      ((coord (p.val 1) 1).mul (coord (p.val 1) 1)).add (constant (-1)) := by
    rw [ScalarTwoJet.ofField_add (hR.mul hR) contDiffAt_const,
      ScalarTwoJet.ofField_mul hR hR, ScalarTwoJet.ofField_constant, coordinate_jet]
    rfl
  constructor
  · unfold frequencyStreamTimeBlock
    rw [ScalarTwoJet.ofField_mul hF (frequencyRadialFields_smooth w v a square p 2).2,
      hJF, frequencyRadialDerivative_jet]
  · have hFi : ContDiffAt ℝ 2
        (fun x : Fin 4 → ℝ => ((x 1 : ℂ) * (x 1 : ℂ) + (-1))⁻¹) p.val :=
      hF.inv hF0
    unfold frequencyStreamRadiusBlock
    rw [ScalarTwoJet.ofField_mul
        ((contDiffAt_const (c := w)).mul (frequencyRadialFields_smooth w v a square p 2).1) hFi,
      ScalarTwoJet.ofField_mul (contDiffAt_const (c := w))
        (frequencyRadialFields_smooth w v a square p 2).1,
      ScalarTwoJet.ofField_constant, ScalarTwoJet.ofField_inv hF hF0, hJF,
      frequencyRadialField_jet]

private def frequency_assemble
    (J : Matrix (Fin 4) (Fin 4) (ScalarTwoJet (Fin 4) ℂ)) : CoordinateMetricTwoJet 4 ℂ :=
  ⟨fun i j => (J i j).value, fun k i j => (J i j).first k,
    fun k l i j => (J i j).second k l⟩

/-- Every displayed off-frequency stream component and derivative is realized by the field. -/
theorem frequencyStreamMetricField_jet (w v a : ℂ) (square : Bool) (V : Covector)
    (p : D4BMBackground.ExteriorPoint)
    (hV : ∀ k, ContDiffAt ℝ 2 (V k) (angularPoint p.val))
    (hD : ∀ z, 0 < z 1 → divergence V z = 0) :
    ofMetricField (frequencyStreamMetricField w v a square V) p.val =
      frozenStreamMetricJet w v (p.val 1) (frequencyEnvelope w v a p.val) square V
        (angularPoint p.val) := by
  have hu : ContDiff ℝ 2 angularPoint := by
    apply contDiff_pi.mpr
    intro k
    fin_cases k <;> exact contDiff_apply ℝ ℝ _
  have hLift (k : Fin 2) : ContDiffAt ℝ 2 (fun x => V k (angularPoint x)) p.val :=
    (hV k).comp p.val hu.contDiffAt
  have ht (k : Fin 2) :=
    ScalarTwoJet.ofField_mul (frequency_block_smooth w v a square p).1 (hLift k)
  have hr (k : Fin 2) :=
    ScalarTwoJet.ofField_mul (frequency_block_smooth w v a square p).2 (hLift k)
  simp_rw [(frequency_block_jets w v a square p).1,
    streamAngularJet_actual V p hV hD] at ht
  simp_rw [(frequency_block_jets w v a square p).2,
    streamAngularJet_actual V p hV hD] at hr
  change frequency_assemble _ = frequency_assemble _
  congr 1
  funext i j
  fin_cases i <;> fin_cases j
  all_goals
    first
    | exact ScalarTwoJet.ofField_constant 0 p.val
    | exact ht 0
    | exact ht 1
    | exact hr 0
    | exact hr 1

/-- The literal off-frequency metric is twice continuously differentiable on the exterior. -/
theorem frequencyStreamMetricField_smooth (w v a : ℂ) (square : Bool) (V : Covector)
    (p : D4BMBackground.ExteriorPoint)
    (hV : ∀ k, ContDiffAt ℝ 2 (V k) (angularPoint p.val)) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun x => frequencyStreamMetricField w v a square V x i j) p.val := by
  have hu : ContDiff ℝ 2 angularPoint := by
    apply contDiff_pi.mpr
    intro k
    fin_cases k <;> exact contDiff_apply ℝ ℝ _
  have hLift (k : Fin 2) : ContDiffAt ℝ 2 (fun x => V k (angularPoint x)) p.val :=
    (hV k).comp p.val hu.contDiffAt
  fin_cases i <;> fin_cases j
  all_goals
    first
    | exact contDiffAt_const
    | exact (frequency_block_smooth w v a square p).1.mul (hLift 0)
    | exact (frequency_block_smooth w v a square p).1.mul (hLift 1)
    | exact (frequency_block_smooth w v a square p).2.mul (hLift 0)
    | exact (frequency_block_smooth w v a square p).2.mul (hLift 1)

private theorem frequency_response_c2 (q : XiZeroCopy) (branch : Bool)
    (p : D4BMBackground.ExteriorPoint) (k : Fin 2) :
    ContDiffAt ℝ 2 (fullAngularCovector q branch k) (angularPoint p.val) := by
  have h := (contDiffAt_infty.mp
    (fullAngularCovector_smooth q branch (angularPoint p.val) p.property.2 k)) 2
  norm_num at h
  exact h

private theorem frequency_square_c2 (q : XiZeroCopy) (p : D4BMBackground.ExteriorPoint)
    (k : Fin 2) : ContDiffAt ℝ 2 (fullSquareCovector q k) (angularPoint p.val) := by
  simpa using fullSquareCovector_smooth q (angularPoint p.val) p.property.2 2 k

/-- Complete literal metric field carrying the source-pole cochain at temporal frequency `w`. -/
def frequencyMixedMetricField (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let s := physicalRate q branch
  frequencyStreamMetricField w (2 * s) (a ^ (2 : ℕ)) false (fullAngularCovector q branch) x -
    (s * (s - 1) / 4) •
      frequencyStreamMetricField w (2 * s) (a ^ (2 : ℕ)) true (fullSquareCovector q) x

private theorem frequencyRadialField_smul (w v c a : ℂ) (square : Bool) (x : Fin 4 → ℝ) :
    frequencyRadialField w v (c * a) square x =
      c * frequencyRadialField w v a square x := by
  simp only [frequencyRadialField, streamRadialField, envelope_eq_exp]
  split <;> ring

private theorem frequencyRadialField_add (w v a d : ℂ) (square : Bool) (x : Fin 4 → ℝ) :
    frequencyRadialField w v (a + d) square x =
      frequencyRadialField w v a square x + frequencyRadialField w v d square x := by
  simp only [frequencyRadialField, streamRadialField, envelope_eq_exp]
  split <;> ring

private theorem frequencyRadialDerivative_smul (w v c a : ℂ) (square : Bool)
    (x : Fin 4 → ℝ) :
    frequencyRadialDerivative w v (c * a) square x =
      c * frequencyRadialDerivative w v a square x := by
  simp only [frequencyRadialDerivative, streamRadialDerivative, envelope_eq_exp]
  split <;> ring

private theorem frequencyRadialDerivative_add (w v a d : ℂ) (square : Bool)
    (x : Fin 4 → ℝ) :
    frequencyRadialDerivative w v (a + d) square x =
      frequencyRadialDerivative w v a square x + frequencyRadialDerivative w v d square x := by
  simp only [frequencyRadialDerivative, streamRadialDerivative, envelope_eq_exp]
  split <;> ring

private theorem frequencyStreamMetricField_smul (w v c a : ℂ) (square : Bool) (V : Covector)
    (x : Fin 4 → ℝ) :
    frequencyStreamMetricField w v (c * a) square V x =
      c • frequencyStreamMetricField w v a square V x := by
  have hT : frequencyStreamTimeBlock w v (c * a) square x =
      c * frequencyStreamTimeBlock w v a square x := by
    unfold frequencyStreamTimeBlock
    rw [frequencyRadialDerivative_smul]
    ring
  have hR : frequencyStreamRadiusBlock w v (c * a) square x =
      c * frequencyStreamRadiusBlock w v a square x := by
    unfold frequencyStreamRadiusBlock
    rw [frequencyRadialField_smul]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frequencyStreamMetricField, hT, hR] <;> ring

private theorem frequencyStreamMetricField_add (w v a d : ℂ) (square : Bool) (V : Covector)
    (x : Fin 4 → ℝ) :
    frequencyStreamMetricField w v (a + d) square V x =
      frequencyStreamMetricField w v a square V x + frequencyStreamMetricField w v d square V x := by
  have hT : frequencyStreamTimeBlock w v (a + d) square x =
      frequencyStreamTimeBlock w v a square x + frequencyStreamTimeBlock w v d square x := by
    unfold frequencyStreamTimeBlock
    rw [frequencyRadialDerivative_add]
    ring
  have hR : frequencyStreamRadiusBlock w v (a + d) square x =
      frequencyStreamRadiusBlock w v a square x + frequencyStreamRadiusBlock w v d square x := by
    unfold frequencyStreamRadiusBlock
    rw [frequencyRadialField_add]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frequencyStreamMetricField, hT, hR] <;> ring

/-- Exact bilinear polarization of the literal stream with independent temporal and radial rates. -/
def frequencyStreamMetricBilinear (w v : ℂ) (square : Bool) (V : Covector) :
    ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ((Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) :=
  LinearMap.mk₂ ℂ (fun a d x => frequencyStreamMetricField w v (a * d) square V x)
    (by
      intro a b d
      funext x
      rw [show (a + b) * d = a * d + b * d by ring, frequencyStreamMetricField_add]
      rfl)
    (by
      intro c a d
      funext x
      change frequencyStreamMetricField w v ((c * a) * d) square V x =
        c • frequencyStreamMetricField w v (a * d) square V x
      rw [show (c * a) * d = c * (a * d) by ring, frequencyStreamMetricField_smul])
    (by
      intro a d e
      funext x
      rw [show a * (d + e) = a * d + a * e by ring, frequencyStreamMetricField_add]
      rfl)
    (by
      intro c a d
      funext x
      change frequencyStreamMetricField w v (a * (c * d)) square V x =
        c • frequencyStreamMetricField w v (a * d) square V x
      rw [show a * (c * d) = c * (a * d) by ring, frequencyStreamMetricField_smul])

/-- Its diagonal is the literal squared-primary stream field. -/
theorem frequencyStreamMetricBilinear_diag (w v a : ℂ) (square : Bool) (V : Covector)
    (x : Fin 4 → ℝ) :
    frequencyStreamMetricBilinear w v square V a a x =
      frequencyStreamMetricField w v (a ^ (2 : ℕ)) square V x := by
  simp only [frequencyStreamMetricBilinear, LinearMap.mk₂_apply, pow_two]

/-- The literal two-rate stream is symmetric in its two primary amplitudes. -/
theorem frequencyStreamMetricBilinear_symm (w v a d : ℂ) (square : Bool) (V : Covector)
    (x : Fin 4 → ℝ) :
    frequencyStreamMetricBilinear w v square V a d x =
      frequencyStreamMetricBilinear w v square V d a x := by
  simp only [frequencyStreamMetricBilinear, LinearMap.mk₂_apply]
  rw [mul_comm]

/-- Literal cyclic polarization of the off-frequency source-pole metric field. -/
def frequencyMixedMetricBilinear (q : XiZeroCopy) (branch : Bool) (w : ℂ) :
    ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ((Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) :=
  let s := physicalRate q branch
  frequencyStreamMetricBilinear w (2 * s) false (fullAngularCovector q branch) -
    (s * (s - 1) / 4) •
      frequencyStreamMetricBilinear w (2 * s) true (fullSquareCovector q)

/-- This polarized source-pole metric is symmetric before imposing causal boundary data. -/
theorem frequencyMixedMetricBilinear_symm (q : XiZeroCopy) (branch : Bool) (w a d : ℂ)
    (x : Fin 4 → ℝ) :
    frequencyMixedMetricBilinear q branch w a d x =
      frequencyMixedMetricBilinear q branch w d a x := by
  unfold frequencyMixedMetricBilinear
  have hA := frequencyStreamMetricBilinear_symm w (2 * physicalRate q branch) a d false
    (fullAngularCovector q branch) x
  have hB := frequencyStreamMetricBilinear_symm w (2 * physicalRate q branch) a d true
    (fullSquareCovector q) x
  dsimp only
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply]
  rw [hA, hB]

/-! The next two lemmas keep the two primary legs literal.  They identify the
off-diagonal field with the polarization of two independently constructed physical diagonal
fields; no square-root choice, fitted propagator, or causal boundary condition enters. -/

private theorem linear_polarization {E : Type*} [AddCommGroup E] [Module ℂ E]
    (L : ℂ →ₗ[ℂ] E) (a d : ℂ) :
    L (a * d) = (4 : ℂ)⁻¹ • (L ((a + d) ^ (2 : ℕ)) - L ((a - d) ^ (2 : ℕ))) := by
  have h : a * d = (4 : ℂ)⁻¹ • ((a + d) ^ (2 : ℕ) - (a - d) ^ (2 : ℕ)) := by
    change a * d = (4 : ℂ)⁻¹ * ((a + d) ^ (2 : ℕ) - (a - d) ^ (2 : ℕ))
    ring
  rw [h, L.map_smul, L.map_sub]

private theorem frequencyStreamMetricBilinear_polarization (w v a d : ℂ) (square : Bool)
    (V : Covector) (x : Fin 4 → ℝ) :
    frequencyStreamMetricBilinear w v square V a d x =
      (4 : ℂ)⁻¹ •
        (frequencyStreamMetricField w v ((a + d) ^ (2 : ℕ)) square V x -
          frequencyStreamMetricField w v ((a - d) ^ (2 : ℕ)) square V x) := by
  let L : ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ :=
    { toFun := fun z => frequencyStreamMetricField w v z square V x
      map_add' := by
        intro z z'
        exact frequencyStreamMetricField_add w v z z' square V x
      map_smul' := by
        intro c z
        change frequencyStreamMetricField w v (c * z) square V x =
          c • frequencyStreamMetricField w v z square V x
        exact frequencyStreamMetricField_smul w v c z square V x }
  change L (a * d) = (4 : ℂ)⁻¹ • (L ((a + d) ^ (2 : ℕ)) - L ((a - d) ^ (2 : ℕ)))
  exact linear_polarization L a d

/-- The literal off-diagonal stream metric is exactly the polarization of its two actual
diagonal metric fields.  This is the bulk two-leg realization required before a causal
retarded-minus-advanced comparison can be attempted. -/
theorem frequencyMixedMetricBilinear_polarization (q : XiZeroCopy) (branch : Bool)
    (w a d : ℂ) (x : Fin 4 → ℝ) :
    frequencyMixedMetricBilinear q branch w a d x =
      (4 : ℂ)⁻¹ •
        (frequencyMixedMetricField q branch w (a + d) x -
          frequencyMixedMetricField q branch w (a - d) x) := by
  unfold frequencyMixedMetricBilinear frequencyMixedMetricField
  dsimp only
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply]
  rw [frequencyStreamMetricBilinear_polarization,
    frequencyStreamMetricBilinear_polarization]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Diagonal restriction of cyclic polarization recovers the source-pole field exactly. -/
theorem frequencyMixedMetricBilinear_diag (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (x : Fin 4 → ℝ) :
    frequencyMixedMetricBilinear q branch w a a x =
      frequencyMixedMetricField q branch w a x := by
  unfold frequencyMixedMetricBilinear frequencyMixedMetricField
  dsimp only
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply]
  rw [frequencyStreamMetricBilinear_diag, frequencyStreamMetricBilinear_diag]

/-- The amplitude-free tensor retained by the literal mixed Einstein source. -/
private def literalMixedSourceKernel (q : XiZeroCopy) (branch : Bool) (r : ℂ) (z : Point) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  let s := physicalRate q branch
  let J := fullSquareCovector q
  let K := fullGradientCovector q branch
  let T0 := timeSquare s r * J 0 z + timeGradient s r * K 0 z
  let T1 := timeSquare s r * J 1 z + timeGradient s r * K 1 z
  let R0 := radialSquare s r * J 0 z + radialGradient s r * K 0 z
  let R1 := radialSquare s r * J 1 z + radialGradient s r * K 1 z
  !![0, 0, T0, T1; 0, 0, R0, R1; T0, R0, 0, 0; T1, R1, 0, 0]

/-- Exact two-leg polarization of every channel in the literal mixed Einstein source. -/
def literalMixedSourceBilinear (q : XiZeroCopy) (branch : Bool) (r B D : ℂ) (z : Point) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  (B * D) • literalMixedSourceKernel q branch r z

/-- The two-leg source is symmetric before any causal boundary condition is imposed. -/
theorem literalMixedSourceBilinear_symm (q : XiZeroCopy) (branch : Bool) (r B D : ℂ)
    (z : Point) :
    literalMixedSourceBilinear q branch r B D z =
      literalMixedSourceBilinear q branch r D B z := by
  unfold literalMixedSourceBilinear
  rw [mul_comm B D]

/-- Diagonal restriction recovers the original retained mixed source exactly. -/
theorem literalMixedSourceBilinear_diag (q : XiZeroCopy) (branch : Bool) (r B : ℂ)
    (z : Point) :
    literalMixedSourceBilinear q branch r B B z = literalMixedSource q branch r B z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [literalMixedSourceBilinear, literalMixedSourceKernel, literalMixedSource, pow_two]

/-- Literal paired source at the two primary temporal frequencies. -/
def frequencyMixedSourceBilinear (q : XiZeroCopy) (branch : Bool) (w a d : ℂ)
    (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  literalMixedSourceBilinear q branch (x 1)
    (frequencyEnvelope (w / 2) (physicalRate q branch) a x)
    (frequencyEnvelope (w / 2) (physicalRate q branch) d x) (angularPoint x)

/-- The actual paired source is cyclic in the two primary legs. -/
theorem frequencyMixedSourceBilinear_symm (q : XiZeroCopy) (branch : Bool) (w a d : ℂ)
    (x : Fin 4 → ℝ) :
    frequencyMixedSourceBilinear q branch w a d x =
      frequencyMixedSourceBilinear q branch w d a x := by
  unfold frequencyMixedSourceBilinear
  exact literalMixedSourceBilinear_symm _ _ _ _ _ _

/-- The paired source's diagonal is the original source-pole source. -/
theorem frequencyMixedSourceBilinear_diag (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (x : Fin 4 → ℝ) :
    frequencyMixedSourceBilinear q branch w a a x =
      literalMixedSource q branch (x 1)
        (frequencyEnvelope (w / 2) (physicalRate q branch) a x) (angularPoint x) := by
  unfold frequencyMixedSourceBilinear
  exact literalMixedSourceBilinear_diag _ _ _ _ _

private theorem frequencyEnvelope_add (w v a d : ℂ) (x : Fin 4 → ℝ) :
    frequencyEnvelope w v (a + d) x =
      frequencyEnvelope w v a x + frequencyEnvelope w v d x := by
  simp [frequencyEnvelope, frequencyPhase, envelope_eq_exp]
  ring

private theorem frequencyEnvelope_sub (w v a d : ℂ) (x : Fin 4 → ℝ) :
    frequencyEnvelope w v (a - d) x =
      frequencyEnvelope w v a x - frequencyEnvelope w v d x := by
  simp [frequencyEnvelope, frequencyPhase, envelope_eq_exp]
  ring

/-- The complete literal mixed Einstein source is the exact two-leg polarization of the original
source-pole source.  Both angular channels and every tensor component are retained. -/
theorem frequencyMixedSourceBilinear_polarization (q : XiZeroCopy) (branch : Bool)
    (w a d : ℂ) (x : Fin 4 → ℝ) :
    frequencyMixedSourceBilinear q branch w a d x =
      (4 : ℂ)⁻¹ •
        (literalMixedSource q branch (x 1)
          (frequencyEnvelope (w / 2) (physicalRate q branch) (a + d) x)
          (angularPoint x) -
          literalMixedSource q branch (x 1)
            (frequencyEnvelope (w / 2) (physicalRate q branch) (a - d) x)
            (angularPoint x)) := by
  let B := frequencyEnvelope (w / 2) (physicalRate q branch) a x
  let D := frequencyEnvelope (w / 2) (physicalRate q branch) d x
  have hplus : frequencyEnvelope (w / 2) (physicalRate q branch) (a + d) x = B + D := by
    dsimp only [B, D]
    exact frequencyEnvelope_add _ _ _ _ _
  have hminus : frequencyEnvelope (w / 2) (physicalRate q branch) (a - d) x = B - D := by
    dsimp only [B, D]
    exact frequencyEnvelope_sub _ _ _ _ _
  unfold frequencyMixedSourceBilinear
  change literalMixedSourceBilinear q branch (x 1) B D (angularPoint x) = _
  rw [hplus, hminus]
  let K := literalMixedSourceKernel q branch (x 1) (angularPoint x)
  let L : ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ :=
    { toFun := fun t => t • K
      map_add' := by
        intro u v
        exact add_smul u v K
      map_smul' := by
        intro c u
        change (c * u) • K = c • u • K
        rw [mul_smul] }
  change L (B * D) = _
  rw [linear_polarization L B D]
  have hL (u : ℂ) : L (u ^ (2 : ℕ)) =
      literalMixedSourceBilinear q branch (x 1) u u (angularPoint x) := by
    change u ^ (2 : ℕ) • K = (u * u) • K
    rw [pow_two]
  rw [hL, hL, literalMixedSourceBilinear_diag, literalMixedSourceBilinear_diag]

/-- Polarized source-pole residue cochain.  It is defined by the two literal primary legs,
rather than by choosing a square root of their product. -/
def frequencyDefectCochainBilinear (q : XiZeroCopy) (branch : Bool) (w r B D : ℂ)
    (z : Point) : Matrix (Fin 4) (Fin 4) ℂ :=
  (4 : ℂ)⁻¹ •
    (frequencyDefectCochain q branch w r (B + D) z -
      frequencyDefectCochain q branch w r (B - D) z)

private theorem frequencyMixedMetricField_smooth (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun x => frequencyMixedMetricField q branch w a x i j) p.val := by
  unfold frequencyMixedMetricField
  exact (frequencyStreamMetricField_smooth _ _ _ false _ p
    (frequency_response_c2 q branch p) i j).sub
      (contDiffAt_const.mul (frequencyStreamMetricField_smooth _ _ _ true _ p
        (frequency_square_c2 q p) i j))

private theorem ofMetricField_smul (F : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (p : D4BMBackground.ExteriorPoint)
    (hF : ∀ i j, ContDiffAt ℝ 2 (fun x => F x i j) p.val) (c : ℂ) :
    ofMetricField (fun x => c • F x) p.val =
      ofSpace (c • toSpace (ofMetricField F p.val)) := by
  have hs (i j : Fin 4) :
      ScalarTwoJet.ofField (fun x => c * F x i j) p.val =
        ScalarTwoJet.mul (ScalarTwoJet.constant c)
          (ScalarTwoJet.ofField (fun x => F x i j) p.val) := by
    rw [ScalarTwoJet.ofField_mul contDiffAt_const (hF i j),
      ScalarTwoJet.ofField_constant]
  apply Eq.trans (ofSpace_toSpace _).symm
  congr 1
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext k i j
      change (ScalarTwoJet.ofField (fun x => c * F x i j) p.val).first k = _
      rw [hs]
      simp [ScalarTwoJet.mul, ScalarTwoJet.constant, toSpace, ofMetricField]
      rfl
    · funext k l i j
      change (ScalarTwoJet.ofField (fun x => c * F x i j) p.val).second k l = _
      rw [hs]
      simp [ScalarTwoJet.mul, ScalarTwoJet.constant, toSpace, ofMetricField]
      rfl

private theorem cosmological_ofSpace_smul (J K : CoordinateMetricTwoJet 4 ℂ)
    (hJ : J.metric.det ≠ 0) (c Λ : ℂ) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological J (ofSpace (c • toSpace K)) Λ i j =
      c * CoordinateMetricTwoJet.Linearization.cosmological J K Λ i j := by
  simp only [CoordinateMetricTwoJet.Linearization.cosmological,
    CoordinateMetricTwoJet.Linearization.einstein_eq_fderiv _ _ hJ,
    toSpace_ofSpace, map_smul]
  change c * _ + Λ * (c * K.metric i j) = c * (_ + Λ * K.metric i j)
  ring

/-- Literal realization of the source-pole cochain by an actual off-frequency metric field.
This removes the former formal-jet gap; the remaining HB burden is its noncompact causal cap
pairing with the retained contact field. -/
theorem frequencyMixedMetricField_cosmological_source (q : XiZeroCopy) (branch : Bool)
    (p : D4BMBackground.ExteriorPoint) (w a : ℂ) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological
      (D4BMBackground.jet (p.val 1) (p.val 3))
      (ofMetricField (frequencyMixedMetricField q branch w a) p.val) (-3) i j +
      literalMixedSource q branch (p.val 1)
        (frequencyEnvelope (w / 2) (physicalRate q branch) a p.val)
        (angularPoint p.val) i j =
      (w - 2 * physicalRate q branch) *
        frequencyDefectCochain q branch w (p.val 1)
          (frequencyEnvelope (w / 2) (physicalRate q branch) a p.val)
          (angularPoint p.val) i j := by
  have hJ : (D4BMBackground.jet (p.val 1) (p.val 3)).metric.det ≠ 0 := by
    have hr : (p.val 1 : ℂ) ≠ 0 := by
      exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
    have hy : (p.val 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
    have hf : (p.val 1 : ℂ) ^ (2 : ℕ) - 1 ≠ 0 := by
      exact_mod_cast (by nlinarith [p.property.1] : (p.val 1) ^ (2 : ℕ) - 1 ≠ 0)
    change (D4BMBackground.metric (p.val 1) (p.val 3)).det ≠ 0
    rw [D4BMBackground.metric_det _ _ hf]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ (inv_ne_zero hy)))
  have hfield : frequencyMixedMetricField q branch w a =
      fun x i j =>
        frequencyStreamMetricField w (2 * physicalRate q branch) (a ^ (2 : ℕ)) false
            (fullAngularCovector q branch) x i j -
          (physicalRate q branch * (physicalRate q branch - 1) / 4) *
            frequencyStreamMetricField w (2 * physicalRate q branch) (a ^ (2 : ℕ)) true
              (fullSquareCovector q) x i j := by
    funext x i j
    unfold frequencyMixedMetricField
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hfield, frequency_ofMetricField_combination _ _ _ p.val
      (frequencyStreamMetricField_smooth _ _ _ false _ p (frequency_response_c2 q branch p))
      (frequencyStreamMetricField_smooth _ _ _ true _ p (frequency_square_c2 q p)),
    cosmological_frequencyMetricJetCombination _ _ _ hJ,
    frequencyStreamMetricField_jet _ _ _ false _ p (frequency_response_c2 q branch p)
      (fullAngularCovector_divergence q branch),
    frequencyStreamMetricField_jet _ _ _ true _ p (frequency_square_c2 q p)
      (fullSquareCovector_divergence q)]
  rw [← frequencyEnvelope_square]
  exact frozen_stream_cosmological_source_factor q branch p
    (frequencyEnvelope (w / 2) (physicalRate q branch) a p.val) w i j

/-- Literal cyclic Peierls bulk realization.  The two independent primary legs produce an
actual exterior metric field whose full cosmological Einstein residual is exactly the paired
literal mixed source plus the paired source-pole cochain.  No causal propagator, branch lift,
or target-dependent normalization is introduced. -/
theorem frequencyMixedMetricBilinear_cosmological_source (q : XiZeroCopy) (branch : Bool)
    (p : D4BMBackground.ExteriorPoint) (w a d : ℂ) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological
      (D4BMBackground.jet (p.val 1) (p.val 3))
      (ofMetricField (frequencyMixedMetricBilinear q branch w a d) p.val) (-3) i j +
      frequencyMixedSourceBilinear q branch w a d p.val i j =
      (w - 2 * physicalRate q branch) *
        frequencyDefectCochainBilinear q branch w (p.val 1)
          (frequencyEnvelope (w / 2) (physicalRate q branch) a p.val)
          (frequencyEnvelope (w / 2) (physicalRate q branch) d p.val)
          (angularPoint p.val) i j := by
  let Fp := frequencyMixedMetricField q branch w (a + d)
  let Fm := frequencyMixedMetricField q branch w (a - d)
  let c : ℂ := (4 : ℂ)⁻¹
  have hfield : frequencyMixedMetricBilinear q branch w a d =
      fun x i j => (c • Fp x) i j - (1 : ℂ) * (c • Fm x) i j := by
    funext x i j
    rw [frequencyMixedMetricBilinear_polarization]
    dsimp only [c, Fp, Fm]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hFp (u v : Fin 4) : ContDiffAt ℝ 2 (fun x => Fp x u v) p.val := by
    exact frequencyMixedMetricField_smooth q branch w (a + d) p u v
  have hFm (u v : Fin 4) : ContDiffAt ℝ 2 (fun x => Fm x u v) p.val := by
    exact frequencyMixedMetricField_smooth q branch w (a - d) p u v
  have hJ : (D4BMBackground.jet (p.val 1) (p.val 3)).metric.det ≠ 0 := by
    have hr : (p.val 1 : ℂ) ≠ 0 := by
      exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
    have hy : (p.val 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
    have hf : (p.val 1 : ℂ) ^ (2 : ℕ) - 1 ≠ 0 := by
      exact_mod_cast (by nlinarith [p.property.1] : (p.val 1) ^ (2 : ℕ) - 1 ≠ 0)
    change (D4BMBackground.metric (p.val 1) (p.val 3)).det ≠ 0
    rw [D4BMBackground.metric_det _ _ hf]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ (inv_ne_zero hy)))
  have hplus := frequencyMixedMetricField_cosmological_source q branch p w (a + d) i j
  have hminus := frequencyMixedMetricField_cosmological_source q branch p w (a - d) i j
  have hsource := frequencyMixedSourceBilinear_polarization q branch w a d p.val
  have hscale := ofMetricField_smul Fp p hFp c
  have hscale' := ofMetricField_smul Fm p hFm c
  rw [hfield, frequency_ofMetricField_combination 1 (fun x => c • Fp x) (fun x => c • Fm x) p.val
    (fun u v => (contDiffAt_const.mul (hFp u v)))
    (fun u v => (contDiffAt_const.mul (hFm u v))),
    cosmological_frequencyMetricJetCombination _ _ _ hJ 1 (-3) i j,
    hscale, cosmological_ofSpace_smul _ _ hJ c (-3) i j,
    hscale', cosmological_ofSpace_smul _ _ hJ c (-3) i j,
    hsource]
  dsimp only [frequencyDefectCochainBilinear]
  rw [frequencyEnvelope_add] at hplus
  rw [frequencyEnvelope_sub] at hminus
  rw [frequencyEnvelope_add, frequencyEnvelope_sub]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at ⊢
  dsimp only [Fp, Fm, c] at hplus hminus ⊢
  linear_combination (4 : ℂ)⁻¹ * hplus - (4 : ℂ)⁻¹ * hminus

/-- Diagonal source identity for the literal cyclic two-leg source-pole metric. -/
theorem frequencyMixedMetricBilinear_diagonal_cosmological_source (q : XiZeroCopy) (branch : Bool)
    (p : D4BMBackground.ExteriorPoint) (w a : ℂ) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological
      (D4BMBackground.jet (p.val 1) (p.val 3))
      (ofMetricField (frequencyMixedMetricBilinear q branch w a a) p.val) (-3) i j +
      frequencyMixedSourceBilinear q branch w a a p.val i j =
      (w - 2 * physicalRate q branch) *
        frequencyDefectCochain q branch w (p.val 1)
          (frequencyEnvelope (w / 2) (physicalRate q branch) a p.val)
          (angularPoint p.val) i j := by
  have hfield : frequencyMixedMetricBilinear q branch w a a =
      frequencyMixedMetricField q branch w a := by
    funext x
    exact frequencyMixedMetricBilinear_diag q branch w a x
  rw [hfield, frequencyMixedSourceBilinear_diag]
  exact frequencyMixedMetricField_cosmological_source q branch p w a i j

end

end RHTower.D4BMModularCore
