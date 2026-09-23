import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamGreenSourced
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamHarmonic
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamEinsteinLower
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalScalarMetric
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarLinearEinsteinEquation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMHorizonCovectorEquation

/-!
# The per-harmonic scalar–scalar `++` response as an actual metric field

The Kodama–Ishibashi-gauge harmonic metric field `harmonicMetricField s a f0 f1 f2 h Y` is the
envelope `a e^{2st} z^{s}` times the undressed radial functions `f0, f1, f2` (orbit block) and
`2r²h/y²` (angular block), times the angular profile `Y`. Its complete coordinate two-jet at an
exterior point is the harmonic stream jet `metricJet` with dressed twisted radial jets
(`harmonicMetricField_jet`). With the radial functions reconstructed from a solution of the sourced
master equation (`SourcedMasterData`) and a harmonic profile (`ΔY = μY`), the linearized cosmological
Einstein operator of the field plus the harmonic source tensor vanishes at every exterior point and
in every component (`harmonicMetricField_einstein`); for the scalar–scalar source and the corpus
Green response this is `greenSS_metricField_einstein`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet GaloisForLFunctions.HTGeometry.ScalarTwoJet
  GaloisForLFunctions.HTGeometry.TwistedRadial
open RHTower.D4BMFundamentalScalarMetric (envelope envelopeJet envelope_jet envelope_contDiffAt
  coordinateJet coordinate_jet)
open RHTower.D4BMScalarLinearEquation (angular_lift_jet coord)
open RHTower.D4BMHorizon (coordDeriv_commute)
open RHTower.D4BMMetricReconstruction (angularPoint ofMetricField)
open Filter Topology Set
open scoped ContDiff
noncomputable section

/-- The radial coefficient `2r²/y²` of the angular block. -/
def angularWeight (x : Fin 4 → ℝ) : ℂ :=
  (2 * ((x 1 : ℂ) * (x 1 : ℂ))) * ((x 3 : ℂ)⁻¹ * (x 3 : ℂ)⁻¹)

/-- Kodama–Ishibashi-gauge harmonic metric field: envelope × undressed radial functions × profile. -/
def harmonicMetricField (s a : ℂ) (f0 f1 f2 h : ℝ → ℂ) (Y : (Fin 2 → ℝ) → ℂ) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  !![envelope (2 * s) a x * Y (angularPoint x) * f0 (x 1),
      envelope (2 * s) a x * Y (angularPoint x) * f1 (x 1), 0, 0;
    envelope (2 * s) a x * Y (angularPoint x) * f1 (x 1),
      envelope (2 * s) a x * Y (angularPoint x) * f2 (x 1), 0, 0;
    0, 0, envelope (2 * s) a x * Y (angularPoint x) * (angularWeight x * h (x 1)), 0;
    0, 0, 0, envelope (2 * s) a x * Y (angularPoint x) * (angularWeight x * h (x 1))]

theorem coordinate_contDiffAt (k : Fin 4) (x : Fin 4 → ℝ) :
    ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x k : ℂ)) x := by
  have h : ContDiff ℝ 2 (fun x : Fin 4 → ℝ => (x k : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ k)
  exact h.contDiffAt

theorem coordinateJet_eq_coord (v : ℂ) (i : Fin 4) : coordinateJet v i = coord v i := by
  ext k l <;> simp [coordinateJet, coord]

theorem angularPoint_contDiff : ContDiff ℝ 2 angularPoint := by
  apply contDiff_pi.mpr
  intro k
  fin_cases k <;> exact contDiff_apply ℝ ℝ _

theorem angularWeight_jet (p : D4BMBackground.ExteriorPoint) :
    ofField angularWeight p.val =
      ((ScalarTwoJet.constant 2).mul ((coord (p.val 1) 1).mul (coord (p.val 1) 1))).mul
        (((coord (p.val 3) 3).inv).mul ((coord (p.val 3) 3).inv)) := by
  have hy : (p.val 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
  have hR := coordinate_contDiffAt 1 p.val
  have hY := coordinate_contDiffAt 3 p.val
  have hYi : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 3 : ℂ)⁻¹) p.val := hY.inv hy
  unfold angularWeight
  rw [ofField_mul (contDiffAt_const.mul (hR.mul hR)) (hYi.mul hYi),
    ofField_mul contDiffAt_const (hR.mul hR), ofField_constant, ofField_mul hR hR,
    ofField_mul hYi hYi, ofField_inv hY hy, coordinate_jet, coordinate_jet]
  simp only [coordinateJet_eq_coord]

/-- Two-jet of a smooth radial function lifted through the radial coordinate, with the twisted
second derivative. -/
theorem radialLift_jet (s : ℂ) {g : ℝ → ℂ} (hg : ContDiffOn ℝ ∞ g (Ioi 1))
    (p : D4BMBackground.ExteriorPoint) :
    ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => g (x 1)) p.val ∧
      ofField (fun x : Fin 4 → ℝ => g (x 1)) p.val =
        ⟨g (p.val 1), fun i => if i = 1 then deriv g (p.val 1) else 0,
          fun i j => if i = 1 ∧ j = 1 then deriv (deriv g) (p.val 1) else 0⟩ ∧
      twist s (twist s g) (p.val 1) =
        deriv (deriv g) (p.val 1) +
          (-(2 * s * (3 * (p.val 1 : ℂ) ^ (2 : ℕ) - 1)) / ((p.val 1 : ℂ) ^ (2 : ℕ) * ((p.val 1 : ℂ) ^ (2 : ℕ) - 1) ^ (2 : ℕ))) *
            g (p.val 1) +
          2 * s / ((p.val 1 : ℂ) * ((p.val 1 : ℂ) ^ (2 : ℕ) - 1)) * deriv g (p.val 1) +
          2 * s / ((p.val 1 : ℂ) * ((p.val 1 : ℂ) ^ (2 : ℕ) - 1)) *
            (deriv g (p.val 1) + 2 * s / ((p.val 1 : ℂ) * ((p.val 1 : ℂ) ^ (2 : ℕ) - 1)) * g (p.val 1)) := by
  have hr1 : 1 < p.val 1 := p.property.1
  have hr := (exterior_ne _ hr1).1
  have hf := (exterior_ne _ hr1).2
  have hgd : ∀ᶠ r in 𝓝 (p.val 1), HasDerivAt g (deriv g r) r := by
    filter_upwards [isOpen_Ioi.mem_nhds hr1] with r hr
    exact (differentiableAt_twistIter s hg 0 hr).hasDerivAt
  have hg1 : HasDerivAt (deriv g) (deriv (deriv g) (p.val 1)) (p.val 1) := by
    have hd : ContDiffOn ℝ ∞ (deriv g) (Ioi 1) := hg.deriv_of_isOpen isOpen_Ioi (by simp)
    exact (differentiableAt_twistIter s hd 0 hr1).hasDerivAt
  refine ⟨?_, ofField_radialLift hgd hg1, ?_⟩
  · exact ((hg.contDiffAt (isOpen_Ioi.mem_nhds hr1)).of_le (WithTop.coe_le_coe.mpr le_top)).comp p.val
      (contDiff_apply ℝ ℝ 1).contDiffAt
  · show deriv (twist s g) (p.val 1) + _ * twist s g (p.val 1) = _
    rw [(hasDerivAt_twist s hr hf hgd hg1).deriv]
    rfl

/-- Jet of an orbit-block component `E · Y · g(r)`. -/
theorem orbit_component_jet (s a : ℂ) (Y : (Fin 2 → ℝ) → ℂ) {g : ℝ → ℂ}
    (hg : ContDiffOn ℝ ∞ g (Ioi 1)) (p : D4BMBackground.ExteriorPoint)
    (hY : ContDiffAt ℝ 2 Y (angularPoint p.val)) :
    ofField (fun x => envelope (2 * s) a x * Y (angularPoint x) * g (x 1)) p.val =
      (orbitJet (2 * s) (envelope (2 * s) a p.val * g (p.val 1))
        (envelope (2 * s) a p.val * twist s g (p.val 1))
        (envelope (2 * s) a p.val * twist s (twist s g) (p.val 1))).mul
        (angularJet (Y (angularPoint p.val)) (coordDeriv 0 Y (angularPoint p.val))
          (coordDeriv 1 Y (angularPoint p.val)) (coordDeriv 0 (coordDeriv 0 Y) (angularPoint p.val))
          (coordDeriv 0 (coordDeriv 1 Y) (angularPoint p.val))
          (coordDeriv 1 (coordDeriv 1 Y) (angularPoint p.val))) := by
  obtain ⟨hgl, hgj, h2⟩ := radialLift_jet s hg p
  have hE := envelope_contDiffAt (2 * s) a p 2
  have hYl : ContDiffAt ℝ 2 (fun x => Y (angularPoint x)) p.val :=
    hY.comp p.val angularPoint_contDiff.contDiffAt
  rw [ofField_mul (hE.mul hYl) hgl, ofField_mul hE hYl, envelope_jet, angular_lift_jet Y p.val hY, hgj,
    coordDeriv_commute hY 1 0, h2]
  simp only [twist]
  generalize envelope (2 * s) a p.val = B
  generalize Y (angularPoint p.val) = Y0
  generalize coordDeriv 0 Y (angularPoint p.val) = Yx
  generalize coordDeriv 1 Y (angularPoint p.val) = Yy
  generalize coordDeriv 0 (coordDeriv 0 Y) (angularPoint p.val) = Yxx
  generalize coordDeriv 0 (coordDeriv 1 Y) (angularPoint p.val) = Yxy
  generalize coordDeriv 1 (coordDeriv 1 Y) (angularPoint p.val) = Yyy
  generalize g (p.val 1) = g0
  generalize deriv g (p.val 1) = g1
  generalize deriv (deriv g) (p.val 1) = g2
  have hr := (exterior_ne _ p.property.1).1
  have hf := (exterior_ne _ p.property.1).2
  generalize (p.val 1 : ℂ) = r at hr hf ⊢
  ext i j
  · simp only [ScalarTwoJet.mul, envelopeJet, orbitJet, angularJet, coord, ScalarTwoJet.inv, ScalarTwoJet.constant, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Fin.isValue, Fin.reduceEq, if_true, if_false, and_true, and_false, true_and, false_and, and_self, ite_true, ite_false]
    ring
  · fin_cases i <;> simp only [ScalarTwoJet.mul, envelopeJet, orbitJet, angularJet, coord, ScalarTwoJet.inv, ScalarTwoJet.constant, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Fin.isValue, Fin.reduceEq, if_true, if_false, and_true, and_false, true_and, false_and, and_self, ite_true, ite_false] <;> ring
  · fin_cases i <;> fin_cases j <;> simp only [ScalarTwoJet.mul, envelopeJet, orbitJet, angularJet, coord, ScalarTwoJet.inv, ScalarTwoJet.constant, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Fin.isValue, Fin.reduceEq, if_true, if_false, and_true, and_false, true_and, false_and, and_self, ite_true, ite_false] <;> field_simp <;> ring

/-- The angular-block jet `(2r²/y²) · orbit · angular` of the stream metric jet. -/
def angularBlockJet (w r y H H1 H2 P Px Py Pxx Pxy Pyy : ℂ) : ScalarTwoJet (Fin 4) ℂ :=
  ((((ScalarTwoJet.constant 2).mul ((coord r 1).mul (coord r 1))).mul
    (((coord y 3).inv).mul ((coord y 3).inv))).mul (orbitJet w H H1 H2)).mul
    (angularJet P Px Py Pxx Pxy Pyy)

/-- Jet of an angular-block component `E · Y · (2r²/y²) h(r)`. -/
theorem angular_component_jet (s a : ℂ) (Y : (Fin 2 → ℝ) → ℂ) {h : ℝ → ℂ}
    (hh : ContDiffOn ℝ ∞ h (Ioi 1)) (p : D4BMBackground.ExteriorPoint)
    (hY : ContDiffAt ℝ 2 Y (angularPoint p.val)) :
    ofField (fun x => envelope (2 * s) a x * Y (angularPoint x) * (angularWeight x * h (x 1))) p.val =
      angularBlockJet (2 * s) (p.val 1) (p.val 3) (envelope (2 * s) a p.val * h (p.val 1))
        (envelope (2 * s) a p.val * twist s h (p.val 1))
        (envelope (2 * s) a p.val * twist s (twist s h) (p.val 1))
        (Y (angularPoint p.val)) (coordDeriv 0 Y (angularPoint p.val))
        (coordDeriv 1 Y (angularPoint p.val)) (coordDeriv 0 (coordDeriv 0 Y) (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 1 Y) (angularPoint p.val))
        (coordDeriv 1 (coordDeriv 1 Y) (angularPoint p.val)) := by
  obtain ⟨hhl, hhj, h2⟩ := radialLift_jet s hh p
  have hE := envelope_contDiffAt (2 * s) a p 2
  have hYl : ContDiffAt ℝ 2 (fun x => Y (angularPoint x)) p.val :=
    hY.comp p.val angularPoint_contDiff.contDiffAt
  have hy : (p.val 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
  have hW : ContDiffAt ℝ 2 angularWeight p.val := by
    unfold angularWeight
    exact (contDiffAt_const.mul ((coordinate_contDiffAt 1 p.val).mul (coordinate_contDiffAt 1 p.val))).mul
      (((coordinate_contDiffAt 3 p.val).inv hy).mul ((coordinate_contDiffAt 3 p.val).inv hy))
  rw [ofField_mul (hE.mul hYl) (hW.mul hhl), ofField_mul hE hYl, ofField_mul hW hhl, envelope_jet,
    angular_lift_jet Y p.val hY, hhj, angularWeight_jet, coordDeriv_commute hY 1 0, h2]
  simp only [twist]
  generalize envelope (2 * s) a p.val = B
  generalize Y (angularPoint p.val) = Y0
  generalize coordDeriv 0 Y (angularPoint p.val) = Yx
  generalize coordDeriv 1 Y (angularPoint p.val) = Yy
  generalize coordDeriv 0 (coordDeriv 0 Y) (angularPoint p.val) = Yxx
  generalize coordDeriv 0 (coordDeriv 1 Y) (angularPoint p.val) = Yxy
  generalize coordDeriv 1 (coordDeriv 1 Y) (angularPoint p.val) = Yyy
  generalize h (p.val 1) = h0
  generalize deriv h (p.val 1) = h1
  generalize deriv (deriv h) (p.val 1) = h2'
  have hr := (exterior_ne _ p.property.1).1
  have hf := (exterior_ne _ p.property.1).2
  have hy : (p.val 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
  generalize (p.val 1 : ℂ) = r at hr hf ⊢
  generalize (p.val 3 : ℂ) = yv at hy ⊢
  unfold angularBlockJet
  ext i j
  · simp only [ScalarTwoJet.mul, envelopeJet, orbitJet, angularJet, coord, ScalarTwoJet.inv, ScalarTwoJet.constant, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Fin.isValue, Fin.reduceEq, if_true, if_false, and_true, and_false, true_and, false_and, and_self, ite_true, ite_false]
    ring
  · fin_cases i <;> simp only [ScalarTwoJet.mul, envelopeJet, orbitJet, angularJet, coord, ScalarTwoJet.inv, ScalarTwoJet.constant, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Fin.isValue, Fin.reduceEq, if_true, if_false, and_true, and_false, true_and, false_and, and_self, ite_true, ite_false] <;> ring
  · fin_cases i <;> fin_cases j <;> simp only [ScalarTwoJet.mul, envelopeJet, orbitJet, angularJet, coord, ScalarTwoJet.inv, ScalarTwoJet.constant, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Fin.isValue, Fin.reduceEq, if_true, if_false, and_true, and_false, true_and, false_and, and_self, ite_true, ite_false] <;> field_simp <;> ring

/-! ## Linearity of the harmonic coefficients in the jets -/

theorem harmonicTT_smul (s r μ B F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) :
    harmonicTT s r μ (B * F0) (B * F01) (B * F02) (B * F1) (B * F11) (B * F12) (B * F2) (B * F21) (B * F22) (B * H) (B * H1) (B * H2) =
      B * harmonicTT s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 := by
  unfold harmonicTT; ring
theorem harmonicTR_smul (s r μ B F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) :
    harmonicTR s r μ (B * F0) (B * F01) (B * F02) (B * F1) (B * F11) (B * F12) (B * F2) (B * F21) (B * F22) (B * H) (B * H1) (B * H2) =
      B * harmonicTR s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 := by
  unfold harmonicTR; ring
theorem harmonicRR_smul (s r μ B F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) :
    harmonicRR s r μ (B * F0) (B * F01) (B * F02) (B * F1) (B * F11) (B * F12) (B * F2) (B * F21) (B * F22) (B * H) (B * H1) (B * H2) =
      B * harmonicRR s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 := by
  unfold harmonicRR; ring
theorem harmonicT_smul (s r μ B F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) :
    harmonicT s r μ (B * F0) (B * F01) (B * F02) (B * F1) (B * F11) (B * F12) (B * F2) (B * F21) (B * F22) (B * H) (B * H1) (B * H2) =
      B * harmonicT s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 := by
  unfold harmonicT; ring
theorem harmonicR_smul (s r μ B F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) :
    harmonicR s r μ (B * F0) (B * F01) (B * F02) (B * F1) (B * F11) (B * F12) (B * F2) (B * F21) (B * F22) (B * H) (B * H1) (B * H2) =
      B * harmonicR s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 := by
  unfold harmonicR; ring
theorem harmonicTF_smul (s r μ B F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) :
    harmonicTF s r μ (B * F0) (B * F01) (B * F02) (B * F1) (B * F11) (B * F12) (B * F2) (B * F21) (B * F22) (B * H) (B * H1) (B * H2) =
      B * harmonicTF s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 := by
  unfold harmonicTF; ring
theorem harmonicL_smul (s r μ B F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ) :
    harmonicL s r μ (B * F0) (B * F01) (B * F02) (B * F1) (B * F11) (B * F12) (B * F2) (B * F21) (B * F22) (B * H) (B * H1) (B * H2) =
      B * harmonicL s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 := by
  unfold harmonicL; ring

/-! ## The metric two-jet and the sourced Einstein equation -/

theorem CoordinateMetricTwoJet.ext' {A B : CoordinateMetricTwoJet 4 ℂ} (hm : A.metric = B.metric)
    (hf : A.first = B.first) (hs : A.second = B.second) : A = B := by
  cases A; cases B
  simp only at hm hf hs
  subst hm hf hs
  rfl

/-- The jet matrix of the harmonic stream metric jet. -/
def harmonicJetMatrix (w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy : ℂ) :
    Matrix (Fin 4) (Fin 4) (ScalarTwoJet (Fin 4) ℂ) :=
  !![(orbitJet w F0 F01 F02).mul (angularJet P Px Py Pxx Pxy Pyy),
      (orbitJet w F1 F11 F12).mul (angularJet P Px Py Pxx Pxy Pyy), ScalarTwoJet.constant 0, ScalarTwoJet.constant 0;
    (orbitJet w F1 F11 F12).mul (angularJet P Px Py Pxx Pxy Pyy),
      (orbitJet w F2 F21 F22).mul (angularJet P Px Py Pxx Pxy Pyy), ScalarTwoJet.constant 0, ScalarTwoJet.constant 0;
    ScalarTwoJet.constant 0, ScalarTwoJet.constant 0, angularBlockJet w r y H H1 H2 P Px Py Pxx Pxy Pyy, ScalarTwoJet.constant 0;
    ScalarTwoJet.constant 0, ScalarTwoJet.constant 0, ScalarTwoJet.constant 0, angularBlockJet w r y H H1 H2 P Px Py Pxx Pxy Pyy]

theorem metricJet_eq_matrix (w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy : ℂ) :
    metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy =
      ⟨fun i j => (harmonicJetMatrix w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy i j).value,
        fun k i j => (harmonicJetMatrix w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy i j).first k,
        fun k l i j => (harmonicJetMatrix w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy i j).second k l⟩ :=
  rfl

/-- The complete coordinate two-jet of the harmonic metric field is the harmonic stream jet with
dressed twisted radial jets. -/
theorem harmonicMetricField_jet (s a : ℂ) {f0 f1 f2 h : ℝ → ℂ} (hf0 : ContDiffOn ℝ ∞ f0 (Ioi 1))
    (hf1 : ContDiffOn ℝ ∞ f1 (Ioi 1)) (hf2 : ContDiffOn ℝ ∞ f2 (Ioi 1)) (hh : ContDiffOn ℝ ∞ h (Ioi 1))
    (Y : (Fin 2 → ℝ) → ℂ) (p : D4BMBackground.ExteriorPoint) (hY : ContDiffAt ℝ 2 Y (angularPoint p.val)) :
    ofMetricField (harmonicMetricField s a f0 f1 f2 h Y) p.val =
      metricJet (2 * s) (p.val 1) (p.val 3)
        (envelope (2 * s) a p.val * f0 (p.val 1)) (envelope (2 * s) a p.val * twist s f0 (p.val 1))
        (envelope (2 * s) a p.val * twist s (twist s f0) (p.val 1))
        (envelope (2 * s) a p.val * f1 (p.val 1)) (envelope (2 * s) a p.val * twist s f1 (p.val 1))
        (envelope (2 * s) a p.val * twist s (twist s f1) (p.val 1))
        (envelope (2 * s) a p.val * f2 (p.val 1)) (envelope (2 * s) a p.val * twist s f2 (p.val 1))
        (envelope (2 * s) a p.val * twist s (twist s f2) (p.val 1))
        (envelope (2 * s) a p.val * h (p.val 1)) (envelope (2 * s) a p.val * twist s h (p.val 1))
        (envelope (2 * s) a p.val * twist s (twist s h) (p.val 1))
        (Y (angularPoint p.val)) (coordDeriv 0 Y (angularPoint p.val)) (coordDeriv 1 Y (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 0 Y) (angularPoint p.val)) (coordDeriv 0 (coordDeriv 1 Y) (angularPoint p.val))
        (coordDeriv 1 (coordDeriv 1 Y) (angularPoint p.val)) := by
  have h00 := orbit_component_jet s a Y hf0 p hY
  have h01 := orbit_component_jet s a Y hf1 p hY
  have h11 := orbit_component_jet s a Y hf2 p hY
  have hL := angular_component_jet s a Y hh p hY
  have hcomp : ∀ i j, ofField (fun x => harmonicMetricField s a f0 f1 f2 h Y x i j) p.val =
      harmonicJetMatrix (2 * s) (p.val 1) (p.val 3)
        (envelope (2 * s) a p.val * f0 (p.val 1)) (envelope (2 * s) a p.val * twist s f0 (p.val 1))
        (envelope (2 * s) a p.val * twist s (twist s f0) (p.val 1))
        (envelope (2 * s) a p.val * f1 (p.val 1)) (envelope (2 * s) a p.val * twist s f1 (p.val 1))
        (envelope (2 * s) a p.val * twist s (twist s f1) (p.val 1))
        (envelope (2 * s) a p.val * f2 (p.val 1)) (envelope (2 * s) a p.val * twist s f2 (p.val 1))
        (envelope (2 * s) a p.val * twist s (twist s f2) (p.val 1))
        (envelope (2 * s) a p.val * h (p.val 1)) (envelope (2 * s) a p.val * twist s h (p.val 1))
        (envelope (2 * s) a p.val * twist s (twist s h) (p.val 1))
        (Y (angularPoint p.val)) (coordDeriv 0 Y (angularPoint p.val)) (coordDeriv 1 Y (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 0 Y) (angularPoint p.val)) (coordDeriv 0 (coordDeriv 1 Y) (angularPoint p.val))
        (coordDeriv 1 (coordDeriv 1 Y) (angularPoint p.val)) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [harmonicMetricField, harmonicJetMatrix, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Fin.isValue] <;>
      first | exact ofField_constant 0 p.val | exact h00 | exact h01 | exact h11 | exact hL
  rw [metricJet_eq_matrix]
  refine CoordinateMetricTwoJet.ext' ?_ ?_ ?_
  · funext i j
    exact congrArg ScalarTwoJet.value (hcomp i j)
  · funext k i j
    exact congrArg (fun J => ScalarTwoJet.first J k) (hcomp i j)
  · funext k l i j
    exact congrArg (fun J => ScalarTwoJet.second J k l) (hcomp i j)

theorem recForm_contDiffOn {n : ℕ} (cs : Fin n → List ℂ) (P Q : ℕ) (X : Fin n → ℝ → ℂ)
    (hX : ∀ i, ContDiffOn ℝ ∞ (X i) (Ioi 1)) :
    ContDiffOn ℝ ∞ (fun r => ∑ i, ratCoef (cs i) P Q r * X i r) (Ioi 1) :=
  ContDiffOn.sum fun i _ => (contDiffOn_ratCoef _ _ _).mul (hX i)

/-- Smoothness of the symbol functions of a reconstruction chain. -/
theorem symbolVec_contDiffOn (s : ℂ) {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ}
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hTT : ContDiffOn ℝ ∞ tTT (Ioi 1)) (hTR : ContDiffOn ℝ ∞ tTR (Ioi 1))
    (hRR : ContDiffOn ℝ ∞ tRR (Ioi 1)) (hT : ContDiffOn ℝ ∞ tT (Ioi 1)) (hR : ContDiffOn ℝ ∞ tR (Ioi 1))
    (hTF : ContDiffOn ℝ ∞ tTF (Ioi 1)) (hL : ContDiffOn ℝ ∞ tL (Ioi 1)) (k : ℕ) :
    ContDiffOn ℝ ∞ (twistIter s k y) (Ioi 1) ∧ ContDiffOn ℝ ∞ (twistIter s k tTT) (Ioi 1) ∧
      ContDiffOn ℝ ∞ (twistIter s k tTR) (Ioi 1) ∧ ContDiffOn ℝ ∞ (twistIter s k tRR) (Ioi 1) ∧
      ContDiffOn ℝ ∞ (twistIter s k tT) (Ioi 1) ∧ ContDiffOn ℝ ∞ (twistIter s k tR) (Ioi 1) ∧
      ContDiffOn ℝ ∞ (twistIter s k tTF) (Ioi 1) ∧ ContDiffOn ℝ ∞ (twistIter s k tL) (Ioi 1) :=
  ⟨contDiffOn_twistIter s hy k, contDiffOn_twistIter s hTT k, contDiffOn_twistIter s hTR k,
    contDiffOn_twistIter s hRR k, contDiffOn_twistIter s hT k, contDiffOn_twistIter s hR k,
    contDiffOn_twistIter s hTF k, contDiffOn_twistIter s hL k⟩

theorem recF0R_contDiffOn (s μ : ℂ) {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ}
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hTT : ContDiffOn ℝ ∞ tTT (Ioi 1)) (hTR : ContDiffOn ℝ ∞ tTR (Ioi 1))
    (hRR : ContDiffOn ℝ ∞ tRR (Ioi 1)) (hT : ContDiffOn ℝ ∞ tT (Ioi 1)) (hR : ContDiffOn ℝ ∞ tR (Ioi 1))
    (hTF : ContDiffOn ℝ ∞ tTF (Ioi 1)) (hL : ContDiffOn ℝ ∞ tL (Ioi 1)) :
    ContDiffOn ℝ ∞ (recF0R s μ y tTT tTR tRR tT tR tTF tL) (Ioi 1) := by
  unfold recF0R
  refine recForm_contDiffOn _ _ _ _ ?_
  intro i
  fin_cases i <;> simp only [recF0X, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val', Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Fin.isValue] <;>
    exact contDiffOn_twistIter s (by assumption) _

theorem recF1R_contDiffOn (s μ : ℂ) {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ}
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hTT : ContDiffOn ℝ ∞ tTT (Ioi 1)) (hTR : ContDiffOn ℝ ∞ tTR (Ioi 1))
    (hRR : ContDiffOn ℝ ∞ tRR (Ioi 1)) (hT : ContDiffOn ℝ ∞ tT (Ioi 1)) (hR : ContDiffOn ℝ ∞ tR (Ioi 1))
    (hTF : ContDiffOn ℝ ∞ tTF (Ioi 1)) (hL : ContDiffOn ℝ ∞ tL (Ioi 1)) :
    ContDiffOn ℝ ∞ (recF1R s μ y tTT tTR tRR tT tR tTF tL) (Ioi 1) := by
  unfold recF1R
  refine recForm_contDiffOn _ _ _ _ ?_
  intro i
  fin_cases i <;> simp only [recF1X, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val', Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Fin.isValue] <;>
    exact contDiffOn_twistIter s (by assumption) _

theorem recF2R_contDiffOn (s μ : ℂ) {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ}
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hTT : ContDiffOn ℝ ∞ tTT (Ioi 1)) (hTR : ContDiffOn ℝ ∞ tTR (Ioi 1))
    (hRR : ContDiffOn ℝ ∞ tRR (Ioi 1)) (hT : ContDiffOn ℝ ∞ tT (Ioi 1)) (hR : ContDiffOn ℝ ∞ tR (Ioi 1))
    (hTF : ContDiffOn ℝ ∞ tTF (Ioi 1)) (hL : ContDiffOn ℝ ∞ tL (Ioi 1)) :
    ContDiffOn ℝ ∞ (recF2R s μ y tTT tTR tRR tT tR tTF tL) (Ioi 1) := by
  unfold recF2R
  refine recForm_contDiffOn _ _ _ _ ?_
  intro i
  fin_cases i <;> simp only [recF2X, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val', Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Fin.isValue] <;>
    exact contDiffOn_twistIter s (by assumption) _

theorem recHR_contDiffOn (s μ : ℂ) {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ}
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hTT : ContDiffOn ℝ ∞ tTT (Ioi 1)) (hTR : ContDiffOn ℝ ∞ tTR (Ioi 1))
    (hRR : ContDiffOn ℝ ∞ tRR (Ioi 1)) (hT : ContDiffOn ℝ ∞ tT (Ioi 1)) (hR : ContDiffOn ℝ ∞ tR (Ioi 1))
    (hTF : ContDiffOn ℝ ∞ tTF (Ioi 1)) (hL : ContDiffOn ℝ ∞ tL (Ioi 1)) :
    ContDiffOn ℝ ∞ (recHR s μ y tTT tTR tRR tT tR tTF tL) (Ioi 1) := by
  unfold recHR
  refine recForm_contDiffOn _ _ _ _ ?_
  intro i
  fin_cases i <;> simp only [recHX, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val', Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Fin.isValue] <;>
    exact contDiffOn_twistIter s (by assumption) _

/-- The harmonic source tensor `B · (τ_A ⊗ harmonic structures of Y)`. -/
def harmonicSourceTensor (μ B y τTT τTR τRR τT τR τTF τL P Px Py Pxx Pxy Pyy : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![B * τTT * P, B * τTR * P, B * τT * Px, B * τT * Py;
    B * τTR * P, B * τRR * P, B * τR * Px, B * τR * Py;
    B * τT * Px, B * τR * Px, B * (τL * P / y ^ (2 : ℕ) + τTF * (Pxx - Py / y - μ * P / (2 * y ^ (2 : ℕ)))), B * (τTF * (Pxy + Px / y));
    B * τT * Py, B * τR * Py, B * (τTF * (Pxy + Px / y)), B * (τL * P / y ^ (2 : ℕ) - τTF * (Pxx - Py / y - μ * P / (2 * y ^ (2 : ℕ))))]

/-- The reconstructed harmonic metric field solves the sourced linearized Einstein equation with the
harmonic source tensor, in every component and at every exterior point. -/
theorem harmonicMetricField_einstein (s μ a : ℂ) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0)
    {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ} (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL)
    (hy : ContDiffOn ℝ ∞ y (Ioi 1)) (hTT : ContDiffOn ℝ ∞ tTT (Ioi 1)) (hTR : ContDiffOn ℝ ∞ tTR (Ioi 1))
    (hRR : ContDiffOn ℝ ∞ tRR (Ioi 1)) (hT : ContDiffOn ℝ ∞ tT (Ioi 1)) (hR : ContDiffOn ℝ ∞ tR (Ioi 1))
    (hTF : ContDiffOn ℝ ∞ tTF (Ioi 1)) (hL : ContDiffOn ℝ ∞ tL (Ioi 1))
    (Y : (Fin 2 → ℝ) → ℂ) (hY : ∀ z : Fin 2 → ℝ, 0 < z 1 → ContDiffAt ℝ 2 Y z)
    (hYeig : ∀ z : Fin 2 → ℝ, 0 < z 1 →
      coordDeriv 1 (coordDeriv 1 Y) z = μ * Y z / (z 1 : ℂ) ^ (2 : ℕ) - coordDeriv 0 (coordDeriv 0 Y) z)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    Linearization.cosmological (D4BMBackground.jet (p.val 1) (p.val 3))
      (ofMetricField (harmonicMetricField s a (recF0R s μ y tTT tTR tRR tT tR tTF tL) (recF1R s μ y tTT tTR tRR tT tR tTF tL) (recF2R s μ y tTT tTR tRR tT tR tTF tL) (recHR s μ y tTT tTR tRR tT tR tTF tL) Y) p.val)
      (-3) i j +
      harmonicSourceTensor μ (envelope (2 * s) a p.val) (p.val 3) (tTT (p.val 1)) (tTR (p.val 1)) (tRR (p.val 1))
        (tT (p.val 1)) (tR (p.val 1)) (tTF (p.val 1)) (tL (p.val 1))
        (Y (angularPoint p.val)) (coordDeriv 0 Y (angularPoint p.val)) (coordDeriv 1 Y (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 0 Y) (angularPoint p.val)) (coordDeriv 0 (coordDeriv 1 Y) (angularPoint p.val))
        (coordDeriv 1 (coordDeriv 1 Y) (angularPoint p.val)) i j = 0 := by
  have hr1 : 1 < p.val 1 := p.property.1
  have hr := (exterior_ne _ hr1).1
  have hf := (exterior_ne _ hr1).2
  have hy3 : (p.val 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
  have hz : 0 < angularPoint p.val 1 := p.property.2
  have hYz := hY _ hz
  have hP : coordDeriv 1 (coordDeriv 1 Y) (angularPoint p.val) =
      μ * Y (angularPoint p.val) / (p.val 3 : ℂ) ^ (2 : ℕ) - coordDeriv 0 (coordDeriv 0 Y) (angularPoint p.val) :=
    hYeig _ hz
  rw [harmonicMetricField_jet s a (recF0R_contDiffOn s μ hy hTT hTR hRR hT hR hTF hL)
    (recF1R_contDiffOn s μ hy hTT hTR hRR hT hR hTF hL) (recF2R_contDiffOn s μ hy hTT hTR hRR hT hR hTF hL)
    (recHR_contDiffOn s μ hy hTT hTR hRR hT hR hTF hL) Y p hYz]
  generalize hB : envelope (2 * s) a p.val = B
  generalize hzz : angularPoint p.val = z at hP hYz ⊢
  generalize hrr : p.val 1 = r at hr hf hr1 ⊢
  generalize hyy : p.val 3 = y at hy3 hP ⊢
  have hy : (y : ℂ) ≠ 0 := hy3
  fin_cases i <;> fin_cases j <;>
    simp only [harmonicSourceTensor, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Matrix.empty_val', Fin.isValue]
  · rw [harmonic_0_0 (μ := μ) hr hy hf hP, harmonicTT_smul]
    linear_combination (B * Y z) * sourced_equation_TT hs hμ h hr1
  · rw [harmonic_0_1 (μ := μ) hr hy hf hP, harmonicTR_smul]
    linear_combination (B * Y z) * sourced_equation_TR hs hμ h hr1
  · rw [harmonic_0_2 (μ := μ) hr hy hf, harmonicT_smul]
    linear_combination (B * coordDeriv 0 Y z) * sourced_equation_T hs hμ h hr1
  · rw [harmonic_0_3 (μ := μ) hr hy hf, harmonicT_smul]
    linear_combination (B * coordDeriv 1 Y z) * sourced_equation_T hs hμ h hr1
  · rw [metricJet_cosmological_symm_1_0 hr hy hf, harmonic_0_1 (μ := μ) hr hy hf hP, harmonicTR_smul]
    linear_combination (B * Y z) * sourced_equation_TR hs hμ h hr1
  · rw [harmonic_1_1 (μ := μ) hr hy hf hP, harmonicRR_smul]
    linear_combination (B * Y z) * sourced_equation_RR hs hμ h hr1
  · rw [harmonic_1_2 (μ := μ) hr hy hf, harmonicR_smul]
    linear_combination (B * coordDeriv 0 Y z) * sourced_equation_R hs hμ h hr1
  · rw [harmonic_1_3 (μ := μ) hr hy hf, harmonicR_smul]
    linear_combination (B * coordDeriv 1 Y z) * sourced_equation_R hs hμ h hr1
  · rw [metricJet_cosmological_symm_2_0 hr hy hf, harmonic_0_2 (μ := μ) hr hy hf, harmonicT_smul]
    linear_combination (B * coordDeriv 0 Y z) * sourced_equation_T hs hμ h hr1
  · rw [metricJet_cosmological_symm_2_1 hr hy hf, harmonic_1_2 (μ := μ) hr hy hf, harmonicR_smul]
    linear_combination (B * coordDeriv 0 Y z) * sourced_equation_R hs hμ h hr1
  · rw [harmonic_2_2 (μ := μ) hr hy hf hP, harmonicL_smul, harmonicTF_smul]
    linear_combination (B * Y z / (y : ℂ) ^ (2 : ℕ)) * sourced_equation_L hs hμ h hr1 + (B * (coordDeriv 0 (coordDeriv 0 Y) z - coordDeriv 1 Y z / y - μ * Y z / (2 * (y : ℂ) ^ (2 : ℕ)))) * sourced_equation_TF hs hμ h hr1
  · rw [harmonic_2_3 (μ := μ) hr hy hf, harmonicTF_smul]
    linear_combination (B * (coordDeriv 0 (coordDeriv 1 Y) z + coordDeriv 0 Y z / y)) * sourced_equation_TF hs hμ h hr1
  · rw [metricJet_cosmological_symm_3_0 hr hy hf, harmonic_0_3 (μ := μ) hr hy hf, harmonicT_smul]
    linear_combination (B * coordDeriv 1 Y z) * sourced_equation_T hs hμ h hr1
  · rw [metricJet_cosmological_symm_3_1 hr hy hf, harmonic_1_3 (μ := μ) hr hy hf, harmonicR_smul]
    linear_combination (B * coordDeriv 1 Y z) * sourced_equation_R hs hμ h hr1
  · rw [metricJet_cosmological_symm_3_2 hr hy hf, harmonic_2_3 (μ := μ) hr hy hf, harmonicTF_smul]
    linear_combination (B * (coordDeriv 0 (coordDeriv 1 Y) z + coordDeriv 0 Y z / y)) * sourced_equation_TF hs hμ h hr1
  · rw [harmonic_3_3 (μ := μ) hr hy hf, harmonicL_smul, harmonicTF_smul]
    linear_combination (B * Y z / (y : ℂ) ^ (2 : ℕ)) * sourced_equation_L hs hμ h hr1 - (B * (coordDeriv 0 (coordDeriv 0 Y) z - coordDeriv 1 Y z / y - μ * Y z / (2 * (y : ℂ) ^ (2 : ℕ)))) * sourced_equation_TF hs hμ h hr1

/-- The scalar–scalar `++` harmonic response built from the corpus Green function, as an actual
metric field: it solves the sourced linearized Einstein equation with the scalar–scalar harmonic
source tensor at every exterior point and in every component. -/
theorem greenSS_metricField_einstein (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hs : dictRate n chi ≠ 0)
    (hμ : (2 : ℂ) - dictEigen chi ≠ 0) (amp : ℂ) (Y : (Fin 2 → ℝ) → ℂ)
    (hY : ∀ z : Fin 2 → ℝ, 0 < z 1 → ContDiffAt ℝ 2 Y z)
    (hYeig : ∀ z : Fin 2 → ℝ, 0 < z 1 →
      coordDeriv 1 (coordDeriv 1 Y) z = dictEigen chi * Y z / (z 1 : ℂ) ^ (2 : ℕ) - coordDeriv 0 (coordDeriv 0 Y) z)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    Linearization.cosmological (D4BMBackground.jet (p.val 1) (p.val 3))
      (ofMetricField (harmonicMetricField (dictRate n chi) amp (recF0R (dictRate n chi) (dictEigen chi) (greenSS n chi a b) (srcTT (dictRate n chi) (dictEigen chi)) (srcTR (dictRate n chi) (dictEigen chi)) (srcRR (dictRate n chi) (dictEigen chi)) (srcT (dictRate n chi) (dictEigen chi)) (srcR (dictRate n chi) (dictEigen chi)) (srcTF (dictRate n chi) (dictEigen chi)) (srcL (dictRate n chi) (dictEigen chi))) (recF1R (dictRate n chi) (dictEigen chi) (greenSS n chi a b) (srcTT (dictRate n chi) (dictEigen chi)) (srcTR (dictRate n chi) (dictEigen chi)) (srcRR (dictRate n chi) (dictEigen chi)) (srcT (dictRate n chi) (dictEigen chi)) (srcR (dictRate n chi) (dictEigen chi)) (srcTF (dictRate n chi) (dictEigen chi)) (srcL (dictRate n chi) (dictEigen chi))) (recF2R (dictRate n chi) (dictEigen chi) (greenSS n chi a b) (srcTT (dictRate n chi) (dictEigen chi)) (srcTR (dictRate n chi) (dictEigen chi)) (srcRR (dictRate n chi) (dictEigen chi)) (srcT (dictRate n chi) (dictEigen chi)) (srcR (dictRate n chi) (dictEigen chi)) (srcTF (dictRate n chi) (dictEigen chi)) (srcL (dictRate n chi) (dictEigen chi)))
        (recHR (dictRate n chi) (dictEigen chi) (greenSS n chi a b) (srcTT (dictRate n chi) (dictEigen chi)) (srcTR (dictRate n chi) (dictEigen chi)) (srcRR (dictRate n chi) (dictEigen chi)) (srcT (dictRate n chi) (dictEigen chi)) (srcR (dictRate n chi) (dictEigen chi)) (srcTF (dictRate n chi) (dictEigen chi)) (srcL (dictRate n chi) (dictEigen chi))) Y) p.val) (-3) i j +
      harmonicSourceTensor (dictEigen chi) (envelope (2 * dictRate n chi) amp p.val) (p.val 3)
        (srcTT (dictRate n chi) (dictEigen chi) (p.val 1)) (srcTR (dictRate n chi) (dictEigen chi) (p.val 1))
        (srcRR (dictRate n chi) (dictEigen chi) (p.val 1)) (srcT (dictRate n chi) (dictEigen chi) (p.val 1))
        (srcR (dictRate n chi) (dictEigen chi) (p.val 1)) (srcTF (dictRate n chi) (dictEigen chi) (p.val 1))
        (srcL (dictRate n chi) (dictEigen chi) (p.val 1))
        (Y (angularPoint p.val)) (coordDeriv 0 Y (angularPoint p.val)) (coordDeriv 1 Y (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 0 Y) (angularPoint p.val)) (coordDeriv 0 (coordDeriv 1 Y) (angularPoint p.val))
        (coordDeriv 1 (coordDeriv 1 Y) (angularPoint p.val)) i j = 0 :=
  harmonicMetricField_einstein _ _ amp hs hμ
    (ssSourcedMasterData _ _ hs hμ _ (greenSS_contDiffOn n chi hchi ha hb) (greenSS_masterEquation n chi hchi ha hb hs hμ))
    (greenSS_contDiffOn n chi hchi ha hb) (srcTT_contDiffOn _ _) (srcTR_contDiffOn _ _) (srcRR_contDiffOn _ _)
    (srcT_contDiffOn _ _) (srcR_contDiffOn _ _) (srcTF_contDiffOn _ _) (srcL_contDiffOn _ _) Y hY hYeig p i j

end
end RHTower.D4BMScalarStream
