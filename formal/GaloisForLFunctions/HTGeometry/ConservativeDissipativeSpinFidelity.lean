import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinorLift
import GaloisForLFunctions.HTGeometry.ResolutionQuotientReplicaFrameCapacityLaw

/-!
# Spin evolution, chordal geometry, and quantum replica fidelity

Schaffer–Exl's spin mechanism (arXiv:2609.04530) acts on the corpus's normalized
Higgs spinor chart. Its pure-state fidelity is complementary Böttcher chordal
separation; projector distances and all replica fidelities inherit exact
formulas. The actual damped evolution has an explicit pair-fidelity law and
a closed family of initially nonorthogonal states that become orthogonal at
a constructed positive finite time.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate RealInnerProductSpace
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Exact complex overlap of the canonically normalized spinor chart. -/
theorem finiteComplexInner_spinChartSpinor (z w : ℂ) :
    finiteComplexInner (spinChartSpinor z) (spinChartSpinor w) =
      (spinChartScale z : ℂ) * (spinChartScale w : ℂ) * (1 + conj z * w) := by
  simp [finiteComplexInner, spinChartSpinor, Fin.sum_univ_two]
  ring

/-- The normalized spinor chart discharges the corpus's complex unit-state premise. -/
theorem finiteComplexInner_spinChartSpinor_self (z : ℂ) :
    finiteComplexInner (spinChartSpinor z) (spinChartSpinor z) = 1 := by
  have h := spinChartSpinor_normSq z
  unfold abelianHiggsSpinorNormSq at h
  unfold finiteComplexInner
  simp only [Fin.sum_univ_two, ← Complex.normSq_eq_conj_mul_self]
  exact_mod_cast h

/-- The chart states satisfy the existing pure-state normalization predicate unconditionally. -/
theorem spinChartSpinor_normalized (z : ℂ) : FinitePureStateNormalized (spinChartSpinor z) := by
  unfold FinitePureStateNormalized finitePureStateFidelity
  rw [finiteComplexInner_spinChartSpinor_self]
  simp

/-- Complex overlap plus chart separation has its exact two-coordinate Gram identity. -/
theorem spinChartOverlap_identity (z w : ℂ) :
    ‖1 + conj z * w‖ ^ 2 + ‖z - w‖ ^ 2 = (1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  ring

/-- Quantum pure-state fidelity is precisely complementary Böttcher chordal separation. -/
theorem spinChartSpinor_fidelity (z w : ℂ) :
    finitePureStateFidelity (spinChartSpinor z) (spinChartSpinor w) =
      1 - _root_.Bottcher.chordalDist z w ^ 2 := by
  have hz : 1 + ‖z‖ ^ 2 ≠ 0 := by positivity
  have hw : 1 + ‖w‖ ^ 2 ≠ 0 := by positivity
  rw [finitePureStateFidelity, finiteComplexInner_spinChartSpinor,
    norm_mul, norm_mul, mul_pow, mul_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, spinChartScale_sq]
  rw [_root_.Bottcher.chordalDist_sq]
  have h := spinChartOverlap_identity z w
  field_simp
  nlinarith

/-- Hilbert–Schmidt distance of the actual pure projectors is twice squared chordal distance. -/
theorem spinChartSpinor_projector_distance (z w : ℂ) :
    ‖finitePureProjectorEuclidean (spinChartSpinor z) -
      finitePureProjectorEuclidean (spinChartSpinor w)‖ ^ 2 =
        2 * _root_.Bottcher.chordalDist z w ^ 2 := by
  rw [norm_finitePureProjectorEuclidean_sub_sq (spinChartSpinor_normalized z)
    (spinChartSpinor_normalized w), spinChartSpinor_fidelity]
  ring

/-- Every replica order has its exact inherited chordal fidelity, including zero copies. -/
theorem spinChartSpinor_replica_fidelity (r : ℕ) (z w : ℂ) :
    finitePureStateFidelity (finitePureTensorPower r (spinChartSpinor z))
      (finitePureTensorPower r (spinChartSpinor w)) =
        (1 - _root_.Bottcher.chordalDist z w ^ 2) ^ r := by
  rw [finitePureStateFidelity_tensorPower, spinChartSpinor_fidelity]

/-- All replica chart states retain exact pure-state normalization. -/
theorem spinChartSpinor_replica_normalized (r : ℕ) (z : ℂ) :
    FinitePureStateNormalized (finitePureTensorPower r (spinChartSpinor z)) := by
  unfold FinitePureStateNormalized
  rw [finitePureStateFidelity_tensorPower]
  have h := spinChartSpinor_normalized z
  change finitePureStateFidelity (spinChartSpinor z) (spinChartSpinor z) = 1 at h
  rw [h, one_pow]

/-- Replica-projector distance has an exact formula in the original stereographic metric. -/
theorem spinChartSpinor_replica_projector_distance (r : ℕ) (z w : ℂ) :
    ‖finitePureProjectorEuclidean (finitePureTensorPower r (spinChartSpinor z)) -
      finitePureProjectorEuclidean (finitePureTensorPower r (spinChartSpinor w))‖ ^ 2 =
        2 - 2 * (1 - _root_.Bottcher.chordalDist z w ^ 2) ^ r := by
  rw [norm_finitePureProjectorEuclidean_sub_sq (spinChartSpinor_replica_normalized r z)
    (spinChartSpinor_replica_normalized r w), spinChartSpinor_replica_fidelity]

/-- Pairwise fidelity along the actual damped spin evolution, with both initial coordinates free. -/
theorem spinSpinorFlow_fidelity (a : ℝ) (z w : ℂ) (t : ℝ) :
    finitePureStateFidelity (spinSpinorFlow a z t) (spinSpinorFlow a w t) =
      1 - Real.exp (-2 * a ^ 2 * t) * ‖z - w‖ ^ 2 /
        ((1 + Real.exp (-2 * a ^ 2 * t) * ‖z‖ ^ 2) *
          (1 + Real.exp (-2 * a ^ 2 * t) * ‖w‖ ^ 2)) := by
  have hd : spinPlaneFlow a z t - spinPlaneFlow a w t = spinPlaneFlow a (z - w) t := by
    simp [spinPlaneFlow, mul_sub]
  rw [spinSpinorFlow, spinSpinorFlow, spinChartSpinor_fidelity, _root_.Bottcher.chordalDist_sq,
    hd, spinPlaneFlow_norm_sq, spinPlaneFlow_norm_sq, spinPlaneFlow_norm_sq]

/-- Opposite chart coordinates have a simple latitude-square fidelity. -/
theorem spinChartSpinor_opposite_fidelity (z : ℂ) :
    finitePureStateFidelity (spinChartSpinor z) (spinChartSpinor (-z)) =
      ((‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2)) ^ 2 := by
  rw [spinChartSpinor_fidelity, _root_.Bottcher.chordalDist_sq, norm_neg]
  have hd : 1 + ‖z‖ ^ 2 ≠ 0 := by positivity
  have hn : ‖z - -z‖ ^ 2 = 4 * ‖z‖ ^ 2 := by
    rw [sub_neg_eq_add, ← two_mul, norm_mul, mul_pow, show ‖(2 : ℂ)‖ = (2 : ℝ) by simp]
    ring
  rw [hn]
  field_simp
  ring

/-- A nonorthogonal opposite pair above the equator, built without any positivity premise. -/
def spinSeparationSeed (x : ℝ) : ℂ := (Real.exp (Real.exp x) : ℂ)

/-- Positive finite time at which this pair reaches the equator. -/
def spinSeparationTime (s x : ℝ) : ℝ := Real.exp x / (Real.exp s) ^ 2

theorem spinSeparationTime_pos (s x : ℝ) : 0 < spinSeparationTime s x := by
  unfold spinSeparationTime
  positivity

/-- The constructed separation time places the evolving chart coordinate exactly on the unit circle. -/
theorem spinSeparation_norm (s x : ℝ) :
    ‖spinPlaneFlow (Real.exp s) (spinSeparationSeed x) (spinSeparationTime s x)‖ = 1 := by
  rw [spinPlaneFlow_norm, spinSeparationSeed, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  have he : -(Real.exp s) ^ 2 * spinSeparationTime s x + Real.exp (x) = 0 := by
    unfold spinSeparationTime
    field_simp
    ring
  rw [he, Real.exp_zero]

/-- The initial pair has strictly positive fidelity. -/
theorem spinSeparation_initial_fidelity_pos (x : ℝ) :
    0 < finitePureStateFidelity (spinChartSpinor (spinSeparationSeed x))
      (spinChartSpinor (-spinSeparationSeed x)) := by
  rw [spinChartSpinor_opposite_fidelity]
  have hn : ‖spinSeparationSeed x‖ = Real.exp (Real.exp x) := by
    rw [spinSeparationSeed, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [hn]
  have h := Real.one_lt_exp_iff.mpr (Real.exp_pos x)
  have hp : 0 < Real.exp (Real.exp x) ^ 2 - 1 := by nlinarith
  positivity

/-- Two initially nonorthogonal states become exactly orthogonal at a positive finite time. -/
theorem spinSeparation_final_fidelity_zero (s x : ℝ) :
    finitePureStateFidelity
      (spinSpinorFlow (Real.exp s) (spinSeparationSeed x) (spinSeparationTime s x))
      (spinSpinorFlow (Real.exp s) (-spinSeparationSeed x) (spinSeparationTime s x)) = 0 := by
  have hn : spinPlaneFlow (Real.exp s) (-spinSeparationSeed x) (spinSeparationTime s x) =
      -spinPlaneFlow (Real.exp s) (spinSeparationSeed x) (spinSeparationTime s x) := by
    simp [spinPlaneFlow]
  rw [spinSpinorFlow, spinSpinorFlow, hn, spinChartSpinor_opposite_fidelity, spinSeparation_norm]
  simp

end
end GaloisForLFunctions.HTGeometry.SchafferExl
