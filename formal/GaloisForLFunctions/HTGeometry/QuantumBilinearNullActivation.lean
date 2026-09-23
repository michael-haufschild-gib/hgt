import GaloisForLFunctions.HTGeometry.PureStateProjectorTangentInertia

/-!
# A normalized quantum state with a moving invisible direction

For the nonlinear two-parameter ansatz `psi(x,y) = (cos(xy), sin(xy))`,
the actual Hilbert-space derivative in direction `(dx,dy)` has projective
energy `(y dx + x dy)²`. Along `(x,y) = (1,t)`, the direction `(1,-s)` is
invisible at `t=s` and has energy `(t-s)²` later. This is a closed analytic
model of the null-space activation mechanism of arXiv:2609.07645, §V.3.
It does not assert that this path solves a TDVP or Ising evolution.
-/

open scoped InnerProductSpace
noncomputable section
namespace HTGeometry

/-- A normalized real-amplitude state in the complex two-level Hilbert space. -/
def qgtQubitState (theta : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(Real.cos theta : ℂ), (Real.sin theta : ℂ)]

/-- Horizontal tangent at angular speed `v`. -/
def qgtQubitTangent (theta v : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![((-v * Real.sin theta : ℝ) : ℂ), ((v * Real.cos theta : ℝ) : ℂ)]

private theorem real_pair_inner (a b c d : ℝ) :
    inner ℂ (WithLp.toLp 2 ![(a : ℂ), (b : ℂ)] : EuclideanSpace ℂ (Fin 2))
      (WithLp.toLp 2 ![(c : ℂ), (d : ℂ)]) = ((a * c + b * d : ℝ) : ℂ) := by
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, RCLike.inner_apply, Complex.conj_ofReal]
  push_cast
  ring

theorem qgtQubitState_norm_sq (theta : ℝ) : ‖qgtQubitState theta‖ ^ (2 : ℕ) = 1 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  unfold qgtQubitState
  rw [real_pair_inner, RCLike.re_to_complex, Complex.ofReal_re]
  nlinarith [Real.cos_sq_add_sin_sq theta]

/-- The tangent is exactly horizontal: no normalization or phase direction remains. -/
theorem qgtQubitState_inner_tangent (theta v : ℝ) :
    inner ℂ (qgtQubitState theta) (qgtQubitTangent theta v) = 0 := by
  unfold qgtQubitState qgtQubitTangent
  rw [real_pair_inner]
  have h : Real.cos theta * (-v * Real.sin theta) +
      Real.sin theta * (v * Real.cos theta) = 0 := by ring
  rw [h, Complex.ofReal_zero]

theorem qgtQubitTangent_norm_sq (theta v : ℝ) : ‖qgtQubitTangent theta v‖ ^ (2 : ℕ) = v ^ (2 : ℕ) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  unfold qgtQubitTangent
  rw [real_pair_inner, RCLike.re_to_complex, Complex.ofReal_re]
  nlinarith [congrArg (fun z : ℝ => v ^ (2 : ℕ) * z) (Real.sin_sq_add_cos_sq theta)]

/-- A genuine derivative of the bilinear ansatz along every affine parameter perturbation. -/
theorem hasDerivAt_qgt_bilinear_state (x y dx dy : ℝ) :
    HasDerivAt (fun e : ℝ => qgtQubitState ((x + e * dx) * (y + e * dy)))
      (qgtQubitTangent (x * y) (y * dx + x * dy)) 0 := by
  have hp : HasDerivAt (fun e : ℝ => (x + e * dx) * (y + e * dy))
      (y * dx + x * dy) 0 := by
    have h := ((hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id 0).mul_const dx)).mul
      ((hasDerivAt_const 0 y).add ((hasDerivAt_id 0).mul_const dy))
    exact h.congr_deriv (by dsimp; ring)
  have hc := hp.cos.ofReal_comp
  have hs := hp.sin.ofReal_comp
  have hv : HasDerivAt
      (fun e : ℝ => ![(Real.cos ((x + e * dx) * (y + e * dy)) : ℂ),
        (Real.sin ((x + e * dx) * (y + e * dy)) : ℂ)])
      ![((-(y * dx + x * dy) * Real.sin (x * y) : ℝ) : ℂ),
        (((y * dx + x * dy) * Real.cos (x * y) : ℝ) : ℂ)] 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · apply hc.congr_deriv
      simp only [zero_mul, add_zero]
      congr 1
      ring
    · apply hs.congr_deriv
      simp only [zero_mul, add_zero]
      congr 1
      ring
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℂ)).symm.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0 hv

/-- The corpus's intrinsic projective Gram energy is exactly squared angular speed. -/
theorem qgtQubit_projective_energy (theta v : ℝ) :
    projectiveGramTangentEnergy (𝕜 := ℂ) (qgtQubitState theta) (qgtQubitTangent theta v) = v ^ (2 : ℕ) := by
  simp [projectiveGramTangentEnergy, qgtQubitState_norm_sq,
    qgtQubitTangent_norm_sq, qgtQubitState_inner_tangent]

/-- The pure-state quantum Fisher normalization gives four times squared angular speed. -/
theorem qgtQubit_fisher (theta v : ℝ) :
    pureStateQuantumFisherValue (‖qgtQubitState theta‖ ^ (2 : ℕ))
      ‖inner ℂ (qgtQubitState theta) (qgtQubitTangent theta v)‖
      (‖qgtQubitTangent theta v‖ ^ (2 : ℕ)) = 4 * v ^ (2 : ℕ) := by
  simp [pureStateQuantumFisherValue, projectiveQuantumTangentValue,
    qgtQubitState_norm_sq, qgtQubitTangent_norm_sq, qgtQubitState_inner_tangent]

/-- Exact finite-time activation of the old null direction. -/
theorem qgt_bilinear_null_activation (s t : ℝ) :
    projectiveGramTangentEnergy (𝕜 := ℂ) (qgtQubitState t)
      (qgtQubitTangent t (t * 1 + 1 * (-s))) = (t - s) ^ (2 : ℕ) := by
  rw [qgtQubit_projective_energy]
  ring

/-- A nonzero parameter direction is initially invisible and later carries unit energy. -/
theorem qgt_bilinear_null_then_visible (s : ℝ) :
    projectiveGramTangentEnergy (𝕜 := ℂ) (qgtQubitState s)
      (qgtQubitTangent s (s * 1 + 1 * (-s))) = 0 ∧
    projectiveGramTangentEnergy (𝕜 := ℂ) (qgtQubitState (s + 1))
      (qgtQubitTangent (s + 1) ((s + 1) * 1 + 1 * (-s))) = 1 := by
  rw [qgt_bilinear_null_activation, qgt_bilinear_null_activation]
  simp

/-- The same activation reaches the corpus's pure-state projector-tangent determinant. -/
theorem qgt_bilinear_projector_determinant (s t : ℝ) :
    (pureStateProjectorTangentCompression (qgtQubitState t)
      (qgtQubitTangent t (t * 1 + 1 * (-s)))).det = -((t - s : ℝ) : ℂ) ^ (4 : ℕ) := by
  rw [det_pureStateProjectorTangentCompression_eq_neg_projectiveEnergy_sq,
    qgt_bilinear_null_activation]
  push_cast
  ring

/-- Real-amplitude states have no Berry curvature despite nonzero projective sensitivity. -/
theorem qgtQubit_berry_zero (theta v : ℝ) :
    berryCurvatureValue (qgtQubitState theta) (qgtQubitTangent theta v) = 0 := by
  simp [berryCurvatureValue, qgtQubitState_inner_tangent]

/-- The metric area records the sensitivity missed by the Berry value. -/
theorem qgtQubit_metric_area (theta v : ℝ) :
    quantumMetricAreaValue (qgtQubitState theta) (qgtQubitTangent theta v) = v ^ (2 : ℕ) := by
  rw [quantumMetricAreaValue_eq_projectiveGram_add_berry,
    qgtQubit_projective_energy, qgtQubit_berry_zero]
  ring

end HTGeometry
