import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixCurvedSuspensionHodgeTrace
import GaloisForLFunctions.RHTower.HedenmalmThetaRouteRPositiveUnitCurrentBridge

/-!
# Relative reflection framing of the source-horizontal Gamma-six suspension

The curved two-orientation suspension is not an isolated differential.  It is the difference
between the bare reflection and its horizontal half-density transport.  Both reflections are
involutions, and their positive idempotents are conjugate rank-one carriers with identical trace
and determinant.  Nevertheless the determinant of their *framed difference* is exactly one
quarter of the positive Gamma-six curvature.

This gives a single exact explanation for the trace, index, stabilization, transported-metric,
and polar-normalization no-go results: all unframed invariants identify the two carriers at every
horizontal grade.  The surviving producer must compare them in the fixed source framing.
-/

open Complex Matrix

namespace RHTower

noncomputable section

/-- Coefficient-free exchange of the forward and reflected source orientations. -/
def sourceHorizontalGammaSixBareReflection : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- Exchange after transporting the two orientations by reciprocal horizontal characters. -/
def sourceHorizontalGammaSixTransportedReflection (a : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, (Real.exp a : ℂ); (Real.exp (-a) : ℂ), 0]

/-- Positive half-density gauge whose conjugation transports the bare reflection. -/
def sourceHorizontalGammaSixHalfDensityGauge (a : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.exp (a / 2) : ℂ), 0; 0, (Real.exp (-a / 2) : ℂ)]

/-- Explicit inverse of the positive half-density gauge. -/
def sourceHorizontalGammaSixHalfDensityGaugeInv (a : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.exp (-a / 2) : ℂ), 0; 0, (Real.exp (a / 2) : ℂ)]

/-- Positive magnitude in the polar factorization of the transported reflection. -/
def sourceHorizontalGammaSixReflectionPolarMagnitude (a : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.exp (-a) : ℂ), 0; 0, (Real.exp a : ℂ)]

/-- Bare positive reflection idempotent `(1+R)/2`, written coefficientwise. -/
def sourceHorizontalGammaSixBareReflectionIdempotent :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 / 2 : ℂ), (1 / 2 : ℂ); (1 / 2 : ℂ), (1 / 2 : ℂ)]

/-- Transported positive reflection idempotent `(1+T_a)/2`. -/
def sourceHorizontalGammaSixTransportedReflectionIdempotent (a : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 / 2 : ℂ), (Real.exp a : ℂ) / 2;
     (Real.exp (-a) : ℂ) / 2, (1 / 2 : ℂ)]

/-- Fixed diagonal source frame.  Unlike a transported frame, it does not depend on grade. -/
def sourceHorizontalGammaSixFixedDiagonalFrame : Fin 2 → ℂ :=
  ![1, 1]

private theorem sourceHorizontalGammaSix_cexp_mul_cexp_neg (z : ℂ) :
    Complex.exp z * Complex.exp (-z) = 1 := by
  rw [Complex.exp_neg]
  exact mul_inv_cancel₀ (Complex.exp_ne_zero z)

/-- Bare reflection is an involution. -/
theorem sourceHorizontalGammaSixBareReflection_sq :
    sourceHorizontalGammaSixBareReflection *
        sourceHorizontalGammaSixBareReflection = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceHorizontalGammaSixBareReflection, Matrix.mul_apply]

/-- Every transported reflection is still an involution. -/
theorem sourceHorizontalGammaSixTransportedReflection_sq (a : ℝ) :
    sourceHorizontalGammaSixTransportedReflection a *
        sourceHorizontalGammaSixTransportedReflection a = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceHorizontalGammaSixTransportedReflection, Matrix.mul_apply,
      ← Complex.exp_add]

/-- The two explicit half-density gauges are mutual inverses. -/
theorem sourceHorizontalGammaSixHalfDensityGauge_mul_inv (a : ℝ) :
    sourceHorizontalGammaSixHalfDensityGauge a *
        sourceHorizontalGammaSixHalfDensityGaugeInv a = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceHorizontalGammaSixHalfDensityGauge,
      sourceHorizontalGammaSixHalfDensityGaugeInv, Matrix.mul_apply,
      ← Complex.exp_add] <;> ring_nf <;> simp

theorem sourceHorizontalGammaSixHalfDensityGaugeInv_mul (a : ℝ) :
    sourceHorizontalGammaSixHalfDensityGaugeInv a *
        sourceHorizontalGammaSixHalfDensityGauge a = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceHorizontalGammaSixHalfDensityGauge,
      sourceHorizontalGammaSixHalfDensityGaugeInv, Matrix.mul_apply,
      ← Complex.exp_add] <;> ring_nf <;> simp

/-- Half-density conjugation is the exact horizontal transport of reflection. -/
theorem sourceHorizontalGammaSixTransportedReflection_eq_halfDensity_conj (a : ℝ) :
    sourceHorizontalGammaSixTransportedReflection a =
      sourceHorizontalGammaSixHalfDensityGauge a *
        sourceHorizontalGammaSixBareReflection *
          sourceHorizontalGammaSixHalfDensityGaugeInv a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceHorizontalGammaSixTransportedReflection,
      sourceHorizontalGammaSixHalfDensityGauge,
      sourceHorizontalGammaSixHalfDensityGaugeInv,
      sourceHorizontalGammaSixBareReflection, Matrix.mul_apply,
      ← Complex.exp_add]

/-- Polar factorization: the unitary/sign part is the same bare reflection at every grade. -/
theorem sourceHorizontalGammaSixTransportedReflection_eq_bare_mul_polarMagnitude (a : ℝ) :
    sourceHorizontalGammaSixTransportedReflection a =
      sourceHorizontalGammaSixBareReflection *
        sourceHorizontalGammaSixReflectionPolarMagnitude a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceHorizontalGammaSixTransportedReflection,
      sourceHorizontalGammaSixBareReflection,
      sourceHorizontalGammaSixReflectionPolarMagnitude, Matrix.mul_apply]

/-- The curved suspension is exactly transported reflection minus bare reflection. -/
theorem sourceHorizontalGammaSixCurvedSuspension_eq_reflection_difference (a : ℝ) :
    sourceHorizontalGammaSixCurvedSuspension a =
      sourceHorizontalGammaSixTransportedReflection a -
        sourceHorizontalGammaSixBareReflection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceHorizontalGammaSixCurvedSuspension,
      sourceHorizontalGammaSixForwardSuspensionLeg,
      sourceHorizontalGammaSixReflectedSuspensionLeg,
      sourceHorizontalGammaSixTransportedReflection,
      sourceHorizontalGammaSixBareReflection,
      sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq,
      sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq]

/-- Fixed-framing equality of the two involutions occurs exactly at neutral grade. -/
theorem sourceHorizontalGammaSixTransportedReflection_eq_bare_iff (a : ℝ) :
    sourceHorizontalGammaSixTransportedReflection a =
        sourceHorizontalGammaSixBareReflection ↔ a = 0 := by
  constructor
  · intro h
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    have h01' : Complex.exp (a : ℂ) = 1 := by
      simpa [sourceHorizontalGammaSixTransportedReflection,
        sourceHorizontalGammaSixBareReflection] using h01
    have hre := congrArg Complex.re h01'
    have hexp : Real.exp a = 1 := by
      calc
        Real.exp a = (Complex.exp (a : ℂ)).re :=
          (Complex.exp_ofReal_re a).symm
        _ = 1 := hre
    exact (Real.exp_eq_one_iff a).1 hexp
  · rintro rfl
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sourceHorizontalGammaSixTransportedReflection,
        sourceHorizontalGammaSixBareReflection]

/-- The fixed diagonal source frame is preserved exactly at neutral horizontal grade. -/
theorem sourceHorizontalGammaSixTransportedReflection_fixedFrame_iff (a : ℝ) :
    (sourceHorizontalGammaSixTransportedReflection a).mulVec
        sourceHorizontalGammaSixFixedDiagonalFrame =
      sourceHorizontalGammaSixFixedDiagonalFrame ↔ a = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun v : Fin 2 → ℂ => v 0) h
    have h0' : Complex.exp (a : ℂ) = 1 := by
      simpa [sourceHorizontalGammaSixTransportedReflection,
        sourceHorizontalGammaSixFixedDiagonalFrame, Matrix.mulVec,
        dotProduct] using h0
    have hre := congrArg Complex.re h0'
    have hexp : Real.exp a = 1 := by
      calc
        Real.exp a = (Complex.exp (a : ℂ)).re :=
          (Complex.exp_ofReal_re a).symm
        _ = 1 := hre
    exact (Real.exp_eq_one_iff a).1 hexp
  · rintro rfl
    ext i
    fin_cases i <;>
      simp [sourceHorizontalGammaSixTransportedReflection,
        sourceHorizontalGammaSixFixedDiagonalFrame, Matrix.mulVec, dotProduct]

/-- Both positive reflection carriers are idempotent. -/
theorem sourceHorizontalGammaSixBareReflectionIdempotent_sq :
    sourceHorizontalGammaSixBareReflectionIdempotent *
        sourceHorizontalGammaSixBareReflectionIdempotent =
      sourceHorizontalGammaSixBareReflectionIdempotent := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceHorizontalGammaSixBareReflectionIdempotent, Matrix.mul_apply]
  all_goals norm_num

theorem sourceHorizontalGammaSixTransportedReflectionIdempotent_sq (a : ℝ) :
    sourceHorizontalGammaSixTransportedReflectionIdempotent a *
        sourceHorizontalGammaSixTransportedReflectionIdempotent a =
      sourceHorizontalGammaSixTransportedReflectionIdempotent a := by
  have h := sourceHorizontalGammaSix_cexp_mul_cexp_neg (a : ℂ)
  ext i j
  fin_cases i <;> fin_cases j
  · simp [sourceHorizontalGammaSixTransportedReflectionIdempotent,
      Matrix.mul_apply]
    field_simp
    rw [h]
    norm_num
  · simp [sourceHorizontalGammaSixTransportedReflectionIdempotent,
      Matrix.mul_apply]
    ring
  · simp [sourceHorizontalGammaSixTransportedReflectionIdempotent,
      Matrix.mul_apply]
    ring
  · simp [sourceHorizontalGammaSixTransportedReflectionIdempotent,
      Matrix.mul_apply]
    field_simp
    rw [mul_comm (Complex.exp (-(a : ℂ))) (Complex.exp (a : ℂ)), h]
    norm_num

/-- The transported idempotent is conjugate to the bare one by the same positive gauge. -/
theorem sourceHorizontalGammaSixTransportedReflectionIdempotent_eq_halfDensity_conj (a : ℝ) :
    sourceHorizontalGammaSixTransportedReflectionIdempotent a =
      sourceHorizontalGammaSixHalfDensityGauge a *
        sourceHorizontalGammaSixBareReflectionIdempotent *
          sourceHorizontalGammaSixHalfDensityGaugeInv a := by
  have hdiag : Complex.exp ((a : ℂ) / 2) *
      Complex.exp (-(a : ℂ) / 2) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    all_goals ring
  have hdiag' : Complex.exp (-(a : ℂ) / 2) *
      Complex.exp ((a : ℂ) / 2) = 1 := by
    rw [mul_comm]
    exact hdiag
  have hsq : Complex.exp ((a : ℂ) / 2) *
      Complex.exp ((a : ℂ) / 2) = Complex.exp (a : ℂ) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hsq' : Complex.exp (-(a : ℂ) / 2) *
      Complex.exp (-(a : ℂ) / 2) = Complex.exp (-(a : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  ext i j
  fin_cases i <;> fin_cases j
  · simp [sourceHorizontalGammaSixTransportedReflectionIdempotent,
      sourceHorizontalGammaSixHalfDensityGauge,
      sourceHorizontalGammaSixHalfDensityGaugeInv,
      sourceHorizontalGammaSixBareReflectionIdempotent,
      Matrix.mul_apply]
    field_simp
    convert hdiag.symm using 1
    all_goals ring
  · simp [sourceHorizontalGammaSixTransportedReflectionIdempotent,
      sourceHorizontalGammaSixHalfDensityGauge,
      sourceHorizontalGammaSixHalfDensityGaugeInv,
      sourceHorizontalGammaSixBareReflectionIdempotent,
      Matrix.mul_apply]
    field_simp
    simpa [pow_two] using hsq.symm
  · simp [sourceHorizontalGammaSixTransportedReflectionIdempotent,
      sourceHorizontalGammaSixHalfDensityGauge,
      sourceHorizontalGammaSixHalfDensityGaugeInv,
      sourceHorizontalGammaSixBareReflectionIdempotent,
      Matrix.mul_apply]
    field_simp
    rw [pow_two]
    convert hsq'.symm using 1
    all_goals ring
  · simp [sourceHorizontalGammaSixTransportedReflectionIdempotent,
      sourceHorizontalGammaSixHalfDensityGauge,
      sourceHorizontalGammaSixHalfDensityGaugeInv,
      sourceHorizontalGammaSixBareReflectionIdempotent,
      Matrix.mul_apply]
    field_simp
    convert hdiag'.symm using 1
    all_goals ring

/-- The relative idempotent class is exactly one half of the curved suspension. -/
theorem sourceHorizontalGammaSixTransportedIdempotent_sub_bare (a : ℝ) :
    sourceHorizontalGammaSixTransportedReflectionIdempotent a -
        sourceHorizontalGammaSixBareReflectionIdempotent =
      (1 / 2 : ℂ) • sourceHorizontalGammaSixCurvedSuspension a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceHorizontalGammaSixTransportedReflectionIdempotent,
      sourceHorizontalGammaSixBareReflectionIdempotent,
      sourceHorizontalGammaSixCurvedSuspension,
      sourceHorizontalGammaSixForwardSuspensionLeg,
      sourceHorizontalGammaSixReflectedSuspensionLeg,
      sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq,
      sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq]
  all_goals ring

/-- Unframed polynomial invariants identify the two idempotents at every grade. -/
theorem trace_sourceHorizontalGammaSixTransportedReflectionIdempotent (a : ℝ) :
    Matrix.trace (sourceHorizontalGammaSixTransportedReflectionIdempotent a) = 1 := by
  norm_num [sourceHorizontalGammaSixTransportedReflectionIdempotent,
    Matrix.trace_fin_two]

theorem trace_sourceHorizontalGammaSixBareReflectionIdempotent :
    Matrix.trace sourceHorizontalGammaSixBareReflectionIdempotent = 1 := by
  norm_num [sourceHorizontalGammaSixBareReflectionIdempotent, Matrix.trace_fin_two]

theorem det_sourceHorizontalGammaSixTransportedReflectionIdempotent (a : ℝ) :
    Matrix.det (sourceHorizontalGammaSixTransportedReflectionIdempotent a) = 0 := by
  have h := sourceHorizontalGammaSix_cexp_mul_cexp_neg (a : ℂ)
  rw [Matrix.det_fin_two]
  simp [sourceHorizontalGammaSixTransportedReflectionIdempotent]
  field_simp
  rw [h]
  norm_num

theorem det_sourceHorizontalGammaSixBareReflectionIdempotent :
    Matrix.det sourceHorizontalGammaSixBareReflectionIdempotent = 0 := by
  rw [Matrix.det_fin_two]
  simp [sourceHorizontalGammaSixBareReflectionIdempotent]

/-- Framed relative determinant recovers exactly one quarter of positive Gamma-six curvature. -/
theorem det_sourceHorizontalGammaSixTransportedIdempotent_sub_bare (a : ℝ) :
    Matrix.det
        (sourceHorizontalGammaSixTransportedReflectionIdempotent a -
          sourceHorizontalGammaSixBareReflectionIdempotent) =
      (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a : ℂ) / 4 := by
  rw [sourceHorizontalGammaSixTransportedIdempotent_sub_bare,
    Matrix.det_smul, det_sourceHorizontalGammaSixCurvedSuspension]
  norm_num
  ring

/-- Normalized transpose-skew of the transported carrier in the fixed Euclidean source metric. -/
def sourceHorizontalGammaSixFixedMetricSkewRatio (a : ℝ) : ℝ :=
  ((sourceHorizontalGammaSixTransportedReflectionIdempotent a 0 1).re -
      (sourceHorizontalGammaSixTransportedReflectionIdempotent a 1 0).re) /
    ((sourceHorizontalGammaSixTransportedReflectionIdempotent a 0 1).re +
      (sourceHorizontalGammaSixTransportedReflectionIdempotent a 1 0).re)

/-- Fixed-metric non-self-adjointness is exactly hyperbolic rapidity in bounded Cayley
coordinates. -/
theorem sourceHorizontalGammaSixFixedMetricSkewRatio_eq_tanh (a : ℝ) :
    sourceHorizontalGammaSixFixedMetricSkewRatio a = Real.tanh a := by
  have hsum : Real.exp a + Real.exp (-a) ≠ 0 :=
    ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _))
  rw [sourceHorizontalGammaSixFixedMetricSkewRatio, Real.tanh_eq]
  simp [sourceHorizontalGammaSixTransportedReflectionIdempotent]
  have hnegRe : (Complex.exp (-(a : ℂ))).re = Real.exp (-a) := by
    convert Complex.exp_ofReal_re (-a) using 1
    all_goals norm_num
  rw [Complex.exp_ofReal_re a, hnegRe]
  field_simp [hsum]

/-- Route P's physical Julia/Cayley coordinate is literally the normalized fixed-metric skew of
the source-horizontal reflection idempotent. -/
theorem sourceHorizontalGammaSixFixedMetricSkewRatio_eq_cayleyDiscrepancy (a : ℝ) :
    sourceHorizontalGammaSixFixedMetricSkewRatio a =
      HedenmalmThetaSource.mobiusCriticalTwoSidedCayleyDiscrepancy
        (sourceHorizontalGammaSixRapidityAperture a) 0 := by
  rw [sourceHorizontalGammaSixFixedMetricSkewRatio_eq_tanh,
    mobiusCriticalTwoSidedCayleyDiscrepancy_gammaSixRapidityAperture]

/-- The transported carrier is an orthogonal projection in the fixed physical metric exactly at
neutral horizontal grade.  Idempotence alone holds at every grade; self-adjointness is the missing
positive-polar datum. -/
theorem sourceHorizontalGammaSixTransportedReflectionIdempotent_conjTranspose_eq_iff (a : ℝ) :
    (sourceHorizontalGammaSixTransportedReflectionIdempotent a).conjTranspose =
        sourceHorizontalGammaSixTransportedReflectionIdempotent a ↔ a = 0 := by
  constructor
  · intro h
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    have hre := congrArg Complex.re h01
    have hexp : Real.exp (-a) = Real.exp a := by
      have hre' : (Complex.exp (-(a : ℂ))).re =
          (Complex.exp (a : ℂ)).re := by
        simpa [Matrix.conjTranspose_apply,
          sourceHorizontalGammaSixTransportedReflectionIdempotent] using hre
      have hnegRe : (Complex.exp (-(a : ℂ))).re = Real.exp (-a) := by
        convert Complex.exp_ofReal_re (-a) using 1
        all_goals norm_num
      calc
        Real.exp (-a) = (Complex.exp (-(a : ℂ))).re :=
          hnegRe.symm
        _ = (Complex.exp (a : ℂ)).re := hre'
        _ = Real.exp a := Complex.exp_ofReal_re a
    have ha := Real.exp_injective hexp
    linarith
  · rintro rfl
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply,
        sourceHorizontalGammaSixTransportedReflectionIdempotent]

/-- Functional-equation reflection supplies cross-fibre adjointness unconditionally: adjoint sends
grade `a` to grade `-a`.  It does not identify the two fibres. -/
theorem sourceHorizontalGammaSixTransportedReflectionIdempotent_conjTranspose (a : ℝ) :
    (sourceHorizontalGammaSixTransportedReflectionIdempotent a).conjTranspose =
      sourceHorizontalGammaSixTransportedReflectionIdempotent (-a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply,
      sourceHorizontalGammaSixTransportedReflectionIdempotent,
      -Complex.ofReal_exp]

/-- Exact reflection no-go: cross-fibre adjointness holds at every grade, while failure of
same-fibre self-adjointness is equivalent to nonzero horizontal displacement. -/
theorem sourceHorizontalGammaSix_crossFibreAdjoint_but_not_selfAdjoint_iff (a : ℝ) :
    ((sourceHorizontalGammaSixTransportedReflectionIdempotent a).conjTranspose =
          sourceHorizontalGammaSixTransportedReflectionIdempotent (-a) ∧
      (sourceHorizontalGammaSixTransportedReflectionIdempotent a).conjTranspose ≠
          sourceHorizontalGammaSixTransportedReflectionIdempotent a) ↔
      a ≠ 0 := by
  constructor
  · intro h ha
    exact h.2
      ((sourceHorizontalGammaSixTransportedReflectionIdempotent_conjTranspose_eq_iff a).2 ha)
  · intro ha
    exact ⟨sourceHorizontalGammaSixTransportedReflectionIdempotent_conjTranspose a,
      fun hself => ha
        ((sourceHorizontalGammaSixTransportedReflectionIdempotent_conjTranspose_eq_iff a).1
          hself)⟩

/-- Positive-polar handoff and curved-complex flatness are literally the same local equation. -/
theorem sourceHorizontalGammaSix_idempotentSelfAdjoint_iff_curvedSuspensionFlat (a : ℝ) :
    ((sourceHorizontalGammaSixTransportedReflectionIdempotent a).conjTranspose =
        sourceHorizontalGammaSixTransportedReflectionIdempotent a) ↔
      sourceHorizontalGammaSixCurvedSuspension a *
        sourceHorizontalGammaSixCurvedSuspension a = 0 := by
  rw [sourceHorizontalGammaSixTransportedReflectionIdempotent_conjTranspose_eq_iff,
    sourceHorizontalGammaSixCurvedSuspension_sq_eq_zero_iff]

/-- On an actual multiplicity-labelled Xi divisor class, fixed-metric orthogonality of one
prime-clock reflection carrier is exactly critical-line placement. -/
theorem sourceHorizontalGammaSixPrimePhysicalReflectionIdempotentSelfAdjoint_iff
    (q : XiZeroCopy) (p : Nat.Primes) :
    (sourceHorizontalGammaSixTransportedReflectionIdempotent
        (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1)).conjTranspose =
      sourceHorizontalGammaSixTransportedReflectionIdempotent
        (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [sourceHorizontalGammaSixTransportedReflectionIdempotent_conjTranspose_eq_iff]
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  constructor
  · intro h
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1
      ((mul_eq_zero.mp h).resolve_left hlog)
  · intro hline
    rw [(primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hline, mul_zero]

/-- Fixed-prime external positive-polar handoff for every Xi divisor multiplicity copy. -/
def SourceHorizontalGammaSixPhysicalReflectionIdempotentsSelfAdjoint
    (p : Nat.Primes) : Prop :=
  ∀ q : XiZeroCopy,
    (sourceHorizontalGammaSixTransportedReflectionIdempotent
        (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1)).conjTranspose =
      sourceHorizontalGammaSixTransportedReflectionIdempotent
        (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1)

/-- Exact endpoint exposed by relative framing: proving fixed physical self-adjointness from source
arithmetic at any retained prime would prove RH, and RH supplies it. -/
theorem sourceHorizontalGammaSixPhysicalReflectionIdempotentsSelfAdjoint_iff_riemannHypothesis
    (p : Nat.Primes) :
    SourceHorizontalGammaSixPhysicalReflectionIdempotentsSelfAdjoint p ↔
      RiemannHypothesis := by
  constructor
  · intro hself
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hline :=
      (sourceHorizontalGammaSixPrimePhysicalReflectionIdempotentSelfAdjoint_iff q p).1
        (hself q)
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [xiSpectralPoint]
    · simp [xiSpectralPoint, hline]
  · intro hRH q
    apply (sourceHorizontalGammaSixPrimePhysicalReflectionIdempotentSelfAdjoint_iff q p).2
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

/-- Cayley saturation, fixed-metric self-adjointness, and fixed-frame equality are the same exact
condition on the relative carrier. -/
theorem sourceHorizontalGammaSix_cayleyZero_iff_idempotentSelfAdjoint_iff_framedEquality
    (a : ℝ) :
    (HedenmalmThetaSource.mobiusCriticalTwoSidedCayleyDiscrepancy
          (sourceHorizontalGammaSixRapidityAperture a) 0 = 0 ↔
      (sourceHorizontalGammaSixTransportedReflectionIdempotent a).conjTranspose =
        sourceHorizontalGammaSixTransportedReflectionIdempotent a) ∧
    ((sourceHorizontalGammaSixTransportedReflectionIdempotent a).conjTranspose =
          sourceHorizontalGammaSixTransportedReflectionIdempotent a ↔
      sourceHorizontalGammaSixTransportedReflection a =
        sourceHorizontalGammaSixBareReflection) := by
  rw [sourceHorizontalGammaSixTransportedReflectionIdempotent_conjTranspose_eq_iff,
    sourceHorizontalGammaSixTransportedReflection_eq_bare_iff,
    mobiusCriticalTwoSidedCayleyDiscrepancy_gammaSixRapidityAperture]
  constructor
  · constructor
    · intro h
      apply Real.tanh_injective
      simpa using h
    · rintro rfl
      simp
  · rfl

/-- Gauss-weighted determinant of the framed idempotent difference.  Factor four restores the
literal curved-suspension determinant. -/
def gaussGammaSixRelativeReflectionDeterminantEnergy
    (m : ℕ) (p : Nat.Primes) (t : ℝ) : ℝ :=
  4 * gaussReciprocalCharacterWeight m p *
    (Matrix.det
      (sourceHorizontalGammaSixTransportedReflectionIdempotent
          (Real.log (p : ℝ) * t) -
        sourceHorizontalGammaSixBareReflectionIdempotent)).re

theorem gaussGammaSixRelativeReflectionDeterminantEnergy_eq_suspensionTraceEnergy
    (m : ℕ) (p : Nat.Primes) (t : ℝ) :
    gaussGammaSixRelativeReflectionDeterminantEnergy m p t =
      gaussGammaSixSuspensionTraceEnergy m p t := by
  rw [gaussGammaSixRelativeReflectionDeterminantEnergy,
    det_sourceHorizontalGammaSixTransportedIdempotent_sub_bare,
    gaussGammaSixSuspensionTraceEnergy,
    sourceHorizontalGammaSixSuspensionTraceEnergy_eq_curvature]
  simp
  ring

/-- Frankenstein transgression: Gauss Hodge mass is the Euler derivative of the framed relative
idempotent determinant, not of either unframed idempotent invariant. -/
theorem gaussHodgeMassCurrent_eq_euler_relativeReflectionDeterminant
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    gaussHodgeMassCurrent m q p =
      primeDepthBVWoldXiCenteredRate q.1 *
        deriv (gaussGammaSixRelativeReflectionDeterminantEnergy m p)
          (primeDepthBVWoldXiCenteredRate q.1) := by
  have hfun : gaussGammaSixRelativeReflectionDeterminantEnergy m p =
      gaussGammaSixSuspensionTraceEnergy m p := by
    funext t
    exact gaussGammaSixRelativeReflectionDeterminantEnergy_eq_suspensionTraceEnergy m p t
  rw [hfun]
  exact gaussHodgeMassCurrent_eq_euler_gaussGammaSixSuspensionTraceEnergy m q p

/-- Actual theta-root-to-relative-framing comparison.  At every retained prime and every
multiplicity-labelled Xi divisor class, inverse Cayley transform of fixed-metric skew is exactly
the normalized signed rank-two boundary flux.  No root orientation or prime label is discarded. -/
theorem sourceHorizontalGammaSixPrimePhysical_artanh_fixedMetricSkewRatio_eq_thetaFlux
    (q : XiZeroCopy) (p : Nat.Primes) :
    Real.artanh
        (sourceHorizontalGammaSixFixedMetricSkewRatio
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1)) =
      -Real.log (p : ℝ) * thetaXiRankTwoBoundaryFlux q /
        (HedenmalmThetaSource.thetaSource.mass * thetaXiRootEnergy q) := by
  rw [sourceHorizontalGammaSixFixedMetricSkewRatio_eq_tanh, Real.artanh_tanh,
    HedenmalmThetaSource.primeDepthBVWoldXiCenteredRate_eq_neg_two_spectralIm,
    thetaXiRankTwoBoundaryFlux_eq]
  have hmass : HedenmalmThetaSource.thetaSource.mass ≠ 0 :=
    HedenmalmThetaSource.thetaSource.mass_ne_zero
  have henergy : thetaXiRootEnergy q ≠ 0 := (thetaXiRootEnergy_pos q).ne'
  field_simp [hmass, henergy]

/-- Same-fibre positive-polar handoff is exactly neutrality of the genuine compact theta root
boundary flux.  This closes the comparison, not the source annihilation theorem. -/
theorem sourceHorizontalGammaSixPrimePhysical_idempotentSelfAdjoint_iff_thetaFlux_zero
    (q : XiZeroCopy) (p : Nat.Primes) :
    ((sourceHorizontalGammaSixTransportedReflectionIdempotent
        (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1)).conjTranspose =
      sourceHorizontalGammaSixTransportedReflectionIdempotent
        (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1)) ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  rw [sourceHorizontalGammaSixTransportedReflectionIdempotent_conjTranspose_eq_iff,
    thetaXiRankTwoBoundaryFlux_eq_zero_iff_spectralIm_eq_zero,
    HedenmalmThetaSource.primeDepthBVWoldXiCenteredRate_eq_neg_two_spectralIm]
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  constructor
  · intro h
    have hrate : -2 * (xiSpectralPoint q).im = 0 :=
      (mul_eq_zero.mp h).resolve_left hlog
    linarith
  · intro him
    rw [him]
    ring

/-- Equality of the two fixed-frame idempotents is exactly neutrality. -/
theorem sourceHorizontalGammaSixTransportedReflectionIdempotent_eq_bare_iff (a : ℝ) :
    sourceHorizontalGammaSixTransportedReflectionIdempotent a =
        sourceHorizontalGammaSixBareReflectionIdempotent ↔ a = 0 := by
  constructor
  · intro h
    have hdet : Matrix.det
        (sourceHorizontalGammaSixTransportedReflectionIdempotent a -
          sourceHorizontalGammaSixBareReflectionIdempotent) = 0 := by
      rw [h]
      simp
    rw [det_sourceHorizontalGammaSixTransportedIdempotent_sub_bare] at hdet
    have hcurvC : (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a : ℂ) = 0 := by
      exact ((div_eq_zero_iff).1 hdet).resolve_right (by norm_num)
    have hcurv : sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a = 0 := by
      exact_mod_cast hcurvC
    exact (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff a).1 hcurv
  · rintro rfl
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sourceHorizontalGammaSixTransportedReflectionIdempotent,
        sourceHorizontalGammaSixBareReflectionIdempotent]

/-- Exact no-go/survivor package.  Trace and determinant agree unconditionally, while the framed
relative determinant is positive exactly off center.  Thus stable/unframed carrier data erase the
horizontal class; fixed-framing equality is the sharp surviving producer. -/
theorem sourceHorizontalGammaSix_unframedIdempotents_blind_but_relativeDet_pos_iff (a : ℝ) :
    (Matrix.trace (sourceHorizontalGammaSixTransportedReflectionIdempotent a) =
          Matrix.trace sourceHorizontalGammaSixBareReflectionIdempotent ∧
      Matrix.det (sourceHorizontalGammaSixTransportedReflectionIdempotent a) =
          Matrix.det sourceHorizontalGammaSixBareReflectionIdempotent ∧
      0 < (Matrix.det
        (sourceHorizontalGammaSixTransportedReflectionIdempotent a -
          sourceHorizontalGammaSixBareReflectionIdempotent)).re) ↔
      a ≠ 0 := by
  rw [trace_sourceHorizontalGammaSixTransportedReflectionIdempotent,
    trace_sourceHorizontalGammaSixBareReflectionIdempotent,
    det_sourceHorizontalGammaSixTransportedReflectionIdempotent,
    det_sourceHorizontalGammaSixBareReflectionIdempotent,
    det_sourceHorizontalGammaSixTransportedIdempotent_sub_bare]
  norm_num
  constructor
  · intro h
    exact (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_pos_iff a).1
      (by linarith)
  · intro ha
    have hpos :=
      (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_pos_iff a).2 ha
    linarith

end

end RHTower
