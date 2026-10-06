import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicFourierLattice

/-!
# Normal differential operator for the complete physical cubic

The exact Fourier symbol is 2*pi*i times the full signed defect
xi_2+xi_0*xi_1, at every iteration. The original reciprocal oscillation
satisfies the corresponding differential equation, and its factorization
retains every literal physical weight. Moving derivative bounds and
source aggregation are separate obligations; no exterior cancellation is
inferred from these identities alone.
-/

noncomputable section
open MeasureTheory
open GaloisForLFunctions.RHTower
open scoped FourierTransform LineDeriv
namespace RHTower.BAGTrace

private def axis (i : Fin 3) : BAGPhysicalSpace := EuclideanSpace.single i 1

/-- Constant differential operator with the complete global cone as symbol. -/
def bagCubicNormalOperator (f : SchwartzMap BAGPhysicalSpace ℂ) :
    SchwartzMap BAGPhysicalSpace ℂ :=
  ∂_{axis 2} f - (Complex.I / (2 * Real.pi : ℂ)) • ∂_{axis 0} (∂_{axis 1} f)

private theorem fourier_axis (i : Fin 3) (f : SchwartzMap BAGPhysicalSpace ℂ)
    (x : BAGPhysicalSpace) :
    (𝓕 (∂_{axis i} f)) x = (2 * Real.pi * Complex.I : ℂ) * (x i : ℂ) * (𝓕 f) x := by
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  have ht : (inner ℝ · (axis i)).HasTemperateGrowth := ((innerSL ℝ).flip (axis i)).hasTemperateGrowth
  change (2 * Real.pi * Complex.I : ℂ) •
    ((SchwartzMap.smulLeftCLM ℂ (fun v : BAGPhysicalSpace => inner ℝ v (axis i)) (𝓕 f)) x) = _
  rw [SchwartzMap.smulLeftCLM_apply_apply ht]
  simp only [axis, EuclideanSpace.inner_single_right, conj_trivial, one_mul,
    Complex.real_smul, smul_eq_mul]
  ring

theorem bagCubicNormalOperator_fourier (f : SchwartzMap BAGPhysicalSpace ℂ)
    (x : BAGPhysicalSpace) :
    (𝓕 (bagCubicNormalOperator f)) x =
      (2 * Real.pi * Complex.I : ℂ) * ((x 2 + x 0 * x 1 : ℝ) : ℂ) * (𝓕 f) x := by
  have he : 𝓕 (bagCubicNormalOperator f) =
      𝓕 (∂_{axis 2} f) - (Complex.I / (2 * Real.pi : ℂ)) • 𝓕 (∂_{axis 0} (∂_{axis 1} f)) := by
    change (SchwartzMap.fourierTransformCLM ℂ) _ = _
    rw [bagCubicNormalOperator, map_sub, map_smul]
    rfl
  rw [he]
  change (𝓕 (∂_{axis 2} f)) x - (Complex.I / (2 * Real.pi : ℂ)) *
    (𝓕 (∂_{axis 0} (∂_{axis 1} f))) x = _
  rw [fourier_axis, fourier_axis, fourier_axis]
  push_cast only [Complex.ofReal_add, Complex.ofReal_mul]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  simp only [Complex.I_sq]
  ring

/-- Every iteration retains the exact signed global defect, with no
rational separation or restriction to one cone sheet. -/
theorem bagCubicNormalOperator_iterate_fourier (k : ℕ)
    (f : SchwartzMap BAGPhysicalSpace ℂ) (x : BAGPhysicalSpace) :
    (𝓕 (bagCubicNormalOperator^[k] f)) x =
      (2 * Real.pi * Complex.I : ℂ)^k * ((x 2 + x 0 * x 1 : ℝ) : ℂ)^k * (𝓕 f) x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', bagCubicNormalOperator_fourier, ih, pow_succ, pow_succ]
    ring

/-- The reciprocal oscillatory factor of the literal physical amplitude. -/
def bagCubicReciprocalPhase (p q r : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (p : ℂ) * (q : ℂ) / (r : ℂ)) / (r : ℂ)

private theorem kernel_deriv_left (p q r : ℝ) :
    HasDerivAt (fun x : ℝ => bagCubicReciprocalPhase x q r)
      ((2 * Real.pi * Complex.I : ℂ) * (q : ℂ) / (r : ℂ) *
        bagCubicReciprocalPhase p q r) p := by
  have h := (((((Complex.hasDerivAt_ofReal p).const_mul
    (2 * Real.pi * Complex.I : ℂ)).mul_const (q : ℂ)).div_const (r : ℂ)).cexp).div_const (r : ℂ)
  apply h.congr_deriv
  dsimp only [bagCubicReciprocalPhase]
  ring

private theorem kernel_deriv_right (p q r : ℝ) :
    HasDerivAt (fun x : ℝ => bagCubicReciprocalPhase p x r)
      ((2 * Real.pi * Complex.I : ℂ) * (p : ℂ) / (r : ℂ) *
        bagCubicReciprocalPhase p q r) q := by
  have h := ((((Complex.hasDerivAt_ofReal q).const_mul
    ((2 * Real.pi * Complex.I : ℂ) * (p : ℂ))).div_const (r : ℂ)).cexp).div_const (r : ℂ)
  apply h.congr_deriv
  dsimp only [bagCubicReciprocalPhase]
  ring

private theorem kernel_deriv_height (p q : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (bagCubicReciprocalPhase p q)
      ((-1 / (r : ℂ) - (2 * Real.pi * Complex.I : ℂ) * (p : ℂ) * (q : ℂ) / (r : ℂ)^2) *
        bagCubicReciprocalPhase p q r) r := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have h := ((hasDerivAt_const r ((2 * Real.pi * Complex.I : ℂ) * (p : ℂ) * (q : ℂ))).div
    (Complex.hasDerivAt_ofReal r) hrC).cexp.div (Complex.hasDerivAt_ofReal r) hrC
  apply h.congr_deriv
  simp only [bagCubicReciprocalPhase, Pi.div_apply]
  field_simp
  ring

private theorem kernel_deriv_mixed (p q r : ℝ) :
    deriv (fun x : ℝ => deriv (fun y : ℝ => bagCubicReciprocalPhase x y r) q) p =
      ((2 * Real.pi * Complex.I : ℂ) / (r : ℂ) +
        (2 * Real.pi * Complex.I : ℂ)^2 * (p : ℂ) * (q : ℂ) / (r : ℂ)^2) *
          bagCubicReciprocalPhase p q r := by
  simp_rw [(kernel_deriv_right _ q r).deriv]
  have h := (((Complex.hasDerivAt_ofReal p).const_mul
    (2 * Real.pi * Complex.I : ℂ)).div_const (r : ℂ)).mul (kernel_deriv_left p q r)
  exact h.deriv.trans (by ring)

/-- Exact cancellation of the principal reciprocal oscillation in the normal
operator. The denominator is structural; no arithmetic or analytic estimate
is assumed. -/
theorem bagCubicReciprocalPhase_normal_eq_zero (p q : ℝ) (r : {r : ℝ // r ≠ 0}) :
    deriv (bagCubicReciprocalPhase p q) r.1 -
      (Complex.I / (2 * Real.pi : ℂ)) *
        deriv (fun x : ℝ => deriv (fun y : ℝ => bagCubicReciprocalPhase x y r.1) q) p = 0 := by
  rw [(kernel_deriv_height p q r.2).deriv, kernel_deriv_mixed]
  have hrC : (r.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr r.2
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hi3 : Complex.I^3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  field_simp
  ring_nf
  simp only [Complex.I_sq, hi3]
  ring

/-- All literal physical factors remaining after the reciprocal oscillation
has been removed; no Gaussian, logarithm or height window is discarded. -/
def bagCubicPhysicalWeight (N : ℝ) (η : ℝ → ℝ) (v : BAGPhysicalSpace) : ℂ :=
  (2 * Real.pi : ℂ) * bagCubicMellinSliceValue N η 0 (v 0) *
    bagCubicMellinSliceValue N η 0 (v 1) *
    (starRingEnd ℂ) (bagCubicMellinSliceValue N η 0 (v 2)) *
    (bagPhysicalHeightWindow (v 0 * v 1 / (v 2 * N)) : ℂ)

/-- Exact attachment of the annihilated kernel to the ENTIRE original
physical cubic amplitude, including its totalized zero-denominator value. -/
theorem bagCubicPhysicalAmplitude_weight_phase (N : ℝ) (η : ℝ → ℝ)
    (v : BAGPhysicalSpace) :
    bagCubicPhysicalAmplitude N η v =
      bagCubicPhysicalWeight N η v * bagCubicReciprocalPhase (v 0) (v 1) (v 2) := by
  have he : bourgainOscillation (2 * Real.pi * (v 0 * v 1 / v 2)) =
      Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (v 0 : ℂ) * (v 1 : ℂ) / (v 2 : ℂ)) := by
    unfold bourgainOscillation
    congr 1
    push_cast
    ring
  simp only [bagCubicPhysicalAmplitude, bagCubicPhysicalWeight, bagCubicReciprocalPhase, he]
  ring

end RHTower.BAGTrace
