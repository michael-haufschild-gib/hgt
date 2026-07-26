import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Halving unitary reflection phases

A complex value satisfying `w² * conj z = z` is not intrinsically complex when `w` is unitary:
multiplication by `conj w` rotates it onto the real axis.  This module packages that exact
phase-halving law, its polar normal form, and its norm and zero interfaces.

The result is the multiplicative real-structure counterpart of additive reflection-cocycle
halving.  It applies uniformly to completed finite carriers and to the Riemann zeta value on the
critical line.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- A complex scalar is a unitary phase when its conjugate times itself is one. -/
def IsUnitaryPhase (w : ℂ) : Prop :=
  (starRingEnd ℂ) w * w = 1

/-- The value `z` obeys the real structure carried by the square of `w`. -/
def IsPhaseReflected (w z : ℂ) : Prop :=
  w * w * (starRingEnd ℂ) z = z

/-- The real amplitude obtained after removing a phase from a reflected value. -/
def phaseHalvedAmplitude (w z : ℂ) : ℝ :=
  ((starRingEnd ℂ) w * z).re

/-- Simultaneous conjugation of the phase and value leaves the real phase-halved amplitude
unchanged.  This is the general height-reflection law behind every even Hardy amplitude. -/
@[simp] theorem phaseHalvedAmplitude_conj (w z : ℂ) :
    phaseHalvedAmplitude ((starRingEnd ℂ) w) ((starRingEnd ℂ) z) =
      phaseHalvedAmplitude w z := by
  unfold phaseHalvedAmplitude
  rw [Complex.conj_conj]
  have hvalue : w * (starRingEnd ℂ) z =
      (starRingEnd ℂ) ((starRingEnd ℂ) w * z) := by
    rw [map_mul, Complex.conj_conj]
  rw [hvalue, Complex.conj_re]

/-- **First-jet phase-halving law.**  The derivative of a phase-halved amplitude is the real part
of the ordinary product rule after conjugating the phase jet.  This is the exact differential
interface behind every continuously oriented Hardy amplitude. -/
theorem hasDerivAt_phaseHalvedAmplitude {w z : ℝ → ℂ} {w' z' : ℂ} {x : ℝ}
    (hw : HasDerivAt w w' x) (hz : HasDerivAt z z' x) :
    HasDerivAt (fun y => phaseHalvedAmplitude (w y) (z y))
      (((starRingEnd ℂ) w' * z x + (starRingEnd ℂ) (w x) * z').re) x := by
  have hwc : HasDerivAt (fun y => (starRingEnd ℂ) (w y))
      ((starRingEnd ℂ) w') x := by
    simpa using Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x hw
  have hprod := hwc.mul hz
  unfold phaseHalvedAmplitude
  simpa only [Function.comp_apply, Pi.mul_apply] using
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hprod

theorem hasDerivAt_log_norm_complex {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (h0 : f x ≠ 0) :
    HasDerivAt (fun y => Real.log ‖f y‖) (f' / f x).re x := by
  have hre : HasDerivAt (fun y => (f y).re) f'.re x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf
  have him : HasDerivAt (fun y => (f y).im) f'.im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hf
  let B : ℝ := 2 * ((f x).re * f'.re + (f x).im * f'.im)
  have hnsq : HasDerivAt (fun y => Complex.normSq (f y)) B x := by
    have h := (hre.mul hre).add (him.mul him)
    have heq : (fun y => Complex.normSq (f y)) =
        fun y => (f y).re * (f y).re + (f y).im * (f y).im := by
      funext y
      rw [Complex.normSq_apply]
    rw [heq]
    convert h using 1
    dsimp [B]
    ring
  have hnsq0 : Complex.normSq (f x) ≠ 0 := fun h => h0 (Complex.normSq_eq_zero.mp h)
  have hlog := (Real.hasDerivAt_log hnsq0).comp x hnsq
  have hhalf := hlog.const_mul (1 / 2 : ℝ)
  simp only [Function.comp_apply] at hhalf
  have heq : (fun y => (1 / 2 : ℝ) * Real.log (Complex.normSq (f y))) =
      fun y => Real.log ‖f y‖ := by
    funext y
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]
    ring
  rw [heq] at hhalf
  convert hhalf using 1
  rw [Complex.div_re]
  dsimp [B]
  field_simp [Complex.normSq_apply]

private theorem hasDerivAt_norm_complex {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (h0 : f x ≠ 0) :
    HasDerivAt (fun y => ‖f y‖) (‖f x‖ * (f' / f x).re) x := by
  have hlog := hasDerivAt_log_norm_complex hf h0
  have hcomp := (Real.hasDerivAt_exp (Real.log ‖f x‖)).comp x hlog
  have hne : ∀ᶠ y in nhds x, f y ≠ 0 := hf.continuousAt.eventually_ne h0
  have heq : (fun y => Real.exp (Real.log ‖f y‖)) =ᶠ[nhds x]
      fun y => ‖f y‖ := by
    filter_upwards [hne] with y hy
    exact Real.exp_log (norm_pos_iff.mpr hy)
  have hresult := hcomp.congr_of_eventuallyEq heq.symm
  convert hresult using 1
  rw [Real.exp_log (norm_pos_iff.mpr h0)]

/-- **Normalized conjugate-phase velocity.**  For every nonvanishing differentiable complex
path, the derivative of `conj f / ‖f‖` is the phase itself times the purely imaginary logarithmic
velocity `-i Im(f'/f)`.  Thus normalization removes the radial derivative exactly. -/
theorem hasDerivAt_normalizedConjPhase {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (h0 : f x ≠ 0) :
    HasDerivAt (fun y => (starRingEnd ℂ) (f y) / ‖f y‖)
      ((-I * ((f' / f x).im : ℂ)) *
        ((starRingEnd ℂ) (f x) / ‖f x‖)) x := by
  have hc : HasDerivAt (fun y => (starRingEnd ℂ) (f y))
      ((starRingEnd ℂ) f') x := by
    simpa using Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x hf
  have hn := hasDerivAt_norm_complex hf h0
  have hnC : HasDerivAt (fun y => (‖f y‖ : ℂ))
      ((‖f x‖ * (f' / f x).re : ℝ) : ℂ) x := by
    simpa using Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hn
  have hn0 : (‖f x‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr h0)
  have hdiv := hc.div hnC hn0
  convert hdiv using 1
  let a : ℂ := f' / f x
  have hf' : f' = a * f x := by
    dsimp [a]
    field_simp
  have ha : (starRingEnd ℂ) a - (a.re : ℂ) = -I * (a.im : ℂ) := by
    apply Complex.ext <;> simp
  rw [hf', map_mul]
  have haf : a * f x / f x = a := by field_simp
  rw [haf]
  change (-I * (a.im : ℂ)) * ((starRingEnd ℂ) (f x) / (‖f x‖ : ℂ)) =
    ((starRingEnd ℂ) a * (starRingEnd ℂ) (f x) * (‖f x‖ : ℂ) -
      (starRingEnd ℂ) (f x) * ((‖f x‖ * a.re : ℝ) : ℂ)) /
      (‖f x‖ : ℂ) ^ 2
  have hcast : ((‖f x‖ * a.re : ℝ) : ℂ) = (‖f x‖ : ℂ) * (a.re : ℂ) := by
    push_cast
    rfl
  rw [hcast]
  field_simp
  rw [ha]
  ring

/-- **Differentiability transfer through phase halving.**  Removing a differentiable complex
phase from a differentiable complex value and taking the resulting real amplitude preserves real
differentiability.  This general law discharges the regularity interface uniformly for Hardy Z
and all continuously oriented finite carriers. -/
theorem differentiable_phaseHalvedAmplitude
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w z : E → ℂ} (hw : Differentiable ℝ w) (hz : Differentiable ℝ z) :
    Differentiable ℝ (fun x => phaseHalvedAmplitude (w x) (z x)) := by
  intro x
  have hwc : DifferentiableAt ℝ (fun y => (starRingEnd ℂ) (w y)) x := by
    simpa using Complex.conjCLE.differentiableAt.comp x (hw x)
  exact Complex.reCLM.differentiableAt.comp x (hwc.mul (hz x))

/-- **Unitary phase-halving law.** A value obeys `w² * conj z = z` exactly when rotation by
`conj w` makes it real.  Thus a multiplicative conjugate-reflection law is equivalent to one real
scalar equation. -/
theorem isPhaseReflected_iff_rotated_im_eq_zero {w z : ℂ}
    (hw : IsUnitaryPhase w) :
    IsPhaseReflected w z ↔ ((starRingEnd ℂ) w * z).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  constructor
  · intro hz
    rw [map_mul, Complex.conj_conj]
    calc
      w * (starRingEnd ℂ) z
          = ((starRingEnd ℂ) w * w) * w * (starRingEnd ℂ) z := by
              rw [hw, one_mul]
      _ = (starRingEnd ℂ) w * (w * w * (starRingEnd ℂ) z) := by ring
      _ = (starRingEnd ℂ) w * z := by rw [hz]
  · intro hz
    have h := hz
    rw [map_mul, Complex.conj_conj] at h
    calc
      w * w * (starRingEnd ℂ) z
          = w * (w * (starRingEnd ℂ) z) := by ring
      _ = w * ((starRingEnd ℂ) w * z) := by rw [h]
      _ = (w * (starRingEnd ℂ) w) * z := by ring
      _ = z := by rw [mul_comm w, hw, one_mul]

/-- A unitary phase has norm one. -/
theorem IsUnitaryPhase.norm_eq_one {w : ℂ} (hw : IsUnitaryPhase w) : ‖w‖ = 1 := by
  have h := congrArg norm hw
  rw [norm_mul, Complex.norm_conj, norm_one] at h
  nlinarith [norm_nonneg w]

/-- A unitary phase is nonzero. -/
theorem IsUnitaryPhase.ne_zero {w : ℂ} (hw : IsUnitaryPhase w) : w ≠ 0 := by
  intro hzero
  unfold IsUnitaryPhase at hw
  rw [hzero, map_zero, zero_mul] at hw
  exact zero_ne_one hw

/-- Removing a unitary reflection phase produces the embedded real amplitude exactly. -/
theorem IsPhaseReflected.conj_mul_eq_ofReal_amplitude {w z : ℂ}
    (hw : IsUnitaryPhase w) (hz : IsPhaseReflected w z) :
    (starRingEnd ℂ) w * z = (phaseHalvedAmplitude w z : ℂ) := by
  apply Complex.ext
  · rfl
  · simp [phaseHalvedAmplitude, (isPhaseReflected_iff_rotated_im_eq_zero hw).mp hz]

/-- **Exact polar normal form.** Every unitary phase-reflected value is its phase times one real
amplitude. -/
theorem IsPhaseReflected.eq_phase_mul_amplitude {w z : ℂ}
    (hw : IsUnitaryPhase w) (hz : IsPhaseReflected w z) :
    z = w * (phaseHalvedAmplitude w z : ℂ) := by
  calc
    z = (w * (starRingEnd ℂ) w) * z := by rw [mul_comm w, hw, one_mul]
    _ = w * ((starRingEnd ℂ) w * z) := by ring
    _ = w * (phaseHalvedAmplitude w z : ℂ) := by
      rw [hz.conj_mul_eq_ofReal_amplitude hw]

/-- **Classification of the reflected fixed locus.**  For a unitary phase, a value satisfies the
reflection law exactly when it is the phase times a unique real amplitude.  The unique witness is
`phaseHalvedAmplitude w z`; this packages the fixed locus as one real line rather than merely
constructing a normal form in one direction. -/
theorem isPhaseReflected_iff_existsUnique_phase_mul {w z : ℂ}
    (hw : IsUnitaryPhase w) :
    IsPhaseReflected w z ↔ ∃! r : ℝ, z = w * (r : ℂ) := by
  constructor
  · intro hz
    refine ⟨phaseHalvedAmplitude w z, hz.eq_phase_mul_amplitude hw, ?_⟩
    intro r hr
    have hmul : w * (r : ℂ) = w * (phaseHalvedAmplitude w z : ℂ) := by
      rw [← hr]
      exact hz.eq_phase_mul_amplitude hw
    have hcast : (r : ℂ) = (phaseHalvedAmplitude w z : ℂ) :=
      mul_left_cancel₀ hw.ne_zero hmul
    exact Complex.ofReal_injective hcast
  · rintro ⟨r, hr, _⟩
    unfold IsPhaseReflected
    rw [hr, map_mul, Complex.conj_ofReal]
    unfold IsUnitaryPhase at hw
    calc
      w * w * ((starRingEnd ℂ) w * (r : ℂ)) =
          w * ((starRingEnd ℂ) w * w) * (r : ℂ) := by ring
      _ = w * (r : ℂ) := by rw [hw, mul_one]

/-- **Common-phase correlation law.**  The Hermitian product of two values fixed by the same
unitary reflection is the embedded product of their real amplitudes.  In particular, every
common-phase Gram entry is real; the complex reflected family has only one real direction. -/
theorem IsPhaseReflected.conj_mul_eq_amplitude_mul_amplitude {w z y : ℂ}
    (hw : IsUnitaryPhase w) (hz : IsPhaseReflected w z) (hy : IsPhaseReflected w y) :
    (starRingEnd ℂ) z * y =
      ((phaseHalvedAmplitude w z * phaseHalvedAmplitude w y : ℝ) : ℂ) := by
  let A := phaseHalvedAmplitude w z
  let B := phaseHalvedAmplitude w y
  have hzform : z = w * (A : ℂ) := by
    simpa [A] using hz.eq_phase_mul_amplitude hw
  have hyform : y = w * (B : ℂ) := by
    simpa [B] using hy.eq_phase_mul_amplitude hw
  change (starRingEnd ℂ) z * y = ((A * B : ℝ) : ℂ)
  rw [hzform, hyform, map_mul, Complex.conj_ofReal]
  calc
    (starRingEnd ℂ) w * (A : ℂ) * (w * (B : ℂ)) =
        ((starRingEnd ℂ) w * w) * ((A : ℂ) * (B : ℂ)) := by ring
    _ = (A : ℂ) * (B : ℂ) := by rw [hw, one_mul]
    _ = ((A * B : ℝ) : ℂ) := by
      push_cast
      ring

/-- **Weighted common-phase isometry.**  Every real linear combination of two values carrying
the same unitary reflection phase has exactly the absolute value of the corresponding real
amplitude combination as its norm.  This simultaneously covers distances, scaled errors, and
one-value norm laws. -/
theorem IsPhaseReflected.norm_real_mul_sub_real_mul_eq_abs_amplitude_sub
    {w z y : ℂ} (hw : IsUnitaryPhase w)
    (hz : IsPhaseReflected w z) (hy : IsPhaseReflected w y) (a b : ℝ) :
    ‖(a : ℂ) * z - (b : ℂ) * y‖ =
      |a * phaseHalvedAmplitude w z - b * phaseHalvedAmplitude w y| := by
  let A := phaseHalvedAmplitude w z
  let B := phaseHalvedAmplitude w y
  have hzform : z = w * (A : ℂ) := by
    simpa [A] using hz.eq_phase_mul_amplitude hw
  have hyform : y = w * (B : ℂ) := by
    simpa [B] using hy.eq_phase_mul_amplitude hw
  change ‖(a : ℂ) * z - (b : ℂ) * y‖ = |a * A - b * B|
  rw [hzform, hyform]
  rw [show (a : ℂ) * (w * (A : ℂ)) - (b : ℂ) * (w * (B : ℂ)) =
      w * ((a * A - b * B : ℝ) : ℂ) by
      push_cast
      ring,
    norm_mul, hw.norm_eq_one, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- The norm of a phase-reflected value is the absolute value of its real amplitude. -/
theorem IsPhaseReflected.norm_eq_abs_amplitude {w z : ℂ}
    (hw : IsUnitaryPhase w) (hz : IsPhaseReflected w z) :
    ‖z‖ = |phaseHalvedAmplitude w z| := by
  simpa using IsPhaseReflected.norm_real_mul_sub_real_mul_eq_abs_amplitude_sub
    hw hz hz 1 0

/-- Exact zero interface for a phase-reflected value. -/
theorem IsPhaseReflected.eq_zero_iff_amplitude_eq_zero {w z : ℂ}
    (hw : IsUnitaryPhase w) (hz : IsPhaseReflected w z) :
    z = 0 ↔ phaseHalvedAmplitude w z = 0 := by
  rw [← norm_eq_zero, hz.norm_eq_abs_amplitude hw, abs_eq_zero]

end GaloisForLFunctions.HTGeometry
