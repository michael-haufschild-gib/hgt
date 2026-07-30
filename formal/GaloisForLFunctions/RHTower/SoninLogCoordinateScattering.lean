import GaloisForLFunctions.RHTower.EvenL2LogUnitary
import GaloisForLFunctions.RHTower.ConstrainedProlateOperator
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry
import GaloisForLFunctions.HTGeometry.TwoProjectionSupersymmetry
import GaloisForLFunctions.HTGeometry.TwoOutcomePinchingKadison

/-!
# The true Sonin Fourier constraint in logarithmic coordinates

Normalized dilations become translations under the exact even logarithmic
unitary, but the Sonin Fourier transform does not become the ordinary Fourier
transform in that coordinate.  Its conjugate is an involutive scattering
operator which reverses translations.

The distinction is forced by the orbital-length commutator.  Multiplication by
`log |x|` has scalar commutator `-log p` with normalized dilation by `p`, whereas
ordinary position has an `x`-dependent commutator and cannot produce any scalar
orbital length.  Thus a Sonin realization of the Euler logarithm must carry the
Mellin-scattering/Burnol conductor channel; the ordinary-position two-edge
Fourier-cutoff calculation is not that channel.
-/

open Complex

namespace RHTower

noncomputable section

/-- The original Fourier involution conjugated through the exact even
logarithmic-coordinate unitary. -/
def soninLogFourierScattering : SoninL2 →L[ℂ] SoninL2 :=
  logEvenUnitary.toLinearIsometry.toContinuousLinearMap ∘L
    evenFourierTransform ∘L
      logEvenUnitary.symm.toLinearIsometry.toContinuousLinearMap

@[simp] theorem soninLogFourierScattering_apply (g : SoninL2) :
    soninLogFourierScattering g =
      logEvenUnitary (evenFourierTransform (logEvenUnitary.symm g)) := rfl

/-- Original Fourier inversion sends physical dilation by `p` to dilation by
`p⁻¹`, also on the even carrier. -/
theorem evenFourierTransform_evenDilation
    (p : ℝ) (hp : 0 < p) (f : evenSubspace) :
    evenFourierTransform (evenDilationUnitary p hp f) =
      evenDilationUnitary p⁻¹ (inv_pos.mpr hp) (evenFourierTransform f) := by
  apply Subtype.ext
  exact fourierUnitary_dilation p hp f

/-- The logarithmic-coordinate Sonin Fourier scattering is an involution. -/
@[simp] theorem soninLogFourierScattering_involutive (g : SoninL2) :
    soninLogFourierScattering (soninLogFourierScattering g) = g := by
  change logEvenUnitary
      (evenFourierTransform
        (logEvenUnitary.symm
          (logEvenUnitary
            (evenFourierTransform (logEvenUnitary.symm g))))) = g
  rw [logEvenUnitary.symm_apply_apply, evenFourierTransform_involutive,
    logEvenUnitary.apply_symm_apply]

/-- The logarithmic-coordinate Sonin Fourier scattering preserves the Hilbert norm. -/
theorem soninLogFourierScattering_norm (g : SoninL2) :
    ‖soninLogFourierScattering g‖ = ‖g‖ := by
  rw [soninLogFourierScattering_apply, logEvenUnitary.norm_map,
    evenFourierTransform_isometry, logEvenUnitary.symm.norm_map]

/-- Operator form of the unitarity of logarithmic Sonin Fourier scattering. -/
theorem soninLogFourierScattering_adjoint_mul_self :
    soninLogFourierScattering.adjoint * soninLogFourierScattering = 1 := by
  simpa only [ContinuousLinearMap.mul_def] using
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self
      soninLogFourierScattering).mp soninLogFourierScattering_norm

/-- Operator form of the existing involution relation. -/
theorem soninLogFourierScattering_sq_eq_one :
    soninLogFourierScattering ^ 2 = 1 := by
  apply ContinuousLinearMap.ext
  intro g
  change soninLogFourierScattering (soninLogFourierScattering g) = g
  exact soninLogFourierScattering_involutive g

/-- The involutive unitary logarithmic scattering is self-adjoint. -/
theorem soninLogFourierScattering_isSelfAdjoint :
    IsSelfAdjoint soninLogFourierScattering :=
  HTGeometry.isSelfAdjoint_of_adjoint_mul_self_of_sq_eq_one
    soninLogFourierScattering soninLogFourierScattering_adjoint_mul_self
    soninLogFourierScattering_sq_eq_one

/-- **Sonin optical-theorem collapse.**  The positive master constraint of logarithmic Fourier
scattering is not a new quadratic operator: involutive unitarity reduces it exactly to twice the
anti-invariant scattering sector. -/
theorem quantumMasterConstraint_soninLogFourierScattering_eq_two_mul_complement :
    HTGeometry.quantumMasterConstraint (soninLogFourierScattering - 1) =
      2 * (1 - soninLogFourierScattering) := by
  exact HTGeometry.quantumMasterConstraint_involutiveScattering_eq_two_mul_complement
    soninLogFourierScattering soninLogFourierScattering_adjoint_mul_self
    soninLogFourierScattering_sq_eq_one

/-- The `Z₂` group average selecting the invariant logarithmic Sonin scattering sector. -/
def soninLogFourierInvariantAverage : SoninL2 →L[ℂ] SoninL2 :=
  HTGeometry.finiteCyclicGaugeAverage soninLogFourierScattering 2

/-- The invariant-sector average is an orthogonal projection: its self-adjointness no longer has
to be supplied as a downstream hypothesis. -/
theorem soninLogFourierInvariantAverage_isSelfAdjoint :
    IsSelfAdjoint soninLogFourierInvariantAverage := by
  exact HTGeometry.finiteInvolutiveGaugeAverage_isSelfAdjoint
    soninLogFourierScattering soninLogFourierScattering_adjoint_mul_self
    soninLogFourierScattering_sq_eq_one

/-- The invariant-sector average is idempotent without a downstream projection hypothesis. -/
theorem soninLogFourierInvariantAverage_isIdempotentElem :
    IsIdempotentElem soninLogFourierInvariantAverage := by
  exact HTGeometry.finiteInvolutiveGaugeAverage_isIdempotentElem
    soninLogFourierScattering soninLogFourierScattering_sq_eq_one

/-- The fixed vectors of the logarithmic scattering average are exactly the physical vectors for
the static constraint `S - 1`. -/
theorem physicalState_soninLogFourierScattering_iff_invariantAverage_fixed
    (g : SoninL2) :
    GaloisForLFunctions.PhysicalState (soninLogFourierScattering - 1).toLinearMap g ↔
      soninLogFourierInvariantAverage g = g := by
  exact HTGeometry.physicalState_iff_finiteCyclicGaugeAverage_fixed
    soninLogFourierScattering 2 two_ne_zero soninLogFourierScattering_sq_eq_one g

/-- **Exact Sonin physical-sector image.**  Logarithmic scattering averaging maps onto precisely
the kernel of the static scattering constraint. -/
theorem soninLogFourierInvariantAverage_range_eq_constraint_ker :
    soninLogFourierInvariantAverage.toLinearMap.range =
      LinearMap.ker (soninLogFourierScattering - 1).toLinearMap := by
  simpa only [soninLogFourierInvariantAverage] using
    (HTGeometry.finiteCyclicGaugeAverage_range_eq_constraint_ker
      soninLogFourierScattering 2 two_ne_zero soninLogFourierScattering_sq_eq_one)

/-- The same invariant Sonin sector is exactly the zero-energy space of the positive scattering
master constraint. -/
theorem soninLogFourierInvariantAverage_range_eq_masterConstraint_ker :
    soninLogFourierInvariantAverage.toLinearMap.range =
      (HTGeometry.quantumMasterConstraint
        (soninLogFourierScattering - 1)).toLinearMap.ker := by
  simpa only [soninLogFourierInvariantAverage] using
    (HTGeometry.finiteCyclicGaugeAverage_range_eq_masterConstraint_ker
      soninLogFourierScattering 2 two_ne_zero soninLogFourierScattering_sq_eq_one)

/-- The `Z₂` observer-algebra projection of a Sonin observable under logarithmic Fourier
scattering.  This is a static observable average, not a temporal evolution. -/
def soninLogFourierObservableTwirl
    (A : SoninL2 →L[ℂ] SoninL2) : SoninL2 →L[ℂ] SoninL2 :=
  HTGeometry.finiteCyclicObservableTwirl soninLogFourierScattering A 2

/-- The Sonin observable twirl is an exact projection onto the scattering commutant. -/
theorem soninLogFourierObservableTwirl_idempotent
    (A : SoninL2 →L[ℂ] SoninL2) :
    soninLogFourierObservableTwirl (soninLogFourierObservableTwirl A) =
      soninLogFourierObservableTwirl A := by
  exact HTGeometry.finiteCyclicObservableTwirl_idempotent
    soninLogFourierScattering A 2 two_ne_zero soninLogFourierScattering_sq_eq_one

/-- On scattering-invariant states, the observer-algebra projection preserves every Sonin
matrix element.  Thus the observable relation survives even though the global state obeys the
static constraint `S - 1`. -/
theorem inner_soninLogFourierObservableTwirl_eq_of_fixed
    (A : SoninL2 →L[ℂ] SoninL2) {φ ψ : SoninL2}
    (hφ : soninLogFourierScattering φ = φ)
    (hψ : soninLogFourierScattering ψ = ψ) :
    inner ℂ φ (soninLogFourierObservableTwirl A ψ) = inner ℂ φ (A ψ) := by
  have hφadj : soninLogFourierScattering.adjoint φ = φ := by
    have hadj := soninLogFourierScattering_isSelfAdjoint.star_eq
    change soninLogFourierScattering.adjoint = soninLogFourierScattering at hadj
    rw [hadj, hφ]
  exact HTGeometry.inner_finiteCyclicObservableTwirl_of_fixed
    soninLogFourierScattering A 2 two_ne_zero hφadj hψ

/-- The complete conditional Sonin value is likewise unchanged by observable twirling.  This is
the direct RHTower form of the periodic-clock Page--Wootters/Dirac equivalence. -/
theorem soninLogFourierConditionalValue_twirl_eq_of_fixed
    (A B : SoninL2 →L[ℂ] SoninL2) {φ ψ : SoninL2}
    (hφ : soninLogFourierScattering φ = φ)
    (hψ : soninLogFourierScattering ψ = ψ) :
    inner ℂ φ (soninLogFourierObservableTwirl A ψ) /
        inner ℂ φ (soninLogFourierObservableTwirl B ψ) =
      inner ℂ φ (A ψ) / inner ℂ φ (B ψ) := by
  rw [inner_soninLogFourierObservableTwirl_eq_of_fixed A hφ hψ,
    inner_soninLogFourierObservableTwirl_eq_of_fixed B hφ hψ]

/-- A complementary two-reading Sonin clock has uniform raw weight on every invariant state.
Consequently its nontrivial clock information can only occur in conditional observable values. -/
theorem soninStationaryClockEffect_matrixElement_eq_half_of_fixed
    (e : SoninL2 →L[ℂ] SoninL2) {φ ψ : SoninL2}
    (hφ : soninLogFourierScattering φ = φ)
    (hψ : soninLogFourierScattering ψ = ψ)
    (hresolve : soninLogFourierObservableTwirl e = ((2 : ℂ)⁻¹) • 1) :
    inner ℂ φ (e ψ) = (2 : ℂ)⁻¹ * inner ℂ φ ψ := by
  calc
    inner ℂ φ (e ψ) = inner ℂ φ (soninLogFourierObservableTwirl e ψ) :=
      (inner_soninLogFourierObservableTwirl_eq_of_fixed e hφ hψ).symm
    _ = (2 : ℂ)⁻¹ * inner ℂ φ ψ := by
      rw [hresolve, _root_.smul_apply, inner_smul_right]
      simp

/-- The multiplicativity defect of the Sonin clock-observer projection.  It vanishes exactly
when the observed self-adjoint quantity has no transition energy between the invariant and
anti-invariant logarithmic-scattering sectors. -/
def soninLogFourierObservableTwirlKadisonDefect
    (X : SoninL2 →L[ℂ] SoninL2) : SoninL2 →L[ℂ] SoninL2 :=
  HTGeometry.finiteInvolutiveObservableTwirlKadisonDefect
    soninLogFourierScattering X

/-- The Sonin clock-observability defect vanishes exactly for observables commuting with
logarithmic Fourier scattering.  This is the direct Sonin instance of the general static clock
criterion in `HTGeometry`. -/
theorem soninLogFourierObservableTwirlKadisonDefect_eq_zero_iff_commutes
    (X : SoninL2 →L[ℂ] SoninL2) (hXAdj : X.adjoint = X) :
    soninLogFourierObservableTwirlKadisonDefect X = 0 ↔
      soninLogFourierScattering * X = X * soninLogFourierScattering := by
  simpa only [soninLogFourierObservableTwirlKadisonDefect] using
    HTGeometry.finiteInvolutiveObservableTwirlKadisonDefect_eq_zero_iff_commutes
      soninLogFourierScattering X soninLogFourierScattering_adjoint_mul_self
      soninLogFourierScattering_sq_eq_one hXAdj

/-- **Sonin clock-observability energy.**  The clock-twirl defect is exactly the sum of the
squared transitions across the physical/nonphysical logarithmic-scattering split.  In
particular, its positivity needs no additional operator hypothesis. -/
theorem re_inner_soninLogFourierObservableTwirlKadisonDefect_eq_transitionNormSq_add
    (X : SoninL2 →L[ℂ] SoninL2) (hXAdj : X.adjoint = X) (psi : SoninL2) :
    Complex.re
        (inner ℂ psi (soninLogFourierObservableTwirlKadisonDefect X psi)) =
      ‖HTGeometry.twoOutcomeLowerTransition
          soninLogFourierInvariantAverage X psi‖ ^ 2 +
      ‖HTGeometry.twoOutcomeUpperTransition
          soninLogFourierInvariantAverage X psi‖ ^ 2 := by
  simpa only [soninLogFourierObservableTwirlKadisonDefect,
    soninLogFourierInvariantAverage] using!
      HTGeometry.re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_transitionNormSq_add
        soninLogFourierScattering X soninLogFourierScattering_adjoint_mul_self
        soninLogFourierScattering_sq_eq_one hXAdj psi

/-- **Physical Sonin clock commutator law.**  On the static logarithmic-scattering constraint
surface, the full clock-observability defect is exactly one quarter of the squared commutator
between the observed quantity and scattering.  No time evolution or positivity premise remains. -/
theorem re_inner_soninLogFourierObservableTwirlKadisonDefect_eq_quarter_commutatorNormSq
    (X : SoninL2 →L[ℂ] SoninL2) (hXAdj : X.adjoint = X) {psi : SoninL2}
    (hpsi : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap psi) :
    Complex.re
        (inner ℂ psi (soninLogFourierObservableTwirlKadisonDefect X psi)) =
      (4 : ℝ)⁻¹ *
        ‖((X * soninLogFourierScattering - soninLogFourierScattering * X) :
          SoninL2 →L[ℂ] SoninL2) psi‖ ^ 2 := by
  rw [GaloisForLFunctions.PhysicalState] at hpsi
  have hfixed : soninLogFourierScattering psi = psi := by
    apply sub_eq_zero.mp
    simpa using hpsi
  exact
    HTGeometry.re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_quarter_commutatorNormSq_of_fixed
      soninLogFourierScattering X soninLogFourierScattering_adjoint_mul_self
      soninLogFourierScattering_sq_eq_one hXAdj hfixed

/-- A physical Sonin state carries zero clock-observability energy exactly when the
scattering--observable commutator annihilates that state. -/
theorem re_inner_soninLogFourierObservableTwirlKadisonDefect_eq_zero_iff_commutator
    (X : SoninL2 →L[ℂ] SoninL2) (hXAdj : X.adjoint = X) {psi : SoninL2}
    (hpsi : GaloisForLFunctions.PhysicalState
      (soninLogFourierScattering - 1).toLinearMap psi) :
    Complex.re
        (inner ℂ psi (soninLogFourierObservableTwirlKadisonDefect X psi)) = 0 ↔
      ((X * soninLogFourierScattering - soninLogFourierScattering * X) :
        SoninL2 →L[ℂ] SoninL2) psi = 0 := by
  rw [GaloisForLFunctions.PhysicalState] at hpsi
  have hfixed : soninLogFourierScattering psi = psi := by
    apply sub_eq_zero.mp
    simpa using hpsi
  exact
    HTGeometry.re_inner_finiteInvolutiveObservableTwirlKadisonDefect_eq_zero_iff_commutator_of_fixed
      soninLogFourierScattering X soninLogFourierScattering_adjoint_mul_self
      soninLogFourierScattering_sq_eq_one hXAdj hfixed

/-- **Invariant/anti-invariant scattering energy partition.**  Every logarithmic Sonin state
splits exactly into its group-averaged physical part and its orthogonal complement. -/
theorem norm_soninLogFourierInvariantAverage_sq_add_complement_sq (g : SoninL2) :
    ‖soninLogFourierInvariantAverage g‖ ^ 2 +
        ‖(1 - soninLogFourierInvariantAverage) g‖ ^ 2 = ‖g‖ ^ 2 := by
  exact HTGeometry.norm_finiteInvolutiveGaugeAverage_sq_add_complement_sq
    soninLogFourierScattering soninLogFourierScattering_adjoint_mul_self
    soninLogFourierScattering_sq_eq_one g

/-- The native logarithmic Sonin scattering reverses additive translations.
This is the exact conjugate of `Fourier · dilation(p) = dilation(p⁻¹) · Fourier`. -/
theorem soninLogFourierScattering_additiveTranslation
    (p : ℝ) (hp : 0 < p) (g : SoninL2) :
    soninLogFourierScattering
        (MellinL2.additiveTranslationUnitary (Real.log p) g) =
      MellinL2.additiveTranslationUnitary (-Real.log p)
        (soninLogFourierScattering g) := by
  let f : evenSubspace := logEvenUnitary.symm g
  have hforward := logEvenUnitary_evenDilation p hp f
  have hfg : logEvenUnitary f = g := logEvenUnitary.apply_symm_apply g
  rw [hfg] at hforward
  rw [← hforward]
  simp only [soninLogFourierScattering_apply,
    logEvenUnitary.symm_apply_apply]
  rw [evenFourierTransform_evenDilation]
  rw [logEvenUnitary_evenDilation]
  rw [Real.log_inv]

/-- The invariant-sector projector is the explicit `Z₂` symmetrizer `(1 + S) / 2`. -/
theorem soninLogFourierInvariantAverage_apply (g : SoninL2) :
    soninLogFourierInvariantAverage g =
      ((2 : ℂ)⁻¹) • (g + soninLogFourierScattering g) := by
  simp [soninLogFourierInvariantAverage, HTGeometry.finiteCyclicGaugeAverage,
    HTGeometry.finiteCyclicGaugeSum, add_comm]

/-- On a scattering-invariant state, group averaging a translated state produces the exact
forward/backward logarithmic-translation pair.  This is the static cosine-channel relation used
by the Mellin/dilation corpus, with no extra projection hypothesis. -/
theorem soninLogFourierInvariantAverage_additiveTranslation_of_fixed
    (p : ℝ) (hp : 0 < p) (g : SoninL2)
    (hfixed : soninLogFourierScattering g = g) :
    soninLogFourierInvariantAverage
        (MellinL2.additiveTranslationUnitary (Real.log p) g) =
      ((2 : ℂ)⁻¹) •
        (MellinL2.additiveTranslationUnitary (Real.log p) g +
          MellinL2.additiveTranslationUnitary (-Real.log p) g) := by
  rw [soninLogFourierInvariantAverage_apply,
    soninLogFourierScattering_additiveTranslation p hp, hfixed]

/-- Pointwise logarithmic-position multiplier on a common function core. -/
def logPositionFunction (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.log |x| : ℂ) * f x

/-- Pointwise normalized physical dilation. -/
def normalizedDilationFunction (p : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.sqrt p : ℂ) * f (p * x)

/-- Exact orbital-length commutator.  Away from the null point `x=0`,
`[log|x|, U_p] = -log(p) U_p`. -/
theorem logPosition_normalizedDilation_commutator
    (p : ℝ) (hp : 0 < p) (f : ℝ → ℂ) {x : ℝ} (hx : x ≠ 0) :
    logPositionFunction (normalizedDilationFunction p f) x -
        normalizedDilationFunction p (logPositionFunction f) x =
      -(Real.log p : ℂ) * normalizedDilationFunction p f x := by
  have habsx : 0 < |x| := abs_pos.mpr hx
  have habs : |p * x| = p * |x| := by rw [abs_mul, abs_of_pos hp]
  rw [logPositionFunction, normalizedDilationFunction,
    normalizedDilationFunction, logPositionFunction, habs,
    Real.log_mul hp.ne' habsx.ne']
  push_cast
  ring

/-- Ordinary position, the multiplier used by the finite-edge Fourier
commutator, has an `x`-dependent dilation commutator. -/
def ordinaryPositionFunction (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) * f x

theorem ordinaryPosition_normalizedDilation_commutator
    (p : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    ordinaryPositionFunction (normalizedDilationFunction p f) x -
        normalizedDilationFunction p (ordinaryPositionFunction f) x =
      ((1 - p) * x : ℝ) * normalizedDilationFunction p f x := by
  simp [ordinaryPositionFunction, normalizedDilationFunction]
  ring

/-- For a nontrivial dilation, ordinary position cannot have any scalar
commutator even on the constant pointwise test.  It therefore cannot supply the
Euler orbital length `log p`. -/
theorem ordinaryPosition_commutator_not_scalar
    (p : ℝ) (hp : 0 < p) (hp1 : p ≠ 1) :
    ¬ ∃ c : ℂ, ∀ x : ℝ,
      ordinaryPositionFunction (normalizedDilationFunction p (fun _ => 1)) x -
          normalizedDilationFunction p (ordinaryPositionFunction (fun _ => 1)) x =
        c * normalizedDilationFunction p (fun _ => 1) x := by
  rintro ⟨c, h⟩
  have h0 := h 0
  have hsqrt : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr hp)
  have hc : c = 0 := by
    simpa [ordinaryPositionFunction, normalizedDilationFunction, hsqrt] using
      (mul_eq_zero.mp (by
        simpa [ordinaryPositionFunction, normalizedDilationFunction] using h0)).resolve_right hsqrt
  have h1 := h 1
  rw [hc] at h1
  simp [ordinaryPositionFunction, normalizedDilationFunction] at h1
  norm_cast at h1
  exact hp1 (by nlinarith [Real.sqrt_pos.2 hp])

end

end RHTower
