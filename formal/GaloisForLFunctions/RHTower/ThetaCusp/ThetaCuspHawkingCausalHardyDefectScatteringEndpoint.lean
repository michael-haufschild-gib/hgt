import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingStimulatedCubicUnmaskingEndpoint
import GaloisForLFunctions.HTGeometry.HardyLeakageRankOne

/-!
# Causal Hardy-defect Bogoliubov scattering endpoint

This endpoint removes the arbitrary-selector gap left by stimulated cubic
unmasking.  An upper theta-Hawking resonance has a one-dimensional causal
Hardy defect.  Orthogonal projection onto that Gamow/Szego line and its
outgoing complement canonically lifts the genuine modular coefficients
`cosh r` and `sinh r` to the whole causal carrier.

* **[PROVED FULL S-MATRIX]** The resulting two-input exterior/partner map is
  a rapidity-additive group, has inverse at `-r`, and preserves the full
  Nambu/Krein norm for arbitrary Hardy inputs.  Its reduced exterior leg is
  the unique continuous linear map that fixes every outgoing scattering
  state and multiplies the defect line by `cosh r`.
* **[PROVED SOURCE WELD]** Inverse Cayley transport of the same defect node
  reconstructs the resonance spectral square exactly.  Its real part and
  squared imaginary part are therefore precisely the squared-Euler orbit
  parameters, for either physical resonance orientation.  The selectively
  stimulated kernel is now defined from the scattering defect itself and is
  theorem-equal to the former Xi-labelled kernel.
* **[PROVED REDUCTION]** Every off-critical orbit yields one such full
  pseudo-unitary scattering channel whose genuine modular gain eventually
  forces a negative three-shell determinant.  Stability of every canonical
  defect-stimulated channel is equivalent to RH.

This is not an RH proof: no generic KMS, CCR, group, inverse, or Krein law
forces that final three-shell stability.  Remaining producer is a
coefficient-faithful theta backreaction/passivity theorem excluding the
negative cubic chamber for these already-canonical channels.

Physical motivation is source-faithful: stimulated Hawking output is governed
by Bogoliubov coefficients (arXiv:2110.06796), recent analogue work finds
transmission peaked at a quasinormal-mode frequency under pseudo-unitary
Bogoliubov scattering (arXiv:2511.12339), and Lax--Phillips resonance states
live in the scattering Hilbert space (arXiv:hep-th/9709036).  The synthesis
with the theta/Xi squared-Euler response is local research; novelty remains
unverified.
-/

open Complex Real

noncomputable section

namespace RHTower

private abbrev ThetaCuspHawkingHardyCarrier :=
  GaloisForLFunctions.HTGeometry.HardyDisk

/-- Rank-one Gamow/Szego defect line of an upper theta-Hawking resonance. -/
def thetaCuspHawkingCausalHardyDefectLine
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) : Submodule ℂ ThetaCuspHawkingHardyCarrier :=
  ℂ ∙ thetaCuspHawkingCausalHardyKernel mode hmode

noncomputable instance thetaCuspHawkingCausalHardyDefectLineFiniteDimensional
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) :
    FiniteDimensional ℂ (thetaCuspHawkingCausalHardyDefectLine mode hmode) := by
  unfold thetaCuspHawkingCausalHardyDefectLine
  exact FiniteDimensional.span_singleton ℂ _

noncomputable instance thetaCuspHawkingCausalHardyDefectLineHasOrthogonalProjection
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) :
    (thetaCuspHawkingCausalHardyDefectLine mode hmode).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- Exterior leg of the canonical defect-supported Hawking dilation. -/
def thetaCuspHawkingCausalHardyExterior
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) : ThetaCuspHawkingHardyCarrier →L[ℂ] ThetaCuspHawkingHardyCarrier :=
  ((Real.cosh r : ℂ) • (thetaCuspHawkingCausalHardyDefectLine mode hmode).starProjection) +
    (thetaCuspHawkingCausalHardyDefectLine mode hmode)ᗮ.starProjection

/-- Partner leg of the canonical defect-supported Hawking dilation. -/
def thetaCuspHawkingCausalHardyPartner
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) : ThetaCuspHawkingHardyCarrier →L[ℂ] ThetaCuspHawkingHardyCarrier :=
  (Real.sinh r : ℂ) • (thetaCuspHawkingCausalHardyDefectLine mode hmode).starProjection

theorem thetaCuspHawkingCausalHardyExterior_apply
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f : ThetaCuspHawkingHardyCarrier) :
    thetaCuspHawkingCausalHardyExterior mode hmode r f =
      (Real.cosh r : ℂ) • (thetaCuspHawkingCausalHardyDefectLine mode hmode).starProjection f +
        (thetaCuspHawkingCausalHardyDefectLine mode hmode)ᗮ.starProjection f := rfl

theorem thetaCuspHawkingCausalHardyPartner_apply
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f : ThetaCuspHawkingHardyCarrier) :
    thetaCuspHawkingCausalHardyPartner mode hmode r f =
      (Real.sinh r : ℂ) • (thetaCuspHawkingCausalHardyDefectLine mode hmode).starProjection f := rfl

theorem thetaCuspHawkingCausalHardyDefectDilation_fixes_outgoingRange
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f : ThetaCuspHawkingHardyCarrier)
    (hf : f ∈ thetaCuspHawkingCausalHardyRange mode hmode) :
    thetaCuspHawkingCausalHardyExterior mode hmode r f = f ∧ thetaCuspHawkingCausalHardyPartner mode hmode r f = 0 := by
  let S := thetaCuspHawkingCausalHardyDefectLine mode hmode
  have hfS : f ∈ Sᗮ := by
    rw [thetaCuspHawkingCausalHardyRange_eq_kernel_orthogonal] at hf
    simpa [S, thetaCuspHawkingCausalHardyDefectLine] using hf
  have hP : S.starProjection f = 0 :=
    S.starProjection_apply_eq_zero_iff.mpr hfS
  have hQ : Sᗮ.starProjection f = f :=
    Submodule.starProjection_eq_self_iff.mpr hfS
  constructor <;> simp [thetaCuspHawkingCausalHardyExterior, thetaCuspHawkingCausalHardyPartner, S, hP, hQ]

theorem thetaCuspHawkingCausalHardyDefectDilation_on_gamowKernel
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) :
    thetaCuspHawkingCausalHardyExterior mode hmode r
        (thetaCuspHawkingCausalHardyKernel mode hmode) =
      (Real.cosh r : ℂ) • thetaCuspHawkingCausalHardyKernel mode hmode ∧
    thetaCuspHawkingCausalHardyPartner mode hmode r
        (thetaCuspHawkingCausalHardyKernel mode hmode) =
      (Real.sinh r : ℂ) • thetaCuspHawkingCausalHardyKernel mode hmode := by
  let S := thetaCuspHawkingCausalHardyDefectLine mode hmode
  let k := thetaCuspHawkingCausalHardyKernel mode hmode
  have hkS : k ∈ S := by
    exact Submodule.mem_span_singleton_self k
  have hP : S.starProjection k = k :=
    Submodule.starProjection_eq_self_iff.mpr hkS
  have hsum := S.starProjection_add_starProjection_orthogonal k
  have hQ : Sᗮ.starProjection k = 0 := by rw [hP] at hsum; exact add_eq_left.mp hsum
  constructor <;> simp [thetaCuspHawkingCausalHardyExterior, thetaCuspHawkingCausalHardyPartner, S, k, hP, hQ]

theorem thetaCuspHawkingCausalHardyVacuumPartner_krein
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f : ThetaCuspHawkingHardyCarrier) :
    ‖thetaCuspHawkingCausalHardyExterior mode hmode r f‖ ^ (2 : ℕ) -
        ‖thetaCuspHawkingCausalHardyPartner mode hmode r f‖ ^ (2 : ℕ) = ‖f‖ ^ (2 : ℕ) := by
  let S := thetaCuspHawkingCausalHardyDefectLine mode hmode
  let p := S.starProjection f
  let q := Sᗮ.starProjection f
  have hp : p ∈ S := S.starProjection_apply_mem f
  have hq : q ∈ Sᗮ := Sᗮ.starProjection_apply_mem f
  have horth : (inner ℂ ((Real.cosh r : ℂ) • p) q : ℂ) = 0 := by
    rw [inner_smul_left]
    rw [(Submodule.mem_orthogonal S q).mp hq p hp, mul_zero]
  have hext : ‖thetaCuspHawkingCausalHardyExterior mode hmode r f‖ ^ (2 : ℕ) =
      ‖(Real.cosh r : ℂ) • p‖ ^ (2 : ℕ) + ‖q‖ ^ (2 : ℕ) := by
    rw [thetaCuspHawkingCausalHardyExterior_apply]
    simpa only [S, p, q, pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have hsplit : ‖f‖ ^ (2 : ℕ) = ‖p‖ ^ (2 : ℕ) + ‖q‖ ^ (2 : ℕ) := by
    simpa only [p, q] using Submodule.norm_sq_eq_add_norm_sq_starProjection f S
  have hext' : ‖thetaCuspHawkingCausalHardyExterior mode hmode r f‖ ^ (2 : ℕ) =
      Real.cosh r ^ (2 : ℕ) * ‖p‖ ^ (2 : ℕ) + ‖q‖ ^ (2 : ℕ) := by
    rw [hext, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.cosh_pos r), mul_pow]
  have hpartner : ‖thetaCuspHawkingCausalHardyPartner mode hmode r f‖ ^ (2 : ℕ) =
      Real.sinh r ^ (2 : ℕ) * ‖p‖ ^ (2 : ℕ) := by
    rw [thetaCuspHawkingCausalHardyPartner_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    change (|Real.sinh r| * ‖p‖) ^ (2 : ℕ) = _
    rw [mul_pow, sq_abs]
  rw [hext', hpartner]
  nlinarith [Real.cosh_sq_sub_sinh_sq r]

theorem thetaCuspHawkingCausalHardyExterior_unique
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ)
    (A : ThetaCuspHawkingHardyCarrier →L[ℂ] ThetaCuspHawkingHardyCarrier)
    (hdef : ∀ f : ThetaCuspHawkingHardyCarrier, f ∈ thetaCuspHawkingCausalHardyDefectLine mode hmode →
      A f = (Real.cosh r : ℂ) • f)
    (hout : ∀ f : ThetaCuspHawkingHardyCarrier,
      f ∈ thetaCuspHawkingCausalHardyRange mode hmode → A f = f) :
    A = thetaCuspHawkingCausalHardyExterior mode hmode r := by
  let S := thetaCuspHawkingCausalHardyDefectLine mode hmode
  apply ContinuousLinearMap.ext
  intro f
  let p := S.starProjection f
  let q := Sᗮ.starProjection f
  have hp : p ∈ S := S.starProjection_apply_mem f
  have hqS : q ∈ Sᗮ := Sᗮ.starProjection_apply_mem f
  have hq : q ∈ thetaCuspHawkingCausalHardyRange mode hmode := by
    rw [thetaCuspHawkingCausalHardyRange_eq_kernel_orthogonal]
    simpa [S, thetaCuspHawkingCausalHardyDefectLine] using hqS
  have hsplit := S.starProjection_add_starProjection_orthogonal f
  have hsplit' : p + q = f := hsplit
  calc
    A f = A (p + q) := by rw [hsplit']
    _ = A p + A q := map_add A p q
    _ = (Real.cosh r : ℂ) • p + q := by rw [hdef p hp, hout q hq]
    _ = thetaCuspHawkingCausalHardyExterior mode hmode r f := by rfl

/-- Spectral square reconstructed only from the causal Hardy node. -/
def thetaCuspHawkingCausalHardyReconstructedSpectralSquare
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (_hmode : 0 < mode.1.im) : ℂ :=
  -((1 + thetaCuspHawkingCausalHardyNode mode) /
      (1 - thetaCuspHawkingCausalHardyNode mode)) ^ (2 : ℕ)

theorem thetaCuspHawkingCausalHardyReconstructedSpectralSquare_eq
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) :
    thetaCuspHawkingCausalHardyReconstructedSpectralSquare mode hmode = mode.1 ^ (2 : ℕ) := by
  unfold thetaCuspHawkingCausalHardyReconstructedSpectralSquare thetaCuspHawkingCausalHardyNode
  rw [GaloisForLFunctions.HTGeometry.cayleyRight_inv]
  · unfold thetaCuspHawkingCausalZero
    rw [mul_pow]
    simp [Complex.I_sq]
  · rw [thetaCuspHawkingCausalZero_re]
    exact hmode.le

def thetaCuspHawkingCausalHardyOrbitT
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) : ℝ :=
  (thetaCuspHawkingCausalHardyReconstructedSpectralSquare mode hmode).re

def thetaCuspHawkingCausalHardyOrbitCharge
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) : ℝ :=
  (thetaCuspHawkingCausalHardyReconstructedSpectralSquare mode hmode).im ^ (2 : ℕ)

def thetaCuspHawkingCausalHardyOrbitKernel
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (x y : ℝ) : ℝ :=
  squaredEulerOrbitKernel (thetaCuspHawkingCausalHardyOrbitT mode hmode)
    (thetaCuspHawkingCausalHardyOrbitCharge mode hmode) x y

theorem thetaCuspHawkingCausalHardyOrbitT_original
    (q : XiZeroCopy)
    (hmode : 0 < (thetaCuspHawkingXiOrbitResonantMode q).1.im) :
    thetaCuspHawkingCausalHardyOrbitT (thetaCuspHawkingXiOrbitResonantMode q) hmode =
      xiSquaredEulerOrbitT q := by
  rw [thetaCuspHawkingCausalHardyOrbitT, thetaCuspHawkingCausalHardyReconstructedSpectralSquare_eq,
    thetaCuspHawkingXiOrbitResonantMode_value,
    xiSpectralPoint_sq_re_eq_squaredEulerOrbitT]

theorem thetaCuspHawkingCausalHardyOrbitCharge_original
    (q : XiZeroCopy)
    (hmode : 0 < (thetaCuspHawkingXiOrbitResonantMode q).1.im) :
    thetaCuspHawkingCausalHardyOrbitCharge (thetaCuspHawkingXiOrbitResonantMode q) hmode =
      xiSquaredEulerOrbitCharge q := by
  rw [thetaCuspHawkingCausalHardyOrbitCharge, thetaCuspHawkingCausalHardyReconstructedSpectralSquare_eq,
    thetaCuspHawkingXiOrbitResonantMode_value,
    xiSpectralPoint_sq_im_sq_eq_squaredEulerOrbitCharge]

theorem thetaCuspHawkingCausalHardyOrbitT_reflected
    (q : XiZeroCopy)
    (hmode : 0 < (thetaCuspHawkingBackreactionReflectedResonantMode
      (thetaCuspHawkingXiOrbitResonantMode q)).1.im) :
    thetaCuspHawkingCausalHardyOrbitT (thetaCuspHawkingBackreactionReflectedResonantMode
        (thetaCuspHawkingXiOrbitResonantMode q)) hmode =
      xiSquaredEulerOrbitT q := by
  rw [thetaCuspHawkingCausalHardyOrbitT, thetaCuspHawkingCausalHardyReconstructedSpectralSquare_eq]
  change ((-xiSpectralPoint q) ^ (2 : ℕ)).re = _
  rw [neg_sq, xiSpectralPoint_sq_re_eq_squaredEulerOrbitT]

theorem thetaCuspHawkingCausalHardyOrbitCharge_reflected
    (q : XiZeroCopy)
    (hmode : 0 < (thetaCuspHawkingBackreactionReflectedResonantMode
      (thetaCuspHawkingXiOrbitResonantMode q)).1.im) :
    thetaCuspHawkingCausalHardyOrbitCharge (thetaCuspHawkingBackreactionReflectedResonantMode
        (thetaCuspHawkingXiOrbitResonantMode q)) hmode =
      xiSquaredEulerOrbitCharge q := by
  rw [thetaCuspHawkingCausalHardyOrbitCharge, thetaCuspHawkingCausalHardyReconstructedSpectralSquare_eq]
  change ((-xiSpectralPoint q) ^ (2 : ℕ)).im ^ (2 : ℕ) = _
  rw [neg_sq, xiSpectralPoint_sq_im_sq_eq_squaredEulerOrbitCharge]

theorem thetaCuspHawkingCausalHardyOrbitKernel_eq_xiSquaredEulerOrbitKernel
    (q : XiZeroCopy) (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im)
    (horient : mode = thetaCuspHawkingXiOrbitResonantMode q ∨
      mode = thetaCuspHawkingBackreactionReflectedResonantMode
        (thetaCuspHawkingXiOrbitResonantMode q)) :
    thetaCuspHawkingCausalHardyOrbitKernel mode hmode = xiSquaredEulerOrbitKernel q := by
  funext x y
  rcases horient with rfl | rfl
  · rw [thetaCuspHawkingCausalHardyOrbitKernel, xiSquaredEulerOrbitKernel,
      thetaCuspHawkingCausalHardyOrbitT_original, thetaCuspHawkingCausalHardyOrbitCharge_original]
  · rw [thetaCuspHawkingCausalHardyOrbitKernel, xiSquaredEulerOrbitKernel,
      thetaCuspHawkingCausalHardyOrbitT_reflected, thetaCuspHawkingCausalHardyOrbitCharge_reflected]

theorem thetaCuspHawkingCausalHardyPartner_energy
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f : ThetaCuspHawkingHardyCarrier) :
    ‖thetaCuspHawkingCausalHardyPartner mode hmode r f‖ ^ (2 : ℕ) =
      thetaCuspHawkingModularPartnerNumber r *
        ‖(thetaCuspHawkingCausalHardyDefectLine mode hmode).starProjection f‖ ^ (2 : ℕ) := by
  rw [thetaCuspHawkingCausalHardyPartner_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    thetaCuspHawkingModularPartnerNumber]
  rw [mul_pow, sq_abs]

theorem thetaCuspHawkingCausalHardyExterior_energy_sub
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f : ThetaCuspHawkingHardyCarrier) :
    ‖thetaCuspHawkingCausalHardyExterior mode hmode r f‖ ^ (2 : ℕ) - ‖f‖ ^ (2 : ℕ) =
      (thetaCuspHawkingModularGain r - 1) *
        ‖(thetaCuspHawkingCausalHardyDefectLine mode hmode).starProjection f‖ ^ (2 : ℕ) := by
  have hkrein := thetaCuspHawkingCausalHardyVacuumPartner_krein mode hmode r f
  have hpartner := thetaCuspHawkingCausalHardyPartner_energy mode hmode r f
  rw [hpartner] at hkrein
  rw [thetaCuspHawkingModularPartnerNumber] at hkrein
  rw [thetaCuspHawkingModularGain]
  nlinarith [Real.cosh_sq_sub_sinh_sq r]

/-- Full two-input exterior output: identity on outgoing Hardy directions and
Lorentz/Bogoliubov mixing on the resonance defect line. -/
def thetaCuspHawkingCausalHardyFullExteriorOutput
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f h : ThetaCuspHawkingHardyCarrier) : ThetaCuspHawkingHardyCarrier :=
  thetaCuspHawkingCausalHardyExterior mode hmode r f + thetaCuspHawkingCausalHardyPartner mode hmode r h

/-- Full two-input partner output. -/
def thetaCuspHawkingCausalHardyFullPartnerOutput
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f h : ThetaCuspHawkingHardyCarrier) : ThetaCuspHawkingHardyCarrier :=
  thetaCuspHawkingCausalHardyPartner mode hmode r f + thetaCuspHawkingCausalHardyExterior mode hmode r h

private theorem thetaCuspHawkingCausalHardy_projection_exterior
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f : ThetaCuspHawkingHardyCarrier) :
    (thetaCuspHawkingCausalHardyDefectLine mode hmode).starProjection
        (thetaCuspHawkingCausalHardyExterior mode hmode r f) =
      (Real.cosh r : ℂ) •
        (thetaCuspHawkingCausalHardyDefectLine mode hmode).starProjection f := by
  let S := thetaCuspHawkingCausalHardyDefectLine mode hmode
  have hPP : S.starProjection (S.starProjection f) = S.starProjection f :=
    Submodule.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem f)
  have hPQ : S.starProjection (Sᗮ.starProjection f) = 0 :=
    S.starProjection_apply_eq_zero_iff.mpr (Sᗮ.starProjection_apply_mem f)
  rw [thetaCuspHawkingCausalHardyExterior_apply, map_add, map_smul, hPP, hPQ, add_zero]

private theorem thetaCuspHawkingCausalHardy_projection_partner
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f : ThetaCuspHawkingHardyCarrier) :
    (thetaCuspHawkingCausalHardyDefectLine mode hmode).starProjection
        (thetaCuspHawkingCausalHardyPartner mode hmode r f) =
      (Real.sinh r : ℂ) •
        (thetaCuspHawkingCausalHardyDefectLine mode hmode).starProjection f := by
  let S := thetaCuspHawkingCausalHardyDefectLine mode hmode
  have hPP : S.starProjection (S.starProjection f) = S.starProjection f :=
    Submodule.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem f)
  rw [thetaCuspHawkingCausalHardyPartner_apply, map_smul, hPP]

private theorem thetaCuspHawkingCausalHardy_orthogonalProjection_exterior
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f : ThetaCuspHawkingHardyCarrier) :
    (thetaCuspHawkingCausalHardyDefectLine mode hmode)ᗮ.starProjection
        (thetaCuspHawkingCausalHardyExterior mode hmode r f) =
      (thetaCuspHawkingCausalHardyDefectLine mode hmode)ᗮ.starProjection f := by
  let S := thetaCuspHawkingCausalHardyDefectLine mode hmode
  have hPP : S.starProjection (S.starProjection f) = S.starProjection f :=
    Submodule.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem f)
  have hsum := S.starProjection_add_starProjection_orthogonal (S.starProjection f)
  have hQP : Sᗮ.starProjection (S.starProjection f) = 0 := by
    rw [hPP] at hsum
    exact add_eq_left.mp hsum
  have hQQ : Sᗮ.starProjection (Sᗮ.starProjection f) =
      Sᗮ.starProjection f :=
    Submodule.starProjection_eq_self_iff.mpr (Sᗮ.starProjection_apply_mem f)
  rw [thetaCuspHawkingCausalHardyExterior_apply, map_add, map_smul, hQP, smul_zero, zero_add, hQQ]

private theorem thetaCuspHawkingCausalHardy_orthogonalProjection_partner
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f : ThetaCuspHawkingHardyCarrier) :
    (thetaCuspHawkingCausalHardyDefectLine mode hmode)ᗮ.starProjection
        (thetaCuspHawkingCausalHardyPartner mode hmode r f) = 0 := by
  let S := thetaCuspHawkingCausalHardyDefectLine mode hmode
  have hPP : S.starProjection (S.starProjection f) = S.starProjection f :=
    Submodule.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem f)
  have hsum := S.starProjection_add_starProjection_orthogonal (S.starProjection f)
  have hQP : Sᗮ.starProjection (S.starProjection f) = 0 := by
    rw [hPP] at hsum
    exact add_eq_left.mp hsum
  rw [thetaCuspHawkingCausalHardyPartner_apply, map_smul, hQP, smul_zero]

private theorem thetaCuspHawkingCausalHardy_projection_fullExterior
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f h : ThetaCuspHawkingHardyCarrier) :
    (thetaCuspHawkingCausalHardyDefectLine mode hmode).starProjection
        (thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode r f h) =
      (Real.cosh r : ℂ) • (thetaCuspHawkingCausalHardyDefectLine mode hmode).starProjection f +
        (Real.sinh r : ℂ) • (thetaCuspHawkingCausalHardyDefectLine mode hmode).starProjection h := by
  rw [thetaCuspHawkingCausalHardyFullExteriorOutput, map_add, thetaCuspHawkingCausalHardy_projection_exterior,
    thetaCuspHawkingCausalHardy_projection_partner]

private theorem thetaCuspHawkingCausalHardy_projection_fullPartner
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f h : ThetaCuspHawkingHardyCarrier) :
    (thetaCuspHawkingCausalHardyDefectLine mode hmode).starProjection
        (thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode r f h) =
      (Real.sinh r : ℂ) • (thetaCuspHawkingCausalHardyDefectLine mode hmode).starProjection f +
        (Real.cosh r : ℂ) • (thetaCuspHawkingCausalHardyDefectLine mode hmode).starProjection h := by
  rw [thetaCuspHawkingCausalHardyFullPartnerOutput, map_add, thetaCuspHawkingCausalHardy_projection_partner,
    thetaCuspHawkingCausalHardy_projection_exterior]

private theorem thetaCuspHawkingCausalHardy_orthogonalProjection_fullExterior
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f h : ThetaCuspHawkingHardyCarrier) :
    (thetaCuspHawkingCausalHardyDefectLine mode hmode)ᗮ.starProjection
        (thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode r f h) =
      (thetaCuspHawkingCausalHardyDefectLine mode hmode)ᗮ.starProjection f := by
  rw [thetaCuspHawkingCausalHardyFullExteriorOutput, map_add, thetaCuspHawkingCausalHardy_orthogonalProjection_exterior,
    thetaCuspHawkingCausalHardy_orthogonalProjection_partner, add_zero]

private theorem thetaCuspHawkingCausalHardy_orthogonalProjection_fullPartner
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f h : ThetaCuspHawkingHardyCarrier) :
    (thetaCuspHawkingCausalHardyDefectLine mode hmode)ᗮ.starProjection
        (thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode r f h) =
      (thetaCuspHawkingCausalHardyDefectLine mode hmode)ᗮ.starProjection h := by
  rw [thetaCuspHawkingCausalHardyFullPartnerOutput, map_add, thetaCuspHawkingCausalHardy_orthogonalProjection_partner,
    thetaCuspHawkingCausalHardy_orthogonalProjection_exterior, zero_add]

theorem thetaCuspHawkingCausalHardyFullScattering_add
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r s : ℝ) (f h : ThetaCuspHawkingHardyCarrier) :
    thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode (r + s) f h =
        thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode r
          (thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode s f h)
          (thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode s f h) ∧
      thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode (r + s) f h =
        thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode r
          (thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode s f h)
          (thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode s f h) := by
  let S := thetaCuspHawkingCausalHardyDefectLine mode hmode
  constructor
  · change
      (Real.cosh (r + s) : ℂ) • S.starProjection f +
          Sᗮ.starProjection f +
          (Real.sinh (r + s) : ℂ) • S.starProjection h =
        (Real.cosh r : ℂ) • S.starProjection
            (thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode s f h) +
          Sᗮ.starProjection (thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode s f h) +
          (Real.sinh r : ℂ) • S.starProjection
            (thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode s f h)
    rw [thetaCuspHawkingCausalHardy_orthogonalProjection_fullExterior, thetaCuspHawkingCausalHardy_projection_fullExterior,
      thetaCuspHawkingCausalHardy_projection_fullPartner]
    simp only [Real.cosh_add, Real.sinh_add]
    module
  · change
      (Real.sinh (r + s) : ℂ) • S.starProjection f +
          ((Real.cosh (r + s) : ℂ) • S.starProjection h +
            Sᗮ.starProjection h) =
        (Real.sinh r : ℂ) • S.starProjection
            (thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode s f h) +
          ((Real.cosh r : ℂ) • S.starProjection
              (thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode s f h) +
            Sᗮ.starProjection (thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode s f h))
    rw [thetaCuspHawkingCausalHardy_projection_fullExterior, thetaCuspHawkingCausalHardy_projection_fullPartner,
      thetaCuspHawkingCausalHardy_orthogonalProjection_fullPartner]
    simp only [Real.cosh_add, Real.sinh_add]
    module

theorem thetaCuspHawkingCausalHardyFullScattering_zero
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (f h : ThetaCuspHawkingHardyCarrier) :
    thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode 0 f h = f ∧
      thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode 0 f h = h := by
  constructor <;>
    simp [thetaCuspHawkingCausalHardyFullExteriorOutput, thetaCuspHawkingCausalHardyFullPartnerOutput, thetaCuspHawkingCausalHardyExterior_apply,
      thetaCuspHawkingCausalHardyPartner_apply, add_comm]

theorem thetaCuspHawkingCausalHardyFullScattering_inverse
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f h : ThetaCuspHawkingHardyCarrier) :
    thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode (-r)
        (thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode r f h)
        (thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode r f h) = f ∧
      thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode (-r)
        (thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode r f h)
        (thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode r f h) = h := by
  have hadd := thetaCuspHawkingCausalHardyFullScattering_add mode hmode (-r) r f h
  have hcomp :
      thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode 0 f h =
          thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode (-r)
            (thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode r f h)
            (thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode r f h) ∧
        thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode 0 f h =
          thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode (-r)
            (thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode r f h)
            (thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode r f h) := by
    simpa using hadd
  have hzero := thetaCuspHawkingCausalHardyFullScattering_zero mode hmode f h
  exact ⟨hcomp.1.symm.trans hzero.1, hcomp.2.symm.trans hzero.2⟩

private theorem thetaCuspHawkingCausalHardy_lorentzNorm
    (r : ℝ) (p h : ThetaCuspHawkingHardyCarrier) :
    ‖(Real.cosh r : ℂ) • p + (Real.sinh r : ℂ) • h‖ ^ (2 : ℕ) -
        ‖(Real.sinh r : ℂ) • p + (Real.cosh r : ℂ) • h‖ ^ (2 : ℕ) =
      ‖p‖ ^ (2 : ℕ) - ‖h‖ ^ (2 : ℕ) := by
  rw [norm_add_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ)]
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [abs_of_pos (Real.cosh_pos r)]
  have hsinh : |Real.sinh r| ^ (2 : ℕ) = Real.sinh r ^ (2 : ℕ) := sq_abs _
  simp only [mul_pow]
  rw [hsinh]
  have hcross :
      RCLike.re ((Real.sinh r : ℂ) *
          ((Real.cosh r : ℂ) * inner ℂ p h)) =
        RCLike.re ((Real.cosh r : ℂ) *
          ((Real.sinh r : ℂ) * inner ℂ p h)) := by
    congr 1
    ring
  rw [hcross]
  nlinarith [Real.cosh_sq_sub_sinh_sq r]

theorem thetaCuspHawkingCausalHardyFullScattering_krein
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r : ℝ) (f h : ThetaCuspHawkingHardyCarrier) :
    ‖thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode r f h‖ ^ (2 : ℕ) -
        ‖thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode r f h‖ ^ (2 : ℕ) =
      ‖f‖ ^ (2 : ℕ) - ‖h‖ ^ (2 : ℕ) := by
  let S := thetaCuspHawkingCausalHardyDefectLine mode hmode
  let pf := S.starProjection f
  let ph := S.starProjection h
  let qf := Sᗮ.starProjection f
  let qh := Sᗮ.starProjection h
  let de := (Real.cosh r : ℂ) • pf + (Real.sinh r : ℂ) • ph
  let dh := (Real.sinh r : ℂ) • pf + (Real.cosh r : ℂ) • ph
  have hdeS : de ∈ S := S.add_mem
    (S.smul_mem _ (S.starProjection_apply_mem f))
    (S.smul_mem _ (S.starProjection_apply_mem h))
  have hdhS : dh ∈ S := S.add_mem
    (S.smul_mem _ (S.starProjection_apply_mem f))
    (S.smul_mem _ (S.starProjection_apply_mem h))
  have hqfS : qf ∈ Sᗮ := Sᗮ.starProjection_apply_mem f
  have hqhS : qh ∈ Sᗮ := Sᗮ.starProjection_apply_mem h
  have horthE : (inner ℂ de qf : ℂ) = 0 :=
    (Submodule.mem_orthogonal S qf).mp hqfS de hdeS
  have horthH : (inner ℂ dh qh : ℂ) = 0 :=
    (Submodule.mem_orthogonal S qh).mp hqhS dh hdhS
  have houtE : thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode r f h = de + qf := by
    rw [thetaCuspHawkingCausalHardyFullExteriorOutput, thetaCuspHawkingCausalHardyExterior_apply, thetaCuspHawkingCausalHardyPartner_apply]
    dsimp only [S, pf, ph, qf, de]
    module
  have houtH : thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode r f h = dh + qh := by
    rw [thetaCuspHawkingCausalHardyFullPartnerOutput, thetaCuspHawkingCausalHardyPartner_apply, thetaCuspHawkingCausalHardyExterior_apply]
    dsimp only [S, pf, ph, qh, dh]
    module
  have hnormE : ‖thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode r f h‖ ^ (2 : ℕ) =
      ‖de‖ ^ (2 : ℕ) + ‖qf‖ ^ (2 : ℕ) := by
    rw [houtE]
    simpa only [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero de qf horthE
  have hnormH : ‖thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode r f h‖ ^ (2 : ℕ) =
      ‖dh‖ ^ (2 : ℕ) + ‖qh‖ ^ (2 : ℕ) := by
    rw [houtH]
    simpa only [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero dh qh horthH
  have hsplitF : ‖f‖ ^ (2 : ℕ) = ‖pf‖ ^ (2 : ℕ) + ‖qf‖ ^ (2 : ℕ) := by
    simpa only [pf, qf] using Submodule.norm_sq_eq_add_norm_sq_starProjection f S
  have hsplitH : ‖h‖ ^ (2 : ℕ) = ‖ph‖ ^ (2 : ℕ) + ‖qh‖ ^ (2 : ℕ) := by
    simpa only [ph, qh] using Submodule.norm_sq_eq_add_norm_sq_starProjection h S
  have hdefect := thetaCuspHawkingCausalHardy_lorentzNorm r pf ph
  rw [hnormE, hnormH]
  linarith

/-- Squared-Euler response produced by stimulating the mode reconstructed
from the actual causal Hardy defect. -/
def thetaCuspHawkingCausalHardyStimulatedKernel
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im) (r x y : ℝ) : ℝ :=
  xiSquaredEulerFullKernel x y +
    (thetaCuspHawkingModularGain r - 1) *
      thetaCuspHawkingCausalHardyOrbitKernel mode hmode x y

theorem thetaCuspHawkingCausalHardyStimulatedKernel_eq_selectiveModularGainKernel
    (q : XiZeroCopy) (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im)
    (horient : mode = thetaCuspHawkingXiOrbitResonantMode q ∨
      mode = thetaCuspHawkingBackreactionReflectedResonantMode
        (thetaCuspHawkingXiOrbitResonantMode q))
    (r : ℝ) :
    thetaCuspHawkingCausalHardyStimulatedKernel mode hmode r =
      thetaCuspHawkingSelectiveModularGainKernel q r := by
  funext x y
  rw [thetaCuspHawkingCausalHardyStimulatedKernel, thetaCuspHawkingSelectiveModularGainKernel,
    xiSquaredEulerReweightedFullKernel,
    thetaCuspHawkingCausalHardyOrbitKernel_eq_xiSquaredEulerOrbitKernel q mode hmode horient]

theorem exists_thetaCuspHawkingCausalHardyDefect_fullScattering_eventually_negative
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    ∃ (mode : ThetaCuspHawkingBackreactionResonantMode)
        (hmode : 0 < mode.1.im),
      (mode = thetaCuspHawkingXiOrbitResonantMode q ∨
          mode = thetaCuspHawkingBackreactionReflectedResonantMode
            (thetaCuspHawkingXiOrbitResonantMode q)) ∧
        Module.finrank ℂ ((thetaCuspHawkingCausalHardyRange mode hmode)ᗮ) = 1 ∧
        thetaCuspHawkingCausalHardyOrbitKernel mode hmode = xiSquaredEulerOrbitKernel q ∧
        (∀ r : ℝ, ∀ f h : ThetaCuspHawkingHardyCarrier,
          ‖thetaCuspHawkingCausalHardyFullExteriorOutput mode hmode r f h‖ ^ (2 : ℕ) -
            ‖thetaCuspHawkingCausalHardyFullPartnerOutput mode hmode r f h‖ ^ (2 : ℕ) =
              ‖f‖ ^ (2 : ℕ) - ‖h‖ ^ (2 : ℕ)) ∧
        ∃ R : ℝ, ∀ r : ℝ, R ≤ r →
          symmetricThreePointDet (thetaCuspHawkingCausalHardyStimulatedKernel mode hmode r) x y z < 0 := by
  obtain ⟨mode, hmode, horient⟩ :=
    exists_upper_thetaCuspHawkingXiOrbitResonantMode q hoff
  refine ⟨mode, hmode, horient,
    finrank_thetaCuspHawkingCausalHardyDefect_eq_one mode hmode,
    thetaCuspHawkingCausalHardyOrbitKernel_eq_xiSquaredEulerOrbitKernel q mode hmode horient,
    thetaCuspHawkingCausalHardyFullScattering_krein mode hmode, ?_⟩
  obtain ⟨R, hR⟩ :=
    exists_eventually_negative_thetaCuspHawkingSelectiveModularGainKernel_threePointDet
      q hoff hx hxy hyz
  refine ⟨R, ?_⟩
  intro r hr
  rw [thetaCuspHawkingCausalHardyStimulatedKernel_eq_selectiveModularGainKernel q mode hmode horient r]
  exact hR r hr

/-- Every upper theta-Hawking Hardy defect remains three-shell stable under
its canonical source-reconstructed modular dilation. -/
def ThetaCuspHawkingCausalHardyDefectStimulatedCubicStable : Prop :=
  ∀ (mode : ThetaCuspHawkingBackreactionResonantMode)
      (hmode : 0 < mode.1.im) (x y z r : ℝ),
    0 < x → x < y → y < z →
      0 ≤ symmetricThreePointDet (thetaCuspHawkingCausalHardyStimulatedKernel mode hmode r) x y z

theorem thetaCuspHawkingCausalHardyDefectStimulatedCubicStable_iff_riemannHypothesis : ThetaCuspHawkingCausalHardyDefectStimulatedCubicStable ↔ RiemannHypothesis := by
  constructor
  · intro hstable
    apply xiSquaredEulerAllOrbitChargeDensitiesVanish_iff_riemannHypothesis.1
    intro q
    apply (xiSquaredEulerApertureOrbitChargeDensity_eq_zero_iff q).2
    by_contra hoff
    obtain ⟨mode, hmode, _horient, _hrank, _hkernel, _hkrein, R, hR⟩ :=
      exists_thetaCuspHawkingCausalHardyDefect_fullScattering_eventually_negative q hoff
        (x := 1) (y := 2) (z := 3)
        (by norm_num) (by norm_num) (by norm_num)
    have hneg := hR R le_rfl
    have hnonneg := hstable mode hmode 1 2 3 R
      (by norm_num) (by norm_num) (by norm_num)
    linarith
  · intro hRH mode hmode
    have hreal :=
      (riemannHypothesis_iff_XiC_zeros_real.mp hRH) mode.1
        (thetaCuspHawkingBackreactionResonantMode_XiC_eq_zero mode)
    exfalso
    linarith

end RHTower
