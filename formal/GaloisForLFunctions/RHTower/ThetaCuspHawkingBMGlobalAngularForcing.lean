import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularCuspBounds
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuadraticMixedCurrent
import GaloisForLFunctions.HTGeometry.ModularFundamentalDomainVolume
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.L2Space

/-!
The full squared scalar source admits an actual cusp-subtracted forcing vector in the invariant modular L² space. The original mixed-source amplitude, both Weyl powers, every Fourier mode, and all cutoff derivatives are retained.
-/

open Complex Real Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMGlobalAngularResponse
open D4BMAngularSeries
noncomputable section

/-- The full literal scalar field, including both Weyl terms and every Fourier mode. -/
def scalar (u : ℂ) (z : Fin 2 → ℝ) : ℂ :=
  d4BMCompletedEisensteinCuspLeg .scalar u (z 0) (z 1)

/-- The full two-term cusp principal part. -/
def principal (u : ℂ) (z : Fin 2 → ℝ) : ℂ :=
  d4BMCompletedEisensteinCuspConstantPart .scalar u (z 1)

/-- All nonconstant modes, with the original normalization. -/
def tail (u : ℂ) (z : Fin 2 → ℝ) : ℂ :=
  d4BMCompletedEisensteinCuspTailPart .scalar u (z 0) (z 1)

/-- Every tail and cross term left after subtracting the full squared principal part. -/
def squareRemainder (u : ℂ) (z : Fin 2 → ℝ) : ℂ :=
  scalar u z ^ 2 - principal u z ^ 2

/-- Uniform bound on an arbitrary complex-power-weighted full signed scalar tail. -/
theorem weighted_tail_bounded (u w : ℂ) (l : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l ≤ z 1 → ‖(z 1 : ℂ)^w * tail u z‖ ≤ C := by
  obtain ⟨C0,hC0,h0⟩ := weighted_value_bounded u u w (1/2) 0 false l hl
  obtain ⟨C1,hC1,h1⟩ := weighted_value_bounded u u w (1/2) 0 true l hl
  refine ⟨2*(C0+C1), by positivity, ?_⟩
  intro z hz
  have hy := hl.trans_le hz
  have he : (z 1 : ℂ)^w * tail u z = 2*((z 1 : ℂ)^w*value u u (1/2) 0 false z +
      (z 1 : ℂ)^w*value u u (1/2) 0 true z) := by
    simp only [tail, d4BMCompletedEisensteinCuspTailPart,
      d4BMCompletedEisensteinFullSignedZeroWord, signedTail_eq_value _ _ _ _ _ z hy,
      Nat.cast_zero, zero_add]
    ring
  rw [he, norm_mul]
  norm_num only [Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (h0 z hz) (h1 z hz)))
    (by norm_num)

/-- Exact remainder expansion keeps the constant--tail and tail--tail interactions. -/
theorem squareRemainder_eq (u : ℂ) (z : Fin 2 → ℝ) :
    squareRemainder u z = 2*(principal u z*tail u z) + tail u z^2 := by
  dsimp [squareRemainder, scalar, principal, tail, d4BMCompletedEisensteinCuspLeg]
  ring

/-- The full squared-source remainder is bounded on every positive-height half-strip,
with a bound independent of the horizontal coordinate. -/
theorem squareRemainder_bounded (u : ℂ) (l : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l ≤ z 1 → ‖squareRemainder u z‖ ≤ C := by
  obtain ⟨C0,hC0,h0⟩ := weighted_tail_bounded u 0 l hl
  obtain ⟨Cm,hCm,hm⟩ := weighted_tail_bounded u (d4BMCompletedEisensteinCuspWeylExponent u false) l hl
  obtain ⟨Cp,hCp,hp⟩ := weighted_tail_bounded u (d4BMCompletedEisensteinCuspWeylExponent u true) l hl
  let A := d4BMCompletedEisensteinCuspConstantCoefficient u false
  let D := d4BMCompletedEisensteinCuspConstantCoefficient u true
  refine ⟨2*(‖A‖*Cm+‖D‖*Cp)+C0^2, by positivity, ?_⟩
  intro z hz
  have ht : ‖tail u z‖ ≤ C0 := by simpa only [Complex.cpow_zero, one_mul] using h0 z hz
  have hcross : ‖principal u z*tail u z‖ ≤ ‖A‖*Cm+‖D‖*Cp := by
    have he : principal u z*tail u z =
        A*((z 1 : ℂ)^(d4BMCompletedEisensteinCuspWeylExponent u false)*tail u z) +
        D*((z 1 : ℂ)^(d4BMCompletedEisensteinCuspWeylExponent u true)*tail u z) := by
      dsimp [principal, d4BMCompletedEisensteinCuspConstantPart,
        d4BMCompletedEisensteinCuspConstantTerm, d4BMCompletedEisensteinCuspConstantMaassFactor, A,D]
      ring
    rw [he]
    calc
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by rw [norm_mul A, norm_mul D]; gcongr; exacts [hm z hz,hp z hz]
  rw [squareRemainder_eq]
  calc
    _ ≤ ‖2*(principal u z*tail u z)‖ + ‖tail u z^2‖ := norm_add_le _ _
    _ = 2*‖principal u z*tail u z‖ + ‖tail u z‖^2 := by rw [norm_mul,norm_pow]; norm_num
    _ ≤ _ := by gcongr

end
end RHTower.D4BMGlobalAngularResponse


open Complex Real Set Filter Topology MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMGlobalAngularResponse
open D4BMAngularSeries D4BMQuadraticMixedSource
noncomputable section

/-- Centered angular parameter of the actual Xi occurrence. -/
def center (q : XiZeroCopy) : ℂ := (q.1 : ℂ)-1/2

/-- The actual doubled-rate angular parameter on either physical branch. -/
def parameter (q : XiZeroCopy) (minusBranch : Bool) : ℂ :=
  branchParameter (q.1 : ℂ) minusBranch

/-- The complete principal-part response with its actual mixed-source amplitude. -/
def cuspResponse (q : XiZeroCopy) (minusBranch : Bool) (z : Fin 2 → ℝ) : ℂ :=
  (parameter q minusBranch/2)*cuspPowerResponse (parameter q minusBranch) (q.1 : ℂ)
    (d4BMCompletedEisensteinCuspConstantCoefficient (center q) true)
    (d4BMCompletedEisensteinCuspConstantCoefficient (center q) false) z

/-- Smooth cusp cutoff, zero below height two and one above height three. -/
def cutoff (z : Fin 2 → ℝ) : ℂ := Real.smoothTransition (z 1-2)

/-- The explicit response cut off away from the modular seams. -/
def cutoffResponse (q : XiZeroCopy) (minusBranch : Bool) (z : Fin 2 → ℝ) : ℂ :=
  cutoff z*cuspResponse q minusBranch z

/-- The literal full forcing remaining after the cutoff response; all cutoff derivatives
remain in the actual hyperbolic differential expression. -/
def forcing (q : XiZeroCopy) (minusBranch : Bool) (z : Fin 2 → ℝ) : ℂ :=
  (parameter q minusBranch/2)*scalar (center q) z^2 -
    (hyperbolicLaplacian (cutoffResponse q minusBranch) z -
      parameter q minusBranch*cutoffResponse q minusBranch z)

private theorem principal_center (q : XiZeroCopy) (z : Fin 2 → ℝ) :
    principal (center q) z =
      d4BMCompletedEisensteinCuspConstantCoefficient (center q) true*(z 1 : ℂ)^(q.1 : ℂ) +
      d4BMCompletedEisensteinCuspConstantCoefficient (center q) false*(z 1 : ℂ)^(1-(q.1 : ℂ)) := by
  have hm : d4BMCompletedEisensteinCuspWeylExponent (center q) false = 1-(q.1 : ℂ) := by
    norm_num [d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign, center]
    ring
  have hp : d4BMCompletedEisensteinCuspWeylExponent (center q) true = (q.1 : ℂ) := by
    norm_num [d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign, center]
  simp only [principal, d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm, d4BMCompletedEisensteinCuspConstantMaassFactor,
    mul_one, hm,hp]
  exact add_comm _ _

/-- The explicit cusp response has exactly the original full principal-part forcing. -/
theorem cuspResponse_equation (q : XiZeroCopy) (minusBranch : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    hyperbolicLaplacian (cuspResponse q minusBranch) z -
      parameter q minusBranch*cuspResponse q minusBranch z =
      (parameter q minusBranch/2)*principal (center q) z^2 := by
  rw [principal_center]
  exact xi_forced_cusp_response_equation q minusBranch (parameter q minusBranch/2)
    (d4BMCompletedEisensteinCuspConstantCoefficient (center q) true)
    (d4BMCompletedEisensteinCuspConstantCoefficient (center q) false) z hz

private theorem cuspResponse_smooth (q : XiZeroCopy) (minusBranch : Bool) :
    ContDiffOn ℝ ∞ (cuspResponse q minusBranch) domain := by
  unfold cuspResponse cuspPowerResponse powerResponse
  exact contDiffOn_const.mul (((contDiffOn_const.mul (height_cpow_contDiffOn _ ∞)).add
    (contDiffOn_const.mul (height_cpow_contDiffOn _ ∞))).add
    (contDiffOn_const.mul (height_cpow_contDiffOn _ ∞)))

private theorem cutoff_smooth : ContDiff ℝ ∞ cutoff := by
  let Y : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  exact Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
    (Y.contDiff.sub contDiff_const))

private theorem cutoffResponse_smooth (q : XiZeroCopy) (minusBranch : Bool) :
    ContDiffOn ℝ ∞ (cutoffResponse q minusBranch) domain :=
  cutoff_smooth.contDiffOn.mul (cuspResponse_smooth q minusBranch)

private theorem laplacian_continuous {f : (Fin 2 → ℝ) → ℂ}
    (hf : ContDiffOn ℝ 2 f domain) : ContinuousOn (hyperbolicLaplacian f) domain := by
  intro z hz
  have hfo : ContDiffAt ℝ 2 f z := hf.contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)
  have hd (i : Fin 2) : ContDiffAt ℝ 1 (coordDeriv i f) z :=
    (hfo.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hdd (i : Fin 2) : ContinuousAt (coordDeriv i (coordDeriv i f)) z :=
    (((hd i).fderiv_right (show (0 : WithTop ℕ∞)+1 ≤ 1 by norm_num)).clm_apply
      contDiffAt_const).continuousAt
  exact (((Complex.ofRealCLM.continuous.continuousAt.comp (continuous_apply 1).continuousAt).pow 2).mul
    ((hdd 0).add (hdd 1))).continuousWithinAt

/-- The full residual is continuous on the whole positive-height chart. -/
theorem forcing_continuousOn (q : XiZeroCopy) (minusBranch : Bool) :
    ContinuousOn (forcing q minusBranch) domain := by
  have hr := cutoffResponse_smooth q minusBranch
  have hl := laplacian_continuous ((contDiffOn_infty.mp hr) 2)
  exact (continuousOn_const.mul ((cuspLeg_contDiffOn .scalar (center q)).continuousOn.pow 2)).sub
    (hl.sub (continuousOn_const.mul hr.continuousOn))

/-- The cutoff response vanishes on a neighborhood of the entire compact modular seam. -/
theorem cutoffResponse_zero (q : XiZeroCopy) (minusBranch : Bool)
    (z : Fin 2 → ℝ) (hz : z 1 ≤ 2) : cutoffResponse q minusBranch z = 0 := by
  unfold cutoffResponse cutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  simp

/-- Above the transition region, the actual residual is precisely the full squared-source
remainder, with the physical forcing amplitude retained. -/
theorem forcing_high (q : XiZeroCopy) (minusBranch : Bool)
    (z : Fin 2 → ℝ) (hz : 3 < z 1) :
    forcing q minusBranch z = (parameter q minusBranch/2)*squareRemainder (center q) z := by
  have he : cutoffResponse q minusBranch =ᶠ[𝓝 z] cuspResponse q minusBranch := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    unfold cutoffResponse cutoff
    rw [Real.smoothTransition.one_of_one_le (by linarith)]
    simp
  rw [forcing, hyperbolicLaplacian_congr he, he.eq_of_nhds,
    cuspResponse_equation q minusBranch z (by linarith)]
  dsimp [squareRemainder]
  ring

/-- The original positive-height coordinate chart on the upper half-plane. -/
def coordinates (z : UpperHalfPlane) : Fin 2 → ℝ := ![z.re,z.im]

private theorem coordinates_continuous : Continuous coordinates := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact UpperHalfPlane.continuous_re
  · exact UpperHalfPlane.continuous_im

/-- The actual invariant measure on the standard modular cell. -/
def angularMeasure : Measure UpperHalfPlane := volume.restrict ModularGroup.fd

instance : IsFiniteMeasure angularMeasure :=
  isFiniteMeasure_restrict.mpr volume_fd_ne_top

/-- The full residual is bounded on the entire standard modular cell, including its cusp. -/
theorem forcing_bounded (q : XiZeroCopy) (minusBranch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, z ∈ ModularGroup.fd →
      ‖forcing q minusBranch (coordinates z)‖ ≤ C := by
  obtain ⟨B,hB,hb⟩ := squareRemainder_bounded (center q) (1/2) (by norm_num)
  let lo : Fin 2 → ℝ := ![-1/2,1/2]
  let hi : Fin 2 → ℝ := ![1/2,4]
  have hc : ContinuousOn (forcing q minusBranch) (Icc lo hi) :=
    (forcing_continuousOn q minusBranch).mono (by
      intro z hz
      have hh := hz.1 1
      change (1/2 : ℝ) ≤ z 1 at hh
      change 0 < z 1
      linarith)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C (‖parameter q minusBranch/2‖*B),
    le_trans (mul_nonneg (norm_nonneg _) hB) (le_max_right _ _), ?_⟩
  intro z hz
  have hre := abs_le.mp hz.2
  have hsq := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have him : (1/2 : ℝ) ≤ z.im := by nlinarith [z.im_pos]
  by_cases hh : 4 ≤ z.im
  · rw [forcing_high q minusBranch (coordinates z) (by change 3 < z.im; linarith),norm_mul]
    exact (mul_le_mul_of_nonneg_left (hb (coordinates z) him) (norm_nonneg _)).trans (le_max_right _ _)
  · apply (hC (coordinates z) ?_).trans (le_max_left _ _)
    constructor
    · intro i
      fin_cases i
      · simpa [lo, coordinates, neg_div] using hre.1
      · exact him
    · intro i
      fin_cases i
      · exact hre.2
      · exact le_of_not_ge hh

/-- The entire physical residual belongs to the actual modular hyperbolic L² space,
for every Xi occurrence and both physical branches, without a spectral-location hypothesis. -/
theorem forcing_memLp (q : XiZeroCopy) (minusBranch : Bool) :
    MemLp (fun z : UpperHalfPlane => forcing q minusBranch (coordinates z)) 2 angularMeasure := by
  have hc : Continuous (fun z : UpperHalfPlane => forcing q minusBranch (coordinates z)) :=
    (forcing_continuousOn q minusBranch).comp_continuous coordinates_continuous
      (fun z => z.im_pos)
  obtain ⟨C,_,hC⟩ := forcing_bounded q minusBranch
  apply MemLp.of_bound hc.aestronglyMeasurable C
  exact (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet).mono hC

/-- The admitted full forcing as a vector in the actual angular Hilbert space. -/
def forcingVector (q : XiZeroCopy) (minusBranch : Bool) : Lp ℂ 2 angularMeasure :=
  (forcing_memLp q minusBranch).toLp (fun z => forcing q minusBranch (coordinates z))

/-- The Hilbert-space vector retains the original full differential residual almost everywhere. -/
theorem forcingVector_coe (q : XiZeroCopy) (minusBranch : Bool) :
    (forcingVector q minusBranch : UpperHalfPlane → ℂ) =ᵐ[angularMeasure]
      (fun z => forcing q minusBranch (coordinates z)) :=
  (forcing_memLp q minusBranch).coeFn_toLp

end
end RHTower.D4BMGlobalAngularResponse
