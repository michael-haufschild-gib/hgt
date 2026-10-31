import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalSmoothForcing
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalCuspCutoff

/-!
# Spectral Eisenstein forcing for PW-B

The PW-B source at a Xi zero copy `q` is built from the completed Eisenstein series at the
location `q.1`; its construction uses only `0 < Re q.1 < 1` and `Im q.1 ≠ 0`. This module
constructs the same cusp-subtracted squared-Eisenstein forcing, its modular `L²` vector and
its globally smooth modular gluing at every point `s` of the nonreal open strip, a domain
defined without reference to Xi. At every zero copy the constructions are definitionally the
zero-indexed ones.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped MatrixGroups ContDiff

namespace RHTower.PWBSpectralSource
open D4BMAngularSeries D4BMQuadraticMixedSource
open D4BMGlobalAngularResponse (scalar tail squareRemainder squareRemainder_bounded
  cutoff coordinates angularMeasure clearedScalar clearedScalar_eq clearedScalar_invert
  clearFactor)
open D4BMModularCore (ChartSmooth CellGermCompatible cellGermExtension cellGermExtension_eq
  cellGermExtension_invariant cellGermExtension_germ cellGermExtension_smooth
  nonparabolic_cell_overlap_low globalLift globalLift_invariant globalLift_ae_eq Space
  ChartSmooth.modular_pullback measure ae_mem_interior)

noncomputable section
set_option autoImplicit false

/-! ## The zero-independent spectral domain -/

/-- Nonreal points of the open critical strip; the definition mentions no Xi zero. -/
abbrev SpectralSite := {s : ℂ // 0 < s.re ∧ s.re < 1 ∧ s.im ≠ 0}

/-- The location of a Xi zero copy, as a spectral site. -/
def site (q : XiZeroCopy) : SpectralSite :=
  ⟨(q.1 : ℂ), (xi_divisor_support_re_mem_open_unit q.1).1,
    (xi_divisor_support_re_mem_open_unit q.1).2, xi_divisor_support_im_ne_zero q.1⟩

@[simp] theorem site_val (q : XiZeroCopy) : (site q).1 = (q.1 : ℂ) := rfl

/-! ## Spectral parameters and the explicit cusp response -/

/-- Centered Eisenstein parameter. -/
def center (s : SpectralSite) : ℂ := s.1 - 1/2

/-- Doubled-rate angular parameter on either physical branch. -/
def parameter (s : SpectralSite) (minusBranch : Bool) : ℂ := branchParameter s.1 minusBranch

/-- Both physical angular parameters are nonreal on the whole spectral domain. -/
theorem parameter_im_ne_zero (s : SpectralSite) (minusBranch : Bool) :
    (parameter s minusBranch).im ≠ 0 := by
  have hp := physical_parameter_im s.1
  obtain ⟨h0, h1, hi⟩ := s.2
  cases minusBranch
  · change (resolventParameter (-s.1-1)).im ≠ 0
    rw [hp.2]
    exact mul_ne_zero (by intro h; linarith) hi
  · change (resolventParameter (s.1-2)).im ≠ 0
    rw [hp.1]
    exact mul_ne_zero (by intro h; linarith) hi

/-- No power of the squared cusp principal part is resonant. -/
theorem cusp_denominators (s : SpectralSite) (minusBranch : Bool) :
    (2*s.1)*(2*s.1-1)-parameter s minusBranch ≠ 0 ∧ -parameter s minusBranch ≠ 0 ∧
    (2-2*s.1)*(1-2*s.1)-parameter s minusBranch ≠ 0 := by
  have hi := s.2.2.2
  have hparam := parameter_im_ne_zero s minusBranch
  have hm : -parameter s minusBranch ≠ 0 := by
    apply neg_ne_zero.mpr
    intro h
    apply hparam
    rw [h]
    rfl
  refine ⟨?_, hm, ?_⟩ <;> intro h <;> apply hi
  all_goals have hc := congrArg Complex.im h
  all_goals cases minusBranch <;>
    norm_num [parameter, branchParameter, resolventParameter, Complex.mul_re,
      Complex.mul_im] at hc <;>
    nlinarith

/-- The complete principal-part response with its mixed-source amplitude. -/
def cuspResponse (s : SpectralSite) (minusBranch : Bool) (z : Fin 2 → ℝ) : ℂ :=
  (parameter s minusBranch/2)*cuspPowerResponse (parameter s minusBranch) s.1
    (d4BMCompletedEisensteinCuspConstantCoefficient (center s) true)
    (d4BMCompletedEisensteinCuspConstantCoefficient (center s) false) z

/-- The explicit cusp response cut off away from the modular seams. -/
def cutoffResponse (s : SpectralSite) (minusBranch : Bool) (z : Fin 2 → ℝ) : ℂ :=
  cutoff z*cuspResponse s minusBranch z

/-- The cusp-subtracted squared Eisenstein forcing, with every cutoff derivative retained. -/
def forcing (s : SpectralSite) (minusBranch : Bool) (z : Fin 2 → ℝ) : ℂ :=
  (parameter s minusBranch/2)*scalar (center s) z^(2 : ℕ) -
    (hyperbolicLaplacian (cutoffResponse s minusBranch) z -
      parameter s minusBranch*cutoffResponse s minusBranch z)

@[simp] theorem center_site (q : XiZeroCopy) :
    center (site q) = D4BMGlobalAngularResponse.center q := rfl

@[simp] theorem parameter_site (q : XiZeroCopy) (b : Bool) :
    parameter (site q) b = D4BMGlobalAngularResponse.parameter q b := rfl

@[simp] theorem forcing_site (q : XiZeroCopy) (b : Bool) :
    forcing (site q) b = D4BMGlobalAngularResponse.forcing q b := rfl

private theorem principal_center (s : SpectralSite) (z : Fin 2 → ℝ) :
    D4BMGlobalAngularResponse.principal (center s) z =
      d4BMCompletedEisensteinCuspConstantCoefficient (center s) true*(z 1 : ℂ)^s.1 +
      d4BMCompletedEisensteinCuspConstantCoefficient (center s) false*(z 1 : ℂ)^(1-s.1) := by
  have hm : d4BMCompletedEisensteinCuspWeylExponent (center s) false = 1-s.1 := by
    norm_num [d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign, center]
    ring
  have hp : d4BMCompletedEisensteinCuspWeylExponent (center s) true = s.1 := by
    norm_num [d4BMCompletedEisensteinCuspWeylExponent, d4BMCuspSign, center]
  simp only [D4BMGlobalAngularResponse.principal, d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm, d4BMCompletedEisensteinCuspConstantMaassFactor,
    mul_one, hm, hp]
  exact add_comm _ _

private theorem powerResponse_smooth (lambda p A : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    ContDiffAt ℝ 2 (powerResponse lambda p A) z :=
  contDiffAt_const.mul ((height_cpow_contDiffOn p 2).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz))

/-- The explicit cusp response has exactly the full principal-part forcing. -/
theorem cuspResponse_equation (s : SpectralSite) (minusBranch : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    hyperbolicLaplacian (cuspResponse s minusBranch) z -
      parameter s minusBranch*cuspResponse s minusBranch z =
      (parameter s minusBranch/2)*D4BMGlobalAngularResponse.principal (center s) z^(2 : ℕ) := by
  rw [principal_center]
  obtain ⟨h0, h1, h2⟩ := cusp_denominators s minusBranch
  set L := parameter s minusBranch
  set A := d4BMCompletedEisensteinCuspConstantCoefficient (center s) true
  set D := d4BMCompletedEisensteinCuspConstantCoefficient (center s) false
  have hp := ((powerResponse_smooth L (2*s.1) (A^(2 : ℕ)) z hz).add
    (powerResponse_smooth L 1 (2*A*D) z hz)).add
    (powerResponse_smooth L (2-2*s.1) (D^(2 : ℕ)) z hz)
  change ContDiffAt ℝ 2 (cuspPowerResponse L s.1 A D) z at hp
  have hf : cuspResponse s minusBranch = fun w => (L/2)*cuspPowerResponse L s.1 A D w := rfl
  have he := cusp_response_equation L s.1 A D z hz h0 h1 h2
  rw [hf, hyperbolicLaplacian_const_mul hp]
  linear_combination (L/2)*he

/-! ## Continuity, boundedness and the modular `L²` vector -/

private theorem cuspResponse_smooth (s : SpectralSite) (minusBranch : Bool) :
    ContDiffOn ℝ ∞ (cuspResponse s minusBranch) domain := by
  unfold cuspResponse cuspPowerResponse powerResponse
  exact contDiffOn_const.mul (((contDiffOn_const.mul (height_cpow_contDiffOn _ ∞)).add
    (contDiffOn_const.mul (height_cpow_contDiffOn _ ∞))).add
    (contDiffOn_const.mul (height_cpow_contDiffOn _ ∞)))

private theorem cutoff_smooth : ContDiff ℝ ∞ cutoff := by
  let Y : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  exact Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
    (Y.contDiff.sub contDiff_const))

/-- The cut-off cusp response is smooth throughout positive height. -/
theorem cutoffResponse_contDiffOn (s : SpectralSite) (minusBranch : Bool) :
    ContDiffOn ℝ ∞ (cutoffResponse s minusBranch) domain :=
  cutoff_smooth.contDiffOn.mul (cuspResponse_smooth s minusBranch)

/-- The full forcing is smooth to every spatial order. -/
theorem forcing_contDiffOn (s : SpectralSite) (minusBranch : Bool) :
    ContDiffOn ℝ ∞ (forcing s minusBranch) domain := by
  have hr := cutoffResponse_contDiffOn s minusBranch
  have hl : ContDiffOn ℝ ∞ (hyperbolicLaplacian (cutoffResponse s minusBranch)) domain := by
    intro z hz
    have hf := hr.contDiffAt ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)
    have hd (i : Fin 2) : ContDiffAt ℝ ∞ (coordDeriv i (cutoffResponse s minusBranch)) z :=
      (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
    have hdd (i : Fin 2) : ContDiffAt ℝ ∞
        (coordDeriv i (coordDeriv i (cutoffResponse s minusBranch))) z :=
      ((hd i).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
    let Y : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
    have hy : ContDiffAt ℝ ∞ (fun x : Fin 2 → ℝ => (x 1 : ℂ)) z :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp z Y.contDiff.contDiffAt
    exact ((hy.pow 2).mul ((hdd 0).add (hdd 1))).contDiffWithinAt
  exact (contDiffOn_const.mul ((cuspLeg_contDiffOn .scalar (center s)).pow 2)).sub
    (hl.sub (contDiffOn_const.mul hr))

/-- The cutoff response vanishes below height two. -/
theorem cutoffResponse_zero (s : SpectralSite) (minusBranch : Bool)
    (z : Fin 2 → ℝ) (hz : z 1 ≤ 2) : cutoffResponse s minusBranch z = 0 := by
  unfold cutoffResponse cutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  simp

/-- Above height three the forcing is the squared-source remainder. -/
theorem forcing_high (s : SpectralSite) (minusBranch : Bool)
    (z : Fin 2 → ℝ) (hz : 3 < z 1) :
    forcing s minusBranch z = (parameter s minusBranch/2)*squareRemainder (center s) z := by
  have he : cutoffResponse s minusBranch =ᶠ[𝓝 z] cuspResponse s minusBranch := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    unfold cutoffResponse cutoff
    rw [Real.smoothTransition.one_of_one_le (by linarith)]
    simp
  rw [forcing, hyperbolicLaplacian_congr he, he.eq_of_nhds,
    cuspResponse_equation s minusBranch z (by linarith)]
  dsimp [squareRemainder]
  ring

/-- Below height two the forcing is the unmodified squared Eisenstein source. -/
theorem forcing_low (s : SpectralSite) (minusBranch : Bool) (z : Fin 2 → ℝ)
    (hz : z 1 < 2) :
    forcing s minusBranch z = (parameter s minusBranch/2)*scalar (center s) z^(2 : ℕ) := by
  have he : cutoffResponse s minusBranch =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [(isOpen_lt (continuous_apply 1) continuous_const).mem_nhds hz] with w hw
    exact cutoffResponse_zero s minusBranch w hw.le
  rw [forcing, hyperbolicLaplacian_congr he, he.eq_of_nhds]
  have hd (i : Fin 2) : coordDeriv i (fun _ : Fin 2 → ℝ => (0:ℂ)) = fun _ => 0 := by
    funext w
    simp [coordDeriv]
  simp [hyperbolicLaplacian, hd]

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
  exact (((Complex.ofRealCLM.continuous.continuousAt.comp
    (continuous_apply 1).continuousAt).pow 2).mul ((hdd 0).add (hdd 1))).continuousWithinAt

/-- The forcing is continuous on the positive-height chart. -/
theorem forcing_continuousOn (s : SpectralSite) (minusBranch : Bool) :
    ContinuousOn (forcing s minusBranch) domain := by
  have hr := cutoffResponse_contDiffOn s minusBranch
  have hl := laplacian_continuous ((contDiffOn_infty.mp hr) 2)
  exact (continuousOn_const.mul ((cuspLeg_contDiffOn .scalar (center s)).continuousOn.pow 2)).sub
    (hl.sub (continuousOn_const.mul hr.continuousOn))

/-- The forcing is bounded on the closed modular cell, including its cusp. -/
theorem forcing_bounded (s : SpectralSite) (minusBranch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, z ∈ ModularGroup.fd →
      ‖forcing s minusBranch (coordinates z)‖ ≤ C := by
  obtain ⟨B, hB, hb⟩ := squareRemainder_bounded (center s) (1/2) (by norm_num)
  let lo : Fin 2 → ℝ := ![-1/2, 1/2]
  let hi : Fin 2 → ℝ := ![1/2, 4]
  have hc : ContinuousOn (forcing s minusBranch) (Icc lo hi) :=
    (forcing_continuousOn s minusBranch).mono (by
      intro z hz
      have hh := hz.1 1
      change (1/2 : ℝ) ≤ z 1 at hh
      change 0 < z 1
      linarith)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C (‖parameter s minusBranch/2‖*B),
    le_trans (mul_nonneg (norm_nonneg _) hB) (le_max_right _ _), ?_⟩
  intro z hz
  have hre := abs_le.mp hz.2
  have hsq := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have him : (1/2 : ℝ) ≤ z.im := by nlinarith [z.im_pos]
  by_cases hh : 4 ≤ z.im
  · rw [forcing_high s minusBranch (coordinates z) (by change 3 < z.im; linarith), norm_mul]
    exact (mul_le_mul_of_nonneg_left (hb (coordinates z) him) (norm_nonneg _)).trans
      (le_max_right _ _)
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

private theorem coordinates_continuous : Continuous coordinates := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact UpperHalfPlane.continuous_re
  · exact UpperHalfPlane.continuous_im

/-- The forcing belongs to the modular hyperbolic `L²` space at every spectral site. -/
theorem forcing_memLp (s : SpectralSite) (minusBranch : Bool) :
    MemLp (fun z : UpperHalfPlane => forcing s minusBranch (coordinates z)) 2 angularMeasure := by
  have hc : Continuous (fun z : UpperHalfPlane => forcing s minusBranch (coordinates z)) :=
    (forcing_continuousOn s minusBranch).comp_continuous coordinates_continuous
      (fun z => z.im_pos)
  obtain ⟨C, _, hC⟩ := forcing_bounded s minusBranch
  apply MemLp.of_bound hc.aestronglyMeasurable C
  exact (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet).mono hC

/-- The forcing as a vector of the modular angular Hilbert space. -/
def forcingVector (s : SpectralSite) (minusBranch : Bool) : Lp ℂ 2 angularMeasure :=
  (forcing_memLp s minusBranch).toLp (fun z => forcing s minusBranch (coordinates z))

theorem forcingVector_coe (s : SpectralSite) (minusBranch : Bool) :
    (forcingVector s minusBranch : UpperHalfPlane → ℂ) =ᵐ[angularMeasure]
      (fun z => forcing s minusBranch (coordinates z)) :=
  (forcing_memLp s minusBranch).coeFn_toLp

@[simp] theorem forcingVector_site (q : XiZeroCopy) (b : Bool) :
    forcingVector (site q) b = D4BMGlobalAngularResponse.forcingVector q b := rfl

/-! ## Modular invariance and the globally smooth forcing -/

private theorem clearFactor_ne_zero {u : ℂ} (hu : u.im ≠ 0) : clearFactor u ≠ 0 := by
  have h0 : u ≠ 0 := by intro h; exact hu (by rw [h]; rfl)
  have hm : 2*u-1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hu (by linarith)
  have hp : 2*u+1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hu (by linarith)
  exact mul_ne_zero (mul_ne_zero h0 hm) hp

/-- The Eisenstein scalar obeys modular inversion at every spectral site. -/
theorem scalar_invert (s : SpectralSite) (z : D4BMUpperHalfPlaneCoordinate) :
    scalar (center s) ![(d4BMEisensteinInvertCoordinate z).x,(d4BMEisensteinInvertCoordinate z).y] =
      scalar (center s) ![z.x,z.y] := by
  have hi : (center s).im ≠ 0 := by simpa [center] using s.2.2.2
  have he := clearedScalar_invert (center s) z
  rw [clearedScalar_eq _ hi, clearedScalar_eq _ hi] at he
  exact (mul_left_cancel₀ (clearFactor_ne_zero hi)) he

private theorem scalar_S (s : SpectralSite) (z : UpperHalfPlane) :
    scalar (center s) (coordinates (ModularGroup.S • z)) = scalar (center s) (coordinates z) := by
  have h := scalar_invert s ⟨z.re, z.im, z.im_pos⟩
  rw [UpperHalfPlane.modular_S_smul]
  simpa [coordinates, d4BMEisensteinInvertCoordinate,
    Complex.inv_re, Complex.inv_im, Complex.normSq_apply, sq, neg_div] using h

private theorem scalar_T (s : SpectralSite) (z : UpperHalfPlane) :
    scalar (center s) (coordinates (ModularGroup.T • z)) = scalar (center s) (coordinates z) := by
  simp only [coordinates, ModularGroup.re_T_smul, ModularGroup.im_T_smul]
  simpa [scalar] using
    d4BM_completedEisensteinCuspLeg_scalar_periodic (center s) z.im z.re

/-- The Eisenstein scalar is invariant under the whole modular group. -/
theorem scalar_modular (s : SpectralSite) (A : SL(2, ℤ)) (z : UpperHalfPlane) :
    scalar (center s) (coordinates (A • z)) = scalar (center s) (coordinates z) := by
  have hA : A ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  suffices ∀ z : UpperHalfPlane,
      scalar (center s) (coordinates (A • z)) = scalar (center s) (coordinates z) from this z
  induction hA using Subgroup.closure_induction with
  | mem g hg =>
    simp only [mem_insert_iff, mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact scalar_S s
    · exact scalar_T s
  | one => intro w; simp
  | mul g h _ _ ig ih => intro w; rw [mul_smul, ig, ih]
  | inv g _ ig => intro w; simpa using (ig (g⁻¹ • w)).symm

private theorem periodic_coordDeriv {f : (Fin 2 → ℝ) → ℂ} {p : Fin 2 → ℝ}
    (hf : Function.Periodic f p) (i : Fin 2) : Function.Periodic (coordDeriv i f) p := by
  intro z
  have he : (fun w => f (w+p)) = f := funext hf
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := z) p
  rw [he] at hd
  exact congrArg (fun L => L (Pi.single i 1)) hd.symm

private theorem periodic_laplacian {f : (Fin 2 → ℝ) → ℂ} {p : Fin 2 → ℝ}
    (hf : Function.Periodic f p) (hp : p 1 = 0) :
    Function.Periodic (hyperbolicLaplacian f) p := by
  intro z
  simp only [hyperbolicLaplacian, Pi.add_apply, hp, add_zero,
    periodic_coordDeriv (periodic_coordDeriv hf 0) 0 z,
    periodic_coordDeriv (periodic_coordDeriv hf 1) 1 z]

/-- The forcing is periodic across the vertical modular sides. -/
theorem forcing_periodic (s : SpectralSite) (minusBranch : Bool) :
    Function.Periodic (forcing s minusBranch) ![1,0] := by
  have hs : Function.Periodic (scalar (center s)) ![1,0] := by
    intro z
    simpa [scalar, Pi.add_apply] using
      d4BM_completedEisensteinCuspLeg_scalar_periodic (center s) (z 1) (z 0)
  have hc : Function.Periodic (cutoffResponse s minusBranch) ![1,0] := by
    intro z
    simp [cutoffResponse, cutoff, cuspResponse, cuspPowerResponse, powerResponse, Pi.add_apply]
  have hl := periodic_laplacian hc (by rfl)
  intro z
  unfold forcing
  rw [hs z, hc z, hl z]

/-- The forcing germs agree at every closed-cell modular overlap. -/
theorem forcing_cell_overlap_germ (s : SpectralSite) (branch : Bool) (A : SL(2, ℤ))
    (z : UpperHalfPlane) (hz : z ∈ fd) (hAz : A • z ∈ fd) :
    (fun w : UpperHalfPlane => forcing s branch (coordinates (A • w))) =ᶠ[𝓝 z]
      (fun w => forcing s branch (coordinates w)) := by
  by_cases hc : A 1 0 = 0
  · obtain ⟨n, hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
    apply Filter.Eventually.of_forall
    intro w
    change forcing s branch (coordinates (A • w)) = forcing s branch (coordinates w)
    rw [hn]
    have h := (forcing_periodic s branch).zsmul n (coordinates w)
    convert h using 1
    congr 1
    ext i
    fin_cases i <;>
      simp only [coordinates, Pi.add_apply, Pi.smul_apply,
        ModularGroup.re_T_zpow_smul, ModularGroup.im_T_zpow_smul] <;> simp
  · obtain ⟨hl, hr⟩ := nonparabolic_cell_overlap_low A hc z hz hAz
    have hleft : ∀ᶠ w : UpperHalfPlane in 𝓝 z, w.im < 2 :=
      (isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hl
    have hright : ∀ᶠ w : UpperHalfPlane in 𝓝 z, (A • w).im < 2 :=
      (isOpen_lt (UpperHalfPlane.continuous_im.comp
        (show Continuous (fun w : UpperHalfPlane => A • w) from by
          simp_rw [sl_moeb]; exact continuous_const_smul _))
        continuous_const).mem_nhds hr
    filter_upwards [hleft, hright] with w hw hAw
    rw [forcing_low s branch _ hAw, forcing_low s branch _ hw, scalar_modular]

/-- The chart forcing is smooth before gluing. -/
theorem forcing_chartSmooth (s : SpectralSite) (branch : Bool) :
    ChartSmooth (fun z => forcing s branch (coordinates z)) := by
  have hC : ContDiff ℝ ∞ (fun z : ℂ => ![z.re,z.im]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.contDiff
    · exact Complex.imCLM.contDiff
  have hf : ContDiffOn ℝ ∞ (fun z : ℂ => forcing s branch ![z.re,z.im]) {z : ℂ | 0 < z.im} :=
    (forcing_contDiffOn s branch).comp hC.contDiffOn (fun _ hz => hz)
  intro z
  apply (hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply, coordinates, ofComplex_apply_of_im_pos hw]
  rfl

private theorem forcing_compatible (s : SpectralSite) (branch : Bool) :
    CellGermCompatible (fun z => forcing s branch (coordinates z)) := by
  intro γ z hz hγ
  induction γ using QuotientGroup.induction_on with
  | H A =>
    simp only [PSL2Z_mk_smul] at hγ ⊢
    exact forcing_cell_overlap_germ s branch A z hz hγ

/-- The forcing glued by its compatible closed-cell germs. -/
def globalForcing (s : SpectralSite) (branch : Bool) : UpperHalfPlane → ℂ :=
  cellGermExtension (fun z => forcing s branch (coordinates z))

theorem globalForcing_eq_on_fd (s : SpectralSite) (branch : Bool) (z : UpperHalfPlane)
    (hz : z ∈ fd) : globalForcing s branch z = forcing s branch (coordinates z) :=
  (cellGermExtension_germ _ (forcing_compatible s branch) z hz).eq_of_nhds

theorem globalForcing_invariant (s : SpectralSite) (branch : Bool) (γ : PSL2Z)
    (z : UpperHalfPlane) : globalForcing s branch (γ • z) = globalForcing s branch z :=
  cellGermExtension_invariant _ (forcing_compatible s branch) γ z

/-- The glued forcing is globally smooth. -/
theorem globalForcing_smooth (s : SpectralSite) (branch : Bool) :
    ChartSmooth (globalForcing s branch) :=
  cellGermExtension_smooth _ (forcing_compatible s branch) (forcing_chartSmooth s branch)

private theorem invariant_ae_eq_of_native {f g : UpperHalfPlane → ℂ}
    (hf : ∀ γ : PSL2Z, ∀ z, f (γ • z) = f z)
    (hg : ∀ γ : PSL2Z, ∀ z, g (γ • z) = g z) (he : f =ᵐ[measure] g) :
    f =ᵐ[(volume : Measure UpperHalfPlane)] g := by
  have hn : ∀ᵐ z : UpperHalfPlane ∂volume, z ∈ fd → f z = g z :=
    (ae_restrict_iff' isClosed_fd.measurableSet).mp he
  have ht (γ : PSL2Z) :
      ∀ᵐ z : UpperHalfPlane ∂volume, γ • z ∈ fd → f z = g z := by
    have hh := (measurePreserving_smul γ
      (volume : Measure UpperHalfPlane)).quasiMeasurePreserving.ae hn
    filter_upwards [hh] with z hz hmem
    simpa only [hf γ z, hg γ z] using hz hmem
  have hall : ∀ᵐ z : UpperHalfPlane ∂volume,
      ∀ γ : PSL2Z, γ • z ∈ fd → f z = g z :=
    ae_all_iff.mpr ht
  filter_upwards [hall] with z hz
  obtain ⟨A, hA⟩ := exists_smul_mem_fd z
  exact hz (QuotientGroup.mk A) (by simpa only [PSL2Z_mk_smul] using hA)

/-- The smooth glued forcing represents the modular lift of the `L²` forcing vector. -/
theorem globalForcing_ae_lift (s : SpectralSite) (branch : Bool) :
    globalForcing s branch =ᵐ[(volume : Measure UpperHalfPlane)]
      globalLift (forcingVector s branch) := by
  apply invariant_ae_eq_of_native (globalForcing_invariant s branch)
    (globalLift_invariant (forcingVector s branch))
  filter_upwards [ae_mem_interior, forcingVector_coe s branch,
    globalLift_ae_eq (forcingVector s branch)] with z hz hF hL
  rw [globalForcing_eq_on_fd s branch z (fdo_subset_fd hz), hL, hF]

/-! ## The global cusp cutoff -/

private theorem cutoffResponse_chartSmooth (s : SpectralSite) (branch : Bool) :
    ChartSmooth (fun z => cutoffResponse s branch (coordinates z)) := by
  have hC : ContDiff ℝ ∞ (fun z : ℂ => ![z.re,z.im]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.contDiff
    · exact Complex.imCLM.contDiff
  have hf : ContDiffOn ℝ ∞ (fun z : ℂ => cutoffResponse s branch ![z.re,z.im])
      {z : ℂ | 0 < z.im} :=
    (cutoffResponse_contDiffOn s branch).comp hC.contDiffOn (fun _ hz => hz)
  intro z
  apply (hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply, coordinates, ofComplex_apply_of_im_pos hw]
  rfl

private theorem cutoffResponse_cell_germ (s : SpectralSite) (branch : Bool) :
    CellGermCompatible (fun z => cutoffResponse s branch (coordinates z)) := by
  intro γ z hz hγ
  induction γ using QuotientGroup.induction_on with
  | H A =>
    simp only [PSL2Z_mk_smul] at hγ ⊢
    by_cases hc : A 1 0 = 0
    · obtain ⟨n, hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
      apply Filter.Eventually.of_forall
      intro w
      change cutoffResponse s branch (coordinates (A • w)) =
        cutoffResponse s branch (coordinates w)
      rw [hn]
      simp only [coordinates, cutoffResponse, cutoff, cuspResponse, cuspPowerResponse,
        powerResponse, Matrix.cons_val_one, ModularGroup.im_T_zpow_smul]
    · obtain ⟨hl, hr⟩ := nonparabolic_cell_overlap_low A hc z hz hγ
      have hleft : ∀ᶠ w : UpperHalfPlane in 𝓝 z, w.im < 2 :=
        (isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hl
      have hright : ∀ᶠ w : UpperHalfPlane in 𝓝 z, (A • w).im < 2 :=
        (isOpen_lt (UpperHalfPlane.continuous_im.comp
          (show Continuous (fun w : UpperHalfPlane => A • w) from by
            simp_rw [sl_moeb]; exact continuous_const_smul _)) continuous_const).mem_nhds hr
      filter_upwards [hleft, hright] with w hw hAw
      rw [cutoffResponse_zero s branch _ hAw.le, cutoffResponse_zero s branch _ hw.le]

/-- The globally glued cusp cutoff response. -/
def globalCuspCutoff (s : SpectralSite) (branch : Bool) : UpperHalfPlane → ℂ :=
  cellGermExtension (fun z => cutoffResponse s branch (coordinates z))

theorem globalCuspCutoff_smooth (s : SpectralSite) (branch : Bool) :
    ChartSmooth (globalCuspCutoff s branch) :=
  cellGermExtension_smooth _ (cutoffResponse_cell_germ s branch)
    (cutoffResponse_chartSmooth s branch)

theorem globalCuspCutoff_invariant (s : SpectralSite) (branch : Bool)
    (γ : PSL2Z) (z : UpperHalfPlane) :
    globalCuspCutoff s branch (γ • z) = globalCuspCutoff s branch z :=
  cellGermExtension_invariant _ (cutoffResponse_cell_germ s branch) γ z

@[simp] theorem globalCuspCutoff_site (q : XiZeroCopy) (b : Bool) :
    globalCuspCutoff (site q) b = D4BMModularCore.globalCuspCutoff q b := rfl

end
end RHTower.PWBSpectralSource
