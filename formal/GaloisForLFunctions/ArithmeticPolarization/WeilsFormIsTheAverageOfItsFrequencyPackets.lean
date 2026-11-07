import GaloisForLFunctions.ArithmeticPolarization.TheCollidedFormSamplesHighFrequencies
import GaloisForLFunctions.RHTower.WeilFullConeHerglotzRightHalfPlane
import GaloisForLFunctions.RHTower.RiemannKernelStripPlancherel
import GaloisForLFunctions.RHTower.WeilPositivityTwistObstruction

/-!
# Weil's form is the average of its frequency packets

Let `f` be a `C²` test supported in `[−A, A]` and `φ` a continuous window supported in `[−b, b]`.
The **frequency packet** of `f` at `X` is `f_X = f ⋆ φ_X`, `φ_X(u) = φ(u) e^{−iXu}`; its transform is
`f̂(τ) φ̂(τ − X)`, the part of `f̂` near the frequency `X`. Then

`∫ Re W(f_X) dX = 2π ‖φ‖₂² · Re W(f)`  (`integral_re_W_frequencyPacket`).

**Mechanism.** Every test supported in `[−(A + b), A + b]` has `Re W(g) = ∫ |ĝ|² ν` for the
explicit-formula density `ν = ν_{e^{2(A+b)}}` (`re_W_eq_integral_nuX`). Hence `X ↦ Re W(f_X)` is the
convolution of `|f̂|² ν` with `|φ̂(−·)|²`, the integral of a convolution is the product of the
integrals, and `∫ |φ̂|² = 2π ‖φ‖₂²` (Plancherel).

So Weil's form is diagonal in frequency: a negative test has negative frequency packets on a set of
frequencies of positive measure (`volume_neg_frequencyPacket_pos`).
-/

open Complex MeasureTheory Set Filter Topology Real
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open Zeta23

/-- The window modulated to frequency `X`: `φ_X(u) = φ(u) e^{−iXu}`. -/
def modulatedWindow (φ : ℝ → ℂ) (X u : ℝ) : ℂ := φ u * cexp (-(I * X * u))

/-- The frequency packet `f ⋆ φ_X` of `f` at frequency `X`. -/
def frequencyPacket (f φ : ℝ → ℂ) (X : ℝ) : ℝ → ℂ :=
  convolution f (modulatedWindow φ X) (ContinuousLinearMap.mul ℝ ℂ) volume

theorem paperFT_modulatedWindow (φ : ℝ → ℂ) (X : ℝ) (z : ℂ) :
    paperFT (modulatedWindow φ X) z = paperFT φ (z - X) := by
  simp only [paperFT, modulatedWindow]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem continuous_modulatedWindow {φ : ℝ → ℂ} (hφ : Continuous φ) (X : ℝ) :
    Continuous (modulatedWindow φ X) := by
  unfold modulatedWindow
  fun_prop

theorem modulatedWindow_eq_zero {φ : ℝ → ℂ} {b : ℝ} (hφs : tsupport φ ⊆ Icc (-b) b) (X : ℝ)
    {u : ℝ} (hu : b < |u|) : modulatedWindow φ X u = 0 := by
  have hnot : u ∉ tsupport φ := fun h => by
    have := hφs h
    exact (not_le.mpr hu) (abs_le.mpr ⟨this.1, this.2⟩)
  simp [modulatedWindow, image_eq_zero_of_notMem_tsupport hnot]

theorem eq_zero_of_tsupport_subset {f : ℝ → ℂ} {A : ℝ} (hfs : tsupport f ⊆ Icc (-A) A) {u : ℝ}
    (hu : A < |u|) : f u = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun h => ?_
  have := hfs h
  exact (not_le.mpr hu) (abs_le.mpr ⟨this.1, this.2⟩)

theorem hasCompactSupport_of_tsupport_subset {f : ℝ → ℂ} {A : ℝ} (hfs : tsupport f ⊆ Icc (-A) A) :
    HasCompactSupport f :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport f).trans hfs)

/-- The packet is a `C²` test supported in `[−(A + b), A + b]`. -/
theorem contDiff_frequencyPacket {f φ : ℝ → ℂ} {A : ℝ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-A) A) (hφ : Continuous φ) (X : ℝ) :
    ContDiff ℝ 2 (frequencyPacket f φ X) :=
  (hasCompactSupport_of_tsupport_subset hfs).contDiff_convolution_left (n := 2) _ hf
    (continuous_modulatedWindow hφ X).locallyIntegrable

theorem tsupport_frequencyPacket {f φ : ℝ → ℂ} {A b : ℝ} (hfs : tsupport f ⊆ Icc (-A) A)
    (hφs : tsupport φ ⊆ Icc (-b) b) (X : ℝ) :
    tsupport (frequencyPacket f φ X) ⊆ Icc (-(A + b)) (A + b) := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hout
  have hx' : A + b < |x| := by
    by_contra h
    exact hout (abs_le.mp (not_lt.mp h))
  exact hx (RHTower.convolution_mul_eq_zero_of_abs_gt (fun u hu => eq_zero_of_tsupport_subset hfs hu)
    (fun u hu => modulatedWindow_eq_zero hφs X hu) hx')

/-- The transform of the packet localizes `f̂` at `X`: `f̂_X(τ) = f̂(τ) φ̂(τ − X)`. -/
theorem paperFT_frequencyPacket {f φ : ℝ → ℂ} {A b : ℝ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-A) A) (hφ : Continuous φ) (hφs : tsupport φ ⊆ Icc (-b) b)
    (X : ℝ) (z : ℂ) :
    paperFT (frequencyPacket f φ X) z = paperFT f z * paperFT φ (z - X) := by
  have hfc := hasCompactSupport_of_tsupport_subset hfs
  have hφc := hasCompactSupport_of_tsupport_subset hφs
  have hmc : HasCompactSupport (modulatedWindow φ X) := hφc.mul_right
  rw [frequencyPacket, RHTower.WeilHerglotz.paperFT_convolution
    (hf.continuous.integrable_of_hasCompactSupport hfc)
    ((continuous_modulatedWindow hφ X).integrable_of_hasCompactSupport hmc) hfc hmc z,
    paperFT_modulatedWindow]

/-- The density of `f` against the explicit formula at aperture `A + b`. -/
def packetDensity (f : ℝ → ℂ) (A : ℝ) (τ : ℝ) : ℝ := ‖paperFT f τ‖ ^ 2 * nuX (Real.exp (2 * A)) τ

/-- The reflected spectral window `y ↦ |φ̂(−y)|²`. -/
def reflectedWindowMass (φ : ℝ → ℂ) (y : ℝ) : ℝ := ‖paperFT φ ((-y : ℝ) : ℂ)‖ ^ 2

/-- `Re W(f_X)` is the convolution of `|f̂|² ν` with `|φ̂(−·)|²`, evaluated at `X`. -/
theorem re_W_frequencyPacket_eq_convolution {f φ : ℝ → ℂ} {A b : ℝ} (hA : 0 < A) (hb : 0 < b)
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-A) A) (hφ : Continuous φ)
    (hφs : tsupport φ ⊆ Icc (-b) b) (X : ℝ) :
    (zetaZeroConfig.W (frequencyPacket f φ X) (frequencyPacket f φ X)).re =
      convolution (packetDensity f (A + b)) (reflectedWindowMass φ)
        (ContinuousLinearMap.mul ℝ ℝ) volume X := by
  obtain ⟨-, hW⟩ := re_W_eq_integral_nuX (by linarith : 0 < A + b)
    (contDiff_frequencyPacket hf hfs hφ X) (tsupport_frequencyPacket hfs hφs X)
  rw [hW, convolution_def]
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only [ContinuousLinearMap.mul_apply', packetDensity, reflectedWindowMass]
  rw [paperFT_frequencyPacket hf hfs hφ hφs X, norm_mul, mul_pow]
  have harg : ((τ : ℂ) - (X : ℂ)) = ((-(X - τ) : ℝ) : ℂ) := by push_cast; ring
  rw [harg]
  ring

/-- **Weil's form is the average of its frequency packets.**
`∫ Re W(f ⋆ φ_X) dX = 2π ‖φ‖₂² Re W(f)`, and the packet form is integrable in `X`. -/
theorem integral_re_W_frequencyPacket {f φ : ℝ → ℂ} {A b : ℝ} (hA : 0 < A) (hb : 0 < b)
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-A) A) (hφ : Continuous φ)
    (hφs : tsupport φ ⊆ Icc (-b) b) :
    Integrable (fun X => (zetaZeroConfig.W (frequencyPacket f φ X) (frequencyPacket f φ X)).re) ∧
      ∫ X, (zetaZeroConfig.W (frequencyPacket f φ X) (frequencyPacket f φ X)).re =
        2 * π * (∫ u, ‖φ u‖ ^ 2) * (zetaZeroConfig.W f f).re := by
  have hAb : 0 < A + b := by linarith
  have hfs' : tsupport f ⊆ Icc (-(A + b)) (A + b) :=
    hfs.trans (Icc_subset_Icc (by linarith) (by linarith))
  obtain ⟨hgi, hWf⟩ := re_W_eq_integral_nuX hAb hf hfs'
  have hφc := hasCompactSupport_of_tsupport_subset hφs
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have hφ2 : MemLp φ 2 := hφ.memLp_of_hasCompactSupport hφc
  have hhi : Integrable (reflectedWindowMass φ) := by
    have h := (RHTower.KernelStrip.integrable_norm_sq_paperFT hφi hφ2).comp_neg
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp [reflectedWindowMass]
  have hgi' : Integrable (packetDensity f (A + b)) := hgi
  have hconv := funext (re_W_frequencyPacket_eq_convolution hA hb hf hfs hφ hφs)
  refine ⟨?_, ?_⟩
  · rw [hconv]
    exact hgi'.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hhi
  · rw [hconv, integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hgi' hhi,
      ContinuousLinearMap.mul_apply']
    have hh : ∫ y, reflectedWindowMass φ y = 2 * π * ∫ u, ‖φ u‖ ^ 2 := by
      have hneg := integral_neg_eq_self (fun y : ℝ => ‖paperFT φ (y : ℂ)‖ ^ 2) volume
      simp only [reflectedWindowMass]
      rw [hneg, RHTower.KernelStrip.integral_norm_sq_paperFT_of_memLp hφi hφ2]
    have hg : ∫ τ, packetDensity f (A + b) τ = (zetaZeroConfig.W f f).re := hWf.symm
    rw [hg, hh]
    ring

/-- **Negativity is carried by a set of frequencies of positive measure.** If `Re W(f) < 0` and
`φ ≠ 0`, the packets `f ⋆ φ_X` are negative on a set of `X` of positive measure. -/
theorem volume_neg_frequencyPacket_pos {f φ : ℝ → ℂ} {A b : ℝ} (hA : 0 < A) (hb : 0 < b)
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-A) A) (hφ : Continuous φ)
    (hφs : tsupport φ ⊆ Icc (-b) b) (hφ0 : φ ≠ 0) (hneg : (zetaZeroConfig.W f f).re < 0) :
    0 < volume {X | (zetaZeroConfig.W (frequencyPacket f φ X) (frequencyPacket f φ X)).re < 0} := by
  obtain ⟨hint, hval⟩ := integral_re_W_frequencyPacket hA hb hf hfs hφ hφs
  have hφc := hasCompactSupport_of_tsupport_subset hφs
  have hmass : 0 < ∫ u, ‖φ u‖ ^ 2 := by
    obtain ⟨u₀, hu₀⟩ : ∃ u₀, φ u₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hφ0 (funext h)
    have hc : Continuous fun u => ‖φ u‖ ^ 2 := hφ.norm.pow 2
    have hpos : 0 < ‖φ u₀‖ ^ 2 := by positivity
    exact (integral_pos_iff_support_of_nonneg (fun u => sq_nonneg _)
      (hc.integrable_of_hasCompactSupport
        (hφc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)))).mpr
      ((hc.isOpen_support).measure_pos volume ⟨u₀, hpos.ne'⟩)
  have hlt : ∫ X, (zetaZeroConfig.W (frequencyPacket f φ X) (frequencyPacket f φ X)).re < 0 := by
    rw [hval]
    have : 0 < 2 * π * ∫ u, ‖φ u‖ ^ 2 := by positivity
    nlinarith
  by_contra hzero
  rw [not_lt, nonpos_iff_eq_zero] at hzero
  have hae : 0 ≤ᵐ[volume] fun X =>
      (zetaZeroConfig.W (frequencyPacket f φ X) (frequencyPacket f φ X)).re := by
    rw [Filter.EventuallyLE, ae_iff]
    simpa only [Pi.zero_apply, not_le] using hzero
  exact (not_lt.mpr (integral_nonneg_of_ae hae)) hlt

end GaloisForLFunctions.ArithmeticPolarization
