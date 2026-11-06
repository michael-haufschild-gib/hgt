import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLocalWeilKernelIsHermiteBiehler
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.AUnitaryWithCompactDefectHasCompleteEigenvectors
import GaloisForLFunctions.RHTower.PoleVanishingWeilTraceCertificate
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemma43
import GaloisForLFunctions.RHTower.XiGaussianHeatWeilMarginInterface

/-!
# De Branges sampling bases of the pre-contact Weil spaces

Write `E` for the Hermite–Biehler function of the exact Weil space and `E^#(z) = conj E(conj z)`.
For a unimodular `φ` the companion is `S_φ = φ E^# − E`.

* The zero-moving unitary extends, with one boundary phase `φ`, to a unitary `V_φ` of the whole
  space, and `(z − i) F_{V_φ x} = (z + i) F_x + c(x) S_φ`.
* `V_φ − 1` is a rank-one map plus a division by `z − i`. Division gains a full power of
  `1 + |ξ|²`, which beats the logarithmic Fourier weight of the form norm, so it factors through
  the compact embedding into `L²`. Hence `V_φ` has complete eigenvectors.
* `E` is never in the space, so `S_φ` is in the space for at most one `φ`. For every other `φ`,
  all eigenvectors of `V_φ` are multiples of reproducing kernels at real zeros of `S_φ`, and these
  kernels are mutually orthogonal by the Christoffel–Darboux formula.

This gives the sampling formula `‖x‖² = ∑_{S_φ(t) = 0} |F_x(t)|² / K(t,t)`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct FourierTransform ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact

open _root_.RHTower

variable (a : PrecontactAperture)

/-! ### The weighted Fourier coordinate -/

/-- The unitary Fourier transform of a compactly supported `L²` class is its compact integral. -/
theorem fourierUnitary_ae_eq_compactFourier {b : ℝ} {u : SoninL2} (hfix : suzukiCutoff b u = u) :
    (fourierUnitary u : ℝ → ℂ) =ᵐ[volume]
      fun ξ => suzukiCompactL2Fourier b u ((-(2 * Real.pi * ξ) : ℝ) : ℂ) := by
  have hint : Integrable (u : ℝ → ℂ) := by
    have h := integrable_suzukiCutoff b u
    rwa [hfix] at h
  filter_upwards [fourierUnitary_ae_eq_fourier_of_integrable u hint] with ξ h2
  rw [h2, suzukiCompactL2Fourier_eq_full_integral_of_fixed hfix,
    Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with t
  rw [smul_eq_mul]
  congr 2
  push_cast
  ring

/-- The form-domain coordinate of a Weil vector is its entire transform on the real line. -/
theorem toForm_ae_eq_fourier (x : WeilHilbertBeforeContact a) :
    (((toForm a x : CCMArchimedeanFormDomain a.1).1 : CCMArchimedeanFourierL2) : ℝ → ℂ)
      =ᵐ[volume] fun ξ => fourier a x ((-(2 * Real.pi * ξ) : ℝ) : ℂ) := by
  let f : CCMArchimedeanFourierL2 := (toForm a x).1
  let u : SoninL2 := (ccmArchimedeanFormToAperture a.1 (toForm a x) : SoninL2)
  have hfix : suzukiCutoff a.1.1 u = u := indicatorCutoff_suzukiApertureHilbert a.1 _
  have h1 : fourierUnitary u = ccmArchimedeanWeightedToL2 f :=
    fourierUnitary_ccmArchimedeanFourierToTime f
  filter_upwards [fourierUnitary_ae_eq_compactFourier hfix,
    ccmArchimedeanWeightedToL2_coeFn f] with ξ h2 h3
  change f ξ = _
  rw [← h3, ← h1, h2, fourier_eq_whole]

/-- The form weight grows at most like a square root. -/
theorem exists_formWeight_le_sqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, ccmArchimedeanFormWeight ξ ≤ C * Real.sqrt (1 + |ξ|) := by
  let G : ℝ := |gammaHardyPhaseRate 1| + 33 / 16 + Real.pi / 2
  have hG : 0 ≤ G := by positivity
  have hγ (t : ℝ) (ht : 0 ≤ t) : gammaHardyPhaseRate t ≤ G + Real.sqrt t := by
    rcases le_total t 1 with h | h
    · have hm := strictMonoOn_gammaHardyPhaseRate.monotoneOn (Set.mem_Ici.mpr ht)
        (Set.mem_Ici.mpr zero_le_one) h
      have hs := Real.sqrt_nonneg t
      have ha := le_abs_self (gammaHardyPhaseRate 1)
      have hπ := Real.pi_pos
      simp only [G]
      linarith only [hm, hs, ha, hπ]
    · have ht0 : 0 < t := by linarith only [h]
      have hb := (abs_le.mp (gammaHardyPhaseRate_sub_log_conductor_bound ht0)).2
      have hsq : (1 : ℝ) ≤ t ^ 2 := one_le_pow₀ h
      have h1 : 33 / (16 * t ^ 2) ≤ 33 / 16 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith only [hsq]
      have h2 : Real.pi / (2 * t) ≤ Real.pi / 2 := by
        apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
        linarith only [h]
      have hlog : Real.log (t / (2 * Real.pi)) ≤ Real.log t := by
        apply Real.log_le_log (div_pos ht0 (by positivity))
        apply div_le_self ht0.le
        nlinarith only [Real.pi_gt_three]
      have hsqrt : Real.log t / 2 ≤ Real.sqrt t - 1 := by
        rw [← Real.log_sqrt ht0.le]
        exact Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ht0)
      have ha := abs_nonneg (gammaHardyPhaseRate 1)
      simp only [G]
      linarith only [hb, h1, h2, hlog, hsqrt, ha]
  refine ⟨7 + 2 * G + 2 * |gammaHardyPhaseRate 0|, by positivity, fun ξ => ?_⟩
  have hs1 : 1 ≤ Real.sqrt (1 + |ξ|) := by
    rw [Real.one_le_sqrt]
    linarith only [abs_nonneg ξ]
  have ht : 0 ≤ 2 * Real.pi * |ξ| := by positivity
  have h3 : Real.sqrt (2 * Real.pi * |ξ|) ≤ 3 * Real.sqrt (1 + |ξ|) := by
    calc
      Real.sqrt (2 * Real.pi * |ξ|) ≤ Real.sqrt (3 ^ 2 * (1 + |ξ|)) := by
        apply Real.sqrt_le_sqrt
        nlinarith only [Real.pi_lt_four, abs_nonneg ξ, Real.pi_pos]
      _ = 3 * Real.sqrt (1 + |ξ|) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hg := hγ _ ht
  have ha := neg_abs_le (gammaHardyPhaseRate 0)
  unfold ccmArchimedeanFormWeight
  nlinarith only [hg, h3, hs1, ha, hG, abs_nonneg (gammaHardyPhaseRate 0)]

/-- The form weight is dominated by the squared division factor at `i`. -/
theorem exists_formWeight_le_quadratic :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, ccmArchimedeanFormWeight ξ ≤ C * (1 + (2 * Real.pi * ξ) ^ 2) := by
  obtain ⟨C, hC, h⟩ := exists_formWeight_le_sqrt
  refine ⟨2 * C, by positivity, fun ξ => (h ξ).trans ?_⟩
  have hs : Real.sqrt (1 + |ξ|) ≤ 1 + |ξ| :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith only [abs_nonneg ξ]⟩
  have hq : 1 + |ξ| ≤ 2 * (1 + (2 * Real.pi * ξ) ^ 2) := by
    have h1 : (2 * Real.pi * ξ) ^ 2 = (2 * Real.pi) ^ 2 * |ξ| ^ 2 := by
      rw [mul_pow, sq_abs]
    have h2 : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith only [Real.pi_gt_three]
    rw [h1]
    nlinarith only [sq_nonneg (|ξ| - 1), sq_nonneg |ξ|, h2]
  calc
    C * Real.sqrt (1 + |ξ|) ≤ C * (2 * (1 + (2 * Real.pi * ξ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hs.trans hq) hC.le
    _ = _ := by ring

/-- Division by `z - i` is bounded from physical `L²` to the form norm. -/
theorem toForm_norm_sq_le_of_division {C : ℝ}
    (hC : ∀ ξ : ℝ, ccmArchimedeanFormWeight ξ ≤ C * (1 + (2 * Real.pi * ξ) ^ 2))
    {x y : WeilHilbertBeforeContact a}
    (h : ∀ z : ℂ, (z - I) * fourier a y z = 2 * I * fourier a x z) :
    ‖toForm a y‖ ^ 2 ≤
      (4 * C) * ‖ccmArchimedeanFormToAperture a.1 (toForm a x)‖ ^ 2 := by
  have hC0 : 0 ≤ C := by
    have h0 := (one_le_ccmArchimedeanFormWeight 0).trans (hC 0)
    norm_num at h0
    linarith only [h0]
  let fx : CCMArchimedeanFourierL2 := (toForm a x).1
  let fy : CCMArchimedeanFourierL2 := (toForm a y).1
  have hny : ‖toForm a y‖ ^ 2 = ∫ ξ : ℝ, ccmArchimedeanFormWeight ξ * ‖(fy : ℝ → ℂ) ξ‖ ^ 2 :=
    norm_sq_ccmArchimedeanFourierL2 fy
  have hL2 : (ccmArchimedeanWeightedToL2 fx : ℝ → ℂ) =ᵐ[volume] fx :=
    ccmArchimedeanWeightedToL2_coeFn fx
  have hnx : ‖ccmArchimedeanFormToAperture a.1 (toForm a x)‖ ^ 2 =
      ∫ ξ : ℝ, ‖(fx : ℝ → ℂ) ξ‖ ^ 2 := by
    rw [norm_ccmArchimedeanFormToAperture]
    exact sq_norm_soninL2_of_ae_eq hL2
  have hix : Integrable (fun ξ : ℝ => ‖(fx : ℝ → ℂ) ξ‖ ^ 2) := by
    have hm := (MeasureTheory.Lp.memLp (ccmArchimedeanWeightedToL2 fx)).integrable_norm_pow
      (by norm_num)
    refine hm.congr ?_
    filter_upwards [hL2] with ξ hξ
    rw [hξ]
  rw [hny, hnx, ← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards with ξ
    exact mul_nonneg (ccmArchimedeanFormWeight_pos ξ).le (sq_nonneg _)
  · exact hix.const_mul _
  filter_upwards [toForm_ae_eq_fourier a x, toForm_ae_eq_fourier a y] with ξ hxξ hyξ
  have hx' : (fx : ℝ → ℂ) ξ = fourier a x ((-(2 * Real.pi * ξ) : ℝ) : ℂ) := hxξ
  have hy' : (fy : ℝ → ℂ) ξ = fourier a y ((-(2 * Real.pi * ξ) : ℝ) : ℂ) := hyξ
  rw [hx', hy']
  set z : ℂ := ((-(2 * Real.pi * ξ) : ℝ) : ℂ) with hz
  have hk := congrArg (fun w : ℂ => ‖w‖ ^ 2) (h z)
  simp only [norm_mul, mul_pow] at hk
  have hzI : ‖z - I‖ ^ 2 = 1 + (2 * Real.pi * ξ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [hz, Complex.sub_re, Complex.ofReal_re, Complex.I_re, Complex.sub_im,
      Complex.ofReal_im, Complex.I_im]
    ring
  have h2I : ‖(2 : ℂ)‖ ^ 2 * ‖I‖ ^ 2 = 4 := by
    simp only [Complex.norm_I, Complex.norm_ofNat]
    norm_num
  rw [hzI, h2I] at hk
  calc
    ccmArchimedeanFormWeight ξ * ‖fourier a y z‖ ^ 2 ≤
        (C * (1 + (2 * Real.pi * ξ) ^ 2)) * ‖fourier a y z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hC ξ) (sq_nonneg _)
    _ = 4 * C * ‖fourier a x z‖ ^ 2 := by
      linear_combination C * hk

/-! ### The boundary unitaries -/

theorem star_I : star (I : ℂ) = -I := Complex.conj_I

theorem sub_star_I (z : ℂ) : z - star I = z + I := by
  rw [star_I, sub_neg_eq_add]

theorem norm_evalVector_star (z : ℂ) : ‖evalVector a (star z)‖ = ‖evalVector a z‖ :=
  norm_evalVector_conj a z

theorem sq_norm_evalVector_ne (κ : ℂ) : (‖evalVector a κ‖ : ℂ) ^ 2 ≠ 0 :=
  pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (evalVector_ne_zero a κ)))

/-- Coefficient of `v_κ` in the orthogonal splitting along `ker(eval κ) ⊕ ℂ v_κ`. -/
def anchorCoeff (κ : ℂ) : WeilHilbertBeforeContact a →L[ℂ] ℂ :=
  ((‖evalVector a κ‖ : ℂ) ^ 2)⁻¹ • eval a κ

theorem anchorCoeff_apply (κ : ℂ) (x : WeilHilbertBeforeContact a) :
    anchorCoeff a κ x = ((‖evalVector a κ‖ : ℂ) ^ 2)⁻¹ * eval a κ x := rfl

theorem anchorCoeff_evalVector (κ : ℂ) : anchorCoeff a κ (evalVector a κ) = 1 := by
  rw [anchorCoeff_apply, evalVector_self]
  exact inv_mul_cancel₀ (sq_norm_evalVector_ne a κ)

/-- Orthogonal projection onto the evaluation kernel at `κ`. -/
def anchorProj (κ : ℂ) : WeilHilbertBeforeContact a →L[ℂ] WeilHilbertBeforeContact a :=
  ContinuousLinearMap.id ℂ _ - (anchorCoeff a κ).smulRight (evalVector a κ)

theorem anchorProj_apply (κ : ℂ) (x : WeilHilbertBeforeContact a) :
    anchorProj a κ x = x - anchorCoeff a κ x • evalVector a κ := rfl

theorem eval_anchorProj (κ : ℂ) (x : WeilHilbertBeforeContact a) :
    eval a κ (anchorProj a κ x) = 0 := by
  rw [anchorProj_apply, map_sub, map_smul, evalVector_self, anchorCoeff_apply, smul_eq_mul,
    mul_right_comm, inv_mul_cancel₀ (sq_norm_evalVector_ne a κ), one_mul, sub_self]

/-- The projection, regarded as a map into the evaluation kernel. -/
def anchorToKernel (κ : ℂ) : WeilHilbertBeforeContact a →ₗ[ℂ] evaluationKernel a κ :=
  LinearMap.codRestrict _ (anchorProj a κ).toLinearMap
    (fun x => LinearMap.mem_ker.mpr (eval_anchorProj a κ x))

theorem anchorToKernel_coe (κ : ℂ) (x : WeilHilbertBeforeContact a) :
    (anchorToKernel a κ x : WeilHilbertBeforeContact a) =
      x - anchorCoeff a κ x • evalVector a κ := rfl

/-- The extension of zero-moving at `i` with boundary phase `φ`. -/
def boundaryLinear (φ : ℂ) : WeilHilbertBeforeContact a →ₗ[ℂ] WeilHilbertBeforeContact a :=
  (evaluationKernel a (star I)).subtype ∘ₗ (zeroMove a I).toLinearEquiv.toLinearMap ∘ₗ
      anchorToKernel a I +
    (φ • anchorCoeff a I).toLinearMap.smulRight (evalVector a (star I))

theorem boundaryLinear_apply (φ : ℂ) (x : WeilHilbertBeforeContact a) :
    boundaryLinear a φ x =
      (zeroMove a I (anchorToKernel a I x) : WeilHilbertBeforeContact a) +
        (φ * anchorCoeff a I x) • evalVector a (star I) := rfl

theorem norm_sq_add_smul_evalVector {κ : ℂ} {y : WeilHilbertBeforeContact a}
    (hy : eval a κ y = 0) (c : ℂ) :
    ‖y + c • evalVector a κ‖ ^ 2 = ‖y‖ ^ 2 + ‖c‖ ^ 2 * ‖evalVector a κ‖ ^ 2 := by
  have h : inner ℂ y (c • evalVector a κ) = 0 := by
    rw [inner_smul_right, ← inner_conj_symm, inner_evalVector, hy, map_zero, mul_zero]
  rw [@norm_add_sq ℂ _ _ _ _ y _, h, norm_smul, mul_pow]
  simp only [map_zero, mul_zero, add_zero]

theorem norm_boundaryLinear {φ : ℂ} (hφ : ‖φ‖ = 1) (x : WeilHilbertBeforeContact a) :
    ‖boundaryLinear a φ x‖ = ‖x‖ := by
  let c := anchorCoeff a I x
  let w := anchorToKernel a I x
  have hx : x = (w : WeilHilbertBeforeContact a) + c • evalVector a I := by
    rw [anchorToKernel_coe]
    abel
  have h1 := norm_sq_add_smul_evalVector a (κ := I) (y := (w : WeilHilbertBeforeContact a))
    (LinearMap.mem_ker.mp w.property) c
  rw [← hx] at h1
  have h2 := norm_sq_add_smul_evalVector a (κ := star I)
    (y := (zeroMove a I w : WeilHilbertBeforeContact a))
    (LinearMap.mem_ker.mp (zeroMove a I w).property) (φ * c)
  rw [← boundaryLinear_apply, norm_mul, hφ, one_mul, norm_evalVector_star] at h2
  have h3 : ‖(zeroMove a I w : WeilHilbertBeforeContact a)‖ = ‖(w : WeilHilbertBeforeContact a)‖ :=
    (zeroMove a I).norm_map w
  rw [h3, ← h1] at h2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

theorem boundaryLinear_surjective {φ : ℂ} (hφ : ‖φ‖ = 1) :
    Function.Surjective (boundaryLinear a φ) := by
  intro y
  have hφ0 : φ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hφ
    exact zero_ne_one hφ
  let c' := anchorCoeff a (star I) y
  let w := anchorToKernel a (star I) y
  let w₀ : evaluationKernel a I := (zeroMove a I).symm w
  have hw₀ : eval a I (w₀ : WeilHilbertBeforeContact a) = 0 := LinearMap.mem_ker.mp w₀.property
  refine ⟨(w₀ : WeilHilbertBeforeContact a) + (c' / φ) • evalVector a I, ?_⟩
  have hc : anchorCoeff a I ((w₀ : WeilHilbertBeforeContact a) + (c' / φ) • evalVector a I) =
      c' / φ := by
    rw [map_add, map_smul, anchorCoeff_evalVector, anchorCoeff_apply, hw₀, mul_zero, zero_add,
      smul_eq_mul, mul_one]
  have hk : anchorToKernel a I ((w₀ : WeilHilbertBeforeContact a) + (c' / φ) • evalVector a I) =
      w₀ := by
    apply Subtype.ext
    rw [anchorToKernel_coe, hc]
    abel
  rw [boundaryLinear_apply, hk, hc]
  have hmove : (zeroMove a I w₀ : WeilHilbertBeforeContact a) =
      y - c' • evalVector a (star I) := by
    rw [show zeroMove a I w₀ = w from (zeroMove a I).apply_symm_apply w]
    rfl
  rw [hmove, mul_div_cancel₀ c' hφ0, sub_add_cancel]

/-- The unitary extension of zero-moving at `i` with boundary phase `φ`. -/
def boundaryUnitary {φ : ℂ} (hφ : ‖φ‖ = 1) :
    WeilHilbertBeforeContact a ≃ₗᵢ[ℂ] WeilHilbertBeforeContact a :=
  LinearIsometryEquiv.ofSurjective ⟨boundaryLinear a φ, norm_boundaryLinear a hφ⟩
    (boundaryLinear_surjective a hφ)

theorem boundaryUnitary_apply {φ : ℂ} (hφ : ‖φ‖ = 1) (x : WeilHilbertBeforeContact a) :
    boundaryUnitary a hφ x = boundaryLinear a φ x := rfl

/-- The companion function of phase `φ`. -/
def companion (φ z : ℂ) : ℂ :=
  φ * conj (hermiteBiehler a (conj z)) - hermiteBiehler a z

theorem kernel_star_I (z : ℂ) : kernel a (star I) z = kernel a (-I) z := by
  rw [star_I]

/-- Fourier law of the boundary unitary. -/
theorem sub_I_mul_fourier_boundaryLinear (φ : ℂ) (x : WeilHilbertBeforeContact a) (z : ℂ) :
    (z - I) * fourier a (boundaryLinear a φ x) z =
      (z + I) * fourier a x z + anchorCoeff a I x * companion a φ z := by
  let c := anchorCoeff a I x
  let w := anchorToKernel a I x
  have hZ := zeroMove_fourier a I z w
  rw [sub_star_I] at hZ
  have hw : fourier a (w : WeilHilbertBeforeContact a) z = fourier a x z - c * kernel a I z := by
    change eval a z (x - c • evalVector a I) = _
    rw [map_sub, map_smul]
    rfl
  have hB : fourier a (boundaryLinear a φ x) z =
      fourier a (zeroMove a I w : WeilHilbertBeforeContact a) z + (φ * c) * kernel a (star I) z := by
    change eval a z (boundaryLinear a φ x) = _
    rw [boundaryLinear_apply, map_add, map_smul]
    rfl
  have hS : companion a φ z = φ * ((z - I) * kernel a (-I) z) - (z + I) * kernel a I z := by
    rw [companion, hermiteBiehler_sharp, hermiteBiehler]
  rw [hB, hS, kernel_star_I]
  rw [hw] at hZ
  linear_combination hZ

/-- The boundary unitary is a finite-rank perturbation of a division by `z - i`. -/
theorem isCompactOperator_boundaryUnitary_sub_one {φ : ℂ} (hφ : ‖φ‖ = 1) :
    IsCompactOperator
      ((((boundaryUnitary a hφ).toContinuousLinearEquiv : WeilHilbertBeforeContact a →L[ℂ] _) - 1 :
        WeilHilbertBeforeContact a →L[ℂ] WeilHilbertBeforeContact a) :
          WeilHilbertBeforeContact a → WeilHilbertBeforeContact a) := by
  let V : WeilHilbertBeforeContact a →L[ℂ] WeilHilbertBeforeContact a :=
    (boundaryUnitary a hφ).toContinuousLinearEquiv
  let R : WeilHilbertBeforeContact a →L[ℂ] WeilHilbertBeforeContact a :=
    (anchorCoeff a I).smulRight (φ • evalVector a (star I) - evalVector a I)
  let T : WeilHilbertBeforeContact a →L[ℂ] WeilHilbertBeforeContact a := V - 1 - R
  have hTapply (x : WeilHilbertBeforeContact a) :
      T x = (zeroMove a I (anchorToKernel a I x) : WeilHilbertBeforeContact a) -
        (anchorToKernel a I x : WeilHilbertBeforeContact a) := by
    change boundaryLinear a φ x - x -
      anchorCoeff a I x • (φ • evalVector a (star I) - evalVector a I) = _
    rw [boundaryLinear_apply, anchorToKernel_coe, smul_sub, smul_smul, mul_comm φ]
    abel
  have hdiv (x : WeilHilbertBeforeContact a) (z : ℂ) :
      (z - I) * fourier a (T x) z =
        2 * I * fourier a (anchorToKernel a I x : WeilHilbertBeforeContact a) z := by
    have hZ := zeroMove_fourier a I z (anchorToKernel a I x)
    rw [sub_star_I] at hZ
    have hsub : fourier a (T x) z =
        fourier a (zeroMove a I (anchorToKernel a I x) : WeilHilbertBeforeContact a) z -
          fourier a (anchorToKernel a I x : WeilHilbertBeforeContact a) z := by
      change eval a z (T x) = _
      rw [hTapply, map_sub]
      rfl
    rw [hsub]
    linear_combination hZ
  obtain ⟨C, hC, hw⟩ := exists_formWeight_le_quadratic
  let A : WeilHilbertBeforeContact a →L[ℂ] suzukiApertureHilbert a.1 :=
    (ccmArchimedeanFormToAperture a.1).comp ((toFormCLM a).comp (anchorProj a I))
  have hA : IsCompactOperator A :=
    (isCompactOperator_ccmArchimedeanFormToAperture a.1).comp_clm _
  let K : ℝ := (‖ccmRestrictedWeilZeroFormOperator a.1‖ + 1) * (2 * Real.sqrt C)
  have hbound (x : WeilHilbertBeforeContact a) : ‖T x‖ ≤ K * ‖A x‖ := by
    have h := toForm_norm_sq_le_of_division a hw (hdiv x)
    have hAx : ccmArchimedeanFormToAperture a.1
        (toForm a (anchorToKernel a I x : WeilHilbertBeforeContact a)) = A x := rfl
    rw [hAx] at h
    have hs : ‖toForm a (T x)‖ ≤ 2 * Real.sqrt C * ‖A x‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      rw [mul_pow, mul_pow, Real.sq_sqrt hC.le]
      linarith only [h]
    calc
      ‖T x‖ ≤ (‖ccmRestrictedWeilZeroFormOperator a.1‖ + 1) * ‖toForm a (T x)‖ :=
        norm_le_toForm a (T x)
      _ ≤ (‖ccmRestrictedWeilZeroFormOperator a.1‖ + 1) * (2 * Real.sqrt C * ‖A x‖) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = K * ‖A x‖ := by
        simp only [K]
        ring
  have hTc : IsCompactOperator T := isCompactOperator_of_norm_le hA hbound
  have hRc : IsCompactOperator R := by
    have h := (isCompactOperator_of_locallyCompactSpace_dom (anchorCoeff a I)).clm_comp
      (ContinuousLinearMap.toSpanSingleton ℂ (φ • evalVector a (star I) - evalVector a I))
    exact h
  have hfun : ((V - 1 : WeilHilbertBeforeContact a →L[ℂ] WeilHilbertBeforeContact a) :
      WeilHilbertBeforeContact a → WeilHilbertBeforeContact a) = T + R := by
    funext x
    change V x - x = (V x - x - R x) + R x
    abel
  change IsCompactOperator ((V - 1 : WeilHilbertBeforeContact a →L[ℂ] WeilHilbertBeforeContact a) :
    WeilHilbertBeforeContact a → WeilHilbertBeforeContact a)
  rw [hfun]
  exact hTc.add hRc

/-! ### The exceptional phase -/

/-- `E` itself never lies in the space: zero-moving would otherwise fail to preserve the norm. -/
theorem not_exists_fourier_eq_hermiteBiehler :
    ¬ ∃ y : WeilHilbertBeforeContact a, ∀ z, fourier a y z = hermiteBiehler a z := by
  rintro ⟨y, hy⟩
  have hy0 : eval a (star I) y = 0 := by
    change fourier a y (star I) = 0
    rw [hy, hermiteBiehler, star_I, neg_add_cancel, zero_mul]
  let y' : evaluationKernel a (star I) := ⟨y, LinearMap.mem_ker.mpr hy0⟩
  let b : evaluationKernel a I := (zeroMove a I).symm y'
  have hmove (z : ℂ) : (z - I) * fourier a y z =
      (z + I) * fourier a (b : WeilHilbertBeforeContact a) z := by
    have h := zeroMove_fourier a I z b
    rw [show zeroMove a I b = y' from (zeroMove a I).apply_symm_apply y', sub_star_I] at h
    exact h
  have hb (z : ℂ) : fourier a (b : WeilHilbertBeforeContact a) z = (z - I) * kernel a I z := by
    have hcont := (differentiable_fourier a (b : WeilHilbertBeforeContact a)).continuous
    have hcont2 : Continuous fun z : ℂ => (z - I) * kernel a I z :=
      (continuous_id.sub continuous_const).mul (differentiable_fourier a (evalVector a I)).continuous
    have heq := hcont.ext_on (dense_compl_singleton (-I : ℂ)) hcont2 (by
      intro w hw
      have hne : w + I ≠ 0 := fun h0 => hw (eq_neg_of_add_eq_zero_left h0)
      apply mul_left_cancel₀ hne
      have h := hmove w
      rw [hy, hermiteBiehler] at h
      linear_combination -h)
    exact congrFun heq z
  have hyb : y = (b : WeilHilbertBeforeContact a) + (2 * I) • evalVector a I := by
    apply fourier_injective a
    funext z
    change fourier a y z = eval a z ((b : WeilHilbertBeforeContact a) + (2 * I) • evalVector a I)
    rw [map_add, map_smul]
    change fourier a y z = fourier a (b : WeilHilbertBeforeContact a) z + (2 * I) • kernel a I z
    rw [hy, hb, hermiteBiehler, smul_eq_mul]
    ring
  have hn := norm_sq_add_smul_evalVector a (κ := I) (y := (b : WeilHilbertBeforeContact a))
    (LinearMap.mem_ker.mp b.property) (2 * I)
  rw [← hyb] at hn
  have hbn : ‖(b : WeilHilbertBeforeContact a)‖ = ‖y‖ := (zeroMove a I).symm.norm_map y'
  rw [hbn] at hn
  have hpos : 0 < ‖evalVector a I‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (evalVector_ne_zero a I)) 2
  have h2 : ‖(2 * I : ℂ)‖ ^ 2 = 4 := by
    rw [norm_mul, Complex.norm_I, Complex.norm_ofNat]
    norm_num
  rw [h2] at hn
  linarith only [hn, hpos]

/-- The companion of phase `φ` lies in the space. -/
def IsExceptionalPhase (φ : ℂ) : Prop :=
  ∃ y : WeilHilbertBeforeContact a, ∀ z, fourier a y z = companion a φ z

/-- There is at most one exceptional phase. -/
theorem not_isExceptionalPhase_of_ne {φ₁ φ₂ : ℂ} (hne : φ₁ ≠ φ₂)
    (h₁ : IsExceptionalPhase a φ₁) : ¬ IsExceptionalPhase a φ₂ := by
  rintro ⟨y₂, hy₂⟩
  obtain ⟨y₁, hy₁⟩ := h₁
  have hd : φ₁ - φ₂ ≠ 0 := sub_ne_zero.mpr hne
  refine not_exists_fourier_eq_hermiteBiehler a
    ⟨(φ₁ - φ₂)⁻¹ • (φ₂ • y₁ - φ₁ • y₂), fun z => ?_⟩
  change eval a z _ = _
  rw [map_smul, map_sub, map_smul, map_smul]
  change (φ₁ - φ₂)⁻¹ • (φ₂ • fourier a y₁ z - φ₁ • fourier a y₂ z) = _
  rw [hy₁, hy₂]
  simp only [companion, smul_eq_mul]
  field_simp
  ring

theorem exists_not_isExceptionalPhase :
    ∃ φ : ℂ, ‖φ‖ = 1 ∧ ¬ IsExceptionalPhase a φ := by
  by_cases h : IsExceptionalPhase a 1
  · exact ⟨-1, by simp, not_isExceptionalPhase_of_ne a (by norm_num) h⟩
  · exact ⟨1, by simp, h⟩

/-! ### Eigenvectors are reproducing kernels at real zeros of the companion -/

/-- The real zeros of the companion of phase `φ`. -/
def samplingSet (φ : ℂ) : Set ℝ := {t | companion a φ (t : ℂ) = 0}

/-- Christoffel–Darboux at a real zero of the companion. -/
theorem conj_mul_companion_of_mem {φ : ℂ} {t : ℝ} (ht : t ∈ samplingSet a φ) (z : ℂ) :
    conj (hermiteBiehler a (t : ℂ)) * companion a φ z =
      2 * I * (‖evalVector a I‖ : ℂ) ^ 2 * (z - t) * kernel a (t : ℂ) z := by
  have hCD := kernel_christoffelDarboux a (t : ℂ) z
  rw [Complex.conj_ofReal] at hCD
  have hS : φ * conj (hermiteBiehler a (t : ℂ)) = hermiteBiehler a (t : ℂ) := by
    have h : companion a φ (t : ℂ) = 0 := ht
    rw [companion, Complex.conj_ofReal, sub_eq_zero] at h
    exact h
  rw [companion]
  linear_combination -hCD + conj (hermiteBiehler a (conj z)) * hS

theorem kernel_eq_zero_of_mem {φ : ℂ} {t t' : ℝ} (ht : t ∈ samplingSet a φ)
    (ht' : t' ∈ samplingSet a φ) (hne : t ≠ t') : kernel a (t : ℂ) (t' : ℂ) = 0 := by
  have h := conj_mul_companion_of_mem a ht (t' : ℂ)
  have h0 : companion a φ (t' : ℂ) = 0 := ht'
  rw [h0, mul_zero] at h
  have hd : ((t' : ℂ) - t) ≠ 0 :=
    sub_ne_zero.mpr (Complex.ofReal_injective.ne hne.symm)
  have hc : 2 * I * (‖evalVector a I‖ : ℂ) ^ 2 * ((t' : ℂ) - t) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sq_norm_evalVector_ne a I)) hd
  exact (mul_eq_zero.mp h.symm).resolve_left hc

/-- Every eigenvector of a non-exceptional boundary unitary is a reproducing kernel at a real zero
of the companion. -/
theorem exists_eq_smul_of_eigenvector {φ : ℂ} (hE : ¬ IsExceptionalPhase a φ)
    (hφ : ‖φ‖ = 1) {x : WeilHilbertBeforeContact a} (hx : x ≠ 0) {μ : ℂ}
    (hμ : boundaryLinear a φ x = μ • x) :
    ∃ t ∈ samplingSet a φ, ∃ l : ℂ, x = l • evalVector a (t : ℂ) := by
  let F := fourier a x
  have hFc : Continuous F := (differentiable_fourier a x).continuous
  let c := anchorCoeff a I x
  have hstar (z : ℂ) : (z - I) * (μ * F z) = (z + I) * F z + c * companion a φ z := by
    have h := sub_I_mul_fourier_boundaryLinear a φ x z
    rw [hμ] at h
    have hsmul : fourier a (μ • x) z = μ * F z := by
      change eval a z (μ • x) = _
      rw [map_smul]
      rfl
    rw [hsmul] at h
    exact h
  have hunit : ‖μ‖ = 1 := by
    have h := norm_boundaryLinear a hφ x
    rw [hμ, norm_smul] at h
    exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hx) (h.trans (one_mul _).symm)
  have hμ1 : μ ≠ 1 ∨ c = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, hc⟩ := hcon
    apply hE
    refine ⟨(-(2 * I) / c) • x, fun z => ?_⟩
    change eval a z _ = _
    rw [map_smul, smul_eq_mul]
    have h := hstar z
    rw [h1] at h
    change -(2 * I) / c * F z = _
    rw [div_mul_eq_mul_div, div_eq_iff hc]
    linear_combination h
  by_cases hμ1' : μ = 1
  · -- With `μ = 1` the anchor coefficient vanishes, which forces `x = 0`.
    have hc : c = 0 := hμ1.resolve_left (not_not.mpr hμ1')
    exfalso
    apply hx
    apply eq_zero_of_fourier_eq_zero a
    intro z
    have h := hstar z
    rw [hμ1', hc] at h
    have h2 : -(2 * I) * F z = 0 := by linear_combination h
    have hI : -(2 * I) ≠ 0 := by simp
    exact (mul_eq_zero.mp h2).resolve_left hI
  have hd : μ - 1 ≠ 0 := sub_ne_zero.mpr hμ1'
  have hconjμ : conj μ * μ = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hunit]
    norm_num
  have hdc : conj μ - 1 ≠ 0 := by
    intro h
    apply hd
    have h1 : conj μ = 1 := sub_eq_zero.mp h
    rw [h1, one_mul] at hconjμ
    rw [hconjμ, sub_self]
  -- The eigenvalue corresponds to the real point `t = i(μ + 1)/(μ - 1)`.
  let T₀ : ℂ := I * (μ + 1) / (μ - 1)
  have hT₀ : conj T₀ = T₀ := by
    simp only [T₀, map_div₀, map_mul, map_add, map_sub, map_one, Complex.conj_I]
    rw [div_eq_div_iff hdc hd]
    linear_combination (-2 * I) * hconjμ
  let t : ℝ := T₀.re
  have htT : (t : ℂ) = T₀ :=
    Complex.ext (by simp only [t, Complex.ofReal_re])
      (by rw [Complex.ofReal_im]; exact (Complex.conj_eq_iff_im.mp hT₀).symm)
  have hmulT : (μ - 1) * T₀ = I * (μ + 1) := mul_div_cancel₀ _ hd
  have hfactor (z : ℂ) : (μ - 1) * (z - t) * F z = c * companion a φ z := by
    have h := hstar z
    rw [htT]
    linear_combination h - F z * hmulT
  have hc0 : c ≠ 0 := by
    intro hc
    apply hx
    apply eq_zero_of_fourier_eq_zero a
    intro z
    have hzero := hFc.ext_on (dense_compl_singleton (t : ℂ))
        (continuous_const : Continuous fun _ : ℂ => (0 : ℂ)) (by
      intro w hw
      have h := hfactor w
      rw [hc, zero_mul] at h
      have hne : (μ - 1) * (w - t) ≠ 0 := mul_ne_zero hd (sub_ne_zero.mpr hw)
      exact (mul_eq_zero.mp h).resolve_left hne)
    exact congrFun hzero z
  have ht : t ∈ samplingSet a φ := by
    have h := hfactor (t : ℂ)
    rw [sub_self, mul_zero, zero_mul] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hc0
  have hE0 : conj (hermiteBiehler a (t : ℂ)) ≠ 0 :=
    (map_ne_zero _).mpr (hermiteBiehler_ne_zero_ofReal a t)
  have hCD := conj_mul_companion_of_mem a ht
  let l : ℂ := 2 * I * (‖evalVector a I‖ : ℂ) ^ 2 * c /
    (conj (hermiteBiehler a (t : ℂ)) * (μ - 1))
  refine ⟨t, ht, l, ?_⟩
  apply fourier_injective a
  have hcont2 : Continuous fun z => l * kernel a (t : ℂ) z :=
    continuous_const.mul (differentiable_fourier a (evalVector a (t : ℂ))).continuous
  have heq : F = fun z => l * kernel a (t : ℂ) z :=
    hFc.ext_on (dense_compl_singleton (t : ℂ)) hcont2 (by
      intro w hw
      have hw' : w - t ≠ 0 := sub_ne_zero.mpr hw
      have h1 := hfactor w
      have h2 := hCD w
      have hl : l * (conj (hermiteBiehler a (t : ℂ)) * (μ - 1)) =
          2 * I * (‖evalVector a I‖ : ℂ) ^ 2 * c := div_mul_cancel₀ _ (mul_ne_zero hE0 hd)
      change F w = l * kernel a (t : ℂ) w
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hE0 hd) hw')
      linear_combination (conj (hermiteBiehler a (t : ℂ))) * h1 + c * h2 -
        (w - t) * kernel a (t : ℂ) w * hl)
  funext z
  change F z = eval a z (l • evalVector a (t : ℂ))
  rw [map_smul, congrFun heq z]
  rfl

/-! ### The sampling basis -/

/-- The normalized reproducing kernel at a real point. -/
def samplingVector (t : ℝ) : WeilHilbertBeforeContact a :=
  ((‖evalVector a (t : ℂ)‖ : ℂ)⁻¹) • evalVector a (t : ℂ)

theorem orthonormal_samplingVector (φ : ℂ) :
    Orthonormal ℂ (fun t : samplingSet a φ => samplingVector a (t : ℝ)) := by
  refine ⟨fun t => ?_, fun t t' hne => ?_⟩
  · have hv := norm_ne_zero_iff.mpr (evalVector_ne_zero a ((t : ℝ) : ℂ))
    change ‖samplingVector a (t : ℝ)‖ = 1
    rw [samplingVector, norm_smul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_cancel₀ hv]
  · have hne' : (t : ℝ) ≠ (t' : ℝ) := fun h => hne (Subtype.ext h)
    have h0 := kernel_eq_zero_of_mem a t'.2 t.2 hne'.symm
    simp only [samplingVector, inner_smul_left, inner_smul_right]
    rw [inner_evalVector]
    change _ * (_ * kernel a ((t' : ℝ) : ℂ) ((t : ℝ) : ℂ)) = 0
    rw [h0, mul_zero, mul_zero]

/-- The closed span of the sampling kernels is the whole space. -/
theorem samplingVector_total {φ : ℂ} (hφ : ‖φ‖ = 1) (hE : ¬ IsExceptionalPhase a φ) :
    ⊤ ≤ (Submodule.span ℂ (Set.range fun t : samplingSet a φ =>
      samplingVector a (t : ℝ))).topologicalClosure := by
  rw [top_le_iff, Submodule.topologicalClosure_eq_top_iff]
  set Sp := Submodule.span ℂ (Set.range fun t : samplingSet a φ => samplingVector a (t : ℝ))
    with hSp
  have hbot := orthogonal_iSup_eigenspaces_of_unitary (boundaryUnitary a hφ)
    (isCompactOperator_boundaryUnitary_sub_one a hφ)
  have hle : (⨆ μ : ℂ, Module.End.eigenspace
      ((boundaryUnitary a hφ).toLinearEquiv.toLinearMap : Module.End ℂ _) μ) ≤ Sp := by
    refine iSup_le fun μ x hx => ?_
    by_cases hx0 : x = 0
    · rw [hx0]
      exact Sp.zero_mem
    have hμ : boundaryLinear a φ x = μ • x := Module.End.mem_eigenspace_iff.mp hx
    obtain ⟨t, ht, l, rfl⟩ := exists_eq_smul_of_eigenvector a hE hφ hx0 hμ
    have hv : evalVector a (t : ℂ) = (‖evalVector a (t : ℂ)‖ : ℂ) • samplingVector a t := by
      have hne : (‖evalVector a (t : ℂ)‖ : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (evalVector_ne_zero a (t : ℂ)))
      rw [samplingVector, smul_smul, mul_inv_cancel₀ hne, one_smul]
    rw [hv, smul_smul]
    exact Sp.smul_mem _ (Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩)
  rw [eq_bot_iff, ← hbot]
  exact Submodule.orthogonal_le hle

/-- **The sampling basis of a non-exceptional phase.** -/
def samplingBasis {φ : ℂ} (hφ : ‖φ‖ = 1) (hE : ¬ IsExceptionalPhase a φ) :
    HilbertBasis (samplingSet a φ) ℂ (WeilHilbertBeforeContact a) :=
  HilbertBasis.mk (orthonormal_samplingVector a φ) (samplingVector_total a hφ hE)

theorem samplingBasis_apply {φ : ℂ} (hφ : ‖φ‖ = 1) (hE : ¬ IsExceptionalPhase a φ)
    (t : samplingSet a φ) : samplingBasis a hφ hE t = samplingVector a (t : ℝ) :=
  congrFun (HilbertBasis.coe_mk _ _) t

/-- **Polarized de Branges sampling formula.** -/
theorem hasSum_sampling {φ : ℂ} (hφ : ‖φ‖ = 1) (hE : ¬ IsExceptionalPhase a φ)
    (x y : WeilHilbertBeforeContact a) :
    HasSum (fun t : samplingSet a φ =>
      ((‖evalVector a ((t : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ *
        (conj (fourier a x ((t : ℝ) : ℂ)) * fourier a y ((t : ℝ) : ℂ)))
      (inner ℂ x y) := by
  have h := (samplingBasis a hφ hE).hasSum_inner_mul_inner x y
  have hfun : (fun t : samplingSet a φ =>
      ((‖evalVector a ((t : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ *
        (conj (fourier a x ((t : ℝ) : ℂ)) * fourier a y ((t : ℝ) : ℂ))) =
      fun t => inner ℂ x (samplingBasis a hφ hE t) * inner ℂ (samplingBasis a hφ hE t) y := by
    funext t
    have h1 : inner ℂ x (evalVector a ((t : ℝ) : ℂ)) = conj (fourier a x ((t : ℝ) : ℂ)) := by
      rw [← inner_conj_symm, inner_evalVector]
      rfl
    have h2 : inner ℂ (evalVector a ((t : ℝ) : ℂ)) y = fourier a y ((t : ℝ) : ℂ) :=
      inner_evalVector a _ y
    rw [samplingBasis_apply, samplingVector, inner_smul_right, inner_smul_left, h1, h2, map_inv₀,
      Complex.conj_ofReal, Complex.ofReal_pow, sq, mul_inv]
    ring
  rw [hfun]
  exact h

/-- **De Branges sampling formula.** The Weil norm is the weighted energy on the zeros of a
non-exceptional companion, with atoms `1 / K(t,t)`. -/
theorem hasSum_norm_sq_sampling {φ : ℂ} (hφ : ‖φ‖ = 1) (hE : ¬ IsExceptionalPhase a φ)
    (x : WeilHilbertBeforeContact a) :
    HasSum (fun t : samplingSet a φ =>
      (‖evalVector a ((t : ℝ) : ℂ)‖ ^ 2)⁻¹ * ‖fourier a x ((t : ℝ) : ℂ)‖ ^ 2) (‖x‖ ^ 2) := by
  have h := hasSum_sampling a hφ hE x x
  have hv : inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hv] at h
  rw [← Complex.hasSum_ofReal]
  have hfun : (fun t : samplingSet a φ =>
      (((‖evalVector a ((t : ℝ) : ℂ)‖ ^ 2)⁻¹ * ‖fourier a x ((t : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ)) =
      fun t : samplingSet a φ => ((‖evalVector a ((t : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ *
        (conj (fourier a x ((t : ℝ) : ℂ)) * fourier a x ((t : ℝ) : ℂ)) := by
    funext t
    rw [Complex.conj_mul']
    push_cast
    rfl
  rw [hfun]
  exact h

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact

#print axioms GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact.isCompactOperator_boundaryUnitary_sub_one
#print axioms GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact.not_exists_fourier_eq_hermiteBiehler
#print axioms GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact.hasSum_sampling
#print axioms GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact.hasSum_norm_sq_sampling
