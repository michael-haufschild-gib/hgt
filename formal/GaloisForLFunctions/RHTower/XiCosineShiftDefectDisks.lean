import GaloisForLFunctions.RHTower.XiCosineShiftHeatStrip
import GaloisForLFunctions.RHTower.ZeroFreeRegionFromFour
import GaloisForLFunctions.RHTower.XiEndpointSchwarzPairHeightGap
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion

/-!
# Defect disks of the cosine shift

For `h > 0` let `A_h(z) = (Ξ(z + ih) + Ξ(z − ih))/2 = cos(hD)Ξ`. De Bruijn's strip theorem confines
the zeros of `A_h` to `(Im z)² ≤ max(1/4 − h², 0)`. This file proves a local form of it.

* `exists_zero_mem_defectDisk`: let `f` be entire, even, real, of order one, with `f(0) ≠ 0`. If
  `Im z ≠ 0` and `f(z + iλ) + f(z − iλ) = 0`, then `f` has a zero `ζ` with
  `(Re ζ − Re z)² + (Im z)² + λ² ≤ (Im ζ)²`.
* `cosineShift_nonreal_zero_mem_defectDisk`: every non-real zero `z` of `A_h` lies in a closed
  *defect disk*. The disk is centred at the real point `Re w` of a zero `w` of `Ξ` with
  `|Im w| > h`, and has radius `√((Im w)² − h²)`. In `s = ½ + iz` coordinates, `w` is a zero `ρ`
  of `ξ` with `|Re ρ − ½| > h`. A non-real zero of `cos(hD)Ξ` therefore exists only within
  vertical distance `√((Re ρ − ½)² − h²) < ½` of such a zero.
* `cosineShift_zero_real_of_abs_re_le`: with the zero-free region `Re ρ ≤ 1 − 1/(100 log Im ρ)`
  (`Im ρ ≥ 4`), for `0 < h < ½` every zero `z` of `A_h` with
  `|Re z| + ½ ≤ exp(1/(100(½ − h)))` is real. The window of real zeros grows without bound as
  `h → ½⁻`, and the bound needs no hypothesis.

The radius is sharp for an isolated zero quadruple. For `q(z) = (z − γ)² + b²`,
`cos(hD)q = (z − γ)² + b² − h²` has the zeros `γ ± i√(b² − h²)` on the disk boundary.

Mechanism: the conjugate-pair comparison of de Bruijn's contraction
(`DeBruijn.add_shift_ne_zero`) only needs `X² + Y² + λ² > b²` for each zero, with
`X = Re ζ − Re z`. It does not need the global strip bound `b² < Y² + λ²`.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.EntireZeroDivisor

namespace RHTower.DeBruijn

noncomputable section

variable {f : ℂ → ℂ}

/-! ## The local pair inequality -/

/-- A conjugate pair `ζ, ζ̄` with `(Im ζ)² < (Re ζ − Re z)² + (Im z)² + λ²`, `Im z > 0`, is strictly
farther from `z + iλ` than from `z − iλ`. -/
theorem pair_dist_lt_local {z ζ : ℂ} {lam : ℝ} (hlam : 0 < lam) (hz : 0 < z.im)
    (hb : ζ.im ^ 2 < (ζ.re - z.re) ^ 2 + z.im ^ 2 + lam ^ 2) :
    ‖ζ - (z - lam * I)‖ * ‖(starRingEnd ℂ) ζ - (z - lam * I)‖ <
      ‖ζ - (z + lam * I)‖ * ‖(starRingEnd ℂ) ζ - (z + lam * I)‖ := by
  set X := ζ.re - z.re
  set Y := z.im
  set b := ζ.im
  have hsq : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := fun w => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have e1 : ‖ζ - (z - lam * I)‖ ^ 2 = X ^ 2 + (b - Y + lam) ^ 2 := by
    rw [hsq]; simp [X, Y, b]; ring
  have e2 : ‖(starRingEnd ℂ) ζ - (z - lam * I)‖ ^ 2 = X ^ 2 + (b + Y - lam) ^ 2 := by
    rw [hsq]; simp [X, Y, b]; ring
  have e3 : ‖ζ - (z + lam * I)‖ ^ 2 = X ^ 2 + (b - Y - lam) ^ 2 := by
    rw [hsq]; simp [X, Y, b]; ring
  have e4 : ‖(starRingEnd ℂ) ζ - (z + lam * I)‖ ^ 2 = X ^ 2 + (b + Y + lam) ^ 2 := by
    rw [hsq]; simp [X, Y, b]; ring
  have hdiff : (‖ζ - (z + lam * I)‖ * ‖(starRingEnd ℂ) ζ - (z + lam * I)‖) ^ 2 -
      (‖ζ - (z - lam * I)‖ * ‖(starRingEnd ℂ) ζ - (z - lam * I)‖) ^ 2 =
      8 * Y * lam * (X ^ 2 + Y ^ 2 + lam ^ 2 - b ^ 2) := by
    rw [mul_pow, mul_pow, e1, e2, e3, e4]
    ring
  have hpos : 0 < 8 * Y * lam * (X ^ 2 + Y ^ 2 + lam ^ 2 - b ^ 2) := by
    have : 0 < X ^ 2 + Y ^ 2 + lam ^ 2 - b ^ 2 := by linarith
    positivity
  refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
  linarith

/-- **Local paired factor comparison.** -/
theorem norm_weierstrassE1_pair_lt_local {ζ z : ℂ} (hζ : ζ ≠ 0) {lam : ℝ} (hlam : 0 < lam)
    (hz : 0 < z.im) (hb : ζ.im ^ 2 < (ζ.re - z.re) ^ 2 + z.im ^ 2 + lam ^ 2) :
    ‖weierstrassE1 ((z - lam * I) / ζ)‖ * ‖weierstrassE1 ((z - lam * I) / (starRingEnd ℂ) ζ)‖ <
      ‖weierstrassE1 ((z + lam * I) / ζ)‖ *
        ‖weierstrassE1 ((z + lam * I) / (starRingEnd ℂ) ζ)‖ := by
  rw [norm_weierstrassE1_pair hζ, norm_weierstrassE1_pair hζ]
  have hre : (z - lam * I).re = (z + lam * I).re := by simp
  rw [hre]
  have hζn : 0 < ‖ζ‖ ^ 2 := by have := norm_pos_iff.mpr hζ; positivity
  exact mul_lt_mul_of_pos_right (div_lt_div_of_pos_right (pair_dist_lt_local hlam hz hb) hζn)
    (Real.exp_pos _)

/-- The paired log-ratio of genus-one factors is positive under the local condition. -/
theorem log_ratio_pair_pos_local
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) {lam : ℝ} (hlam : 0 < lam)
    {z : ℂ} (hz : 0 < z.im)
    (hloc : ∀ ζ, f ζ = 0 → ζ.im ^ 2 < (ζ.re - z.re) ^ 2 + z.im ^ 2 + lam ^ 2)
    (hu : f (z - lam * I) ≠ 0) (hv : f (z + lam * I) ≠ 0) {ζ : ℂ} (hζ : ζ ≠ 0) (hζz : f ζ = 0) :
    0 < (Real.log ‖weierstrassE1 ((z + lam * I) / ζ)‖ -
        Real.log ‖weierstrassE1 ((z - lam * I) / ζ)‖) +
      (Real.log ‖weierstrassE1 ((z + lam * I) / (starRingEnd ℂ) ζ)‖ -
        Real.log ‖weierstrassE1 ((z - lam * I) / (starRingEnd ℂ) ζ)‖) := by
  have hne : ∀ w : ℂ, f w ≠ 0 → ∀ ξ : ℂ, f ξ = 0 → ξ ≠ 0 → 0 < ‖weierstrassE1 (w / ξ)‖ := by
    intro w hw ξ hξ hξ0
    refine norm_pos_iff.mpr (weierstrassE1_ne_zero ?_)
    intro h1
    rw [div_eq_one_iff_eq hξ0] at h1
    exact hw (h1 ▸ hξ)
  have hζcz : f ((starRingEnd ℂ) ζ) = 0 := by rw [hconj, hζz, map_zero]
  have hζc0 : (starRingEnd ℂ) ζ ≠ 0 := (map_ne_zero _).mpr hζ
  have key := norm_weierstrassE1_pair_lt_local hζ hlam hz (hloc ζ hζz)
  have p1 := hne _ hu ζ hζz hζ
  have p2 := hne _ hu _ hζcz hζc0
  have p3 := hne _ hv ζ hζz hζ
  have p4 := hne _ hv _ hζcz hζc0
  have hlog := Real.log_lt_log (mul_pos p1 p2) key
  rw [Real.log_mul p1.ne' p2.ne', Real.log_mul p3.ne' p4.ne'] at hlog
  linarith

/-- **Local strict modulus increase across the shift.** -/
theorem norm_sub_shift_lt_local {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ)
    (hf0 : f 0 ≠ 0) (heven : ∀ z, f (-z) = f z)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 0 < z.im)
    (hloc : ∀ ζ, f ζ = 0 → ζ.im ^ 2 < (ζ.re - z.re) ^ 2 + z.im ^ 2 + lam ^ 2)
    (hne : Nonempty (ZeroCopy f)) (hu : f (z - lam * I) ≠ 0) (hv : f (z + lam * I) ≠ 0) :
    ‖f (z - lam * I)‖ < ‖f (z + lam * I)‖ := by
  have hsum := OrderOneHadamard.summable_inv_sq_zeroCopyPoint hC hf hf0 hbound
  have hane := zeroCopyPoint_ne_zero hf hf0
  rw [norm_eq_exp_tsum hC hf hf0 heven hbound hu, norm_eq_exp_tsum hC hf hf0 heven hbound hv]
  refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr ?_) (norm_pos_iff.mpr hf0)
  have hsu := summable_log_norm_weierstrassE1 hsum (z - lam * I)
  have hsv := summable_log_norm_weierstrassE1 hsum (z + lam * I)
  rw [← sub_pos, ← hsv.tsum_sub hsu]
  refine tsum_pos_of_involution (hsv.sub hsu) (zeroCopyConj hf hconj) (fun q => ?_)
  rw [zeroCopyPoint_conj hf hconj q]
  exact log_ratio_pair_pos_local hconj hlam hz hloc hu hv (hane q) (apply_zeroCopyPoint hf q)

/-- **Local shift contraction.** If every zero `ζ` of `f` satisfies
`(Im ζ)² < (Re ζ − Re z)² + (Im z)² + λ²` and `Im z ≠ 0`, then `f(z + iλ) + f(z − iλ) ≠ 0`. -/
theorem add_shift_ne_zero_local {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ)
    (hf0 : f 0 ≠ 0) (heven : ∀ z, f (-z) = f z)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : z.im ≠ 0)
    (hloc : ∀ ζ, f ζ = 0 → ζ.im ^ 2 < (ζ.re - z.re) ^ 2 + z.im ^ 2 + lam ^ 2) :
    f (z + lam * I) + f (z - lam * I) ≠ 0 := by
  have upper : ∀ z : ℂ, 0 < z.im →
      (∀ ζ, f ζ = 0 → ζ.im ^ 2 < (ζ.re - z.re) ^ 2 + z.im ^ 2 + lam ^ 2) →
      f (z + lam * I) + f (z - lam * I) ≠ 0 := by
    intro z hz hloc
    have hv : f (z + lam * I) ≠ 0 := by
      intro h0
      have h1 := hloc _ h0
      have him : (z + lam * I).im = z.im + lam := by simp
      have hre : (z + lam * I).re = z.re := by simp
      rw [him, hre, sub_self] at h1
      nlinarith
    by_cases hu : f (z - lam * I) = 0
    · rw [hu, add_zero]; exact hv
    rcases isEmpty_or_nonempty (ZeroCopy f) with hempty | hne
    · have hford := analyticOrderAt_ne_top_of_ne_zero hf hf0
      have hfac := OrderOneHadamard.eq_const_mul_hadamardProduct_of_even hC hf hf0 hford heven
        hbound
      have hconst : ∀ w, f w = f 0 := by
        intro w
        rw [hfac w]
        change f 0 * ∏' q : ZeroCopy f, weierstrassE1 (w / zeroCopyPoint f q) = f 0
        rw [tprod_empty, mul_one]
      rw [hconst (z + lam * I), hconst (z - lam * I)]
      intro h
      exact hf0 (by linear_combination h / 2)
    · intro hsum0
      have hlt := norm_sub_shift_lt_local hC hf hf0 heven hconj hbound hlam hz hloc hne hu hv
      have : f (z + lam * I) = -f (z - lam * I) := by linear_combination hsum0
      rw [this, norm_neg] at hlt
      exact lt_irrefl _ hlt
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have h := upper ((starRingEnd ℂ) z) (by simpa using hneg) (by
      intro ζ hζ
      have := hloc ζ hζ
      simpa using this)
    intro hsum0
    apply h
    have e1 : (starRingEnd ℂ) z + lam * I = (starRingEnd ℂ) (z - lam * I) := by
      rw [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    have e2 : (starRingEnd ℂ) z - lam * I = (starRingEnd ℂ) (z + lam * I) := by
      rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    rw [e1, e2, hconj, hconj, ← map_add, add_comm, hsum0, map_zero]
  · exact upper z hpos hloc

/-- **Defect disks.** A non-real zero `z` of `f(· + iλ) + f(· − iλ)` lies in the closed disk
centred at `Re ζ` of radius `√((Im ζ)² − λ²)` for some zero `ζ` of `f`. -/
theorem exists_zero_mem_defectDisk {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ)
    (hf0 : f 0 ≠ 0) (heven : ∀ z, f (-z) = f z)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : z.im ≠ 0)
    (hsum : f (z + lam * I) + f (z - lam * I) = 0) :
    ∃ ζ, f ζ = 0 ∧ (ζ.re - z.re) ^ 2 + z.im ^ 2 + lam ^ 2 ≤ ζ.im ^ 2 := by
  by_contra hcon
  refine add_shift_ne_zero_local hC hf hf0 heven hconj hbound hlam hz (fun ζ hζ => ?_) hsum
  by_contra hle
  exact hcon ⟨ζ, hζ, not_lt.mp hle⟩

/-! ## The cosine shift of `Ξ` -/

theorem cosTransform_riemannKernel_eq_XiC : cosTransform riemannKernelReal = XiC := by
  funext w
  rw [cosTransform_riemannKernel, XiC, mul_comm]

theorem XiC_neg' (w : ℂ) : XiC (-w) = XiC w := by
  rw [← cosTransform_riemannKernel_eq_XiC]
  exact riemannKernel_superExp.cosTransform_neg w

theorem XiC_conj' (w : ℂ) : XiC ((starRingEnd ℂ) w) = (starRingEnd ℂ) (XiC w) := by
  rw [← cosTransform_riemannKernel_eq_XiC]
  exact riemannKernel_superExp.cosTransform_conj w

/-- **Defect disks of `cos(hD)Ξ`.** For `h > 0`, every non-real zero `z` of
`(Ξ(z + ih) + Ξ(z − ih))/2` has a zero `w` of `Ξ` with `(Re w − Re z)² + (Im z)² + h² ≤ (Im w)²`.
In particular `|Im w| > h`: the zero `ρ = ½ + iw` of `ξ` has `|Re ρ − ½| > h`. -/
theorem cosineShift_nonreal_zero_mem_defectDisk {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : z.im ≠ 0)
    (h0 : (XiC (z + h * I) + XiC (z - h * I)) / 2 = 0) :
    ∃ w, XiC w = 0 ∧ (w.re - z.re) ^ 2 + z.im ^ 2 + h ^ 2 ≤ w.im ^ 2 := by
  have hg := riemannKernel_superExp
  obtain ⟨C, hC0, hC⟩ := hg.exists_envelope
  have han : AnalyticOnNhd ℂ (cosTransform riemannKernelReal) univ :=
    hg.differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hsum : cosTransform riemannKernelReal (z + h * I) +
      cosTransform riemannKernelReal (z - h * I) = 0 := by
    rw [cosTransform_riemannKernel_eq_XiC]
    linear_combination 2 * h0
  obtain ⟨w, hw, hdisk⟩ := exists_zero_mem_defectDisk hC0 han hg.cosTransform_zero_ne
    hg.cosTransform_neg hg.cosTransform_conj hC hh hz hsum
  rw [cosTransform_riemannKernel_eq_XiC] at hw
  exact ⟨w, hw, hdisk⟩

/-! ## The window of real zeros -/

/-- The zero-free region in `Ξ` coordinates: a zero `w` of `Ξ` with `|Re w| ≥ 4` has
`|Im w| ≤ ½ − 1/(100 log |Re w|)`. -/
theorem abs_im_le_of_XiC_eq_zero {w : ℂ} (hw : XiC w = 0) (h4 : 4 ≤ |w.re|) :
    |w.im| ≤ 1 / 2 - 1 / 100 / Real.log |w.re| := by
  -- one side, at positive real part
  have side : ∀ v : ℂ, XiC v = 0 → 4 ≤ v.re → -v.im ≤ 1 / 2 - 1 / 100 / Real.log v.re := by
    intro v hv hv4
    have hxi : xi (1 / 2 + v * I) = 0 := by rw [← hv, XiC]
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    have him : (q.1 : ℂ).im = v.re := by rw [hq]; simp
    have hre : (q.1 : ℂ).re = 1 / 2 - v.im := by rw [hq]; simp; ring
    have h := xiZeroCopy_zero_free_from_four (q := q) (by rw [him]; exact hv4)
    rw [him, hre] at h
    linarith
  -- reduce to positive real part
  obtain ⟨v, hv, hvre, hvim⟩ : ∃ v : ℂ, XiC v = 0 ∧ v.re = |w.re| ∧ |v.im| = |w.im| := by
    rcases le_or_gt 0 w.re with hpos | hneg
    · exact ⟨w, hw, (abs_of_nonneg hpos).symm, rfl⟩
    · refine ⟨-w, by rw [XiC_neg']; exact hw, ?_, by simp⟩
      simp [abs_of_neg hneg]
  have hvc : XiC ((starRingEnd ℂ) v) = 0 := by rw [XiC_conj', hv, map_zero]
  have h1 := side v hv (by rw [hvre]; exact h4)
  have h2 := side _ hvc (by simp only [Complex.conj_re]; rw [hvre]; exact h4)
  simp only [Complex.conj_re, Complex.conj_im, neg_neg] at h2
  rw [hvre] at h1 h2
  rw [← hvim, abs_le]
  constructor <;> linarith

/-- **Window of real zeros.** For `0 < h < ½`, every zero `z` of `cos(hD)Ξ` with
`|Re z| + ½ ≤ exp(1/(100(½ − h)))` is real. -/
theorem cosineShift_zero_real_of_abs_re_le {h : ℝ} (hh : 0 < h) (hh2 : h < 1 / 2) {z : ℂ}
    (h0 : (XiC (z + h * I) + XiC (z - h * I)) / 2 = 0)
    (hre : |z.re| + 1 / 2 ≤ Real.exp (1 / (100 * (1 / 2 - h)))) : z.im = 0 := by
  by_contra hz
  obtain ⟨w, hw, hdisk⟩ := cosineShift_nonreal_zero_mem_defectDisk hh hz h0
  have hwim : w.im ^ 2 ≤ 1 / 4 := by
    have := riemannKernel_zeros_im_sq_le w (by rw [cosTransform_riemannKernel_eq_XiC]; exact hw)
    exact this
  have hzim : 0 < z.im ^ 2 := by positivity
  -- the zero `w` lies within `½` of `z` horizontally and deeper than `h`
  have hclose : |w.re - z.re| ≤ 1 / 2 := by
    have h1 : (w.re - z.re) ^ 2 ≤ (1 / 2) ^ 2 := by nlinarith
    have := sq_le_sq.mp h1
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
  have hdeep : h < |w.im| := by
    have h1 : h ^ 2 < w.im ^ 2 := by nlinarith [sq_nonneg (w.re - z.re)]
    have := sq_lt_sq.mp h1
    rwa [abs_of_pos hh] at this
  have hwre : 13 / 2 < |w.re| := by
    by_contra hle
    exact XiC_ne_zero_of_abs_re_le_thirteen_halves (not_lt.mp hle) hw
  have hlogpos : 0 < Real.log |w.re| := Real.log_pos (by linarith)
  have hzf := abs_im_le_of_XiC_eq_zero hw (by linarith)
  -- `h < ½ − 1/(100 log |Re w|)`, so `log |Re w| > 1/(100(½ − h))`
  have hgap : 1 / 100 / Real.log |w.re| < 1 / 2 - h := by linarith
  have hlog : 1 / (100 * (1 / 2 - h)) < Real.log |w.re| := by
    have hpos : 0 < 1 / 2 - h := by linarith
    rw [div_lt_iff₀ (by positivity)]
    rw [div_div, div_lt_iff₀ (by positivity)] at hgap
    nlinarith
  have hexp : Real.exp (1 / (100 * (1 / 2 - h))) < |w.re| := by
    rw [← Real.exp_log (show 0 < |w.re| by linarith)]
    exact Real.exp_lt_exp.mpr hlog
  have hwz : |w.re| ≤ |z.re| + 1 / 2 := by
    have := abs_sub_abs_le_abs_sub w.re z.re
    linarith
  linarith

end

end RHTower.DeBruijn
