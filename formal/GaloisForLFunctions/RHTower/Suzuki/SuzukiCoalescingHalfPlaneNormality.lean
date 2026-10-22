import GaloisForLFunctions.Bottcher.DiskSchwarzPick
import GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteApertureHermiteBiehler

/-!
# Coalescing-anchor Schwarz--Pick rate and singular resolvent normality

This module closes the analytic compactness step at a deficiency anchor `ic` that collapses to the
real axis.  For a Schur function `θ` anchored by `θ(ic)=0`, its disk conjugate factors canonically
as `w · dslope f 0 w`; mathlib's removable-singularity theorem proves that the `dslope` factor is
holomorphic at zero.  The project Schwarz--Pick theorem then gives the sharp boundary-one estimate

`‖1-g(w)‖ ≤ (1-κ)(1+‖w‖)/(1-‖w‖)`.

Exact movable-Cayley identities transport a quadratic anchor defect `1-κ ≤ Cc²` into a linear
compact-set estimate `‖1-θ(z)‖ ≤ O(c)`.  Consequently

`(1-θ(z)) / (c(1+θ(z)))`

is uniformly bounded on every fixed upper-half-plane ball after passing to the explicit cofinal
small-anchor tail, and sequential Montel supplies a locally uniform holomorphic subsequence.  No
normal-family premise, boundary regularity assumption, RH hypothesis, or numerical computation is
used.
-/

open Complex Metric Set

namespace RHTower

noncomputable section

theorem norm_one_sub_dslope_le_hyperbolic
    {f : ℂ → ℂ} {κ : ℝ}
    (hfdiff : DifferentiableOn ℂ f (ball 0 1))
    (hfbd : ∀ w ∈ ball (0 : ℂ) 1, ‖f w‖ ≤ 1)
    (hf0 : f 0 = 0)
    (hderiv : deriv f 0 = (κ : ℂ))
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    {w : ℂ} (hw : ‖w‖ < 1) :
    ‖1 - dslope f 0 w‖ ≤
      (1 - κ) * (1 + ‖w‖) / (1 - ‖w‖) := by
  let g : ℂ → ℂ := dslope f 0
  have hball : ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) :=
    ball_mem_nhds _ one_pos
  have hgdiff : DifferentiableOn ℂ g (ball 0 1) := by
    exact (differentiableOn_dslope hball).mpr hfdiff
  have hgbd : ∀ y ∈ ball (0 : ℂ) 1, ‖g y‖ ≤ 1 := by
    intro y hy
    have h := Complex.norm_dslope_le_div_of_mapsTo_ball hfdiff
      (by
        intro z hz
        simpa [mem_closedBall, dist_zero_right, hf0] using hfbd z hz)
      hy
    simpa [g, hf0] using h
  have hg0 : g 0 = (κ : ℂ) := by
    simp [g, hderiv]
  have hgc : ‖g 0‖ < 1 := by
    rw [hg0, norm_real, Real.norm_eq_abs, abs_of_nonneg hκ0]
    exact hκ1
  let η : ℂ := (g w - g 0) / (1 - (starRingEnd ℂ) (g 0) * g w)
  have hwball : w ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_zero_iff] using hw
  have hηle : ‖η‖ ≤ ‖w‖ := by
    have h := Bottcher.blaschke_lift_norm_le_dist_div
      (g := g) (c := 0) (z := w) (R := 1) one_pos hgdiff hgbd hgc hwball
    simpa [η] using h
  have hηlt : ‖η‖ < 1 := lt_of_le_of_lt hηle hw
  have hden : 1 - (starRingEnd ℂ) (g 0) * g w ≠ 0 :=
    Bottcher.one_sub_conj_mul_ne_zero_of_norm_lt_one_norm_le_one hgc (hgbd w hwball)
  have hmob :
      ((g 0) + η) / (1 + (starRingEnd ℂ) (g 0) * η) = g w := by
    simpa [η] using Bottcher.mobius_of_blaschke
      (a := g 0) (w := g w) hgc hden
  have hden2 : 1 + (starRingEnd ℂ) (g 0) * η ≠ 0 :=
    Bottcher.one_add_conj_mul_ne_zero_of_norm_lt_one hgc hηlt
  have hmobBound := Bottcher.one_sub_mobius_norm_le
    (a := g 0) (η := η) hden2
  rw [hmob] at hmobBound
  have hdenLower : 1 - ‖w‖ ≤ ‖1 + (starRingEnd ℂ) (g 0) * η‖ := by
    have hgnorm : ‖g 0‖ = κ := by
      rw [hg0, norm_real, Real.norm_eq_abs, abs_of_nonneg hκ0]
    have hrev := norm_sub_norm_le (1 : ℂ)
      (-((starRingEnd ℂ) (g 0) * η))
    have hmulnorm : ‖(starRingEnd ℂ) (g 0) * η‖ = κ * ‖η‖ := by
      rw [hg0]
      simp [Real.norm_eq_abs, abs_of_nonneg hκ0]
    have hkw : κ * ‖η‖ ≤ ‖w‖ := by
      calc
        κ * ‖η‖ ≤ 1 * ‖η‖ := by
          exact mul_le_mul_of_nonneg_right hκ1.le (norm_nonneg η)
        _ ≤ ‖w‖ := by simpa using hηle
    have : 1 - κ * ‖η‖ ≤
        ‖1 + (starRingEnd ℂ) (g 0) * η‖ := by
      simpa [norm_neg, norm_mul, map_star, hgnorm] using hrev
    linarith
  have hnum : ‖1 - g 0‖ * (1 + ‖η‖) ≤
      (1 - κ) * (1 + ‖w‖) := by
    have hnorm : ‖1 - g 0‖ = 1 - κ := by
      rw [hg0, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hκ1.le)]
    rw [hnorm]
    have hadd : 1 + ‖η‖ ≤ 1 + ‖w‖ := by linarith
    exact mul_le_mul_of_nonneg_left hadd (sub_nonneg.mpr hκ1.le)
  have hdenPos : 0 < 1 - ‖w‖ := sub_pos.mpr hw
  calc
    ‖1 - dslope f 0 w‖ = ‖1 - g w‖ := rfl
    _ ≤ ‖1 - g 0‖ * (1 + ‖η‖) /
        ‖1 + (starRingEnd ℂ) (g 0) * η‖ := hmobBound
    _ ≤ ‖1 - g 0‖ * (1 + ‖η‖) / (1 - ‖w‖) := by
      exact div_le_div_of_nonneg_left (by positivity) hdenPos hdenLower
    _ ≤ (1 - κ) * (1 + ‖w‖) / (1 - ‖w‖) := by
      exact div_le_div_of_nonneg_right hnum hdenPos.le

/-- Cayley chart with movable upper-half-plane anchor `ic`. -/
def suzukiCoalescingCayley (c : ℝ) (z : ℂ) : ℂ :=
  (z - (c : ℂ) * I) / (z + (c : ℂ) * I)

/-- Inverse movable Cayley chart. -/
def suzukiCoalescingCayleyInv (c : ℝ) (w : ℂ) : ℂ :=
  (c : ℂ) * GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w

theorem suzukiCoalescingCayleyInv_im_pos
    {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (suzukiCoalescingCayleyInv c w).im := by
  rw [suzukiCoalescingCayleyInv, Complex.mul_im]
  simp only [ofReal_re, ofReal_im, zero_mul, add_zero]
  exact mul_pos hc
    (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_im_pos_of_norm_lt_one hw)

theorem suzukiCoalescingCayleyInv_zero (c : ℝ) :
    suzukiCoalescingCayleyInv c 0 = (c : ℂ) * I := by
  simp [suzukiCoalescingCayleyInv,
    GaloisForLFunctions.RHTower.suzukiUpperCayleyInv]

theorem suzukiCoalescingCayleyInv_cayley
    {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : 0 < z.im) :
    suzukiCoalescingCayleyInv c (suzukiCoalescingCayley c z) = z := by
  have hden : z + (c : ℂ) * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, ofReal_re, I_im, ofReal_im,
      I_re, mul_one, zero_mul, add_zero, Complex.zero_im] at him
    linarith
  rw [suzukiCoalescingCayleyInv, suzukiCoalescingCayley,
    GaloisForLFunctions.RHTower.suzukiUpperCayleyInv]
  field_simp [hden, hc.ne']
  ring

theorem norm_suzukiCoalescingCayley_lt_one
    {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : 0 < z.im) :
    ‖suzukiCoalescingCayley c z‖ < 1 := by
  have hden : z + (c : ℂ) * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, ofReal_re, I_im, ofReal_im,
      I_re, mul_one, zero_mul, add_zero, Complex.zero_im] at him
    linarith
  rw [suzukiCoalescingCayley, norm_div,
    div_lt_one (norm_pos_iff.mpr hden)]
  have hsq : ‖z - (c : ℂ) * I‖ ^ (2 : ℕ) < ‖z + (c : ℂ) * I‖ ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, ofReal_re, ofReal_im, I_re, I_im]
    nlinarith
  nlinarith [norm_nonneg (z - (c : ℂ) * I),
    norm_nonneg (z + (c : ℂ) * I)]

theorem norm_one_sub_suzukiCoalescingCayley
    {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : 0 < z.im) :
    ‖1 - suzukiCoalescingCayley c z‖ =
      2 * c / ‖z + (c : ℂ) * I‖ := by
  have hden : z + (c : ℂ) * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, ofReal_re, I_im, ofReal_im,
      I_re, mul_one, zero_mul, add_zero, Complex.zero_im] at him
    linarith
  have hid : 1 - suzukiCoalescingCayley c z =
      (2 * (c : ℂ) * I) / (z + (c : ℂ) * I) := by
    rw [suzukiCoalescingCayley]
    field_simp [hden]
    ring
  rw [hid, norm_div, norm_mul, norm_mul]
  simp [norm_real, Real.norm_eq_abs, abs_of_pos hc]

theorem one_sub_norm_sq_suzukiCoalescingCayley
    {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : 0 < z.im) :
    1 - ‖suzukiCoalescingCayley c z‖ ^ (2 : ℕ) =
      4 * c * z.im / ‖z + (c : ℂ) * I‖ ^ (2 : ℕ) := by
  have hden : z + (c : ℂ) * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, ofReal_re, I_im, ofReal_im,
      I_re, mul_one, zero_mul, add_zero, Complex.zero_im] at him
    linarith
  have hdenNorm : ‖z + (c : ℂ) * I‖ ≠ 0 := norm_ne_zero_iff.mpr hden
  rw [suzukiCoalescingCayley, norm_div]
  field_simp [hdenNorm]
  rw [Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, ofReal_re, ofReal_im, I_re, I_im]
  ring

theorem suzukiCoalescingCayley_hyperbolicFactor_le
    {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : 0 < z.im) :
    (1 + ‖suzukiCoalescingCayley c z‖) /
        (1 - ‖suzukiCoalescingCayley c z‖) ≤
      ‖z + (c : ℂ) * I‖ ^ (2 : ℕ) / (c * z.im) := by
  let r := ‖suzukiCoalescingCayley c z‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := norm_suzukiCoalescingCayley_lt_one hc hz
  have hgap : 1 - r ^ (2 : ℕ) =
      4 * c * z.im / ‖z + (c : ℂ) * I‖ ^ (2 : ℕ) := by
    exact one_sub_norm_sq_suzukiCoalescingCayley hc hz
  have hdenNorm : 0 < ‖z + (c : ℂ) * I‖ ^ (2 : ℕ) := by
    apply pow_pos
    apply norm_pos_iff.mpr
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, ofReal_re, I_im, ofReal_im,
      I_re, mul_one, zero_mul, add_zero, Complex.zero_im] at him
    linarith
  have hfactor : (1 + r) / (1 - r) = (1 + r) ^ (2 : ℕ) / (1 - r ^ (2 : ℕ)) := by
    rw [show 1 - r ^ (2 : ℕ) = (1 - r) * (1 + r) by ring]
    field_simp [sub_ne_zero.mpr hr1.ne, ne_of_gt (by positivity : 0 < 1 + r)]
  have hsquare : (1 + r) ^ (2 : ℕ) ≤ 4 := by nlinarith
  rw [hfactor, hgap]
  have hsource : 0 < 4 * c * z.im := by positivity
  calc
    (1 + r) ^ (2 : ℕ) / (4 * c * z.im / ‖z + (c : ℂ) * I‖ ^ (2 : ℕ)) =
        (1 + r) ^ (2 : ℕ) * ‖z + (c : ℂ) * I‖ ^ (2 : ℕ) /
          (4 * c * z.im) := by
      field_simp [hdenNorm.ne', hsource.ne']
    _ ≤ 4 * ‖z + (c : ℂ) * I‖ ^ (2 : ℕ) / (4 * c * z.im) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsquare hdenNorm.le) hsource.le
    _ = ‖z + (c : ℂ) * I‖ ^ (2 : ℕ) / (c * z.im) := by
      field_simp [hc.ne', hz.ne']

theorem hasDerivAt_suzukiCoalescingCayleyInv_zero (c : ℝ) :
    HasDerivAt (suzukiCoalescingCayleyInv c) (2 * (c : ℂ) * I) 0 := by
  have hadd : HasDerivAt (fun w : ℂ => 1 + w) 1 0 := by
    simpa using! (hasDerivAt_const 0 (1 : ℂ)).add (hasDerivAt_id 0)
  have hsub : HasDerivAt (fun w : ℂ => 1 - w) (-1) 0 := by
    simpa using! (hasDerivAt_const 0 (1 : ℂ)).sub (hasDerivAt_id 0)
  have hi : HasDerivAt
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv (2 * I) 0 := by
    have h := (hadd.div hsub (by norm_num : (1 : ℂ) - 0 ≠ 0)).const_mul I
    convert! h using 1
    ring
  have h := hi.const_mul (c : ℂ)
  convert! h using 1
  ring

theorem norm_one_sub_suzukiSchur_le
    {θ : ℂ → ℂ} {c κ : ℝ}
    (hc : 0 < c)
    (hθdiff : DifferentiableOn ℂ θ {z : ℂ | 0 < z.im})
    (hθbd : ∀ z : ℂ, 0 < z.im → ‖θ z‖ ≤ 1)
    (hθanchor : θ ((c : ℂ) * I) = 0)
    (hκderiv : 2 * (c : ℂ) * I * deriv θ ((c : ℂ) * I) = (κ : ℂ))
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    {z : ℂ} (hz : 0 < z.im) :
    ‖1 - θ z‖ ≤
      ‖1 - suzukiCoalescingCayley c z‖ +
        (1 - κ) * (1 + ‖suzukiCoalescingCayley c z‖) /
          (1 - ‖suzukiCoalescingCayley c z‖) := by
  let f : ℂ → ℂ := fun w => θ (suzukiCoalescingCayleyInv c w)
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hfdiff : DifferentiableOn ℂ f (ball 0 1) := by
    intro w hw
    have hwlt : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
    have hw1 : w ≠ 1 := by
      intro h
      rw [h, norm_one] at hwlt
      linarith
    have hinv : DifferentiableAt ℂ (suzukiCoalescingCayleyInv c) w := by
      change DifferentiableAt ℂ
        (fun v : ℂ => (c : ℂ) * (I * ((1 + v) / (1 - v)))) w
      fun_prop (disch := exact sub_ne_zero.mpr (Ne.symm hw1))
    have him := suzukiCoalescingCayleyInv_im_pos hc hwlt
    have hθat : DifferentiableAt ℂ θ (suzukiCoalescingCayleyInv c w) :=
      hθdiff.differentiableAt (hopen.mem_nhds him)
    exact (hθat.comp w hinv).differentiableWithinAt
  have hfbd : ∀ w ∈ ball (0 : ℂ) 1, ‖f w‖ ≤ 1 := by
    intro w hw
    have hwlt : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
    exact hθbd _ (suzukiCoalescingCayleyInv_im_pos hc hwlt)
  have hf0 : f 0 = 0 := by
    simpa [f, suzukiCoalescingCayleyInv_zero] using hθanchor
  have hθat : DifferentiableAt ℂ θ ((c : ℂ) * I) :=
    hθdiff.differentiableAt (hopen.mem_nhds (by simpa using hc))
  have hfderiv : deriv f 0 = (κ : ℂ) := by
    have hθat' : DifferentiableAt ℂ θ (suzukiCoalescingCayleyInv c 0) := by
      simpa [suzukiCoalescingCayleyInv_zero] using hθat
    have hcomp := hθat'.hasDerivAt.comp 0
      (hasDerivAt_suzukiCoalescingCayleyInv_zero c)
    have h := hcomp.deriv
    change deriv (θ ∘ suzukiCoalescingCayleyInv c) 0 = (κ : ℂ)
    rw [h]
    rw [suzukiCoalescingCayleyInv_zero]
    calc
      deriv θ ((c : ℂ) * I) * (2 * (c : ℂ) * I) =
          2 * (c : ℂ) * I * deriv θ ((c : ℂ) * I) := by ring
      _ = (κ : ℂ) := hκderiv
  let w := suzukiCoalescingCayley c z
  have hw : ‖w‖ < 1 := norm_suzukiCoalescingCayley_lt_one hc hz
  have hg := norm_one_sub_dslope_le_hyperbolic
    hfdiff hfbd hf0 hfderiv hκ0 hκ1 hw
  have hfw : f w = w * dslope f 0 w := by
    have h := sub_smul_dslope f 0 w
    simpa [hf0, smul_eq_mul] using h.symm
  have hinv : suzukiCoalescingCayleyInv c w = z :=
    suzukiCoalescingCayleyInv_cayley hc hz
  have hθz : θ z = w * dslope f 0 w := by
    rw [← hinv, ← hfw]
  rw [hθz]
  have hsplit : 1 - w * dslope f 0 w =
      (1 - w) + w * (1 - dslope f 0 w) := by ring
  rw [hsplit]
  calc
    ‖(1 - w) + w * (1 - dslope f 0 w)‖
        ≤ ‖1 - w‖ + ‖w * (1 - dslope f 0 w)‖ := norm_add_le _ _
    _ = ‖1 - w‖ + ‖w‖ * ‖1 - dslope f 0 w‖ := by rw [norm_mul]
    _ ≤ ‖1 - w‖ + ‖1 - dslope f 0 w‖ := by
      gcongr
      exact mul_le_of_le_one_left (norm_nonneg _) hw.le
    _ ≤ ‖1 - w‖ +
        (1 - κ) * (1 + ‖w‖) / (1 - ‖w‖) := by gcongr

theorem norm_one_sub_suzukiSchur_le_linear
    {θ : ℂ → ℂ} {c κ C δ B : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hθdiff : DifferentiableOn ℂ θ {z : ℂ | 0 < z.im})
    (hθbd : ∀ z : ℂ, 0 < z.im → ‖θ z‖ ≤ 1)
    (hθanchor : θ ((c : ℂ) * I) = 0)
    (hκderiv : 2 * (c : ℂ) * I * deriv θ ((c : ℂ) * I) = (κ : ℂ))
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hκgap : 1 - κ ≤ C * c ^ (2 : ℕ))
    {z : ℂ} (hzδ : δ ≤ z.im)
    (hzB : ‖z + (c : ℂ) * I‖ ≤ B) :
    ‖1 - θ z‖ ≤ c * ((2 + C * B ^ (2 : ℕ)) / δ) := by
  have hz : 0 < z.im := lt_of_lt_of_le hδ hzδ
  have hbase := norm_one_sub_suzukiSchur_le hc hθdiff hθbd hθanchor
    hκderiv hκ0 hκ1 hz
  have hdenIm : z.im + c ≤ ‖z + (c : ℂ) * I‖ := by
    have him := Complex.abs_im_le_norm (z + (c : ℂ) * I)
    simp only [Complex.add_im, Complex.mul_im, ofReal_re, I_im, ofReal_im,
      I_re, mul_one, zero_mul, add_zero] at him
    rw [abs_of_pos (add_pos hz hc)] at him
    exact him
  have hdenδ : δ ≤ ‖z + (c : ℂ) * I‖ := by linarith
  have hfirst : ‖1 - suzukiCoalescingCayley c z‖ ≤ 2 * c / δ := by
    rw [norm_one_sub_suzukiCoalescingCayley hc hz]
    exact div_le_div_of_nonneg_left (by positivity) hδ hdenδ
  have hhyp := suzukiCoalescingCayley_hyperbolicFactor_le hc hz
  have hdenSq : ‖z + (c : ℂ) * I‖ ^ (2 : ℕ) ≤ B ^ (2 : ℕ) := by
    nlinarith [norm_nonneg (z + (c : ℂ) * I)]
  have hgeom : ‖z + (c : ℂ) * I‖ ^ (2 : ℕ) / (c * z.im) ≤
      B ^ (2 : ℕ) / (c * δ) := by
    have hcz : 0 < c * z.im := mul_pos hc hz
    have hcδ : 0 < c * δ := mul_pos hc hδ
    rw [div_le_div_iff₀ hcz hcδ]
    calc
      ‖z + (c : ℂ) * I‖ ^ (2 : ℕ) * (c * δ)
          ≤ B ^ (2 : ℕ) * (c * δ) :=
            mul_le_mul_of_nonneg_right hdenSq hcδ.le
      _ ≤ B ^ (2 : ℕ) * (c * z.im) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hzδ hc.le) (sq_nonneg B)
  have hhypB :
      (1 + ‖suzukiCoalescingCayley c z‖) /
          (1 - ‖suzukiCoalescingCayley c z‖) ≤
        B ^ (2 : ℕ) / (c * δ) := le_trans hhyp hgeom
  have hgap0 : 0 ≤ 1 - κ := sub_nonneg.mpr hκ1.le
  have hsecond :
      (1 - κ) *
          ((1 + ‖suzukiCoalescingCayley c z‖) /
            (1 - ‖suzukiCoalescingCayley c z‖)) ≤
        C * c * B ^ (2 : ℕ) / δ := by
    calc
      (1 - κ) *
          ((1 + ‖suzukiCoalescingCayley c z‖) /
            (1 - ‖suzukiCoalescingCayley c z‖))
          ≤ (1 - κ) * (B ^ (2 : ℕ) / (c * δ)) :=
            mul_le_mul_of_nonneg_left hhypB hgap0
      _ ≤ (C * c ^ (2 : ℕ)) * (B ^ (2 : ℕ) / (c * δ)) := by
        gcongr
      _ = C * c * B ^ (2 : ℕ) / δ := by
        field_simp [hc.ne', hδ.ne']
  calc
    ‖1 - θ z‖ ≤ ‖1 - suzukiCoalescingCayley c z‖ +
        (1 - κ) * (1 + ‖suzukiCoalescingCayley c z‖) /
          (1 - ‖suzukiCoalescingCayley c z‖) := hbase
    _ ≤ 2 * c / δ + C * c * B ^ (2 : ℕ) / δ := by
      exact add_le_add hfirst (by simpa [mul_div_assoc] using hsecond)
    _ = c * ((2 + C * B ^ (2 : ℕ)) / δ) := by ring

/-- Singularly normalized half-plane resolvent used in the coalescing limit. -/
def suzukiCoalescingResolvent (θ : ℂ → ℂ) (c : ℝ) (z : ℂ) : ℂ :=
  (1 - θ z) / ((c : ℂ) * (1 + θ z))

theorem norm_suzukiCoalescingResolvent_le
    {θ : ℂ → ℂ} {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    {z : ℂ} (hdefect : ‖1 - θ z‖ ≤ c * A)
    (hsmall : c * A ≤ 1) :
    ‖suzukiCoalescingResolvent θ c z‖ ≤ A := by
  have hplus : 1 ≤ ‖1 + θ z‖ := by
    have hrev := norm_sub_norm_le (2 : ℂ) (1 - θ z)
    have hid : (2 : ℂ) - (1 - θ z) = 1 + θ z := by ring
    rw [hid] at hrev
    norm_num at hrev
    linarith
  have hc0 : ‖(c : ℂ)‖ = c := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos hc]
  rw [suzukiCoalescingResolvent, norm_div, norm_mul, hc0]
  have hden : 0 < c * ‖1 + θ z‖ := mul_pos hc (lt_of_lt_of_le zero_lt_one hplus)
  calc
    ‖1 - θ z‖ / (c * ‖1 + θ z‖)
        ≤ (c * A) / (c * ‖1 + θ z‖) :=
          div_le_div_of_nonneg_right hdefect hden.le
    _ = A / ‖1 + θ z‖ := by field_simp [hc.ne']
    _ ≤ A / 1 := by
      exact div_le_div_of_nonneg_left hA zero_lt_one hplus
    _ = A := div_one A

theorem differentiableOn_suzukiCoalescingResolvent
    {θ : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (hθdiff : DifferentiableOn ℂ θ {z : ℂ | 0 < z.im})
    (hθlt : ∀ z : ℂ, 0 < z.im → ‖θ z‖ < 1) :
    DifferentiableOn ℂ (suzukiCoalescingResolvent θ c)
      {z : ℂ | 0 < z.im} := by
  intro z hz
  have hplus : 1 + θ z ≠ 0 := by
    intro h
    have hval : θ z = -1 := by linear_combination h
    have ht := hθlt z hz
    rw [hval, norm_neg, norm_one] at ht
    linarith
  unfold suzukiCoalescingResolvent
  exact ((differentiableAt_const (c := (1 : ℂ))).sub
      ((hθdiff z hz).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz))).div
    ((differentiableAt_const (c := (c : ℂ))).mul
      ((differentiableAt_const (c := (1 : ℂ))).add
        ((hθdiff z hz).differentiableAt
          ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz))))
    (mul_ne_zero (ofReal_ne_zero.mpr hc.ne') hplus) |>.differentiableWithinAt

/-- The quadratic anchor gap makes the singularly normalized resolvents a normal family on every
fixed upper-half-plane ball.  The explicit smallness premise is exactly the harmless cofinal tail
on which the denominator is separated from zero by the proved linear defect bound. -/
theorem exists_suzukiCoalescingResolvent_montel_subseq
    {θ : ℕ → ℂ → ℂ} {c κ : ℕ → ℝ} {C R r : ℝ} {q : ℂ}
    (hC : 0 ≤ C) (hR0 : 0 < R) (hRq : R < q.im)
    (hr0 : 0 < r) (hrR : r < R / 2)
    (hc : ∀ n, 0 < c n) (hc1 : ∀ n, c n ≤ 1)
    (hθdiff : ∀ n, DifferentiableOn ℂ (θ n) {z : ℂ | 0 < z.im})
    (hθlt : ∀ n z, 0 < z.im → ‖θ n z‖ < 1)
    (hθanchor : ∀ n, θ n ((c n : ℂ) * I) = 0)
    (hκderiv : ∀ n,
      2 * (c n : ℂ) * I * deriv (θ n) ((c n : ℂ) * I) = (κ n : ℂ))
    (hκ0 : ∀ n, 0 ≤ κ n) (hκ1 : ∀ n, κ n < 1)
    (hκgap : ∀ n, 1 - κ n ≤ C * (c n) ^ (2 : ℕ))
    (hsmall : ∀ n,
      c n * ((2 + C * (‖q‖ + R + 1) ^ (2 : ℕ)) / (q.im - R)) ≤ 1) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
      TendstoUniformlyOn
        (fun k => suzukiCoalescingResolvent (θ (φ k)) (c (φ k)))
        g Filter.atTop (closedBall q r) ∧
      DifferentiableOn ℂ g (ball q r) := by
  let δ : ℝ := q.im - R
  let B : ℝ := ‖q‖ + R + 1
  let A : ℝ := (2 + C * B ^ (2 : ℕ)) / δ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (by positivity) hδ.le
  have hgeometry (n : ℕ) (z : ℂ) (hzball : z ∈ ball q R) :
      δ ≤ z.im ∧ ‖z + (c n : ℂ) * I‖ ≤ B := by
    have hzq : ‖z - q‖ < R := by
      simpa [mem_ball, dist_eq_norm] using hzball
    have himle : |(z - q).im| ≤ ‖z - q‖ := Complex.abs_im_le_norm _
    have himabs : |z.im - q.im| < R := by
      rw [Complex.sub_im] at himle
      exact lt_of_le_of_lt himle hzq
    have hzδ : δ ≤ z.im := by
      dsimp [δ]
      have hneg := neg_le_of_abs_le (le_of_lt himabs)
      nlinarith
    have hcNorm : ‖(c n : ℂ) * I‖ = c n := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (hc n), norm_I, mul_one]
    have hsum : ‖z + (c n : ℂ) * I‖ ≤ ‖z - q‖ + ‖q‖ + c n := by
      calc
        ‖z + (c n : ℂ) * I‖ = ‖(z - q) + q + (c n : ℂ) * I‖ := by
          congr 1
          ring
        _ ≤ ‖(z - q) + q‖ + ‖(c n : ℂ) * I‖ := norm_add_le _ _
        _ ≤ ‖z - q‖ + ‖q‖ + ‖(c n : ℂ) * I‖ := by
          gcongr
          exact norm_add_le _ _
        _ = ‖z - q‖ + ‖q‖ + c n := by rw [hcNorm]
    have hzB : ‖z + (c n : ℂ) * I‖ ≤ B := by
      dsimp [B]
      linarith [hc1 n]
    exact ⟨hzδ, hzB⟩
  have hupper : ∀ z ∈ ball q R, 0 < z.im := by
    intro z hz
    exact lt_of_lt_of_le hδ (hgeometry 0 z hz).1
  have hFdiff : ∀ n,
      DifferentiableOn ℂ (suzukiCoalescingResolvent (θ n) (c n)) (ball q R) := by
    intro n
    exact (differentiableOn_suzukiCoalescingResolvent (hc n) (hθdiff n)
      (hθlt n)).mono hupper
  have hFbd : ∀ n, ∀ z ∈ ball q R,
      ‖suzukiCoalescingResolvent (θ n) (c n) z‖ ≤ A := by
    intro n z hzball
    obtain ⟨hzδ, hzB⟩ := hgeometry n z hzball
    have hdefect := norm_one_sub_suzukiSchur_le_linear
      (hc n) hδ hB (hθdiff n)
      (fun w hw => (hθlt n w hw).le) (hθanchor n) (hκderiv n)
      (hκ0 n) (hκ1 n) (hκgap n) hzδ hzB
    have hdefect' : ‖1 - θ n z‖ ≤ c n * A := by
      simpa [A, B, δ] using hdefect
    apply norm_suzukiCoalescingResolvent_le (hc n) hA hdefect'
    simpa [A, B, δ] using hsmall n
  exact Bottcher.montel_subseq hr0 hrR hFdiff hFbd

end

end RHTower
