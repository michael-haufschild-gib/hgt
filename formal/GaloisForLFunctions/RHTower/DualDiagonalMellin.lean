import GaloisForLFunctions.RHTower.DualCarrierWeightRightShift
import GaloisForLFunctions.RHTower.SmoothDiagonalContour

/-!
# The smoothed dual diagonal: Mellin form and residues

On the dual diagonal `mk = nh` of the product approximate functional equation the reduced
direction `m = jh'`, `n = jk'` gives the quadratic sum

`D̃(τ) = Σ_{j ≥ 1} j^{-(1+2d)} · χ(s₁)χ(s₂) W(j² c x)`,   `c = h'k'`,  `σ₀ = ½ − d`,

whose frequency integrand on `Re w = 1` is the carrier integrand times `ζ(1+2d+2w)`:

`F̃(w) = χ(s₁−w)χ(s₂−w) (cx)^{-w} e^{w²}/w · ζ(1+2d+2w)`.

Two poles lie left of the line: the kernel pole at `0` with residue `χ(s₁)χ(s₂)ζ(1+2d)`, and the
zeta pole at `−d`, where the carrier is `χ(½+iτ)χ(½−iτ) = 1`, with the height-independent residue
`−(cx)^d e^{d²}/(2d)`.  The remainder is analytic on `Re w > −½ − d`, which is enough for the
rectangle: a two-pole residue theorem with the remainder analytic on a neighbourhood of the
rectangle is proved here.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Set intervalIntegral GaloisForLFunctions
  GaloisForLFunctions.HTGeometry

/-! ## Two-pole residues with a remainder analytic near the rectangle -/

theorem rectIntegral_eq_two_pole_residues_of_analyticOnNhd
    {F R : ℂ → ℂ} {p q rp rq z₁ z₂ : ℂ} {U : Set ℂ}
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hp1 : z₁.re < p.re) (hp2 : p.re < z₂.re)
    (hp3 : z₁.im < p.im) (hp4 : p.im < z₂.im)
    (hq1 : z₁.re < q.re) (hq2 : q.re < z₂.re)
    (hq3 : z₁.im < q.im) (hq4 : q.im < z₂.im)
    (hR : AnalyticOnNhd ℂ R U)
    (hdecomp : ∀ z, z ≠ p → z ≠ q →
      F z = rp * (z - p)⁻¹ + (rq * (z - q)⁻¹ + R z)) :
    rectIntegral F z₁ z₂ = 2 * Real.pi * I * (rp + rq) := by
  let S : Set ℂ := {z | z ≠ p ∧ z ≠ q}
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₁.im * I) ∈ S := by
    intro x hx
    constructor
    · intro heq
      have him := congrArg Complex.im heq
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
      linarith
    · intro heq
      have him := congrArg Complex.im heq
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
      linarith
  have htop : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₂.im * I) ∈ S := by
    intro x hx
    constructor
    · intro heq
      have him := congrArg Complex.im heq
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
      linarith
    · intro heq
      have him := congrArg Complex.im heq
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_add, mul_one] at him
      linarith
  have hright : ∀ y ∈ uIcc z₁.im z₂.im, ((z₂.re : ℂ) + y * I) ∈ S := by
    intro y hy
    constructor
    · intro heq
      have hre := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
      linarith
    · intro heq
      have hre := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
      linarith
  have hleft : ∀ y ∈ uIcc z₁.im z₂.im, ((z₁.re : ℂ) + y * I) ∈ S := by
    intro y hy
    constructor
    · intro heq
      have hre := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
      linarith
    · intro heq
      have hre := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hre
      linarith
  have hkernel : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt →
      ∀ (c pole : ℂ), (∀ t ∈ uIcc a b, pt t ≠ pole) →
        IntervalIntegrable (fun t => c * (pt t - pole)⁻¹) MeasureTheory.volume a b := by
    intro a b pt hpt c pole hne
    exact (continuousOn_const.mul
      ((hpt.continuousOn.sub continuousOn_const).inv₀
        (fun t ht => sub_ne_zero.mpr (hne t ht)))).intervalIntegrable
  -- the remainder is continuous along each edge, since each edge lies in `U`
  have hRcont : ContinuousOn R U := hR.continuousOn
  have hregular : ∀ {a b : ℝ} (pt : ℝ → ℂ), Continuous pt → (∀ t ∈ uIcc a b, pt t ∈ U) →
      IntervalIntegrable (fun t => R (pt t)) MeasureTheory.volume a b := by
    intro a b pt hpt hmem
    exact (hRcont.comp hpt.continuousOn hmem).intervalIntegrable
  have hmem_bot : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₁.im * I) ∈ U := by
    intro x hx
    apply hsub
    rw [Complex.mem_reProdIm]
    constructor
    · have h : ((x : ℂ) + z₁.im * I).re = x := by simp
      rw [h]; exact hx
    · have h : ((x : ℂ) + z₁.im * I).im = z₁.im := by simp
      rw [h]; exact left_mem_uIcc
  have hmem_top : ∀ x ∈ uIcc z₁.re z₂.re, ((x : ℂ) + z₂.im * I) ∈ U := by
    intro x hx
    apply hsub
    rw [Complex.mem_reProdIm]
    constructor
    · have h : ((x : ℂ) + z₂.im * I).re = x := by simp
      rw [h]; exact hx
    · have h : ((x : ℂ) + z₂.im * I).im = z₂.im := by simp
      rw [h]; exact right_mem_uIcc
  have hmem_right : ∀ y ∈ uIcc z₁.im z₂.im, ((z₂.re : ℂ) + y * I) ∈ U := by
    intro y hy
    apply hsub
    rw [Complex.mem_reProdIm]
    constructor
    · have h : ((z₂.re : ℂ) + y * I).re = z₂.re := by simp
      rw [h]; exact right_mem_uIcc
    · have h : ((z₂.re : ℂ) + y * I).im = y := by simp
      rw [h]; exact hy
  have hmem_left : ∀ y ∈ uIcc z₁.im z₂.im, ((z₁.re : ℂ) + y * I) ∈ U := by
    intro y hy
    apply hsub
    rw [Complex.mem_reProdIm]
    constructor
    · have h : ((z₁.re : ℂ) + y * I).re = z₁.re := by simp
      rw [h]; exact left_mem_uIcc
    · have h : ((z₁.re : ℂ) + y * I).im = y := by simp
      rw [h]; exact hy
  rw [rectIntegral_congr (fun z hz => hdecomp z hz.1 hz.2) hbot htop hright hleft,
    rectIntegral_add
      (hkernel _ (by fun_prop) rp p (fun x hx => (hbot x hx).1))
      ((hkernel _ (by fun_prop) rq q (fun x hx => (hbot x hx).2)).add
        (hregular _ (by fun_prop) hmem_bot))
      (hkernel _ (by fun_prop) rp p (fun x hx => (htop x hx).1))
      ((hkernel _ (by fun_prop) rq q (fun x hx => (htop x hx).2)).add
        (hregular _ (by fun_prop) hmem_top))
      (hkernel _ (by fun_prop) rp p (fun y hy => (hright y hy).1))
      ((hkernel _ (by fun_prop) rq q (fun y hy => (hright y hy).2)).add
        (hregular _ (by fun_prop) hmem_right))
      (hkernel _ (by fun_prop) rp p (fun y hy => (hleft y hy).1))
      ((hkernel _ (by fun_prop) rq q (fun y hy => (hleft y hy).2)).add
        (hregular _ (by fun_prop) hmem_left)),
    rectIntegral_add
      (hkernel _ (by fun_prop) rq q (fun x hx => (hbot x hx).2))
      (hregular _ (by fun_prop) hmem_bot)
      (hkernel _ (by fun_prop) rq q (fun x hx => (htop x hx).2))
      (hregular _ (by fun_prop) hmem_top)
      (hkernel _ (by fun_prop) rq q (fun y hy => (hright y hy).2))
      (hregular _ (by fun_prop) hmem_right)
      (hkernel _ (by fun_prop) rq q (fun y hy => (hleft y hy).2))
      (hregular _ (by fun_prop) hmem_left),
    rectIntegral_const_mul, rectIntegral_cauchyKernel hp1 hp2 hp3 hp4,
    rectIntegral_const_mul, rectIntegral_cauchyKernel hq1 hq2 hq3 hq4,
    rectIntegral_eq_zero_of_analyticOnNhd hsub hR]
  ring

/-! ## The dual diagonal and its frequency integrand -/

/-- The dual diagonal integrand `χ(s₁−w)χ(s₂−w)(cx)^{-w}e^{w²}/w · ζ(1+2d+2w)`. -/
def dualDiagonalIntegrand (d c x τ : ℝ) (w : ℂ) : ℂ :=
  carrierIntegrand d τ (c * x) w * riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * w)

/-- The `j`-th term. -/
def dualDiagonalTerm (d c x τ : ℝ) (j : ℕ) (w : ℂ) : ℂ :=
  (1 / (j + 1 : ℂ) ^ (((1 + 2 * d : ℝ) : ℂ) + 2 * w)) * carrierIntegrand d τ (c * x) w

/-- The dual diagonal `Σ_j (j+1)^{-(1+2d)} χ(s₁)χ(s₂)W((j+1)²cx)`. -/
def dualDiagonal (d c x τ : ℝ) : ℂ :=
  ∑' j : ℕ, (j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ))
    * dualCarrierWeight d ((j + 1 : ℝ) ^ 2 * c * x) τ

theorem dualDiagonalTerm_eq {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (d τ : ℝ) (j : ℕ) (w : ℂ) :
    dualDiagonalTerm d c x τ j w
      = (j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ)) * carrierIntegrand d τ ((j + 1 : ℝ) ^ 2 * c * x) w := by
  have hj : (0 : ℝ) < j + 1 := by positivity
  have hjc : (j + 1 : ℂ) ≠ 0 := by exact_mod_cast hj.ne'
  unfold dualDiagonalTerm carrierIntegrand smoothAFEMellinIntegrand
  have h1 : ((((j + 1 : ℝ) ^ 2 * c * x : ℝ)) : ℂ) ^ (-w)
      = (((j + 1 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-w) * ((c * x : ℝ) : ℂ) ^ (-w) := by
    rw [show (((j + 1 : ℝ) ^ 2 * c * x : ℝ) : ℂ) = (((j + 1 : ℝ) ^ 2 : ℝ) : ℂ) * ((c * x : ℝ) : ℂ) by
      push_cast; ring]
    exact Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity) (-w)
  have h3 : (((j + 1 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-w) = (j + 1 : ℂ) ^ (-w) * (j + 1 : ℂ) ^ (-w) := by
    rw [show (((j + 1 : ℝ) ^ 2 : ℝ) : ℂ) = ((j + 1 : ℝ) : ℂ) * ((j + 1 : ℝ) : ℂ) by
      push_cast; ring]
    rw [Complex.mul_cpow_ofReal_nonneg hj.le hj.le (-w)]
    push_cast
    ring
  have h5 : (1 : ℂ) / (j + 1 : ℂ) ^ (((1 + 2 * d : ℝ) : ℂ) + 2 * w)
      = (j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ)) * ((j + 1 : ℂ) ^ (-w) * (j + 1 : ℂ) ^ (-w)) := by
    rw [one_div, ← Complex.cpow_neg, show -(((1 + 2 * d : ℝ) : ℂ) + 2 * w)
      = -((1 + 2 * d : ℝ) : ℂ) + (-w + -w) by ring, Complex.cpow_add _ _ hjc,
      Complex.cpow_add _ _ hjc]
  rw [h1, h3, h5]
  ring

theorem dualDiagonalIntegrand_eq_tsum {d : ℝ} (c x τ : ℝ) {w : ℂ} (hw : -d < w.re) :
    dualDiagonalIntegrand d c x τ w = ∑' j : ℕ, dualDiagonalTerm d c x τ j w := by
  unfold dualDiagonalIntegrand dualDiagonalTerm
  have hre : 1 < (((1 + 2 * d : ℝ) : ℂ) + 2 * w).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre, mul_comm, ← tsum_mul_right]

/-! ## The line `Re w = 1` -/

theorem carrierIntegrand_one_line_eq (d τ Y v : ℝ) :
    carrierIntegrand d τ Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)
      = chiCarrier d v τ * dualFrequencyKernel Y v := by
  unfold carrierIntegrand chiCarrier dualFrequencyKernel levinsonShift
  push_cast
  ring_nf

theorem dualDiagonalTerm_one_line_eq {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (d τ : ℝ) (j : ℕ)
    (v : ℝ) :
    dualDiagonalTerm d c x τ j (((1 : ℝ) : ℂ) + (v : ℂ) * I)
      = (j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ))
        * (chiCarrier d v τ * dualFrequencyKernel ((j + 1 : ℝ) ^ 2 * c * x) v) := by
  rw [dualDiagonalTerm_eq hc hx, carrierIntegrand_one_line_eq]

theorem norm_dualDiagonalTerm_one_line_le {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (d : ℝ)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v t : ℝ, ‖chiCarrier d v t‖ ≤ C * ((1 + |t - v|) ^ 2 * (1 + |t + v|) ^ 2))
    (τ : ℝ) (j : ℕ) (v : ℝ) :
    ‖dualDiagonalTerm d c x τ j (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ (1 / (j + 1 : ℝ) ^ (3 + 2 * d)) * (C * (1 + |τ|) ^ 4 * ((c * x)⁻¹ * Real.exp 1))
          * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
  have hj : (0 : ℝ) < j + 1 := by positivity
  have hY : (0 : ℝ) < (j + 1 : ℝ) ^ 2 * c * x := by positivity
  rw [dualDiagonalTerm_one_line_eq hc hx, norm_mul, norm_mul]
  have hcoef : ‖(j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ))‖ = (j + 1 : ℝ) ^ (-(1 + 2 * d)) := by
    rw [show (j + 1 : ℂ) = (((j : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hj]
    simp
  have hG : ‖chiCarrier d v τ‖ ≤ C * ((1 + |τ|) ^ 4 * (1 + |v|) ^ 4) := by
    refine (hC v τ).trans ?_
    apply mul_le_mul_of_nonneg_left _ hC0
    have hb1 : 1 + |τ - v| ≤ (1 + |τ|) * (1 + |v|) := by
      have := abs_sub τ v
      nlinarith [abs_nonneg τ, abs_nonneg v]
    have hb2 : 1 + |τ + v| ≤ (1 + |τ|) * (1 + |v|) := by
      have := abs_add_le τ v
      nlinarith [abs_nonneg τ, abs_nonneg v]
    calc (1 + |τ - v|) ^ 2 * (1 + |τ + v|) ^ 2
        ≤ ((1 + |τ|) * (1 + |v|)) ^ 2 * ((1 + |τ|) * (1 + |v|)) ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hb1 2)
            (pow_le_pow_left₀ (by positivity) hb2 2) (by positivity) (by positivity)
      _ = (1 + |τ|) ^ 4 * (1 + |v|) ^ 4 := by ring
  have hk := norm_dualFrequencyKernel_le hY v
  have hinv : ((j + 1 : ℝ) ^ 2 * c * x)⁻¹ = (c * x)⁻¹ * (1 / (j + 1 : ℝ) ^ 2) := by
    field_simp
  calc ‖(j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ))‖ * (‖chiCarrier d v τ‖
        * ‖dualFrequencyKernel ((j + 1 : ℝ) ^ 2 * c * x) v‖)
      ≤ (j + 1 : ℝ) ^ (-(1 + 2 * d)) * ((C * ((1 + |τ|) ^ 4 * (1 + |v|) ^ 4))
          * ((((j + 1 : ℝ) ^ 2 * c * x)⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)))) := by
        rw [hcoef]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hG hk (norm_nonneg _) (by positivity))
          (by positivity)
    _ = (1 / (j + 1 : ℝ) ^ (3 + 2 * d)) * (C * (1 + |τ|) ^ 4 * ((c * x)⁻¹ * Real.exp 1))
          * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
        rw [hinv, show (3 + 2 * d : ℝ) = (1 + 2 * d) + 2 by ring, Real.rpow_add hj,
          Real.rpow_neg hj.le, show ((j + 1 : ℝ)) ^ (2 : ℝ) = (j + 1 : ℝ) ^ 2 by norm_cast]
        field_simp

theorem continuous_dualDiagonalTerm_one_line {c x : ℝ} (hc : 0 < c) (hx : 0 < x) {d : ℝ}
    (hd : 0 < d) (τ : ℝ) (j : ℕ) :
    Continuous (fun v : ℝ => dualDiagonalTerm d c x τ j (((1 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  have hY : (0 : ℝ) < (j + 1 : ℝ) ^ 2 * c * x := by positivity
  have : (fun v : ℝ => dualDiagonalTerm d c x τ j (((1 : ℝ) : ℂ) + (v : ℂ) * I))
      = fun v : ℝ => (j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ))
        * (chiCarrier d v τ * dualFrequencyKernel ((j + 1 : ℝ) ^ 2 * c * x) v) :=
    funext fun v => dualDiagonalTerm_one_line_eq hc hx d τ j v
  rw [this]
  exact continuous_const.mul
    (((continuous_chiCarrier_uncurry hd).comp (Continuous.prodMk continuous_const continuous_id)).mul
      (continuous_dualFrequencyKernel hY))

theorem integrable_dualDiagonalTerm_one_line {c x : ℝ} (hc : 0 < c) (hx : 0 < x) {d : ℝ}
    (hd : 0 < d) (hdq : d ≤ 1 / 4) (τ : ℝ) (j : ℕ) :
    Integrable (fun v : ℝ => dualDiagonalTerm d c x τ j (((1 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_chiCarrier_le hd hdq
  refine Integrable.mono' ((integrable_one_add_abs_pow_mul_exp_neg_sq 4).const_mul
    ((1 / (j + 1 : ℝ) ^ (3 + 2 * d)) * (C * (1 + |τ|) ^ 4 * ((c * x)⁻¹ * Real.exp 1))))
    (continuous_dualDiagonalTerm_one_line hc hx hd τ j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => norm_dualDiagonalTerm_one_line_le hc hx d hC0 hC τ j v)

theorem summable_integral_norm_dualDiagonalTerm_one_line {c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (τ : ℝ) :
    Summable (fun j : ℕ => ∫ v : ℝ,
      ‖dualDiagonalTerm d c x τ j (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_chiCarrier_le hd hdq
  have hG : Integrable (fun v : ℝ => (1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) :=
    integrable_one_add_abs_pow_mul_exp_neg_sq 4
  have hmaj : Summable (fun j : ℕ => (1 / (j + 1 : ℝ) ^ (3 + 2 * d))
      * ((C * (1 + |τ|) ^ 4 * ((c * x)⁻¹ * Real.exp 1))
        * ∫ v : ℝ, (1 + |v|) ^ 4 * Real.exp (-(v ^ 2)))) :=
    (summable_smoothAFEZetaMajorant (by linarith)).mul_right _
  refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun v => norm_nonneg _)
    (fun j => ?_) hmaj
  calc ∫ v : ℝ, ‖dualDiagonalTerm d c x τ j (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ ∫ v : ℝ, (1 / (j + 1 : ℝ) ^ (3 + 2 * d)) * (C * (1 + |τ|) ^ 4 * ((c * x)⁻¹ * Real.exp 1))
          * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _)
          (hG.const_mul _) (Filter.Eventually.of_forall fun v =>
            norm_dualDiagonalTerm_one_line_le hc hx d hC0 hC τ j v)
    _ = (1 / (j + 1 : ℝ) ^ (3 + 2 * d)) * ((C * (1 + |τ|) ^ 4 * ((c * x)⁻¹ * Real.exp 1))
          * ∫ v : ℝ, (1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
        rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
        congr 1
        funext v
        ring

/-- **The dual diagonal is the line integral of its frequency integrand.** -/
theorem dualDiagonal_eq_integral {c x : ℝ} (hc : 0 < c) (hx : 0 < x) {d : ℝ} (hd : 0 < d)
    (hdq : d ≤ 1 / 4) (τ : ℝ) :
    dualDiagonal d c x τ
      = (1 / (2 * Real.pi)) • ∫ v : ℝ, dualDiagonalIntegrand d c x τ (((1 : ℝ) : ℂ) + (v : ℂ) * I) := by
  have hint : ∀ v : ℝ, dualDiagonalIntegrand d c x τ (((1 : ℝ) : ℂ) + (v : ℂ) * I)
      = ∑' j : ℕ, dualDiagonalTerm d c x τ j (((1 : ℝ) : ℂ) + (v : ℂ) * I) := fun v =>
    dualDiagonalIntegrand_eq_tsum c x τ (by simp; linarith)
  simp_rw [hint]
  rw [← integral_tsum_of_summable_integral_norm
    (fun j => integrable_dualDiagonalTerm_one_line hc hx hd hdq τ j)
    (summable_integral_norm_dualDiagonalTerm_one_line hc hx hd hdq τ)]
  unfold dualDiagonal
  rw [← tsum_const_smul'' (1 / (2 * Real.pi))]
  refine tsum_congr fun j => ?_
  rw [dualCarrierWeight_eq_integral_carrierIntegrand]
  have hterm : (fun v : ℝ => dualDiagonalTerm d c x τ j (((1 : ℝ) : ℂ) + (v : ℂ) * I))
      = fun v : ℝ => (j + 1 : ℂ) ^ (-((1 + 2 * d : ℝ) : ℂ))
        * carrierIntegrand d τ ((j + 1 : ℝ) ^ 2 * c * x) (((1 : ℝ) : ℂ) + (v : ℂ) * I) :=
    funext fun v => dualDiagonalTerm_eq hc hx d τ j (((1 : ℝ) : ℂ) + (v : ℂ) * I)
  rw [hterm, MeasureTheory.integral_const_mul, Complex.real_smul, Complex.real_smul]
  ring

/-! ## The two-pole decomposition -/

/-- The numerator `χ(s₁−w)χ(s₂−w)(cx)^{-w}e^{w²}((2d+2w)ζ(1+2d+2w))/2`, analytic on
`Re w > −½ − d`. -/
def dualDiagonalNumerator (d c x τ : ℝ) (w : ℂ) : ℂ :=
  zetaChi (displacedLinePt d τ - w) * zetaChi (displacedLinePt d (-τ) - w)
    * ((c * x : ℝ) : ℂ) ^ (-w) * Complex.exp (w ^ 2)
    * regularizedRiemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * w) / 2

def dualDiagonalRemainder (d c x τ : ℝ) : ℂ → ℂ :=
  dslope (dslope (dualDiagonalNumerator d c x τ) 0) (-(d : ℂ))

/-- The residue at the zeta pole `−d`: `−(cx)^d e^{d²}/(2d)`, height-independent. -/
def dualDiagonalShiftedResidue (d c x : ℝ) : ℂ :=
  -(((c * x : ℝ) : ℂ) ^ (d : ℂ) * Complex.exp ((d : ℂ) ^ 2) / (2 * d))

/-- The open region of analyticity of the numerator. -/
def dualDiagonalRegion (d : ℝ) : Set ℂ := {w : ℂ | -(1 / 2) - d < w.re}

theorem isOpen_dualDiagonalRegion (d : ℝ) : IsOpen (dualDiagonalRegion d) :=
  isOpen_lt continuous_const Complex.continuous_re

theorem analyticOnNhd_dualDiagonalNumerator {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (d τ : ℝ) :
    AnalyticOnNhd ℂ (dualDiagonalNumerator d c x τ) (dualDiagonalRegion d) := by
  intro w hw
  have hw' : -(1 / 2) - d < w.re := hw
  have hcx : ((c * x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mul_pos hc hx).ne'
  have hpow : AnalyticAt ℂ (fun w : ℂ => ((c * x : ℝ) : ℂ) ^ (-w)) w := by
    have : (fun w : ℂ => ((c * x : ℝ) : ℂ) ^ (-w))
        = fun w => Complex.exp (Complex.log ((c * x : ℝ) : ℂ) * (-w)) := by
      funext w
      exact Complex.cpow_def_of_ne_zero hcx _
    rw [this]
    exact analyticAt_cexp.comp (analyticAt_const.mul analyticAt_id.neg)
  have hreg : AnalyticAt ℂ (fun w : ℂ => regularizedRiemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * w)) w :=
    (differentiable_regularizedRiemannZeta.analyticAt _).comp
      (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
  unfold dualDiagonalNumerator
  have hall := ((((analyticAt_zetaChi_displaced_sub d τ hw').mul
    (analyticAt_zetaChi_displaced_sub d (-τ) hw')).mul hpow).mul
    (analyticAt_cexp.comp (analyticAt_id.pow 2))).mul hreg
  exact hall.div_const

theorem analyticOnNhd_dualDiagonalRemainder {c x : ℝ} (hc : 0 < c) (hx : 0 < x) {d : ℝ}
    (hd : 0 < d) (τ : ℝ) :
    AnalyticOnNhd ℂ (dualDiagonalRemainder d c x τ) (dualDiagonalRegion d) := by
  have hU := isOpen_dualDiagonalRegion d
  have hN := analyticOnNhd_dualDiagonalNumerator hc hx d τ
  have h0 : (0 : ℂ) ∈ dualDiagonalRegion d := by
    show -(1 / 2) - d < (0 : ℂ).re
    simp
    linarith
  have hd' : (-(d : ℂ)) ∈ dualDiagonalRegion d := by
    show -(1 / 2) - d < (-(d : ℂ)).re
    simp
    linarith
  have hQ : DifferentiableOn ℂ (dslope (dualDiagonalNumerator d c x τ) 0) (dualDiagonalRegion d) :=
    (differentiableOn_dslope (hU.mem_nhds h0)).mpr hN.differentiableOn
  have hR : DifferentiableOn ℂ (dualDiagonalRemainder d c x τ) (dualDiagonalRegion d) := by
    unfold dualDiagonalRemainder
    exact (differentiableOn_dslope (hU.mem_nhds hd')).mpr hQ
  exact hR.analyticOnNhd hU

theorem dualDiagonalNumerator_zero {d : ℝ} (hd : 0 < d) (c x τ : ℝ) :
    dualDiagonalNumerator d c x τ 0
      = (d : ℂ) * (zetaChi (displacedLinePt d τ) * zetaChi (displacedLinePt d (-τ))
          * riemannZeta ((1 + 2 * d : ℝ) : ℂ)) := by
  have hne : (((1 + 2 * d : ℝ) : ℂ) + 2 * 0) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  unfold dualDiagonalNumerator
  rw [regularizedRiemannZeta_of_ne_one hne]
  simp
  ring

theorem dualDiagonalNumerator_neg_d (d c x τ : ℝ) :
    dualDiagonalNumerator d c x τ (-(d : ℂ))
      = ((c * x : ℝ) : ℂ) ^ (d : ℂ) * Complex.exp ((d : ℂ) ^ 2) / 2 := by
  unfold dualDiagonalNumerator
  have h1 : (((1 + 2 * d : ℝ) : ℂ) + 2 * (-(d : ℂ))) = 1 := by push_cast; ring
  have hs₁ : displacedLinePt d τ - (-(d : ℂ)) = ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I := by
    unfold displacedLinePt; push_cast; ring
  have hs₂ : displacedLinePt d (-τ) - (-(d : ℂ)) = 1 - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) := by
    unfold displacedLinePt; push_cast; ring
  have hχ : zetaChi (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)
      * zetaChi (1 - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)) = 1 :=
    zetaChi_mul_one_sub_of_mem_strip (by simp) (by simp; norm_num)
  rw [h1, regularizedRiemannZeta_one, hs₁, hs₂, hχ, neg_neg, neg_sq]
  ring

private theorem two_pole_quotient_decomposition''
    {Nw N0 Nρ w ρ : ℂ} (hw : w ≠ 0) (hρ : ρ ≠ 0) (hwρ : w - ρ ≠ 0) :
    Nw / (w * (w - ρ)) =
      (-N0 / ρ) * w⁻¹ + (Nρ / ρ) * (w - ρ)⁻¹ +
        (((Nw - N0) / w) - ((Nρ - N0) / ρ)) / (w - ρ) := by
  rw [inv_eq_one_div, inv_eq_one_div]
  field_simp [hw, hρ, hwρ]
  ring

/-- **Two-pole decomposition of the dual diagonal integrand**: residue `χ(s₁)χ(s₂)ζ(1+2d)` at
`0`, residue `−(cx)^d e^{d²}/(2d)` at `−d`, remainder analytic on `Re w > −½ − d`. -/
theorem dualDiagonalIntegrand_eq_two_poles_add_remainder {d : ℝ} (hd : 0 < d)
    (c x τ : ℝ) {w : ℂ} (hw0 : w ≠ 0) (hwd : w ≠ -(d : ℂ)) :
    dualDiagonalIntegrand d c x τ w
      = (zetaChi (displacedLinePt d τ) * zetaChi (displacedLinePt d (-τ))
          * riemannZeta ((1 + 2 * d : ℝ) : ℂ)) * w⁻¹
        + dualDiagonalShiftedResidue d c x * (w - (-(d : ℂ)))⁻¹
        + dualDiagonalRemainder d c x τ w := by
  have hd0 : (-(d : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hwd0 : w - (-(d : ℂ)) ≠ 0 := sub_ne_zero.mpr hwd
  have hpole : (((1 + 2 * d : ℝ) : ℂ) + 2 * w) ≠ 1 := by
    intro h
    apply hwd
    push_cast at h ⊢
    linear_combination h / 2
  have hquot : dualDiagonalIntegrand d c x τ w
      = dualDiagonalNumerator d c x τ w / (w * (w - (-(d : ℂ)))) := by
    rw [dualDiagonalIntegrand, carrierIntegrand, smoothAFEMellinIntegrand, smoothAFEGaussianKernel,
      dualDiagonalNumerator, regularizedRiemannZeta_of_ne_one hpole]
    have hcoord : (((1 + 2 * d : ℝ) : ℂ) + 2 * w - 1) = 2 * (w - (-(d : ℂ))) := by
      push_cast
      ring
    rw [hcoord]
    field_simp [hw0, hwd0]
  have hres0 : -dualDiagonalNumerator d c x τ 0 / (-(d : ℂ))
      = zetaChi (displacedLinePt d τ) * zetaChi (displacedLinePt d (-τ))
          * riemannZeta ((1 + 2 * d : ℝ) : ℂ) := by
    have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [dualDiagonalNumerator_zero hd]
    field_simp [hdc]
  have hresd : dualDiagonalNumerator d c x τ (-(d : ℂ)) / (-(d : ℂ))
      = dualDiagonalShiftedResidue d c x := by
    rw [dualDiagonalNumerator_neg_d, dualDiagonalShiftedResidue]
    field_simp [hd0]
  have hrem : dualDiagonalRemainder d c x τ w
      = (((dualDiagonalNumerator d c x τ w - dualDiagonalNumerator d c x τ 0) / w)
          - ((dualDiagonalNumerator d c x τ (-(d : ℂ)) - dualDiagonalNumerator d c x τ 0) / (-(d : ℂ))))
          / (w - (-(d : ℂ))) := by
    rw [dualDiagonalRemainder, dslope_of_ne _ hwd, slope_def_field, dslope_of_ne _ hw0,
      slope_def_field, dslope_of_ne _ hd0, slope_def_field]
    simp only [sub_zero]
  rw [hquot, two_pole_quotient_decomposition'' (N0 := dualDiagonalNumerator d c x τ 0)
    (Nρ := dualDiagonalNumerator d c x τ (-(d : ℂ))) hw0 hd0 hwd0, hres0, hresd, ← hrem]

/-! ## The exact cancellation of the zeta-pole residues -/

/-- **The two zeta-pole residues cancel exactly.** With the diagonal prefactors
`(hk)^{-σ₀}c^{-σ₀}` (direct) and `(hk)^{-σ₀}c^{σ₀−1}` (dual), `c = h'k'`, `σ₀ = ½ − d`:
`c^{-σ₀}·(x/c)^{δ₀}e^{δ₀²}/(2δ₀) + c^{σ₀−1}·(−(cx)^{d}e^{d²}/(2d)) = 0`. -/
theorem smoothDiagonalShiftedResidue_add_dual_cancel {d c x : ℝ} (hd : 0 < d) (hc : 0 < c)
    (hx : 0 < x) :
    ((c : ℂ) ^ (-((1 / 2 - d : ℝ) : ℂ))) * smoothDiagonalShiftedResidue (1 / 2 - d) c x
      + ((c : ℂ) ^ (((1 / 2 - d : ℝ) : ℂ) - 1)) * dualDiagonalShiftedResidue d c x = 0 := by
  unfold smoothDiagonalShiftedResidue dualDiagonalShiftedResidue diagonalShift
  have hshift : ((1 / 2 - (1 / 2 - d) : ℝ) : ℂ) = (d : ℂ) := by push_cast; ring
  rw [hshift]
  have hxc : ((x / c : ℝ) : ℂ) ^ (d : ℂ) = (x : ℂ) ^ (d : ℂ) * (c : ℂ) ^ (-(d : ℂ)) := by
    have := cpow_div_pos_neg hx hc (-(d : ℂ))
    rw [neg_neg] at this
    exact this
  have hcx : ((c * x : ℝ) : ℂ) ^ (d : ℂ) = (c : ℂ) ^ (d : ℂ) * (x : ℂ) ^ (d : ℂ) := by
    rw [Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg hc.le hx.le _
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have h1 : (c : ℂ) ^ (-((1 / 2 - d : ℝ) : ℂ)) * (c : ℂ) ^ (-(d : ℂ))
      = (c : ℂ) ^ (-(1 / 2 : ℂ)) := by
    rw [← Complex.cpow_add _ _ hc0]
    congr 1
    push_cast
    ring
  have h2 : (c : ℂ) ^ (((1 / 2 - d : ℝ) : ℂ) - 1) * (c : ℂ) ^ (d : ℂ)
      = (c : ℂ) ^ (-(1 / 2 : ℂ)) := by
    rw [← Complex.cpow_add _ _ hc0]
    congr 1
    push_cast
    ring
  rw [hxc, hcx]
  have hd0 : (2 * (d : ℂ)) ≠ 0 := by
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    exact mul_ne_zero two_ne_zero this
  calc (c : ℂ) ^ (-((1 / 2 - d : ℝ) : ℂ)) * ((x : ℂ) ^ (d : ℂ) * (c : ℂ) ^ (-(d : ℂ))
          * Complex.exp ((d : ℂ) ^ 2) / (2 * (d : ℂ)))
        + (c : ℂ) ^ (((1 / 2 - d : ℝ) : ℂ) - 1)
          * -((c : ℂ) ^ (d : ℂ) * (x : ℂ) ^ (d : ℂ) * Complex.exp ((d : ℂ) ^ 2) / (2 * (d : ℂ)))
      = ((c : ℂ) ^ (-((1 / 2 - d : ℝ) : ℂ)) * (c : ℂ) ^ (-(d : ℂ))
          - (c : ℂ) ^ (((1 / 2 - d : ℝ) : ℂ) - 1) * (c : ℂ) ^ (d : ℂ))
          * ((x : ℂ) ^ (d : ℂ) * Complex.exp ((d : ℂ) ^ 2) / (2 * (d : ℂ))) := by ring
    _ = 0 := by rw [h1, h2, sub_self, zero_mul]

end RHTower

end
