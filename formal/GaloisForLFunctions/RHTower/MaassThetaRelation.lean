import GaloisForLFunctions.RHTower.MaassThetaMellin
import GaloisForLFunctions.RHTower.MaassGammaCorrections
import GaloisForLFunctions.HTGeometry.GammaVerticalStripDecay

/-!
# The theta relation of a Dirichlet series with the functional equation of `ζ²`

Let `G(s) = Σ g_n n^{−s}` converge absolutely for `Re s > 1` and let `Λ̂` be entire with
`Λ̂(s) = s²(s−1)² Γ_ℝ(s)² G(s)` on `Re s > 1`, `Λ̂(1 − s) = ε Λ̂(s)` with a sign `ε² = 1`, bounded
on the strip `−1/2 ≤ Re s ≤ 3/2`.  Put `a = Λ̂(1)` and `b = Λ̂'(1) − 2Λ̂(1)`, so that
`Λ(s) = Λ̂(s)/(s²(s−1)²) = a/(s−1)² + b/(s−1) + O(1)` near `1`.

**Theorem** (`kTheta_relation_sign`).  The `K₀`-theta function `Θ(y) = Σ g_n K₀(2πny)` satisfies

`Θ(y) − ε y^{−1} Θ(1/y) = ¼ [(b − a log y)/y − ε(b + a log y)]`   for `y > 0`;

`kTheta_relation` is the case `ε = 1`.

**Proof.**  `Θ` has Mellin transform `Λ/4` on `Re s = 3/2`, and `ε y^{−1}Θ(1/y)` has Mellin transform
`εΛ(1−s)/4 = Λ(s)/4` on `Re s = −1/2`.  The double poles at `0` and `1` are removed by the correction
`P = C(s) + εC(1−s)`, `C = A₀γ₀ + A₁γ₁` with `A₀ = −εb/4`, `A₁ = −εa/4`, whose Mellin pre-images on
the two lines differ by the elementary right-hand side above (`MaassGammaCorrections`).
`E = Λ/4 − P` is holomorphic on the strip: with `H(s) = (2π)^{−s}Γ(s+1)` and
`R₀(s) = A₀ sH(s) + A₁(sH'(s) − H(s)) = s²C(s)`,
`4s²(s−1)² E(s) = N(s) = Λ̂(s) − 4(s−1)²R₀(s) − 4εs²R₀(1−s)`, and `N(1 − s) = εN(s)` vanishes to
second order at `0` and `1` (`numN_zero`, `deriv_numN_zero`).  `E` decays like `Γ` in the strip,
and the two-line engine `eq_of_hasMellin_two_lines` concludes.
-/

open Complex Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.MaassThetaRelation

open MaassThetaMellin MaassGammaCorrections

/-! ## The polar data -/

variable (Λh : ℂ → ℂ) (ε : ℂ)

/-- `a = Λ̂(1)`. -/
def coeffA : ℂ := Λh 1

/-- `b = Λ̂'(1) − 2Λ̂(1)`. -/
def coeffB : ℂ := deriv Λh 1 - 2 * Λh 1

/-- `H(s) = (2π)^{−s} Γ(s + 1)`. -/
def hGam (s : ℂ) : ℂ := ((2 * Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma (s + 1)

theorem hGam_zero : hGam 0 = 1 := by simp [hGam]

theorem differentiableAt_hGam {s : ℂ} (hs : -1 < s.re) : DifferentiableAt ℂ hGam s := by
  unfold hGam
  refine DifferentiableAt.mul ?_ ?_
  · exact (differentiableAt_id.neg).const_cpow (Or.inl (by exact_mod_cast two_pi_pos.ne'))
  · refine (Complex.differentiableAt_Gamma _ fun m h => ?_).comp s (differentiableAt_id.add_const 1)
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

theorem isOpen_re_gt_neg_one : IsOpen {s : ℂ | -1 < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem differentiableOn_hGam : DifferentiableOn ℂ hGam {s : ℂ | -1 < s.re} :=
  fun _ hs => (differentiableAt_hGam hs).differentiableWithinAt

/-- `γ₀(s) = H(s)/s` for `s ≠ 0`. -/
theorem gam0_eq {s : ℂ} (hs : s ≠ 0) : gam0 s = hGam s / s := by
  unfold gam0 hGam
  rw [Complex.Gamma_add_one s hs]
  field_simp

/-- `γ₁(s) = H'(s)/s − H(s)/s²` for `s ≠ 0`, `Re s > −1`. -/
theorem gam1_eq {s : ℂ} (hs : s ≠ 0) (hre : -1 < s.re) :
    gam1 s = deriv hGam s / s - hGam s / s ^ 2 := by
  have hopen : IsOpen ({w : ℂ | -1 < w.re} ∩ {w | w ≠ 0}) :=
    isOpen_re_gt_neg_one.inter isOpen_ne
  have hev : gam0 =ᶠ[𝓝 s] fun w => hGam w / w :=
    Filter.eventually_of_mem (hopen.mem_nhds ⟨hre, hs⟩) fun w hw => gam0_eq hw.2
  have hd : HasDerivAt (fun w => hGam w / w)
      ((deriv hGam s * s - hGam s * 1) / s ^ 2) s :=
    (differentiableAt_hGam hre).hasDerivAt.div (hasDerivAt_id s) hs
  rw [gam1, hev.deriv_eq, hd.deriv]
  field_simp

/-- `A₀ = −εb/4`. -/
def cA0 : ℂ := -ε * coeffB Λh / 4

/-- `A₁ = −εa/4`. -/
def cA1 : ℂ := -ε * coeffA Λh / 4

/-- `R₀(s) = A₀ sH(s) + A₁(sH'(s) − H(s))`. -/
def rZero (s : ℂ) : ℂ := cA0 Λh ε * s * hGam s + cA1 Λh ε * (s * deriv hGam s - hGam s)

theorem sq_mul_corr_eq {s : ℂ} (hs : s ≠ 0) (hre : -1 < s.re) :
    s ^ 2 * (cA0 Λh ε * gam0 s + cA1 Λh ε * gam1 s) = rZero Λh ε s := by
  rw [gam0_eq hs, gam1_eq hs hre, rZero]
  field_simp

/-- The correction `P(s) = A₀(γ₀(s) + εγ₀(1−s)) + A₁(γ₁(s) + εγ₁(1−s))`. -/
def corrP (s : ℂ) : ℂ :=
  cA0 Λh ε * (gam0 s + ε * gam0 (1 - s)) + cA1 Λh ε * (gam1 s + ε * gam1 (1 - s))

/-- `N(s) = Λ̂(s) − 4(s−1)²R₀(s) − 4εs²R₀(1−s)`. -/
def numN (s : ℂ) : ℂ :=
  Λh s - 4 * (s - 1) ^ 2 * rZero Λh ε s - 4 * ε * s ^ 2 * rZero Λh ε (1 - s)

/-- The open strip `−1 < Re s < 2`. -/
def wideStrip : Set ℂ := {s : ℂ | -1 < s.re ∧ s.re < 2}

theorem isOpen_wideStrip : IsOpen wideStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

theorem one_sub_mem_wideStrip {s : ℂ} (hs : s ∈ wideStrip) : 1 - s ∈ wideStrip := by
  obtain ⟨h1, h2⟩ := hs
  constructor <;> simp <;> linarith

theorem zero_mem_wideStrip : (0 : ℂ) ∈ wideStrip := by constructor <;> simp

theorem one_mem_wideStrip : (1 : ℂ) ∈ wideStrip := by constructor <;> simp

variable {Λh} {ε}

theorem differentiableOn_rZero : DifferentiableOn ℂ (rZero Λh ε) {s : ℂ | -1 < s.re} := by
  intro s hs
  have hH := differentiableAt_hGam hs
  have hH' : DifferentiableAt ℂ (deriv hGam) s :=
    ((differentiableOn_hGam.analyticOnNhd isOpen_re_gt_neg_one).deriv s hs).differentiableAt
  unfold rZero
  exact (((differentiableAt_const _).mul differentiableAt_id).mul hH).add
    ((differentiableAt_const _).mul ((differentiableAt_id.mul hH').sub hH)) |>.differentiableWithinAt

theorem differentiableOn_numN (hΛ : Differentiable ℂ Λh) :
    DifferentiableOn ℂ (numN Λh ε) wideStrip := by
  intro s hs
  have h1 : DifferentiableAt ℂ (rZero Λh ε) s :=
    (differentiableOn_rZero s hs.1).differentiableAt (isOpen_re_gt_neg_one.mem_nhds hs.1)
  have hs' : -1 < (1 - s).re := by simp; linarith [hs.2]
  have h2 : DifferentiableAt ℂ (fun w => rZero Λh ε (1 - w)) s :=
    ((differentiableOn_rZero _ hs').differentiableAt (isOpen_re_gt_neg_one.mem_nhds hs')).comp s
      ((differentiableAt_const 1).sub differentiableAt_id)
  unfold numN
  exact (((hΛ s).sub (((differentiableAt_id.sub_const 1).pow 2).const_mul 4 |>.mul h1)).sub
    ((differentiableAt_id.pow 2).const_mul (4 * ε) |>.mul h2)).differentiableWithinAt

theorem numN_one_sub (hsym : ∀ s, Λh (1 - s) = ε * Λh s) (hε : ε * ε = 1) (s : ℂ) :
    numN Λh ε (1 - s) = ε * numN Λh ε s := by
  unfold numN
  rw [hsym, show 1 - (1 - s) = s by ring]
  linear_combination (4 * s ^ 2 * rZero Λh ε (1 - s)) * hε

theorem rZero_zero : rZero Λh ε 0 = -cA1 Λh ε := by simp [rZero, hGam_zero]

theorem deriv_rZero_zero : deriv (rZero Λh ε) 0 = cA0 Λh ε := by
  have hH := differentiableAt_hGam (s := 0) (by simp)
  have hH' : DifferentiableAt ℂ (deriv hGam) 0 :=
    ((differentiableOn_hGam.analyticOnNhd isOpen_re_gt_neg_one).deriv 0 (by simp)).differentiableAt
  have hd := ((((hasDerivAt_id' (0 : ℂ)).const_mul (cA0 Λh ε)).mul hH.hasDerivAt).add
    ((((hasDerivAt_id' (0 : ℂ)).mul hH'.hasDerivAt).sub hH.hasDerivAt).const_mul (cA1 Λh ε)))
  have hd' : HasDerivAt (rZero Λh ε) (cA0 Λh ε * 1 * hGam 0 + cA0 Λh ε * 0 * deriv hGam 0 +
      cA1 Λh ε * (1 * deriv hGam 0 + 0 * deriv (deriv hGam) 0 - deriv hGam 0)) 0 := hd
  rw [hd'.deriv, hGam_zero]
  ring

/-- `N(0) = 0`. -/
theorem numN_zero (hsym : ∀ s, Λh (1 - s) = ε * Λh s) (hε : ε * ε = 1) : numN Λh ε 0 = 0 := by
  have h := hsym 0
  simp only [sub_zero] at h
  simp only [numN, rZero_zero, cA1, coeffA]
  linear_combination (-Λh 0) * hε - ε * h

/-- `N'(0) = 0`. -/
theorem deriv_numN_zero (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = ε * Λh s)
    (hε : ε * ε = 1) : deriv (numN Λh ε) 0 = 0 := by
  have hr0 : DifferentiableAt ℂ (rZero Λh ε) 0 :=
    (differentiableOn_rZero 0 (by simp)).differentiableAt (isOpen_re_gt_neg_one.mem_nhds (by simp))
  have hr1 : DifferentiableAt ℂ (rZero Λh ε) (1 - 0) :=
    (differentiableOn_rZero _ (by simp)).differentiableAt (isOpen_re_gt_neg_one.mem_nhds (by simp))
  -- `εΛ̂'(0) = −Λ̂'(1)`
  have hΛ0 : ε * deriv Λh 0 = -deriv Λh 1 := by
    have h1 : HasDerivAt (fun s => Λh (1 - s)) (deriv Λh (1 - 0) * (-1)) 0 :=
      (hΛ (1 - 0)).hasDerivAt.comp 0 ((hasDerivAt_const _ _).sub (hasDerivAt_id 0)) |>.congr_deriv
        (by ring)
    have h2 : (fun s => Λh (1 - s)) = fun s => ε * Λh s := funext hsym
    rw [h2] at h1
    have h3 := ((hΛ 0).hasDerivAt.const_mul ε).unique h1
    rw [h3]
    simp
  have hr : HasDerivAt (fun s : ℂ => rZero Λh ε (1 - s)) (deriv (rZero Λh ε) (1 - 0) * (-1)) 0 :=
    hr1.hasDerivAt.comp 0 ((hasDerivAt_const _ _).sub (hasDerivAt_id' 0)) |>.congr_deriv (by ring)
  have hB := ((((hasDerivAt_id' (0 : ℂ)).sub_const 1).pow 2).mul hr0.hasDerivAt).const_mul 4
  have hC := (((hasDerivAt_id' (0 : ℂ)).pow 2).mul hr).const_mul (4 * ε)
  have hd := ((hΛ 0).hasDerivAt.sub hB).sub hC
  have hfun : numN Λh ε = fun s => Λh s - 4 * ((s - 1) ^ 2 * rZero Λh ε s) -
      4 * ε * (s ^ 2 * rZero Λh ε (1 - s)) := by
    funext s; unfold numN; ring
  have hd' : HasDerivAt (fun s => Λh s - 4 * ((s - 1) ^ 2 * rZero Λh ε s) -
      4 * ε * (s ^ 2 * rZero Λh ε (1 - s))) _ 0 := hd
  rw [hfun, hd'.deriv, rZero_zero, deriv_rZero_zero]
  simp only [cA0, cA1, coeffA, coeffB, Pi.pow_apply]
  push_cast
  linear_combination ε * hΛ0 - deriv Λh 0 * hε

/-- `N(1) = 0`. -/
theorem numN_one (hsym : ∀ s, Λh (1 - s) = ε * Λh s) (hε : ε * ε = 1) : numN Λh ε 1 = 0 := by
  have h := numN_one_sub hsym hε 0
  rw [sub_zero] at h
  rw [h, numN_zero hsym hε, mul_zero]

/-- `N'(1) = 0`. -/
theorem deriv_numN_one (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = ε * Λh s)
    (hε : ε * ε = 1) : deriv (numN Λh ε) 1 = 0 := by
  have hd0 : DifferentiableAt ℂ (numN Λh ε) (1 - 1) := by
    rw [sub_self]
    exact (differentiableOn_numN hΛ 0 zero_mem_wideStrip).differentiableAt
      (isOpen_wideStrip.mem_nhds zero_mem_wideStrip)
  have h1 : HasDerivAt (fun s => numN Λh ε (1 - s)) (deriv (numN Λh ε) (1 - 1) * (-1)) 1 :=
    hd0.hasDerivAt.comp 1 ((hasDerivAt_const _ _).sub (hasDerivAt_id' 1)) |>.congr_deriv (by ring)
  have h2 : (fun s => numN Λh ε (1 - s)) = fun s => ε * numN Λh ε s :=
    funext (numN_one_sub hsym hε)
  rw [h2, sub_self, deriv_numN_zero hΛ hsym hε] at h1
  have hd1 : DifferentiableAt ℂ (numN Λh ε) 1 :=
    (differentiableOn_numN hΛ 1 one_mem_wideStrip).differentiableAt
      (isOpen_wideStrip.mem_nhds one_mem_wideStrip)
  have h3 := (hd1.hasDerivAt.const_mul ε).unique h1
  have hε0 : ε ≠ 0 := by intro h; rw [h] at hε; simp at hε
  simpa [hε0] using h3

/-! ## The corrected function `E` -/

/-- `E = N/(4s²(s−1)²)`, the removable singularities at `0` and `1` filled in. -/
def eFun (Λh : ℂ → ℂ) (ε : ℂ) (s : ℂ) : ℂ :=
  dslope (dslope (dslope (dslope (numN Λh ε) 0) 0) 1) 1 s / 4

theorem differentiableOn_eFun (hΛ : Differentiable ℂ Λh) :
    DifferentiableOn ℂ (eFun Λh ε) wideStrip := by
  have h0 := isOpen_wideStrip.mem_nhds zero_mem_wideStrip
  have h1 := isOpen_wideStrip.mem_nhds one_mem_wideStrip
  have d1 : DifferentiableOn ℂ (dslope (numN Λh ε) 0) wideStrip :=
    (Complex.differentiableOn_dslope h0).mpr (differentiableOn_numN hΛ)
  have d2 : DifferentiableOn ℂ (dslope (dslope (numN Λh ε) 0) 0) wideStrip :=
    (Complex.differentiableOn_dslope h0).mpr d1
  have d3 : DifferentiableOn ℂ (dslope (dslope (dslope (numN Λh ε) 0) 0) 1) wideStrip :=
    (Complex.differentiableOn_dslope h1).mpr d2
  have d4 : DifferentiableOn ℂ (dslope (dslope (dslope (dslope (numN Λh ε) 0) 0) 1) 1) wideStrip :=
    (Complex.differentiableOn_dslope h1).mpr d3
  exact d4.div_const 4

/-- `dslope (dslope N 0) 0 = N/s²` off `0`. -/
theorem dslope_dslope_zero (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = ε * Λh s)
    (hε : ε * ε = 1) {s : ℂ} (hs : s ≠ 0) :
    dslope (dslope (numN Λh ε) 0) 0 s = numN Λh ε s / s ^ 2 := by
  rw [dslope_of_ne _ hs, slope_def_field, dslope_same, deriv_numN_zero hΛ hsym hε, dslope_of_ne _ hs,
    slope_def_field, numN_zero hsym hε]
  field_simp
  ring

theorem deriv_dslope_dslope_zero_one (hΛ : Differentiable ℂ Λh)
    (hsym : ∀ s, Λh (1 - s) = ε * Λh s) (hε : ε * ε = 1) :
    deriv (dslope (dslope (numN Λh ε) 0) 0) 1 = 0 := by
  have hev : dslope (dslope (numN Λh ε) 0) 0 =ᶠ[𝓝 1] fun s => numN Λh ε s / s ^ 2 :=
    Filter.eventually_of_mem (isOpen_ne.mem_nhds one_ne_zero) fun s hs =>
      dslope_dslope_zero hΛ hsym hε hs
  have hdN : DifferentiableAt ℂ (numN Λh ε) 1 :=
    (differentiableOn_numN hΛ 1 one_mem_wideStrip).differentiableAt
      (isOpen_wideStrip.mem_nhds one_mem_wideStrip)
  have hd := hdN.hasDerivAt.div ((hasDerivAt_id' (1 : ℂ)).pow 2) (by norm_num)
  rw [hev.deriv_eq]
  have hd' : HasDerivAt (fun s => numN Λh ε s / s ^ 2) _ 1 := hd
  rw [hd'.deriv, deriv_numN_one hΛ hsym hε, numN_one hsym hε]
  simp

/-- `E(s) = N(s)/(4s²(s−1)²)` for `s ≠ 0, 1`. -/
theorem eFun_eq (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = ε * Λh s) (hε : ε * ε = 1)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : eFun Λh ε s = numN Λh ε s / (4 * s ^ 2 * (s - 1) ^ 2) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hE2one : dslope (dslope (numN Λh ε) 0) 0 1 = 0 := by
    rw [dslope_dslope_zero hΛ hsym hε one_ne_zero, numN_one hsym hε]; simp
  unfold eFun
  rw [dslope_of_ne _ h1, slope_def_field, dslope_same, deriv_dslope_dslope_zero_one hΛ hsym hε,
    dslope_of_ne _ h1, slope_def_field, hE2one, dslope_dslope_zero hΛ hsym hε h0]
  field_simp
  ring

/-- Off `{0, 1}`: `s²(s−1)² P(s) = (s−1)² R₀(s) + εs² R₀(1−s)`. -/
theorem corrP_mul (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hw : s ∈ wideStrip) :
    s ^ 2 * (s - 1) ^ 2 * corrP Λh ε s =
      (s - 1) ^ 2 * rZero Λh ε s + ε * s ^ 2 * rZero Λh ε (1 - s) := by
  have hA := sq_mul_corr_eq Λh ε hs0 hw.1
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hB := sq_mul_corr_eq Λh ε h1s (by simp; linarith [hw.2])
  rw [← hA, ← hB, show (1 - s) ^ 2 = (s - 1) ^ 2 by ring]
  unfold corrP
  ring

/-- **The corrected function.**  Off `{0, 1}`, `E(s) = Λ̂(s)/(4s²(s−1)²) − P(s)`. -/
theorem eFun_eq_sub (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = ε * Λh s)
    (hε : ε * ε = 1) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hw : s ∈ wideStrip) :
    eFun Λh ε s = Λh s / (4 * s ^ 2 * (s - 1) ^ 2) - corrP Λh ε s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [eFun_eq hΛ hsym hε h0 h1]
  have hc := corrP_mul (Λh := Λh) (ε := ε) h0 h1 hw
  unfold numN
  field_simp
  linear_combination 4 * hc

/-! ## Decay on the strip -/

/-- `|t|^N e^{−π|t|/2} (1 + t²)` is bounded on `|t| ≥ 1`. -/
theorem exists_bound_pow_mul_exp (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 1 ≤ |t| →
      |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) * (1 + t ^ 2) ≤ K := by
  refine ⟨2 * (2 / Real.pi) ^ (N + 2) * (N + 2).factorial, by positivity, fun t ht => ?_⟩
  set x : ℝ := Real.pi * |t| / 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hfac := Real.pow_div_factorial_le_exp x hx0 (N + 2)
  have hexp : x ^ (N + 2) * Real.exp (-x) ≤ (N + 2).factorial := by
    have hf : (0 : ℝ) < (N + 2).factorial := by positivity
    rw [div_le_iff₀ hf] at hfac
    have h1 := mul_le_mul_of_nonneg_right hfac (Real.exp_nonneg (-x))
    have h2 : Real.exp x * ((N + 2).factorial : ℝ) * Real.exp (-x) = (N + 2).factorial := by
      rw [mul_comm (Real.exp x), mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    linarith
  have ht2 : 1 + t ^ 2 ≤ 2 * |t| ^ 2 := by
    have : 1 ≤ |t| ^ 2 := by nlinarith
    rw [sq_abs] at this ⊢
    linarith
  have htx : |t| = (2 / Real.pi) * x := by rw [hx]; field_simp
  calc |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) * (1 + t ^ 2)
      ≤ |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) * (2 * |t| ^ 2) := by gcongr
    _ = 2 * (|t| ^ (N + 2) * Real.exp (-x)) := by rw [hx]; ring_nf
    _ = 2 * ((2 / Real.pi) ^ (N + 2) * (x ^ (N + 2) * Real.exp (-x))) := by
        rw [htx, mul_pow]; ring
    _ ≤ 2 * ((2 / Real.pi) ^ (N + 2) * (N + 2).factorial) := by gcongr
    _ = _ := by ring

/-- `‖γ₀(s)‖ ≤ K/(1 + t²)` for `−1 ≤ Re s ≤ 2`, `|Im s| ≥ 1`. -/
theorem exists_bound_gam0 : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
    ‖gam0 s‖ ≤ K / (1 + s.im ^ 2) := by
  obtain ⟨C, N, hC, hG⟩ := exists_bound_norm_Gamma_vertical_strip (a := 1) one_pos 4
  obtain ⟨K, hK, hKb⟩ := exists_bound_pow_mul_exp N
  refine ⟨2 * Real.pi * (C * K), by positivity, fun s h1 h2 ht => ?_⟩
  have hs0 : s ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
  have hs1 : s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; rw [this] at ht; simp at ht; linarith
  have hG2 := hG (s.re + 2) s.im (by linarith) (by linarith) ht
  have hrepr : ((s.re + 2 : ℝ) : ℂ) + (s.im : ℂ) * I = s + 2 := by
    apply Complex.ext <;> simp
  rw [hrepr] at hG2
  -- `Γ(s) = Γ(s+2)/(s(s+1))`
  have hΓ : Complex.Gamma s = Complex.Gamma (s + 2) / (s * (s + 1)) := by
    rw [show s + 2 = (s + 1) + 1 by ring, Complex.Gamma_add_one _ hs1, Complex.Gamma_add_one _ hs0]
    field_simp
  have hden : 1 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul]
    have a1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    have a2 : |(s + 1).im| ≤ ‖s + 1‖ := Complex.abs_im_le_norm _
    simp only [add_im, one_im, add_zero] at a2
    nlinarith
  have hcp : ‖((2 * Real.pi : ℝ) : ℂ) ^ (-s)‖ ≤ 2 * Real.pi := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos two_pi_pos]
    simp only [neg_re]
    calc (2 * Real.pi) ^ (-s.re) ≤ (2 * Real.pi) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
      _ = 2 * Real.pi := Real.rpow_one _
  have hKt := hKb s.im ht
  have hpos : 0 < 1 + s.im ^ 2 := by positivity
  rw [gam0, norm_mul, hΓ, norm_div, le_div_iff₀ hpos]
  calc ‖((2 * Real.pi : ℝ) : ℂ) ^ (-s)‖ * (‖Complex.Gamma (s + 2)‖ / ‖s * (s + 1)‖) * (1 + s.im ^ 2)
      ≤ (2 * Real.pi) * (C * |s.im| ^ N * Real.exp (-(Real.pi * |s.im| / 2))) * (1 + s.im ^ 2) := by
        gcongr
        exact (div_le_self (norm_nonneg _) hden).trans hG2
    _ = 2 * Real.pi * C * (|s.im| ^ N * Real.exp (-(Real.pi * |s.im| / 2)) * (1 + s.im ^ 2)) := by
        ring
    _ ≤ 2 * Real.pi * C * K := by gcongr
    _ = 2 * Real.pi * (C * K) := by ring

theorem differentiableAt_gam0 {w : ℂ} (hw : ∀ m : ℕ, w ≠ -(m : ℂ)) : DifferentiableAt ℂ gam0 w := by
  unfold gam0
  exact ((differentiableAt_id.neg).const_cpow (Or.inl (by exact_mod_cast two_pi_pos.ne'))).mul
    (Complex.differentiableAt_Gamma w hw)

/-- `‖γ₁(s)‖ ≤ K/(1 + t²)` for `−1/2 ≤ Re s ≤ 3/2`, `|Im s| ≥ 2` (Cauchy estimate). -/
theorem exists_bound_gam1 : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → 2 ≤ |s.im| →
    ‖gam1 s‖ ≤ K / (1 + s.im ^ 2) := by
  obtain ⟨K, hK, hb⟩ := exists_bound_gam0
  refine ⟨4 * K, by positivity, fun s h1 h2 ht => ?_⟩
  have hpos : 0 < 1 + s.im ^ 2 := by positivity
  have hcirc : ∀ w ∈ Metric.closedBall s (1 / 2), -1 ≤ w.re ∧ w.re ≤ 2 ∧ |s.im| - 1 / 2 ≤ |w.im| := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have hre := (abs_le.mp ((Complex.abs_re_le_norm (w - s)).trans hw))
    have him := (Complex.abs_im_le_norm (w - s)).trans hw
    simp only [sub_re, sub_im] at hre him
    refine ⟨by linarith [hre.1], by linarith [hre.2], ?_⟩
    have := abs_sub_abs_le_abs_sub s.im w.im
    rw [abs_sub_comm] at him
    linarith
  have hdiff : DiffContOnCl ℂ gam0 (Metric.ball s (1 / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball s (by norm_num)]
    intro w hw
    refine (differentiableAt_gam0 fun m h => ?_).differentiableWithinAt
    have := (hcirc w hw).2.2
    rw [h] at this
    simp at this
    linarith
  have hbd : ∀ w ∈ Metric.sphere s (1 / 2), ‖gam0 w‖ ≤ 2 * K / (1 + s.im ^ 2) := by
    intro w hw
    have hw' := hcirc w (Metric.sphere_subset_closedBall hw)
    have hwt : 1 ≤ |w.im| := by linarith [hw'.2.2]
    refine (hb w hw'.1 hw'.2.1 hwt).trans ?_
    rw [div_le_div_iff₀ (by positivity) hpos]
    have hsq : (|s.im| - 1 / 2) ^ 2 ≤ w.im ^ 2 := by
      rw [← sq_abs w.im]
      exact pow_le_pow_left₀ (by linarith) hw'.2.2 2
    have h34 : (3 / 4) * |s.im| ≤ |s.im| - 1 / 2 := by linarith
    have h916 : (9 / 16) * s.im ^ 2 ≤ (|s.im| - 1 / 2) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) h34 2
      rw [mul_pow, sq_abs] at this
      linarith
    have hfin : 1 + s.im ^ 2 ≤ 2 * (1 + w.im ^ 2) := by nlinarith
    nlinarith
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) hdiff hbd
  rw [gam1]
  refine this.trans (le_of_eq ?_)
  field_simp
  ring

theorem verticalStrip_subset_wideStrip : verticalStrip (-1 / 2) (3 / 2) ⊆ wideStrip := by
  intro s hs
  rw [mem_verticalStrip] at hs
  constructor <;> linarith [hs.1, hs.2]

/-- **Decay of `E` on the strip.** -/
theorem exists_decay_eFun (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = ε * Λh s)
    (hε : ε * ε = 1) (hbd : ∃ B : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖Λh s‖ ≤ B) :
    ∃ C : ℝ, ∀ s ∈ verticalStrip (-1 / 2) (3 / 2), ‖eFun Λh ε s‖ ≤ C / (1 + s.im ^ 2) := by
  have hεn : ‖ε‖ = 1 := by
    have h := congrArg norm hε
    rw [norm_mul, norm_one] at h
    nlinarith [norm_nonneg ε]
  obtain ⟨B, hB⟩ := hbd
  obtain ⟨K₀, hK₀, hb₀⟩ := exists_bound_gam0
  obtain ⟨K₁, hK₁, hb₁⟩ := exists_bound_gam1
  -- the compact part
  set Kc : Set ℂ := (Icc (-1 / 2 : ℝ) (3 / 2)) ×ℂ (Icc (-2 : ℝ) 2) with hKc
  have hKcc : IsCompact Kc := isCompact_Icc.reProdIm isCompact_Icc
  have hKsub : Kc ⊆ wideStrip := by
    intro s hs
    rw [hKc, Complex.mem_reProdIm] at hs
    constructor <;> linarith [hs.1.1, hs.1.2]
  obtain ⟨M, hM⟩ := hKcc.exists_bound_of_continuousOn
    ((differentiableOn_eFun hΛ).continuousOn.mono hKsub)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by norm_num) (by norm_num))
  have hM0 : 0 ≤ M := by
    have := hM (0 : ℂ) (by rw [hKc, Complex.mem_reProdIm]; simp; norm_num)
    exact (norm_nonneg _).trans this
  refine ⟨5 * M + (B + 2 * ‖cA0 Λh ε‖ * K₀ + 2 * ‖cA1 Λh ε‖ * (K₀ + K₁)), fun s hs => ?_⟩
  rw [mem_verticalStrip] at hs
  have hpos : 0 < 1 + s.im ^ 2 := by positivity
  rcases le_or_gt |s.im| 2 with ht | ht
  · -- compact part
    have hsK : s ∈ Kc := by
      rw [hKc, Complex.mem_reProdIm]
      exact ⟨⟨hs.1, hs.2⟩, abs_le.mp ht⟩
    have h1 := hM s hsK
    rw [le_div_iff₀ hpos]
    have hle : 1 + s.im ^ 2 ≤ 5 := by
      have := sq_abs s.im
      nlinarith [abs_nonneg s.im]
    have hrest : 0 ≤ B + 2 * ‖cA0 Λh ε‖ * K₀ + 2 * ‖cA1 Λh ε‖ * (K₀ + K₁) := by positivity
    nlinarith [norm_nonneg (eFun Λh ε s)]
  · -- the tail: `E = Λ/4 − P`
    have h0 : s ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
    have h1 : s ≠ 1 := by intro h; rw [h] at ht; simp at ht; linarith
    have hw : s ∈ wideStrip := verticalStrip_subset_wideStrip (by rw [mem_verticalStrip]; exact hs)
    rw [eFun_eq_sub hΛ hsym hε h0 h1 hw]
    have ht1 : 1 ≤ |s.im| := by linarith
    have ht2 : 2 ≤ |s.im| := ht.le
    -- `‖Λ/(4s²(s−1)²)‖ ≤ B/(1+t²)`
    have hden : 1 + s.im ^ 2 ≤ ‖4 * s ^ 2 * (s - 1) ^ 2‖ := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, show ‖(4 : ℂ)‖ = 4 by norm_num]
      have a1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
      have a2 : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
      simp only [sub_im, one_im, sub_zero] at a2
      have hsq : s.im ^ 2 = |s.im| ^ 2 := (sq_abs _).symm
      have hx2 : 4 ≤ |s.im| ^ 2 := by nlinarith
      have : 1 + |s.im| ^ 2 ≤ 4 * |s.im| ^ 2 * |s.im| ^ 2 := by nlinarith
      calc 1 + s.im ^ 2 = 1 + |s.im| ^ 2 := by rw [hsq]
        _ ≤ 4 * |s.im| ^ 2 * |s.im| ^ 2 := this
        _ ≤ 4 * ‖s‖ ^ 2 * ‖s - 1‖ ^ 2 := by gcongr
    have hΛq : ‖Λh s / (4 * s ^ 2 * (s - 1) ^ 2)‖ ≤ B / (1 + s.im ^ 2) := by
      rw [norm_div]
      exact div_le_div₀ hB0 (hB s hs.1 hs.2) hpos hden
    -- the corrections
    have hre1 : -1 / 2 ≤ (1 - s).re := by simp; linarith [hs.2]
    have hre2 : (1 - s).re ≤ 3 / 2 := by simp; linarith [hs.1]
    have him : (1 - s).im ^ 2 = s.im ^ 2 := by simp
    have habs : |(1 - s).im| = |s.im| := by simp
    have g0s := hb₀ s (by linarith [hs.1]) (by linarith [hs.2]) ht1
    have g0r := hb₀ (1 - s) (by linarith) (by linarith) (by rw [habs]; exact ht1)
    have g1s := hb₁ s hs.1 hs.2 ht2
    have g1r := hb₁ (1 - s) hre1 hre2 (by rw [habs]; exact ht2)
    rw [him] at g0r g1r
    have hP : ‖corrP Λh ε s‖ ≤
        (2 * ‖cA0 Λh ε‖ * K₀ + 2 * ‖cA1 Λh ε‖ * (K₀ + K₁)) / (1 + s.im ^ 2) := by
      unfold corrP
      have e1 : ‖gam0 s + ε * gam0 (1 - s)‖ ≤ 2 * K₀ / (1 + s.im ^ 2) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, hεn, one_mul, mul_div_assoc, two_mul]
        exact add_le_add g0s g0r
      have e2 : ‖gam1 s + ε * gam1 (1 - s)‖ ≤ 2 * (K₀ + K₁) / (1 + s.im ^ 2) := by
        refine (norm_add_le _ _).trans ?_
        have : K₁ / (1 + s.im ^ 2) ≤ (K₀ + K₁) / (1 + s.im ^ 2) := by gcongr; linarith
        rw [norm_mul, hεn, one_mul, mul_div_assoc, two_mul]
        exact add_le_add (g1s.trans this) (g1r.trans this)
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      calc ‖cA0 Λh ε‖ * ‖gam0 s + ε * gam0 (1 - s)‖ + ‖cA1 Λh ε‖ * ‖gam1 s + ε * gam1 (1 - s)‖
          ≤ ‖cA0 Λh ε‖ * (2 * K₀ / (1 + s.im ^ 2)) +
              ‖cA1 Λh ε‖ * (2 * (K₀ + K₁) / (1 + s.im ^ 2)) := by
            gcongr
        _ = _ := by field_simp
    refine (norm_sub_le _ _).trans ?_
    calc ‖Λh s / (4 * s ^ 2 * (s - 1) ^ 2)‖ + ‖corrP Λh ε s‖
        ≤ B / (1 + s.im ^ 2) +
            (2 * ‖cA0 Λh ε‖ * K₀ + 2 * ‖cA1 Λh ε‖ * (K₀ + K₁)) / (1 + s.im ^ 2) :=
          add_le_add hΛq hP
      _ ≤ (5 * M + (B + 2 * ‖cA0 Λh ε‖ * K₀ + 2 * ‖cA1 Λh ε‖ * (K₀ + K₁))) / (1 + s.im ^ 2) := by
          rw [← add_div]
          apply div_le_div_of_nonneg_right _ hpos.le
          linarith

/-! ## The correction on the two lines -/

/-- The Mellin pre-image of `P` on `Re s = 3/2`. -/
def corrRight (Λh : ℂ → ℂ) (ε : ℂ) (y : ℝ) : ℂ :=
  cA0 Λh ε * (eTwo y + ε * ((y : ℂ) ^ (-1 : ℂ) * (eTwo y⁻¹ - 1))) +
    cA1 Λh ε * (Real.log y • eTwo y + ε * ((y : ℂ) ^ (-1 : ℂ) * (Real.log y⁻¹ • (eTwo y⁻¹ - 1))))

/-- The Mellin pre-image of `P` on `Re s = −1/2`. -/
def corrLeft (Λh : ℂ → ℂ) (ε : ℂ) (y : ℝ) : ℂ :=
  cA0 Λh ε * ((eTwo y - 1) + ε * ((y : ℂ) ^ (-1 : ℂ) * eTwo y⁻¹)) +
    cA1 Λh ε * (Real.log y • (eTwo y - 1) + ε * ((y : ℂ) ^ (-1 : ℂ) * (Real.log y⁻¹ • eTwo y⁻¹)))

/-- Scaling a Mellin pair. -/
theorem hasMellin_const_mul {f : ℝ → ℂ} {s m : ℂ} (h : HasMellin f s m) (c : ℂ) :
    HasMellin (fun y => c * f y) s (c * m) := by
  have h' := hasMellin_const_smul h.1 c
  refine ⟨h'.1, ?_⟩
  show mellin (fun y => c • f y) s = _
  rw [h'.2, h.2]
  rfl

/-- Combining Mellin pairs linearly. -/
theorem hasMellin_lin {f₁ f₂ f₃ f₄ : ℝ → ℂ} {s m₁ m₂ m₃ m₄ c₀ c₁ : ℂ} (h₁ : HasMellin f₁ s m₁)
    (h₂ : HasMellin f₂ s m₂) (h₃ : HasMellin f₃ s m₃) (h₄ : HasMellin f₄ s m₄) :
    HasMellin (fun y => c₀ * (f₁ y + f₂ y) + c₁ * (f₃ y + f₄ y)) s
      (c₀ * (m₁ + m₂) + c₁ * (m₃ + m₄)) := by
  have a12 := hasMellin_add h₁.1 h₂.1
  have a34 := hasMellin_add h₃.1 h₄.1
  have b12 := hasMellin_const_smul a12.1 c₀
  have b34 := hasMellin_const_smul a34.1 c₁
  have c := hasMellin_add b12.1 b34.1
  refine ⟨c.1, ?_⟩
  show mellin (fun y => c₀ • (f₁ y + f₂ y) + c₁ • (f₃ y + f₄ y)) s = _
  rw [c.2]
  have e12 : mellin (fun y => c₀ • (f₁ y + f₂ y)) s = c₀ * (m₁ + m₂) := by
    rw [show (fun y => c₀ • (f₁ y + f₂ y)) = fun y => c₀ • (fun t => f₁ t + f₂ t) y from rfl,
      b12.2, a12.2, h₁.2, h₂.2]; rfl
  have e34 : mellin (fun y => c₁ • (f₃ y + f₄ y)) s = c₁ * (m₃ + m₄) := by
    rw [show (fun y => c₁ • (f₃ y + f₄ y)) = fun y => c₁ • (fun t => f₃ t + f₄ t) y from rfl,
      b34.2, a34.2, h₃.2, h₄.2]; rfl
  rw [e12, e34]

theorem hasMellin_corrRight {s : ℂ} (hs : s.re = 3 / 2) :
    HasMellin (corrRight Λh ε) s (corrP Λh ε s) := by
  have h1s1 : -1 < (1 - s).re := by simp [hs]; norm_num
  have h1s2 : (1 - s).re < 0 := by simp [hs]; norm_num
  have hpos : 0 < s.re := by rw [hs]; norm_num
  have h := hasMellin_lin (c₀ := cA0 Λh ε) (c₁ := cA1 Λh ε) (hasMellin_eTwo hpos)
    (hasMellin_const_mul (hasMellin_dual_inv (hasMellin_eTwo_sub_one h1s1 h1s2)) ε)
    (hasMellin_log_eTwo hpos)
    (hasMellin_const_mul (hasMellin_dual_inv (hasMellin_log_eTwo_sub_one h1s1 h1s2)) ε)
  unfold corrRight corrP
  exact h

theorem hasMellin_corrLeft {s : ℂ} (hs : s.re = -1 / 2) :
    HasMellin (corrLeft Λh ε) s (corrP Λh ε s) := by
  have h1 : -1 < s.re := by rw [hs]; norm_num
  have h2 : s.re < 0 := by rw [hs]; norm_num
  have hpos : 0 < (1 - s).re := by simp [hs]; norm_num
  have h := hasMellin_lin (c₀ := cA0 Λh ε) (c₁ := cA1 Λh ε) (hasMellin_eTwo_sub_one h1 h2)
    (hasMellin_const_mul (hasMellin_dual_inv (hasMellin_eTwo hpos)) ε)
    (hasMellin_log_eTwo_sub_one h1 h2)
    (hasMellin_const_mul (hasMellin_dual_inv (hasMellin_log_eTwo hpos)) ε)
  unfold corrLeft corrP
  exact h

theorem corrRight_sub_corrLeft (hε : ε * ε = 1) {y : ℝ} :
    corrRight Λh ε y - corrLeft Λh ε y = (1 / 4) * ((coeffB Λh - coeffA Λh * Real.log y) / y -
      ε * (coeffB Λh + coeffA Λh * Real.log y)) := by
  have hinv : (y : ℂ) ^ (-1 : ℂ) = (y : ℂ)⁻¹ := by rw [Complex.cpow_neg_one]
  unfold corrRight corrLeft
  rw [hinv, Real.log_inv]
  simp only [Complex.real_smul, cA0, cA1]
  push_cast
  linear_combination ((coeffB Λh - coeffA Λh * Real.log y) / (4 * y)) * hε

theorem continuousAt_corr {y : ℝ} (hy : 0 < y) :
    ContinuousAt (corrRight Λh ε) y ∧ ContinuousAt (corrLeft Λh ε) y := by
  have hinv : ContinuousAt (fun t : ℝ => t⁻¹) y := continuousAt_inv₀ hy.ne'
  have hcp : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) y :=
    Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hy.ne')
  have he : ContinuousAt eTwo y := continuous_eTwo.continuousAt
  have hei : ContinuousAt (fun t : ℝ => eTwo t⁻¹) y := continuous_eTwo.continuousAt.comp hinv
  have hl : ContinuousAt (fun t : ℝ => (Real.log t : ℂ)) y :=
    Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hy.ne')
  have hli : ContinuousAt (fun t : ℝ => (Real.log t⁻¹ : ℂ)) y :=
    Complex.continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_log (inv_ne_zero hy.ne')).comp hinv)
  constructor
  · unfold corrRight
    simp only [Complex.real_smul]
    exact (continuousAt_const.mul (he.add (continuousAt_const.mul
      (hcp.mul (hei.sub continuousAt_const))))).add (continuousAt_const.mul ((hl.mul he).add
        (continuousAt_const.mul (hcp.mul (hli.mul (hei.sub continuousAt_const))))))
  · unfold corrLeft
    simp only [Complex.real_smul]
    exact (continuousAt_const.mul ((he.sub continuousAt_const).add
      (continuousAt_const.mul (hcp.mul hei)))).add (continuousAt_const.mul
        ((hl.mul (he.sub continuousAt_const)).add (continuousAt_const.mul (hcp.mul (hli.mul hei)))))

/-! ## The theta relation -/

variable {g : ℕ → ℂ}

/-- **The theta relation with sign `ε`.**
`Θ(y) − ε y^{−1}Θ(1/y) = ¼[(b − a log y)/y − ε(b + a log y)]`. -/
theorem kTheta_relation_sign
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ))
    (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = ε * Λh s) (hε : ε * ε = 1)
    (heq : ∀ s : ℂ, 1 < s.re → Λh s = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries g s)
    (hbd : ∃ B : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖Λh s‖ ≤ B) {y : ℝ} (hy : 0 < y) :
    kTheta g y - ε * ((y : ℂ) ^ (-1 : ℂ) * kTheta g y⁻¹) =
      (1 / 4) * ((coeffB Λh - coeffA Λh * Real.log y) / y -
        ε * (coeffB Λh + coeffA Λh * Real.log y)) := by
  obtain ⟨C, hC⟩ := exists_decay_eFun hΛ hsym hε hbd
  have hE : DifferentiableOn ℂ (eFun Λh ε) (verticalStrip (-1 / 2) (3 / 2)) :=
    (differentiableOn_eFun hΛ).mono verticalStrip_subset_wideStrip
  -- `Λ/4` on the lines
  have hΛq : ∀ s : ℂ, 1 < s.re →
      (1 / 4 : ℂ) * Complex.Gammaℝ s ^ 2 * LSeries g s = Λh s / (4 * s ^ 2 * (s - 1) ^ 2) := by
    intro s hs
    have h0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
    have h1 : s - 1 ≠ 0 := by intro h; rw [sub_eq_zero] at h; rw [h] at hs; simp at hs
    rw [heq s hs]
    field_simp
  have hR : ∀ s : ℂ, s.re = 3 / 2 →
      HasMellin (fun t => kTheta g t - corrRight Λh ε t) s (eFun Λh ε s) := by
    intro s hs
    have hs1 : 1 < s.re := by rw [hs]; norm_num
    have h0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
    have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
    have hw : s ∈ wideStrip := ⟨by rw [hs]; norm_num, by rw [hs]; norm_num⟩
    have hK := hasMellin_kTheta hsum hs1
    have hP := hasMellin_corrRight (Λh := Λh) (ε := ε) hs
    have hsub := hasMellin_sub hK.1 hP.1
    refine ⟨hsub.1, ?_⟩
    rw [hsub.2, hK.2, hP.2, hΛq s hs1, eFun_eq_sub hΛ hsym hε h0 h1 hw]
  have hL : ∀ s : ℂ, s.re = -1 / 2 →
      HasMellin (fun t => ε * ((t : ℂ) ^ (-1 : ℂ) * kTheta g t⁻¹) - corrLeft Λh ε t) s
        (eFun Λh ε s) := by
    intro s hs
    have hs1 : 1 < (1 - s).re := by simp [hs]; norm_num
    have h0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
    have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
    have hw : s ∈ wideStrip := ⟨by rw [hs]; norm_num, by rw [hs]; norm_num⟩
    have hK := hasMellin_const_mul (hasMellin_dual_inv (hasMellin_kTheta hsum hs1)) ε
    have hP := hasMellin_corrLeft (Λh := Λh) (ε := ε) hs
    have hsub := hasMellin_sub hK.1 hP.1
    refine ⟨hsub.1, ?_⟩
    rw [hsub.2, hK.2, hP.2, hΛq (1 - s) hs1, hsym, eFun_eq_sub hΛ hsym hε h0 h1 hw,
      show (1 - s - 1) ^ 2 = s ^ 2 by ring, show (1 - s) ^ 2 = (s - 1) ^ 2 by ring]
    have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
    field_simp
    linear_combination (Λh s) * hε
  have hc := continuousAt_corr (Λh := Λh) (ε := ε) hy
  have hkc : ContinuousAt (kTheta g) y :=
    (continuousOn_kTheta hsum).continuousAt (Ioi_mem_nhds hy)
  have hkci : ContinuousAt (fun t : ℝ => kTheta g t⁻¹) y :=
    ((continuousOn_kTheta hsum).continuousAt (Ioi_mem_nhds (inv_pos.mpr hy))).comp
      (continuousAt_inv₀ hy.ne')
  have hcp : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) y :=
    Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hy.ne')
  have heng := MaassThetaMellin.eq_of_hasMellin_two_lines (by norm_num) hE hC hR hL hy
    (hkc.sub hc.1) ((continuousAt_const.mul (hcp.mul hkci)).sub hc.2)
  rw [← corrRight_sub_corrLeft hε]
  linear_combination heng

/-- **The theta relation.**  `Θ(y) − y^{−1}Θ(1/y) = ¼[(b − a log y)/y − b − a log y]`. -/
theorem kTheta_relation (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ))
    (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = Λh s)
    (heq : ∀ s : ℂ, 1 < s.re → Λh s = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries g s)
    (hbd : ∃ B : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖Λh s‖ ≤ B) {y : ℝ} (hy : 0 < y) :
    kTheta g y - (y : ℂ) ^ (-1 : ℂ) * kTheta g y⁻¹ =
      (1 / 4) * ((coeffB Λh - coeffA Λh * Real.log y) / y - coeffB Λh - coeffA Λh * Real.log y) := by
  have h := kTheta_relation_sign (ε := 1) hsum hΛ (fun s => by rw [one_mul]; exact hsym s)
    (one_mul 1) heq hbd hy
  linear_combination h

end RHTower.MaassThetaRelation
