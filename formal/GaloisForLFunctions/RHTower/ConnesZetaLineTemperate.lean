import GaloisForLFunctions.RHTower.ConnesHolomorphicLineTemperate

/-!
# App I (25): `ζ` on the critical line has temperate growth

App I (25) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `|L(1/2 + it)| = O(|t|^N)`, *"in particular ... it is a multiplier of the algebra `𝒮(ℝ)`"*.

For `L = ζ` this is proved here, in the form the paper actually uses:
`t ↦ ζ(1/2 + it)` has temperate growth, hence — by mathlib's `SchwartzMap.smulLeftCLM` —
multiplies Schwartz functions to Schwartz functions, so `ζ(1/2+it)ψ̂(t)` is tempered.

The two ingredients are the corpus's polynomial bound on a vertical strip
(`RHTower.exists_bound_norm_riemannZeta_strip`) and the general upgrade
`connes_hasTemperateGrowth_lineRestrict`, which converts a pointwise bound on a *tube* around the
line into bounds on every derivative.  The tube of radius `1/8` about the critical line stays
inside `3/8 ≤ Re ≤ 5/8`, so it never meets the pole at `1`.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The open strip around the critical line used to run Cauchy's estimate. -/
def connesCriticalStrip : Set ℂ := {z : ℂ | 1 / 4 < z.re ∧ z.re < 3 / 4}

theorem connesCriticalStrip_isOpen : IsOpen connesCriticalStrip := by
  have h : connesCriticalStrip = Complex.re ⁻¹' (Set.Ioo (1 / 4) (3 / 4)) := by
    ext z
    simp [connesCriticalStrip, Set.mem_Ioo]
  rw [h]
  exact isOpen_Ioo.preimage Complex.continuous_re

theorem connesCriticalStrip_ne_one {z : ℂ} (hz : z ∈ connesCriticalStrip) : z ≠ 1 := by
  intro h
  have := hz.2
  rw [h] at this
  simp at this
  linarith

theorem connes_zeta_analyticOnNhd :
    AnalyticOnNhd ℂ riemannZeta connesCriticalStrip := by
  refine DifferentiableOn.analyticOnNhd ?_ connesCriticalStrip_isOpen
  intro z hz
  exact (differentiableAt_riemannZeta (connesCriticalStrip_ne_one hz)).differentiableWithinAt

theorem connes_criticalLine_mem (s : ℝ) :
    (1 / 2 : ℂ) + (s : ℂ) * I ∈ connesCriticalStrip := by
  have hre : ((1 / 2 : ℂ) + (s : ℂ) * I).re = 1 / 2 := by
    simp
  constructor <;> rw [hre] <;> norm_num

theorem connes_criticalTube_re {s : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall ((1 / 2 : ℂ) + (s : ℂ) * I) (1 / 8)) :
    3 / 8 ≤ z.re ∧ z.re ≤ 5 / 8 := by
  have hd : ‖z - ((1 / 2 : ℂ) + (s : ℂ) * I)‖ ≤ 1 / 8 := by
    rw [← Complex.dist_eq]
    exact Metric.mem_closedBall.mp hz
  have hre : |z.re - 1 / 2| ≤ 1 / 8 := by
    have h1 : |(z - ((1 / 2 : ℂ) + (s : ℂ) * I)).re|
        ≤ ‖z - ((1 / 2 : ℂ) + (s : ℂ) * I)‖ := Complex.abs_re_le_norm _
    have h2 : (z - ((1 / 2 : ℂ) + (s : ℂ) * I)).re = z.re - 1 / 2 := by
      simp
    rw [h2] at h1
    linarith
  have := abs_le.mp hre
  constructor <;> linarith [this.1, this.2]

theorem connes_criticalTube_im {s : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall ((1 / 2 : ℂ) + (s : ℂ) * I) (1 / 8)) :
    |z.im - s| ≤ 1 / 8 := by
  have hd : ‖z - ((1 / 2 : ℂ) + (s : ℂ) * I)‖ ≤ 1 / 8 := by
    rw [← Complex.dist_eq]
    exact Metric.mem_closedBall.mp hz
  have h1 : |(z - ((1 / 2 : ℂ) + (s : ℂ) * I)).im|
      ≤ ‖z - ((1 / 2 : ℂ) + (s : ℂ) * I)‖ := Complex.abs_im_le_norm _
  have h2 : (z - ((1 / 2 : ℂ) + (s : ℂ) * I)).im = z.im - s := by
    simp
  rw [h2] at h1
  linarith

theorem connes_criticalTube_subset (s : ℝ) :
    Metric.closedBall ((1 / 2 : ℂ) + (s : ℂ) * I) (1 / 8) ⊆ connesCriticalStrip := by
  intro z hz
  obtain ⟨h1, h2⟩ := connes_criticalTube_re hz
  exact ⟨by linarith, by linarith⟩

/-- The compact box that swallows the low-height part of the tube. -/
def connesCriticalBox : Set ℂ := Metric.closedBall (1 / 2 : ℂ) 2 ∩ {w : ℂ | w.re ≤ 5 / 8}

theorem connesCriticalBox_isCompact : IsCompact connesCriticalBox := by
  refine (isCompact_closedBall (1 / 2 : ℂ) 2).inter_right ?_
  exact isClosed_le Complex.continuous_re continuous_const

theorem connesCriticalBox_continuousOn : ContinuousOn riemannZeta connesCriticalBox := by
  intro z hz
  have hne : z ≠ 1 := by
    intro h
    have := hz.2
    rw [h] at this
    simp at this
    linarith
  exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt

theorem connes_criticalTube_mem_box {s : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall ((1 / 2 : ℂ) + (s : ℂ) * I) (1 / 8))
    (him : |z.im| ≤ 1) : z ∈ connesCriticalBox := by
  obtain ⟨hre1, hre2⟩ := connes_criticalTube_re hz
  refine ⟨?_, hre2⟩
  rw [Metric.mem_closedBall, Complex.dist_eq]
  have hbound : ‖z - (1 / 2 : ℂ)‖ ≤ |(z - (1 / 2 : ℂ)).re| + |(z - (1 / 2 : ℂ)).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  have h1 : (z - (1 / 2 : ℂ)).re = z.re - 1 / 2 := by simp
  have h2 : (z - (1 / 2 : ℂ)).im = z.im := by simp
  rw [h1, h2] at hbound
  have h3 : |z.re - 1 / 2| ≤ 1 / 8 := by
    rw [abs_le]
    constructor <;> linarith
  linarith

/-- **App I (25) for `ζ`.**  The zeta function restricted to the critical line has temperate
growth, hence is a multiplier of `𝒮(ℝ)`. -/
theorem connes_zeta_hasTemperateGrowth :
    Function.HasTemperateGrowth (fun t : ℝ => riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)) := by
  obtain ⟨C₁, N, hC₁0, hC₁⟩ := _root_.RHTower.exists_bound_norm_riemannZeta_strip 1
  obtain ⟨C₂, hC₂⟩ := connesCriticalBox_isCompact.exists_bound_of_continuousOn
    connesCriticalBox_continuousOn
  refine connes_hasTemperateGrowth_lineRestrict connesCriticalStrip_isOpen
    connes_zeta_analyticOnNhd (1 / 2 : ℂ) (by norm_num : (0 : ℝ) < 1 / 8)
    connes_criticalLine_mem (fun s z hz => connes_criticalTube_subset s hz)
    (C := C₁ + max C₂ 0) (N := N) ?_
  intro s z hz
  have hbase : (1 : ℝ) ≤ 1 + |s| := by
    have := abs_nonneg s
    linarith
  have hpow1 : (1 : ℝ) ≤ (1 + |s|) ^ N := one_le_pow₀ hbase
  have hpow0 : (0 : ℝ) ≤ (1 + |s|) ^ N := by positivity
  have hzeq : ((z.re : ℂ) + (z.im : ℂ) * I) = z := Complex.re_add_im z
  obtain ⟨hre1, hre2⟩ := connes_criticalTube_re hz
  have him := connes_criticalTube_im hz
  have hreabs : |z.re| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rcases le_or_gt 1 |z.im| with hbig | hsmall
  · have h1 := hC₁ z.re z.im hreabs hbig
    rw [hzeq] at h1
    have himle : |z.im| ≤ 1 + |s| := by
      have h2 := abs_le.mp him
      rcases abs_cases z.im with ⟨he, _⟩ | ⟨he, _⟩ <;>
        rcases abs_cases s with ⟨hs, _⟩ | ⟨hs, _⟩ <;> rw [he] <;> linarith [h2.1, h2.2]
    have hmono : |z.im| ^ N ≤ (1 + |s|) ^ N :=
      pow_le_pow_left₀ (abs_nonneg _) himle N
    have hC₂nn : (0 : ℝ) ≤ max C₂ 0 := le_max_right _ _
    calc ‖riemannZeta z‖ ≤ C₁ * |z.im| ^ N := h1
      _ ≤ C₁ * (1 + |s|) ^ N := mul_le_mul_of_nonneg_left hmono hC₁0
      _ ≤ (C₁ + max C₂ 0) * (1 + |s|) ^ N := by nlinarith
  · have hmem := connes_criticalTube_mem_box hz (le_of_lt hsmall)
    have h1 : ‖riemannZeta z‖ ≤ C₂ := hC₂ z hmem
    have h2 : ‖riemannZeta z‖ ≤ max C₂ 0 := le_trans h1 (le_max_left _ _)
    have hC₂nn : (0 : ℝ) ≤ max C₂ 0 := le_max_right _ _
    calc ‖riemannZeta z‖ ≤ max C₂ 0 := h2
      _ ≤ (C₁ + max C₂ 0) * (1 + |s|) ^ N := by nlinarith

/-- **The multiplier of App I (25).**  Multiplication by `ζ(1/2 + it)` as a continuous linear map
of the Schwartz space. -/
def connesZetaLineMultiplier : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun t : ℝ => riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I))

/-- **App I (25), the conclusion.**  `ζ(1/2+it)ψ(t)` is again a Schwartz function; in particular
`ζ(1/2+it)ψ̂(t)` is a tempered distribution, which is what Connes' argument needs. -/
theorem connesZetaLineMultiplier_apply (ψ : SchwartzMap ℝ ℂ) (t : ℝ) :
    connesZetaLineMultiplier ψ t = riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I) * ψ t := by
  rw [connesZetaLineMultiplier,
    SchwartzMap.smulLeftCLM_apply_apply connes_zeta_hasTemperateGrowth, smul_eq_mul]

end

end GaloisForLFunctions.RHTower
