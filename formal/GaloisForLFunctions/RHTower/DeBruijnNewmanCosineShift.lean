import GaloisForLFunctions.RHTower.DeBruijnNewmanNonnegative
import GaloisForLFunctions.RHTower.XiCosineShiftLaguerrePolya
import GaloisForLFunctions.RHTower.RiemannKernelGaussianDampedNotLaguerrePolya
import GaloisForLFunctions.RHTower.XiLaguerrePolyaRiemannHypothesis
import GaloisForLFunctions.HTGeometry.LaguerrePolyaLocallyUniformLimit

/-!
# Newman's theorem along the cosine family of Ξ

For `τ > 0` and every shift `b > 0`, the backward heat image of the cosine shift
`A_b(z) = (Ξ(z + ib) + Ξ(z − ib))/2`, namely `(H_{−τ}(z + ib) + H_{−τ}(z − ib))/2`, has non-real zeros
of arbitrarily large real part (`exists_cosineShift_negHeat_zero_im_neg`).  Since `A_b` is
Laguerre–Pólya for `b ≥ ½` (`laguerrePolya_cosineShiftXi`), the de Bruijn–Newman constant of `A_b`
is exactly `0` for every `b ≥ ½`, unconditionally (`cosineShift_heat_threshold`), while RH is the
statement that `A_b` is Laguerre–Pólya for every `b > 0`
(`riemannHypothesis_iff_forall_laguerrePolya_cosineShift`): the shifts `A_b → Ξ` locally uniformly as
`b → 0`, and the Laguerre–Pólya class is closed.  Gaussian (heat) zero
slack is therefore not a critical-line phenomenon: it persists along the whole family, whereas the
finite-order Laguerre–Pólya slack of `A_b` opens for `b > 0` (`XiCosineFamilyLaguerrePolyaSlack`).

Proof.  In `s = ½ + iz`, the two terms are `A_τ(s − b)` and `A_τ(s + b)` with `A_τ = H_{−τ}`.
Normalised by `N_T(s)` on the disc around a zero `w₀` of the Gaussian-damped series `F_τ`
(`DeBruijnNewmanNonnegative`), the shifted term carries the extra normaliser factor
`e^{−2bL_T}`, of modulus `(T/2π)^{−b}`, because `lineShift` moves by `2b` while the archimedean
argument is unchanged.  The dominant term is within `δ/5` of `F_τ(w)` and the dominated one is below
`δ/10`, so the minimum-modulus argument still produces a zero inside the disc, at real part
`Re s ≥ 3/2 + b`, i.e. `Im z < 0`.
-/

open Complex MeasureTheory Filter Topology Set Metric

namespace RHTower.DeBruijn

noncomputable section

theorem exists_cosineShift_negHeat_zero_im_neg {τ : ℝ} (hτ : 0 < τ) {b : ℝ} (hb : 0 < b)
    (R : ℝ) :
    ∃ z : ℂ, riemannHeat (-τ) (z + b * I) + riemannHeat (-τ) (z - b * I) = 0 ∧ z.im < 0 ∧
      R ≤ z.re := by
  have hF := differentiable_gaussDirichlet hτ
  obtain ⟨w₀, hw₀⟩ := exists_gaussDirichlet_eq_zero hτ
  have hp : gaussDirichlet τ ((1 : ℝ) : ℂ) ≠ 0 := by
    intro h
    have := one_lt_gaussDirichlet_ofReal hτ 1
    rw [h, norm_zero] at this
    linarith
  obtain ⟨ρ, δ, hρ, hρ', hδ, hsph⟩ := exists_sphere_lower_of_entire hF hp w₀ (ε := 1 / 2)
    (by norm_num)
  obtain ⟨L₀, hL₀, hap⟩ := isStripAlmostPeriodic_gaussDirichlet hτ w₀.re 1 ρ (by linarith)
    (δ / 10) (by positivity)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp
    (eventually_norm_negHeatS_sub_le hτ w₀ hρ hρ' (ε := δ / 10) (by positivity))
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    (eventually_norm_negHeatS_sub_le hτ (w₀ - 2 * b) hρ hρ' (ε := 1) one_pos)
  -- the dominated partner decays like `(T/2π)^{−b}`
  set B : ℝ := Real.exp ((-w₀.re + 2 * b + ρ + 2) ^ 2 / (4 * τ)) * 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hdecay : Tendsto (fun T : ℝ => Real.exp (-(2 * b) * (horizontalSlope T).re)) atTop (𝓝 0) := by
    have hlog : Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi))) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
    have h2 : Tendsto (fun T : ℝ => -(2 * b) * (horizontalSlope T).re) atTop atBot := by
      simp only [horizontalSlope_re]
      have := hlog.atTop_mul_const (r := b) hb
      refine tendsto_neg_atTop_atBot.comp this |>.congr fun T => ?_
      simp only [Function.comp_apply]; ring
    exact Real.tendsto_exp_atBot.comp h2
  obtain ⟨T₃, hT₃⟩ := eventually_atTop.mp (hdecay.eventually
    (ge_mem_nhds (show (0 : ℝ) < δ / (10 * (B + 1)) by positivity)))
  set a₀ := max (max T₁ (max T₂ T₃))
    (max (|R| + |w₀.im| + 1) (2 * Real.pi * Real.exp ((|w₀.re| + 2 + b) / τ) + 1))
  obtain ⟨T', ⟨hT'a, -⟩, hT'ap⟩ := hap a₀
  have hT'T₁ : T₁ ≤ T' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT'a
  have hT'T₂ : T₂ ≤ T' :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hT'a
  have hT'T₃ : T₃ ≤ T' :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hT'a
  have hT'R : |R| + |w₀.im| + 1 ≤ T' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT'a
  have hT'L : 2 * Real.pi * Real.exp ((|w₀.re| + 2 + b) / τ) + 1 ≤ T' :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT'a
  have hT'pos : 0 < T' := by
    have : 0 < 2 * Real.pi * Real.exp ((|w₀.re| + 2 + b) / τ) := by positivity
    linarith
  have happrox := hT₁ T' hT'T₁
  have happrox₂ := hT₂ T' hT'T₂
  have hsmall := hT₃ T' hT'T₃
  -- the slope is large
  have hslope : |w₀.re| + 2 + b ≤ 2 * τ * (horizontalSlope T').re := by
    rw [horizontalSlope_re]
    have h1 : Real.exp ((|w₀.re| + 2 + b) / τ) ≤ T' / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    rw [div_le_iff₀ hτ] at h2
    linarith
  -- the normalised function
  set s : ℂ → ℂ := discPoint τ T'
  set N : ℂ → ℂ := normaliser τ w₀ T'
  have hsre : ∀ w, (s w + lineShift τ w₀ T').re = 2 + w.re - w₀.re := fun w => by
    rw [discPoint_add_lineShift]; simp
  have hsim : ∀ w, (s w + lineShift τ w₀ T').im = w.im + T' + τ * (Real.pi / 2) := fun w => by
    rw [discPoint_add_lineShift]; simp
  have hball_re : ∀ w ∈ closedBall w₀ ρ, |w.re - w₀.re| ≤ ρ := fun w hw => by
    have := (Complex.abs_re_le_norm (w - w₀)).trans (mem_closedBall_iff_norm.mp hw)
    simpa using this
  have hball_im : ∀ w ∈ closedBall w₀ ρ, |w.im - w₀.im| ≤ ρ := fun w hw => by
    have := (Complex.abs_im_le_norm (w - w₀)).trans (mem_closedBall_iff_norm.mp hw)
    simpa using this
  have hNne : ∀ w ∈ closedBall w₀ ρ, N (s w) ≠ 0 := by
    intro w hw
    have hr := hball_re w hw
    have hi := hball_im w hw
    refine mul_ne_zero (archG_ne_zero ?_ ?_) (Complex.exp_ne_zero _)
    · rw [hsre]; have := (abs_le.mp hr).1; linarith
    · intro h
      have := congrArg Complex.im h
      rw [hsim] at this
      simp at this
      have := (abs_le.mp hi).1
      have : 0 ≤ τ * (Real.pi / 2) := by positivity
      have := neg_abs_le w₀.im
      have := abs_nonneg R
      linarith
  have hNd : DifferentiableOn ℂ (fun w => N (s w)) (closedBall w₀ ρ) := by
    intro w hw
    have hr := hball_re w hw
    have hre : 0 < (s w + lineShift τ w₀ T').re := by
      rw [hsre]; have := (abs_le.mp hr).1; linarith
    have h1 : DifferentiableAt ℂ (fun w => archG (s w + lineShift τ w₀ T')) w :=
      (differentiableAt_archG hre).comp w (f := fun w => s w + (lineShift τ w₀ T' : ℂ))
        (((differentiable_discPoint τ T') w).add_const _)
    exact (h1.mul (differentiableAt_const _)).differentiableWithinAt
  -- the dominant term
  set g₁ : ℂ → ℂ := fun w => negHeatS τ (s w) / N (s w)
  set g₂ : ℂ → ℂ := fun w => negHeatS τ (s w - 2 * b) / N (s w)
  have hg₁d : DifferentiableOn ℂ g₁ (closedBall w₀ ρ) := by
    refine DifferentiableOn.div ?_ hNd hNne
    exact ((differentiable_negHeatS τ).comp (differentiable_discPoint τ T')).differentiableOn
  have hg₂d : DifferentiableOn ℂ g₂ (closedBall w₀ ρ) := by
    refine DifferentiableOn.div ?_ hNd hNne
    exact ((differentiable_negHeatS τ).comp
      ((differentiable_discPoint τ T').sub_const _)).differentiableOn
  have herr : ∀ w ∈ closedBall w₀ ρ, ‖g₁ w - gaussDirichlet τ (w + T' * I)‖ ≤ δ / 10 := by
    intro w hw
    have hN0 : 0 < ‖N (s w)‖ := norm_pos_iff.mpr (hNne w hw)
    have hsplit : g₁ w - gaussDirichlet τ (w + T' * I) =
        (negHeatS τ (s w) - N (s w) * gaussDirichlet τ (w + T' * I)) / N (s w) := by
      simp only [g₁]
      field_simp [hNne w hw]
    rw [hsplit, norm_div, div_le_iff₀ hN0]
    exact happrox w hw
  -- the dominated partner
  have hextra : ∀ w ∈ closedBall w₀ ρ, ‖g₂ w‖ ≤ δ / 10 := by
    intro w hw
    have hN0 : 0 < ‖N (s w)‖ := norm_pos_iff.mpr (hNne w hw)
    have hw' : w - 2 * b ∈ closedBall (w₀ - 2 * b) ρ := by
      rw [mem_closedBall, dist_eq_norm] at hw ⊢
      rwa [show w - 2 * b - (w₀ - 2 * b) = w - w₀ by ring]
    have hdp : s (w - 2 * b) = s w - 2 * b := by
      simp only [s, discPoint]; ring
    have hls : lineShift τ (w₀ - 2 * b) T' = lineShift τ w₀ T' + 2 * b := by
      simp [lineShift]; ring
    have hnorm : normaliser τ (w₀ - 2 * b) T' (s w - 2 * b) =
        N (s w) * Complex.exp (-(2 * b * horizontalSlope T')) := by
      have e1 : s w - 2 * (b : ℂ) + ((lineShift τ w₀ T' + 2 * b : ℝ) : ℂ) =
          s w + (lineShift τ w₀ T' : ℂ) := by push_cast; ring
      simp only [N, normaliser]
      rw [hls, e1, mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast; ring
    have hexp : ‖Complex.exp (-(2 * b * horizontalSlope T'))‖ =
        Real.exp (-(2 * b) * (horizontalSlope T').re) := by
      rw [Complex.norm_exp]
      congr 1
      have : (2 * (b : ℂ) * horizontalSlope T').re = 2 * b * (horizontalSlope T').re := by
        rw [show (2 * (b : ℂ)) = ((2 * b : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
      rw [Complex.neg_re, this]; ring
    have h2 := happrox₂ (w - 2 * b) hw'
    rw [hdp, hnorm, one_mul, norm_mul, hexp] at h2
    have hgd : ‖gaussDirichlet τ (w - 2 * b + T' * I)‖ ≤ B := by
      refine norm_gaussDirichlet_le hτ ?_
      have hr := hball_re w hw
      have := (abs_le.mp hr).1
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.re_ofNat,
        Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      linarith
    have hbound : ‖negHeatS τ (s w - 2 * b)‖ ≤
        ‖N (s w)‖ * (Real.exp (-(2 * b) * (horizontalSlope T').re) * (B + 1)) := by
      set e := Real.exp (-(2 * b) * (horizontalSlope T').re)
      have hM : ‖N (s w) * Complex.exp (-(2 * b * horizontalSlope T')) *
          gaussDirichlet τ (w - 2 * b + T' * I)‖ ≤ ‖N (s w)‖ * (e * B) := by
        rw [norm_mul, norm_mul, hexp, mul_assoc]
        gcongr
      have htri := norm_le_insert' (negHeatS τ (s w - 2 * b))
        (N (s w) * Complex.exp (-(2 * b * horizontalSlope T')) *
          gaussDirichlet τ (w - 2 * b + T' * I))
      have : ‖N (s w)‖ * (e * (B + 1)) = ‖N (s w)‖ * (e * B) + ‖N (s w)‖ * e := by ring
      linarith
    have hsm : Real.exp (-(2 * b) * (horizontalSlope T').re) * (B + 1) ≤ δ / 10 := by
      have h0 : Real.exp (-(2 * b) * (horizontalSlope T').re) ≤ δ / (10 * (B + 1)) := hsmall
      calc Real.exp (-(2 * b) * (horizontalSlope T').re) * (B + 1)
          ≤ δ / (10 * (B + 1)) * (B + 1) := by gcongr
        _ = δ / 10 := by field_simp
    simp only [g₂]
    rw [norm_div, div_le_iff₀ hN0]
    calc ‖negHeatS τ (s w - 2 * b)‖
        ≤ ‖N (s w)‖ * (Real.exp (-(2 * b) * (horizontalSlope T').re) * (B + 1)) := hbound
      _ ≤ ‖N (s w)‖ * (δ / 10) := by gcongr
      _ = δ / 10 * ‖N (s w)‖ := by ring
  -- the sum
  set g : ℂ → ℂ := fun w => g₁ w + g₂ w
  have hgd : DifferentiableOn ℂ g (closedBall w₀ ρ) := hg₁d.add hg₂d
  have hap' : ∀ w ∈ closedBall w₀ ρ, ‖gaussDirichlet τ (w + T' * I) - gaussDirichlet τ w‖ ≤ δ / 10 :=
    fun w hw => hT'ap w (hball_re w hw)
  have hclose : ∀ w ∈ closedBall w₀ ρ, ‖g w - gaussDirichlet τ w‖ ≤ 3 * δ / 10 := by
    intro w hw
    have e : g w - gaussDirichlet τ w = (g₁ w - gaussDirichlet τ (w + T' * I)) +
        (gaussDirichlet τ (w + T' * I) - gaussDirichlet τ w) + g₂ w := by
      simp only [g]; ring
    rw [e]
    have := norm_add₃_le (a := g₁ w - gaussDirichlet τ (w + T' * I))
      (b := gaussDirichlet τ (w + T' * I) - gaussDirichlet τ w) (c := g₂ w)
    linarith [herr w hw, hap' w hw, hextra w hw]
  have hsphere : ∀ w ∈ sphere w₀ ρ, ‖g w₀‖ < ‖g w‖ := by
    intro w hw
    have hwc : w ∈ closedBall w₀ ρ := sphere_subset_closedBall hw
    have hc : w₀ ∈ closedBall w₀ ρ := mem_closedBall_self hρ.le
    have h1 := hclose w₀ hc
    rw [hw₀, sub_zero] at h1
    have h2 := hclose w hwc
    have h3 := hsph w hw
    have h4 : ‖gaussDirichlet τ w‖ ≤ ‖g w‖ + ‖g w - gaussDirichlet τ w‖ := by
      have := norm_sub_le (g w) (g w - gaussDirichlet τ w)
      rwa [sub_sub_cancel] at this
    linarith
  obtain ⟨wz, hwz, hzero⟩ := exists_zero_of_norm_lt_sphere_on hρ hgd hsphere
  have hwzc : wz ∈ closedBall w₀ ρ := ball_subset_closedBall hwz
  have hA : negHeatS τ (s wz) + negHeatS τ (s wz - 2 * b) = 0 := by
    have hN := hNne wz hwzc
    have : g wz = (negHeatS τ (s wz) + negHeatS τ (s wz - 2 * b)) / N (s wz) := by
      simp only [g, g₁, g₂]; field_simp
    rw [this] at hzero
    rcases div_eq_zero_iff.mp hzero with h0 | h0
    · exact h0
    · exact absurd h0 hN
  refine ⟨-I * (s wz - b - 1 / 2), ?_, ?_, ?_⟩
  · have e1 : -I * (s wz - b - 1 / 2) + b * I = -I * ((s wz - 2 * b) - 1 / 2) := by ring
    have e2 : -I * (s wz - b - 1 / 2) - b * I = -I * (s wz - 1 / 2) := by ring
    rw [e1, e2, ← negHeatS, ← negHeatS, add_comm]
    exact hA
  · have e : (-I * (s wz - b - 1 / 2)).im = -((s wz).re - b - 1 / 2) := by
      simp [Complex.mul_im]
    rw [e]
    have hsre' : (s wz).re = wz.re + 2 * τ * (horizontalSlope T').re := by
      simp [s, discPoint]
    have := (abs_le.mp (hball_re wz hwzc)).1
    have := neg_abs_le w₀.re
    rw [hsre']
    linarith
  · have e : (-I * (s wz - b - 1 / 2)).re = (s wz).im := by simp [Complex.mul_re]
    rw [e]
    have hsim' : (s wz).im = wz.im + T' + τ * (Real.pi / 2) := by
      simp [s, discPoint, horizontalSlope]; ring
    rw [hsim']
    have := (abs_le.mp (hball_im wz hwzc)).1
    have := neg_abs_le w₀.im
    have : 0 ≤ τ * (Real.pi / 2) := by positivity
    have := le_abs_self R
    linarith

/-- **Infinitely many non-real zeros along the cosine family.** -/
theorem cosineShift_negHeat_nonreal_zeros_infinite {τ : ℝ} (hτ : 0 < τ) {b : ℝ} (hb : 0 < b) :
    {z : ℂ | riemannHeat (-τ) (z + b * I) + riemannHeat (-τ) (z - b * I) = 0 ∧ z.im ≠ 0}.Infinite := by
  intro hfin
  obtain ⟨R, hR⟩ := (hfin.image Complex.re).bddAbove
  obtain ⟨z, hz, him, hre⟩ := exists_cosineShift_negHeat_zero_im_neg hτ hb (R + 1)
  have := hR ⟨z, ⟨hz, him.ne⟩, rfl⟩
  linarith

/-- `x ↦ Φ(x)e^{−τx²}e^{cx}` is integrable for `τ ≥ 0`. -/
theorem integrable_riemannKernelReal_mul_gauss_mul_exp {τ : ℝ} (hτ : 0 ≤ τ) (c : ℝ) :
    Integrable fun x : ℝ => riemannKernelReal x * Real.exp (-τ * x ^ 2) * Real.exp (c * x) := by
  obtain ⟨C, hC0, hC⟩ := KernelStrip.exists_norm_riemannPhiKernel_le_exp (|c| + 1)
  refine ((RHTower.integrable_exp_neg_mul_abs' (c := 1) one_pos).const_mul C).mono'
    ((continuous_riemannKernelReal.mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have h := hC x
  rw [riemannPhiKernel_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
  have hg : Real.exp (-τ * x ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have he : Real.exp (c * x) ≤ Real.exp (|c| * |x|) := Real.exp_le_exp.mpr
    ((le_abs_self (c * x)).trans_eq (abs_mul c x))
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos (c * x))]
  calc |riemannKernelReal x| * Real.exp (-τ * x ^ 2) * Real.exp (c * x)
      ≤ C * Real.exp (-((|c| + 1) * |x|)) * 1 * Real.exp (|c| * |x|) := by gcongr
    _ = C * Real.exp (-(1 * |x|)) := by
      rw [mul_one, mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- On the imaginary axis the backward heat flow is a real Laplace transform:
`H_{−τ}(ic) = ∫ Φ(x) e^{−τx²} e^{−cx} dx`. -/
theorem riemannHeat_neg_ofReal_mul_I (τ c : ℝ) :
    riemannHeat (-τ) ((c : ℂ) * I) =
      ((∫ x : ℝ, riemannKernelReal x * Real.exp (-τ * x ^ 2) * Real.exp (-c * x) : ℝ) : ℂ) := by
  unfold riemannHeat cosTransform
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have e : I * ((c : ℂ) * I) * (x : ℂ) = ((-c * x : ℝ) : ℂ) := by
    push_cast
    linear_combination ((c : ℂ) * (x : ℂ)) * Complex.I_sq
  simp only
  rw [e, ← Complex.ofReal_exp]
  push_cast
  ring

theorem riemannHeat_neg_ofReal_mul_I_pos {τ : ℝ} (hτ : 0 ≤ τ) (c : ℝ) :
    0 < ∫ x : ℝ, riemannKernelReal x * Real.exp (-τ * x ^ 2) * Real.exp (-c * x) := by
  have hpos : ∀ x : ℝ, 0 < riemannKernelReal x * Real.exp (-τ * x ^ 2) * Real.exp (-c * x) :=
    fun x => mul_pos (mul_pos (riemannKernelReal_pos x) (Real.exp_pos _)) (Real.exp_pos _)
  rw [integral_pos_iff_support_of_nonneg (fun x => (hpos x).le)
    (integrable_riemannKernelReal_mul_gauss_mul_exp hτ (-c))]
  have hs : Function.support
      (fun x : ℝ => riemannKernelReal x * Real.exp (-τ * x ^ 2) * Real.exp (-c * x)) = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hpos x).ne'
  rw [hs, Real.volume_univ]
  exact ENNReal.zero_lt_top

/-- **The de Bruijn–Newman constant of the cosine family is `0` for `b ≥ ½`.** The cosine shift
`(Ξ(z+ib) + Ξ(z−ib))/2` is Laguerre–Pólya, while its backward heat image at every time `−τ < 0`
is not. -/
theorem cosineShift_heat_threshold {b : ℝ} (hb : 1 / 2 ≤ b) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya
        (fun z => (riemannHeat 0 (z + b * I) + riemannHeat 0 (z - b * I)) / 2) ∧
      ∀ τ : ℝ, 0 < τ → ¬ GaloisForLFunctions.HTGeometry.LaguerrePolya
        (fun z => (riemannHeat (-τ) (z + b * I) + riemannHeat (-τ) (z - b * I)) / 2) := by
  constructor
  · have e : (fun z => (riemannHeat 0 (z + b * I) + riemannHeat 0 (z - b * I)) / 2) =
        fun z => (XiC (z + b * I) + XiC (z - b * I)) / 2 := by
      funext z
      rw [riemannHeat_zero, riemannHeat_zero, XiC, XiC, mul_comm I (z + b * I),
        mul_comm I (z - b * I)]
    rw [e]
    exact laguerrePolya_cosineShiftXi hb
  · intro τ hτ hLP
    have hb0 : 0 < b := by linarith
    obtain ⟨z, hz, him, -⟩ := exists_cosineShift_negHeat_zero_im_neg hτ hb0 0
    have h0 : (riemannHeat (-τ) (0 + b * I) + riemannHeat (-τ) (0 - b * I)) / 2 ≠ 0 := by
      have e1 : (0 : ℂ) + b * I = (b : ℂ) * I := zero_add _
      have e2 : (0 : ℂ) - b * I = ((-b : ℝ) : ℂ) * I := by push_cast; ring
      rw [e1, e2, riemannHeat_neg_ofReal_mul_I, riemannHeat_neg_ofReal_mul_I]
      have p1 := riemannHeat_neg_ofReal_mul_I_pos hτ.le b
      have p2 := riemannHeat_neg_ofReal_mul_I_pos hτ.le (-b)
      intro h
      have := congrArg Complex.re h
      simp only [Complex.div_ofNat_re, Complex.add_re, Complex.ofReal_re, Complex.zero_re] at this
      linarith
    have hzero : (fun z => (riemannHeat (-τ) (z + b * I) + riemannHeat (-τ) (z - b * I)) / 2) z
        = 0 := by
      show (riemannHeat (-τ) (z + b * I) + riemannHeat (-τ) (z - b * I)) / 2 = 0
      rw [hz, zero_div]
    exact him.ne (GaloisForLFunctions.HTGeometry.im_eq_zero_of_laguerrePolya hLP h0 hzero)

/-- The cosine shifts converge to `Ξ`: `(Ξ(z + i/(m+1)) + Ξ(z − i/(m+1)))/2 → Ξ(z)` locally
uniformly. -/
theorem tendstoLocallyUniformly_cosineShift_XiC :
    TendstoLocallyUniformly
      (fun (m : ℕ) (z : ℂ) =>
        (XiC (z + ((1 / ((m : ℝ) + 1) : ℝ) : ℂ) * I) +
          XiC (z - ((1 / ((m : ℝ) + 1) : ℝ) : ℂ) * I)) / 2) XiC atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hcont : Continuous XiC := continuous_iff_continuousAt.mpr fun z =>
    (XiC_analytic z (mem_univ z)).continuousAt
  have huc := (isCompact_closedBall (0 : ℂ) (R + 1)).uniformContinuousOn_of_continuous
    hcont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := huc ε hε
  have hev : ∀ᶠ m : ℕ in atTop, 1 / ((m : ℝ) + 1) < min δ 1 :=
    (tendsto_one_div_add_atTop_nhds_zero_nat).eventually (gt_mem_nhds (lt_min hδ one_pos))
  filter_upwards [hev] with m hm z hz
  set c : ℝ := 1 / ((m : ℝ) + 1) with hc
  have hc0 : 0 < c := by positivity
  have hcδ : c < δ := lt_of_lt_of_le hm (min_le_left _ _)
  have hc1 : c < 1 := lt_of_lt_of_le hm (min_le_right _ _)
  have hzR : ‖z‖ ≤ R := by simpa using hR hz
  have hnorm : ‖(c : ℂ) * I‖ = c := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  have hz0 : z ∈ closedBall (0 : ℂ) (R + 1) := by
    rw [mem_closedBall, dist_zero_right]; linarith
  have hzp : z + (c : ℂ) * I ∈ closedBall (0 : ℂ) (R + 1) := by
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_add_le z ((c : ℂ) * I)]
  have hzm : z - (c : ℂ) * I ∈ closedBall (0 : ℂ) (R + 1) := by
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_sub_le z ((c : ℂ) * I)]
  have d1 : dist z (z + (c : ℂ) * I) < δ := by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, hnorm]; exact hcδ
  have d2 : dist z (z - (c : ℂ) * I) < δ := by
    rw [dist_eq_norm, sub_sub_cancel, hnorm]; exact hcδ
  have e1 := hclose z hz0 _ hzp d1
  have e2 := hclose z hz0 _ hzm d2
  rw [dist_eq_norm] at e1 e2 ⊢
  have hsplit : XiC z - (XiC (z + (c : ℂ) * I) + XiC (z - (c : ℂ) * I)) / 2 =
      ((XiC z - XiC (z + (c : ℂ) * I)) + (XiC z - XiC (z - (c : ℂ) * I))) / 2 := by ring
  rw [hsplit, norm_div, Complex.norm_ofNat]
  have := norm_add_le (XiC z - XiC (z + (c : ℂ) * I)) (XiC z - XiC (z - (c : ℂ) * I))
  linarith

/-- **RH is Laguerre–Pólya membership of the whole cosine family.** -/
theorem riemannHypothesis_iff_forall_laguerrePolya_cosineShift :
    RiemannHypothesis ↔ ∀ b : ℝ, 0 < b → GaloisForLFunctions.HTGeometry.LaguerrePolya
      (fun z => (XiC (z + b * I) + XiC (z - b * I)) / 2) := by
  refine ⟨fun hRH b hb => laguerrePolya_cosineShiftXi_of_rh hRH hb, fun h => ?_⟩
  refine riemannHypothesis_of_laguerrePolya_XiC
    (GaloisForLFunctions.HTGeometry.LaguerrePolya.of_tendstoLocallyUniformly (fun m => ?_)
      tendstoLocallyUniformly_cosineShift_XiC)
  exact h _ (by positivity)

end

end RHTower.DeBruijn
