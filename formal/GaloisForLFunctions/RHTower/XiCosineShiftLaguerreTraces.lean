import GaloisForLFunctions.RHTower.XiCosineShiftStrictLaguerre
import GaloisForLFunctions.RHTower.XiLaguerreShadow
import GaloisForLFunctions.RHTower.XiCosineShiftDefectDisks
import GaloisForLFunctions.RHTower.XiCosineShiftUniformLosslessHeights

/-!
# The Laguerre trace law at every depth

Let `Q(s) = (Im ξ'(s))² + Re ξ(s) · Re ξ''(s)`. At `s = ½ + h + ix` this is the first Laguerre
expression of the producer `A_h = cos(hD)Ξ` at `x`, and RH is `Q > 0` on `½ < Re s < 1`
(`riemannHypothesis_iff_strict_laguerre_strip`).

**Theorem** (`laguerre_nonneg_of_trace`). For `h > 0` and real `x`, `Q(½ + h + ix) ≥ 0` as soon as
`x` lies outside every doubled trace `|x − γ| < 2√((β − ½)² − h²)` of a zero `ρ = β + iγ` deeper
than `h`.

**Proof.**
* If every zero `ζ` of `A_h` satisfies `(Im ζ)² ≤ (Re ζ − x)²`, the local pair law makes
  `y ↦ |A_h(x + iy)|` nondecreasing on `y ≥ 0` (`monotoneOn_norm_vertical`, applied to the kernel
  `Φ(u) cosh(hu)`), and vertical monotonicity forces the first Laguerre inequality at `x`
  (`laguerre_of_monotoneOn_norm_vertical`).
* A non-real zero `ζ` of `A_h` lies in the defect disk of a zero `w` of `Ξ`:
  `(Re w − Re ζ)² + (Im ζ)² + h² ≤ (Im w)²` (`cosineShift_nonreal_zero_mem_defectDisk`). With
  `c = √((Im w)² − h²)`, both `|Re ζ − Re w|` and `|Im ζ|` are at most `c`, while `|x − Re w| ≥ 2c`.
  So `|Re ζ − x| ≥ c ≥ |Im ζ|`.

At `h = 0` the doubled traces contain the shadows of `XiLaguerreShadow`; for `h > 0` they shrink
with the depth and vanish once `h` exceeds every offset.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

theorem cosProducer_eq_cosTransform_kernel (h : ℝ) :
    cosProducer h = DeBruijn.cosTransform (fun x => riemannKernelReal x * Real.cosh (h * x)) := by
  funext z
  rw [DeBruijn.cosTransform_riemannKernel_mul_cosh]; rfl

/-- **Laguerre at `x` from the local pair law of `A_h`.** -/
theorem laguerre_nonneg_of_local {h x : ℝ}
    (hloc : ∀ ζ : ℂ, cosProducer h ζ = 0 → ζ.im ^ 2 ≤ (ζ.re - x) ^ 2) :
    0 ≤ foldFx h x ^ 2 - foldF h x * foldFxx h x := by
  have hk := DeBruijn.riemannKernel_mul_cosh_superExp h
  obtain ⟨C, hC, hbound⟩ := hk.exists_envelope
  have hE := cosProducer_eq_cosTransform_kernel h
  have han : AnalyticOnNhd ℂ (cosProducer h) univ := by
    rw [hE]; exact hk.differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hmono := DeBruijn.monotoneOn_norm_vertical hC han (by rw [hE]; exact hk.cosTransform_zero_ne)
    (fun z => by rw [hE]; exact hk.cosTransform_neg z)
    (fun z => by rw [hE]; exact hk.cosTransform_conj z)
    (fun z => by rw [hE]; exact hbound z) hloc
  have hlag := DeBruijn.laguerre_of_monotoneOn_norm_vertical (differentiable_cosProducer h)
    (fun z => by rw [hE]; exact hk.cosTransform_conj z) hmono
  rw [deriv_cosProducer_real, deriv_deriv_cosProducer_real, cosProducer_eq_foldF] at hlag
  have e : ((foldFx h x : ℂ) ^ 2 - (foldF h x : ℂ) * (foldFxx h x : ℂ)).re =
      foldFx h x ^ 2 - foldF h x * foldFxx h x := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]
  rwa [e] at hlag

/-- **The Laguerre trace law.** If `x` avoids the doubled trace `|x − γ| < 2√((β−½)² − h²)` of every
zero deeper than `h`, then `Q(½ + h + ix) ≥ 0`. -/
theorem laguerre_nonneg_of_trace {h x : ℝ} (hh : 0 < h)
    (htrace : ∀ w : ℂ, XiC w = 0 → h ^ 2 < w.im ^ 2 → 4 * (w.im ^ 2 - h ^ 2) ≤ (x - w.re) ^ 2) :
    0 ≤ foldFx h x ^ 2 - foldF h x * foldFxx h x := by
  refine laguerre_nonneg_of_local fun ζ hζ => ?_
  by_cases hζim : ζ.im = 0
  · rw [hζim]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sq_nonneg _
  obtain ⟨w, hw, hdisk⟩ := DeBruijn.cosineShift_nonreal_zero_mem_defectDisk hh hζim hζ
  have hpos : 0 < ζ.im ^ 2 := by positivity
  have hwh : h ^ 2 < w.im ^ 2 := by nlinarith [sq_nonneg (w.re - ζ.re)]
  have ht := htrace w hw hwh
  set E : ℝ := w.im ^ 2 - h ^ 2 with hE
  have hE0 : 0 < E := by rw [hE]; linarith
  have hu : |ζ.re - w.re| ≤ Real.sqrt E := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (w.re - ζ.re)])
  have hv : 2 * Real.sqrt E ≤ |w.re - x| := by
    rw [← Real.sqrt_sq_eq_abs]
    have h4 : (2 * Real.sqrt E) ^ 2 = 4 * E := by rw [mul_pow, Real.sq_sqrt hE0.le]; norm_num
    rw [show 2 * Real.sqrt E = Real.sqrt ((2 * Real.sqrt E) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by rw [h4]; nlinarith [sq_nonneg (x - w.re)])
  have him : |ζ.im| ≤ Real.sqrt E := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (w.re - ζ.re)])
  have hgap : Real.sqrt E ≤ |ζ.re - x| := by
    have := abs_sub_abs_le_abs_sub (w.re - x) (w.re - ζ.re)
    rw [show w.re - x - (w.re - ζ.re) = ζ.re - x by ring] at this
    rw [abs_sub_comm (w.re) (ζ.re)] at this
    linarith
  rw [← sq_abs ζ.im, ← sq_abs (ζ.re - x)]
  exact pow_le_pow_left₀ (abs_nonneg _) (him.trans hgap) 2

/-- **Doubly shadow-free heights.** If `|x − γ| ≥ 2|β − ½|` for every zero of `ξ`, then
`Q(½ + h + ix) ≥ 0` at every depth `h > 0`. -/
theorem laguerre_nonneg_of_doubleShadowFree {h x : ℝ} (hh : 0 < h)
    (hfree : ∀ w : ℂ, XiC w = 0 → 4 * w.im ^ 2 ≤ (x - w.re) ^ 2) :
    0 ≤ foldFx h x ^ 2 - foldF h x * foldFxx h x :=
  laguerre_nonneg_of_trace hh fun w hw _ => by nlinarith [hfree w hw, sq_nonneg h]

/-! ## The measure of the Laguerre failure set -/

/-- **The Laguerre failure set is small.** The heights `t ∈ [20, V]` at which the first Laguerre
inequality of some producer `A_h`, `h > 0`, fails have measure at most `4·offLineMoment(V + 1)`. -/
theorem volume_laguerreFail_le (V : ℝ) :
    volume {t : ℝ | t ∈ Icc 20 V ∧ ∃ h : ℝ, 0 < h ∧
        foldFx h t ^ 2 - foldF h t * foldFxx h t < 0}
      ≤ ENNReal.ofReal (4 * offLineMoment (V + 1)) := by
  classical
  set F := boxFinsetLe (V + 1) with hF
  have hsub : {t : ℝ | t ∈ Icc 20 V ∧ ∃ h : ℝ, 0 < h ∧
      foldFx h t ^ 2 - foldF h t * foldFxx h t < 0} ⊆
      ⋃ w ∈ F, Icc (w.im - 2 * (w.re - 1 / 2)) (w.im + 2 * (w.re - 1 / 2)) := by
    rintro t ⟨ht, h, hh, hQ⟩
    obtain ⟨w, hw, hwh, hlt⟩ : ∃ w : ℂ, XiC w = 0 ∧ h ^ 2 < w.im ^ 2 ∧
        (t - w.re) ^ 2 < 4 * (w.im ^ 2 - h ^ 2) := by
      by_contra hno
      push Not at hno
      exact absurd (laguerre_nonneg_of_trace hh hno) (not_le.mpr hQ)
    have him2 : w.im ^ 2 ≤ 1 / 4 := by
      have h0 : DeBruijn.cosTransform riemannKernelReal w = 0 := by
        rw [DeBruijn.cosTransform_riemannKernel_eq_XiC]; exact hw
      exact DeBruijn.riemannKernel_zeros_im_sq_le w h0
    have habs : |w.im| ≤ 1 / 2 := by
      rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
    have hwpos : 0 < |w.im| := by
      have : 0 < w.im ^ 2 := lt_of_le_of_lt (sq_nonneg h) hwh
      exact abs_pos.mpr (fun h0 => by rw [h0] at this; simp at this)
    have hdist : |t - w.re| < 2 * |w.im| := by
      have : (t - w.re) ^ 2 < (2 * |w.im|) ^ 2 := by
        rw [mul_pow, sq_abs]; nlinarith [sq_nonneg h]
      exact abs_lt_of_sq_lt_sq this (by positivity)
    -- the zero of `ξ` with real part `½ + |Im w|`
    set ρ : ℂ := 1 / 2 + I * w with hρ
    have hρ0 : xi ρ = 0 := by
      have e : XiC w = xi ρ := by rw [hρ, XiC, mul_comm]
      rw [← e]; exact hw
    have hρre : ρ.re = 1 / 2 - w.im := by simp [hρ]; ring
    have hρim : ρ.im = w.re := by simp [hρ]
    obtain ⟨u, hu, hure, huim⟩ : ∃ u : ℂ, xi u = 0 ∧ u.re = 1 / 2 + |w.im| ∧ u.im = w.re := by
      rcases le_or_gt w.im 0 with hc | hc
      · refine ⟨ρ, hρ0, ?_, hρim⟩
        rw [hρre, abs_of_nonpos hc]; ring
      · refine ⟨1 - (starRingEnd ℂ) ρ, by rw [xi_one_sub, xi_conj, hρ0, map_zero], ?_, ?_⟩
        · rw [abs_of_pos hc]; simp [hρre]; ring
        · simp [hρim]
    have hdist' := abs_lt.mp hdist
    have humem : u ∈ F := by
      rw [hF, mem_boxFinsetLe]
      refine ⟨by rw [hure]; linarith, xi_zero_re_lt_one hu, ?_, ?_, hu⟩
      · rw [huim]; linarith [ht.1, hdist'.2, habs]
      · rw [huim]; linarith [ht.2, hdist'.1, habs]
    refine Set.mem_iUnion₂.mpr ⟨u, humem, ?_, ?_⟩
    · rw [huim, hure]; linarith [hdist'.2]
    · rw [huim, hure]; linarith [hdist'.1]
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ w ∈ F, volume (Icc (w.im - 2 * (w.re - 1 / 2)) (w.im + 2 * (w.re - 1 / 2))) ≤
      ENNReal.ofReal (4 * (((analyticOrderAt xi w).toNat : ℝ) * (w.re - 1 / 2))) := by
    intro w hw
    rw [hF, mem_boxFinsetLe] at hw
    obtain ⟨hw1, -, -, -, hw0⟩ := hw
    have hm := DeBruijn.one_le_toNat_analyticOrderAt_xi hw0
    have hm' : (1 : ℝ) ≤ ((analyticOrderAt xi w).toNat : ℝ) := by exact_mod_cast hm
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  have hnn : ∀ w ∈ F, 0 ≤ 4 * (((analyticOrderAt xi w).toNat : ℝ) * (w.re - 1 / 2)) := by
    intro w hw
    rw [hF, mem_boxFinsetLe] at hw
    have := hw.1
    have : (0 : ℝ) ≤ ((analyticOrderAt xi w).toNat : ℝ) := Nat.cast_nonneg _
    nlinarith
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum]
  rfl

/-- **The strict-strip criterion holds on most heights at every depth.** For all large `V`, the
heights in `[20, V]` at which the first Laguerre inequality of some producer fails have measure at
most `0.268 (V + 1)`: on at least `73%` of the heights, `Q(½ + h + it) ≥ 0` for every `h > 0`. -/
theorem eventually_volume_laguerreFail_le :
    ∀ᶠ V in atTop,
      volume {t : ℝ | t ∈ Icc 20 V ∧ ∃ h : ℝ, 0 < h ∧
          foldFx h t ^ 2 - foldF h t * foldFxx h t < 0}
        ≤ ENNReal.ofReal (268 / 1000 * (V + 1)) := by
  have hshift : Tendsto (fun V : ℝ => V + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id
  filter_upwards [hshift.eventually ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper]
    with V hV
  refine (volume_laguerreFail_le V).trans (ENNReal.ofReal_le_ofReal ?_)
  linarith

end

end RHTower
