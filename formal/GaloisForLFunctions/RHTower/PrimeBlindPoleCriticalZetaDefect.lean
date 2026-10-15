import GaloisForLFunctions.RHTower.InvertedCosineDistanceGammaPhase
import GaloisForLFunctions.RHTower.CosDilationKernelBlindnessLink
import GaloisForLFunctions.HTGeometry.VerticalStripResidueShift

/-!
# The Weil pole term of a prime-blind test is a critical-line zeta defect

Let `f` be smooth and supported in `[α, β]`, `0 < α ≤ β`, with dilation autocorrelation
`A_f(r) = ∫_0^∞ f(y) f(ry) dy` and `M(t) = 𝓜f(½+it)`.

* **Mellin transform of the autocorrelation** (`mellin_dilationAutocorr`):
  `𝓜A_f(s) = 𝓜f(s) 𝓜f(1−s)` for every `s`, by Fubini and the dilation rule.
* **First moment of `ζ`** (`tsum_dilationAutocorr_eq_pole_add_integral_zeta`): for every such `f`,
  `Σ_{m≥1} A_f(m) = (∫ f)(∫ f(y)/y dy) + (1/2π) ∫ |M(t)|² Re ζ(½+it) dt`.
  The integer samples of the autocorrelation are its mass (the residue of `ζ 𝓜A_f` at `s = 1`)
  plus the critical-line `ζ`-moment of the spectral density `|M|²`.
* **Prime-blind tests** (`pole_eq_integral_one_sub_re_zeta_of_blind`): if `A_f(n) = 0` for every
  `n ≥ 2`, then the Weil pole term is
  `2 (∫ f)(∫ f(y)/y dy) = (1/π) ∫ |M(t)|² (1 − Re ζ(½+it)) dt`.

* **Second-moment bound** (`pole_ge_of_blind_secondMoment`): for prime-blind `f`, with
  `m = ∫ |M|²` and `S = ∫ |M|² |ζ(½+it)|²`, the pole term is at least `(m − √m √S)/π`.  A
  prime-blind test whose pole term is below `−P` therefore has `S ≥ (m + πP)²/m`: violators of
  prime-blind positivity live on large values of `|ζ|` on the critical line.

With the archimedean term `(1/π) ∫ |M|² θ'`, the prime-blind energy of `f` is
`(1/π) ∫ |𝓜f(½+it)|² (θ'(t) + 1 − Re ζ(½+it)) dt`. Prime-blind positivity, which the corpus proves
equivalent to the Riemann hypothesis, says that prime-blind spectral densities never charge the
set where `Re ζ(½+it)` exceeds `θ'(t) + 1` more than they charge its complement.

**Proof of the first-moment identity.**  The function `ζ(s) 𝓜A_f(s)` is holomorphic on
`½ ≤ Re s ≤ 2` except for a simple pole at `s = 1` with residue `𝓜A_f(1) = 𝓜f(1)𝓜f(0)`.  It
decays like `|t|^{−2}` there (`ζ` grows at most linearly, `𝓜f` decays to all orders), so the line
integral at `Re s = 2` minus the line integral at `Re s = ½` is `2π 𝓜A_f(1)`
(`integral_line_sub_integral_line_eq`).  On `Re s = 2` the Dirichlet series of `ζ` integrates
termwise to `2π Σ_m 𝓜^{−1}[𝓜A_f](m) = 2π Σ_m A_f(m)` by Mellin inversion.  On `Re s = ½`,
`𝓜A_f(½+it) = |M(t)|²`.
-/

open MeasureTheory Set Real Complex Filter Topology
open scoped ContDiff ComplexConjugate

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ}

/-! ### The Mellin transform of the dilation autocorrelation -/

theorem dilationAutocorr_support {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    ∀ r, dilationAutocorr f r ≠ 0 → α / β ≤ r ∧ r ≤ β / α := fun r hr => by
  by_contra h
  exact hr (dilationAutocorr_eq_zero_of_not_mem hα hαβ hsupp fun h' => h h')

/-- **Mellin transform of the dilation autocorrelation**: `𝓜A_f(s) = 𝓜f(s) 𝓜f(1−s)`. -/
theorem mellin_dilationAutocorr (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (s : ℂ) :
    mellin (fun r => (dilationAutocorr f r : ℂ)) s =
      mellin (fun y => (f y : ℂ)) s * mellin (fun y => (f y : ℂ)) (1 - s) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  set G : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) ^ (s - 1) * ((f p.2 : ℂ) * (f (p.1 * p.2) : ℂ))
    with hG
  have hKsub : Icc (α / β) (β / α) ×ˢ Icc α β ⊆ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    rintro ⟨r, y⟩ ⟨hr, hy⟩
    exact ⟨lt_of_lt_of_le (div_pos hα hβ) hr.1, lt_of_lt_of_le hα hy.1⟩
  have hGint : IntegrableOn G (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    refine (ContinuousOn.integrableOn_compact
      ((isCompact_Icc (a := α / β) (b := β / α)).prod (isCompact_Icc (a := α) (b := β)))
      fun p hp => ?_).of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioi)
      fun p hp => ?_
    · have hp1 : 0 < p.1 := (hKsub hp).1
      refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
      · exact (Complex.continuousAt_ofReal_cpow_const p.1 _ (Or.inr hp1.ne')).comp
          continuous_fst.continuousAt
      · exact ((Complex.continuous_ofReal.comp (hf.comp continuous_snd)).mul
          (Complex.continuous_ofReal.comp
            (hf.comp (continuous_fst.mul continuous_snd)))).continuousAt
    · obtain ⟨_, hpout⟩ := hp
      simp only [hG]
      by_contra hne
      have h1 : f p.2 ≠ 0 := fun h => hne (by simp [h])
      have h2 : f (p.2 * p.1) ≠ 0 := fun h => hne (by rw [mul_comm p.1 p.2]; simp [h])
      obtain ⟨hy, hr⟩ := ratio_mem_Icc_of_support hα hαβ hsupp h1 h2
      exact hpout ⟨hr, hy⟩
  have hswap := integral_integral_swap (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := volume.restrict (Ioi (0 : ℝ))) (f := fun r y => G (r, y)) (by
      rw [Measure.prod_restrict]
      exact hGint)
  have hL : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) ^ (s - 1) • ((dilationAutocorr f r : ℝ) : ℂ) =
      ∫ y in Ioi (0 : ℝ), G (r, y) := by
    intro r _
    unfold dilationAutocorr
    rw [← integral_complex_ofReal, smul_eq_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [hG]
    push_cast
    ring
  have hR : ∀ y ∈ Ioi (0 : ℝ), ∫ r in Ioi (0 : ℝ), G (r, y) =
      mellin (fun y => (f y : ℂ)) s * ((y : ℂ) ^ ((1 - s) - 1) • (f y : ℂ)) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have hm := mellin_comp_mul_left (fun t => (f t : ℂ)) s hy0
    have e1 : (y : ℂ) ^ ((1 - s) - 1) • (f y : ℂ) = (f y : ℂ) * (y : ℂ) ^ (-s) := by
      rw [smul_eq_mul, show (1 - s) - 1 = -s by ring, mul_comm]
    rw [e1, mul_comm (mellin _ s), mul_assoc, ← smul_eq_mul ((y : ℂ) ^ (-s)), ← hm, mellin,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [hG, smul_eq_mul]
    rw [mul_comm r y]
    ring
  conv_lhs => rw [mellin]
  rw [setIntegral_congr_fun measurableSet_Ioi hL, hswap,
    setIntegral_congr_fun measurableSet_Ioi hR, integral_const_mul]
  rfl

/-! ### The Mellin product `K(s) = 𝓜f(s) 𝓜f(1−s)` -/

/-- `K(s) = 𝓜f(s) 𝓜f(1−s)`, the Mellin transform of the dilation autocorrelation. -/
def autocorrMellin (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  mellin (fun y => (f y : ℂ)) s * mellin (fun y => (f y : ℂ)) (1 - s)

theorem differentiableAt_autocorrMellin (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (s : ℂ) :
    DifferentiableAt ℂ (autocorrMellin f) s := by
  have htest := isTest_ofReal_of_support hf hα hαβ hsupp
  have h1s : DifferentiableAt ℂ (fun x : ℂ => 1 - x) s := by fun_prop
  exact (htest.differentiableAt_mellin s).mul ((htest.differentiableAt_mellin (1 - s)).comp s h1s)

/-- `‖K(2+it)‖ ≤ C/(1+t²)`. -/
theorem exists_norm_autocorrMellin_two_le (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    ∃ C : ℝ, ∀ t : ℝ, ‖autocorrMellin f (((2 : ℝ) : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2) := by
  have htest := isTest_ofReal_of_support hf hα hαβ hsupp
  obtain ⟨C₁, hC₁0, hC₁⟩ := htest.exists_norm_mellin_le_decay 1
  obtain ⟨C₀, hC₀⟩ := IsTest.exists_norm_pow_mul_norm_mellin_le 0 htest 2
  have hC₀0 : 0 ≤ C₀ := le_trans (by positivity) (hC₀ 1 (by simp))
  refine ⟨C₁ * C₀, fun t => ?_⟩
  have h1 : ‖mellin (fun y => (f y : ℂ)) (((2 : ℝ) : ℂ) + t * I)‖ ≤ C₁ / (1 + t ^ 2) := by
    have := hC₁ (((2 : ℝ) : ℂ) + t * I) (by norm_num)
    simpa using this
  have h0 : ‖mellin (fun y => (f y : ℂ)) (1 - (((2 : ℝ) : ℂ) + t * I))‖ ≤ C₀ := by
    have := hC₀ (1 - (((2 : ℝ) : ℂ) + t * I)) (by norm_num)
    simpa using this
  rw [autocorrMellin, norm_mul]
  calc ‖mellin (fun y => (f y : ℂ)) (((2 : ℝ) : ℂ) + t * I)‖ *
        ‖mellin (fun y => (f y : ℂ)) (1 - (((2 : ℝ) : ℂ) + t * I))‖
      ≤ C₁ / (1 + t ^ 2) * C₀ := mul_le_mul h1 h0 (norm_nonneg _) (by positivity)
    _ = C₁ * C₀ / (1 + t ^ 2) := by ring

/-- `‖ζ(s) K(s)‖ ≤ C (1+t²)^{−1}` on `½ ≤ Re s ≤ 2`, `|Im s| ≥ 1`. -/
theorem exists_bound_zeta_mul_autocorrMellin (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖riemannZeta s * autocorrMellin f s‖ ≤ C * (1 + s.im ^ 2)⁻¹ := by
  have htest := isTest_ofReal_of_support hf hα hαβ hsupp
  obtain ⟨C₃, hC₃⟩ := IsTest.exists_norm_pow_mul_norm_mellin_le 3 htest 1
  obtain ⟨C₀, hC₀⟩ := IsTest.exists_norm_pow_mul_norm_mellin_le 0 htest 2
  have hC₀0 : 0 ≤ C₀ := le_trans (by positivity) (hC₀ 1 (by simp))
  set Z : ℝ := 5 * Real.sqrt (2 + 3)
  refine ⟨2 * Z * C₃ * C₀, fun s h1 h2 ht => ?_⟩
  set t := s.im with ht_def
  have hs : (s.re : ℂ) + (t : ℂ) * I = s := Complex.re_add_im s
  have hz : ‖riemannZeta s‖ ≤ Z * |t| := by
    have := norm_riemannZeta_le_linear_of_re_ge_half (B := 2) h1
      (by rw [abs_le]; constructor <;> linarith) ht
    rwa [hs] at this
  set X := ‖mellin (fun y => (f y : ℂ)) s‖
  have hm3 : ‖s‖ ^ 3 * X ≤ C₃ := hC₃ s (by rw [abs_le]; constructor <;> linarith)
  have hre1 : |(1 - s).re - 1| ≤ 2 := by
    rw [Complex.sub_re, Complex.one_re, abs_le]
    constructor <;> linarith
  have hm0 : ‖mellin (fun y => (f y : ℂ)) (1 - s)‖ ≤ C₀ := by
    have := hC₀ (1 - s) hre1
    simpa [pow_zero, one_mul] using this
  have hst : |t| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hX0 : 0 ≤ X := norm_nonneg _
  have ht3 : |t| ^ 3 * X ≤ C₃ :=
    le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg t) hst 3) hX0) hm3
  have hZ0 : 0 ≤ Z := by positivity
  have hsq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have h1t : 1 + t ^ 2 ≤ 2 * |t| ^ 2 := by nlinarith [hsq]
  rw [autocorrMellin, ← mul_assoc, norm_mul, norm_mul, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  calc ‖riemannZeta s‖ * X * ‖mellin (fun y => (f y : ℂ)) (1 - s)‖ * (1 + t ^ 2)
      ≤ Z * |t| * X * C₀ * (2 * |t| ^ 2) := by
        gcongr
    _ = 2 * Z * C₀ * (|t| ^ 3 * X) := by ring
    _ ≤ 2 * Z * C₀ * C₃ := by gcongr
    _ = 2 * Z * C₃ * C₀ := by ring

theorem tendsto_sub_one_mul_zeta_mul_autocorrMellin (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    Tendsto (fun s => (s - 1) * (riemannZeta s * autocorrMellin f s)) (𝓝[≠] 1)
      (𝓝 (autocorrMellin f 1)) := by
  have hK : ContinuousAt (autocorrMellin f) 1 :=
    (differentiableAt_autocorrMellin hf hα hαβ hsupp 1).continuousAt
  have h := riemannZeta_residue_one.mul (hK.tendsto.mono_left nhdsWithin_le_nhds)
  rw [one_mul] at h
  refine h.congr fun s => ?_
  ring

/-- **Contour shift past the pole of `ζ`.** -/
theorem integral_zeta_mul_autocorrMellin_two_sub_half (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    (∫ t : ℝ, riemannZeta (((2 : ℝ) : ℂ) + t * I) * autocorrMellin f (((2 : ℝ) : ℂ) + t * I)) -
      ∫ t : ℝ, riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I) *
        autocorrMellin f (((1 / 2 : ℝ) : ℂ) + t * I) =
      2 * Real.pi * autocorrMellin f 1 := by
  obtain ⟨C, hC⟩ := exists_bound_zeta_mul_autocorrMellin hf hα hαβ hsupp
  exact GaloisForLFunctions.HTGeometry.integral_line_sub_integral_line_eq
    (F := fun s => riemannZeta s * autocorrMellin f s) (p := 1) (by norm_num) (by norm_num)
    (fun s _ _ hs1 => (differentiableAt_riemannZeta hs1).mul
      (differentiableAt_autocorrMellin hf hα hαβ hsupp s))
    (tendsto_sub_one_mul_zeta_mul_autocorrMellin hf hα hαβ hsupp) (T₀ := 1)
    (fun s h1 h2 ht => hC s h1 h2 ht)

/-! ### The right line: the Dirichlet series of `ζ` -/

/-- **The `ζ` expansion on `Re s = c > 1`.**
`∫ ζ(c+it) K(c+it) dt = 2π Σ_m 𝓜^{−1}_c[K](m)`. -/
theorem integral_zeta_mul_line_eq_tsum {K : ℂ → ℂ} {c : ℝ} (hc : 1 < c)
    (hKc : ∀ t : ℝ, ContinuousAt K ((c : ℂ) + t * I))
    {C : ℝ} (hKb : ∀ t : ℝ, ‖K ((c : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2)) :
    ∫ t : ℝ, riemannZeta ((c : ℂ) + t * I) * K ((c : ℂ) + t * I) =
      2 * Real.pi * ∑' m : ℕ, mellinInv c K (m : ℝ) := by
  set L : ℝ → ℂ := fun t => K ((c : ℂ) + t * I) with hL
  set F : ℕ → ℝ → ℂ := fun m t => (m : ℂ) ^ (-((c : ℂ) + t * I)) * L t with hF
  have hre : ∀ t : ℝ, 1 < ((c : ℂ) + t * I).re := fun t => by simpa using hc
  have hser : ∀ t : ℝ, riemannZeta ((c : ℂ) + t * I) * K ((c : ℂ) + t * I) = ∑' m, F m t := by
    intro t
    rw [zeta_eq_tsum_one_div_nat_cpow (hre t), ← tsum_mul_right]
    refine tsum_congr fun m => ?_
    simp only [hF, hL]
    rw [one_div, ← Complex.cpow_neg]
  have hLcont : Continuous L := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hKc t).comp (f := fun t : ℝ => (c : ℂ) + t * I) (by fun_prop)
  have hLint : Integrable L := by
    refine (integrable_inv_one_add_sq.const_mul C).mono' hLcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    simpa [hL, div_eq_mul_inv] using hKb t
  have hnorm_cpow : ∀ m : ℕ, ∀ t : ℝ,
      ‖(m : ℂ) ^ (-((c : ℂ) + t * I))‖ = (m : ℝ) ^ (-c) := by
    intro m t
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hne : -((c : ℂ) + t * I) ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      rw [Nat.cast_zero, Complex.zero_cpow hne, norm_zero, Nat.cast_zero,
        Real.zero_rpow (by linarith)]
    · have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      rw [show ((m : ℂ)) = (((m : ℝ)) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hpos]
      simp
  have hFint : ∀ m : ℕ, Integrable (F m) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hz : F 0 = fun _ => 0 := by
        funext t
        have hne : -((c : ℂ) + t * I) ≠ 0 := fun h => by
          have := congrArg Complex.re h; simp at this; linarith
        simp only [hF, Nat.cast_zero, Complex.zero_cpow hne, zero_mul]
      rw [hz]
      exact integrable_zero _ _ _
    have hcp : Continuous fun t : ℝ => (m : ℂ) ^ (-((c : ℂ) + t * I)) := by
      have hb0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      exact Continuous.const_cpow (by fun_prop) (Or.inl hb0)
    have hbound : ∀ t, ‖F m t‖ ≤ (m : ℝ) ^ (-c) * ‖L t‖ := by
      intro t
      simp only [hF, norm_mul, hnorm_cpow m t, le_refl]
    exact (hLint.norm.const_mul ((m : ℝ) ^ (-c))).mono'
      ((hcp.mul hLcont).aestronglyMeasurable) (Filter.Eventually.of_forall hbound)
  have hFnorm : ∀ m : ℕ, ∫ t, ‖F m t‖ = (m : ℝ) ^ (-c) * ∫ t, ‖L t‖ := by
    intro m
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hF, norm_mul, hnorm_cpow m t]
  have hFsum : Summable fun m => ∫ t, ‖F m t‖ := by
    simp_rw [hFnorm]
    exact (Real.summable_nat_rpow.mpr (by linarith)).mul_right _
  rw [show (∫ t : ℝ, riemannZeta ((c : ℂ) + t * I) * K ((c : ℂ) + t * I)) =
      ∫ t : ℝ, ∑' m, F m t from integral_congr_ae (Filter.Eventually.of_forall hser),
    ← integral_tsum_of_summable_integral_norm hFint hFsum, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [mellinInv, Complex.real_smul]
  have hI : (∫ y : ℝ, (((m : ℝ)) : ℂ) ^ (-((c : ℂ) + y * I)) • K ((c : ℂ) + y * I)) =
      ∫ t : ℝ, F m t := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hF, hL, smul_eq_mul, Complex.ofReal_natCast]
  rw [hI]
  push_cast
  field_simp

/-! ### The first-moment identity -/

theorem mellinInv_autocorrMellin_eq (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (m : ℕ) :
    mellinInv 2 (autocorrMellin f) (m : ℝ) = (dilationAutocorr f m : ℂ) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hK : autocorrMellin f = mellin (fun r => (dilationAutocorr f r : ℂ)) := by
    funext s
    rw [mellin_dilationAutocorr hf.continuous hα hαβ hsupp s]
    rfl
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hA0 : dilationAutocorr f 0 = 0 := by
      have hf0 : f 0 = 0 := eq_zero_of_not_mem_Icc hsupp fun h => by linarith [h.1]
      unfold dilationAutocorr
      simp [hf0]
    rw [Nat.cast_zero, hA0, Complex.ofReal_zero, mellinInv]
    have hz : (fun y : ℝ => (((0 : ℝ)) : ℂ) ^ (-(((2 : ℝ) : ℂ) + y * I)) •
        autocorrMellin f (((2 : ℝ) : ℂ) + y * I)) = fun _ => 0 := by
      funext y
      have hne : -(((2 : ℝ) : ℂ) + y * I) ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this
      rw [Complex.ofReal_zero, Complex.zero_cpow hne, zero_smul]
    rw [hz, integral_zero, smul_zero]
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hAc := continuous_dilationAutocorr hf.continuous hα hsupp
  have hconv : MellinConvergent (fun r => (dilationAutocorr f r : ℂ)) ((2 : ℝ) : ℂ) :=
    mellinConvergent_ofReal_of_support hAc (div_pos hα hβ)
      (dilationAutocorr_support hα hαβ hsupp) _
  obtain ⟨C, hC⟩ := exists_norm_autocorrMellin_two_le hf hα hαβ hsupp
  have hvert : Complex.VerticalIntegrable (mellin fun r => (dilationAutocorr f r : ℂ)) 2 := by
    rw [← hK]
    unfold Complex.VerticalIntegrable
    have hcont : Continuous fun t : ℝ => autocorrMellin f (((2 : ℝ) : ℂ) + t * I) :=
      continuous_iff_continuousAt.mpr fun t =>
        (differentiableAt_autocorrMellin hf hα hαβ hsupp _).continuousAt.comp (by fun_prop)
    refine (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    simpa [div_eq_mul_inv] using hC t
  rw [hK]
  exact mellinInv_mellin_eq 2 _ hm0 hconv hvert hAc.continuousAt.ofReal

/-- On the critical line `K(½+it) = |𝓜f(½+it)|²`. -/
theorem autocorrMellin_phaseLinePt (f : ℝ → ℝ) (t : ℝ) :
    autocorrMellin f (phaseLinePt t) =
      ((‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 : ℝ) : ℂ) := by
  rw [autocorrMellin, mellin_one_sub_phaseLinePt, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem mellin_one_ofReal (f : ℝ → ℝ) :
    mellin (fun y => (f y : ℂ)) 1 = ((∫ y in Ioi (0 : ℝ), f y : ℝ) : ℂ) := by
  rw [mellin, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  simp

theorem mellin_zero_ofReal (f : ℝ → ℝ) :
    mellin (fun y => (f y : ℂ)) 0 = ((∫ y in Ioi (0 : ℝ), f y / y : ℝ) : ℂ) := by
  rw [mellin, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [zero_sub, Complex.cpow_neg_one, smul_eq_mul]
  push_cast
  ring

/-- **The first moment of `ζ` against the critical-line spectral density** (complex form):
`∫ ζ(½+it) |𝓜f(½+it)|² dt = 2π Σ_m A_f(m) − 2π (∫ f)(∫ f(y)/y dy)`. -/
theorem integral_zeta_mul_norm_mellin_sq_eq (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    ∫ t : ℝ, riemannZeta (phaseLinePt t) *
        ((‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 : ℝ) : ℂ) =
      2 * Real.pi * ∑' m : ℕ, (dilationAutocorr f m : ℂ) -
        2 * Real.pi * (((∫ y in Ioi (0 : ℝ), f y) * ∫ y in Ioi (0 : ℝ), f y / y : ℝ) : ℂ) := by
  have hshift := integral_zeta_mul_autocorrMellin_two_sub_half hf hα hαβ hsupp
  obtain ⟨C, hC⟩ := exists_norm_autocorrMellin_two_le hf hα hαβ hsupp
  have hright := integral_zeta_mul_line_eq_tsum (K := autocorrMellin f) (c := 2) (by norm_num)
    (fun t => (differentiableAt_autocorrMellin hf hα hαβ hsupp _).continuousAt) hC
  simp_rw [mellinInv_autocorrMellin_eq hf hα hαβ hsupp] at hright
  have hhalf : (fun t : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I) *
      autocorrMellin f (((1 / 2 : ℝ) : ℂ) + t * I)) = fun t : ℝ => riemannZeta (phaseLinePt t) *
        ((‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    rw [← autocorrMellin_phaseLinePt]
    rfl
  rw [hhalf, hright] at hshift
  have h1 : autocorrMellin f 1 =
      (((∫ y in Ioi (0 : ℝ), f y) * ∫ y in Ioi (0 : ℝ), f y / y : ℝ) : ℂ) := by
    rw [autocorrMellin, sub_self, mellin_one_ofReal, mellin_zero_ofReal, Complex.ofReal_mul]
  rw [h1] at hshift
  linear_combination -hshift

/-- The critical-line integrand `ζ(½+it) |𝓜f(½+it)|²` is integrable. -/
theorem integrable_zeta_mul_norm_mellin_sq (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    Integrable fun t : ℝ => riemannZeta (phaseLinePt t) *
      ((‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨C, hC⟩ := exists_bound_zeta_mul_autocorrMellin hf hα hαβ hsupp
  have hne : ∀ t : ℝ, (((1 / 2 : ℝ) : ℂ) + t * I) ≠ 1 := fun t h => by
    have := congrArg Complex.re h
    norm_num at this
  have hl := GaloisForLFunctions.HTGeometry.integrable_line_of_bound
    (F := fun s => riemannZeta s * autocorrMellin f s) (x := 1 / 2) (T₀ := 1) (C := C)
    (fun (t : ℝ) => ((differentiableAt_riemannZeta (hne t)).mul
      (differentiableAt_autocorrMellin hf hα hαβ hsupp _)).continuousAt)
    (fun (t : ℝ) (ht : (1 : ℝ) ≤ |t|) => by
      have h := hC (((1 / 2 : ℝ) : ℂ) + t * I) (by norm_num) (by norm_num) (by simpa using ht)
      simpa using h)
  refine hl.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [← autocorrMellin_phaseLinePt]
  rfl

/-- **The integer samples of the dilation autocorrelation** (real form):
`Σ_{m≥1} A_f(m) = (∫ f)(∫ f(y)/y dy) + (1/2π) ∫ |𝓜f(½+it)|² Re ζ(½+it) dt`. -/
theorem tsum_dilationAutocorr_eq_pole_add_integral_zeta (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    ∑' m : ℕ, dilationAutocorr f m =
      (∫ y in Ioi (0 : ℝ), f y) * (∫ y in Ioi (0 : ℝ), f y / y) + 1 / (2 * Real.pi) *
        ∫ t : ℝ, ‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 *
          (riemannZeta (phaseLinePt t)).re := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have h := integral_zeta_mul_norm_mellin_sq_eq hf hα hαβ hsupp
  obtain ⟨C, hC⟩ := exists_bound_zeta_mul_autocorrMellin hf hα hαβ hsupp
  have hint := integrable_zeta_mul_norm_mellin_sq hf hα hαβ hsupp
  have hfin : Summable fun m : ℕ => dilationAutocorr f m := by
    refine summable_of_ne_finset_zero (s := Finset.range (⌈β / α⌉₊ + 1)) fun m hm => ?_
    apply dilationAutocorr_eq_zero_of_not_mem hα hαβ hsupp
    intro hmem
    apply hm
    rw [Finset.mem_range]
    have : (m : ℝ) ≤ ⌈β / α⌉₊ := hmem.2.trans (Nat.le_ceil _)
    exact Nat.lt_succ_of_le (by exact_mod_cast this)
  have h' : ∫ t : ℝ, riemannZeta (phaseLinePt t) *
        ((‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 : ℝ) : ℂ) =
      ((2 * Real.pi * ∑' m : ℕ, dilationAutocorr f m - 2 * Real.pi *
        ((∫ y in Ioi (0 : ℝ), f y) * ∫ y in Ioi (0 : ℝ), f y / y) : ℝ) : ℂ) := by
    rw [h, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_tsum]
    push_cast
    ring
  have hre := congrArg Complex.re h'
  have hcomm := integral_re hint
  simp only [RCLike.re_to_complex] at hcomm
  rw [← hcomm, Complex.ofReal_re] at hre
  have e : ∀ t : ℝ, (riemannZeta (phaseLinePt t) *
      ((‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 : ℝ) : ℂ)).re =
      ‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 * (riemannZeta (phaseLinePt t)).re :=
    fun t => by rw [Complex.re_mul_ofReal, mul_comm]
  simp_rw [e] at hre
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  field_simp
  linarith

/-- **The Weil pole term of a prime-blind test is a critical-line zeta defect**:
if `A_f(n) = 0` for every `n ≥ 2`, then
`2 (∫ f)(∫ f(y)/y dy) = (1/π) ∫ |𝓜f(½+it)|² (1 − Re ζ(½+it)) dt`. -/
theorem pole_eq_integral_one_sub_re_zeta_of_blind (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hA : ∀ n : ℕ, 2 ≤ n → dilationAutocorr f n = 0) :
    2 * (∫ y in Ioi (0 : ℝ), f y) * (∫ y in Ioi (0 : ℝ), f y / y) =
      1 / Real.pi * ∫ t : ℝ, ‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 *
        (1 - (riemannZeta (phaseLinePt t)).re) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have hT := tsum_dilationAutocorr_eq_pole_add_integral_zeta hf hα hαβ hsupp
  have hf0 : f 0 = 0 := eq_zero_of_not_mem_Icc hsupp fun h => by linarith [h.1]
  have hsingle : ∑' m : ℕ, dilationAutocorr f m = dilationAutocorr f 1 := by
    refine (tsum_eq_single 1 fun m hm => ?_).trans (by norm_num)
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m
      · unfold dilationAutocorr; simp [hf0]
      · exact absurd rfl hm
    · exact hA m h
  rw [hsingle, dilationAutocorr_one_eq_setIntegral_sq,
    integral_Ioi_sq_eq_integral_norm_mellin_sq hf hα hsupp] at hT
  have hM := integrable_norm_mellin_phaseLinePt_sq hf hα hαβ hsupp
  have hR : Integrable fun t : ℝ => ‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 *
      (riemannZeta (phaseLinePt t)).re :=
    (integrable_zeta_mul_norm_mellin_sq hf hα hαβ hsupp).re.congr
      (Filter.Eventually.of_forall fun t => by
        simp only [RCLike.re_to_complex]
        rw [Complex.re_mul_ofReal, mul_comm])
  have e : ∀ t : ℝ, ‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 *
      (1 - (riemannZeta (phaseLinePt t)).re) =
      ‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 -
        ‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 * (riemannZeta (phaseLinePt t)).re :=
    fun t => by ring
  simp_rw [e]
  rw [integral_sub hM hR]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  field_simp
  field_simp at hT
  linarith


/-! ### The second-moment bound for the pole of a prime-blind test -/

/-- A real `X` bounded by `½(εa + b/ε)` for every `ε > 0` is at most `√a √b`. -/
theorem le_sqrt_mul_sqrt_of_forall_amgm {X a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ ε : ℝ, 0 < ε → X ≤ (ε * a + b / ε) / 2) : X ≤ Real.sqrt a * Real.sqrt b := by
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · have hsa := Real.sqrt_pos.mpr ha'
      have hsb := Real.sqrt_pos.mpr hb'
      have h1 := h (Real.sqrt b / Real.sqrt a) (div_pos hsb hsa)
      have ea : a = Real.sqrt a ^ 2 := (Real.sq_sqrt ha).symm
      have eb : b = Real.sqrt b ^ 2 := (Real.sq_sqrt hb).symm
      have e : (Real.sqrt b / Real.sqrt a * a + b / (Real.sqrt b / Real.sqrt a)) / 2 =
          Real.sqrt a * Real.sqrt b := by
        rw [ea, eb]
        field_simp
        ring_nf
        rw [Real.sqrt_sq (Real.sqrt_nonneg _), Real.sqrt_sq (Real.sqrt_nonneg _)]
        ring
      linarith
    · subst hb'
      by_contra hX
      push Not at hX
      rw [Real.sqrt_zero, mul_zero] at hX
      have h1 := h (X / a) (div_pos hX ha')
      field_simp at h1
      nlinarith
  · subst ha'
    rcases hb.lt_or_eq with hb' | hb'
    · by_contra hX
      push Not at hX
      rw [Real.sqrt_zero, zero_mul] at hX
      have h1 := h (b / X) (div_pos hb' hX)
      field_simp at h1
      nlinarith
    · subst hb'
      have h1 := h 1 one_pos
      simp only [mul_zero, zero_div, add_zero] at h1
      simp [h1]

/-- The critical-line second moment `‖𝓜f(½+it)‖² ‖ζ(½+it)‖²` is integrable. -/
theorem integrable_norm_mellin_sq_mul_norm_zeta_sq (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    Integrable fun t : ℝ => ‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 *
      ‖riemannZeta (phaseLinePt t)‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := (isTest_ofReal_of_support hf hα hαβ hsupp).exists_norm_mellin_le_decay 1
  have hne : ∀ t : ℝ, phaseLinePt t ≠ 1 := fun t h => by
    have := congrArg Complex.re h
    simp [phaseLinePt] at this
  have hzc : Continuous fun t : ℝ => riemannZeta (phaseLinePt t) :=
    continuous_iff_continuousAt.mpr fun t =>
      (differentiableAt_riemannZeta (hne t)).continuousAt.comp (by unfold phaseLinePt; fun_prop)
  have hMc : Continuous fun t : ℝ => mellin (fun y => (f y : ℂ)) (phaseLinePt t) :=
    continuous_mellin_verticalLine_of_continuous (Complex.continuous_ofReal.comp hf.continuous)
      (mellinConvergent_ofReal_of_support hf.continuous hα hsupp ((1 / 2 : ℝ) : ℂ))
  obtain ⟨K₁, hK₁⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hzc.norm.continuousOn
  have hK₁0 : 0 ≤ K₁ := le_trans (norm_nonneg _) (hK₁ 0 (by norm_num))
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul ((K₁ ^ 2 + 100) * C ^ 2))
    ((hMc.norm.pow 2).mul (hzc.norm.pow 2)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have hM : ‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ≤ C / (1 + t ^ 2) := by
    have h := hC (phaseLinePt t) (by simp [phaseLinePt]; norm_num [abs_of_neg])
    simpa [phaseLinePt] using h
  have hz : ‖riemannZeta (phaseLinePt t)‖ ^ 2 ≤ (K₁ ^ 2 + 100) * (1 + t ^ 2) := by
    rcases le_or_gt |t| 1 with ht | ht
    · have h1 := hK₁ t (by rw [Set.mem_Icc, ← abs_le]; exact ht)
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h1
      have h2 : ‖riemannZeta (phaseLinePt t)‖ ^ 2 ≤ K₁ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg t]
    · have h1 := norm_riemannZeta_le_linear_of_re_ge_half (B := 1) (σ := 1 / 2) (t := t)
        (by norm_num) (by norm_num) ht.le
      have e : (((1 / 2 : ℝ)) : ℂ) + (t : ℂ) * I = phaseLinePt t := rfl
      rw [e, show Real.sqrt (1 + 3) = 2 by
        rw [show (1 : ℝ) + 3 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h1
      have h2 : ‖riemannZeta (phaseLinePt t)‖ ^ 2 ≤ (5 * 2 * |t|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h3 : (5 * 2 * |t|) ^ 2 = 100 * t ^ 2 := by rw [mul_pow, sq_abs]; ring
      nlinarith [sq_nonneg K₁, sq_nonneg t]
  have hM2 : ‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 ≤ C ^ 2 / (1 + t ^ 2) ^ 2 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hM 2
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 * ‖riemannZeta (phaseLinePt t)‖ ^ 2
      ≤ C ^ 2 / (1 + t ^ 2) ^ 2 * ((K₁ ^ 2 + 100) * (1 + t ^ 2)) :=
        mul_le_mul hM2 hz (by positivity) (by positivity)
    _ = (K₁ ^ 2 + 100) * C ^ 2 * (1 + t ^ 2)⁻¹ := by
        field_simp

/-- **The pole of a prime-blind test is bounded below by the critical-line second moment**:
with `m = ∫ |𝓜f(½+it)|²` and `S = ∫ |𝓜f(½+it)|² |ζ(½+it)|²`,
`2 (∫ f)(∫ f(y)/y dy) ≥ (m − √m √S)/π`.  So a prime-blind test whose pole term is below `−P`
has `S ≥ (m + πP)²/m`: violators of prime-blind positivity live on large values of `|ζ|` on the
critical line. -/
theorem pole_ge_of_blind_secondMoment (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hA : ∀ n : ℕ, 2 ≤ n → dilationAutocorr f n = 0) :
    1 / Real.pi * ((∫ t : ℝ, ‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2) -
      Real.sqrt (∫ t : ℝ, ‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2) *
        Real.sqrt (∫ t : ℝ, ‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 *
          ‖riemannZeta (phaseLinePt t)‖ ^ 2)) ≤
      2 * (∫ y in Ioi (0 : ℝ), f y) * (∫ y in Ioi (0 : ℝ), f y / y) := by
  set M : ℝ → ℝ := fun t => ‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 with hMdef
  set Z : ℝ → ℂ := fun t => riemannZeta (phaseLinePt t) with hZdef
  have hMi := integrable_norm_mellin_phaseLinePt_sq hf hα hαβ hsupp
  have hSi := integrable_norm_mellin_sq_mul_norm_zeta_sq hf hα hαβ hsupp
  have hRi : Integrable fun t : ℝ => M t * (Z t).re :=
    (integrable_zeta_mul_norm_mellin_sq hf hα hαβ hsupp).re.congr
      (Filter.Eventually.of_forall fun t => by
        simp only [RCLike.re_to_complex, hMdef, hZdef]
        rw [Complex.re_mul_ofReal, mul_comm])
  have hM0 : ∀ t, 0 ≤ M t := fun t => by positivity
  have hcs : (∫ t, M t * (Z t).re) ≤ Real.sqrt (∫ t, M t) *
      Real.sqrt (∫ t, M t * ‖Z t‖ ^ 2) := by
    refine le_sqrt_mul_sqrt_of_forall_amgm (integral_nonneg hM0)
      (integral_nonneg fun t => by positivity) fun ε hε => ?_
    have hpt : ∀ t, M t * (Z t).re ≤ (ε * M t + M t * ‖Z t‖ ^ 2 / ε) / 2 := by
      intro t
      have h1 : (Z t).re ≤ ‖Z t‖ := Complex.re_le_norm _
      have h2 : ‖Z t‖ ≤ (ε + ‖Z t‖ ^ 2 / ε) / 2 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
        have : 0 ≤ (ε - ‖Z t‖) ^ 2 / ε := by positivity
        have e : (ε - ‖Z t‖) ^ 2 / ε = ε - 2 * ‖Z t‖ + ‖Z t‖ ^ 2 / ε := by
          field_simp
          ring
        linarith
      calc M t * (Z t).re ≤ M t * ‖Z t‖ := mul_le_mul_of_nonneg_left h1 (hM0 t)
        _ ≤ M t * ((ε + ‖Z t‖ ^ 2 / ε) / 2) := mul_le_mul_of_nonneg_left h2 (hM0 t)
        _ = (ε * M t + M t * ‖Z t‖ ^ 2 / ε) / 2 := by ring
    calc (∫ t, M t * (Z t).re) ≤ ∫ t, (ε * M t + M t * ‖Z t‖ ^ 2 / ε) / 2 :=
          integral_mono hRi ((((hMi.const_mul ε).add (hSi.div_const ε)).div_const 2)) hpt
      _ = (ε * (∫ t, M t) + (∫ t, M t * ‖Z t‖ ^ 2) / ε) / 2 := by
          rw [integral_div, integral_add (hMi.const_mul ε) (hSi.div_const ε),
            integral_const_mul, integral_div]
  rw [pole_eq_integral_one_sub_re_zeta_of_blind hf hα hαβ hsupp hA]
  have e : ∀ t : ℝ, ‖mellin (fun y => (f y : ℂ)) (phaseLinePt t)‖ ^ 2 *
      (1 - (riemannZeta (phaseLinePt t)).re) = M t - M t * (Z t).re := fun t => by
    simp only [hMdef, hZdef]; ring
  simp_rw [e]
  rw [integral_sub hMi hRi]
  have hpi : (0 : ℝ) < 1 / Real.pi := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hpi.le

end

end RHTower
