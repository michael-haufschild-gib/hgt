import GaloisForLFunctions.RHTower.CosDilationKernelPositivityRigidity

/-!
# Divisor-moment dominance and periodization sign-separation rigidity for cosine–dilation cores

Let `f : ℝ → ℝ` be smooth and supported in `[α, β]` (`0 < α ≤ β`) with `𝓜f(1) = ∫_0^∞ f = 0`, and
let `R_f = cosDilationCertMultiplier f` and `Ψ_f = cosDilationKernel f = Cf ⋆ f`.

* **Unconditional critical-line second-moment uniqueness**
  (`eq_zero_of_integral_norm_zeta_mul_mellin_sq_eq_zero`): without any blindness hypothesis, if
  `∫ ‖ζ(½+it) 𝓜f(½+it)‖² dt = 0`, then `f = 0`.
* **General divisor-moment transfer and Parseval identity**
  (`summable_divisorCard_mul_cosDilationKernel`,
  `integral_norm_zeta_mul_mellin_sq_mul_cpow_eq_tsum`,
  `integral_norm_zeta_mul_mellin_sq_eq_tsum_divisorCard`): for every smooth core `f` with
  `𝓜f(1) = 0` (not assumed blind) and every `n ≥ 1`, the divisor-weighted kernel series
  `Σ_{m≥1} d(m) Ψ_f(mn)` is summable and
  `∫ ‖ζ(½+it) 𝓜f(½+it)‖² n^{−(½+it)} dt = 2π Σ_{m≥1} d(m) Ψ_f(mn)`.
  At `n = 1`, `∫ ‖ζ(½+it) 𝓜f(½+it)‖² dt = 2π Σ_{m≥1} d(m) Ψ_f(m) ≥ 0`.
* **Divisor-series positivity, rigidity, and √n-dominance**
  (`tsum_divisorCard_mul_cosDilationKernel_nonneg`,
  `eq_zero_of_tsum_divisorCard_mul_cosDilationKernel_nonpos`,
  `sqrt_mul_abs_tsum_divisorCard_mul_cosDilationKernel_le`): for every smooth core `f` with
  `𝓜f(1) = 0`, `Σ_{m≥1} d(m) Ψ_f(m) ≤ 0` forces `f = 0`, and for every `n ≥ 1`,
  `√n |Σ_{m≥1} d(m) Ψ_f(mn)| ≤ Σ_{m≥1} d(m) Ψ_f(m)`.
* **Periodization sign-separation and point-obstruction laws for blind cores**
  (`tsum_dilationAutocorr_abs_eq_two_mul_cos`, `tsum_dilationAutocorr_abs_add_half`,
  `eq_zero_of_cosDilationKernel_blind_of_tsum_dilationAutocorr_nonneg_of_cos_neg`,
  `eq_zero_of_cosDilationKernel_blind_of_tsum_dilationAutocorr_nonpos_of_cos_pos`,
  `eq_zero_of_cosDilationKernel_blind_of_dilationAutocorr_half_int_nonneg`): for a blind core `f`
  with `𝓜f(1) = 0`, the periodization satisfies `Σ_{k∈ℤ} A_f(|x+k|) = 2 Ψ_f(1) cos 2πx`. Since
  `Ψ_f(1) > 0` for every nonzero smooth blind core, if there exists even a single point `x` with
  `cos 2πx < 0` and `Σ_{k∈ℤ} A_f(|x+k|) ≥ 0` (or `cos 2πx > 0` and `Σ_{k∈ℤ} A_f(|x+k|) ≤ 0`), then
  `f = 0` regardless of the support ratio `β/α`. In particular, if `A_f(|½+k|) ≥ 0` for all
  `k ∈ ℤ`, then `f = 0`.
-/

open Complex MeasureTheory Set Real Filter Topology
open scoped FourierTransform ContDiff

namespace RHTower

open RHTower.ExactNullDivisorTransfer RHTower.PrimeBlindCarlson

noncomputable section

variable {f : ℝ → ℝ}

/-! ### Unconditional critical-line second-moment uniqueness -/

/-- If `f` is smooth and supported in `[α, β]` (`0 < α ≤ β`) with `𝓜f(1) = 0`, and
`∫ ‖ζ(½+it) 𝓜f(½+it)‖² dt = 0`, then `f = 0` (without any blindness assumption). -/
theorem eq_zero_of_integral_norm_zeta_mul_mellin_sq_eq_zero (hf : ContDiff ℝ ∞ f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0)
    (hint0 : ∫ t : ℝ, ‖riemannZeta (1 / 2 + t * I) *
      mellin (fun y : ℝ => (f y : ℂ)) (1 / 2 + t * I)‖ ^ 2 = 0)
    (y : ℝ) : f y = 0 := by
  set g : ℝ → ℝ := fun t => ‖riemannZeta (1 / 2 + t * I) *
    mellin (fun y : ℝ => (f y : ℂ)) (1 / 2 + t * I)‖ ^ 2 with hg_def
  have hgeq : ∀ t : ℝ, g t = ‖xi (1 / 2 + (t : ℂ) * I) ^ 2 *
      cosDilationCertMultiplier f (1 / 2 + (t : ℂ) * I)‖ := by
    intro t
    rw [xi_sq_mul_cosDilationCertMultiplier_criticalLine h0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hgcont : Continuous g := by
    rw [show g = fun t : ℝ => ‖xi (1 / 2 + (t : ℂ) * I) ^ 2 *
      cosDilationCertMultiplier f (1 / 2 + (t : ℂ) * I)‖ from funext hgeq]
    refine Continuous.norm ?_
    rw [continuous_iff_continuousAt]
    intro t
    have hsre : 0 < ((1 / 2 : ℂ) + t * I).re := by simp
    have hd : DifferentiableAt ℂ (fun s => xi s ^ 2 * cosDilationCertMultiplier f s)
        (1 / 2 + t * I) :=
      ((xi_differentiable _).pow 2).mul
        (differentiableAt_cosDilationCertMultiplier hf hα hαβ hsupp hsre)
    exact ContinuousAt.comp (g := fun s => xi s ^ 2 * cosDilationCertMultiplier f s)
      hd.continuousAt (by fun_prop : ContinuousAt (fun t : ℝ => (1 / 2 : ℂ) + t * I) t)
  obtain ⟨C, hC⟩ := exists_bound_xi_sq_mul_cosDilationCertMultiplier hf hα hαβ hsupp h0
  have hgint : Integrable g := by
    refine (integrable_inv_one_add_sq.const_mul C).mono' hgcont.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hgeq t]
    have h := hC (1 / 2 + t * I) (by simp) (by simp; norm_num)
    simpa [div_eq_mul_inv] using h
  have hgae : g =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hgint).mp hint0
  have hg0 : ∀ t : ℝ, g t = 0 :=
    fun t => congrFun ((Continuous.ae_eq_iff_eq volume hgcont continuous_const).mp hgae) t
  have htest := isTest_ofReal_of_support hf hα hαβ hsupp
  set G : ℂ → ℂ := fun s => xi s * mellin (fun y : ℝ => (f y : ℂ)) s with hG_def
  have hGd : Differentiable ℂ G := fun s =>
    (xi_differentiable s).mul (htest.differentiableAt_mellin s)
  have hGa : AnalyticOnNhd ℂ G univ :=
    hGd.differentiableOn.analyticOnNhd isOpen_univ
  have hGline : ∀ t : ℝ, G (1 / 2 + t * I) = 0 := by
    intro t
    have hgt := hg0 t
    simp only [hg_def, sq_eq_zero_iff, norm_eq_zero] at hgt
    have hsre : 0 < ((1 / 2 : ℂ) + t * I).re := by simp
    have hs1 : (1 / 2 : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this
    simp only [hG_def, xi_eq_archXi_mul_riemannZeta hsre hs1, mul_assoc, hgt, mul_zero]
  have hGuniv : EqOn G 0 univ := by
    refine hGa.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (mem_univ (1 / 2 : ℂ)) ?_
    have ht : Tendsto (fun k : ℕ => (1 / 2 : ℂ) + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I)
        atTop (𝓝[≠] (1 / 2 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
        have h2 := (h.mul_const I).const_add (1 / 2 : ℂ)
        simpa using h2
      · simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have h0' : ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I = 0 := by linear_combination h
        have hne : (1 / ((k : ℝ) + 1) : ℝ) ≠ 0 := by positivity
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hne) I_ne_zero h0'
    exact ht.frequently (Frequently.of_forall fun k => hGline _)
  set M : ℂ → ℂ := mellin (fun y : ℝ => (f y : ℂ)) with hM_def
  have hMd : Differentiable ℂ M := fun s => htest.differentiableAt_mellin s
  have hMa : AnalyticOnNhd ℂ M univ :=
    hMd.differentiableOn.analyticOnNhd isOpen_univ
  have hMray : ∀ x : ℝ, 1 < x → M x = 0 := by
    intro x hx
    have hGx : G x = 0 := hGuniv (mem_univ (x : ℂ))
    have hxre : 1 < (x : ℂ).re := by simpa using hx
    have hx0 : 0 < (x : ℂ).re := by linarith
    have hx1 : (x : ℂ) ≠ 1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have hzeta : riemannZeta (x : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hxre
    have harch : archXi (x : ℂ) ≠ 0 := by
      unfold archXi
      refine mul_ne_zero (div_ne_zero (mul_ne_zero ?_ (sub_ne_zero.mpr hx1)) two_ne_zero)
        (Complex.Gammaℝ_ne_zero_of_re_pos hx0)
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hxi : xi (x : ℂ) ≠ 0 := by
      rw [xi_eq_archXi_mul_riemannZeta hx0 hx1]
      exact mul_ne_zero harch hzeta
    exact (mul_eq_zero.mp hGx).resolve_left hxi
  have hMuniv : EqOn M 0 univ := by
    refine hMa.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (mem_univ (2 : ℂ)) ?_
    have ht : Tendsto (fun k : ℕ => ((2 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ))
        atTop (𝓝[≠] (2 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (2 : ℝ)
        rw [add_zero] at h
        exact (Complex.continuous_ofReal.tendsto 2).comp h
      · simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have h' := Complex.ofReal_injective h
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    exact ht.frequently (Frequently.of_forall fun k => hMray _ (by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith))
  exact eq_zero_of_mellin_criticalLine_eq_zero hf hα hαβ hsupp
    (fun t => hMuniv (mem_univ _)) y

/-! ### General divisor-moment transfer and dominance for arbitrary smooth cores -/

/-- For any smooth core `f` supported in `[α, β]` (`0 < α ≤ β`) with `𝓜f(1) = 0` and any `n ≥ 1`,
the divisor-weighted cosine–dilation series `Σ_m d(m) Ψ_f(mn)` is absolutely summable. -/
theorem summable_divisorCard_mul_cosDilationKernel (hf : ContDiff ℝ ∞ f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0) {n : ℕ} (hn : 1 ≤ n) :
    Summable fun m : ℕ =>
      (m.divisors.card : ℝ) * cosDilationKernel f ((m * n : ℕ) : ℝ) := by
  set R := cosDilationCertMultiplier f
  set K := ∫ t : ℝ, ‖archXi (3 + t * I) ^ 2 * R (3 + t * I)‖
  have hK0 : 0 ≤ K := integral_nonneg fun _ => norm_nonneg _
  refine Summable.of_norm_bounded
    (g := fun m : ℕ => K / (2 * π) * ((m : ℝ) ^ 2)⁻¹)
    ((Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).mul_left (K / (2 * π)))
    fun m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hmn : (0 : ℝ) < ((m * n : ℕ) : ℝ) := by
    have : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hcert : |cosDilationKernel f ((m * n : ℕ) : ℝ)| =
      ‖certKernel R ((m * n : ℕ) : ℝ)‖ := by
    rw [certKernel_cosDilationCertMultiplier hf hα hαβ hsupp h0 hmn,
      Complex.norm_real, Real.norm_eq_abs]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), hcert]
  have hbound := norm_certKernel_le R hmn
  have hd : (m.divisors.card : ℝ) ≤ m := by exact_mod_cast Nat.card_divisors_le_self m
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmn_pow : ((m * n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ (m : ℝ) ^ (-(3 : ℝ)) := by
    push_cast
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by norm_num)
  calc (m.divisors.card : ℝ) * ‖certKernel R ((m * n : ℕ) : ℝ)‖
      ≤ (m : ℝ) * (K / (2 * π) * ((m * n : ℕ) : ℝ) ^ (-(3 : ℝ))) :=
        mul_le_mul hd hbound (norm_nonneg _) (by positivity)
    _ ≤ (m : ℝ) * (K / (2 * π) * (m : ℝ) ^ (-(3 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmn_pow (by positivity)) (by positivity)
    _ = K / (2 * π) * ((m : ℝ) * (m : ℝ) ^ (-(3 : ℝ))) := by ring
    _ = K / (2 * π) * ((m : ℝ) ^ 2)⁻¹ := by
        congr 1
        rw [Real.rpow_neg (by positivity), show ((m : ℝ) ^ (3 : ℝ)) = (m : ℝ) ^ (3 : ℕ) by
          norm_cast]
        field_simp

/-- **General divisor-moment transfer for cosine–dilation cores.**
For any smooth core `f` supported in `[α, β]` (`0 < α ≤ β`) with `𝓜f(1) = 0` and any `n ≥ 1`,
`∫ ‖ζ(½+it) 𝓜f(½+it)‖² n^{−(½+it)} dt = 2π Σ_m d(m) Ψ_f(mn)`. -/
theorem integral_norm_zeta_mul_mellin_sq_mul_cpow_eq_tsum (hf : ContDiff ℝ ∞ f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0) {n : ℕ} (hn : 1 ≤ n) :
    ∫ t : ℝ, ((‖riemannZeta (1 / 2 + t * I) *
        mellin (fun y : ℝ => (f y : ℂ)) (1 / 2 + t * I)‖ ^ 2 : ℝ) : ℂ) *
      (n : ℂ) ^ (-(1 / 2 + t * I)) =
      ((2 * π * ∑' m : ℕ, (m.divisors.card : ℝ) *
        cosDilationKernel f ((m * n : ℕ) : ℝ) : ℝ) : ℂ) := by
  have hR : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 →
      DifferentiableAt ℂ (cosDilationCertMultiplier f) s :=
    fun s h1 _ => differentiableAt_cosDilationCertMultiplier hf hα hαβ hsupp (by linarith)
  obtain ⟨C, hC⟩ := exists_bound_xi_sq_mul_cosDilationCertMultiplier hf hα hαβ hsupp h0
  obtain ⟨Ca, hCa⟩ := exists_bound_archXi_sq_mul_cosDilationCertMultiplier hf hα hαβ hsupp h0
  have hC' : ∀ t : ℝ, ‖archXi (3 + t * I) ^ 2 * cosDilationCertMultiplier f (3 + t * I)‖ ≤
      Ca / (1 + t ^ 2) := fun t => by
    have h := hCa (3 + t * I) (by simp; norm_num) (by simp)
    simpa using h
  have hint := integral_xi_sq_mul_cpow_eq_tsum (cosDilationCertMultiplier f) hR hC hC' hn
  simp_rw [xi_sq_mul_cosDilationCertMultiplier_criticalLine h0] at hint
  rw [hint, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_tsum]
  congr 1
  refine tsum_congr fun m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [divisorCard]
  · have hmn : (0 : ℝ) < ((m * n : ℕ) : ℝ) := by
      have : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact_mod_cast this
    have hc := certKernel_cosDilationCertMultiplier hf hα hαβ hsupp h0 hmn
    unfold certKernel at hc
    rw [hc]
    simp [divisorCard]

/-- **Critical-line Parseval–divisor identity for arbitrary smooth cores.**
For any smooth core `f` supported in `[α, β]` (`0 < α ≤ β`) with `𝓜f(1) = 0`,
`∫ ‖ζ(½+it) 𝓜f(½+it)‖² dt = 2π Σ_m d(m) Ψ_f(m)`. -/
theorem integral_norm_zeta_mul_mellin_sq_eq_tsum_divisorCard (hf : ContDiff ℝ ∞ f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0) :
    ∫ t : ℝ, ‖riemannZeta (1 / 2 + t * I) *
        mellin (fun y : ℝ => (f y : ℂ)) (1 / 2 + t * I)‖ ^ 2 =
      2 * π * ∑' m : ℕ, (m.divisors.card : ℝ) * cosDilationKernel f (m : ℝ) := by
  have h := integral_norm_zeta_mul_mellin_sq_mul_cpow_eq_tsum hf hα hαβ hsupp h0 le_rfl
  simp only [Nat.cast_one, Complex.one_cpow, mul_one, integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

/-- **Unconditional divisor-series positivity.**
For every smooth core `f` supported in `[α, β]` (`0 < α ≤ β`) with `𝓜f(1) = 0`,
`0 ≤ Σ_m d(m) Ψ_f(m)`. -/
theorem tsum_divisorCard_mul_cosDilationKernel_nonneg (hf : ContDiff ℝ ∞ f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0) :
    0 ≤ ∑' m : ℕ, (m.divisors.card : ℝ) * cosDilationKernel f (m : ℝ) := by
  have h := integral_norm_zeta_mul_mellin_sq_eq_tsum_divisorCard hf hα hαβ hsupp h0
  have hnn : 0 ≤ ∫ t : ℝ, ‖riemannZeta (1 / 2 + t * I) *
      mellin (fun y : ℝ => (f y : ℂ)) (1 / 2 + t * I)‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  rw [h] at hnn
  exact nonneg_of_mul_nonneg_right hnn (by positivity)

/-- **Divisor-series rigidity.**
If `f` is smooth and supported in `[α, β]` (`0 < α ≤ β`) with `𝓜f(1) = 0`, and
`Σ_m d(m) Ψ_f(m) ≤ 0`, then `f = 0`. -/
theorem eq_zero_of_tsum_divisorCard_mul_cosDilationKernel_nonpos (hf : ContDiff ℝ ∞ f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0)
    (hle : (∑' m : ℕ, (m.divisors.card : ℝ) * cosDilationKernel f (m : ℝ)) ≤ 0)
    (y : ℝ) : f y = 0 := by
  have hsum0 : (∑' m : ℕ, (m.divisors.card : ℝ) * cosDilationKernel f (m : ℝ)) = 0 :=
    le_antisymm hle (tsum_divisorCard_mul_cosDilationKernel_nonneg hf hα hαβ hsupp h0)
  have hint0 : ∫ t : ℝ, ‖riemannZeta (1 / 2 + t * I) *
      mellin (fun y : ℝ => (f y : ℂ)) (1 / 2 + t * I)‖ ^ 2 = 0 := by
    rw [integral_norm_zeta_mul_mellin_sq_eq_tsum_divisorCard hf hα hαβ hsupp h0,
      hsum0, mul_zero]
  exact eq_zero_of_integral_norm_zeta_mul_mellin_sq_eq_zero hf hα hαβ hsupp h0 hint0 y

/-- **Universal √n-divisor-moment dominance.**
For any smooth core `f` supported in `[α, β]` (`0 < α ≤ β`) with `𝓜f(1) = 0` and any `n ≥ 1`,
`√n |Σ_m d(m) Ψ_f(mn)| ≤ Σ_m d(m) Ψ_f(m)`. -/
theorem sqrt_mul_abs_tsum_divisorCard_mul_cosDilationKernel_le (hf : ContDiff ℝ ∞ f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0) {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt n * |∑' m : ℕ, (m.divisors.card : ℝ) * cosDilationKernel f ((m * n : ℕ) : ℝ)| ≤
      ∑' m : ℕ, (m.divisors.card : ℝ) * cosDilationKernel f (m : ℝ) := by
  set g : ℝ → ℝ := fun t => ‖riemannZeta (1 / 2 + t * I) *
    mellin (fun y : ℝ => (f y : ℂ)) (1 / 2 + t * I)‖ ^ 2 with hg_def
  have hgeq : ∀ t : ℝ, g t = ‖xi (1 / 2 + (t : ℂ) * I) ^ 2 *
      cosDilationCertMultiplier f (1 / 2 + (t : ℂ) * I)‖ := by
    intro t
    rw [xi_sq_mul_cosDilationCertMultiplier_criticalLine h0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hgcont : Continuous g := by
    rw [show g = fun t : ℝ => ‖xi (1 / 2 + (t : ℂ) * I) ^ 2 *
      cosDilationCertMultiplier f (1 / 2 + (t : ℂ) * I)‖ from funext hgeq]
    refine Continuous.norm ?_
    rw [continuous_iff_continuousAt]
    intro t
    have hsre : 0 < ((1 / 2 : ℂ) + t * I).re := by simp
    have hd : DifferentiableAt ℂ (fun s => xi s ^ 2 * cosDilationCertMultiplier f s)
        (1 / 2 + t * I) :=
      ((xi_differentiable _).pow 2).mul
        (differentiableAt_cosDilationCertMultiplier hf hα hαβ hsupp hsre)
    exact ContinuousAt.comp (g := fun s => xi s ^ 2 * cosDilationCertMultiplier f s)
      hd.continuousAt (by fun_prop : ContinuousAt (fun t : ℝ => (1 / 2 : ℂ) + t * I) t)
  obtain ⟨C, hC⟩ := exists_bound_xi_sq_mul_cosDilationCertMultiplier hf hα hαβ hsupp h0
  have hgint : Integrable g := by
    refine (integrable_inv_one_add_sq.const_mul C).mono' hgcont.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hgeq t]
    have h := hC (1 / 2 + t * I) (by simp) (by simp; norm_num)
    simpa [div_eq_mul_inv] using h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnorm_cpow : ∀ t : ℝ, ‖(n : ℂ) ^ (-(1 / 2 + (t : ℂ) * I))‖ = (Real.sqrt n)⁻¹ := by
    intro t
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hn0]
    have hre : (-(1 / 2 + (t : ℂ) * I)).re = -(1 / 2 : ℝ) := by simp
    rw [hre, Real.rpow_neg hn0.le, Real.sqrt_eq_rpow]
  have hId := congrArg norm
    (integral_norm_zeta_mul_mellin_sq_mul_cpow_eq_tsum hf hα hαβ hsupp h0 hn)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < 2 * π)] at hId
  have hle : 2 * π * |∑' m : ℕ, (m.divisors.card : ℝ) *
      cosDilationKernel f ((m * n : ℕ) : ℝ)| ≤
      (Real.sqrt n)⁻¹ * ∫ t : ℝ, g t := by
    rw [← hId]
    calc ‖∫ t : ℝ, (g t : ℂ) * (n : ℂ) ^ (-(1 / 2 + (t : ℂ) * I))‖
        ≤ ∫ t : ℝ, ‖(g t : ℂ) * (n : ℂ) ^ (-(1 / 2 + (t : ℂ) * I))‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ t : ℝ, (Real.sqrt n)⁻¹ * g t := by
          refine integral_congr_ae (Eventually.of_forall fun t => ?_)
          dsimp only
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
            hnorm_cpow t, mul_comm]
      _ = (Real.sqrt n)⁻¹ * ∫ t : ℝ, g t := integral_const_mul _ _
  rw [integral_norm_zeta_mul_mellin_sq_eq_tsum_divisorCard hf hα hαβ hsupp h0] at hle
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hpi_pos : 0 < 2 * π := by positivity
  have hmul := mul_le_mul_of_nonneg_left hle hsqrt_pos.le
  have hsimp : Real.sqrt n * ((Real.sqrt n)⁻¹ *
      (2 * π * ∑' m : ℕ, (m.divisors.card : ℝ) * cosDilationKernel f (m : ℝ))) =
      2 * π * ∑' m : ℕ, (m.divisors.card : ℝ) * cosDilationKernel f (m : ℝ) := by
    rw [← mul_assoc, mul_inv_cancel₀ hsqrt_pos.ne', one_mul]
  rw [hsimp, show Real.sqrt n * (2 * π * |∑' m : ℕ, (m.divisors.card : ℝ) *
      cosDilationKernel f ((m * n : ℕ) : ℝ)|) =
      2 * π * (Real.sqrt n * |∑' m : ℕ, (m.divisors.card : ℝ) *
      cosDilationKernel f ((m * n : ℕ) : ℝ)|) by ring] at hmul
  exact le_of_mul_le_mul_left hmul hpi_pos

/-! ### Periodization sign-separation and point-obstruction laws for blind cores -/

/-- `𝓜f(1) = 0` is equivalent to `∫_0^∞ f(y) dy = 0`. -/
theorem integral_Ioi_eq_zero_of_mellin_one_eq_zero
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0) :
    ∫ y in Ioi (0 : ℝ), f y = 0 := by
  have hm : mellin (fun y : ℝ => (f y : ℂ)) 1 =
      ((∫ y in Ioi (0 : ℝ), f y : ℝ) : ℂ) := by
    unfold mellin
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp
  rw [hm, Complex.ofReal_eq_zero] at h0
  exact h0

/-- If `𝓜f(1) = 0`, the cosine–dilation kernel vanishes at the origin: `Ψ_f(0) = 0`. -/
theorem cosDilationKernel_zero_eq_zero_of_mellin_one_eq_zero
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0) :
    cosDilationKernel f 0 = 0 :=
  cosDilationKernel_zero_of_integral_eq_zero (integral_Ioi_eq_zero_of_mellin_one_eq_zero h0)

/-- **Pure-cosine Poisson periodization for blind cores with `𝓜f(1) = 0`.**
If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`) with `𝓜f(1) = 0` and
`Ψ_f(n) = 0` for all `n ≥ 2`, then for every `x ∈ ℝ`,
`Σ_{k ∈ ℤ} A_f(|x + k|) = 2 Ψ_f(1) cos(2πx)`. -/
theorem tsum_dilationAutocorr_abs_eq_two_mul_cos (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) (x : ℝ) :
    ∑' k : ℤ, dilationAutocorr f |x + k| =
      2 * cosDilationKernel f 1 * Real.cos (2 * π * x) := by
  have hblindℤ := cosDilationKernel_int_eq_zero hf hα hαβ hsupp hblind
  have h := tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp hblindℤ x
  rw [← Complex.ofReal_tsum, cosDilationKernel_zero_eq_zero_of_mellin_one_eq_zero h0,
    zero_add] at h
  exact Complex.ofReal_injective h

/-- **Half-period anti-symmetry of the periodized dilation autocorrelation.**
For any continuous blind core `f` supported in `[α, β]` with `𝓜f(1) = 0`,
`Σ_{k ∈ ℤ} A_f(|x + ½ + k|) = − Σ_{k ∈ ℤ} A_f(|x + k|)`. -/
theorem tsum_dilationAutocorr_abs_add_half (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) (x : ℝ) :
    (∑' k : ℤ, dilationAutocorr f |x + 1 / 2 + k|) =
      -∑' k : ℤ, dilationAutocorr f |x + k| := by
  rw [tsum_dilationAutocorr_abs_eq_two_mul_cos hf hα hαβ hsupp h0 hblind (x + 1 / 2),
    tsum_dilationAutocorr_abs_eq_two_mul_cos hf hα hαβ hsupp h0 hblind x]
  have hcos : Real.cos (2 * π * (x + 1 / 2)) = -Real.cos (2 * π * x) := by
    rw [show 2 * π * (x + 1 / 2) = 2 * π * x + π by ring, Real.cos_add_pi]
  rw [hcos]
  ring

/-- **Quarter-integer node law for the periodized dilation autocorrelation.**
For any continuous blind core `f` supported in `[α, β]` with `𝓜f(1) = 0`,
`Σ_{k ∈ ℤ} A_f(|¼ + k|) = 0`. -/
theorem tsum_dilationAutocorr_abs_quarter (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    (∑' k : ℤ, dilationAutocorr f |(1 / 4 : ℝ) + k|) = 0 := by
  rw [tsum_dilationAutocorr_abs_eq_two_mul_cos hf hα hαβ hsupp h0 hblind (1 / 4),
    show 2 * π * (1 / 4 : ℝ) = π / 2 by ring, Real.cos_pi_div_two, mul_zero]

/-- **Single-point negative-cosine obstruction law.**
Let `f` be a smooth core supported in `[α, β]` (`0 < α ≤ β`) with `𝓜f(1) = 0` that is blind at
`n ≥ 2`. If there exists a point `x ∈ ℝ` with `cos(2πx) < 0` and `0 ≤ Σ_{k ∈ ℤ} A_f(|x + k|)`,
then `f = 0` (for any support ratio `β/α`). -/
theorem eq_zero_of_cosDilationKernel_blind_of_tsum_dilationAutocorr_nonneg_of_cos_neg
    (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    {x : ℝ} (hcos : Real.cos (2 * π * x) < 0)
    (hP : 0 ≤ ∑' k : ℤ, dilationAutocorr f |x + k|) (y : ℝ) : f y = 0 := by
  rw [tsum_dilationAutocorr_abs_eq_two_mul_cos hf.continuous hα hαβ hsupp h0 hblind x] at hP
  have hΨ1 : cosDilationKernel f 1 ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have : 2 * cosDilationKernel f 1 * Real.cos (2 * π * x) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hcos
    linarith
  exact eq_zero_of_cosDilationKernel_blind_of_one_nonpos hf hα hαβ hsupp h0 hblind hΨ1 y

/-- **Single-point positive-cosine obstruction law.**
Let `f` be a smooth core supported in `[α, β]` (`0 < α ≤ β`) with `𝓜f(1) = 0` that is blind at
`n ≥ 2`. If there exists a point `x ∈ ℝ` with `0 < cos(2πx)` and `Σ_{k ∈ ℤ} A_f(|x + k|) ≤ 0`,
then `f = 0` (for any support ratio `β/α`). -/
theorem eq_zero_of_cosDilationKernel_blind_of_tsum_dilationAutocorr_nonpos_of_cos_pos
    (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    {x : ℝ} (hcos : 0 < Real.cos (2 * π * x))
    (hP : (∑' k : ℤ, dilationAutocorr f |x + k|) ≤ 0) (y : ℝ) : f y = 0 := by
  rw [tsum_dilationAutocorr_abs_eq_two_mul_cos hf.continuous hα hαβ hsupp h0 hblind x] at hP
  have hΨ1 : cosDilationKernel f 1 ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have : 0 < 2 * cosDilationKernel f 1 * Real.cos (2 * π * x) := by positivity
    linarith
  exact eq_zero_of_cosDilationKernel_blind_of_one_nonpos hf hα hαβ hsupp h0 hblind hΨ1 y

/-- **Half-integer nonnegativity rigidity.**
If `f` is a smooth core supported in `[α, β]` (`0 < α ≤ β`) with `𝓜f(1) = 0` that is blind at
`n ≥ 2`, and `0 ≤ A_f(|½ + k|)` for every `k ∈ ℤ` (in particular, if `A_f ≥ 0` on `(0, ∞)`),
then `f = 0` regardless of the support ratio `β/α`. -/
theorem eq_zero_of_cosDilationKernel_blind_of_dilationAutocorr_half_int_nonneg
    (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    (hnn : ∀ k : ℤ, 0 ≤ dilationAutocorr f |(1 / 2 : ℝ) + k|) (y : ℝ) : f y = 0 := by
  have hcos : Real.cos (2 * π * (1 / 2 : ℝ)) < 0 := by
    rw [show 2 * π * (1 / 2 : ℝ) = π by ring, Real.cos_pi]
    norm_num
  exact eq_zero_of_cosDilationKernel_blind_of_tsum_dilationAutocorr_nonneg_of_cos_neg
    hf hα hαβ hsupp h0 hblind hcos (tsum_nonneg hnn) y

end

end RHTower
