import GaloisForLFunctions.SquareRootThreshold.AttainedDepthIsVisible

/-!
# A bounded exponential sum has no top pole

Let `F(v) = Σ_t q_t e^{λ_t v}` with `Σ_t |q_t| < ∞` and `0 < Re λ_t ≤ A`. If `F` is bounded on
`[0, ∞)`, then `q_{t₁} = 0` for every exponent `λ_{t₁}` that is rightmost on its horizontal line
and separated from the other horizontal lines (`eq_zero_of_norm_tsum_exp_le`). No exponent needs
to be rightmost overall: the supremum of `Re λ_t` may be approached and not attained.

* **Laplace transform as a Mellin transform.** Under `x = e^{−v}` the Laplace transform of `F` is
  the Mellin transform of the profile `x ↦ Σ_t q_t x^{−λ_t}` on `(0, 1]`. The profile is bounded,
  so the transform `L` is holomorphic on `Re s > 0` (`differentiableAt_mellin_expSumProfile`).
  For `Re s > A` it is `G(s) = Σ_t q_t/(s − λ_t)` (`mellin_expSumProfile_eq`).
* **Continuation along a strip.** `G` is holomorphic on the strip
  `R = {Re s > Re λ_{t₁}, |Im s − Im λ_{t₁}| < η/2}`, which contains no exponent
  (`differentiableOn_resolventSum`). `R` is convex, so the identity theorem carries `L = G` from
  `Re s > A` to all of `R`.
* **Residue.** Along `s = σ + i Im λ_{t₁}`, `σ ↓ Re λ_{t₁}`, `(s − λ_{t₁}) G(s) → q_{t₁}` by
  dominated convergence, while `(s − λ_{t₁}) L(s) → 0` because `L` is continuous at `λ_{t₁}`.
-/

open MeasureTheory Complex Set Filter Topology Asymptotics
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

section BoundedExponentialSums

variable {ι : Type*} (lam q : ι → ℂ)

/-- The Mellin profile `x ↦ Σ_t q_t x^{−λ_t}` of `Σ_t q_t e^{λ_t v}`, cut off to `(0, 1]`. -/
def expSumProfile (x : ℝ) : ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun x : ℝ => ∑' t, q t * (x : ℂ) ^ (-lam t)) x

/-- The resolvent sum `G(s) = Σ_t q_t/(s − λ_t)`. -/
def resolventSum (s : ℂ) : ℂ := ∑' t, q t / (s - lam t)

theorem ofReal_cpow_neg_eq_exp {x : ℝ} (hx : 0 < x) (l : ℂ) :
    (x : ℂ) ^ (-l) = cexp (l * ((-Real.log x : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]
  push_cast
  ring_nf

variable {lam q}

/-- On `(0, 1]` the profile is the exponential sum at `v = −log x ≥ 0`. -/
theorem norm_expSumProfile_le {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ v : ℝ, 0 ≤ v → ‖∑' t, q t * cexp (lam t * v)‖ ≤ K) (x : ℝ) :
    ‖expSumProfile lam q x‖ ≤ K := by
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · rw [expSumProfile, Set.indicator_of_mem hx]
    have h := hK (-Real.log x) (by have := Real.log_nonpos hx.1.le hx.2; linarith)
    rwa [show (∑' t, q t * (x : ℂ) ^ (-lam t)) = ∑' t, q t * cexp (lam t * ((-Real.log x : ℝ) : ℂ))
      from tsum_congr fun t => by rw [ofReal_cpow_neg_eq_exp hx.1]]
  · rw [expSumProfile, Set.indicator_of_notMem hx, norm_zero]
    exact hK0

/-- The uncut profile is continuous on `(0, ∞)`. -/
theorem continuousOn_profileSum (hq : Summable fun t => ‖q t‖) {A : ℝ}
    (hlam : ∀ t, 0 < (lam t).re ∧ (lam t).re ≤ A) :
    ContinuousOn (fun x : ℝ => ∑' t, q t * (x : ℂ) ^ (-lam t)) (Ioi 0) := by
  intro x₀ hx₀
  have hx₀' : (0 : ℝ) < x₀ := hx₀
  set a := x₀ / 2 with ha
  have ha0 : 0 < a := by positivity
  have hon : ContinuousOn (fun x : ℝ => ∑' t, q t * (x : ℂ) ^ (-lam t)) (Ioi a) := by
    refine continuousOn_tsum (u := fun t => ‖q t‖ * max 1 (a ^ (-A))) (fun t => ?_)
      (hq.mul_right _) (fun t x hx => ?_)
    · intro x hx
      have hx0 : (0 : ℝ) < x := ha0.trans hx
      exact (continuousAt_const.mul
        (continuousAt_ofReal_cpow_const x (-lam t) (Or.inr hx0.ne'))).continuousWithinAt
    · have hx0 : (0 : ℝ) < x := ha0.trans hx
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.neg_re]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 : x ^ (-(lam t).re) ≤ a ^ (-(lam t).re) :=
        Real.rpow_le_rpow_of_nonpos ha0 (le_of_lt hx) (by linarith [(hlam t).1])
      refine h1.trans ?_
      rcases le_or_gt 1 a with h | h
      · exact (Real.rpow_le_one_of_one_le_of_nonpos h (by linarith [(hlam t).1])).trans
          (le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge ha0 h.le (by linarith [(hlam t).2])).trans
          (le_max_right _ _)
  exact (hon.continuousAt (Ioi_mem_nhds (by rw [ha]; linarith))).continuousWithinAt

/-- **The Laplace transform is holomorphic on `Re s > 0`.** -/
theorem differentiableAt_mellin_expSumProfile (hq : Summable fun t => ‖q t‖) {A : ℝ}
    (hlam : ∀ t, 0 < (lam t).re ∧ (lam t).re ≤ A) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ v : ℝ, 0 ≤ v → ‖∑' t, q t * cexp (lam t * v)‖ ≤ K) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (expSumProfile lam q)) s := by
  have hfb := norm_expSumProfile_le hK0 hK
  have hint : IntegrableOn (fun x : ℝ => ∑' t, q t * (x : ℂ) ^ (-lam t)) (Ioc 0 1) := by
    refine Integrable.of_bound (μ := volume.restrict (Ioc 0 1))
      (((continuousOn_profileSum hq hlam).mono Ioc_subset_Ioi_self).aestronglyMeasurable
        measurableSet_Ioc) K ((ae_restrict_iff' measurableSet_Ioc).mpr
          (Eventually.of_forall fun x hx => ?_))
    have := hfb x
    rwa [expSumProfile, Set.indicator_of_mem hx] at this
  have hfc : LocallyIntegrableOn (expSumProfile lam q) (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioc).mpr hint).locallyIntegrable.locallyIntegrableOn _
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0) hfc ?_ (by linarith) ?_ hs
  · refine IsBigO.of_bound 0 ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    rw [expSumProfile, Set.indicator_of_notMem (fun h => by linarith [h.2]), norm_zero, zero_mul]
  · refine IsBigO.of_bound K (Eventually.of_forall fun x => ?_)
    rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
    exact hfb x

/-- The integral `∫₀¹ x^r dx = 1/(r + 1)` for `Re r > −1`. -/
theorem integral_Ioc_cpow {r : ℂ} (hr : -1 < r.re) :
    ∫ x in Ioc (0 : ℝ) 1, (x : ℂ) ^ r = 1 / (r + 1) := by
  have hr1 : r + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl hr), Complex.ofReal_one,
    Complex.one_cpow, Complex.ofReal_zero, Complex.zero_cpow hr1, sub_zero]

/-- **The Laplace transform is the resolvent sum** for `Re s > A`. -/
theorem mellin_expSumProfile_eq [Countable ι] (hq : Summable fun t => ‖q t‖) {A : ℝ}
    (hlam : ∀ t, 0 < (lam t).re ∧ (lam t).re ≤ A) {s : ℂ} (hs : A < s.re) :
    mellin (expSumProfile lam q) s = resolventSum lam q s := by
  have hr : ∀ t, -1 < (s - lam t - 1).re := fun t => by
    simp only [Complex.sub_re, Complex.one_re]
    linarith [(hlam t).2]
  have hr1 : ∀ t, s - lam t - 1 + 1 = s - lam t := fun t => by ring
  -- restrict to `(0, 1]` and expand the profile
  have h1 : mellin (expSumProfile lam q) s =
      ∫ x in Ioc (0 : ℝ) 1, ∑' t, q t * (x : ℂ) ^ (s - lam t - 1) := by
    rw [mellin]
    have hind : (fun x : ℝ => (x : ℂ) ^ (s - 1) • expSumProfile lam q x) =
        (Ioc (0 : ℝ) 1).indicator fun x : ℝ => (x : ℂ) ^ (s - 1) • ∑' t, q t * (x : ℂ) ^ (-lam t) := by
      funext x
      by_cases hx : x ∈ Ioc (0 : ℝ) 1
      · rw [expSumProfile, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [expSumProfile, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, smul_zero]
    rw [hind, setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr Ioc_subset_Ioi_self]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
    simp only [smul_eq_mul]
    rw [← tsum_mul_left]
    refine tsum_congr fun t => ?_
    rw [mul_left_comm, ← Complex.cpow_add _ _ hx0]
    ring_nf
  -- exchange sum and integral
  have hint : ∀ t, Integrable (fun x : ℝ => q t * (x : ℂ) ^ (s - lam t - 1))
      (volume.restrict (Ioc 0 1)) := fun t =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      ((intervalIntegral.intervalIntegrable_cpow' (hr t)).const_mul (q t))
  have hnorm : ∀ t, ∫ x in Ioc (0 : ℝ) 1, ‖q t * (x : ℂ) ^ (s - lam t - 1)‖ =
      ‖q t‖ / (s.re - (lam t).re) := by
    intro t
    have hc : -1 < s.re - (lam t).re - 1 := by linarith [(hlam t).2]
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun x : ℝ => ‖q t‖ * x ^ (s.re - (lam t).re - 1))
      fun x hx => by
        simp only
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
        simp, integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl hc), Real.one_rpow,
      Real.zero_rpow (by linarith : s.re - (lam t).re - 1 + 1 ≠ 0)]
    field_simp
    ring_nf
  have hsum : Summable fun t => ∫ x in Ioc (0 : ℝ) 1, ‖q t * (x : ℂ) ^ (s - lam t - 1)‖ := by
    simp_rw [hnorm]
    refine Summable.of_nonneg_of_le (fun t => div_nonneg (norm_nonneg _)
      (by linarith [(hlam t).2])) (fun t => ?_) (hq.div_const (s.re - A))
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) (by linarith [(hlam t).2])
  rw [h1, ← integral_tsum_of_summable_integral_norm hint hsum, resolventSum]
  refine tsum_congr fun t => ?_
  rw [integral_const_mul, integral_Ioc_cpow (hr t), hr1, mul_one_div]

/-- **The resolvent sum is holomorphic on the strip** `{Re s > Re λ_{t₁}, |Im s − Im λ_{t₁}| < η/2}`
when `λ_{t₁}` is rightmost on its line and the other lines are `η` away. -/
theorem differentiableOn_resolventSum (hq : Summable fun t => ‖q t‖) (t₁ : ι)
    (htop : ∀ t, (lam t).im = (lam t₁).im → (lam t).re ≤ (lam t₁).re) {η : ℝ} (hη : 0 < η)
    (hsep : ∀ t, |(lam t).im - (lam t₁).im| < η → (lam t).im = (lam t₁).im) :
    DifferentiableOn ℂ (resolventSum lam q)
      {s | (lam t₁).re < s.re ∧ |s.im - (lam t₁).im| < η / 2} := by
  intro s₀ hs₀
  set ε := (s₀.re - (lam t₁).re) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith [hs₀.1]
  set U : Set ℂ := {s | (lam t₁).re + ε < s.re ∧ |s.im - (lam t₁).im| < η / 2} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt ((Complex.continuous_im.sub continuous_const).abs) continuous_const)
  have hs₀U : s₀ ∈ U := ⟨by rw [hε]; linarith [hs₀.1], hs₀.2⟩
  set m := min ε (η / 2) with hm
  have hm0 : 0 < m := lt_min hε0 (by linarith)
  have hgap : ∀ t, ∀ s ∈ U, m ≤ ‖s - lam t‖ := by
    intro t s hs
    by_cases hline : (lam t).im = (lam t₁).im
    · have h1 : s.re - (lam t).re ≤ ‖s - lam t‖ := by
        have := Complex.re_le_norm (s - lam t)
        simpa using this
      have := htop t hline
      have := hs.1
      exact (min_le_left _ _).trans (by linarith)
    · have hfar : η ≤ |(lam t).im - (lam t₁).im| := by
        by_contra h
        exact hline (hsep t (lt_of_not_ge h))
      have h1 : |(s - lam t).im| ≤ ‖s - lam t‖ := Complex.abs_im_le_norm _
      have h2 : |(lam t).im - (lam t₁).im| ≤ |(s - lam t).im| + |s.im - (lam t₁).im| := by
        rw [Complex.sub_im]
        calc |(lam t).im - (lam t₁).im| = |(-(s.im - (lam t).im)) + (s.im - (lam t₁).im)| := by
              ring_nf
          _ ≤ |(-(s.im - (lam t).im))| + |s.im - (lam t₁).im| := abs_add_le _ _
          _ = |s.im - (lam t).im| + |s.im - (lam t₁).im| := by rw [abs_neg]
      have := hs.2
      exact (min_le_right _ _).trans (by linarith)
  have hdiff : DifferentiableOn ℂ (resolventSum lam q) U := by
    refine differentiableOn_tsum_of_summable_norm (u := fun t => ‖q t‖ / m) (hq.div_const m)
      (fun t => ?_) hUo (fun t s hs => ?_)
    · refine (differentiableOn_const _).div (differentiableOn_id.sub_const _) fun s hs h0 => ?_
      have := hgap t s hs
      rw [h0, norm_zero] at this
      linarith
    · rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hm0 (hgap t s hs)
  exact (hdiff.differentiableAt (hUo.mem_nhds hs₀U)).differentiableWithinAt

/-- **A bounded exponential sum has no top pole.** If `Σ_t |q_t| < ∞`, `0 < Re λ_t ≤ A`, and
`F(v) = Σ_t q_t e^{λ_t v}` is bounded on `[0, ∞)`, then `q_{t₁} = 0` for every `t₁` whose exponent
is rightmost on its horizontal line, not shared, and `η`-separated from the other lines. -/
theorem eq_zero_of_norm_tsum_exp_le [Countable ι] (hq : Summable fun t => ‖q t‖) {A : ℝ}
    (hlam : ∀ t, 0 < (lam t).re ∧ (lam t).re ≤ A) (t₁ : ι)
    (htop : ∀ t, (lam t).im = (lam t₁).im → (lam t).re ≤ (lam t₁).re)
    (hinj : ∀ t, lam t = lam t₁ → t = t₁) {η : ℝ} (hη : 0 < η)
    (hsep : ∀ t, |(lam t).im - (lam t₁).im| < η → (lam t).im = (lam t₁).im) {K : ℝ}
    (hK : ∀ v : ℝ, 0 ≤ v → ‖∑' t, q t * cexp (lam t * v)‖ ≤ K) : q t₁ = 0 := by
  classical
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 le_rfl)
  set γ := (lam t₁).im with hγ
  set δ₁ := (lam t₁).re with hδ₁
  have hδ₁0 : 0 < δ₁ := (hlam t₁).1
  set L := mellin (expSumProfile lam q) with hL
  set R : Set ℂ := {s | δ₁ < s.re ∧ |s.im - γ| < η / 2} with hR
  have hRo : IsOpen R :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt ((Complex.continuous_im.sub continuous_const).abs) continuous_const)
  have hRc : Convex ℝ R := by
    have hre : IsLinearMap ℝ fun s : ℂ => s.re := ⟨fun x y => by simp, fun c x => by simp⟩
    have him : IsLinearMap ℝ fun s : ℂ => s.im := ⟨fun x y => by simp, fun c x => by simp⟩
    have hRe : R = {s : ℂ | δ₁ < s.re} ∩
        ({s : ℂ | γ - η / 2 < s.im} ∩ {s : ℂ | s.im < γ + η / 2}) := by
      ext s
      simp only [hR, Set.mem_setOf_eq, Set.mem_inter_iff, abs_lt]
      constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨h1, ?_, ?_⟩ <;> linarith
    rw [hRe]
    exact (convex_halfSpace_gt hre δ₁).inter
      ((convex_halfSpace_gt him _).inter (convex_halfSpace_lt him _))
  -- `L = G` on the strip
  have hLan : AnalyticOnNhd ℂ L R := DifferentiableOn.analyticOnNhd (fun s hs =>
    (differentiableAt_mellin_expSumProfile hq hlam hK0 hK (hδ₁0.trans hs.1)).differentiableWithinAt)
    hRo
  have hGan : AnalyticOnNhd ℂ (resolventSum lam q) R :=
    (differentiableOn_resolventSum hq t₁ htop hη hsep).analyticOnNhd hRo
  set z₀ : ℂ := ((max A δ₁ + 1 : ℝ) : ℂ) + γ * I with hz₀
  have hz₀re : z₀.re = max A δ₁ + 1 := by simp [hz₀]
  have hz₀im : z₀.im = γ := by simp [hz₀]
  have hz₀R : z₀ ∈ R := ⟨by rw [hz₀re]; linarith [le_max_right A δ₁], by
    rw [hz₀im, sub_self, abs_zero]; linarith⟩
  have hev : L =ᶠ[𝓝 z₀] resolventSum lam q := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show A < z₀.re by rw [hz₀re]; linarith [le_max_left A δ₁])] with s hs
    exact mellin_expSumProfile_eq hq hlam hs
  have hEq := hLan.eqOn_of_preconnected_of_eventuallyEq hGan hRc.isPreconnected hz₀R hev
  -- approach `λ_{t₁}` horizontally from the right
  set p : ℝ → ℂ := fun σ => (σ : ℂ) + γ * I with hp
  have hpl : p δ₁ = lam t₁ := by
    apply Complex.ext <;> simp [hp, hδ₁, hγ]
  have hpR : ∀ σ, δ₁ < σ → p σ ∈ R := fun σ hσ => ⟨by simp [hp]; exact hσ, by simp [hp]; linarith⟩
  have hpc : Continuous p := by rw [hp]; fun_prop
  have hlimL : Tendsto (fun σ : ℝ => ((σ : ℂ) - δ₁) * L (p σ)) (𝓝[>] δ₁) (𝓝 0) := by
    have hcont : ContinuousAt L (lam t₁) :=
      (differentiableAt_mellin_expSumProfile hq hlam hK0 hK hδ₁0).continuousAt
    have h1 : Tendsto (fun σ : ℝ => L (p σ)) (𝓝 δ₁) (𝓝 (L (lam t₁))) := by
      rw [← hpl]
      exact (hcont.comp_of_eq (hpc.continuousAt) hpl).tendsto.congr fun σ => rfl
    have h2 : Tendsto (fun σ : ℝ => ((σ : ℂ) - δ₁)) (𝓝 δ₁) (𝓝 0) := by
      have : Tendsto (fun σ : ℝ => ((σ : ℂ) - δ₁)) (𝓝 δ₁) (𝓝 (((δ₁ : ℝ) : ℂ) - δ₁)) :=
        (Complex.continuous_ofReal.tendsto δ₁).sub tendsto_const_nhds
      simpa using this
    simpa using (h2.mul h1).mono_left nhdsWithin_le_nhds
  have hlimG : Tendsto (fun σ : ℝ => ((σ : ℂ) - δ₁) * resolventSum lam q (p σ)) (𝓝[>] δ₁)
      (𝓝 (q t₁)) := by
    have hrw : ∀ σ : ℝ, ((σ : ℂ) - δ₁) * resolventSum lam q (p σ) =
        ∑' t, q t * (((σ : ℂ) - δ₁) / (p σ - lam t)) := fun σ => by
      rw [resolventSum, ← tsum_mul_left]
      exact tsum_congr fun t => by ring
    simp_rw [hrw]
    rw [← tsum_ite_eq t₁ q]
    refine tendsto_tsum_of_dominated_convergence hq (fun t => ?_) ?_
    · by_cases ht : t = t₁
      · subst ht
        rw [if_pos rfl]
        have : ∀ᶠ σ : ℝ in 𝓝[>] δ₁, q t * (((σ : ℂ) - δ₁) / (p σ - lam t)) = q t := by
          filter_upwards [self_mem_nhdsWithin] with σ hσ
          have hne : (σ : ℂ) - δ₁ ≠ 0 := by
            rw [sub_ne_zero]; exact_mod_cast (ne_of_gt (show δ₁ < σ from hσ))
          rw [show p σ - lam t = (σ : ℂ) - δ₁ by
            rw [← hpl]; simp [hp], div_self hne, mul_one]
        exact tendsto_const_nhds.congr' (this.mono fun σ h => h.symm)
      · rw [if_neg ht]
        have hne : lam t₁ - lam t ≠ 0 := sub_ne_zero.mpr fun h => ht (hinj t h.symm)
        have h1 : Tendsto (fun σ : ℝ => ((σ : ℂ) - δ₁) / (p σ - lam t)) (𝓝 δ₁)
            (𝓝 ((((δ₁ : ℝ) : ℂ) - δ₁) / (lam t₁ - lam t))) := by
          refine ((Complex.continuous_ofReal.tendsto δ₁).sub tendsto_const_nhds).div ?_ ?_
          · rw [← hpl]
            exact (hpc.tendsto δ₁).sub tendsto_const_nhds
          · exact hne
        simpa using ((h1.const_mul (q t)).mono_left nhdsWithin_le_nhds)
    · filter_upwards [Ioo_mem_nhdsGT (show δ₁ < δ₁ + η by linarith)] with σ hσ t
      rw [norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      rw [norm_div]
      have hnum : ‖(σ : ℂ) - δ₁‖ = σ - δ₁ := by
        rw [show (σ : ℂ) - δ₁ = ((σ - δ₁ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith [hσ.1])]
      have hden : σ - δ₁ ≤ ‖p σ - lam t‖ := by
        by_cases hline : (lam t).im = γ
        · have h1 : σ - (lam t).re ≤ ‖p σ - lam t‖ := by
            have := Complex.re_le_norm (p σ - lam t)
            simpa [hp] using this
          have := htop t hline
          linarith
        · have hfar : η ≤ |(lam t).im - γ| := by
            by_contra h
            exact hline (hsep t (lt_of_not_ge h))
          have h1 : |(p σ - lam t).im| ≤ ‖p σ - lam t‖ := Complex.abs_im_le_norm _
          have h2 : (p σ - lam t).im = γ - (lam t).im := by simp [hp]
          rw [h2, abs_sub_comm] at h1
          linarith [hσ.2]
      have hpos : 0 < σ - δ₁ := by linarith [hσ.1]
      rw [hnum, div_le_one₀ (hpos.trans_le hden)]
      exact hden
  have hcongr : (fun σ : ℝ => ((σ : ℂ) - δ₁) * L (p σ)) =ᶠ[𝓝[>] δ₁]
      fun σ : ℝ => ((σ : ℂ) - δ₁) * resolventSum lam q (p σ) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    rw [hEq (hpR σ hσ)]
  exact tendsto_nhds_unique (hlimL.congr' hcongr) hlimG |>.symm

end BoundedExponentialSums

end GaloisForLFunctions.SquareRootThreshold
