import GaloisForLFunctions.SquareRootThreshold.EvenAndOddTwoBumpTestsDecideTheCriticalLine
import GaloisForLFunctions.SquareRootThreshold.PoleFreeDyadicWindowsDecideTheCriticalLine
import GaloisForLFunctions.RHTower.FiniteOffLineLandau
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionUnrestricted

/-!
# Difference two-bump tests decide the critical line

The even and odd two-bump tests decide the line (`onLine_iff_evenOdd_twoBump_nonneg`). For
configurations without real zeros the difference tests `κ_γ(t + v/2) − κ_γ(t − v/2)` alone
suffice: one sign and two real parameters.

* **One-sided bound.** The difference test has `Re W = 2 Re S(0) − 2 Re S(v)`. Its positivity
  bounds the exponential sum `φ(v) = 2 Re S(v) = Σ_z D(z) e^{zv}` from above only.
* **Landau.** The Laplace transform of `φ` is `Σ_z D(z)/(s − z)` for `Re s > ½`
  (`integral_tsum_exp_mul_exp_neg`). Without real zeros every exponent keeps a fixed distance
  from the real axis, so this transform is analytic at every real point. Landau's theorem for
  one-sided bounded functions (`RHTower.exists_differentiable_extension_of_le_exp`) then
  continues it holomorphically to `Re s > 0`.
* **Residue.** A function holomorphic on `Re s > c` that agrees with `Σ_t q_t/(s − λ_t)` far to
  the right has no residue at a top exponent with `Re λ_{t₁} > c`
  (`eq_zero_of_resolventSum_eq_differentiable`). With the non-cancellation of the merged
  coefficients (`exists_center_evenCoeff_ne_zero`) this excludes every off-line zero.

**One sign decides the line** (`onLine_iff_difference_twoBump_nonneg`). A tempered configuration
without real zeros has all its zeros on the critical line iff `Re W ≥ 0` on every test
`κ_{w,γ}(t + v/2) − κ_{w,γ}(t − v/2)`, `γ ∈ ℝ`, `v ≥ V`, for any `V`. On `[0, V]` the a priori
bound `|2 Re S(v)| ≤ K e^{v/2}` keeps the one-sided bound. For `ζ`, whose nontrivial zeros
satisfy `|Im ρ| ≥ 4`, this holds on the prime side
(`onLine_iff_primeSide_difference_twoBump_nonneg`). It also holds through the dyadic prime windows
beyond any `X₀` (`onLine_iff_difference_primeWindow_nonneg`).

**Hodge class.** For the polar-free bump the merged coefficient is `(¼ − z²)²` times that of the
modulated bump (`evenCoeff_scaledBumpPolarFree`), and the pole terms vanish. RH holds iff, for
every height and every lag `v ≥ V`, the dyadic window prime sum of the polar-free difference
kernel is at most its archimedean term (`onLine_iff_polarFree_difference_primeWindow_le_arch`).
-/

open MeasureTheory Complex Set Filter Topology Asymptotics
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Residues and Laplace transforms of exponential sums -/

/-- **A holomorphic extension kills the top residue.** Let `Σ_t |q_t| < ∞`, `Re λ_t ≤ A`, and let
`λ_{t₁}` be rightmost on its horizontal line, unshared and separated from the other lines. If `F`
is holomorphic on `Re s > c`, `c < Re λ_{t₁}`, and agrees with `Σ_t q_t/(s − λ_t)` on
`Re s > A`, then `q_{t₁} = 0`. -/
theorem eq_zero_of_resolventSum_eq_differentiable {ι : Type*} [Countable ι] {lam q : ι → ℂ}
    (hq : Summable fun t => ‖q t‖) {A : ℝ} (t₁ : ι)
    (htop : ∀ t, (lam t).im = (lam t₁).im → (lam t).re ≤ (lam t₁).re)
    (hinj : ∀ t, lam t = lam t₁ → t = t₁) {η : ℝ} (hη : 0 < η)
    (hsep : ∀ t, |(lam t).im - (lam t₁).im| < η → (lam t).im = (lam t₁).im)
    {F : ℂ → ℂ} {c : ℝ} (hc : c < (lam t₁).re) (hF : ∀ s : ℂ, c < s.re → DifferentiableAt ℂ F s)
    (hFG : ∀ s : ℂ, A < s.re → F s = resolventSum lam q s) : q t₁ = 0 := by
  classical
  set γ := (lam t₁).im with hγ
  set δ₁ := (lam t₁).re with hδ₁
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
  -- `F = G` on the strip
  have hFan : AnalyticOnNhd ℂ F R := DifferentiableOn.analyticOnNhd
    (fun s hs => (hF s (hc.trans hs.1)).differentiableWithinAt) hRo
  have hGan : AnalyticOnNhd ℂ (resolventSum lam q) R :=
    (differentiableOn_resolventSum (lam := lam) (q := q) hq t₁ htop hη hsep).analyticOnNhd hRo
  set z₀ : ℂ := ((max A δ₁ + 1 : ℝ) : ℂ) + γ * I with hz₀
  have hz₀re : z₀.re = max A δ₁ + 1 := by simp [hz₀]
  have hz₀im : z₀.im = γ := by simp [hz₀]
  have hz₀R : z₀ ∈ R := ⟨by rw [hz₀re]; linarith [le_max_right A δ₁], by
    rw [hz₀im, sub_self, abs_zero]; linarith⟩
  have hev : F =ᶠ[𝓝 z₀] resolventSum lam q := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show A < z₀.re by rw [hz₀re]; linarith [le_max_left A δ₁])] with s hs
    exact hFG s hs
  have hEq := hFan.eqOn_of_preconnected_of_eventuallyEq hGan hRc.isPreconnected hz₀R hev
  -- approach `λ_{t₁}` horizontally from the right
  set p : ℝ → ℂ := fun σ => (σ : ℂ) + γ * I with hp
  have hpl : p δ₁ = lam t₁ := by
    apply Complex.ext <;> simp [hp, hδ₁, hγ]
  have hpR : ∀ σ, δ₁ < σ → p σ ∈ R := fun σ hσ => ⟨by simp [hp]; exact hσ, by simp [hp]; linarith⟩
  have hpc : Continuous p := by rw [hp]; fun_prop
  have hlimF : Tendsto (fun σ : ℝ => ((σ : ℂ) - δ₁) * F (p σ)) (𝓝[>] δ₁) (𝓝 0) := by
    have hcont : ContinuousAt F (lam t₁) := (hF _ hc).continuousAt
    have h1 : Tendsto (fun σ : ℝ => F (p σ)) (𝓝 δ₁) (𝓝 (F (lam t₁))) := by
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
  have hcongr : (fun σ : ℝ => ((σ : ℂ) - δ₁) * F (p σ)) =ᶠ[𝓝[>] δ₁]
      fun σ : ℝ => ((σ : ℂ) - δ₁) * resolventSum lam q (p σ) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    rw [hEq (hpR σ hσ)]
  exact tendsto_nhds_unique (hlimF.congr' hcongr) hlimG |>.symm

/-- **The Laplace transform of an exponential sum.** If `Σ_t |q_t| < ∞` and `Re λ_t ≤ A < Re s`,
then `∫_0^∞ (Σ_t q_t e^{λ_t u}) e^{−su} du = Σ_t q_t/(s − λ_t)`. -/
theorem integral_tsum_exp_mul_exp_neg {ι : Type*} [Countable ι] {lam q : ι → ℂ}
    (hq : Summable fun t => ‖q t‖) {A : ℝ} (hA : ∀ t, (lam t).re ≤ A) {s : ℂ}
    (hs : A < s.re) :
    ∫ u in Ioi (0 : ℝ), (∑' t, q t * cexp (lam t * u)) * cexp (-s * u) =
      resolventSum lam q s := by
  have hneg : ∀ t, (lam t - s).re < 0 := fun t => by simp; linarith [hA t]
  have hF : ∀ t, Integrable (fun u : ℝ => q t * cexp ((lam t - s) * u))
      (volume.restrict (Ioi 0)) :=
    fun t => (integrableOn_exp_mul_complex_Ioi (hneg t) 0).const_mul (q t)
  have hnorm : ∀ t, ∫ u in Ioi (0 : ℝ), ‖q t * cexp ((lam t - s) * u)‖ =
      ‖q t‖ / (s.re - (lam t).re) := fun t => by
    have e : ∀ u : ℝ, ‖q t * cexp ((lam t - s) * u)‖ =
        ‖q t‖ * Real.exp (((lam t).re - s.re) * u) := fun u => by
      rw [norm_mul, Complex.norm_exp]
      congr 2
      simp
    simp_rw [e]
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith [hA t]) 0, mul_zero,
      Real.exp_zero]
    have h1 : (lam t).re - s.re ≠ 0 := by linarith [hA t]
    have h2 : s.re - (lam t).re ≠ 0 := by linarith [hA t]
    field_simp
    ring
  have hsum : Summable fun t => ∫ u in Ioi (0 : ℝ), ‖q t * cexp ((lam t - s) * u)‖ := by
    simp_rw [hnorm]
    exact Summable.of_nonneg_of_le (fun t => div_nonneg (norm_nonneg _) (by linarith [hA t]))
      (fun t => div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) (by linarith [hA t]))
      (hq.div_const (s.re - A))
  have hint : ∀ u : ℝ, (∑' t, q t * cexp (lam t * u)) * cexp (-s * u) =
      ∑' t, q t * cexp ((lam t - s) * u) := fun u => by
    rw [← tsum_mul_right]
    refine tsum_congr fun t => ?_
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp_rw [hint]
  rw [← integral_tsum_of_summable_integral_norm hF hsum, resolventSum]
  refine tsum_congr fun t => ?_
  rw [integral_const_mul, integral_exp_mul_complex_Ioi (hneg t) 0, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero]
  have : lam t - s ≠ 0 := fun h => by have := hneg t; rw [h] at this; simp at this
  have : s - lam t ≠ 0 := fun h => this (by rw [← neg_sub, h, neg_zero])
  field_simp
  ring

/-! ### The lag structure as a one-sided bounded function -/

theorem abs_re_le_of_lagCoeff_ne_zero {Z : ZeroConfig} {b : ℝ → ℂ} {z : ℂ}
    (hz : lagCoeff Z b z ≠ 0) : |z.re| ≤ 1 / 2 := by
  have hmem : (1 / 2 + z) ∈ Z.carrier := by
    by_contra h; exact hz (by rw [lagCoeff, Set.indicator_of_notMem h])
  have := Z.strip _ hmem
  simp at this
  exact abs_le.mpr ⟨by linarith [this.1], by linarith [this.2]⟩

theorem summable_norm_lagCoeff (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) :
    Summable fun z : ℂ => ‖lagCoeff Z b z‖ := by
  have h := (lagStructure_eq_tsum_lagCoeff Z hZ hb hbs 0).1.norm
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
  exact h

/-- `‖F(z) e^{zv}‖ ≤ ‖F(z)‖ e^{R/2}` for `|v| ≤ R`. -/
theorem norm_lagCoeff_mul_exp_le {Z : ZeroConfig} {b : ℝ → ℂ} (z : ℂ) {v R : ℝ} (hv : |v| ≤ R) :
    ‖lagCoeff Z b z * cexp (z * v)‖ ≤ ‖lagCoeff Z b z‖ * Real.exp (R / 2) := by
  by_cases h0 : lagCoeff Z b z = 0
  · simp [h0]
  rw [norm_mul, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have hre := abs_re_le_of_lagCoeff_ne_zero h0
  have : (z * (v : ℂ)).re = z.re * v := by simp
  rw [this]
  calc z.re * v ≤ |z.re * v| := le_abs_self _
    _ = |z.re| * |v| := abs_mul _ _
    _ ≤ 1 / 2 * R := mul_le_mul hre hv (abs_nonneg _) (by norm_num)
    _ = R / 2 := by ring

/-- The lag structure is continuous in the lag. -/
theorem continuous_lagStructure (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) :
    Continuous fun v : ℝ => lagStructure Z b v := by
  have heq : (fun v : ℝ => lagStructure Z b v) =
      fun v : ℝ => ∑' z : ℂ, lagCoeff Z b z * cexp (z * v) :=
    funext fun v => (lagStructure_eq_tsum_lagCoeff Z hZ hb hbs v).2
  rw [heq, continuous_iff_continuousAt]
  intro x
  have hon : ContinuousOn (fun v : ℝ => ∑' z : ℂ, lagCoeff Z b z * cexp (z * v))
      (Ioo (x - 1) (x + 1)) :=
    continuousOn_tsum (fun z => by fun_prop)
      ((summable_norm_lagCoeff Z hZ hb hbs).mul_right (Real.exp ((|x| + 1) / 2)))
      fun z v hv => norm_lagCoeff_mul_exp_le z (by
        rw [abs_le]; constructor <;> linarith [hv.1, hv.2, abs_le.mp (le_refl |x|),
          neg_abs_le x, le_abs_self x])
  exact hon.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))

/-- **Near the real axis the exponents are real.** -/
theorem exists_im_eq_zero_of_evenCoeff (Z : ZeroConfig) (b : ℝ → ℂ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ z : ℂ, evenCoeff Z b z ≠ 0 → |z.im| < η₀ → z.im = 0 := by
  obtain ⟨η₀, hη₀, hsep⟩ := exists_sep_height Z 0
  refine ⟨η₀, hη₀, fun z hz hlt => ?_⟩
  rcases mem_of_evenCoeff_ne_zero hz with h | h
  · simpa using hsep _ h (by simpa using hlt)
  · simpa using hsep _ h (by simpa using hlt)

/-- **The one-sided bound on all lags.** If the difference tests `b(t + v/2) − b(t − v/2)` are Weil
nonnegative at every lag `v ≥ V`, then `2 Re S(v) ≤ M` for all `v ≥ 0`, with some `M ≥ 0`: on
`[V, ∞)` from `Re W = 2 Re S(0) − 2 Re S(v)`, on `[0, V]` from `|2 Re S(v)| ≤ K e^{v/2}`. -/
theorem exists_two_re_lagStructure_le (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ}
    (hm : ∀ v : ℝ, V ≤ v → 0 ≤ (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, 0 ≤ u → 2 * (lagStructure Z b u).re ≤ M := by
  set K := 2 * ∑' z : ℂ, ‖lagCoeff Z b z‖ with hK
  have hK0 : 0 ≤ K := mul_nonneg zero_le_two (tsum_nonneg fun _ => norm_nonneg _)
  have hKb : ∀ u, 0 < u → |2 * (lagStructure Z b u).re| ≤ K * Real.exp (u / 2) := by
    intro u hu
    obtain ⟨hs, he⟩ := lagStructure_eq_tsum_lagCoeff Z hZ hb hbs u
    have hle : ‖lagStructure Z b u‖ ≤ (∑' z : ℂ, ‖lagCoeff Z b z‖) * Real.exp (u / 2) := by
      rw [he, ← tsum_mul_right]
      refine (norm_tsum_le_tsum_norm hs.norm).trans (Summable.tsum_le_tsum
        (fun z => norm_lagCoeff_mul_exp_le z (le_of_eq (abs_of_pos hu))) hs.norm
        ((summable_norm_lagCoeff Z hZ hb hbs).mul_right _))
    have := Complex.abs_re_le_norm (lagStructure Z b u)
    simp only [abs_mul, abs_two, hK]
    nlinarith
  refine ⟨max (2 * (lagStructure Z b 0).re) (K * Real.exp (|V| / 2)),
    (mul_nonneg hK0 (Real.exp_pos _).le).trans (le_max_right _ _), fun u hu => ?_⟩
  rcases le_or_gt V u with hVu | huV
  · have h := hm u hVu
    have hX : lagStructure Z b u + conj (lagStructure Z b (-u)) = 2 * lagStructure Z b u := by
      rw [conj_lagStructure_neg Z hZ hb hbs u]; ring
    rw [re_W_unit_twoBump Z hZ hb hbs u (by simp), hX] at h
    simp only [neg_mul, one_mul, Complex.neg_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, zero_mul, sub_zero] at h
    linarith [le_max_left (2 * (lagStructure Z b 0).re) (K * Real.exp (|V| / 2))]
  · rcases hu.lt_or_eq with hu0 | hu0
    · refine (le_abs_self _).trans ((hKb u hu0).trans ((mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr ?_) hK0).trans (le_max_right _ _)))
      linarith [le_abs_self V]
    · rw [← hu0]
      exact le_max_left _ _

/-- **No top pole under one-sided growth, above the real exponents.** Let `0 ≤ a < ½` bound the
real exponents of `2 Re S`. If `2 Re S(u) ≤ M e^{au}` for `u ≥ 0`, then `D(z) = 0` for every
exponent with `Re z > a`. -/
theorem evenCoeff_eq_zero_of_two_re_lagStructure_le_exp (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (hreal : ∀ x : ℂ, evenCoeff Z b x ≠ 0 → x.im = 0 → x.re ≤ a) {M : ℝ}
    (hMa : ∀ u : ℝ, 0 ≤ u → 2 * (lagStructure Z b u).re ≤ M * Real.exp (a * u))
    {z : ℂ} (hz : a < z.re) : evenCoeff Z b z = 0 := by
  classical
  by_contra hne
  set ι : Set ℂ := {z | evenCoeff Z b z ≠ 0} with hι
  haveI : Countable ι := (countable_evenCoeff_support Z b).to_subtype
  -- the rightmost exponent on the line of `z`
  set L := (finite_evenCoeff_line Z b z.im).toFinset with hL
  obtain ⟨z₀, hz₀L, hmax⟩ := L.exists_max_image Complex.re
    ⟨z, (Set.Finite.mem_toFinset _).mpr ⟨hne, rfl⟩⟩
  obtain ⟨hz₀, him₀⟩ := (Set.Finite.mem_toFinset _).mp hz₀L
  have hre₀ : z.re ≤ z₀.re := hmax z ((Set.Finite.mem_toFinset _).mpr ⟨hne, rfl⟩)
  -- separation of the line of `z₀`
  obtain ⟨η₁, hη₁, hsep₁⟩ := exists_sep_height Z z₀.im
  obtain ⟨η₂, hη₂, hsep₂⟩ := exists_sep_height Z (-z₀.im)
  have hsep : ∀ t : ι, |(t : ℂ).im - z₀.im| < min η₁ η₂ → (t : ℂ).im = z₀.im := fun t ht => by
    rcases mem_of_evenCoeff_ne_zero t.2 with h | h
    · have := hsep₁ _ h (by simpa using ht.trans_le (min_le_left _ _))
      simpa using this
    · have := hsep₂ _ h (by
        rw [show (1 / 2 + conj (t : ℂ)).im - -z₀.im = -((t : ℂ).im - z₀.im) by simp; ring,
          abs_neg]
        exact ht.trans_le (min_le_right _ _))
      simp at this; linarith
  have hD0 : Summable fun z : ℂ => ‖evenCoeff Z b z‖ := by
    have h0 := (two_re_lagStructure_eq Z hZ hb hbs 0).1.norm
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
    exact h0
  have hD : Summable fun t : ι => ‖evenCoeff Z b t‖ := hD0.subtype ι
  -- `φ = 2 Re S` as an exponential sum over `ι`
  set φ : ℝ → ℝ := fun u => 2 * (lagStructure Z b u).re with hφ
  have hφm : Measurable φ :=
    (continuous_const.mul (Complex.continuous_re.comp
      (continuous_lagStructure Z hZ hb hbs))).measurable
  have hφrep : ∀ u : ℝ, ((φ u : ℝ) : ℂ) = ∑' t : ι, evenCoeff Z b t * cexp ((t : ℂ) * u) := by
    intro u
    have hsub : Function.support (fun z : ℂ => evenCoeff Z b z * cexp (z * u)) ⊆ ι :=
      fun z hz h0 => hz (show evenCoeff Z b z * cexp (z * u) = 0 by rw [h0, zero_mul])
    rw [tsum_subtype_eq_of_support_subset hsub]
    exact (two_re_lagStructure_eq Z hZ hb hbs u).2
  -- the inputs of Landau's theorem
  set K := 2 * ∑' z : ℂ, ‖lagCoeff Z b z‖ with hK
  have hKb : ∀ u, 0 < u → |φ u| ≤ K * Real.exp (u / 2) := by
    intro u hu
    obtain ⟨hs, he⟩ := lagStructure_eq_tsum_lagCoeff Z hZ hb hbs u
    have hle : ‖lagStructure Z b u‖ ≤ (∑' z : ℂ, ‖lagCoeff Z b z‖) * Real.exp (u / 2) := by
      rw [he, ← tsum_mul_right]
      refine (norm_tsum_le_tsum_norm hs.norm).trans (Summable.tsum_le_tsum
        (fun z => norm_lagCoeff_mul_exp_le z (le_of_eq (abs_of_pos hu))) hs.norm
        ((summable_norm_lagCoeff Z hZ hb hbs).mul_right _))
    have := Complex.abs_re_le_norm (lagStructure Z b u)
    simp only [hφ, abs_mul, abs_two, hK]
    nlinarith
  obtain ⟨η₀, hη₀, hnear⟩ := exists_im_eq_zero_of_evenCoeff Z b
  set Λ := resolventSum (fun t : ι => (t : ℂ)) fun t => evenCoeff Z b t with hΛ
  have hΛan : ∀ t : ℝ, a < t → AnalyticAt ℂ Λ t := by
    intro t hat
    set r := min η₀ (t - a) / 2 with hr
    have hr0 : 0 < r := by rw [hr]; exact half_pos (lt_min hη₀ (by linarith))
    have hr1 : 2 * r ≤ η₀ := by rw [hr]; linarith [min_le_left η₀ (t - a)]
    have hr2 : 2 * r ≤ t - a := by rw [hr]; linarith [min_le_right η₀ (t - a)]
    have hgap : ∀ (x : ι) (s : ℂ), s ∈ Metric.ball (t : ℂ) r → r ≤ ‖s - (x : ℂ)‖ := by
      intro x s hs
      rw [Metric.mem_ball, Complex.dist_eq] at hs
      have h2 : |s.im| ≤ ‖s - t‖ := by
        have := Complex.abs_im_le_norm (s - t); simpa using this
      have h2' : |s.re - t| ≤ ‖s - t‖ := by
        have := Complex.abs_re_le_norm (s - t); simpa using this
      by_cases hx : |(x : ℂ).im| < η₀
      · have him := hnear _ x.2 hx
        have hre := hreal _ x.2 him
        have h3 : (s - (x : ℂ)).re ≤ ‖s - (x : ℂ)‖ := Complex.re_le_norm _
        rw [Complex.sub_re] at h3
        linarith [(abs_le.mp h2').1]
      · push Not at hx
        have h3 : |(s - (x : ℂ)).im| ≤ ‖s - (x : ℂ)‖ := Complex.abs_im_le_norm _
        have h4 : |(x : ℂ).im| ≤ |(s - (x : ℂ)).im| + |s.im| := by
          rw [Complex.sub_im]
          calc |(x : ℂ).im| = |-(s.im - (x : ℂ).im) + s.im| := by ring_nf
            _ ≤ |-(s.im - (x : ℂ).im)| + |s.im| := abs_add_le _ _
            _ = |s.im - (x : ℂ).im| + |s.im| := by rw [abs_neg]
        linarith
    have hdiff : DifferentiableOn ℂ Λ (Metric.ball (t : ℂ) r) := by
      refine Complex.differentiableOn_tsum_of_summable_norm (u := fun x => ‖evenCoeff Z b x‖ / r)
        (hD.div_const _) (fun x => ?_) Metric.isOpen_ball (fun x s hs => ?_)
      · refine (differentiableOn_const _).div (differentiableOn_id.sub_const _) fun s hs h0 => ?_
        have := hgap x s hs
        rw [h0, norm_zero] at this
        linarith
      · rw [norm_div]
        exact div_le_div_of_nonneg_left (norm_nonneg _) hr0 (hgap x s hs)
    exact hdiff.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr0))
  have hΛφ : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ u in Ioi (0 : ℝ), ((φ u : ℝ) : ℂ) * cexp (-s * u) = Λ s := fun s hs => by
    simp_rw [hφrep]
    exact integral_tsum_exp_mul_exp_neg hD (fun t => re_le_of_evenCoeff_ne_zero t.2) hs
  obtain ⟨F, hF, hFG⟩ := exists_differentiable_extension_of_le_exp hφm hKb ha0 ha hMa hΛan hΛφ
  exact hz₀ (eq_zero_of_resolventSum_eq_differentiable (lam := fun t : ι => (t : ℂ))
    (q := fun t => evenCoeff Z b t) hD (A := 1 / 2) ⟨z₀, hz₀⟩
    (fun t ht => hmax t ((Set.Finite.mem_toFinset _).mpr ⟨t.2, ht.trans him₀⟩))
    (fun t ht => Subtype.ext ht) (lt_min hη₁ hη₂) hsep (c := a) (by simp; linarith) hF hFG)

/-- **No top pole from one side, above the real exponents.** Let `0 ≤ a < ½` bound the real
exponents of `2 Re S`. If the difference tests `b(t + v/2) − b(t − v/2)` are Weil nonnegative at
every lag `v ≥ V`, then `D(z) = 0` for every exponent with `Re z > a`. -/
theorem evenCoeff_eq_zero_of_difference_nonneg_above (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (hreal : ∀ x : ℂ, evenCoeff Z b x ≠ 0 → x.im = 0 → x.re ≤ a) {V : ℝ}
    (hm : ∀ v : ℝ, V ≤ v → 0 ≤ (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {z : ℂ} (hz : a < z.re) : evenCoeff Z b z = 0 := by
  obtain ⟨M, hM0, hMb⟩ := exists_two_re_lagStructure_le Z hZ hb hbs hm
  exact evenCoeff_eq_zero_of_two_re_lagStructure_le_exp Z hZ hb hbs ha0 ha hreal (fun u hu =>
    (hMb u hu).trans (le_mul_of_one_le_right hM0 (Real.one_le_exp (mul_nonneg ha0 hu)))) hz

/-- **No top pole from one side.** For a configuration without real zeros, if the difference
tests `b(t + v/2) − b(t − v/2)` are Weil nonnegative at every lag `v ≥ V`, then `D(z) = 0` for
every exponent with `Re z > 0`. -/
theorem evenCoeff_eq_zero_of_difference_nonneg (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w)
    (hreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {V : ℝ}
    (hm : ∀ v : ℝ, V ≤ v → 0 ≤ (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {z : ℂ} (hz : 0 < z.re) : evenCoeff Z b z = 0 :=
  evenCoeff_eq_zero_of_difference_nonneg_above Z hZ hb hbs le_rfl (by norm_num)
    (fun x hx him => absurd him (by
      rcases mem_of_evenCoeff_ne_zero hx with h | h
      · exact fun h0 => hreal _ h (by simpa using h0)
      · exact fun h0 => hreal _ h (by simpa using h0))) hm hz

/-! ### One sign decides the line -/

/-- **One sign decides the line.** Let `0 < w` and `V ∈ ℝ`. A tempered configuration without real
zeros has all its zeros on the critical line iff its Weil form is nonnegative on every difference
two-bump test `κ_{w,γ}(t + v/2) − κ_{w,γ}(t − v/2)`, `γ ∈ ℝ`, `v ≥ V`. -/
theorem onLine_iff_difference_twoBump_nonneg (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {w : ℝ} (hw : 0 < w) (V : ℝ) :
    (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) ↔ ∀ (γ v : ℝ), V ≤ v →
      0 ≤ (Z.W (twoBump (modScaledBump w γ) v (-1)) (twoBump (modScaledBump w γ) v (-1))).re := by
  refine ⟨fun hon _ _ _ => weil_nonneg_of_onLine Z hon _, fun h ρ hρ => ?_⟩
  by_contra hre
  obtain ⟨t, ht, -⟩ := exists_rightZero_of_offLine Z hρ hre
  have hz : (1 / 2 + (t - 1 / 2)) ∈ Z.carrier := by rw [add_sub_cancel]; exact ht.1
  have hzre : 0 < (t - 1 / 2).re := by simp; linarith [ht.2]
  obtain ⟨c, hc⟩ := exists_center_evenCoeff_ne_zero Z hw hz
  exact hc (evenCoeff_eq_zero_of_difference_nonneg Z hZ (contDiff_modScaledBump_two w c)
    (modScaledBump_support hw c) hreal (fun v hv => h c v hv) hzre)

/-- The nontrivial zeros of `ζ` are not real. -/
theorem zetaZeroConfig_im_ne_zero : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.im ≠ 0 := by
  intro ρ hρ him
  have h : 0 < ρ.re ∧ ρ.re < 1 := hρ.2
  exact riemannZeta_ne_zero_of_abs_im_lt_four h.1 h.2 (by rw [him, abs_zero]; norm_num) hρ.1

/-- **For `ζ`, on the prime side.** RH holds iff the prime-side functional is nonnegative on the
autocorrelations of the difference tests `κ_γ(t + v/2) − κ_γ(t − v/2)`, `γ ∈ ℝ`, `v ≥ 0`. -/
theorem onLine_iff_primeSide_difference_twoBump_nonneg :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) ↔ ∀ (γ v : ℝ), 0 ≤ v →
      0 ≤ (EF.literatureRHS (EF.weilTest (twoBump (modScaledBump 1 γ) v (-1))
        (twoBump (modScaledBump 1 γ) v (-1)))).re := by
  refine (onLine_iff_difference_twoBump_nonneg _ temperedConfig_zetaZeroConfig
    zetaZeroConfig_im_ne_zero one_pos 0).trans ?_
  refine forall_congr' fun γ => forall_congr' fun v => ?_
  rw [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump 1 γ) v (-1))
    (contDiff_bumpTest (contDiff_modScaledBump_two 1 γ) v ![1, -1])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support one_pos γ)) v (-1))]

/-- **RH as one-signed dyadic prime windows.** Let `0 < w`, `2w < log 2` and `V ≥ 0`. RH holds
iff the window functional `P_v` is nonnegative on the difference tests
`κ_{w,γ}(t + v/2) − κ_{w,γ}(t − v/2)` at every height `γ` and every lag `v ≥ V`. Two real
parameters, one sign, and the primes of one dyadic window per test. -/
theorem onLine_iff_difference_primeWindow_nonneg {w : ℝ} (hw : 0 < w)
    (hw2 : 2 * w < Real.log 2) {V : ℝ} (hV : 0 ≤ V) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) ↔ ∀ (γ v : ℝ), V ≤ v →
      0 ≤ (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w γ) v (-1))
        (twoBump (modScaledBump w γ) v (-1)))).re := by
  refine (onLine_iff_difference_twoBump_nonneg _ temperedConfig_zetaZeroConfig
    zetaZeroConfig_im_ne_zero hw V).trans ?_
  refine forall_congr' fun γ => forall_congr' fun v => imp_congr_right fun hv => ?_
  rw [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w γ) v (-1))
    (contDiff_bumpTest (contDiff_modScaledBump_two w γ) v ![1, -1])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw γ)) v (-1)),
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw γ) hw2 (hV.trans hv)]

/-! ### The Hodge class -/

/-- For the polar-free bump `κ₂,w` modulated to `c`, the coefficient of the zero `½ + z` is
`(¼ − z²)²` times that of `κ_w` modulated to `c`. -/
theorem lagCoeff_scaledBumpPolarFree (Z : ZeroConfig) {w : ℝ} (hw : 0 < w) (c : ℝ) (z : ℂ) :
    lagCoeff Z (scaledBumpPolarFree w c) z =
      (1 / 4 - z ^ 2) ^ 2 * lagCoeff Z (modScaledBump w c) z := by
  by_cases hz : (1 / 2 + z) ∈ Z.carrier
  · have hbc : HasCompactSupport (scaledBumpPolarFree w c) :=
      hasCompactSupport_of_support_subset_abs (scaledBumpPolarFree_support hw c)
    have hcont := (contDiff_scaledBumpPolarFree w c).continuous
    rw [lagCoeff_modScaledBump Z hw c hz, lagCoeff, Set.indicator_of_mem hz,
      EF.paperFT_weilTest hcont hcont hbc hbc, paperFT_scaledBumpPolarFree hw,
      paperFT_scaledBumpPolarFree hw, map_mul, conj_paperFT_scaledBump, gammaOf_half_add]
    simp only [map_sub, map_neg, map_mul, map_add, map_pow, map_div₀, map_one, map_ofNat,
      Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
    ring_nf
    simp only [Complex.I_sq, Complex.I_pow_four]
    ring
  · rw [lagCoeff, lagCoeff, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]

theorem evenCoeff_scaledBumpPolarFree (Z : ZeroConfig) {w : ℝ} (hw : 0 < w) (c : ℝ) (z : ℂ) :
    evenCoeff Z (scaledBumpPolarFree w c) z =
      (1 / 4 - z ^ 2) ^ 2 * evenCoeff Z (modScaledBump w c) z := by
  rw [evenCoeff, evenCoeff, lagCoeff_scaledBumpPolarFree Z hw, lagCoeff_scaledBumpPolarFree Z hw,
    map_mul, map_pow, map_sub, map_pow, Complex.conj_conj, map_div₀, map_one, map_ofNat]
  ring

/-- **One sign decides the line in the Hodge class.** Let `0 < w` and `V ∈ ℝ`. A tempered
configuration without real zeros has all its zeros on the critical line iff its Weil form is
nonnegative on every polar-free difference test `κ₂,γ(t + v/2) − κ₂,γ(t − v/2)`, `v ≥ V`. -/
theorem onLine_iff_polarFree_difference_twoBump_nonneg (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {w : ℝ} (hw : 0 < w) (V : ℝ) :
    (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) ↔ ∀ (γ v : ℝ), V ≤ v →
      0 ≤ (Z.W (twoBump (scaledBumpPolarFree w γ) v (-1))
        (twoBump (scaledBumpPolarFree w γ) v (-1))).re := by
  refine ⟨fun hon _ _ _ => weil_nonneg_of_onLine Z hon _, fun h ρ hρ => ?_⟩
  by_contra hre
  obtain ⟨t, ht, -⟩ := exists_rightZero_of_offLine Z hρ hre
  have hz : (1 / 2 + (t - 1 / 2)) ∈ Z.carrier := by rw [add_sub_cancel]; exact ht.1
  have hzre : 0 < (t - 1 / 2).re := by simp; linarith [ht.2]
  obtain ⟨c, hc⟩ := exists_center_evenCoeff_ne_zero Z hw hz
  have hpol : (1 / 4 - (t - 1 / 2) ^ 2 : ℂ) ≠ 0 := by
    intro h0
    have hfac : (t - 1 / 2 - 1 / 2) * (t - 1 / 2 + 1 / 2) = (0 : ℂ) := by linear_combination -h0
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact hreal t ht.1 (by have := congrArg Complex.im h1; simpa using this)
    · exact hreal t ht.1 (by have := congrArg Complex.im h1; simpa using this)
  have h0 := evenCoeff_eq_zero_of_difference_nonneg Z hZ (contDiff_scaledBumpPolarFree w c)
    (scaledBumpPolarFree_support hw c) hreal (fun v hv => h c v hv) hzre
  rw [evenCoeff_scaledBumpPolarFree Z hw] at h0
  exact hc ((mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 hpol))

/-- **RH: the archimedean term dominates the pole-free dyadic prime windows, one sign.** Let
`0 < w`, `2w < log 2` and `V ≥ 0`. RH holds iff for every height `γ` and lag `v ≥ V` the window
prime sum of the kernel `k` of the polar-free difference test `κ₂,γ(t + v/2) − κ₂,γ(t − v/2)` is
at most its archimedean term. -/
theorem onLine_iff_polarFree_difference_primeWindow_le_arch {w : ℝ} (hw : 0 < w)
    (hw2 : 2 * w < Real.log 2) {V : ℝ} (hV : 0 ≤ V) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) ↔
      ∀ (γ v : ℝ), V ≤ v →
        (∑ n ∈ lagPrimeWindow v w, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
          (polarFreeKernel w γ v (-1) (Real.log n) +
            polarFreeKernel w γ v (-1) (-Real.log n))).re ≤
        ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (polarFreeKernel w γ v (-1)) r *
          (EF.gammaBracket r : ℂ)).re := by
  refine (onLine_iff_polarFree_difference_twoBump_nonneg _ temperedConfig_zetaZeroConfig
    zetaZeroConfig_im_ne_zero hw V).trans ?_
  refine forall_congr' fun γ => forall_congr' fun v => imp_congr_right fun hv => ?_
  have hc := (contDiff_scaledBumpPolarFree w γ).continuous
  have hbc := hasCompactSupport_of_support_subset_abs (scaledBumpPolarFree_support hw γ)
  have hfc := hasCompactSupport_twoBump hbc v (-1)
  have hfcont : Continuous (twoBump (scaledBumpPolarFree w γ) v (-1)) :=
    (contDiff_bumpTest (contDiff_scaledBumpPolarFree w γ) v ![1, -1]).continuous
  obtain ⟨hp, hn⟩ := paperFT_scaledBumpPolarFree_half hw γ
  have hpole : ∀ z : ℂ, paperFT (twoBump (scaledBumpPolarFree w γ) v (-1)) z = 0 →
      paperFT (polarFreeKernel w γ v (-1)) z = 0 := fun z hz => by
    rw [polarFreeKernel, EF.paperFT_weilTest hfcont hfcont hfc hfc, hz, zero_mul]
  rw [zeta_W_eq_literatureRHS (f := twoBump (scaledBumpPolarFree w γ) v (-1))
    (contDiff_bumpTest (contDiff_scaledBumpPolarFree w γ) v ![1, -1]) hfc,
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (scaledBumpPolarFree_support hw γ) hw2
      (hV.trans hv), lagPrimeWindowRHS, ← polarFreeKernel,
    hpole _ (paperFT_twoBump_eq_zero hc hbc v (-1) hp),
    hpole _ (by rw [neg_div]; exact paperFT_twoBump_eq_zero hc hbc v (-1) hn)]
  simp only [add_zero, zero_sub, Complex.add_re, Complex.neg_re]
  constructor <;> intro h <;> linarith

end GaloisForLFunctions.SquareRootThreshold
