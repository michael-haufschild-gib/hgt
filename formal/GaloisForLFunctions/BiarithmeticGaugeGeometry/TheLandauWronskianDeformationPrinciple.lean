import GaloisForLFunctions.RHTower.LandauSingularAtAbscissa
import GaloisForLFunctions.RHTower.ComplexLaplaceHolomorphy
import GaloisForLFunctions.RHTower.LaplaceAbscissaExists
import GaloisForLFunctions.RHTower.LandauAbscissaWitnesses
import GaloisForLFunctions.RHTower.TailMeasureLaplace

/-!
# The Landau–Wronskian Deformation Principle

Two entire functions `Λ, Λ₀` whose logarithmic derivatives differ, on a real ray, by the Laplace
transform of a nonnegative measure (plus a holomorphic perturbation) have the same divisor right of
the abscissa of the measure, and the abscissa, if positive, is a real zero of `Λ₀` at which `Λ`
vanishes to strictly lower order. No functional equation, growth or Euler product enters: the
comparison is local in the divisor and global only through Landau's theorem.

1. **Logarithmic derivatives near a zero (`exists_logDeriv_cofactor`, `tendsto_sub_mul_logDeriv`).**
   Near a zero of order `n`, `f = (z − w)^n g` with `g` analytic and nonvanishing on a ball, so
   `f'/f = n/(z − w) + g'/g` and `(z − w) f'/f → n`.
2. **Lebesgue thickening (`exists_isAbscissa_add_volume`, `complexLaplace_add_volume`).** Adding
   Lebesgue measure on `(0, ∞)` pins a finite abscissa `c ≥ 0` and changes the transform by `1/s`.
3. **The principle (`landauWronskian_orders_and_anchor`).** The Wronskian
   `Λ₀'Λ − Λ'Λ₀ − (𝓛ν' − 1/s + E) Λ Λ₀` vanishes on the ray, hence on `Re s > max(c, σ_E)`; its
   residues give equal orders there; Landau's theorem and positivity on the real ray give the
   anchor `ord_c Λ < ord_c Λ₀` when `c > max(0, σ_E)`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

open GaloisForLFunctions.RHTower (laplaceReal laplaceMass complexLaplace IsAbscissa
  complexLaplace_ofReal differentiableOn_complexLaplace integrable_cexp_of_gt_abscissa
  isAbscissa_volume_zero exists_isAbscissa false_of_analyticAt_abscissa laplaceMass_antitone)

/-! ## §1. Logarithmic derivatives near a zero of finite order -/

/-- Near a zero of order `n`, `f = (z − w)^n g` on a ball with `g` analytic and nonvanishing, and
`f'/f = n/(z − w) + g'/g` off the centre. -/
theorem exists_logDeriv_cofactor {f : ℂ → ℂ} {w : ℂ} (hf : AnalyticAt ℂ f w) {n : ℕ}
    (hn : analyticOrderAt f w = n) :
    ∃ g : ℂ → ℂ, ∃ δ > 0, ∀ z ∈ Metric.ball w δ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
      f z = (z - w) ^ n * g z ∧
      (z ≠ w → f z ≠ 0 ∧ logDeriv f z = n / (z - w) + logDeriv g z) := by
  obtain ⟨g, hg, hgw, hfg⟩ := (hf.analyticOrderAt_eq_natCast).mp hn
  have hev : ∀ᶠ z in 𝓝 w, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ f z = (z - w) ^ n * g z :=
    hg.eventually_analyticAt.and ((hg.continuousAt.eventually_ne hgw).and
      (hfg.mono fun z hz => by simpa [smul_eq_mul] using hz))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨g, δ, hδ, fun z hz => ⟨(hball z hz).1, (hball z hz).2.1, (hball z hz).2.2,
    fun hzw => ?_⟩⟩
  obtain ⟨hgz, hgnz, hfz⟩ := hball z hz
  have hzw' : z - w ≠ 0 := sub_ne_zero.mpr hzw
  refine ⟨by rw [hfz]; exact mul_ne_zero (pow_ne_zero _ hzw') hgnz, ?_⟩
  have hloc : f =ᶠ[𝓝 z] fun y => (y - w) ^ n * g y := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy using (hball y hy).2.2
  rw [logDeriv_apply, hloc.deriv_eq, hloc.eq_of_nhds, ← logDeriv_apply,
    logDeriv_mul (f := fun y : ℂ => (y - w) ^ n) z (pow_ne_zero _ hzw') hgnz (by fun_prop)
      hgz.differentiableAt,
    logDeriv_fun_pow (f := fun y : ℂ => y - w)
      (by fun_prop : DifferentiableAt ℂ (fun y : ℂ => y - w) z), logDeriv_apply,
    deriv_sub_const, deriv_id'']
  ring

/-- `(z − w) f'(z)/f(z) → ord_w f` as `z → w`, `z ≠ w`. -/
theorem tendsto_sub_mul_logDeriv {f : ℂ → ℂ} {w : ℂ} (hf : AnalyticAt ℂ f w) {n : ℕ}
    (hn : analyticOrderAt f w = n) :
    Tendsto (fun z => (z - w) * logDeriv f z) (𝓝[≠] w) (𝓝 (n : ℂ)) := by
  obtain ⟨g, δ, hδ, hball⟩ := exists_logDeriv_cofactor hf hn
  have hgw := hball w (Metric.mem_ball_self hδ)
  have hcont : ContinuousAt (fun z => (n : ℂ) + (z - w) * logDeriv g z) w := by
    have hlg : ContinuousAt (fun z => deriv g z / g z) w :=
      hgw.1.deriv.continuousAt.div hgw.1.continuousAt hgw.2.1
    exact continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul hlg)
  have hlim := hcont.tendsto
  simp only [sub_self, zero_mul, add_zero] at hlim
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ)),
    self_mem_nhdsWithin] with z hz hzw
  rw [((hball z hz).2.2.2 hzw).2]
  have hzw' : z - w ≠ 0 := sub_ne_zero.mpr hzw
  field_simp

/-! ## §2. The thickened positive measure and its abscissa -/

/-- Laplace transform of Lebesgue measure on `(0, ∞)`: `1/s`. -/
theorem complexLaplace_volume {s : ℂ} (hs : 0 < s.re) : complexLaplace volume s = 1 / s := by
  unfold complexLaplace
  have h := integral_exp_mul_complex_Ioi (a := -s) (by simp; linarith) 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h
  rw [h, neg_div_neg_eq]

theorem laplaceMass_add_volume (ν : Measure ℝ) (σ : ℝ) :
    laplaceMass (ν + volume) σ = laplaceMass ν σ + laplaceMass volume σ := by
  unfold laplaceMass
  rw [Measure.restrict_add, lintegral_add_measure]

/-- Thickening by Lebesgue measure pins a finite abscissa `c ≥ 0`. -/
theorem exists_isAbscissa_add_volume {ν : Measure ℝ} {σ₁ : ℝ} (hconv : laplaceMass ν σ₁ ≠ ⊤) :
    ∃ c : ℝ, 0 ≤ c ∧ IsAbscissa (ν + volume) c := by
  have hconv' : ∃ σ, laplaceMass (ν + volume) σ ≠ ⊤ := by
    refine ⟨max σ₁ 1, ?_⟩
    rw [laplaceMass_add_volume]
    exact ENNReal.add_ne_top.mpr ⟨ne_top_of_le_ne_top hconv
      (laplaceMass_antitone ν (le_max_left σ₁ 1)),
      isAbscissa_volume_zero.1 _ (lt_of_lt_of_le one_pos (le_max_right σ₁ 1))⟩
  have hdiv : ∃ σ, laplaceMass (ν + volume) σ = ⊤ :=
    ⟨-1, by rw [laplaceMass_add_volume, isAbscissa_volume_zero.2 (-1) (by norm_num), add_top]⟩
  obtain ⟨c, hc⟩ := exists_isAbscissa hconv' hdiv
  refine ⟨c, ?_, hc⟩
  by_contra hneg
  push Not at hneg
  have h1 := hc.1 (c / 2) (by linarith)
  rw [laplaceMass_add_volume, isAbscissa_volume_zero.2 (c / 2) (by linarith), add_top] at h1
  exact h1 rfl

theorem complexLaplace_add_volume {ν : Measure ℝ} {c : ℝ} (hc : IsAbscissa (ν + volume) c)
    (hc0 : 0 ≤ c) {s : ℂ} (hs : c < s.re) :
    complexLaplace (ν + volume) s = complexLaplace ν s + 1 / s := by
  have hint := integrable_cexp_of_gt_abscissa hc hs
  rw [Measure.restrict_add] at hint
  have h1 := hint.mono_measure (Measure.le_add_right le_rfl)
  have h2 := hint.mono_measure (Measure.le_add_left le_rfl)
  unfold complexLaplace
  rw [Measure.restrict_add, integral_add_measure h1 h2]
  congr 1
  exact complexLaplace_volume (by linarith)


/-! ## §3. The principle -/

/-- **The Landau–Wronskian deformation principle.** Let `Λ, Λ₀` be entire with finite orders
everywhere, and suppose that on a real ray both are nonzero and
`Λ₀'/Λ₀ − Λ'/Λ = 𝓛ν + E` with `ν ≥ 0` and `E` holomorphic on `Re s > σ_E`. Then there is `c ≥ 0`
such that `ord_w Λ = ord_w Λ₀` for all `Re w > max(c, σ_E)`, the relation holds on that half-plane
away from zeros, the Laplace kernel of `ν` is integrable on `Re z > c`, and if `c > max(0, σ_E)`
then `c` is a real zero of `Λ₀` with `ord_c Λ < ord_c Λ₀`.

Proof: thicken `ν` by Lebesgue measure to pin a finite abscissa `c`; the Wronskian
`Λ₀'Λ − Λ'Λ₀ − (𝓛(ν + Leb) − 1/s + E) Λ Λ₀` vanishes on the ray, hence on `Re s > max(c, σ_E)`,
so residues of `Λ₀'/Λ₀ − Λ'/Λ` vanish there. At `c > 0` Landau's theorem forbids equal orders and
positivity of the transform on the real ray fixes the sign. -/
theorem landauWronskian_orders_and_anchor {Λ Λ₀ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    (hΛ₀ : Differentiable ℂ Λ₀) (htop : ∀ z, analyticOrderAt Λ z ≠ ⊤)
    (htop₀ : ∀ z, analyticOrderAt Λ₀ z ≠ ⊤) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv : laplaceMass ν σ₁ ≠ ⊤) {E : ℂ → ℂ} {σE : ℝ}
    (hE : DifferentiableOn ℂ E {s : ℂ | σE < s.re})
    (hagree : ∀ σ : ℝ, σ₁ < σ → Λ σ ≠ 0 ∧ Λ₀ σ ≠ 0 ∧
      logDeriv Λ₀ (σ : ℂ) - logDeriv Λ (σ : ℂ) = ((laplaceReal ν σ : ℝ) : ℂ) + E σ) :
    ∃ c : ℝ, 0 ≤ c ∧
      (∀ w : ℂ, max c σE < w.re → analyticOrderAt Λ w = analyticOrderAt Λ₀ w) ∧
      (0 < c → σE < c → Λ₀ (c : ℂ) = 0 ∧
        (analyticOrderAt Λ (c : ℂ)).toNat < (analyticOrderAt Λ₀ (c : ℂ)).toNat) ∧
      (∀ z : ℂ, max c σE < z.re → Λ z ≠ 0 → Λ₀ z ≠ 0 →
        logDeriv Λ₀ z - logDeriv Λ z = complexLaplace ν z + E z) ∧
      (∀ z : ℂ, c < z.re →
        Integrable (fun u : ℝ => Complex.exp (-z * (u : ℂ))) (ν.restrict (Ioi (0 : ℝ)))) := by
  obtain ⟨c, hc0, hc⟩ := exists_isAbscissa_add_volume hconv
  set ν' : Measure ℝ := ν + volume with hν'
  obtain ⟨L, hLdef⟩ : ∃ L : ℂ → ℂ, L = fun s => complexLaplace ν' s - 1 / s + E s := ⟨_, rfl⟩
  set U : Set ℂ := {s : ℂ | max c σE < s.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : U ⊆ {s : ℂ | c < s.re} := fun s (hs : max c σE < s.re) =>
    show c < s.re from lt_of_le_of_lt (le_max_left _ _) hs
  have hUE : U ⊆ {s : ℂ | σE < s.re} := fun s (hs : max c σE < s.re) =>
    show σE < s.re from lt_of_le_of_lt (le_max_right _ _) hs
  have hne0 : ∀ s ∈ U, s ≠ 0 := fun s hs h => by
    have : c < s.re := hUc hs; rw [h] at this; simp at this; linarith
  have hLd : DifferentiableOn ℂ L U := hLdef ▸
    (((differentiableOn_complexLaplace hc).mono hUc).sub
      (DifferentiableOn.div (differentiableOn_const 1) differentiableOn_id hne0)).add (hE.mono hUE)
  have hLan : AnalyticOnNhd ℂ L U := hLd.analyticOnNhd hU
  have hΛan : ∀ z, AnalyticAt ℂ Λ z := fun z => hΛ.analyticAt z
  have hΛ₀an : ∀ z, AnalyticAt ℂ Λ₀ z := fun z => hΛ₀.analyticAt z
  -- the Wronskian vanishes on the half-plane
  obtain ⟨K, hKdef⟩ : ∃ K : ℂ → ℂ,
      K = fun s => deriv Λ₀ s * Λ s - deriv Λ s * Λ₀ s - L s * Λ s * Λ₀ s := ⟨_, rfl⟩
  have hKan : AnalyticOnNhd ℂ K U := fun s hs => hKdef ▸
    ((((hΛ₀an s).deriv.mul (hΛan s)).sub ((hΛan s).deriv.mul (hΛ₀an s))).sub
      (((hLan s hs).mul (hΛan s)).mul (hΛ₀an s)))
  set M : ℝ := max σ₁ (max c σE) with hMdef
  have hK0 : ∀ σ : ℝ, M < σ → K (σ : ℂ) = 0 := by
    intro σ hσ
    have hσcE : max c σE < σ := lt_of_le_of_lt (le_max_right _ _) hσ
    have hσc : c < σ := lt_of_le_of_lt (le_max_left _ _) hσcE
    have hσσ₁ : σ₁ < σ := lt_of_le_of_lt (le_max_left _ _) hσ
    obtain ⟨hΛne, hΛ₀ne, h3⟩ := hagree σ hσσ₁
    have hlog : -logDeriv Λ (σ : ℂ) + logDeriv Λ₀ (σ : ℂ) = L σ := by
      have hLσ : L σ = ((laplaceReal ν σ : ℝ) : ℂ) + E σ := by
        simp only [hLdef]
        rw [complexLaplace_add_volume hc hc0 (by simpa using hσc), complexLaplace_ofReal]
        ring
      rw [hLσ, ← h3]
      ring
    rw [hKdef]
    show deriv Λ₀ σ * Λ σ - deriv Λ σ * Λ₀ σ - L σ * Λ σ * Λ₀ σ = 0
    rw [logDeriv_apply, logDeriv_apply] at hlog
    field_simp at hlog
    linear_combination hlog
  have hfreq : ∃ᶠ z in 𝓝[≠] (((M + 1 : ℝ)) : ℂ), K z = 0 := by
    have htend : Tendsto (fun n : ℕ => (((M + 1 + 1 / ((n : ℝ) + 1) : ℝ)) : ℂ)) atTop
        (𝓝[≠] (((M + 1 : ℝ)) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h := ((tendsto_one_div_add_atTop_nhds_zero_nat).const_add (M + 1))
        rw [add_zero] at h
        exact (Complex.continuous_ofReal.tendsto _).comp h
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h
        have := Complex.ofReal_injective h
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    exact htend.frequently (Frequently.of_forall fun n => hK0 _ (by
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith))
  have hMU : (((M + 1 : ℝ)) : ℂ) ∈ U := by
    show max c σE < (((M + 1 : ℝ)) : ℂ).re
    simp only [Complex.ofReal_re]
    have : max c σE ≤ M := le_max_right _ _
    linarith
  have hKzero : ∀ s ∈ U, K s = 0 := fun s hs =>
    hKan.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
      (convex_halfSpace_re_gt (max c σE)).isPreconnected hMU hfreq hs
  -- away from zeros, `Λ_γ'/Λ_γ − Λ'/Λ = L` on the half-plane
  have hrel : ∀ z ∈ U, Λ z ≠ 0 → Λ₀ z ≠ 0 → logDeriv Λ₀ z - logDeriv Λ z = L z := by
    intro z hz hΛz hΛ₀z
    have h := hKzero z hz
    rw [hKdef] at h
    change deriv Λ₀ z * Λ z - deriv Λ z * Λ₀ z - L z * Λ z * Λ₀ z = 0 at h
    rw [logDeriv_apply, logDeriv_apply]
    field_simp
    linear_combination h
  -- equal orders right of the abscissa
  have hordU : ∀ w : ℂ, max c σE < w.re → analyticOrderAt Λ w = analyticOrderAt Λ₀ w := by
    intro w hw
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (htop w)
    obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (htop₀ w)
    have hta := tendsto_sub_mul_logDeriv (hΛan w) ha.symm
    have htb := tendsto_sub_mul_logDeriv (hΛ₀an w) hb.symm
    obtain ⟨gA, δA, hδA, hA⟩ := exists_logDeriv_cofactor (hΛan w) ha.symm
    obtain ⟨gB, δB, hδB, hB⟩ := exists_logDeriv_cofactor (hΛ₀an w) hb.symm
    have hwU : w ∈ U := hw
    have hlim0 : Tendsto (fun z => (z - w) * L z) (𝓝[≠] w) (𝓝 0) := by
      have h : ContinuousAt (fun z => (z - w) * L z) w :=
        (continuousAt_id.sub continuousAt_const).mul (hLan w hwU).continuousAt
      have h' := h.tendsto
      simp only [sub_self, zero_mul] at h'
      exact h'.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ z in 𝓝[≠] w,
        (z - w) * logDeriv Λ₀ z - (z - w) * logDeriv Λ z = (z - w) * L z := by
      filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδA)),
        nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδB)),
        nhdsWithin_le_nhds (hU.mem_nhds hwU), self_mem_nhdsWithin] with z hzA hzB hzU hzw
      rw [← mul_sub, hrel z hzU ((hA z hzA).2.2.2 hzw).1 ((hB z hzB).2.2.2 hzw).1]
    have hlim := (htb.sub hta).congr' hev
    have hba : (b : ℂ) - a = 0 := tendsto_nhds_unique hlim hlim0
    have hab : (a : ℂ) = b := (sub_eq_zero.mp hba).symm
    rw [← ha, ← hb]
    exact_mod_cast hab
  refine ⟨c, hc0, hordU, fun hcpos hcE => ?_, fun z hz hΛz hΛ₀z => ?_, fun z hz => ?_⟩
  rotate_left
  · rw [hrel z hz hΛz hΛ₀z, hLdef]
    simp only
    rw [complexLaplace_add_volume hc hc0 (hUc hz)]
    ring
  · have hint := integrable_cexp_of_gt_abscissa hc hz
    rw [Measure.restrict_add] at hint
    exact hint.mono_measure (Measure.le_add_right le_rfl)
  -- the abscissa: Landau's theorem against equal orders, positivity for the sign
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (htop (c : ℂ))
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (htop₀ (c : ℂ))
  obtain ⟨gA, δA, hδA, hA⟩ := exists_logDeriv_cofactor (hΛan c) ha.symm
  obtain ⟨gB, δB, hδB, hB⟩ := exists_logDeriv_cofactor (hΛ₀an c) hb.symm
  set δ : ℝ := min (min δA δB) (min (c / 2) (c - σE)) with hδdef
  have hδ : 0 < δ := lt_min (lt_min hδA hδB) (lt_min (by linarith) (by linarith))
  have hδc : δ ≤ c / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδE : δ ≤ c - σE := le_trans (min_le_right _ _) (min_le_right _ _)
  have hballA : ∀ z ∈ Metric.ball (c : ℂ) δ, z ∈ Metric.ball (c : ℂ) δA := fun z hz =>
    Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _)) hz
  have hballB : ∀ z ∈ Metric.ball (c : ℂ) δ, z ∈ Metric.ball (c : ℂ) δB := fun z hz =>
    Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_right _ _)) hz
  have hballE : ∀ z ∈ Metric.ball (c : ℂ) δ, σE < z.re := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have h1 := Complex.abs_re_le_norm (z - c)
    simp only [Complex.sub_re, Complex.ofReal_re] at h1
    have := (abs_lt.mp (lt_of_le_of_lt h1 hz)).1
    linarith
  have hreal_ball : ∀ σ : ℝ, c < σ → σ < c + δ → (σ : ℂ) ∈ Metric.ball (c : ℂ) δ := by
    intro σ h1 h2
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  -- on the real segment right of `c`: `Λ_γ'/Λ_γ − Λ'/Λ + 1/σ = 𝓛ν'(σ)`
  have hseg : ∀ σ : ℝ, c < σ → σ < c + δ →
      logDeriv Λ₀ (σ : ℂ) - logDeriv Λ (σ : ℂ) + 1 / (σ : ℂ) - E σ =
          ((laplaceReal ν' σ : ℝ) : ℂ) ∧
        logDeriv Λ (σ : ℂ) = a / ((σ : ℂ) - c) + logDeriv gA σ ∧
        logDeriv Λ₀ (σ : ℂ) = b / ((σ : ℂ) - c) + logDeriv gB σ := by
    intro σ h1 h2
    have hb' := hreal_ball σ h1 h2
    have hσc : (σ : ℂ) ≠ (c : ℂ) := fun h => by
      have := Complex.ofReal_injective h; linarith
    have hAσ := (hA σ (hballA σ hb')).2.2.2 hσc
    have hBσ := (hB σ (hballB σ hb')).2.2.2 hσc
    have hσU : (σ : ℂ) ∈ U := by
      show max c σE < (σ : ℂ).re; simpa using max_lt h1 (by linarith)
    refine ⟨?_, hAσ.2, hBσ.2⟩
    rw [hrel σ hσU hAσ.1 hBσ.1, ← complexLaplace_ofReal]
    simp only [hLdef]
    ring
  have hab : a ≠ b := by
    intro hab
    refine false_of_analyticAt_abscissa hc hδ
      (Φ := fun z => deriv gB z / gB z - deriv gA z / gA z + 1 / z - E z) (fun z hz => ?_)
      (fun σ h1 h2 => ?_)
    · have hzA := hA z (hballA z hz)
      have hzB := hB z (hballB z hz)
      have hz0 : z ≠ 0 := by
        intro h
        rw [h, Metric.mem_ball, dist_comm, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)] at hz
        linarith
      exact (((hzB.1.deriv.div hzB.1 hzB.2.1).sub (hzA.1.deriv.div hzA.1 hzA.2.1)).add
        (analyticAt_const.div analyticAt_id hz0)).sub
        ((hE.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)) z (hballE z hz))
    · obtain ⟨hL, hlA, hlB⟩ := hseg σ h1 h2
      rw [← hL, hlA, hlB, hab, logDeriv_apply, logDeriv_apply]
      ring
  -- sign of `ord_c Λ_γ − ord_c Λ` from positivity of the transform on the real ray
  have hsign : (a : ℝ) ≤ b := by
    have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] c) (𝓝[≠] (c : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto c).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with σ hσ
        intro h
        have := Complex.ofReal_injective h
        have hσ' : c < σ := hσ
        linarith
    have hta := (tendsto_sub_mul_logDeriv (hΛan c) ha.symm).comp hmap
    have htb := (tendsto_sub_mul_logDeriv (hΛ₀an c) hb.symm).comp hmap
    have hdiv : Tendsto (fun σ : ℝ => ((σ : ℂ) - c) * (1 / (σ : ℂ))) (𝓝[>] c) (𝓝 0) := by
      have h : ContinuousAt (fun σ : ℝ => ((σ : ℂ) - c) * (1 / (σ : ℂ))) c := by
        have hc0' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
        exact ((Complex.continuous_ofReal.continuousAt).sub continuousAt_const).mul
          (continuousAt_const.div Complex.continuous_ofReal.continuousAt hc0')
      have h' := h.tendsto
      simp only [sub_self, zero_mul] at h'
      exact h'.mono_left nhdsWithin_le_nhds
    have hEt : Tendsto (fun σ : ℝ => ((σ : ℂ) - c) * E σ) (𝓝[>] c) (𝓝 0) := by
      have hEc : ContinuousAt E (c : ℂ) :=
        ((hE.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)) _
          (by simpa using hcE)).continuousAt
      have h : ContinuousAt (fun σ : ℝ => ((σ : ℂ) - c) * E σ) c :=
        ((Complex.continuous_ofReal.continuousAt).sub continuousAt_const).mul
          (hEc.comp Complex.continuous_ofReal.continuousAt)
      have h' := h.tendsto
      simp only [sub_self, zero_mul] at h'
      exact h'.mono_left nhdsWithin_le_nhds
    have hsum := ((htb.sub hta).add hdiv).sub hEt
    rw [add_zero, sub_zero] at hsum
    have hre := (Complex.continuous_re.tendsto _).comp hsum
    simp only [Function.comp_def, Complex.sub_re, Complex.natCast_re] at hre
    refine sub_nonneg.mp (ge_of_tendsto hre ?_)
    filter_upwards [Ioo_mem_nhdsGT (show c < c + δ by linarith)] with σ hσ
    obtain ⟨hL, -, -⟩ := hseg σ hσ.1 hσ.2
    have heq : ((σ : ℂ) - c) * logDeriv Λ₀ (σ : ℂ) - ((σ : ℂ) - c) * logDeriv Λ (σ : ℂ) +
        ((σ : ℂ) - c) * (1 / (σ : ℂ)) - ((σ : ℂ) - c) * E σ =
          (((σ - c) * laplaceReal ν' σ : ℝ) : ℂ) := by
      push_cast; rw [← hL]; ring
    rw [← Complex.sub_re, heq, Complex.ofReal_re]
    refine mul_nonneg (by linarith [hσ.1]) ?_
    exact setIntegral_nonneg measurableSet_Ioi fun u _ => (Real.exp_pos _).le
  have hlt : a < b := by
    have : (a : ℝ) < b := lt_of_le_of_ne hsign (by exact_mod_cast hab)
    exact_mod_cast this
  refine ⟨by
    by_contra hnz
    have h0 := ((hΛ₀an c).analyticOrderAt_eq_zero.mpr hnz)
    rw [h0] at hb
    exact absurd hb (by exact_mod_cast (show b ≠ 0 by omega)), ?_⟩
  rw [← ha, ← hb, ENat.toNat_coe, ENat.toNat_coe]
  exact hlt

end GaloisForLFunctions.BiarithmeticGaugeGeometry
