import GaloisForLFunctions.RHTower.OneSignTailImpossible
import Mathlib.Analysis.Meromorphic.Order

/-!
# Meromorphic Laplace poles separate source tails

Landau continuation of the literal positive tail retains its compact head.
Local analyticity along the real axis fixes the tail abscissa; meromorphic
identity propagation then contradicts any surviving pole in that half-plane.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower (tailMeasure complexLaplace hasDerivAt_complexLaplace
  complexLaplace_ofReal false_of_analyticAt_abscissa headLaplace)
namespace RHTower

/-- A real-analytic meromorphic Laplace continuation with a nonreal pole excludes an eventually nonnegative source. -/
theorem no_oneSign_tail_of_meromorphic_pole
    {g : ℝ → ℝ} (hgc : Continuous g) {G : ℂ → ℂ}
    (hgi : ∀ σ : ℝ, 3 / 2 < σ →
      IntegrableOn (fun u : ℝ => g u * Real.exp (-σ * u)) (Ioi 0))
    (htrans : ∀ σ : ℝ, 3 / 2 < σ →
      ((∫ u in Ioi (0 : ℝ), g u * Real.exp (-σ * u) : ℝ) : ℂ) = G (σ : ℂ))
    (hGan : ∀ σ : ℝ, 1 / 4 < σ → AnalyticAt ℂ G (σ : ℂ))
    (hGm : MeromorphicOn G {s : ℂ | 1 / 4 < s.re})
    {p : ℂ} (hp : 1 / 4 < p.re) (hpo : meromorphicOrderAt G p < 0) :
    ¬ ∃ H : ℝ, 0 ≤ H ∧ ∀ u : ℝ, H < u → 0 ≤ g u := by
  rintro ⟨H, hH, htail⟩
  have hpos : ∀ u : ℝ, 0 < u → 0 ≤ g (H + u) :=
    fun u hu => htail _ (by linarith)
  obtain ⟨c, hc, hc4, _⟩ := exists_isAbscissa_tail hgc hH hgi hpos
  let ν : Measure ℝ := tailMeasure g H
  have hΦan : ∀ σ : ℝ, 1 / 4 < σ →
      AnalyticAt ℂ (tailTransform g G H) (σ : ℂ) := by
    intro σ hσ
    apply analyticAt_tailTransform hgc hH _ (hGan σ hσ)
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
    linarith
  have hCLan : ∀ z : ℂ, c < z.re → AnalyticAt ℂ (complexLaplace ν) z := by
    intro z hz
    have hopen : IsOpen {w : ℂ | c < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hd : DifferentiableOn ℂ (complexLaplace ν) {w : ℂ | c < w.re} :=
      fun w hw => ((hasDerivAt_complexLaplace hc hw).differentiableAt).differentiableWithinAt
    exact hd.analyticAt (hopen.mem_nhds hz)
  have hray : ∀ σ : ℝ, c < σ →
      tailTransform g G H (σ : ℂ) = complexLaplace ν (σ : ℂ) := by
    have h1 : AnalyticOnNhd ℝ (fun t : ℝ => tailTransform g G H (t : ℂ)) (Ioi c) :=
      fun t ht => analyticAt_ofReal_comp (hΦan t (hc4.trans_lt ht))
    have h2 : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace ν (t : ℂ)) (Ioi c) :=
      fun t ht => analyticAt_ofReal_comp (hCLan _ (by simpa using ht))
    let z₀ : ℝ := max 2 c + 1
    have hz₀c : c < z₀ := by dsimp [z₀]; linarith [le_max_right 2 c]
    have hz₀big : 3 / 2 < z₀ := by dsimp [z₀]; linarith [le_max_left 2 c]
    have hev : (fun t : ℝ => tailTransform g G H (t : ℂ)) =ᶠ[𝓝 z₀]
        fun t : ℝ => complexLaplace ν (t : ℂ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz₀big] with t ht
      change 3 / 2 < t at ht
      rw [tailTransform_ofReal hgc hH (by linarith) (hgi t ht) hpos (htrans t ht),
        complexLaplace_ofReal]
    exact fun σ hσ => h1.eqOn_of_preconnected_of_eventuallyEq h2
      isPreconnected_Ioi hz₀c hev hσ
  have hceq : c = 1 / 4 := by
    by_contra hne
    have hcgt : 1 / 4 < c := lt_of_le_of_ne hc4 (Ne.symm hne)
    obtain ⟨δ, hδ, hball⟩ := (hΦan c hcgt).exists_ball_analyticOnNhd
    exact false_of_analyticAt_abscissa hc hδ hball
      (fun σ hσ _ => by rw [hray σ hσ, complexLaplace_ofReal])
  subst hceq
  let Ψ : ℂ → ℂ := fun s =>
    Complex.exp (-s * (H : ℂ)) * (complexLaplace ν s - 1 / (s - 1 / 4)) +
      headLaplace g H s
  have hΨan : ∀ z : ℂ, 1 / 4 < z.re → AnalyticAt ℂ Ψ z := by
    intro z hz
    have hz4 : z ≠ 1 / 4 := by intro he; rw [he] at hz; norm_num at hz
    have he : AnalyticAt ℂ (fun s : ℂ => Complex.exp (-s * (H : ℂ))) z :=
      ((analyticAt_id.neg).mul analyticAt_const).cexp
    have hd : AnalyticAt ℂ (fun s : ℂ => 1 / (s - 1 / 4)) z :=
      analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hz4)
    exact (he.mul ((hCLan z hz).sub hd)).add (analyticAt_headLaplace hgc hH z)
  have hGΨ : ∀ σ : ℝ, 1 / 4 < σ → G (σ : ℂ) = Ψ (σ : ℂ) := by
    intro σ hσ
    have h := hray σ hσ
    rw [tailTransform] at h
    have he : Complex.exp (-((σ : ℂ)) * (H : ℂ)) *
        Complex.exp ((σ : ℂ) * (H : ℂ)) = 1 := by
      rw [← Complex.exp_add, show -((σ : ℂ)) * (H : ℂ) + (σ : ℂ) * (H : ℂ) = 0 by ring,
        Complex.exp_zero]
    dsimp only [Ψ]
    rw [← h]
    linear_combination (headLaplace g H (σ : ℂ) - G (σ : ℂ)) * he
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] (2 : ℂ), G z = Ψ z := by
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] (2 : ℝ), G (t : ℂ) = Ψ (t : ℂ) := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds
        (show (1 : ℝ) / 4 < 2 by norm_num))] with t ht
      exact hGΨ t ht
    exact (tendsto_ofReal_nhdsNE 2).frequently hev.frequently
  have heq : G =ᶠ[𝓝 (2 : ℂ)] Ψ :=
    ((hGan 2 (by norm_num)).frequently_eq_iff_eventually_eq
      (hΨan 2 (by norm_num))).mp hfreq
  have hsub : MeromorphicOn (G - Ψ) {s : ℂ | 1 / 4 < s.re} :=
    fun s hs => (hGm s hs).sub (hΨan s hs).meromorphicAt
  have htop2 : meromorphicOrderAt (G - Ψ) (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [heq.filter_mono nhdsWithin_le_nhds] with z hz
    exact sub_eq_zero.mpr hz
  have htop : meromorphicOrderAt (G - Ψ) p = ⊤ := by
    by_contra hn
    exact (hsub.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_halfSpace_re_gt (1 / 4)).isPreconnected hp
      (by norm_num : (1 : ℝ) / 4 < (2 : ℂ).re) hn) htop2
  have hlocal : G =ᶠ[𝓝[≠] p] Ψ := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp htop] with z hz
    exact sub_eq_zero.mp hz
  have hord := meromorphicOrderAt_congr hlocal
  exact (not_lt_of_ge ((hΨan p hp).meromorphicOrderAt_nonneg)) (hord ▸ hpo)

end RHTower
