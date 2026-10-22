import GaloisForLFunctions.RHTower.Suzuki.SuzukiTailTransform
import GaloisForLFunctions.RHTower.LandauSingularAtAbscissa
import GaloisForLFunctions.HTGeometry.ConvexDiffCountableConnected

/-!
# No profile with a completed double pole can keep one sign

If a profile whose Laplace transform continues to a function with a genuine double pole above a Xi
zero were eventually of one sign, its thickened tail would be a nonnegative carrier whose abscissa
Landau's theorem places at a real singularity of the continuation.  The completed Xi has no real
zero, so the only surviving candidate is the reference abscissa `1/4`; but then the carrier's
transform is holomorphic across the whole half-plane `Re s > 1/4`, and the identity theorem carries
that holomorphy onto the continuation at the double pole.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal
open GaloisForLFunctions.RHTower (laplaceReal laplaceMass complexLaplace IsAbscissa tailCarrier
  tailMeasure headLaplace complexLaplace_ofReal hasDerivAt_complexLaplace
  false_of_analyticAt_abscissa)
open GaloisForLFunctions.HTGeometry (isPreconnected_diff_of_countable_of_convex_complex)

noncomputable section

namespace RHTower

/-- A holomorphic function restricts to a real-analytic one on the real axis. -/
theorem analyticAt_ofReal_comp {f : ℂ → ℂ} {σ : ℝ} (hf : AnalyticAt ℂ f ((σ : ℂ))) :
    AnalyticAt ℝ (fun t : ℝ => f ((t : ℂ))) σ := by
  have h1 : AnalyticAt ℝ f ((σ : ℂ)) := hf.restrictScalars
  have h2 : AnalyticAt ℝ (fun t : ℝ => ((t : ℂ))) σ := Complex.ofRealCLM.analyticAt σ
  exact AnalyticAt.comp (x := σ) (g := f) (f := fun t : ℝ => ((t : ℂ))) h1 h2

/-- The real axis accumulates at each of its points inside the plane. -/
theorem tendsto_ofReal_nhdsNE (a : ℝ) :
    Filter.Tendsto (fun t : ℝ => ((t : ℂ))) (𝓝[≠] a) (𝓝[≠] ((a : ℂ))) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact Filter.Tendsto.mono_left (Complex.continuous_ofReal.tendsto a) nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [mem_compl_iff, mem_singleton_iff] at ht ⊢
    exact fun h => ht (Complex.ofReal_inj.mp h)

theorem countable_shifted_xi_zeroSet :
    {s : ℂ | xi (s - 1 / 2) = 0}.Countable := by
  have hinj : Function.Injective (fun s : ℂ => s - 1 / 2) := fun a b h => sub_left_inj.mp h
  exact xi_zeroSet_countable.preimage hinj

/-- **No one-sign tail.**  A profile whose transform continues with a genuine double pole above a
Xi zero cannot be eventually nonnegative. -/
theorem no_oneSign_tail {g : ℝ → ℝ} (hgc : Continuous g) {Gc : ℂ → ℂ}
    (hgi : ∀ σ : ℝ, 3 / 2 < σ → IntegrableOn (fun L : ℝ => g L * Real.exp (-σ * L)) (Ioi 0))
    (htrans : ∀ σ : ℝ, 3 / 2 < σ →
      ((∫ L in Ioi (0 : ℝ), g L * Real.exp (-σ * L) : ℝ) : ℂ) = Gc ((σ : ℂ)))
    (hGan : ∀ z : ℂ, 1 / 4 < z.re → xi (z - 1 / 2) ≠ 0 → AnalyticAt ℂ Gc z)
    {p : ℂ} (hp : 1 / 4 < p.re)
    (hporder : meromorphicOrderAt Gc p = ((-2 : ℤ) : WithTop ℤ)) :
    ¬ ∃ H : ℝ, 0 ≤ H ∧ ∀ L : ℝ, H < L → 0 ≤ g L := by
  rintro ⟨H, hH, hTpos⟩
  have hpos : ∀ u : ℝ, 0 < u → 0 ≤ g (H + u) := fun u hu => hTpos (H + u) (by linarith)
  obtain ⟨c, hc, hc4, hc32⟩ := exists_isAbscissa_tail hgc hH hgi hpos
  set ν : Measure ℝ := tailMeasure g H with hνdef
  -- the tail transform is analytic at every real point right of `1/4`
  have hΦan : ∀ σ : ℝ, 1 / 4 < σ → AnalyticAt ℂ (tailTransform g Gc H) ((σ : ℂ)) := by
    intro σ hσ
    refine analyticAt_tailTransform hgc hH ?_ ?_
    · intro hcon
      have hre : ((σ : ℂ)).re = ((1 : ℂ) / 4).re := by rw [hcon]
      simp only [Complex.ofReal_re] at hre
      norm_num at hre
      linarith
    · refine hGan _ (by simpa using hσ) ?_
      have hcast : ((σ : ℂ)) - 1 / 2 = (((σ - 1 / 2 : ℝ)) : ℂ) := by push_cast; ring
      rw [hcast]
      exact xi_ne_zero_of_real _
  -- the complex transform is holomorphic right of the abscissa
  have hCLan : ∀ z : ℂ, c < z.re → AnalyticAt ℂ (complexLaplace ν) z := by
    intro z hz
    have hopen : IsOpen {w : ℂ | c < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hdiff : DifferentiableOn ℂ (complexLaplace ν) {w : ℂ | c < w.re} := fun w hw =>
      ((hasDerivAt_complexLaplace hc hw).differentiableAt).differentiableWithinAt
    exact hdiff.analyticAt (hopen.mem_nhds hz)
  -- the two agree on the whole ray right of the abscissa
  have hray : ∀ σ : ℝ, c < σ → tailTransform g Gc H ((σ : ℂ)) = complexLaplace ν ((σ : ℂ)) := by
    have h1 : AnalyticOnNhd ℝ (fun t : ℝ => tailTransform g Gc H ((t : ℂ))) (Ioi c) := by
      intro t ht
      exact analyticAt_ofReal_comp (hΦan t (lt_of_le_of_lt hc4 ht))
    have h2 : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace ν ((t : ℂ))) (Ioi c) := by
      intro t ht
      exact analyticAt_ofReal_comp (hCLan _ (by simpa using ht))
    set z₀ : ℝ := max 2 c + 1 with hz₀def
    have hz₀c : c < z₀ := by
      have : c ≤ max 2 c := le_max_right _ _
      linarith
    have hz₀big : (3 : ℝ) / 2 < z₀ := by
      have : (2 : ℝ) ≤ max 2 c := le_max_left _ _
      linarith
    have hev : (fun t : ℝ => tailTransform g Gc H ((t : ℂ)))
        =ᶠ[nhds z₀] fun t : ℝ => complexLaplace ν ((t : ℂ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds (show z₀ ∈ Ioi ((3 : ℝ) / 2) from hz₀big)] with t ht
      have hgt : (3 : ℝ) / 2 < t := ht
      rw [tailTransform_ofReal hgc hH (by linarith) (hgi t hgt) hpos (htrans t hgt),
        complexLaplace_ofReal]
    have heq := h1.eqOn_of_preconnected_of_eventuallyEq h2 isPreconnected_Ioi hz₀c hev
    intro σ hσ
    exact heq hσ
  -- Landau: the abscissa must be the reference one
  have hceq : c = 1 / 4 := by
    by_contra hne
    have hcgt : 1 / 4 < c := lt_of_le_of_ne hc4 (Ne.symm hne)
    have hxic : xi (((c : ℂ)) - 1 / 2) ≠ 0 := by
      have hcast : ((c : ℂ)) - 1 / 2 = (((c - 1 / 2 : ℝ)) : ℂ) := by push_cast; ring
      rw [hcast]
      exact xi_ne_zero_of_real _
    have hopenxi : IsOpen {w : ℂ | xi w ≠ 0} :=
      isOpen_compl_singleton.preimage (xi_differentiable.continuous)
    obtain ⟨δ₁, hδ₁, hsub⟩ := Metric.isOpen_iff.mp hopenxi _ hxic
    set δ : ℝ := min δ₁ (c - 1 / 4) with hδdef
    have hδpos : 0 < δ := lt_min hδ₁ (by linarith)
    refine false_of_analyticAt_abscissa (Φ := tailTransform g Gc H) hc hδpos ?_ ?_
    · intro z hz
      have hdist : dist z ((c : ℂ)) < δ := Metric.mem_ball.mp hz
      have hre : |z.re - c| < δ := by
        have h1 : |z.re - ((c : ℂ)).re| ≤ ‖z - ((c : ℂ))‖ := by
          have := Complex.abs_re_le_norm (z - ((c : ℂ)))
          simpa using this
        have h2 : ‖z - ((c : ℂ))‖ < δ := by
          rw [← Complex.dist_eq]
          exact hdist
        simpa using lt_of_le_of_lt h1 h2
      have hzre : 1 / 4 < z.re := by
        have hlt : δ ≤ c - 1 / 4 := min_le_right _ _
        have := abs_lt.mp hre
        linarith [this.1]
      have hz4 : z ≠ 1 / 4 := by
        intro hcon
        rw [hcon] at hzre
        norm_num at hzre
      refine analyticAt_tailTransform hgc hH hz4 (hGan z hzre ?_)
      refine hsub (Metric.mem_ball.mpr ?_)
      have : dist (z - 1 / 2) (((c : ℂ)) - 1 / 2) = dist z ((c : ℂ)) := by
        rw [Complex.dist_eq, Complex.dist_eq]
        congr 1
        ring
      rw [this]
      exact lt_of_lt_of_le hdist (min_le_left _ _)
    · intro σ h1 _
      rw [hray σ h1, complexLaplace_ofReal]
  subst hceq
  -- the tail transform is now holomorphic across the whole half-plane
  set Psi : ℂ → ℂ := fun s : ℂ =>
    Complex.exp (-s * (H : ℂ)) * (complexLaplace ν s - 1 / (s - 1 / 4))
      + headLaplace g H s with hPsidef
  have hPsian : ∀ z : ℂ, 1 / 4 < z.re → AnalyticAt ℂ Psi z := by
    intro z hz
    have hz4 : z ≠ 1 / 4 := by
      intro hcon
      rw [hcon] at hz
      norm_num at hz
    have hexp : AnalyticAt ℂ (fun s : ℂ => Complex.exp (-s * (H : ℂ))) z :=
      ((analyticAt_id.neg).mul analyticAt_const).cexp
    have hpole : AnalyticAt ℂ (fun s : ℂ => 1 / (s - 1 / 4)) z :=
      analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hz4)
    rw [hPsidef]
    exact (hexp.mul ((hCLan z hz).sub hpole)).add (analyticAt_headLaplace hgc hH z)
  have hGPsi : ∀ σ : ℝ, 1 / 4 < σ → Gc ((σ : ℂ)) = Psi ((σ : ℂ)) := by
    intro σ hσ
    have h := hray σ hσ
    rw [tailTransform] at h
    have hEE : Complex.exp (-((σ : ℂ)) * (H : ℂ)) * Complex.exp (((σ : ℂ)) * (H : ℂ)) = 1 := by
      rw [← Complex.exp_add, show -((σ : ℂ)) * (H : ℂ) + ((σ : ℂ)) * (H : ℂ) = 0 by ring,
        Complex.exp_zero]
    rw [hPsidef]
    simp only
    rw [← h]
    linear_combination (headLaplace g H ((σ : ℂ)) - Gc ((σ : ℂ))) * hEE
  -- the identity theorem on the half-plane minus the divisor
  set W : Set ℂ := {s : ℂ | 1 / 4 < s.re} \ {s : ℂ | xi (s - 1 / 2) = 0} with hWdef
  have h2W : (2 : ℂ) ∈ W := by
    constructor
    · show (1 : ℝ) / 4 < (2 : ℂ).re
      norm_num
    · intro hcon
      have hcast : ((2 : ℂ)) - 1 / 2 = (((3 / 2 : ℝ)) : ℂ) := by push_cast; ring
      rw [Set.mem_setOf_eq, hcast] at hcon
      exact xi_ne_zero_of_real _ hcon
  have hWopen : IsOpen W := by
    refine IsOpen.sdiff (isOpen_lt continuous_const Complex.continuous_re) ?_
    refine IsClosed.preimage ?_ (isClosed_singleton (x := (0 : ℂ)))
    exact (xi_differentiable.continuous.comp (by fun_prop))
  have hWconn : IsPreconnected W :=
    isPreconnected_diff_of_countable_of_convex_complex (convex_halfSpace_re_gt _)
      (isOpen_lt continuous_const Complex.continuous_re) countable_shifted_xi_zeroSet h2W
  have hGW : AnalyticOnNhd ℂ Gc W := fun z hz => hGan z hz.1 hz.2
  have hPsiW : AnalyticOnNhd ℂ Psi W := fun z hz => hPsian z hz.1
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] ((2 : ℂ)), Gc z = Psi z := by
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] (2 : ℝ), Gc ((t : ℂ)) = Psi ((t : ℂ)) := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds
        (show (2 : ℝ) ∈ Ioi ((1 : ℝ) / 4) by norm_num))] with t ht
      exact hGPsi t ht
    have hcast : ((2 : ℂ)) = (((2 : ℝ)) : ℂ) := by norm_num
    rw [hcast]
    exact (tendsto_ofReal_nhdsNE 2).frequently hev.frequently
  have hEqOn := hGW.eqOn_of_preconnected_of_frequently_eq hPsiW hWconn h2W hfreq
  -- transfer the order at the double pole
  have hxiAn : AnalyticAt ℂ (fun s : ℂ => xi (s - 1 / 2)) p :=
    AnalyticAt.comp (x := p) (g := xi) (f := fun s : ℂ => s - 1 / 2)
      (analyticAt_xi _) (analyticAt_id.sub analyticAt_const)
  have hnear : ∀ᶠ s : ℂ in 𝓝[≠] p, s ∈ W := by
    rcases hxiAn.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exfalso
      have htend : Filter.Tendsto (fun w : ℂ => w + 1 / 2) (nhds (p - 1 / 2)) (nhds p) := by
        have hcont : Continuous fun w : ℂ => w + 1 / 2 := by fun_prop
        have h2 := hcont.tendsto (p - 1 / 2)
        simpa using h2
      have hev : ∀ᶠ w : ℂ in nhds (p - 1 / 2), xi w = 0 := by
        have h3 := htend.eventually hzero
        filter_upwards [h3] with w hw
        simpa using hw
      have hcon := xi_orderAt_ne_top (p - 1 / 2)
      exact hcon (analyticOrderAt_eq_top.mpr hev)
    · have hre : ∀ᶠ s : ℂ in 𝓝[≠] p, 1 / 4 < s.re :=
        nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp)
      filter_upwards [hre, hne] with s h1 h2
      exact ⟨h1, h2⟩
  have hEv : Gc =ᶠ[𝓝[≠] p] Psi := by
    filter_upwards [hnear] with s hs
    exact hEqOn hs
  have hord : meromorphicOrderAt Gc p = meromorphicOrderAt Psi p := meromorphicOrderAt_congr hEv
  rw [hporder] at hord
  exact analytic_meromorphicOrderAt_ne_neg_two (hPsian p hp) hord.symm

end RHTower
