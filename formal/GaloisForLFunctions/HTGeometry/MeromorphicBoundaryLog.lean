import GaloisForLFunctions.HTGeometry.HelsonLogTailSum

/-!
# A continuable exponential has at most a logarithmic boundary singularity

Suppose `F` is meromorphic on the whole plane, `E` is holomorphic on the open half plane
`Re s > 1/2`, and `F = exp E` on `Re s > 1`.  Then the identity theorem forces `F = exp E`
throughout `Re s > 1/2` — in particular `F` has neither zero nor pole there — and the meromorphic
normal form of `F` at the boundary point `1/2` gives an integer `m` with

```text
| Re E(σ) - m log(σ - 1/2) |  ≤  B          on some interval (1/2, 1/2 + δ).
```

That is the only trace of continuation which survives at the boundary, and it is exactly what the
Helson seam argument has to contradict: `Re E` is `Re(∑_p χ(p) p^{-s})` plus a bounded remainder,
and a random Dirichlet series with independent coefficients is not confined to a logarithmic
envelope.

The proof compares two local models of `F`: the exponential model, valid on a punctured
neighbourhood of every interior point by the identity theorem, and the normal form
`(s - 1/2)^m · g(s)` at the boundary point.  Both are continuous on the open half disc, so they
agree there, not merely off a discrete set.
-/

noncomputable section

open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

theorem convex_halfPlane_re_gt (x : ℝ) : Convex ℝ {s : ℂ | x < s.re} :=
  convex_halfSpace_gt ⟨fun _ _ => rfl, fun c z => by simp⟩ x

theorem isOpen_halfPlane_re_gt (x : ℝ) : IsOpen {s : ℂ | x < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem isConnected_halfPlane_re_gt (x : ℝ) : IsConnected {s : ℂ | x < s.re} :=
  ⟨⟨((x + 1 : ℝ) : ℂ), by simp⟩, (convex_halfPlane_re_gt x).isPreconnected⟩

/-- **The identity theorem in the half plane.**  A meromorphic function agreeing with a
nonvanishing holomorphic function on `Re s > 1` agrees with it on a punctured neighbourhood of
every point of `Re s > 1/2`. -/
theorem eventuallyEq_of_eq_on_abscissa {F Φ : ℂ → ℂ}
    (hF : MeromorphicOn F Set.univ)
    (hΦ : AnalyticOnNhd ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (heq : ∀ s : ℂ, 1 < s.re → F s = Φ s) :
    ∀ z ∈ {s : ℂ | 1 / 2 < s.re}, F =ᶠ[𝓝[≠] z] Φ := by
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hUdef
  have hUconn : IsConnected U := isConnected_halfPlane_re_gt _
  have hFU : MeromorphicOn F U := fun x _ => hF x (Set.mem_univ x)
  have hW : MeromorphicOn (F - Φ) U := hFU.sub hΦ.meromorphicOn
  have hz0 : (2 : ℂ) ∈ U := by
    simp only [hUdef, Set.mem_setOf_eq]
    norm_num
  have hWtop0 : meromorphicOrderAt (F - Φ) (2 : ℂ) = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hnbhd : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_halfPlane_re_gt 1).mem_nhds (by simp only [Set.mem_setOf_eq]; norm_num)
    filter_upwards [nhdsWithin_le_nhds hnbhd] with w hw
    show F w - Φ w = 0
    rw [heq w hw, sub_self]
  have hall : ∀ z ∈ U, meromorphicOrderAt (F - Φ) z = ⊤ := by
    by_contra hc
    push Not at hc
    obtain ⟨z, hzU, hzne⟩ := hc
    exact ((hW.exists_meromorphicOrderAt_ne_top_iff_forall hUconn).mp
      ⟨⟨z, hzU⟩, hzne⟩ ⟨2, hz0⟩) hWtop0
  intro z hz
  have h := meromorphicOrderAt_eq_top_iff.mp (hall z hz)
  filter_upwards [h] with w hw
  have hw' : F w - Φ w = 0 := hw
  exact sub_eq_zero.mp hw'


/-- **The boundary logarithmic envelope.** -/
theorem exists_boundary_log_bound {F E : ℂ → ℂ}
    (hF : MeromorphicOn F Set.univ)
    (hE : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re})
    (heq : ∀ s : ℂ, 1 < s.re → F s = Complex.exp (E s)) :
    ∃ (m : ℤ) (δ B : ℝ), 0 < δ ∧ ∀ σ : ℝ, 1 / 2 < σ → σ < 1 / 2 + δ →
      |(E (σ : ℂ)).re - (m : ℝ) * Real.log (σ - 1 / 2)| ≤ B := by
  classical
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hUdef
  have hUopen : IsOpen U := isOpen_halfPlane_re_gt _
  set Φ : ℂ → ℂ := fun s => Complex.exp (E s) with hΦdef
  have hΦdiff : DifferentiableOn ℂ Φ U := Complex.differentiable_exp.comp_differentiableOn hE
  have hΦan : AnalyticOnNhd ℂ Φ U := hΦdiff.analyticOnNhd hUopen
  have hΦne : ∀ w : ℂ, Φ w ≠ 0 := fun w => Complex.exp_ne_zero _
  have hFeq : ∀ z ∈ U, F =ᶠ[𝓝[≠] z] Φ := eventuallyEq_of_eq_on_abscissa hF hΦan heq
  -- the boundary point has finite order
  have hFmero : MeromorphicAt F (1 / 2 : ℂ) := hF _ (Set.mem_univ _)
  have hFord : meromorphicOrderAt F (1 / 2 : ℂ) ≠ ⊤ := by
    intro htop
    rw [meromorphicOrderAt_eq_top_iff] at htop
    obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp htop
    set z : ℂ := ((1 / 2 + ρ / 2 : ℝ) : ℂ) with hzdef
    have hzre : z.re = 1 / 2 + ρ / 2 := by rw [hzdef, Complex.ofReal_re]
    have hzU : z ∈ U := by
      simp only [hUdef, Set.mem_setOf_eq, hzre]
      linarith
    have hzdist : dist z (1 / 2 : ℂ) = ρ / 2 := by
      rw [Complex.dist_eq, hzdef]
      have : ((1 / 2 + ρ / 2 : ℝ) : ℂ) - (1 / 2 : ℂ) = ((ρ / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    set V : Set ℂ := Metric.ball (1 / 2 : ℂ) ρ ∩ {(1 / 2 : ℂ)}ᶜ with hVdef
    have hVopen : IsOpen V := Metric.isOpen_ball.inter (isOpen_compl_singleton)
    have hzV : z ∈ V := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, hzdist]; linarith
      · intro hc
        rw [Set.mem_singleton_iff] at hc
        rw [hc, dist_self] at hzdist
        linarith
    have hFzero : ∀ᶠ w in 𝓝[≠] z, F w = 0 := by
      filter_upwards [nhdsWithin_le_nhds (hVopen.mem_nhds hzV)] with w hw
      exact hsub hw
    have hΦzero : ∀ᶠ w in 𝓝[≠] z, Φ w = 0 := by
      filter_upwards [(hFeq z hzU).symm, hFzero] with w h1 h2
      exact h1.trans h2
    obtain ⟨w, hw⟩ := hΦzero.exists
    exact hΦne w hw
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hFord
  obtain ⟨g, hgan, hgne, hgeq⟩ := (meromorphicOrderAt_eq_int_iff hFmero).mp hm.symm
  -- a ball on which the normal form and the analyticity of `g` are both available
  obtain ⟨ρ₁, hρ₁, hsub₁⟩ := Metric.mem_nhdsWithin_iff.mp hgeq
  obtain ⟨ρ₂, hρ₂, hsub₂⟩ := Metric.mem_nhds_iff.mp hgan.eventually_analyticAt
  set c : ℝ := ‖g (1 / 2 : ℂ)‖ with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact norm_pos_iff.mpr hgne
  have hnormcont : ContinuousAt (fun w : ℂ => ‖g w‖) (1 / 2 : ℂ) := hgan.continuousAt.norm
  obtain ⟨ρ₃, hρ₃, hsub₃⟩ := Metric.mem_nhds_iff.mp
    (hnormcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds
      (show c ∈ Set.Ioo (c / 2) (3 * c / 2) from ⟨by linarith, by linarith⟩)))
  -- the common radius
  set ρ₀ : ℝ := min ρ₁ (min ρ₂ ρ₃) with hρ₀def
  have hρ₀ : 0 < ρ₀ := by
    rw [hρ₀def]
    exact lt_min hρ₁ (lt_min hρ₂ hρ₃)
  refine ⟨m, ρ₀ / 2, |Real.log (c / 2)| + |Real.log (3 * c / 2)|, by linarith, ?_⟩
  intro σ hσ1 hσ2
  set z : ℂ := ((σ : ℝ) : ℂ) with hzdef
  have hzre : z.re = σ := by rw [hzdef, Complex.ofReal_re]
  have hzU : z ∈ U := by
    simp only [hUdef, Set.mem_setOf_eq, hzre]
    exact hσ1
  have hzsub : z - (1 / 2 : ℂ) = ((σ - 1 / 2 : ℝ) : ℂ) := by
    rw [hzdef]
    push_cast
    ring
  have hzdist : dist z (1 / 2 : ℂ) = σ - 1 / 2 := by
    rw [Complex.dist_eq, hzsub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hzball : dist z (1 / 2 : ℂ) < ρ₀ := by rw [hzdist]; linarith
  have hzne : z ≠ (1 / 2 : ℂ) := by
    intro hc
    rw [hc, dist_self] at hzdist
    linarith
  -- the normal form holds on a neighbourhood of `z`
  set V : Set ℂ := Metric.ball (1 / 2 : ℂ) ρ₀ ∩ {(1 / 2 : ℂ)}ᶜ with hVdef
  have hVopen : IsOpen V := Metric.isOpen_ball.inter isOpen_compl_singleton
  have hzV : z ∈ V := ⟨Metric.mem_ball.mpr hzball, hzne⟩
  set Ψ : ℂ → ℂ := fun w => (w - (1 / 2 : ℂ)) ^ m * g w with hΨdef
  have hFΨ : ∀ w ∈ V, F w = Ψ w := by
    intro w hw
    have hmem : w ∈ Metric.ball (1 / 2 : ℂ) ρ₁ ∩ {(1 / 2 : ℂ)}ᶜ := by
      refine ⟨?_, hw.2⟩
      exact Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hw.1) (min_le_left _ _))
    have := hsub₁ hmem
    rw [hΨdef]
    simpa [smul_eq_mul] using this
  -- the two local models agree at `z`
  have hΦΨ : Φ =ᶠ[𝓝[≠] z] Ψ := by
    filter_upwards [(hFeq z hzU).symm,
      nhdsWithin_le_nhds (hVopen.mem_nhds hzV)] with w h1 h2
    exact h1.trans (hFΨ w h2)
  have hgcont : ContinuousAt g z := by
    have hzball₂ : z ∈ Metric.ball (1 / 2 : ℂ) ρ₂ :=
      Metric.mem_ball.mpr (lt_of_lt_of_le hzball
        (le_trans (min_le_right _ _) (min_le_left _ _)))
    exact (hsub₂ hzball₂).continuousAt
  have hΨcont : ContinuousAt Ψ z := by
    rw [hΨdef]
    refine ContinuousAt.mul ?_ hgcont
    exact (continuousAt_id.sub continuousAt_const).zpow₀ m
      (Or.inl (sub_ne_zero.mpr hzne))
  have hΦcont : ContinuousAt Φ z :=
    (hΦdiff.differentiableAt (hUopen.mem_nhds hzU)).continuousAt
  have hvalue : Φ z = Ψ z := by
    have h1 : Filter.Tendsto Φ (𝓝[≠] z) (𝓝 (Φ z)) :=
      hΦcont.continuousWithinAt.tendsto
    have h2 : Filter.Tendsto Ψ (𝓝[≠] z) (𝓝 (Ψ z)) :=
      hΨcont.continuousWithinAt.tendsto
    exact tendsto_nhds_unique (h1.congr' hΦΨ) h2
  -- read off the modulus
  have hnormΦ : ‖Φ z‖ = Real.exp ((E z).re) := by
    rw [hΦdef]
    exact Complex.norm_exp _
  have hnormΨ : ‖Ψ z‖ = (σ - 1 / 2) ^ m * ‖g z‖ := by
    rw [hΨdef]
    simp only [norm_mul, norm_zpow, hzsub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ σ - 1 / 2)]
  have hpos : (0:ℝ) < σ - 1 / 2 := by linarith
  have hgz : ‖g z‖ ∈ Set.Ioo (c / 2) (3 * c / 2) := by
    refine hsub₃ ?_
    exact Metric.mem_ball.mpr (lt_of_lt_of_le hzball
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hgzpos : 0 < ‖g z‖ := lt_trans (by linarith) hgz.1
  have hkey : (E z).re = (m : ℝ) * Real.log (σ - 1 / 2) + Real.log ‖g z‖ := by
    have hval : Real.exp ((E z).re) = (σ - 1 / 2) ^ m * ‖g z‖ := by
      rw [← hnormΦ, ← hnormΨ, hvalue]
    have hlog := congrArg Real.log hval
    rw [Real.log_exp, Real.log_mul (by positivity) (ne_of_gt hgzpos), Real.log_zpow] at hlog
    exact hlog
  rw [hkey]
  have hsimp : (m : ℝ) * Real.log (σ - 1 / 2) + Real.log ‖g z‖
      - (m : ℝ) * Real.log (σ - 1 / 2) = Real.log ‖g z‖ := by ring
  rw [hsimp]
  have hlow : Real.log (c / 2) ≤ Real.log ‖g z‖ :=
    Real.log_le_log (by linarith) hgz.1.le
  have hhigh : Real.log ‖g z‖ ≤ Real.log (3 * c / 2) :=
    Real.log_le_log hgzpos hgz.2.le
  have h1 : -|Real.log (c / 2)| ≤ Real.log (c / 2) := neg_abs_le _
  have h2 : Real.log (3 * c / 2) ≤ |Real.log (3 * c / 2)| := le_abs_self _
  rw [abs_le]
  constructor
  · have : (0:ℝ) ≤ |Real.log (3 * c / 2)| := abs_nonneg _
    linarith
  · have : (0:ℝ) ≤ |Real.log (c / 2)| := abs_nonneg _
    linarith

end GaloisForLFunctions.HTGeometry

end
