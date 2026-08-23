import GaloisForLFunctions.RHTower.BurnolResidueSeries
import GaloisForLFunctions.RHTower.SoninMellinInjective
import GaloisForLFunctions.RHTower.SoninRapidMellinDense
import GaloisForLFunctions.RHTower.ZetaRealStrip

/-!
# Completeness of the evaluators for apertures `a > 1`

Burnol's Proposition 6.1 for `a > 1`, without Krein's theorem.  A vector orthogonal to every
evaluator is one whose Mellin transform is divisible by `ζ`; that divisibility is preserved by the
smoothing of Theorem 4.9, because the smoothing acts on the Mellin side as multiplication by an
*entire* multiplier.  So each smoothed vector lies in the dense subspace of Definition 12 and is
still orthogonal to all the evaluators, hence vanishes by Corollary 5.3 and the injectivity of the
Mellin transform; letting the smoothing width tend to `0` gives the vector itself.

For `a = 1` the smoothing leaves `L_1` (every dilation lowers the aperture), which is exactly why
Burnol needs Krein's theorem there.

## Main results

* `extendedMellinContinuation_eq_zero_of_open` — vanishing near one good point forces vanishing.
* `eq_zero_of_zeta_dvd_extendedMellin` — **Proposition 6.1 for `a > 1`**.
-/

open Complex Set Topology Filter MeasureTheory
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## From a neighbourhood to the whole strip -/

/-- A point of the open strip at which `ζ` does not vanish. -/
theorem exists_good_point : ∃ Z : ℂ, 1 / 2 < Z.re ∧ Z.re < 1 ∧ riemannZeta Z ≠ 0 := by
  refine ⟨((3 / 4 : ℝ) : ℂ), by simp; norm_num, by simp; norm_num, ?_⟩
  exact riemannZeta_real_strip_ne_zero (by norm_num) (by norm_num)

/-- If the continued Mellin transform vanishes at every point of a neighbourhood of a good point,
its entire numerator vanishes identically. -/
theorem extendedMellinNumerator_eq_zero_of_eventually {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {Z₀ : ℂ} (hZ₀ : ∀ᶠ Z in 𝓝 Z₀, extendedMellinContinuation a c d f Z = 0)
    (hZ₀0 : Z₀ ≠ 0) (hZ₀1 : Z₀ ≠ 1) (s : ℂ) :
    extendedMellinNumerator a c d f s = 0 := by
  have hnum := (differentiable_extendedMellinNumerator ha hev hc hd).1
  have hA : AnalyticOnNhd ℂ (extendedMellinNumerator a c d f) univ :=
    hnum.differentiableOn.analyticOnNhd isOpen_univ
  have hB : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) univ := by
    intro z _
    exact analyticAt_const
  have hev₀ : extendedMellinNumerator a c d f =ᶠ[𝓝 Z₀] fun _ : ℂ => (0 : ℂ) := by
    have hne0 : ∀ᶠ Z in 𝓝 Z₀, Z ≠ 0 :=
      ContinuousAt.eventually_ne (g := fun z : ℂ => z) continuousAt_id hZ₀0
    have hne1 : ∀ᶠ Z in 𝓝 Z₀, Z ≠ 1 :=
      ContinuousAt.eventually_ne (g := fun z : ℂ => z) continuousAt_id hZ₀1
    filter_upwards [hZ₀, hne0, hne1] with Z hZ h0 h1
    have hden : Z * (1 - Z) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.2 fun h => h1 h.symm)
    have := hZ
    rw [extendedMellinContinuation, div_eq_zero_iff] at this
    rcases this with h | h
    · exact h
    · exact absurd h hden
  exact hA.eqOn_of_preconnected_of_eventuallyEq hB isPreconnected_univ (mem_univ _) hev₀
    (mem_univ s)

/-! ## Proposition 6.1 for `a > 1` -/

/-- **Proposition 6.1 for `a > 1`.**  A vector of `L_b`, `b > 1`, whose continued Mellin transform
is divisible by `ζ` at every nontrivial zero is zero: the evaluators are complete. -/
theorem eq_zero_of_zeta_dvd_extendedMellin {b : ℝ} (hb : 1 < b) {g : SoninL2} {c d : ℂ}
    (hev : g ∈ evenSubspace) (hg : g ∈ centralSoninExtendedCarrier b)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval b →
      ((fourierUnitary g : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (g : ℝ → ℂ) t = d)
    (hdvd : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      meromorphicOrderAt riemannZeta ρ
        ≤ meromorphicOrderAt (extendedMellinContinuation b c d g) ρ) :
    g = 0 := by
  classical
  have hb0 : (0 : ℝ) < b := by linarith
  have hlogb : 0 < Real.log b := Real.log_pos hb
  -- it suffices to bound the norm by every positive number
  have hnorm : ∀ ε : ℝ, 0 < ε → ‖g‖ < ε := by
    intro ε hε
    -- the modulus of strong continuity of the dilation group
    have hcont : Tendsto (fun x : ℝ => ‖rayDilate (Real.exp x) g - g‖) (𝓝 0) (𝓝 0) := by
      have h1 := tendsto_norm_rayDilate_sub_self g
      have h2 : Tendsto (fun x : ℝ => Real.exp x) (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ)) := by
        simpa using (Real.continuous_exp.tendsto (0 : ℝ))
      exact h1.comp h2
    obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.tendsto_nhds_nhds.1 hcont (ε / 2) (by linarith)
    set δ : ℝ := min (δ₀ / 2) (Real.log b) with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]
      exact lt_min (by linarith) hlogb
    have hδlog : δ ≤ Real.log b := by rw [hδdef]; exact min_le_right _ _
    have hexpδ : Real.exp δ ≤ b := by
      have := Real.exp_le_exp.2 hδlog
      rwa [Real.exp_log hb0] at this
    have hmodulus : ∀ x : ℝ, |x| ≤ δ → ‖rayDilate (Real.exp x) g - g‖ ≤ ε / 2 := by
      intro x hx
      have hxd : dist x 0 < δ₀ := by
        rw [Real.dist_eq, sub_zero]
        have : δ ≤ δ₀ / 2 := by rw [hδdef]; exact min_le_left _ _
        linarith
      have := hδ₀ hxd
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
      linarith
    -- the smoothing kernel
    set φ : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, by positivity, by linarith⟩ with hφdef
    set k : ℝ → ℝ := φ.normed (volume : Measure ℝ) with hkdef
    have hkC : ContDiff ℝ (⊤ : ℕ∞) k := φ.contDiff_normed
    have hkcont : Continuous k := hkC.continuous
    have hksupp : ∀ x : ℝ, δ ≤ |x| → k x = 0 := by
      intro x hx
      have hsupp := φ.support_normed_eq (μ := (volume : Measure ℝ))
      have hnot : x ∉ Function.support k := by
        rw [hkdef, hsupp]
        simp only [Metric.mem_ball, Real.dist_eq, sub_zero, not_lt]
        exact hx
      exact Function.notMem_support.1 hnot
    have hks : HasCompactSupport k := hasCompactSupport_of_vanishing hksupp
    have hkint : (∫ x : ℝ, k x) = 1 := φ.integral_normed
    have hkabs : (∫ x : ℝ, |k x|) = 1 := by
      rw [← hkint]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      exact abs_of_nonneg (φ.nonneg_normed x)
    -- the smoothed vector
    set G : SoninL2 := dilationAverage k g with hGdef
    have hmem : ∀ x : ℝ, k x ≠ 0 → rayDilate (Real.exp x) g ∈ centralSoninExtendedCarrier 1 :=
      rayDilate_mem_extended_one hexpδ hksupp hg
    have hGmem : G ∈ centralSoninExtendedCarrier 1 := dilationAverage_mem_extended hkcont hks hmem
    have hGev : G ∈ evenSubspace := dilationAverage_mem_evenSubspace hkcont hks hev
    obtain ⟨c', hc'⟩ := ae_fourier_eq_of_mem_extended hGmem
    obtain ⟨d', hd'⟩ := ae_eq_of_mem_extended hGmem
    have hrapid : HasStripRapidDecrease (extendedMellinContinuation 1 c' d' G) := by
      obtain ⟨c₀, d₀, hc₀, hd₀, hrap⟩ :=
        hasRapidMellin_dilationAverage hkC hδpos hksupp hexpδ hev hg
      have hcc : c₀ = c' := by
        have := hc₀
        have hboth : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval 1 → c₀ = c' := by
          filter_upwards [hc₀, hc'] with u h1 h2 hm
          rw [← h1 hm, ← h2 hm]
        have hmeas : (volume : Measure ℝ) (centralInterval 1) ≠ 0 := by
          rw [centralInterval, Real.volume_Icc]
          norm_num
        by_contra hne
        have : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ centralInterval 1 := by
          filter_upwards [hboth] with u hu hmem
          exact hne (hu hmem)
        rw [MeasureTheory.ae_iff] at this
        simp only [not_not] at this
        exact hmeas this
      have hdd : d₀ = d' := by
        have hboth : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval 1 → d₀ = d' := by
          filter_upwards [hd₀, hd'] with t h1 h2 hm
          rw [← h1 hm, ← h2 hm]
        have hmeas : (volume : Measure ℝ) (centralInterval 1) ≠ 0 := by
          rw [centralInterval, Real.volume_Icc]
          norm_num
        by_contra hne
        have : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ centralInterval 1 := by
          filter_upwards [hboth] with t ht hmem
          exact hne (ht hmem)
        rw [MeasureTheory.ae_iff] at this
        simp only [not_not] at this
        exact hmeas this
      rw [← hcc, ← hdd]
      exact hrap
    -- the multiplier identity keeps the divisibility
    have hmulid := extendedMellinContinuation_dilationAverage hkC hδpos hksupp hexpδ hev hg
      hc hd hc' hd'
    have hdvd' : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        meromorphicOrderAt riemannZeta ρ
          ≤ meromorphicOrderAt (extendedMellinContinuation 1 c' d' G) ρ := by
      intro ρ hzero h1 h2
      rw [hGdef, hmulid]
      have hmul : AnalyticAt ℂ (fun s : ℂ => logSmoothMultiplier k (s - 1 / 2)) ρ := by
        refine Differentiable.analyticAt ?_ ρ
        exact (differentiable_logSmoothMultiplier hkcont hδpos hksupp).comp
          (differentiable_id.sub (differentiable_const _))
      have hM : MeromorphicAt (extendedMellinContinuation b c d g) ρ :=
        meromorphicAt_extendedMellinContinuation hb0 hev hc hd ρ
      have hfun : (fun s : ℂ => logSmoothMultiplier k (s - 1 / 2)
          * extendedMellinContinuation b c d g s)
          = (fun s : ℂ => logSmoothMultiplier k (s - 1 / 2))
            * extendedMellinContinuation b c d g := by
        funext s
        simp [Pi.mul_apply]
      rw [hfun, meromorphicOrderAt_mul hmul.meromorphicAt hM]
      have h0 : (0 : WithTop ℤ) ≤ meromorphicOrderAt
          (fun s : ℂ => logSmoothMultiplier k (s - 1 / 2)) ρ :=
        meromorphicOrderAt_nonneg_of_analyticAt hmul
      calc meromorphicOrderAt riemannZeta ρ
          ≤ meromorphicOrderAt (extendedMellinContinuation b c d g) ρ := hdvd ρ hzero h1 h2
        _ = 0 + meromorphicOrderAt (extendedMellinContinuation b c d g) ρ := by rw [zero_add]
        _ ≤ _ := by gcongr
    -- Corollary 5.3 and injectivity
    have hzeroG : ∀ Z : ℂ, riemannZeta Z ≠ 0 → Z ≠ 1 → Z ≠ 0 →
        extendedMellinContinuation 1 c' d' G Z = 0 := fun Z h1 h2 h3 =>
      extendedMellinContinuation_eq_zero_of_dvd le_rfl hGev hc' hd' hrapid hdvd' h1 h2 h3
    obtain ⟨Z₀, hZ₀1, hZ₀2, hZ₀ne⟩ := exists_good_point
    have hZ₀0 : Z₀ ≠ 0 := by
      intro h; rw [h] at hZ₀1; norm_num at hZ₀1
    have hZ₀one : Z₀ ≠ 1 := by
      intro h; rw [h] at hZ₀2; norm_num at hZ₀2
    have hnear : ∀ᶠ Z in 𝓝 Z₀, extendedMellinContinuation 1 c' d' G Z = 0 := by
      have hζ : ∀ᶠ Z in 𝓝 Z₀, riemannZeta Z ≠ 0 := by
        have hana : ContinuousAt riemannZeta Z₀ :=
          (differentiableAt_riemannZeta hZ₀one).continuousAt
        exact hana.eventually_ne hZ₀ne
      have h0 : ∀ᶠ Z in 𝓝 Z₀, Z ≠ 0 :=
        ContinuousAt.eventually_ne (g := fun z : ℂ => z) continuousAt_id hZ₀0
      have h1 : ∀ᶠ Z in 𝓝 Z₀, Z ≠ 1 :=
        ContinuousAt.eventually_ne (g := fun z : ℂ => z) continuousAt_id hZ₀one
      filter_upwards [hζ, h0, h1] with Z hζZ hZ0 hZ1
      exact hzeroG Z hζZ hZ1 hZ0
    have hnum : ∀ s : ℂ, extendedMellinNumerator 1 c' d' G s = 0 :=
      extendedMellinNumerator_eq_zero_of_eventually one_pos hGev hc' hd' hnear hZ₀0 hZ₀one
    have hGzero : G = 0 := by
      refine eq_zero_of_extendedMellinContinuation_eq_zero one_pos hGev hc' hd' ?_
      intro s _ _
      rw [extendedMellinContinuation, hnum s, zero_div]
    -- and the smoothing moves `g` by less than `ε`
    have hmove := norm_dilationAverage_sub_smul_le hkcont hks g hδpos hksupp hmodulus
    rw [hkint, hkabs, Complex.ofReal_one, one_smul, one_mul, ← hGdef, hGzero] at hmove
    have : ‖g‖ ≤ ε / 2 := by
      have h := hmove
      rw [zero_sub, norm_neg] at h
      exact h
    linarith
  have : ‖g‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hne)
    exact absurd (hnorm ‖g‖ hpos) (lt_irrefl _)
  exact norm_eq_zero.1 this

end

end RHTower
