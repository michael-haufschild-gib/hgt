import GaloisForLFunctions.RHTower.BurnolFiniteExceptional
import GaloisForLFunctions.RHTower.BurnolCompletenessLarge
import GaloisForLFunctions.HTGeometry.PolyTimesGeometricDecay

/-!
# Completeness after omitting finitely many evaluators

Burnol's Proposition 6.2.  If the Mellin transform of a vector of the dense subspace is divisible
by `ζ` at every nontrivial zero outside a finite set `R`, then Theorem 5.2 makes it `ζ(Z)` times a
rational function with poles in `R`; a rational function cannot decay exponentially on the real
axis, so it vanishes, and with it the transform.

## Main results

* `extendedMellin_eq_zero_of_finite_exceptional`
-/

open Complex Set Topology Filter MeasureTheory
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℝ} {f : SoninL2} {c d : ℂ}

/-- **A vector whose transform is `ζ`-divisible off a finite set has vanishing transform.** -/
theorem extendedMellin_eq_zero_of_finite_exceptional (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f))
    {R : Finset ℂ}
    (hRzero : ∀ ρ ∈ R, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1)
    (hdvd : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ ∉ R →
      meromorphicOrderAt riemannZeta ρ
        ≤ meromorphicOrderAt (extendedMellinContinuation a c d f) ρ)
    {C A : ℝ} (hC : 0 ≤ C) (hA0 : 0 < A) (hA1 : A < 1)
    (hdecay : ∀ σ : ℝ, 2 ≤ σ →
      ‖extendedMellinContinuation a c d f ((σ : ℝ) : ℂ)‖ ≤ C * A ^ σ)
    {Z : ℂ} (hZζ : riemannZeta Z ≠ 0) (hZ1 : Z ≠ 1) (hZ0 : Z ≠ 0) :
    extendedMellinContinuation a c d f Z = 0 := by
  classical
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  set G : ℂ → ℂ := extendedMellinContinuation a c d f with hGdef
  set H : ℂ → ℂ := burnolQuotient G with hHdef
  -- a common clearing exponent
  have hex : ∀ ρ : ℂ, ∃ m : ℕ, 1 ≤ m ∧ AnalyticAt ℂ (laurentShift H ρ m) 0 := by
    intro ρ
    refine exists_analyticAt_laurentShift_ge ?_ 1
    exact meromorphicAt_burnolQuotient (meromorphicAt_extendedMellinContinuation ha0 hev hc hd ρ)
  choose kf hkf1 hkf using hex
  set k : ℕ := max 1 (R.sup kf) with hkdef
  have hk1 : 1 ≤ k := le_max_left _ _
  have hkne : k ≠ 0 := by omega
  have hk : ∀ ρ ∈ R, AnalyticAt ℂ (laurentShift H ρ k) 0 := by
    intro ρ hρ
    refine analyticAt_laurentShift_of_le (hkf ρ) ?_
    exact le_trans (Finset.le_sup hρ) (le_max_right _ _)
  -- Theorem 5.2 collapses
  have hkey : ∀ W : ℂ, riemannZeta W ≠ 0 → W ≠ 1 → W ≠ 0 →
      G W = riemannZeta W * principalSum H R k W := by
    intro W hWζ hW1 hW0
    exact extendedMellin_eq_zeta_mul_principalSum ha hev hc hd hrapid hRzero hdvd hk hWζ hW1 hW0
  -- the polynomial decays on the real axis
  set M₀ : ℕ := R.sup (fun ρ => ⌈‖ρ‖⌉₊) with hM₀def
  have hM₀ : ∀ ρ ∈ R, ‖ρ‖ ≤ (M₀ : ℝ) := by
    intro ρ hρ
    refine le_trans (Nat.le_ceil ‖ρ‖) ?_
    exact_mod_cast Finset.le_sup (f := fun ρ : ℂ => ⌈‖ρ‖⌉₊) hρ
  set N : ℕ := k * R.card with hNdef
  have hpolybound : ∀ σ : ℝ, 2 ≤ σ →
      ‖(principalPoly H R k).eval ((σ : ℝ) : ℂ)‖ ≤ (4 * C) * (((σ + M₀) ^ N) * A ^ σ) := by
    intro σ hσ
    have hre : (((σ : ℝ) : ℂ)).re = σ := by simp
    have hσR : ((σ : ℝ) : ℂ) ∉ R := by
      intro h
      obtain ⟨-, -, h2⟩ := hRzero _ h
      rw [hre] at h2
      linarith
    have hζne : riemannZeta ((σ : ℝ) : ℂ) ≠ 0 := by
      have h := norm_riemannZeta_ge_of_two_le_re (s := ((σ : ℝ) : ℂ)) (by rw [hre]; linarith)
      intro hzero
      rw [hzero] at h
      simp at h
      linarith
    have hσ1 : ((σ : ℝ) : ℂ) ≠ 1 := by
      intro h; rw [h] at hre; simp at hre; linarith
    have hσ0 : ((σ : ℝ) : ℂ) ≠ 0 := by
      intro h; rw [h] at hre; simp at hre; linarith
    have hS : principalSum H R k ((σ : ℝ) : ℂ)
        = G ((σ : ℝ) : ℂ) * (riemannZeta ((σ : ℝ) : ℂ))⁻¹ := by
      have h := hkey ((σ : ℝ) : ℂ) hζne hσ1 hσ0
      field_simp
      linear_combination -h
    have hζ4 : ‖(riemannZeta ((σ : ℝ) : ℂ))⁻¹‖ ≤ 4 := by
      refine norm_zeta_inv_le_of_two_le_re ?_
      rw [hre]
      linarith
    have hSbound : ‖principalSum H R k ((σ : ℝ) : ℂ)‖ ≤ 4 * (C * A ^ σ) := by
      rw [hS, norm_mul]
      have hG := hdecay σ hσ
      have hG0 : (0:ℝ) ≤ ‖G ((σ : ℝ) : ℂ)‖ := norm_nonneg _
      have hA0' : (0:ℝ) ≤ A ^ σ := (Real.rpow_pos_of_pos hA0 σ).le
      nlinarith [hG, hζ4, hG0, norm_nonneg ((riemannZeta ((σ : ℝ) : ℂ))⁻¹)]
    have hDbound : ‖principalDen R k ((σ : ℝ) : ℂ)‖ ≤ (σ + M₀) ^ N := by
      rw [principalDen, norm_prod]
      have hterm : ∀ ρ ∈ R, ‖(((σ : ℝ) : ℂ) - ρ) ^ k‖ ≤ (σ + M₀) ^ k := by
        intro ρ hρ
        rw [norm_pow]
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ k
        refine le_trans (norm_sub_le _ _) ?_
        have h1 : ‖((σ : ℝ) : ℂ)‖ = σ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        rw [h1]
        linarith [hM₀ ρ hρ]
      calc (∏ ρ ∈ R, ‖(((σ : ℝ) : ℂ) - ρ) ^ k‖)
          ≤ ∏ _ρ ∈ R, (σ + M₀) ^ k := by
            refine Finset.prod_le_prod (fun ρ _ => norm_nonneg _) hterm
        _ = ((σ + M₀) ^ k) ^ R.card := by rw [Finset.prod_const]
        _ = (σ + M₀) ^ N := by rw [hNdef, ← pow_mul]
    rw [eval_principalPoly H R k hσR, norm_mul]
    have hD0 : (0:ℝ) ≤ ‖principalDen R k ((σ : ℝ) : ℂ)‖ := norm_nonneg _
    have hpow0 : (0:ℝ) ≤ (σ + M₀) ^ N := by positivity
    have hCA : (0:ℝ) ≤ 4 * (C * A ^ σ) := by
      have : (0:ℝ) ≤ A ^ σ := (Real.rpow_pos_of_pos hA0 σ).le
      positivity
    calc ‖principalSum H R k ((σ : ℝ) : ℂ)‖ * ‖principalDen R k ((σ : ℝ) : ℂ)‖
        ≤ (4 * (C * A ^ σ)) * (σ + M₀) ^ N := by
          exact mul_le_mul hSbound hDbound hD0 hCA
      _ = (4 * C) * (((σ + M₀) ^ N) * A ^ σ) := by ring
  have hmaj : Tendsto (fun σ : ℝ => (4 * C) * (((σ + M₀) ^ N) * A ^ σ)) atTop (𝓝 0) := by
    have h := tendsto_poly_mul_rpow_atTop_nhds_zero (A := A) (M := (M₀ : ℝ)) hA0 hA1 N
    have := h.const_mul (4 * C)
    simpa using this
  have hpolyzero : Tendsto (fun σ : ℝ => (principalPoly H R k).eval ((σ : ℝ) : ℂ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [Filter.eventually_ge_atTop (2:ℝ)] with σ hσ
    exact hpolybound σ hσ
  have hSzero : ∀ W : ℂ, W ∉ R → principalSum H R k W = 0 := fun W hW =>
    principalSum_eq_zero_of_tendsto hpolyzero hW hkne
  have hZR : Z ∉ R := by
    intro h
    obtain ⟨hz, -, -⟩ := hRzero Z h
    exact hZζ hz
  rw [hkey Z hZζ hZ1 hZ0, hSzero Z hZR, mul_zero]

/-! ## Proposition 6.2 -/

/-- **Burnol's Proposition 6.2 for `b > 1`.**  A vector of `L_b` whose transform is divisible by
`ζ` at all but finitely many nontrivial zeros is zero: the evaluators remain complete after
omitting arbitrarily finitely many of them. -/
theorem eq_zero_of_zeta_dvd_off_finite {b : ℝ} (hb : 1 < b) {g : SoninL2} {c d : ℂ}
    (hev : g ∈ evenSubspace) (hg : g ∈ centralSoninExtendedCarrier b)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval b →
      ((fourierUnitary g : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (g : ℝ → ℂ) t = d)
    {R : Finset ℂ}
    (hRzero : ∀ ρ ∈ R, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1)
    (hdvd : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ ∉ R →
      meromorphicOrderAt riemannZeta ρ
        ≤ meromorphicOrderAt (extendedMellinContinuation b c d g) ρ) :
    g = 0 := by
  classical
  have hb0 : (0 : ℝ) < b := by linarith
  have hlogb : 0 < Real.log b := Real.log_pos hb
  obtain ⟨Cg, hCg0, hgdecay⟩ := exists_norm_extendedMellin_real_decay hb0 hev hc hd
  have hnorm : ∀ ε : ℝ, 0 < ε → ‖g‖ < ε := by
    intro ε hε
    -- the modulus of strong continuity
    have hcont : Tendsto (fun x : ℝ => ‖rayDilate (Real.exp x) g - g‖) (𝓝 0) (𝓝 0) := by
      have h1 := tendsto_norm_rayDilate_sub_self g
      have h2 : Tendsto (fun x : ℝ => Real.exp x) (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ)) := by
        simpa using (Real.continuous_exp.tendsto (0 : ℝ))
      exact h1.comp h2
    obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.tendsto_nhds_nhds.1 hcont (ε / 2) (by linarith)
    set δ : ℝ := min (δ₀ / 2) (Real.log b / 2) with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]
      exact lt_min (by linarith) (by linarith)
    have hδlog : δ ≤ Real.log b / 2 := by rw [hδdef]; exact min_le_right _ _
    have hhalf : Real.exp (Real.log b / 2) = b ^ ((1:ℝ)/2) := by
      rw [Real.rpow_def_of_pos hb0]
      congr 1
      ring
    have hlt : b ^ ((1:ℝ)/2) < b := by
      have h : b ^ ((1:ℝ)/2) < b ^ (1:ℝ) := (Real.rpow_lt_rpow_left_iff hb).2 (by norm_num)
      rwa [Real.rpow_one] at h
    have hexpδlt : Real.exp δ < b := by
      refine lt_of_le_of_lt (Real.exp_le_exp.2 hδlog) ?_
      rw [hhalf]
      exact hlt
    have hexpδ : Real.exp δ ≤ b := le_of_lt hexpδlt
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
    set kk : ℝ → ℝ := φ.normed (volume : Measure ℝ) with hkkdef
    have hkC : ContDiff ℝ (⊤ : ℕ∞) kk := φ.contDiff_normed
    have hkcont : Continuous kk := hkC.continuous
    have hksupp : ∀ x : ℝ, δ ≤ |x| → kk x = 0 := by
      intro x hx
      have hsupp := φ.support_normed_eq (μ := (volume : Measure ℝ))
      have hnot : x ∉ Function.support kk := by
        rw [hkkdef, hsupp]
        simp only [Metric.mem_ball, Real.dist_eq, sub_zero, not_lt]
        exact hx
      exact Function.notMem_support.1 hnot
    have hks : HasCompactSupport kk := hasCompactSupport_of_vanishing hksupp
    have hkint : (∫ x : ℝ, kk x) = 1 := φ.integral_normed
    have hkabs : (∫ x : ℝ, |kk x|) = 1 := by
      rw [← hkint]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      exact abs_of_nonneg (φ.nonneg_normed x)
    -- the smoothed vector
    set G : SoninL2 := dilationAverage kk g with hGdef
    have hmem : ∀ x : ℝ, kk x ≠ 0 → rayDilate (Real.exp x) g ∈ centralSoninExtendedCarrier 1 :=
      rayDilate_mem_extended_one hexpδ hksupp hg
    have hGmem : G ∈ centralSoninExtendedCarrier 1 := dilationAverage_mem_extended hkcont hks hmem
    have hGev : G ∈ evenSubspace := dilationAverage_mem_evenSubspace hkcont hks hev
    obtain ⟨c', hc'⟩ := ae_fourier_eq_of_mem_extended hGmem
    obtain ⟨d', hd'⟩ := ae_eq_of_mem_extended hGmem
    have hmulid := extendedMellinContinuation_dilationAverage hkC hδpos hksupp hexpδ hev hg
      hc hd hc' hd'
    have hrapid : HasStripRapidDecrease (extendedMellinContinuation 1 c' d' G) := by
      rw [hGdef, hmulid]
      exact (hasStripRapidDecrease_logSmoothMultiplier hkC hδpos hksupp).mul_stripPolyGrowth
        (hasLProperty_extendedMellinContinuation hb0 hev hc hd).stripPolyGrowthOffReal
    -- divisibility is preserved
    have hdvd' : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ ∉ R →
        meromorphicOrderAt riemannZeta ρ
          ≤ meromorphicOrderAt (extendedMellinContinuation 1 c' d' G) ρ := by
      intro ρ hzero h1 h2 hρR
      rw [hGdef, hmulid]
      have hmul : AnalyticAt ℂ (fun s : ℂ => logSmoothMultiplier kk (s - 1 / 2)) ρ := by
        refine Differentiable.analyticAt ?_ ρ
        exact (differentiable_logSmoothMultiplier hkcont hδpos hksupp).comp
          (differentiable_id.sub (differentiable_const _))
      have hM : MeromorphicAt (extendedMellinContinuation b c d g) ρ :=
        meromorphicAt_extendedMellinContinuation hb0 hev hc hd ρ
      have hfun : (fun s : ℂ => logSmoothMultiplier kk (s - 1 / 2)
          * extendedMellinContinuation b c d g s)
          = (fun s : ℂ => logSmoothMultiplier kk (s - 1 / 2))
            * extendedMellinContinuation b c d g := by
        funext s
        simp [Pi.mul_apply]
      rw [hfun, meromorphicOrderAt_mul hmul.meromorphicAt hM]
      have h0 : (0 : WithTop ℤ) ≤ meromorphicOrderAt
          (fun s : ℂ => logSmoothMultiplier kk (s - 1 / 2)) ρ :=
        meromorphicOrderAt_nonneg_of_analyticAt hmul
      calc meromorphicOrderAt riemannZeta ρ
          ≤ meromorphicOrderAt (extendedMellinContinuation b c d g) ρ := hdvd ρ hzero h1 h2 hρR
        _ = 0 + meromorphicOrderAt (extendedMellinContinuation b c d g) ρ := by rw [zero_add]
        _ ≤ _ := by gcongr
    -- the decay of the smoothed transform
    set A : ℝ := Real.exp δ / b with hAdef
    have hA0 : 0 < A := by rw [hAdef]; positivity
    have hA1 : A < 1 := by
      rw [hAdef, div_lt_one hb0]
      exact hexpδlt
    have hGdecay : ∀ σ : ℝ, 2 ≤ σ →
        ‖extendedMellinContinuation 1 c' d' G ((σ : ℝ) : ℂ)‖ ≤ Cg * A ^ σ := by
      intro σ hσ
      rw [hGdef, hmulid]
      simp only
      have hmb := GaloisForLFunctions.HTGeometry.norm_logSmoothMultiplier_le_exp hkcont hδpos
        hksupp hkabs (((σ : ℝ) : ℂ) - 1 / 2)
      have hre : ((((σ : ℝ) : ℂ) - 1 / 2)).re = σ - 1 / 2 := by simp
      rw [hre] at hmb
      have habs : |σ - 1 / 2| = σ - 1 / 2 := abs_of_nonneg (by linarith)
      rw [habs] at hmb
      have hgd := hgdecay σ hσ
      have hArw : A ^ σ = Real.exp (δ * σ) * b ^ (-σ) := by
        rw [hAdef, Real.div_rpow (Real.exp_pos δ).le hb0.le, Real.rpow_neg hb0.le,
          Real.rpow_def_of_pos (Real.exp_pos δ), Real.log_exp, div_eq_mul_inv]
      have hmb0 : (0:ℝ) ≤ ‖logSmoothMultiplier kk (((σ : ℝ) : ℂ) - 1 / 2)‖ := norm_nonneg _
      have hgd0 : (0:ℝ) ≤ ‖extendedMellinContinuation b c d g ((σ : ℝ) : ℂ)‖ := norm_nonneg _
      have hexple : Real.exp (δ * (σ - 1 / 2)) ≤ Real.exp (δ * σ) := by
        refine Real.exp_le_exp.2 ?_
        nlinarith [hδpos]
      rw [norm_mul, hArw]
      have hbpow : (0:ℝ) < b ^ (-σ) := Real.rpow_pos_of_pos hb0 _
      calc ‖logSmoothMultiplier kk (((σ : ℝ) : ℂ) - 1 / 2)‖
            * ‖extendedMellinContinuation b c d g ((σ : ℝ) : ℂ)‖
          ≤ Real.exp (δ * (σ - 1 / 2)) * (Cg * b ^ (-σ)) := by
            exact mul_le_mul hmb hgd hgd0 (Real.exp_pos _).le
        _ ≤ Real.exp (δ * σ) * (Cg * b ^ (-σ)) := by
            refine mul_le_mul_of_nonneg_right hexple ?_
            positivity
        _ = Cg * (Real.exp (δ * σ) * b ^ (-σ)) := by ring
    -- the transform vanishes
    have hzeroG : ∀ Z : ℂ, riemannZeta Z ≠ 0 → Z ≠ 1 → Z ≠ 0 →
        extendedMellinContinuation 1 c' d' G Z = 0 := by
      intro Z hZζ hZ1 hZ0
      exact extendedMellin_eq_zero_of_finite_exceptional le_rfl hGev hc' hd' hrapid hRzero hdvd'
        hCg0.le hA0 hA1 hGdecay hZζ hZ1 hZ0
    obtain ⟨Z₀, hZ₀1, hZ₀2, hZ₀ne⟩ := exists_good_point
    have hZ₀0 : Z₀ ≠ 0 := by
      intro h; rw [h] at hZ₀1; norm_num at hZ₀1
    have hZ₀one : Z₀ ≠ 1 := by
      intro h; rw [h] at hZ₀2; norm_num at hZ₀2
    have hnear : ∀ᶠ Z in 𝓝 Z₀, extendedMellinContinuation 1 c' d' G Z = 0 := by
      have hζ : ∀ᶠ Z in 𝓝 Z₀, riemannZeta Z ≠ 0 :=
        ((differentiableAt_riemannZeta hZ₀one).continuousAt).eventually_ne hZ₀ne
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
    have hmove := norm_dilationAverage_sub_smul_le hkcont hks g hδpos hksupp hmodulus
    rw [hkint, hkabs, Complex.ofReal_one, one_smul, one_mul, ← hGdef, hGzero] at hmove
    have hfin : ‖g‖ ≤ ε / 2 := by
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
