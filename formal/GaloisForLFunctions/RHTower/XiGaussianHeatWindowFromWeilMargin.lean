import GaloisForLFunctions.RHTower.XiGaussianHeatWindowWeilMarginAsymptotics

/-!
# The heat Hankel window from a pole-vanishing Weil margin

**Theorem** (`eventually_le_re_heatHankel_of_polarGroundEnergy`).  Let `A` be an aperture whose
pole-vanishing ground energy `μ₀(A)` of the restricted Weil form is positive, and let
`0 < K < A²/4`.  Then for all large `n`, every `0 < a ≤ K/n` and every real polynomial `P` of
degree `≤ n` with `P(−1/4) = 0`,

`(μ₀(A)/4) ∫ g² ≤ Re H_a(P, P)`,

where `g` is the physical heat test of `P`.  Since `g ≠ 0` for `P ≠ 0`
(`integral_heatTest_sq_pos`), the heat Hankel form is positive definite on the pole hyperplane
throughout the window `aN ≤ K` (`eventually_re_heatHankel_pos_of_polarGroundEnergy`).

The constant `A²/4` is the phase-space size of the heat test: `g` is a polynomial–Gaussian of degree
`2n` at width `√a`, whose classical turning point is `x² = 4an ≤ 4K < A²`, so `g` lives in the
aperture up to an exponentially small tail.  The proof truncates `g` with a smooth even cutoff,
restores the pole condition with a small multiple of the cutoff, applies the Weil margin to the
resulting source, and controls the change of the zero sum by integration by parts on the strip
(`le_re_heatHankel_of_polarGroundEnergy`), with tails from position moments of order `≍ n/m`
(`exists_heatMomentOrder`).
-/

open scoped Real
open Complex MeasureTheory Set Polynomial Filter Topology
open GaloisForLFunctions (gaussPolyFun)

namespace RHTower

noncomputable section

/-- **The heat test of a nonzero polynomial is nonzero.** -/
theorem integral_heatTest_sq_pos {a : ℝ} (ha : 0 < a) {P : ℝ[X]} (hP : P ≠ 0) :
    0 < ∫ x, heatTest a P x ^ 2 := by
  have hint := integrable_heatTest_sq ha P
  refine lt_of_le_of_ne (integral_nonneg fun _ => sq_nonneg _) fun h0 => hP ?_
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (heatTest a P x)) hint).1 h0.symm
  have hcont : Continuous fun x => heatTest a P x ^ 2 := (continuous_heatTest a P).pow 2
  have hzero : ∀ x, heatTest a P x = 0 := fun x => by
    have := congrFun ((hcont.ae_eq_iff_eq volume continuous_const).1 hae) x
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  have heval : ∀ w : ℂ, (P.map (algebraMap ℝ ℂ)).eval w = 0 := fun w => by
    obtain ⟨z, rfl⟩ := IsSepClosed.exists_pow_nat_eq w 2
    have h := heatStripTransform_heatPhysical ha P z
    have hl : heatStripTransform (fun x => ((gaussPolyFun (heatPolyR a P) (1 / (2 * a)) x : ℝ) : ℂ))
        z = 0 := by
      unfold heatStripTransform
      have : ∀ x, gaussPolyFun (heatPolyR a P) (1 / (2 * a)) x = 0 := hzero
      simp only [this, Complex.ofReal_zero, zero_mul, MeasureTheory.integral_zero]
    rw [hl] at h
    exact (mul_eq_zero.1 h.symm).resolve_left (Complex.exp_ne_zero _)
  have hmap : P.map (algebraMap ℝ ℂ) = 0 := Polynomial.funext (by simpa using heval)
  exact Polynomial.map_injective _ (algebraMap ℝ ℂ).injective (by rw [hmap, Polynomial.map_zero])

theorem exists_cutoff_radii {A K : ℝ} (hA : 0 < A) (hKA : 4 * K < A ^ 2) :
    ∃ B₀ B₁ : ℝ, 0 < B₀ ∧ B₀ < B₁ ∧ B₁ < A ∧ 4 * K < B₀ ^ 2 := by
  have hs : Real.sqrt (4 * K) < A := (Real.sqrt_lt' hA).2 hKA
  have hs0 : 0 ≤ Real.sqrt (4 * K) := Real.sqrt_nonneg _
  refine ⟨(Real.sqrt (4 * K) + A) / 2, ((Real.sqrt (4 * K) + A) / 2 + A) / 2, by linarith,
    by linarith, by linarith, ?_⟩
  exact (Real.sqrt_lt' (x := 4 * K) (by linarith : (0 : ℝ) < (Real.sqrt (4 * K) + A) / 2)).1
    (by linarith)

/-- **A pole-vanishing Weil margin forces the heat Hankel window `aN ≤ K` for every
`K < A²/4`.** -/
theorem eventually_le_re_heatHankel_of_polarGroundEnergy {A : SuzukiPositiveAperture}
    (hμ : 0 < ccmRestrictedWeilPolarGroundEnergy A) {K : ℝ} (hK : 0 < K) (hKA : 4 * K < A.1 ^ 2) :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 0 < a → a ≤ K / n → ∀ P : ℝ[X], P.natDegree ≤ n →
      P.eval (-1 / 4) = 0 →
        ccmRestrictedWeilPolarGroundEnergy A / 4 * ∫ x, heatTest a P x ^ 2 ≤
          (heatHankel a (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re := by
  obtain ⟨B₀, B₁, hB₀, h01, h1A, hKB⟩ := exists_cutoff_radii A.2 hKA
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_heatCutoff (B₀ := B₀) (B₁ := B₁) hB₀.le h01
  have hc₀ : 0 < cutoffMoment B₀ B₁ := cutoffMoment_pos hB₀ h01
  have hN : 0 ≤ ∫ x, |deriv (heatCutoff B₀ B₁) x| * Real.exp (|x| / 2) :=
    integral_nonneg fun _ => by positivity
  have hE : 0 ≤ heatStripConstant B₀ := by unfold heatStripConstant; positivity
  have hS : 0 ≤ ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := tsum_nonneg fun _ => by positivity
  -- opaque names for the constants
  obtain ⟨μ, hμe⟩ : ∃ μ, μ = ccmRestrictedWeilPolarGroundEnergy A := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀e⟩ : ∃ c₀, c₀ = cutoffMoment B₀ B₁ := ⟨_, rfl⟩
  obtain ⟨N, hNe⟩ : ∃ N, N = ∫ x, |deriv (heatCutoff B₀ B₁) x| * Real.exp (|x| / 2) := ⟨_, rfl⟩
  obtain ⟨E, hEe⟩ : ∃ E, E = heatStripConstant B₀ := ⟨_, rfl⟩
  obtain ⟨S, hSe⟩ : ∃ S, S = ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := ⟨_, rfl⟩
  rw [← hμe] at hμ ⊢
  rw [← hc₀e] at hc₀
  rw [← hNe] at hN
  rw [← hEe] at hE
  rw [← hSe] at hS
  obtain ⟨D, hDe⟩ : ∃ D, D = μ / 2 + 2 * μ * B₀ * E / c₀ ^ 2 + 7 * S * E +
      6 * S * E * (C ^ 2 + N ^ 2 / c₀ ^ 2) := ⟨_, rfl⟩
  have hD : 0 < D := by rw [hDe]; positivity
  obtain ⟨δ, hδe⟩ : ∃ δ : ℝ, δ = min (1 / 2) (μ / (4 * D)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδe]; exact lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := by rw [hδe]; exact min_le_left _ _
  have hδD : δ * D ≤ μ / 4 := by
    have h := min_le_right (1 / 2 : ℝ) (μ / (4 * D))
    rw [← hδe] at h
    calc δ * D ≤ μ / (4 * D) * D := mul_le_mul_of_nonneg_right h hD.le
      _ = μ / 4 := by field_simp
  obtain ⟨m, hm0, hmom⟩ := exists_heatMomentOrder hK hB₀ hKB
  filter_upwards [hmom δ hδ0] with n hn a ha haK P hdeg hP
  obtain ⟨ha1, hσδ, hσYδ⟩ := hn a ha haK
  have htpos : 0 < heatMomentRatio n (2 * (n / m + 1)) a B₀ := heatMomentRatio_pos ha ha1 hB₀
  obtain ⟨σ, hσe⟩ : ∃ σ, σ = heatMomentRatio n (2 * (n / m + 1)) a B₀ ^ (n / m + 1) := ⟨_, rfl⟩
  rw [← hσe] at hσδ hσYδ
  have hσ0 : 0 < σ := by rw [hσe]; exact pow_pos htpos _
  have hσ1 : σ ≤ 1 := by linarith only [hσδ, hδ1]
  have hσ2 : heatMomentRatio n (2 * (n / m + 1)) a B₀ ^ (2 * (n / m + 1)) = σ ^ 2 := by
    rw [hσe, ← pow_mul, mul_comm]
  have hk : heatMomentRatio n (2 * (n / m + 1)) a B₀ ^ (2 * (n / m + 1)) ≤ 1 / 2 := by
    rw [hσ2]
    have h := mul_le_mul_of_nonneg_left hσ1 hσ0.le
    rw [mul_one, ← pow_two] at h
    linarith only [h, hσδ, hδ1]
  obtain ⟨hT, hτ₀, hτ₁, hM⟩ := heatTest_tail_bounds ha ha1 hdeg hB₀ (2 * (n / m + 1)) hk
  rw [hσ2] at hT hτ₀ hτ₁
  rw [← hEe] at hτ₀ hτ₁ hM
  have hmain := le_re_heatHankel_of_polarGroundEnergy A hB₀ h01 h1A ha ha1 P (hμe ▸ hμ.le) hC
  rw [← hμe, ← hNe, ← hSe] at hmain
  have hκ := abs_heatPoleCorrection_mul_le hB₀ h01 ha ha1 P hP
  rw [← hc₀e] at hκ
  obtain ⟨Y, hYe⟩ : ∃ Y : ℝ, Y = 4 * (1 / (2 * a)) * (2 * n + 1) := ⟨_, rfl⟩
  rw [← hYe] at hσYδ hτ₁ hM
  have hY : 0 ≤ Y := by rw [hYe]; positivity
  have hτ₀0 : 0 ≤ stripMassOn (heatTest a P) (heatTailSet B₀) :=
    setIntegral_nonneg (measurableSet_heatTailSet B₀) fun _ _ => by positivity
  have hτ₁0 : 0 ≤ stripMassOn (heatTestDeriv a P) (heatTailSet B₀) :=
    setIntegral_nonneg (measurableSet_heatTailSet B₀) fun _ _ => by positivity
  have hfin := le_of_margin_bounds hμ.le hS hc₀ hC0 hN hB₀.le hσ0 hσ1 hY hτ₀0 hτ₁0 hmain rfl
    hT hτ₀ hτ₁ hM hκ
  have hV : 0 ≤ ∫ x, heatTest a P x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hbr : μ / 4 ≤ μ / 2 - σ ^ 2 * (μ / 2 + 2 * μ * B₀ * E / c₀ ^ 2) -
      S * E * σ * (7 * Y + 6 * (C ^ 2 + N ^ 2 / c₀ ^ 2)) := by
    have hσσ : σ ^ 2 ≤ δ := by
      have h := mul_le_mul_of_nonneg_left hσ1 hσ0.le
      rw [mul_one, ← pow_two] at h
      exact h.trans hσδ
    have h1 : σ ^ 2 * (μ / 2 + 2 * μ * B₀ * E / c₀ ^ 2) ≤ δ * (μ / 2 + 2 * μ * B₀ * E / c₀ ^ 2) :=
      mul_le_mul_of_nonneg_right hσσ (by positivity)
    have hZ : 0 ≤ C ^ 2 + N ^ 2 / c₀ ^ 2 := by positivity
    have h3 : 7 * (σ * Y) + 6 * (C ^ 2 + N ^ 2 / c₀ ^ 2) * σ ≤
        7 * δ + 6 * (C ^ 2 + N ^ 2 / c₀ ^ 2) * δ := by
      have := mul_le_mul_of_nonneg_left (hσδ) (by positivity : (0 : ℝ) ≤ 6 * (C ^ 2 + N ^ 2 / c₀ ^ 2))
      linarith only [this, hσYδ]
    have hSE : 0 ≤ S * E := mul_nonneg hS hE
    have h2 : S * E * σ * (7 * Y + 6 * (C ^ 2 + N ^ 2 / c₀ ^ 2)) ≤
        δ * (7 * S * E + 6 * S * E * (C ^ 2 + N ^ 2 / c₀ ^ 2)) := by
      have e : S * E * σ * (7 * Y + 6 * (C ^ 2 + N ^ 2 / c₀ ^ 2)) =
          S * E * (7 * (σ * Y) + 6 * (C ^ 2 + N ^ 2 / c₀ ^ 2) * σ) := by ring
      rw [e]
      calc S * E * (7 * (σ * Y) + 6 * (C ^ 2 + N ^ 2 / c₀ ^ 2) * σ)
          ≤ S * E * (7 * δ + 6 * (C ^ 2 + N ^ 2 / c₀ ^ 2) * δ) :=
            mul_le_mul_of_nonneg_left h3 hSE
        _ = δ * (7 * S * E + 6 * S * E * (C ^ 2 + N ^ 2 / c₀ ^ 2)) := by ring
    have hDexp : δ * D = δ * (μ / 2 + 2 * μ * B₀ * E / c₀ ^ 2) +
        δ * (7 * S * E + 6 * S * E * (C ^ 2 + N ^ 2 / c₀ ^ 2)) := by rw [hDe]; ring
    linarith only [h1, h2, hδD, hDexp]
  calc μ / 4 * ∫ x, heatTest a P x ^ 2
      ≤ (∫ x, heatTest a P x ^ 2) * (μ / 2 - σ ^ 2 * (μ / 2 + 2 * μ * B₀ * E / c₀ ^ 2) -
          S * E * σ * (7 * Y + 6 * (C ^ 2 + N ^ 2 / c₀ ^ 2))) := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hbr hV
    _ ≤ _ := hfin

/-- **Positivity on the pole hyperplane throughout the window `aN ≤ K`, `K < A²/4`.** -/
theorem eventually_re_heatHankel_pos_of_polarGroundEnergy {A : SuzukiPositiveAperture}
    (hμ : 0 < ccmRestrictedWeilPolarGroundEnergy A) {K : ℝ} (hK : 0 < K) (hKA : 4 * K < A.1 ^ 2) :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 0 < a → a ≤ K / n → ∀ P : ℝ[X], P.natDegree ≤ n →
      P.eval (-1 / 4) = 0 → P ≠ 0 →
        0 < (heatHankel a (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re := by
  filter_upwards [eventually_le_re_heatHankel_of_polarGroundEnergy hμ hK hKA] with n hn a ha haK P
    hdeg hP hP0
  have h := hn a ha haK P hdeg hP
  have hV := integral_heatTest_sq_pos ha hP0
  have : 0 < ccmRestrictedWeilPolarGroundEnergy A / 4 * ∫ x, heatTest a P x ^ 2 := by positivity
  linarith

end

end RHTower
