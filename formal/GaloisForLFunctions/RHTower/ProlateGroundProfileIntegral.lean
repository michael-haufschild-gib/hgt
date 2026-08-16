import GaloisForLFunctions.RHTower.ProlateProfileIntegralLimit
import GaloisForLFunctions.RHTower.ProlateWindowProfileDistance

/-!
# The profile integral of the ground family converges to the Gaussian mass

For the variationally selected ground family the normalized rescaled profile satisfies

```text
∫_{−√c}^{√c} Ψ_c(ξ) dξ  →  ∫_ℝ e^{−ξ²/2} dξ = √(2π) .
```

All four inputs of the growing-window transfer are available at the family: the window comparison
against the Gaussian gives convergence on every fixed window, the Gaussian mass is exhausted by the
symmetric windows, the aperture virial gives a second moment bounded uniformly in the bandwidth, and
the second-moment tail bound turns that into tails uniformly below any target.  Evenness of the
profile converts the right tail bound into the left one.

This is the first-moment counterpart of `tendsto_prolateGround_centreMass`, which runs the same
squeeze on the square of the profile.
-/

noncomputable section

open MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- **The profile integral of the ground family.**  The integral of the normalized rescaled profile
over the natural window converges to the total Gaussian mass. -/
theorem tendsto_prolateGround_profileIntegral :
    ∃ Psi : ℝ → ℝ → ℝ,
      (∀ c : ℝ, 0 < c → ∃ lam chi : ℝ, lam ≠ 0 ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Psi c) ∧ Psi c ≠ 0 ∧ Function.Even (Psi c) ∧
        (∀ x : ℝ, bandTransform c (Psi c) x = lam * Psi c x) ∧
        (∀ x : ℝ, prolateSLAction c (Psi c) x = chi * Psi c x)) ∧
      Tendsto (fun c => ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
        normalizedProlateProfile c (Psi c) xi) atTop (𝓝 (Real.sqrt (2 * Real.pi))) ∧
      Tendsto (fun c => ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
        (normalizedProlateProfile c (Psi c) xi) ^ 2) atTop (𝓝 (Real.sqrt Real.pi)) := by
  obtain ⟨mu, Psi, hmu, hfam⟩ := exists_ground_family
  have hfam' : ∀ c : ℝ, 0 < c → ∃ lam chi : ℝ, lam ≠ 0 ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Psi c) ∧ Psi c ≠ 0 ∧ Function.Even (Psi c) ∧
      (∀ x : ℝ, bandTransform c (Psi c) x = lam * Psi c x) ∧
      (∀ x : ℝ, prolateSLAction c (Psi c) x = chi * Psi c x) := by
    intro c hc
    obtain ⟨lam, chi, hlam, hsm, hne, heven, hband, hprolate, _⟩ := hfam c hc
    exact ⟨lam, chi, hlam, hsm, hne, heven, hband, hprolate⟩
  have hepsP : ∀ K : ℝ, ∀ᶠ c in atTop, prolateWindowEpsP c (mu c) K 0 ≤ 1 := by
    intro K
    have h := tendsto_prolateWindowEpsP (n := 0) (K := K) (c := fun x : ℝ => x)
      (by simpa using hmu) tendsto_id
    filter_upwards [h.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with c hc
    exact hc.le
  have hepsQ : ∀ K : ℝ, ∀ᶠ c in atTop, prolateWindowEpsQ c K ≤ 1 := by
    intro K
    have h := tendsto_prolateWindowEpsQ (K := K) (c := fun x : ℝ => x) tendsto_id
    filter_upwards [h.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with c hc
    exact hc.le
  have hmu2 : ∀ᶠ c in atTop, mu c ≤ 2 := by
    filter_upwards [hmu.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))] with c hc
    exact hc.le
  have hmu0 : ∀ᶠ c in atTop, (0 : ℝ) ≤ mu c := by
    filter_upwards [hmu.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))] with c hc
    exact hc.le
  have hsqrt : ∀ K : ℝ, 0 < K → ∀ᶠ c in atTop, K ≤ Real.sqrt c := by
    intro K hK
    filter_upwards [eventually_ge_atTop (K ^ 2)] with c hc
    calc K = Real.sqrt (K ^ 2) := (Real.sqrt_sq hK.le).symm
      _ ≤ Real.sqrt c := Real.sqrt_le_sqrt hc
  -- the normalized total mass of the square converges to the Gaussian mass
  have htotalSq : Tendsto
      (fun c => ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
        (normalizedProlateProfile c (Psi c) xi) ^ 2) atTop (𝓝 (Real.sqrt Real.pi)) := by
    refine tendsto_total_of_window (M := 2)
      (W := fun K c => ∫ x in (-K)..K, (normalizedProlateProfile c (Psi c) x) ^ 2)
      (G := fun K => ∫ x in (-K)..K, Real.exp (-(x ^ 2))) (by norm_num) ?_ ?_ ?_
      tendsto_gaussianWindow
    · intro K hK _
      filter_upwards [eventually_gt_atTop (0 : ℝ), hsqrt K hK] with c hc hKc
      obtain ⟨lam, chi, hlam, hsm, _⟩ := hfam c hc
      exact window_le_total hKc (continuous_normalizedProlateProfile hsm)
    · intro K hK _
      filter_upwards [eventually_gt_atTop (0 : ℝ), hsqrt K hK, hmu2] with c hc hKc hm
      obtain ⟨lam, chi, hlam, hsm, hne, heven, hband, hprolate, hval, _⟩ := hfam c hc
      exact normalizedProlate_chebyshev hc hK hKc hsm (fun x _ => hprolate x) hval hm
    · intro K hK _
      have henv := tendsto_prolateWindowMassEnvelope (mu := mu) (c := fun x : ℝ => x) (K := K)
        hmu tendsto_id
      have hbnd : ∀ᶠ c in atTop,
          ‖(∫ x in (-K)..K, (normalizedProlateProfile c (Psi c) x) ^ 2)
            - ∫ x in (-K)..K, Real.exp (-(x ^ 2))‖ ≤ prolateWindowMassEnvelope c (mu c) K := by
        filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (2 * K ^ 2),
          hepsP K, hepsQ K] with c hc hcK hP hQ
        obtain ⟨lam, chi, hlam, hsm, hne, heven, hband, hprolate, hval, _⟩ := hfam c hc
        exact prolateGround_windowMass_bound hK hcK hsm hne heven hlam hband hprolate hval hP hQ
      have hzero := squeeze_zero_norm' hbnd henv
      have hadd := hzero.add_const (∫ x in (-K)..K, Real.exp (-(x ^ 2)))
      simpa using hadd
  -- a second moment bounded uniformly in the bandwidth
  set N₀ : ℝ := 2 * (Real.sqrt Real.pi + 1) with hN₀def
  have hN₀pos : 0 < N₀ := by
    have : (0 : ℝ) ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
    rw [hN₀def]; linarith
  have hmomN : ∀ᶠ c in atTop,
      (∫ xi in (-Real.sqrt c)..(Real.sqrt c),
        xi ^ 2 * (normalizedProlateProfile c (Psi c) xi) ^ 2) ≤ N₀ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hmu2, hmu0,
      htotalSq.eventually (eventually_lt_nhds (by linarith [Real.sqrt_nonneg Real.pi] :
        Real.sqrt Real.pi < Real.sqrt Real.pi + 1))] with c hc hm2 hm0 hlt
    obtain ⟨lam, chi, hlam, hsm, hne, heven, hband, hprolate, hval, _⟩ := hfam c hc
    have h1 := normalizedProlate_secondMoment_le hc hsm (fun x _ => hprolate x)
    rw [← hval] at h1
    have hsq : (0 : ℝ) ≤ Real.sqrt c := Real.sqrt_nonneg c
    have hM0 : (0 : ℝ) ≤ ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
        (normalizedProlateProfile c (Psi c) xi) ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) fun xi _ => by positivity
    rw [hN₀def]
    nlinarith [h1, hm2, hm0, hlt, hM0]
  -- the four inputs of the growing-window transfer
  have hint : ∀ᶠ c in atTop, ∀ u v : ℝ,
      IntervalIntegrable (normalizedProlateProfile c (Psi c)) volume u v := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    obtain ⟨lam, chi, hlam, hsm, _⟩ := hfam c hc
    exact fun u v => (continuous_normalizedProlateProfile hsm).intervalIntegrable u v
  have hcompact : ∀ K : ℝ, 0 < K →
      Tendsto (fun c => ∫ x in (-K)..K, normalizedProlateProfile c (Psi c) x) atTop
        (𝓝 (∫ x in (-K)..K, gaussianProfile x)) := by
    intro K hK
    refine tendsto_intervalIntegral_of_window_dist hK.le continuous_gaussianProfile ?_
      (tendsto_prolateWindowDistEnvelope (mu := mu) (c := fun x : ℝ => x) (K := K) hmu tendsto_id)
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (2 * K ^ 2),
      hepsP K, hepsQ K] with c hc hcK hP hQ
    obtain ⟨lam, chi, hlam, hsm, hne, heven, hband, hprolate, hval, _⟩ := hfam c hc
    exact ⟨continuous_normalizedProlateProfile hsm,
      prolateGround_windowDist_bound hK hcK hsm hne heven hlam hband hprolate hval hP hQ⟩
  have htail : ∀ δ : ℝ, 0 < δ → ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ K : ℝ, K₀ ≤ K →
      ∀ᶠ c in atTop,
        |∫ x in K..(Real.sqrt c), normalizedProlateProfile c (Psi c) x| ≤ δ ∧
        |∫ x in (-(Real.sqrt c))..(-K), normalizedProlateProfile c (Psi c) x| ≤ δ := by
    intro δ hδ
    refine ⟨N₀ / δ ^ 2 + 1, by positivity, ?_⟩
    intro K hK0
    have hKpos : 0 < K := lt_of_lt_of_le (by positivity) hK0
    have hcut : N₀ / δ ^ 2 < K := lt_of_lt_of_le (by linarith) hK0
    filter_upwards [eventually_gt_atTop (0 : ℝ), hsqrt K hKpos, hmomN] with c hc hKc hmom
    obtain ⟨lam, chi, hlam, hsm, hne, heven, hband, hprolate, hval, _⟩ := hfam c hc
    have hright := normalizedProlate_tail_lt hc hKpos hKc hN₀pos hδ hcut hsm hmom
    have heu : Function.Even (normalizedProlateProfile c (Psi c)) :=
      even_normalizedProlateProfile heven
    refine ⟨hright.le, ?_⟩
    rw [intervalIntegral_neg_of_even heu K (Real.sqrt c)]
    exact hright.le
  exact ⟨Psi, hfam', tendsto_intervalIntegral_growing_window' hint hcompact
    tendsto_intervalIntegral_gaussianProfile hsqrt htail, htotalSq⟩

/-- **The shape ratio of the ground profile.**  The square of the profile integral divided by the
mass integral is invariant under rescaling the profile, and converges to `2√π`.  This is the
normalization-free form of the two limits above: whatever multiple of the eigenfunction is chosen,
this ratio has the same limit. -/
theorem tendsto_prolateGround_shapeRatio :
    ∃ Psi : ℝ → ℝ → ℝ,
      (∀ c : ℝ, 0 < c → ∃ lam chi : ℝ, lam ≠ 0 ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Psi c) ∧ Psi c ≠ 0 ∧ Function.Even (Psi c) ∧
        (∀ x : ℝ, bandTransform c (Psi c) x = lam * Psi c x) ∧
        (∀ x : ℝ, prolateSLAction c (Psi c) x = chi * Psi c x)) ∧
      Tendsto (fun c => (∫ xi in (-Real.sqrt c)..(Real.sqrt c),
            normalizedProlateProfile c (Psi c) xi) ^ 2
          / ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
            (normalizedProlateProfile c (Psi c) xi) ^ 2)
        atTop (𝓝 (2 * Real.sqrt Real.pi)) := by
  obtain ⟨Psi, hfam, h1, h2⟩ := tendsto_prolateGround_profileIntegral
  refine ⟨Psi, hfam, ?_⟩
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hlim := (h1.pow 2).div h2 hpi.ne'
  have hval : Real.sqrt (2 * Real.pi) ^ 2 / Real.sqrt Real.pi = 2 * Real.sqrt Real.pi := by
    have hsq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
      Real.sq_sqrt (by positivity)
    have hpp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
      Real.mul_self_sqrt Real.pi_pos.le
    rw [hsq, div_eq_iff hpi.ne']
    nlinarith [hpp]
  rw [hval] at hlim
  simpa [Pi.div_def] using hlim

end GaloisForLFunctions.RHTower

end
