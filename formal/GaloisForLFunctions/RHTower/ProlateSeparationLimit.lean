import GaloisForLFunctions.RHTower.ProlateSeparationLowerBound
import GaloisForLFunctions.RHTower.ProlateSharpSeparationMode

/-!
# The ground separation constant converges to the first oscillator rung

The Gaussian trial gives a mode with `μ = c·s < 1` at every bandwidth, and the uncertainty estimate
gives every mode `c δ₀²(1 − 4δ₀²) ≤ μ (5(1 − 4δ₀²) + c δ₀²)` for every window scale `δ₀`.  The two
together pin the constant: at fixed `δ₀` the lower bound tends to `1 − 4δ₀²`, and `δ₀` is free, so

`μ_c → 1` .

The limit is the ground state energy of the harmonic oscillator, reached with no eigenfunction
asymptotics and no spectral theory — only the exact prolate Rayleigh identity, one integration by
parts, and the arithmetic--geometric mean inequality.
-/

open Filter Topology Set MeasureTheory

namespace RHTower

/-- A nonzero global band eigenfunction has positive mass on the aperture. -/
theorem integral_sq_pos_of_band_eigen {c lam : ℝ} {Phi : ℝ → ℝ}
    (hcont : Continuous Phi) (hlam : lam ≠ 0) (hne : Phi ≠ 0)
    (hband : ∀ x : ℝ, bandTransform c Phi x = lam * Phi x) :
    0 < ∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ) := by
  have hbc :=
    GaloisForLFunctions.RHTower.bandClass_ne_zero_of_global_band_eigen hcont hlam hne hband
  have hinner : (0 : ℝ) < inner ℝ (GaloisForLFunctions.RHTower.bandClass Phi hcont)
      (GaloisForLFunctions.RHTower.bandClass Phi hcont) := real_inner_self_pos.2 hbc
  rw [GaloisForLFunctions.RHTower.inner_bandClass_eq] at hinner
  calc (0 : ℝ) < ∫ x in (-1 : ℝ)..1, Phi x * Phi x := hinner
    _ = ∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ) :=
        intervalIntegral.integral_congr fun x _ => by ring

/-- **Sandwich.**  A family below one that satisfies the window lower bound at every scale tends to
one. -/
theorem tendsto_one_of_sandwich {mu : ℝ → ℝ}
    (hupper : ∀ᶠ c in atTop, mu c < 1)
    (hlower : ∀ delta0 : ℝ, 0 < delta0 → delta0 ≤ 1 / 4 →
      ∀ᶠ c in atTop, c * delta0 ^ (2 : ℕ) * (1 - 4 * delta0 ^ (2 : ℕ))
        ≤ mu c * (5 * (1 - 4 * delta0 ^ (2 : ℕ)) + c * delta0 ^ (2 : ℕ))) :
    Tendsto mu atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- lower half
    set eps : ℝ := min (1 - b) 1 with heps
    have hepspos : 0 < eps := by
      rw [heps]
      exact lt_min (by linarith) one_pos
    have hepsle1 : eps ≤ 1 := min_le_right _ _
    have hble : b ≤ 1 - eps := by
      have : eps ≤ 1 - b := min_le_left _ _
      linarith
    set delta0 : ℝ := min (1 / 4) (Real.sqrt (eps / 8)) with hdelta
    have hspos : 0 < Real.sqrt (eps / 8) := Real.sqrt_pos.2 (by linarith)
    have hd0pos : 0 < delta0 := lt_min (by norm_num) hspos
    have hd0le : delta0 ≤ 1 / 4 := min_le_left _ _
    have hd0sq : delta0 ^ (2 : ℕ) ≤ eps / 8 := by
      have h1 : delta0 ≤ Real.sqrt (eps / 8) := min_le_right _ _
      have h2 : Real.sqrt (eps / 8) ^ (2 : ℕ) = eps / 8 := Real.sq_sqrt (by linarith)
      nlinarith [hd0pos, h1, h2]
    have hgap : 1 - 4 * delta0 ^ (2 : ℕ) ≥ 1 - eps / 2 := by linarith
    have hgappos : (0 : ℝ) < 1 - 4 * delta0 ^ (2 : ℕ) := by linarith
    have hgaple : 1 - 4 * delta0 ^ (2 : ℕ) ≤ 1 := by nlinarith [hd0pos]
    have hd0sqpos : (0 : ℝ) < delta0 ^ (2 : ℕ) := by positivity
    have hthresh : ∀ᶠ c in atTop, (10 : ℝ) / (delta0 ^ (2 : ℕ) * eps) < c :=
      eventually_gt_atTop _
    filter_upwards [hlower delta0 hd0pos hd0le, hthresh, eventually_gt_atTop (0 : ℝ)]
      with c hc hcbig hcpos
    have hApos : (0 : ℝ) < c * delta0 ^ (2 : ℕ) := mul_pos hcpos hd0sqpos
    have hden : (0 : ℝ) < 5 * (1 - 4 * delta0 ^ (2 : ℕ)) + c * delta0 ^ (2 : ℕ) := by linarith
    have hAeps : (5 : ℝ) < c * delta0 ^ (2 : ℕ) * eps / 2 := by
      have hpe : (0 : ℝ) < delta0 ^ (2 : ℕ) * eps := by positivity
      rw [div_lt_iff₀ hpe] at hcbig
      linarith
    have hstrict : (1 - eps) * (5 * (1 - 4 * delta0 ^ (2 : ℕ)) + c * delta0 ^ (2 : ℕ))
        < c * delta0 ^ (2 : ℕ) * (1 - 4 * delta0 ^ (2 : ℕ)) := by
      nlinarith [hAeps, hgap, hgaple, hgappos, hApos, hepsle1, hepspos]
    have hmu : 1 - eps < mu c := by
      have h := lt_of_lt_of_le hstrict hc
      exact lt_of_mul_lt_mul_right (by linarith [h]) (le_of_lt hden)
    linarith
  · filter_upwards [hupper] with c hc
    linarith


/-- **The prolate ground separation constant converges to the first oscillator rung.**  At every
bandwidth the variational principle supplies an even joint band/prolate mode with `c·s < 1`, and the
uncertainty bound applies to every mode, so the selected family's separation constants tend to `1`. -/
theorem exists_tendsto_bandwidthSeparation_one :
    ∃ mu : ℝ → ℝ, Tendsto mu atTop (𝓝 1) ∧
      ∀ c : ℝ, 0 < c → ∃ (lam chi : ℝ) (Phi : ℝ → ℝ), lam ≠ 0 ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧ Phi ≠ 0 ∧ Function.Even Phi ∧
        (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) ∧
        (∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x) ∧
        mu c = c * radialSeparationRatio c chi := by
  have hex : ∀ c : ℝ, ∃ m : ℝ, 0 < c →
      ((∃ (lam chi : ℝ) (Phi : ℝ → ℝ), lam ≠ 0 ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧ Phi ≠ 0 ∧ Function.Even Phi ∧
        (∀ x : ℝ, bandTransform c Phi x = lam * Phi x) ∧
        (∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x) ∧
        m = c * radialSeparationRatio c chi) ∧ m < 1) := by
    intro c
    by_cases hc : 0 < c
    · obtain ⟨lam, chi, Phi, hlam, hsm, hne, heven, hband, hprolate, hlt⟩ :=
        exists_even_joint_prolate_eigen_bandwidth_separation_lt_one hc
      exact ⟨c * radialSeparationRatio c chi, fun _ =>
        ⟨⟨lam, chi, Phi, hlam, hsm, hne, heven, hband, hprolate, rfl⟩, hlt⟩⟩
    · exact ⟨0, fun h => absurd h hc⟩
  refine ⟨fun c => Classical.choose (hex c), ?_, ?_⟩
  · refine tendsto_one_of_sandwich ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
      exact ((Classical.choose_spec (hex c)) hc).2
    · intro delta0 hd0 hd0le
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
      obtain ⟨⟨lam, chi, Phi, hlam, hsm, hne, heven, hband, hprolate, hval⟩, _⟩ :=
        (Classical.choose_spec (hex c)) hc
      have hcont : Continuous Phi := hsm.continuous
      have hposS : 0 < ∫ x in (-1 : ℝ)..1, Phi x ^ (2 : ℕ) :=
        integral_sq_pos_of_band_eigen hcont hlam hne hband
      have hlow := bandwidthSeparation_lower hc hd0 hd0le hsm heven hposS
        (fun x _ => hprolate x)
      rw [hval]
      exact hlow
  · intro c hc
    obtain ⟨⟨lam, chi, Phi, hlam, hsm, hne, heven, hband, hprolate, hval⟩, _⟩ :=
      (Classical.choose_spec (hex c)) hc
    exact ⟨lam, chi, Phi, hlam, hsm, hne, heven, hband, hprolate, hval⟩

end RHTower
