import GaloisForLFunctions.RHTower.ProlateApertureVirial
import GaloisForLFunctions.RHTower.ProlateSeparationLimit

/-!
# The selected ground family: separation constant one, and Gaussian shape

The aperture virial bound `c ≤ μ(c+3)` is sharper and simpler than the window estimate, and it
sandwiches the variationally selected family directly against `μ < 1`:

`1 − 3/(c+3) ≤ μ_c < 1` ,   so   `μ_c → 1` .

The same virial identity, with its arithmetic--geometric defect retained, says that the selected
mode's deviation from the prolate Gaussian shape `(1−x²)Φ′ = −cxΦ` is

`∫(cxΦ + (1−x²)Φ′)² ≤ c((μ − 1)∫Φ² + 3∫x²Φ²)` ,

whose right-hand side is `o(c ∫Φ²)` because `μ → 1` and `∫x²Φ² ≤ (μ/c)∫Φ²`.
-/

open Filter Topology Set MeasureTheory

namespace RHTower

/-- **Sharp sandwich.**  `c ≤ μ(c+3)` below and `μ < 1` above force `μ → 1`. -/
theorem tendsto_one_of_sandwich_sharp {mu : ℝ → ℝ}
    (hupper : ∀ᶠ c in atTop, mu c < 1)
    (hlower : ∀ᶠ c in atTop, c ≤ mu c * (c + 3)) :
    Tendsto mu atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨N, hN⟩ := exists_nat_gt (3 * b / (1 - b) + 3)
    filter_upwards [hlower, eventually_ge_atTop ((N : ℝ)), eventually_gt_atTop (0 : ℝ)]
      with c hc hcN hcpos
    have hden : (0 : ℝ) < c + 3 := by linarith
    have hbig : 3 * b / (1 - b) + 3 < c := lt_of_lt_of_le hN hcN
    have hone : (0 : ℝ) < 1 - b := by linarith
    have hstep : 3 * b < (c - 3) * (1 - b) := by
      rw [div_add' _ _ _ (ne_of_gt hone), div_lt_iff₀ hone] at hbig
      nlinarith [hbig]
    nlinarith [hc, hstep, hden]
  · filter_upwards [hupper] with c hc
    linarith

/-- **The selected ground family.**  A single choice of mode at every bandwidth whose separation
constants tend to one and whose Gaussian defect obeys the virial bound. -/
theorem exists_ground_family :
    ∃ (mu : ℝ → ℝ) (Psi : ℝ → ℝ → ℝ), Tendsto mu atTop (𝓝 1) ∧
      ∀ c : ℝ, 0 < c → ∃ (lam chi : ℝ), lam ≠ 0 ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Psi c) ∧ Psi c ≠ 0 ∧ Function.Even (Psi c) ∧
        (∀ x : ℝ, bandTransform c (Psi c) x = lam * Psi c x) ∧
        (∀ x : ℝ, prolateSLAction c (Psi c) x = chi * Psi c x) ∧
        mu c = c * radialSeparationRatio c chi ∧
        0 < (∫ x in (-1 : ℝ)..1, (Psi c x) ^ 2) ∧
        (∫ x in (-1 : ℝ)..1, x ^ 2 * (Psi c x) ^ 2)
          ≤ (mu c / c) * ∫ x in (-1 : ℝ)..1, (Psi c x) ^ 2 ∧
        (∫ x in (-1 : ℝ)..1, (c * x * Psi c x + (1 - x ^ 2) * deriv (Psi c) x) ^ 2)
          ≤ c * ((mu c - 1) * (∫ x in (-1 : ℝ)..1, (Psi c x) ^ 2)
            + 3 * ∫ x in (-1 : ℝ)..1, x ^ 2 * (Psi c x) ^ 2) := by
  have hex : ∀ c : ℝ, ∃ p : ℝ × (ℝ → ℝ), 0 < c →
      ((∃ (lam chi : ℝ), lam ≠ 0 ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p.2 ∧ p.2 ≠ 0 ∧ Function.Even p.2 ∧
        (∀ x : ℝ, bandTransform c p.2 x = lam * p.2 x) ∧
        (∀ x : ℝ, prolateSLAction c p.2 x = chi * p.2 x) ∧
        p.1 = c * radialSeparationRatio c chi) ∧ p.1 < 1) := by
    intro c
    by_cases hc : 0 < c
    · obtain ⟨lam, chi, Phi, hlam, hsm, hne, heven, hband, hprolate, hlt⟩ :=
        exists_even_joint_prolate_eigen_bandwidth_separation_lt_one hc
      exact ⟨(c * radialSeparationRatio c chi, Phi), fun _ =>
        ⟨⟨lam, chi, hlam, hsm, hne, heven, hband, hprolate, rfl⟩, hlt⟩⟩
    · exact ⟨(0, fun _ => 0), fun h => absurd h hc⟩
  refine ⟨fun c => (Classical.choose (hex c)).1, fun c => (Classical.choose (hex c)).2, ?_, ?_⟩
  · refine tendsto_one_of_sandwich_sharp ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
      exact ((Classical.choose_spec (hex c)) hc).2
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
      obtain ⟨⟨lam, chi, hlam, hsm, hne, heven, hband, hprolate, hval⟩, _⟩ :=
        (Classical.choose_spec (hex c)) hc
      have hposS : 0 < ∫ x in (-1 : ℝ)..1, ((Classical.choose (hex c)).2 x) ^ 2 :=
        integral_sq_pos_of_band_eigen hsm.continuous hlam hne hband
      have := bandwidthSeparation_ge hc hsm hposS (fun x _ => hprolate x)
      rw [hval]
      exact this
  · intro c hc
    obtain ⟨⟨lam, chi, hlam, hsm, hne, heven, hband, hprolate, hval⟩, _⟩ :=
      (Classical.choose_spec (hex c)) hc
    have hcne : c ≠ 0 := ne_of_gt hc
    have hposS : 0 < ∫ x in (-1 : ℝ)..1, ((Classical.choose (hex c)).2 x) ^ 2 :=
      integral_sq_pos_of_band_eigen hsm.continuous hlam hne hband
    have hmom := integral_sq_mul_sq_le_separation hcne hsm (fun x _ => hprolate x)
    have hdef := integral_prolateGaussianDefect_le hc hsm (fun x _ => hprolate x)
    refine ⟨lam, chi, hlam, hsm, hne, heven, hband, hprolate, hval, hposS, ?_, ?_⟩
    · show (∫ x in (-1 : ℝ)..1, x ^ 2 * ((Classical.choose (hex c)).2 x) ^ 2)
          ≤ ((Classical.choose (hex c)).1 / c)
            * ∫ x in (-1 : ℝ)..1, ((Classical.choose (hex c)).2 x) ^ 2
      rw [hval]
      have hid : c * radialSeparationRatio c chi / c = radialSeparationRatio c chi := by
        field_simp
      rw [hid]
      exact hmom
    · show (∫ x in (-1 : ℝ)..1,
          (c * x * (Classical.choose (hex c)).2 x
            + (1 - x ^ 2) * deriv ((Classical.choose (hex c)).2) x) ^ 2)
          ≤ c * (((Classical.choose (hex c)).1 - 1)
            * (∫ x in (-1 : ℝ)..1, ((Classical.choose (hex c)).2 x) ^ 2)
            + 3 * ∫ x in (-1 : ℝ)..1, x ^ 2 * ((Classical.choose (hex c)).2 x) ^ 2)
      rw [hval]
      exact hdef

end RHTower
