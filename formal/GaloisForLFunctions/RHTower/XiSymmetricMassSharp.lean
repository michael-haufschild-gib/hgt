import GaloisForLFunctions.RHTower.XiSymmetricMassBounds
import GaloisForLFunctions.RHTower.XiOrdinateBandCopies

/-!
# The sharp divisor-mass asymptotic

`exists_xiSymmetricMass_two_sided` traps the symmetric `ξ`-divisor mass between two fixed multiples
of `T\log T`.  The quarter-path formula gives more: the vertical contribution has ratio exactly
`1/2` and the horizontal one is `O(\log T)`, so at admissible heights

```text
xiSymmetricMass T = (1/π)·T log T · (1 + o(1)).
```

This is the Riemann–von Mangoldt main term for the symmetric count `2N(T)`.  Monotonicity of the
mass in the height is recorded alongside, for the transfer to arbitrary heights.
-/

open Complex Filter Topology


noncomputable section

namespace RHTower

theorem xiSymmetricMass_mono {T₁ T₂ : ℝ} (h₁ : 0 ≤ T₁) (h : T₁ ≤ T₂) :
    xiSymmetricMass T₁ ≤ xiSymmetricMass T₂ := by
  have hdiff := xiSymmetricMass_diff_eq_card h₁ h
  have hnn : (0 : ℤ) ≤ ((xiCopiesBand T₁ T₂).card : ℤ) := Int.natCast_nonneg _
  omega

/-- **The sharp divisor-mass asymptotic at admissible heights.**  The symmetric mass is
`(1/π)·T log T·(1 + o(1))`. -/
theorem exists_xiSymmetricMass_admissible_close (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 4 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → (∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      |(xiSymmetricMass T : ℝ) - (1 / Real.pi) * (T * Real.log T)|
        ≤ ε * (T * Real.log T) := by
  obtain ⟨c, hc, hhoriz⟩ := exists_horizontal_xi_bound
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set δ : ℝ := ε * Real.pi / 8 with hδdef
  have hδ : 0 < δ := by positivity
  have hV := tendsto_vertical_ratio
  rw [Metric.tendsto_atTop] at hV
  obtain ⟨T₁, hT₁⟩ := hV δ hδ
  refine ⟨max (max T₁ (c / δ)) 4, le_max_right _ _, fun T hT hne => ?_⟩
  have hT4 : (4 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hTc : c / δ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTT₁ : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hTlog : (0 : ℝ) < T * Real.log T := by positivity
  set V : ℝ := ∫ y in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + (y : ℂ) * I)).re with hVdef
  set H : ℝ := ∫ x in (1 / 2 : ℝ)..2, (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im with hHdef
  have hmass := two_pi_mul_xiSymmetricMass hT0.le hne
  rw [← hVdef, ← hHdef] at hmass
  -- the vertical piece
  have hVclose : |V - (1 / 2) * (T * Real.log T)| ≤ δ * (T * Real.log T) := by
    have h := hT₁ T hTT₁
    rw [Real.dist_eq] at h
    have hkey : V - (1 / 2) * (T * Real.log T)
        = (V / (T * Real.log T) - 1 / 2) * (T * Real.log T) := by
      field_simp
    rw [hkey, abs_mul, abs_of_pos hTlog]
    exact mul_le_mul_of_nonneg_right h.le hTlog.le
  -- the horizontal piece
  have hHclose : |H| ≤ δ * (T * Real.log T) := by
    refine le_trans (hhoriz T hT4 hne) ?_
    have hcT : c ≤ δ * T := by
      rw [div_le_iff₀ hδ] at hTc
      linarith
    nlinarith [hlog1, hT0, hδ.le]
  -- combine
  have hexpand : (xiSymmetricMass T : ℝ) - (1 / Real.pi) * (T * Real.log T)
      = (2 / Real.pi) * (V - (1 / 2) * (T * Real.log T)) - (2 / Real.pi) * H := by
    field_simp at hmass ⊢
    linarith [hmass]
  rw [hexpand]
  have hpi3 : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi1 : 3.14 < Real.pi := Real.pi_gt_d2
  have hstep : |(2 / Real.pi) * (V - (1 / 2) * (T * Real.log T)) - (2 / Real.pi) * H|
      ≤ (2 / Real.pi) * (δ * (T * Real.log T)) + (2 / Real.pi) * (δ * (T * Real.log T)) := by
    refine le_trans (abs_sub _ _) ?_
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / Real.pi)]
    exact add_le_add (mul_le_mul_of_nonneg_left hVclose (by positivity))
      (mul_le_mul_of_nonneg_left hHclose (by positivity))
  refine le_trans hstep ?_
  have hval : (2 / Real.pi) * (δ * (T * Real.log T)) + (2 / Real.pi) * (δ * (T * Real.log T))
      = (ε / 2) * (T * Real.log T) := by
    rw [hδdef]
    field_simp
    ring
  rw [hval]
  nlinarith [hTlog, hε]

end RHTower

end
