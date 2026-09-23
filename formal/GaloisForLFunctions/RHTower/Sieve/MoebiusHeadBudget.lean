import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The Gallagher budget at the optimal cutoff

At the Gallagher cutoff `G = M/h` and any height `T₀ = G·ω` above it, the budget of
`Sieve/FibreWindowBridge.averagedMeanSquare_of_gallagherBudget` collapses to three independent
quantities: one vanishing with the window length, one with the height multiplier, and one which is
the relative size of the head mean square.  **No condition on the slope survives** — the trivial
mean value theorem's slope is already inside the budget.
-/

namespace RHTower.Sieve

noncomputable section

/-- **The budget, majorised.**  With `δ ≤ 2h/M` — the logarithmic window width against the length of
the sum — the whole Gallagher budget is at most `90/h + 60/ω + 9·B/M²`. -/
theorem headBudget_le {M δ h ω B : ℝ} (hM : 0 < M) (hh : 1 ≤ h) (hω : 1 ≤ ω)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 2 * h / M) (hB0 : 0 ≤ B) :
    (2 * δ ^ (2 : ℕ)
        * ((5 * Real.pi / 2 * M + 5 * Real.exp 1 / 2 * M * M / (M / h * ω)) * (M / h) + B)
      + (4 * (5 * Real.pi / 2 * M + 5 * Real.exp 1 / 2 * M * M / (M / h * ω))
            / (Real.pi ^ (2 : ℕ) * (M / h))
          + 4 * B / (3 * Real.pi ^ (2 : ℕ) * (M / h) ^ (2 : ℕ)))) / h ^ (2 : ℕ)
      ≤ 90 / h + 60 / ω + 9 * (B / M ^ (2 : ℕ)) := by
  have hh0 : (0 : ℝ) < h := lt_of_lt_of_le zero_lt_one hh
  have hω0 : (0 : ℝ) < ω := lt_of_lt_of_le zero_lt_one hω
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hπ4 : Real.pi ≤ 4 := Real.pi_le_four
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hMne : M ≠ 0 := ne_of_gt hM
  have hhne : h ≠ 0 := ne_of_gt hh0
  have hωne : ω ≠ 0 := ne_of_gt hω0
  have hπne : Real.pi ≠ 0 := ne_of_gt hπ0
  set S : ℝ := 5 * Real.pi / 2 * M + 5 * Real.exp 1 / 2 * M * h / ω with hSdef
  have hS0 : (0 : ℝ) ≤ S := by
    rw [hSdef]; positivity
  have hslope : 5 * Real.pi / 2 * M + 5 * Real.exp 1 / 2 * M * M / (M / h * ω) = S := by
    rw [hSdef]; field_simp
  rw [hslope]
  have hsplit : (2 * δ ^ (2 : ℕ) * (S * (M / h) + B)
      + (4 * S / (Real.pi ^ (2 : ℕ) * (M / h)) + 4 * B / (3 * Real.pi ^ (2 : ℕ) * (M / h) ^ (2 : ℕ)))) / h ^ (2 : ℕ)
      = 2 * δ ^ (2 : ℕ) * S * M / h ^ (3 : ℕ) + 2 * δ ^ (2 : ℕ) * B / h ^ (2 : ℕ)
        + 4 * S / (Real.pi ^ (2 : ℕ) * M * h) + 4 * B / (3 * Real.pi ^ (2 : ℕ) * M ^ (2 : ℕ)) := by
    field_simp
    ring
  rw [hsplit]
  -- the four terms
  have hδsq : δ ^ (2 : ℕ) ≤ 4 * h ^ (2 : ℕ) / M ^ (2 : ℕ) := by
    have := pow_le_pow_left₀ hδ0 hδ 2
    calc δ ^ (2 : ℕ) ≤ (2 * h / M) ^ (2 : ℕ) := this
      _ = 4 * h ^ (2 : ℕ) / M ^ (2 : ℕ) := by field_simp; ring
  have hT1 : 2 * δ ^ (2 : ℕ) * S * M / h ^ (3 : ℕ) ≤ 20 * Real.pi / h + 20 * Real.exp 1 / ω := by
    have hstep : 2 * δ ^ (2 : ℕ) * S * M / h ^ (3 : ℕ) ≤ 2 * (4 * h ^ (2 : ℕ) / M ^ (2 : ℕ)) * S * M / h ^ (3 : ℕ) := by
      have hpos : (0 : ℝ) ≤ 2 * S * M / h ^ (3 : ℕ) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hδsq hpos
      calc 2 * δ ^ (2 : ℕ) * S * M / h ^ (3 : ℕ) = 2 * S * M / h ^ (3 : ℕ) * δ ^ (2 : ℕ) := by ring
        _ ≤ 2 * S * M / h ^ (3 : ℕ) * (4 * h ^ (2 : ℕ) / M ^ (2 : ℕ)) := hmul
        _ = 2 * (4 * h ^ (2 : ℕ) / M ^ (2 : ℕ)) * S * M / h ^ (3 : ℕ) := by ring
    refine hstep.trans (le_of_eq ?_)
    rw [hSdef]
    field_simp
    ring
  have hT2 : 2 * δ ^ (2 : ℕ) * B / h ^ (2 : ℕ) ≤ 8 * (B / M ^ (2 : ℕ)) := by
    have hpos : (0 : ℝ) ≤ 2 * B / h ^ (2 : ℕ) := by positivity
    have hstep : 2 * δ ^ (2 : ℕ) * B / h ^ (2 : ℕ) ≤ 2 * (4 * h ^ (2 : ℕ) / M ^ (2 : ℕ)) * B / h ^ (2 : ℕ) := by
      have hmul := mul_le_mul_of_nonneg_left hδsq hpos
      calc 2 * δ ^ (2 : ℕ) * B / h ^ (2 : ℕ) = 2 * B / h ^ (2 : ℕ) * δ ^ (2 : ℕ) := by ring
        _ ≤ 2 * B / h ^ (2 : ℕ) * (4 * h ^ (2 : ℕ) / M ^ (2 : ℕ)) := hmul
        _ = 2 * (4 * h ^ (2 : ℕ) / M ^ (2 : ℕ)) * B / h ^ (2 : ℕ) := by ring
    refine hstep.trans (le_of_eq ?_)
    field_simp
    ring
  have hT3 : 4 * S / (Real.pi ^ (2 : ℕ) * M * h)
      = 10 / (Real.pi * h) + 10 * Real.exp 1 / (Real.pi ^ (2 : ℕ) * ω) := by
    rw [hSdef]
    field_simp
    ring
  have hT4 : 4 * B / (3 * Real.pi ^ (2 : ℕ) * M ^ (2 : ℕ)) ≤ B / M ^ (2 : ℕ) := by
    have hBM : (0 : ℝ) ≤ B / M ^ (2 : ℕ) := by positivity
    have hc : 4 / (3 * Real.pi ^ (2 : ℕ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [hπ3]
    have hfac : B / M ^ (2 : ℕ) - 4 * B / (3 * Real.pi ^ (2 : ℕ) * M ^ (2 : ℕ))
        = (1 - 4 / (3 * Real.pi ^ (2 : ℕ))) * (B / M ^ (2 : ℕ)) := by
      field_simp
    have hnn : 0 ≤ (1 - 4 / (3 * Real.pi ^ (2 : ℕ))) * (B / M ^ (2 : ℕ)) := by
      have hone : (0 : ℝ) ≤ 1 - 4 / (3 * Real.pi ^ (2 : ℕ)) := by linarith
      exact mul_nonneg hone hBM
    rw [← hfac] at hnn
    linarith
  -- numeric comparisons
  have hnum1 : 20 * Real.pi / h + 10 / (Real.pi * h) ≤ 90 / h := by
    have hkey : 10 / Real.pi ≤ 90 - 20 * Real.pi := by
      rw [div_le_iff₀ hπ0]
      nlinarith [hπ3, hπ4]
    have hnn : 0 ≤ (90 - (20 * Real.pi + 10 / Real.pi)) / h :=
      div_nonneg (by linarith) hh0.le
    have hdiff : (90 - (20 * Real.pi + 10 / Real.pi)) / h
        = 90 / h - (20 * Real.pi / h + 10 / (Real.pi * h)) := by
      field_simp
    rw [hdiff] at hnn
    linarith
  have hnum2 : 20 * Real.exp 1 / ω + 10 * Real.exp 1 / (Real.pi ^ (2 : ℕ) * ω) ≤ 60 / ω := by
    have hkey : 10 * Real.exp 1 / Real.pi ^ (2 : ℕ) ≤ 60 - 20 * Real.exp 1 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [he, he0, hπ3]
    have hnn : 0 ≤ (60 - (20 * Real.exp 1 + 10 * Real.exp 1 / Real.pi ^ (2 : ℕ))) / ω :=
      div_nonneg (by linarith) hω0.le
    have hdiff : (60 - (20 * Real.exp 1 + 10 * Real.exp 1 / Real.pi ^ (2 : ℕ))) / ω
        = 60 / ω - (20 * Real.exp 1 / ω + 10 * Real.exp 1 / (Real.pi ^ (2 : ℕ) * ω)) := by
      field_simp
    rw [hdiff] at hnn
    linarith
  linarith

/-- **The rough group, relative to `M²`.**  Turán's rough count `(M + 2|P|)/A` against the mean
value theorem: every term carries `1/A`, so a designated range of divergent harmonic mass makes the
whole group vanish. -/
theorem roughGroup_le {W M A cP : ℝ} (hW : 0 ≤ W) (hM : 0 < M) (hA : 0 < A) (hcP : 0 ≤ cP) :
    (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * M) * ((M + 2 * cP) / A) / M ^ (2 : ℕ)
      ≤ 10 * W / (A * M) + 20 * W * cP / (A * M ^ (2 : ℕ)) + 7 / A + 14 * cP / (A * M) := by
  have hπ4 : Real.pi ≤ 4 := Real.pi_le_four
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hcoef : 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * M ≤ 10 * W + 7 * M := by
    nlinarith [hW, hM.le, hπ4, he]
  have hmass : (0 : ℝ) ≤ (M + 2 * cP) / A := by positivity
  have hM2 : (0 : ℝ) < M ^ (2 : ℕ) := by positivity
  have hstep : (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * M) * ((M + 2 * cP) / A) / M ^ (2 : ℕ)
      ≤ (10 * W + 7 * M) * ((M + 2 * cP) / A) / M ^ (2 : ℕ) := by
    have hnum := mul_le_mul_of_nonneg_right hcoef hmass
    have hnn : (0 : ℝ) ≤ ((10 * W + 7 * M) * ((M + 2 * cP) / A)
        - (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * M) * ((M + 2 * cP) / A)) / M ^ (2 : ℕ) :=
      div_nonneg (by linarith) hM2.le
    have hdiff : ((10 * W + 7 * M) * ((M + 2 * cP) / A)
        - (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * M) * ((M + 2 * cP) / A)) / M ^ (2 : ℕ)
        = (10 * W + 7 * M) * ((M + 2 * cP) / A) / M ^ (2 : ℕ)
          - (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * M) * ((M + 2 * cP) / A) / M ^ (2 : ℕ) := by
      ring
    rw [hdiff] at hnn
    linarith
  refine hstep.trans (le_of_eq ?_)
  field_simp
  ring

end

end RHTower.Sieve
