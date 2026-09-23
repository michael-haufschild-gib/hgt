import GaloisForLFunctions.RHTower.PsiRatioImprove

/-!
# The ψ-ratio descent: the elementary prime number theorem

`∀ ε > 0, ∃ x₀, ∀ N ≥ x₀: |ψ(N) − N| ≤ ε·N`.

From the crude ratio `8`, the single-pass improvement is iterated with
parameters fixed by the target: `δ = κ = ε/8`, `ρ` with
`ρ(log(1/ρ)+3) ≤ ε/8` (so `ε' ≤ 3ε/8`), `Q` with `log Q > 40/δ + 2`,
and `x₁` large enough that the head leak `12b/x₁` eats at most half the
contraction.  While the ratio `b` exceeds `ε` the gap `b − ε' ≥ 5ε/8`
makes each pass drop `b` by the fixed amount `d = ερ/(64·log(2Q))`, so
after `⌈8/d⌉` passes the ratio is below `ε`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

/-- Small `ρ` with `ρ·(log(1/ρ) + 3) ≤ ε`: take `ρ = min(1/2, (ε/5)²)`,
since `ρ(log(1/ρ)+3) ≤ 2√ρ + 3ρ ≤ 5√ρ`. -/
theorem exists_rho_small {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ρ * (Real.log (1 / ρ) + 3) ≤ ε := by
  refine ⟨min (1 / 2) ((ε / 5) ^ (2 : ℕ)),
    lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
  have hρ0 : 0 < min (1 / 2) ((ε / 5) ^ (2 : ℕ)) :=
    lt_min (by norm_num) (by positivity)
  have hρ1 : min (1 / 2) ((ε / 5) ^ (2 : ℕ)) ≤ 1 :=
    le_trans (min_le_left _ _) (by norm_num)
  have hsρ : Real.sqrt (min (1 / 2) ((ε / 5) ^ (2 : ℕ))) ≤ ε / 5 := by
    have h2 := Real.sqrt_le_sqrt (min_le_right (1 / 2) ((ε / 5) ^ (2 : ℕ)))
    rwa [Real.sqrt_sq (by positivity)] at h2
  have hsρ0 : 0 < Real.sqrt (min (1 / 2) ((ε / 5) ^ (2 : ℕ))) :=
    Real.sqrt_pos.2 hρ0
  have hsρ1 : Real.sqrt (min (1 / 2) ((ε / 5) ^ (2 : ℕ))) ≤ 1 := by
    have h1 := Real.sqrt_le_sqrt hρ1
    rwa [Real.sqrt_one] at h1
  have hρs : min (1 / 2) ((ε / 5) ^ (2 : ℕ))
      = Real.sqrt (min (1 / 2) ((ε / 5) ^ (2 : ℕ)))
        * Real.sqrt (min (1 / 2) ((ε / 5) ^ (2 : ℕ))) :=
    (Real.mul_self_sqrt hρ0.le).symm
  have hlog : Real.log (1 / min (1 / 2) ((ε / 5) ^ (2 : ℕ)))
      ≤ 2 * (1 / Real.sqrt (min (1 / 2) ((ε / 5) ^ (2 : ℕ)))) := by
    have h1 := log_le_two_sqrt_psiRatioImprove
      (show (0 : ℝ) < 1 / min (1 / 2) ((ε / 5) ^ (2 : ℕ)) by positivity)
    have h2 : Real.sqrt (1 / min (1 / 2) ((ε / 5) ^ (2 : ℕ)))
        = 1 / Real.sqrt (min (1 / 2) ((ε / 5) ^ (2 : ℕ))) := by
      rw [one_div, Real.sqrt_inv]
      exact (one_div _).symm
    rwa [h2] at h1
  have hρle : min (1 / 2) ((ε / 5) ^ (2 : ℕ))
      ≤ Real.sqrt (min (1 / 2) ((ε / 5) ^ (2 : ℕ))) := by
    nlinarith [hρs, hsρ1, hsρ0]
  have h3 : min (1 / 2) ((ε / 5) ^ (2 : ℕ))
      * (2 * (1 / Real.sqrt (min (1 / 2) ((ε / 5) ^ (2 : ℕ)))))
      = 2 * Real.sqrt (min (1 / 2) ((ε / 5) ^ (2 : ℕ))) := by
    rw [show min (1 / 2) ((ε / 5) ^ (2 : ℕ))
        * (2 * (1 / Real.sqrt (min (1 / 2) ((ε / 5) ^ (2 : ℕ)))))
        = 2 * (min (1 / 2) ((ε / 5) ^ (2 : ℕ))
          / Real.sqrt (min (1 / 2) ((ε / 5) ^ (2 : ℕ)))) from by ring,
      Real.div_sqrt]
  have h4 : min (1 / 2) ((ε / 5) ^ (2 : ℕ))
      * (Real.log (1 / min (1 / 2) ((ε / 5) ^ (2 : ℕ))) + 3)
      ≤ min (1 / 2) ((ε / 5) ^ (2 : ℕ))
        * (2 * (1 / Real.sqrt (min (1 / 2) ((ε / 5) ^ (2 : ℕ)))) + 3) :=
    mul_le_mul_of_nonneg_left (by linarith) hρ0.le
  nlinarith [h3, h4, hρle, hsρ]

set_option maxHeartbeats 3200000 in
/-- **Elementary prime number theorem** (Erdős–Selberg):
`ψ(N) = N + o(N)`. -/
theorem psiRemainder_eventually_le {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℕ, ∀ N : ℕ, x₀ ≤ N → |psiRemainder N| ≤ ε * N := by
  -- parameters fixed by the target
  obtain ⟨ρ, hρ0, hρ1, hρε⟩ := exists_rho_small
    (show (0 : ℝ) < ε / 8 by linarith)
  obtain ⟨Q, hQ1, hQ⟩ : ∃ Q : ℕ, 1 ≤ Q ∧ 40 / (ε / 8) + 2 < Real.log Q := by
    obtain ⟨MQ, hMQ⟩ := exists_nat_log_ge (40 / (ε / 8) + 3)
    exact ⟨max MQ 1, le_max_right _ _,
      by linarith [hMQ (max MQ 1) (le_max_left _ _)]⟩
  have hLhalf : 1 / 2 ≤ Real.log ((2 * Q : ℕ) : ℝ) := by
    have h1 : Real.log 2 ≤ Real.log ((2 * Q : ℕ) : ℝ) := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast (by omega : 2 ≤ 2 * Q)
    linarith [Real.log_two_gt_d9]
  have hL0 : (0 : ℝ) < Real.log ((2 * Q : ℕ) : ℝ) := by linarith
  obtain ⟨x₁, hx₁8, hx₁ρ, hx₁Q, hx₁gap⟩ :
      ∃ x₁ : ℕ, 8 ≤ x₁ ∧ 8 / ρ ≤ (x₁ : ℝ)
        ∧ Real.log ((2 * Q : ℕ) : ℝ) + 2 ≤ 2 * Real.log x₁
        ∧ 6144 * Real.log ((2 * Q : ℕ) : ℝ) / (ε * ρ) ≤ (x₁ : ℝ) := by
    obtain ⟨Mx, hMx⟩ := exists_nat_log_ge
      (Real.log ((2 * Q : ℕ) : ℝ) / 2 + 1)
    refine ⟨max (max Mx 8) (max ⌈8 / ρ⌉₊
      ⌈6144 * Real.log ((2 * Q : ℕ) : ℝ) / (ε * ρ)⌉₊), ?_, ?_, ?_, ?_⟩
    · exact le_trans (le_max_right Mx 8) (le_max_left _ _)
    · have h1 := Nat.le_ceil (8 / ρ)
      have h2 : ⌈8 / ρ⌉₊ ≤ max (max Mx 8) (max ⌈8 / ρ⌉₊
          ⌈6144 * Real.log ((2 * Q : ℕ) : ℝ) / (ε * ρ)⌉₊) :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      have h3 : ((⌈8 / ρ⌉₊ : ℕ) : ℝ) ≤ ((max (max Mx 8) (max ⌈8 / ρ⌉₊
          ⌈6144 * Real.log ((2 * Q : ℕ) : ℝ) / (ε * ρ)⌉₊) : ℕ) : ℝ) := by
        exact_mod_cast h2
      linarith
    · have h1 := hMx (max (max Mx 8) (max ⌈8 / ρ⌉₊
        ⌈6144 * Real.log ((2 * Q : ℕ) : ℝ) / (ε * ρ)⌉₊))
        (le_trans (le_max_left Mx 8) (le_max_left _ _))
      linarith
    · have h1 := Nat.le_ceil
        (6144 * Real.log ((2 * Q : ℕ) : ℝ) / (ε * ρ))
      have h2 : ⌈6144 * Real.log ((2 * Q : ℕ) : ℝ) / (ε * ρ)⌉₊
          ≤ max (max Mx 8) (max ⌈8 / ρ⌉₊
            ⌈6144 * Real.log ((2 * Q : ℕ) : ℝ) / (ε * ρ)⌉₊) :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      have h3 : ((⌈6144 * Real.log ((2 * Q : ℕ) : ℝ) / (ε * ρ)⌉₊ : ℕ) : ℝ)
          ≤ ((max (max Mx 8) (max ⌈8 / ρ⌉₊
            ⌈6144 * Real.log ((2 * Q : ℕ) : ℝ) / (ε * ρ)⌉₊) : ℕ) : ℝ) := by
        exact_mod_cast h2
      linarith
  have hx₁R : (0 : ℝ) < x₁ := by
    exact_mod_cast (by omega : 0 < x₁)
  -- the `ε'`-envelope
  have hρterm0 : 0 ≤ ρ * (Real.log (1 / ρ) + 3) := by
    apply mul_nonneg hρ0.le
    have := Real.log_nonneg
      (show (1 : ℝ) ≤ 1 / ρ by rw [le_div_iff₀ hρ0]; linarith)
    linarith
  -- the descent
  have hdescent : ∀ k : ℕ, ∃ b : ℝ, ∃ y : ℕ, 0 < b
      ∧ (b ≤ 8 - k * (ε * ρ / (64 * Real.log ((2 * Q : ℕ) : ℝ))) ∨ b ≤ ε)
      ∧ ∀ N : ℕ, y ≤ N → |psiRemainder N| ≤ b * N := by
    intro k
    induction k with
    | zero =>
      refine ⟨8, 0, by norm_num, Or.inl (by norm_num), fun N _ => ?_⟩
      exact abs_psiRemainder_le N
    | succ k ih =>
      obtain ⟨b, y, hb0, hbc, hbound⟩ := ih
      rcases le_or_gt b ε with hbε | hbε
      · exact ⟨b, y, hb0, Or.inr hbε, hbound⟩
      · have hd0 : (0 : ℝ)
            < ε * ρ / (64 * Real.log ((2 * Q : ℕ) : ℝ)) := by positivity
        have hbk : b ≤ 8
            - k * (ε * ρ / (64 * Real.log ((2 * Q : ℕ) : ℝ))) := by
          rcases hbc with h | h
          · exact h
          · linarith
        have hb8 : b ≤ 8 := by
          have h1 : (0 : ℝ)
              ≤ k * (ε * ρ / (64 * Real.log ((2 * Q : ℕ) : ℝ))) :=
            mul_nonneg (Nat.cast_nonneg k) hd0.le
          linarith
        have hεfb : ε / 8 + ρ * (Real.log (1 / ρ) + 3) + ε / 8 < b := by
          linarith [hρε]
        obtain ⟨x₀', himp⟩ := psi_ratio_improve hb0
          (show (0 : ℝ) < ε / 8 by linarith) hρ0 hρ1
          (show (0 : ℝ) < ε / 8 by linarith) hQ1 hQ hx₁8 hx₁ρ hx₁Q
          hεfb hbound
        -- the contraction term dominates the head leak
        have hAge : 5 * (ε * ρ / (128 * Real.log ((2 * Q : ℕ) : ℝ)))
            ≤ (b - (ε / 8 + ρ * (Real.log (1 / ρ) + 3) + ε / 8)) * ρ
              / (16 * Real.log ((2 * Q : ℕ) : ℝ)) := by
          have h1 : 5 * ε / 8
              ≤ b - (ε / 8 + ρ * (Real.log (1 / ρ) + 3) + ε / 8) := by
            linarith [hρε]
          have h2 : 5 * ε / 8 * ρ
              ≤ (b - (ε / 8 + ρ * (Real.log (1 / ρ) + 3) + ε / 8)) * ρ :=
            mul_le_mul_of_nonneg_right h1 hρ0.le
          have h3 := div_le_div_of_nonneg_right h2
            (by linarith : (0 : ℝ) ≤ 16 * Real.log ((2 * Q : ℕ) : ℝ))
          have h4 : 5 * ε / 8 * ρ / (16 * Real.log ((2 * Q : ℕ) : ℝ))
              = 5 * (ε * ρ / (128 * Real.log ((2 * Q : ℕ) : ℝ))) := by
            ring
          linarith
        have hAle : (b - (ε / 8 + ρ * (Real.log (1 / ρ) + 3) + ε / 8)) * ρ
            / (16 * Real.log ((2 * Q : ℕ) : ℝ)) ≤ b / 16 := by
          have h1 : (b - (ε / 8 + ρ * (Real.log (1 / ρ) + 3) + ε / 8)) * ρ
              ≤ b * (1 / 2) := by
            apply mul_le_mul (by linarith [hρterm0]) hρ1 hρ0.le hb0.le
          have h2 := div_le_div_of_nonneg_right h1
            (by linarith : (0 : ℝ) ≤ 16 * Real.log ((2 * Q : ℕ) : ℝ))
          have h3 : b * (1 / 2) / (16 * Real.log ((2 * Q : ℕ) : ℝ))
              ≤ b * (1 / 2) / 8 := by
            apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
            linarith
          have h4 : b * (1 / 2) / 8 = b / 16 := by ring
          linarith
        have hBle : 12 * b / (x₁ : ℝ)
            ≤ 2 * (ε * ρ / (128 * Real.log ((2 * Q : ℕ) : ℝ))) := by
          have hgap0 : (0 : ℝ)
              < 6144 * Real.log ((2 * Q : ℕ) : ℝ) / (ε * ρ) := by
            positivity
          have h1 : 12 * b ≤ 96 := by linarith
          have h2 : 12 * b / (x₁ : ℝ) ≤ 96 / (x₁ : ℝ) :=
            div_le_div_of_nonneg_right h1 hx₁R.le
          have h3 : 96 / (x₁ : ℝ)
              ≤ 96 / (6144 * Real.log ((2 * Q : ℕ) : ℝ) / (ε * ρ)) :=
            div_le_div_of_nonneg_left (by norm_num) hgap0 hx₁gap
          have h4 : 96 / (6144 * Real.log ((2 * Q : ℕ) : ℝ) / (ε * ρ))
              = 2 * (ε * ρ / (128 * Real.log ((2 * Q : ℕ) : ℝ))) := by
            field_simp
            ring
          linarith
        have hB0 : 0 ≤ 12 * b / (x₁ : ℝ) := by positivity
        refine ⟨b - (b - (ε / 8 + ρ * (Real.log (1 / ρ) + 3) + ε / 8)) * ρ
            / (16 * Real.log ((2 * Q : ℕ) : ℝ)) + 12 * b / (x₁ : ℝ),
          x₀', ?_, Or.inl ?_, himp⟩
        · linarith [hAle, hB0, hb0]
        · have e64 : ε * ρ / (64 * Real.log ((2 * Q : ℕ) : ℝ))
              = 2 * (ε * ρ / (128 * Real.log ((2 * Q : ℕ) : ℝ))) := by
            ring
          have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
          rw [hcast]
          linarith [hAge, hBle, hbk, e64]
  -- extract the terminal ratio
  have hd0 : (0 : ℝ) < ε * ρ / (64 * Real.log ((2 * Q : ℕ) : ℝ)) := by
    positivity
  obtain ⟨b, y, hb0, hbc, hbound⟩ := hdescent
    ⌈8 / (ε * ρ / (64 * Real.log ((2 * Q : ℕ) : ℝ)))⌉₊
  have hbε : b ≤ ε := by
    rcases hbc with h | h
    · exfalso
      have h1 := Nat.le_ceil
        (8 / (ε * ρ / (64 * Real.log ((2 * Q : ℕ) : ℝ))))
      have h2 : (8 : ℝ)
          ≤ (⌈8 / (ε * ρ / (64 * Real.log ((2 * Q : ℕ) : ℝ)))⌉₊ : ℝ)
            * (ε * ρ / (64 * Real.log ((2 * Q : ℕ) : ℝ))) := by
        rw [div_le_iff₀ hd0] at h1
        exact h1
      linarith
    · exact h
  exact ⟨y, fun N hN => le_trans (hbound N hN)
    (mul_le_mul_of_nonneg_right hbε (Nat.cast_nonneg N))⟩

end RHTower
