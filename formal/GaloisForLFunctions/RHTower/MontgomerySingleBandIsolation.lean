import GaloisForLFunctions.RHTower.MontgomerySingleBandWindow
import GaloisForLFunctions.RHTower.MontgomeryPairCorrelationUniform

/-!
# The single-band isolation law

If, at height `T`, every zero copy with real part above `1/2 + δ₀` lies in one band
`[σ, σ + τ/log T]` of real parts with `σ ≥ 1/2 + 4δ₀`, and the ordinates of that set are
`D`-separated in mean-spacing units, then the set has at most `C · T^{1 − 2a(σ−1/2)} log T`
elements, for every scale window `[a, a+ℓ] ⊂ (0,1)` with `a ≥ 2(a+ℓ)/3` on which the
Montgomery–Vaughan band constant is bounded below by `κ > 0`.  Unconditional: the upper bound is
the uniform leading-order asymptotic of Montgomery's form, the lower bound is the band block over
the window, and the cross terms are the pointwise Lorentzian budget.
-/

open Filter Topology Set

namespace RHTower

/-- **Single-band isolation law.** -/
theorem eventually_card_singleBand_le {a ℓ σ δ₀ D τ κ : ℝ}
    (ha : 0 < a) (hℓ : 0 < ℓ) (hab : a + ℓ < 1) (hwin : 2 * (a + ℓ) ≤ 3 * a)
    (hδ₀ : 0 < δ₀) (hσ : 1 / 2 + 4 * δ₀ ≤ σ) (hD : 0 < D) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hκ : 0 < κ) (hc : ∀ N : ℕ, κ ≤ mvBandConstant ℓ D τ (N + 1) N) :
    ∀ᶠ T : ℝ in atTop, ∀ A : Finset XiZeroCopy, A ⊆ zeroWindow T →
      (∀ j ∈ A, σ ≤ (j.1 : ℂ).re ∧ (j.1 : ℂ).re ≤ σ + τ / Real.log T) →
      (∀ k ∈ zeroWindow T \ A, (k.1 : ℂ).re ≤ 1 / 2 + δ₀) →
      (∀ j ∈ A, ∀ k ∈ A, j ≠ k → D ≤ |bandFreq T j - bandFreq T k|) →
      (A.card : ℝ) ≤ (ℓ * Real.exp 3 / (Real.pi * κ)) *
        T ^ (1 - 2 * a * (σ - 1 / 2)) * Real.log T := by
  classical
  set b := a + ℓ with hb
  set δ := σ - 1 / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδ₀δ : 4 * δ₀ ≤ δ := by rw [hδ]; linarith
  have hb0 : 0 < b := by rw [hb]; linarith
  have hb1 : b < 1 := hab
  have hab' : a ≤ b := by rw [hb]; linarith
  set η := 2 * a * δ - b * (δ₀ + δ) with hη
  have hηpos : 0 < η := by
    rw [hη]
    have : 4 * b ≤ 6 * a := by rw [hb]; linarith
    nlinarith [hδpos, hδ₀δ, hb0]
  set C₀ := xiLineTwoLogDerivConstant with hC₀
  have hC₀0 : 0 ≤ C₀ := xiLineTwoLogDerivConstant_nonneg
  set ε₁ : ℝ := Real.exp (-3) * κ / (192 * Real.exp τ) with hε₁
  have hε₁pos : 0 < ε₁ := by positivity
  -- eventual facts
  have E1 := eventually_montgomeryForm_div_leadingOrder_uniform ha hab' hb1 (one_pos)
  have E2 := eventually_log_bounds
  have E3 := (tendsto_log_pow_div_rpow 1 hηpos).eventually (eventually_le_nhds hε₁pos)
  have E4 := Real.tendsto_log_atTop.eventually_ge_atTop C₀
  filter_upwards [E1, E2, E3, E4, eventually_gt_atTop (1 : ℝ)] with T e1 e2 e3 e4 hT1
  intro A hA hband hR hsep
  obtain ⟨hl1, _, _, hl4⟩ := e2
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT1
  set L := Real.log T with hLdef
  set N : ℝ := (A.card : ℝ) with hN
  have hN0 : 0 ≤ N := by positivity
  -- (i) the band block over the window
  have hcK := hc A.card
  have hwindow := singleBand_block_window_ge A hT1 hD hℓ.le ha.le hab.le hτ0 hτ1 (by linarith)
    hband hsep (K := A.card + 1) (by omega) (le_trans hκ.le hcK)
  have hEexp : Real.exp (2 * (a * (σ - 1 / 2) * Real.log T)) = T ^ (2 * a * δ) := by
    rw [Real.rpow_def_of_pos hT0, hδ]
    congr 1
    ring
  rw [hEexp, ← hb] at hwindow
  have hlow : 2 * Real.exp (-3) * T ^ (2 * a * δ) * κ * N
      ≤ ∫ α in a..b, (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re := by
    refine le_trans ?_ hwindow
    have h0 : 0 ≤ 2 * Real.exp (-3) * T ^ (2 * a * δ) * N := by positivity
    calc 2 * Real.exp (-3) * T ^ (2 * a * δ) * κ * N
        = (2 * Real.exp (-3) * T ^ (2 * a * δ) * N) * κ := by ring
      _ ≤ (2 * Real.exp (-3) * T ^ (2 * a * δ) * N) * mvBandConstant ℓ D τ (A.card + 1) A.card :=
          mul_le_mul_of_nonneg_left hcK h0
      _ = _ := by ring
  -- (ii) pointwise upper bound for the band block at every scale of the window
  have hW : windowLog T ≤ 3 * L := by
    unfold windowLog
    linarith
  have hpt : ∀ α ∈ Icc a b,
      (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        ≤ T / Real.pi * L + 192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)) := by
    intro α hα
    have hα0 : 0 ≤ α := ha.le.trans hα.1
    have hx1 : 1 ≤ T ^ α := Real.one_le_rpow hT1.le hα0
    have hx0 : 0 < T ^ α := by linarith
    -- capstone upper bound
    have hF : (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        ≤ T / Real.pi * L := by
      have h := e1 α hα
      have hNα : 0 < (T / (2 * Real.pi)) * (α * L) := by
        have : 0 < α := lt_of_lt_of_le ha hα.1
        positivity
      rw [abs_lt] at h
      have h2 := h.2
      rw [div_sub_one (ne_of_gt hNα), div_lt_iff₀ hNα] at h2
      have hαL : α * L ≤ L := by
        have : α ≤ 1 := by linarith [hα.2]
        nlinarith
      calc (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
          ≤ 1 * (T / (2 * Real.pi) * (α * L)) + T / (2 * Real.pi) * (α * L) := by linarith
        _ = T / Real.pi * (α * L) := by field_simp; ring
        _ ≤ T / Real.pi * L := by gcongr
    -- block split
    have hRα : ∀ k ∈ zeroWindow T \ A, zeroAmp (T ^ α) k ≤ (T ^ α) ^ δ₀ := by
      intro k hk
      unfold zeroAmp
      apply Real.rpow_le_rpow_of_exponent_le hx1
      linarith [hR k hk]
    have hsplit := montgomeryForm_block_split hx0 A hA (Θ := (T ^ α) ^ δ₀) (by positivity) hRα
    -- amplitudes on the band
    have hamp : ∑ j ∈ A, zeroAmp (T ^ α) j ≤ N * (T ^ (b * δ) * Real.exp τ) := by
      have hone : ∀ j ∈ A, zeroAmp (T ^ α) j ≤ T ^ (b * δ) * Real.exp τ := by
        intro j hj
        obtain ⟨_, hj2⟩ := hband j hj
        unfold zeroAmp
        rw [← Real.rpow_mul hT0.le]
        have hexp : α * ((j.1 : ℂ).re - 1 / 2) ≤ b * δ + τ / L := by
          have h1 : (j.1 : ℂ).re - 1 / 2 ≤ δ + τ / L := by rw [hδ]; linarith
          have h2 : 0 ≤ δ + τ / L := by positivity
          calc α * ((j.1 : ℂ).re - 1 / 2) ≤ α * (δ + τ / L) := by gcongr
            _ ≤ b * (δ + τ / L) := mul_le_mul_of_nonneg_right hα.2 h2
            _ = b * δ + b * (τ / L) := by ring
            _ ≤ b * δ + τ / L := by
                have : b * (τ / L) ≤ 1 * (τ / L) :=
                  mul_le_mul_of_nonneg_right hb1.le (by positivity)
                linarith
        calc T ^ (α * ((j.1 : ℂ).re - 1 / 2)) ≤ T ^ (b * δ + τ / L) :=
              Real.rpow_le_rpow_of_exponent_le hT1.le hexp
          _ = T ^ (b * δ) * T ^ (τ / L) := Real.rpow_add hT0 _ _
          _ = T ^ (b * δ) * Real.exp τ := by
              congr 1
              rw [Real.rpow_def_of_pos hT0, ← hLdef]
              congr 1
              field_simp
      calc ∑ j ∈ A, zeroAmp (T ^ α) j ≤ ∑ _j ∈ A, T ^ (b * δ) * Real.exp τ :=
            Finset.sum_le_sum hone
        _ = N * (T ^ (b * δ) * Real.exp τ) := by
            rw [Finset.sum_const, nsmul_eq_mul, hN]
    have hΘ : (T ^ α) ^ δ₀ ≤ T ^ (b * δ₀) := by
      rw [← Real.rpow_mul hT0.le]
      apply Real.rpow_le_rpow_of_exponent_le hT1.le
      exact mul_le_mul_of_nonneg_right hα.2 hδ₀.le
    have hcross : 64 * (T ^ α) ^ δ₀ * windowLog T * ∑ j ∈ A, zeroAmp (T ^ α) j
        ≤ 192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)) := by
      have hsum0 : 0 ≤ ∑ j ∈ A, zeroAmp (T ^ α) j :=
        Finset.sum_nonneg fun j _ => zeroAmp_nonneg hx0.le j
      have hW0 : 0 ≤ windowLog T := windowLog_nonneg hT0.le
      calc 64 * (T ^ α) ^ δ₀ * windowLog T * ∑ j ∈ A, zeroAmp (T ^ α) j
          ≤ 64 * T ^ (b * δ₀) * (3 * L) * (N * (T ^ (b * δ) * Real.exp τ)) := by
            gcongr
        _ = 192 * Real.exp τ * L * N * (T ^ (b * δ₀) * T ^ (b * δ)) := by ring
        _ = 192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)) := by
            rw [← Real.rpow_add hT0, show b * δ₀ + b * δ = b * (δ₀ + δ) by ring]
    have h1 := sub_le_iff_le_add.mp hsplit
    calc (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        ≤ (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
          + 64 * (T ^ α) ^ δ₀ * windowLog T * ∑ j ∈ A, zeroAmp (T ^ α) j := h1
      _ ≤ T / Real.pi * L + 192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)) := add_le_add hF hcross
  -- (iii) integrate the pointwise bound
  have hcontF := continuous_montgomeryForm_rpow A hT0
  have hup : (∫ α in a..b, (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re)
      ≤ ℓ * (T / Real.pi * L + 192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ))) := by
    have this : (∫ α in a..b, (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re)
        ≤ ∫ _α in a..b, (T / Real.pi * L + 192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ))) :=
      intervalIntegral.integral_mono_on hab' (hcontF.intervalIntegrable _ _)
        intervalIntegrable_const hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have hba : b - a = ℓ := by rw [hb]; ring
    rw [hba] at this
    exact this
  -- (iv) the cross term is dominated by the detection term
  have hgap : 192 * Real.exp τ * L * T ^ (b * (δ₀ + δ)) ≤ Real.exp (-3) * κ * T ^ (2 * a * δ) := by
    have hpow : T ^ (2 * a * δ) = T ^ η * T ^ (b * (δ₀ + δ)) := by
      rw [← Real.rpow_add hT0, hη]; ring_nf
    rw [hpow]
    have hTη : 0 < T ^ η := Real.rpow_pos_of_pos hT0 η
    have hTb : 0 < T ^ (b * (δ₀ + δ)) := Real.rpow_pos_of_pos hT0 _
    have hlogT : L ≤ ε₁ * T ^ η := by
      have h := e3
      simp only [pow_one] at h
      rwa [div_le_iff₀ hTη] at h
    have : 192 * Real.exp τ * L ≤ Real.exp (-3) * κ * T ^ η := by
      calc 192 * Real.exp τ * L ≤ 192 * Real.exp τ * (ε₁ * T ^ η) := by gcongr
        _ = Real.exp (-3) * κ * T ^ η := by
            rw [hε₁]; field_simp
    calc 192 * Real.exp τ * L * T ^ (b * (δ₀ + δ))
        ≤ Real.exp (-3) * κ * T ^ η * T ^ (b * (δ₀ + δ)) := by gcongr
      _ = _ := by ring
  -- conclude
  have hmain : Real.exp (-3) * κ * T ^ (2 * a * δ) * N ≤ ℓ * (T / Real.pi * L) := by
    have h1 : 2 * Real.exp (-3) * T ^ (2 * a * δ) * κ * N
        ≤ ℓ * (T / Real.pi * L) + ℓ * (192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ))) := by
      linarith only [hlow, hup]
    have h2 : ℓ * (192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)))
        ≤ Real.exp (-3) * κ * T ^ (2 * a * δ) * N := by
      have hℓ1 : ℓ ≤ 1 := by linarith
      calc ℓ * (192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)))
          = ℓ * N * (192 * Real.exp τ * L * T ^ (b * (δ₀ + δ))) := by ring
        _ ≤ 1 * N * (Real.exp (-3) * κ * T ^ (2 * a * δ)) := by
            gcongr
        _ = _ := by ring
    linarith only [h1, h2]
  have hTpow : 0 < T ^ (2 * a * δ) := Real.rpow_pos_of_pos hT0 _
  have hfinal : N ≤ (ℓ * Real.exp 3 / (Real.pi * κ)) * (T / T ^ (2 * a * δ)) * L := by
    have hpos : 0 < Real.exp (-3) * κ * T ^ (2 * a * δ) := by positivity
    rw [show Real.exp (-3) * κ * T ^ (2 * a * δ) * N = N * (Real.exp (-3) * κ * T ^ (2 * a * δ)) by ring,
      ← le_div_iff₀ hpos] at hmain
    refine hmain.trans (le_of_eq ?_)
    rw [Real.exp_neg]
    field_simp
  have hdiv : T / T ^ (2 * a * δ) = T ^ (1 - 2 * a * δ) := by
    rw [Real.rpow_sub hT0, Real.rpow_one]
  rw [hdiv] at hfinal
  exact hfinal

end RHTower
