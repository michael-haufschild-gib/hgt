import GaloisForLFunctions.RHTower.MontgomeryMultiBandWindow
import GaloisForLFunctions.RHTower.MontgomeryPairCorrelationUniform

/-!
# The dominant-band isolation law

Several bands of off-line zeros (real parts in `[σ_i, σ_i + τ/log T]`), pairwise disjoint, with
`D`-separated union, all other zeros within `δ₀` of the line.  If band `i₀` dominates the family at
both ends of a scale window `[a, a+ℓ]` — in the Montgomery–Vaughan sense that the other bands'
endpoint-weighted upper budgets are at most a quarter of `i₀`'s lower budget — and the family's
amplitude mass at the top scale is at most twice that of band `i₀`, then
`N_{i₀} ≤ (4ℓe³/(πκ)) T^{1 − 2a(σ_{i₀}−1/2)} log T`.
-/

open Filter Topology Set

namespace RHTower

/-- **Dominant-band isolation law.** -/
theorem eventually_card_dominantBand_le {a ℓ δ₀ D τ κc : ℝ}
    (ha : 0 < a) (hℓ : 0 < ℓ) (hab : a + ℓ < 1) (hwin : 2 * (a + ℓ) ≤ 3 * a)
    (hδ₀ : 0 < δ₀) (hD : 0 < D) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hκ : 0 < κc) (hc : ∀ N : ℕ, κc ≤ mvBandConstant ℓ D τ (N + 1) N) :
    ∀ᶠ T : ℝ in atTop, ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : κ → Finset XiZeroCopy)
      (σ : κ → ℝ) (i₀ : κ), (Set.univ : Set κ).PairwiseDisjoint A →
      Finset.univ.biUnion A ⊆ zeroWindow T → 1 / 2 + 4 * δ₀ ≤ σ i₀ → (∀ i, 1 / 2 ≤ σ i) →
      (∀ i, ∀ j ∈ A i, σ i ≤ (j.1 : ℂ).re ∧ (j.1 : ℂ).re ≤ σ i + τ / Real.log T) →
      (∀ k ∈ zeroWindow T \ Finset.univ.biUnion A, (k.1 : ℂ).re ≤ 1 / 2 + δ₀) →
      (∀ j ∈ Finset.univ.biUnion A, ∀ k ∈ Finset.univ.biUnion A, j ≠ k →
        D ≤ |bandFreq T j - bandFreq T k|) →
      ((Fintype.card κ : ℝ) * ∑ i ∈ Finset.univ.erase i₀,
          bandScalarSq T a (a + ℓ) (σ i₀) (σ i) *
            (mvBandUpperConstant ℓ D τ ((A i).card + 1) (A i).card * (Real.exp 1 * (A i).card))
        ≤ 1 / 4 * (κc * (Real.exp (-1) * (A i₀).card))) →
      (∑ i, ((A i).card : ℝ) * T ^ ((a + ℓ) * (σ i - 1 / 2))
        ≤ 2 * (A i₀).card * T ^ ((a + ℓ) * (σ i₀ - 1 / 2))) →
      ((A i₀).card : ℝ) ≤ (4 * ℓ * Real.exp 3 / (Real.pi * κc)) *
        T ^ (1 - 2 * a * (σ i₀ - 1 / 2)) * Real.log T := by
  classical
  set b := a + ℓ with hb
  have hb0 : 0 < b := by rw [hb]; linarith
  have hb1 : b < 1 := hab
  have hab' : a ≤ b := by rw [hb]; linarith
  set C₀ := xiLineTwoLogDerivConstant with hC₀
  have hC₀0 : 0 ≤ C₀ := xiLineTwoLogDerivConstant_nonneg
  -- the exponent gap depends on `σ i₀`, which is quantified inside; we prove the eventual
  -- statement for each `σ`-value through a uniform gap in `δ₀`
  have hgapmin : ∀ δ : ℝ, 4 * δ₀ ≤ δ → b * δ / 12 ≤ 2 * a * δ - b * (δ₀ + δ) := by
    intro δ hδ
    have : 4 * b ≤ 6 * a := by rw [hb]; linarith
    nlinarith [hδ₀, hb0]
  set η₀ : ℝ := b * (4 * δ₀) / 12 with hη₀
  have hη₀pos : 0 < η₀ := by rw [hη₀]; positivity
  set ε₁ : ℝ := Real.exp (-3) * κc / (1536 * Real.exp τ) with hε₁
  have hε₁pos : 0 < ε₁ := by positivity
  -- eventual facts, uniform in the configuration
  have E1 := eventually_montgomeryForm_div_leadingOrder_uniform ha hab' hb1 (one_pos)
  have E2 := eventually_log_bounds
  have E3 := (tendsto_log_pow_div_rpow 1 hη₀pos).eventually (eventually_le_nhds hε₁pos)
  have E4 := Real.tendsto_log_atTop.eventually_ge_atTop C₀
  filter_upwards [E1, E2, E3, E4, eventually_gt_atTop (1 : ℝ)] with T e1 e2 e3 e4 hT1
  intro κ _ _ A σ i₀ hdisj hU hσ hσall hband hR hsep hdom hmass
  obtain ⟨hl1, _, _, hl4⟩ := e2
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT1
  set L := Real.log T with hLdef
  obtain ⟨U, hUdef⟩ : ∃ U : Finset XiZeroCopy, U = Finset.univ.biUnion A := ⟨_, rfl⟩
  rw [← hUdef] at hU hR
  set δ := σ i₀ - 1 / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδ₀δ : 4 * δ₀ ≤ δ := by rw [hδ]; linarith
  set η := 2 * a * δ - b * (δ₀ + δ) with hη
  have hηη₀ : η₀ ≤ η := by
    rw [hη, hη₀]
    have := hgapmin δ hδ₀δ
    have h2 : b * (4 * δ₀) / 12 ≤ b * δ / 12 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hδ₀δ hb0.le
    linarith
  set N : ℝ := ((A i₀).card : ℝ) with hN
  have hN0 : 0 ≤ N := by positivity
  -- (i) the band block over the window
  have hcK := hc (A i₀).card
  have hwindow := multiBand_block_window_ge A hdisj σ i₀ hT1 hD hℓ.le ha.le hab.le hτ0 hτ1
    (by linarith) hband hsep (K := fun i => (A i).card + 1) (fun i => by omega)
    (le_trans hκ.le hcK)
  have hEexp : Real.exp (2 * (a * (σ i₀ - 1 / 2) * Real.log T)) = T ^ (2 * a * δ) := by
    rw [Real.rpow_def_of_pos hT0, hδ]
    congr 1
    ring
  rw [hEexp, ← hb, ← hUdef] at hwindow
  have hbracket : 1 / 4 * (κc * (Real.exp (-1) * N))
      ≤ 1 / 2 * (mvBandConstant ℓ D τ ((A i₀).card + 1) (A i₀).card * (Real.exp (-1) * N))
        - (Fintype.card κ : ℝ) * ∑ i ∈ Finset.univ.erase i₀,
            bandScalarSq T a b (σ i₀) (σ i) *
              (mvBandUpperConstant ℓ D τ ((A i).card + 1) (A i).card * (Real.exp 1 * (A i).card)) := by
    have h1 : κc * (Real.exp (-1) * N)
        ≤ mvBandConstant ℓ D τ ((A i₀).card + 1) (A i₀).card * (Real.exp (-1) * N) :=
      mul_le_mul_of_nonneg_right hcK (by positivity)
    linarith [hdom, h1]
  have hlow : 1 / 2 * Real.exp (-3) * T ^ (2 * a * δ) * κc * N
      ≤ ∫ α in a..b, (montgomeryForm U (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re := by
    refine le_trans ?_ hwindow
    have hE0 : 0 ≤ T ^ (2 * a * δ) := Real.rpow_nonneg hT0.le _
    have h3 : Real.exp (-3) = Real.exp (-2) * Real.exp (-1) := by
      rw [← Real.exp_add]; norm_num
    rw [h3]
    have := mul_le_mul_of_nonneg_left hbracket (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.exp (-2)) hE0)
    calc 1 / 2 * (Real.exp (-2) * Real.exp (-1)) * T ^ (2 * a * δ) * κc * N
        = 2 * Real.exp (-2) * T ^ (2 * a * δ) * (1 / 4 * (κc * (Real.exp (-1) * N))) := by ring
      _ ≤ 2 * Real.exp (-2) * T ^ (2 * a * δ) * (1 / 2 *
          (mvBandConstant ℓ D τ ((A i₀).card + 1) (A i₀).card * (Real.exp (-1) * N))
          - (Fintype.card κ : ℝ) * ∑ i ∈ Finset.univ.erase i₀,
              bandScalarSq T a b (σ i₀) (σ i) *
                (mvBandUpperConstant ℓ D τ ((A i).card + 1) (A i).card *
                  (Real.exp 1 * (A i).card))) := this
      _ = _ := by ring
  -- (ii) pointwise upper bound for the union block at every scale of the window
  have hW : windowLog T ≤ 3 * L := by
    unfold windowLog
    linarith
  have hpt : ∀ α ∈ Icc a b,
      (montgomeryForm U (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        ≤ T / Real.pi * L + 384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)) := by
    intro α hα
    have hα0 : 0 ≤ α := ha.le.trans hα.1
    have hx1 : 1 ≤ T ^ α := Real.one_le_rpow hT1.le hα0
    have hx0 : 0 < T ^ α := by linarith
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
        have : α ≤ 1 := by linarith only [hα.2, hab]
        exact mul_le_of_le_one_left hL.le this
      calc (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
          ≤ 1 * (T / (2 * Real.pi) * (α * L)) + T / (2 * Real.pi) * (α * L) := by
            linarith only [h2]
        _ = T / Real.pi * (α * L) := by ring
        _ ≤ T / Real.pi * L := by gcongr
    have hRα : ∀ k ∈ zeroWindow T \ U, zeroAmp (T ^ α) k ≤ (T ^ α) ^ δ₀ := by
      intro k hk
      unfold zeroAmp
      apply Real.rpow_le_rpow_of_exponent_le hx1
      linarith only [hR k hk]
    have hsplit := montgomeryForm_block_split hx0 U hU (Θ := (T ^ α) ^ δ₀) (by positivity) hRα
    -- amplitudes on the union
    have hampi : ∀ i, ∑ j ∈ A i, zeroAmp (T ^ α) j
        ≤ ((A i).card : ℝ) * (T ^ (b * (σ i - 1 / 2)) * Real.exp τ) := by
      intro i
      have hone : ∀ j ∈ A i, zeroAmp (T ^ α) j ≤ T ^ (b * (σ i - 1 / 2)) * Real.exp τ := by
        intro j hj
        obtain ⟨_, hj2⟩ := hband i j hj
        unfold zeroAmp
        rw [← Real.rpow_mul hT0.le]
        have hexp : α * ((j.1 : ℂ).re - 1 / 2) ≤ b * (σ i - 1 / 2) + τ / L := by
          have h1 : (j.1 : ℂ).re - 1 / 2 ≤ (σ i - 1 / 2) + τ / L := by linarith
          have h2 : 0 ≤ (σ i - 1 / 2) + τ / L := by
            have := hσall i
            have : 0 ≤ τ / L := by positivity
            linarith only [this, hσall i]
          calc α * ((j.1 : ℂ).re - 1 / 2) ≤ α * ((σ i - 1 / 2) + τ / L) := by gcongr
            _ ≤ b * ((σ i - 1 / 2) + τ / L) := mul_le_mul_of_nonneg_right hα.2 h2
            _ = b * (σ i - 1 / 2) + b * (τ / L) := by ring
            _ ≤ b * (σ i - 1 / 2) + τ / L := by
                have : b * (τ / L) ≤ 1 * (τ / L) :=
                  mul_le_mul_of_nonneg_right hb1.le (by positivity)
                linarith
        calc T ^ (α * ((j.1 : ℂ).re - 1 / 2)) ≤ T ^ (b * (σ i - 1 / 2) + τ / L) :=
              Real.rpow_le_rpow_of_exponent_le hT1.le hexp
          _ = T ^ (b * (σ i - 1 / 2)) * T ^ (τ / L) := Real.rpow_add hT0 _ _
          _ = T ^ (b * (σ i - 1 / 2)) * Real.exp τ := by
              congr 1
              rw [Real.rpow_def_of_pos hT0, ← hLdef]
              congr 1
              field_simp
      calc ∑ j ∈ A i, zeroAmp (T ^ α) j ≤ ∑ _j ∈ A i, T ^ (b * (σ i - 1 / 2)) * Real.exp τ :=
            Finset.sum_le_sum hone
        _ = ((A i).card : ℝ) * (T ^ (b * (σ i - 1 / 2)) * Real.exp τ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hamp : ∑ j ∈ U, zeroAmp (T ^ α) j ≤ 2 * N * (T ^ (b * δ) * Real.exp τ) := by
      have hdisj' : (↑(Finset.univ : Finset κ) : Set κ).PairwiseDisjoint A := by
        simpa using hdisj
      rw [hUdef, Finset.sum_biUnion hdisj']
      calc ∑ i, ∑ j ∈ A i, zeroAmp (T ^ α) j
          ≤ ∑ i, ((A i).card : ℝ) * (T ^ (b * (σ i - 1 / 2)) * Real.exp τ) :=
            Finset.sum_le_sum fun i _ => hampi i
        _ = Real.exp τ * ∑ i, ((A i).card : ℝ) * T ^ (b * (σ i - 1 / 2)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ ≤ Real.exp τ * (2 * N * T ^ (b * (σ i₀ - 1 / 2))) := by
            rw [hb, hN]
            exact mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
        _ = 2 * N * (T ^ (b * δ) * Real.exp τ) := by rw [hδ]; ring
    have hΘ : (T ^ α) ^ δ₀ ≤ T ^ (b * δ₀) := by
      rw [← Real.rpow_mul hT0.le]
      apply Real.rpow_le_rpow_of_exponent_le hT1.le
      exact mul_le_mul_of_nonneg_right hα.2 hδ₀.le
    have hcross : 64 * (T ^ α) ^ δ₀ * windowLog T * ∑ j ∈ U, zeroAmp (T ^ α) j
        ≤ 384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)) := by
      have hsum0 : 0 ≤ ∑ j ∈ U, zeroAmp (T ^ α) j :=
        Finset.sum_nonneg fun j _ => zeroAmp_nonneg hx0.le j
      have hW0 : 0 ≤ windowLog T := windowLog_nonneg hT0.le
      calc 64 * (T ^ α) ^ δ₀ * windowLog T * ∑ j ∈ U, zeroAmp (T ^ α) j
          ≤ 64 * T ^ (b * δ₀) * (3 * L) * (2 * N * (T ^ (b * δ) * Real.exp τ)) := by
            gcongr
        _ = 384 * Real.exp τ * L * N * (T ^ (b * δ₀) * T ^ (b * δ)) := by ring
        _ = 384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)) := by
            rw [← Real.rpow_add hT0, show b * δ₀ + b * δ = b * (δ₀ + δ) by ring]
    have h1 := sub_le_iff_le_add.mp hsplit
    calc (montgomeryForm U (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        ≤ (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
          + 64 * (T ^ α) ^ δ₀ * windowLog T * ∑ j ∈ U, zeroAmp (T ^ α) j := h1
      _ ≤ T / Real.pi * L + 384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)) := add_le_add hF hcross
  -- (iii) integrate the pointwise bound
  have hcontF := continuous_montgomeryForm_rpow U hT0
  have hup : (∫ α in a..b, (montgomeryForm U (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re)
      ≤ ℓ * (T / Real.pi * L + 384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ))) := by
    have this : (∫ α in a..b, (montgomeryForm U (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re)
        ≤ ∫ _α in a..b, (T / Real.pi * L + 384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ))) :=
      intervalIntegral.integral_mono_on hab' (hcontF.intervalIntegrable _ _)
        intervalIntegrable_const hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have hba : b - a = ℓ := by rw [hb]; ring
    rw [hba] at this
    exact this
  -- (iv) the cross term is dominated by the detection term
  have hgap : 384 * Real.exp τ * L * T ^ (b * (δ₀ + δ))
      ≤ 1 / 4 * Real.exp (-3) * κc * T ^ (2 * a * δ) := by
    have hpow : T ^ (2 * a * δ) = T ^ η * T ^ (b * (δ₀ + δ)) := by
      rw [← Real.rpow_add hT0, hη]; ring_nf
    rw [hpow]
    have hTη : 0 < T ^ η := Real.rpow_pos_of_pos hT0 η
    have hTη₀ : 0 < T ^ η₀ := Real.rpow_pos_of_pos hT0 η₀
    have hTb : 0 < T ^ (b * (δ₀ + δ)) := Real.rpow_pos_of_pos hT0 _
    have hlogT : L ≤ ε₁ * T ^ η₀ := by
      have h := e3
      simp only [pow_one] at h
      rwa [div_le_iff₀ hTη₀] at h
    have hηmono : T ^ η₀ ≤ T ^ η := Real.rpow_le_rpow_of_exponent_le hT1.le hηη₀
    have : 384 * Real.exp τ * L ≤ 1 / 4 * Real.exp (-3) * κc * T ^ η := by
      calc 384 * Real.exp τ * L ≤ 384 * Real.exp τ * (ε₁ * T ^ η₀) := by gcongr
        _ = 1 / 4 * Real.exp (-3) * κc * T ^ η₀ := by
            rw [hε₁]; field_simp; ring
        _ ≤ 1 / 4 * Real.exp (-3) * κc * T ^ η := by gcongr
    calc 384 * Real.exp τ * L * T ^ (b * (δ₀ + δ))
        ≤ 1 / 4 * Real.exp (-3) * κc * T ^ η * T ^ (b * (δ₀ + δ)) := by gcongr
      _ = _ := by ring
  -- conclude
  have hmain : 1 / 4 * Real.exp (-3) * κc * T ^ (2 * a * δ) * N ≤ ℓ * (T / Real.pi * L) := by
    have h1 : 1 / 2 * Real.exp (-3) * T ^ (2 * a * δ) * κc * N
        ≤ ℓ * (T / Real.pi * L) + ℓ * (384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ))) := by
      linarith only [hlow, hup]
    have h2 : ℓ * (384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)))
        ≤ 1 / 4 * Real.exp (-3) * κc * T ^ (2 * a * δ) * N := by
      have hℓ1 : ℓ ≤ 1 := by linarith
      calc ℓ * (384 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)))
          = ℓ * N * (384 * Real.exp τ * L * T ^ (b * (δ₀ + δ))) := by ring
        _ ≤ 1 * N * (1 / 4 * Real.exp (-3) * κc * T ^ (2 * a * δ)) := by
            gcongr
        _ = _ := by ring
    linarith only [h1, h2]
  have hTpow : 0 < T ^ (2 * a * δ) := Real.rpow_pos_of_pos hT0 _
  have hfinal : N ≤ (4 * ℓ * Real.exp 3 / (Real.pi * κc)) * (T / T ^ (2 * a * δ)) * L := by
    have hpos : 0 < 1 / 4 * Real.exp (-3) * κc * T ^ (2 * a * δ) := by positivity
    rw [show 1 / 4 * Real.exp (-3) * κc * T ^ (2 * a * δ) * N
        = N * (1 / 4 * Real.exp (-3) * κc * T ^ (2 * a * δ)) by ring,
      ← le_div_iff₀ hpos] at hmain
    refine hmain.trans (le_of_eq ?_)
    rw [Real.exp_neg]
    field_simp
  have hdiv : T / T ^ (2 * a * δ) = T ^ (1 - 2 * a * δ) := by
    rw [Real.rpow_sub hT0, Real.rpow_one]
  rw [hdiv] at hfinal
  exact hfinal

end RHTower
