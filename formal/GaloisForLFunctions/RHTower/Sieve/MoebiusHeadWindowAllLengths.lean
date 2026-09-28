import GaloisForLFunctions.RHTower.Sieve.MoebiusRangeLadderExceptional
import GaloisForLFunctions.RHTower.Sieve.HighRangeRouteTWindowTop
import GaloisForLFunctions.RHTower.Sieve.TwoRangeAssembly

/-!
# The Möbius head window at every short-interval length

For a polynomial length `M ∈ [√x, 2√x]` and a window `W ∈ [1, 2√x]`, the head integral
`∫_{|w| ≤ W} ‖∑_{n ≤ M} μ(n) n^{2πiw}‖²` is bounded by

* the disc `|w| ≤ w₀` (Route T at bounded frequency),
* the ladder of prime ranges of `Sieve/MoebiusRangeLadderWindow` (`3000·M²/log ν`),
* the high range on the exceptional set, whose measure is controlled by
  `Sieve/MoebiusRangeLadderExceptional`,

with the high range's Route-T bound taken up to the frequency top `2√x`.
-/

namespace RHTower.Sieve

open Filter Topology Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The frequency top `2√x` of every head window. -/
def headTop (x : ℝ) : ℝ := 2 * Real.sqrt x

theorem headTop_facts :
    ∀ᶠ x : ℝ in atTop, 1 ≤ headTop x ∧ 2 * Real.pi * headTop x ≤ x
      ∧ twoRangeDisc (99 / 100) 8 x ≤ headTop x := by
  have hsq := tendsto_rpow_log_div_sqrt (4 * (99 / 100 : ℝ) + 3 * 8 + 3)
  filter_upwards [Filter.eventually_ge_atTop (16 * Real.pi ^ 2 + 16),
    Tendsto.eventually_le_const (show (0 : ℝ) < 1 by norm_num) hsq,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hx hsmall hx1
  have hpi := Real.pi_pos
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hs4 : 4 * Real.pi ≤ Real.sqrt x := by
    rw [show 4 * Real.pi = Real.sqrt ((4 * Real.pi) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  refine ⟨?_, ?_, ?_⟩
  · rw [headTop]; nlinarith
  · rw [headTop]; nlinarith
  · rw [twoRangeDisc, headTop, div_le_iff₀ (by positivity)]
    rw [div_le_one hs0] at hsmall
    have h1 : Real.sqrt x ≤ 2 * Real.sqrt x * (2 * Real.pi) := by
      have := Real.pi_gt_three; nlinarith [hs0]
    exact le_trans hsmall h1

/-- A larger window has a larger exceptional annulus. -/
theorem annulusLarge_subset_of_le {T : Set ℝ} {W W' w₀ : ℝ} (hW : W ≤ W') :
    annulusLarge T W w₀ ⊆ annulusLarge (T ∩ Set.Icc (-W) W) W' w₀ := by
  intro w hw
  obtain ⟨⟨hI, hT⟩, hd⟩ := hw
  refine ⟨⟨⟨by linarith [hI.1], by linarith [hI.2]⟩, fun h => hT h.1⟩, hd⟩

/-- **The Halász–Montgomery far constant on a head window.** -/
theorem plainKernelFarConst_head_le :
    ∀ᶠ x : ℝ in atTop, ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ 2 * Real.sqrt x → ∀ W : ℝ, 1 ≤ W →
      W ≤ 2 * Real.sqrt x →
      plainKernelFarConst N (2 * Real.pi * W) ≤ 60000 * Real.log x * Real.sqrt W := by
  filter_upwards [Filter.eventually_ge_atTop (10000 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_log_div_sqrt (0 : ℝ)).eventually_le_const (show (0 : ℝ) < 1 / 30 by norm_num)]
    with x hx hlog1 hsm
  intro N hN hNx W hW hWx
  have hpi := Real.pi_pos
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  rw [Real.rpow_zero, div_le_iff₀ hs0] at hsm
  have hs30 : 30 ≤ Real.sqrt x := by nlinarith
  have hW0 : 0 < W := by linarith
  have hsW : 1 ≤ Real.sqrt W := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hW
  have hsq : Real.sqrt (2 * (2 * Real.pi * W)) ≤ 4 * Real.sqrt W := by
    rw [show 4 * Real.sqrt W = Real.sqrt (16 * W) by
      rw [Real.sqrt_mul (by norm_num), show (16 : ℝ) = 4 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hc1 : 1 ≤ ⌈2 * (2 * Real.pi * W)⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
  have hclog : ((Nat.log 2 ⌈2 * (2 * Real.pi * W)⌉₊ : ℕ) : ℝ) ≤ 2 * Real.log x := by
    refine (natLog_two_le hc1).trans ?_
    have hceil : ((⌈2 * (2 * Real.pi * W)⌉₊ : ℕ) : ℝ) ≤ x := by
      have := Nat.ceil_lt_add_one (show 0 ≤ 2 * (2 * Real.pi * W) by positivity)
      nlinarith
    have := Real.log_le_log (by exact_mod_cast Nat.lt_of_lt_of_le zero_lt_one hc1) hceil
    linarith
  have hNlog : ((Nat.log 2 N : ℕ) : ℝ) ≤ 2 * Real.log x := by
    refine (natLog_two_le hN).trans ?_
    have := Real.log_le_log (by exact_mod_cast Nat.lt_of_lt_of_le zero_lt_one hN)
      (show (N : ℝ) ≤ x by nlinarith)
    linarith
  rw [plainKernelFarConst]
  have hsq0 : 0 ≤ Real.sqrt (2 * (2 * Real.pi * W)) := Real.sqrt_nonneg _
  have hA : ((Nat.log 2 ⌈2 * (2 * Real.pi * W)⌉₊ : ℝ) + 1) * (214 * Real.sqrt (2 * (2 * Real.pi * W)))
      ≤ (2 * Real.log x + 1) * (856 * Real.sqrt W) := by
    have h0 : (0 : ℝ) ≤ (Nat.log 2 ⌈2 * (2 * Real.pi * W)⌉₊ : ℝ) + 1 := by positivity
    calc ((Nat.log 2 ⌈2 * (2 * Real.pi * W)⌉₊ : ℝ) + 1) * (214 * Real.sqrt (2 * (2 * Real.pi * W)))
        ≤ (2 * Real.log x + 1) * (214 * (4 * Real.sqrt W)) := by gcongr
      _ = (2 * Real.log x + 1) * (856 * Real.sqrt W) := by ring
  nlinarith

/-- **The high range's three costs, in closed form.**  The Halász–Montgomery group, the sharp
ladder error and the rough class of a designated range `P'`, with every parameter replaced by an
explicit bound. -/
theorem highRange_costs_le {P' : Finset ℕ} (hPprime : ∀ q ∈ P', q.Prime) (M : ℕ)
    {R' η' W vol ℓ ρ' cL Λ K A : ℝ} {L' : ℕ} (hR1 : 1 ≤ R') (hη : 0 < η') (hη1 : η' ≤ 1)
    (hL1 : 1 ≤ L') (hΛ : 2 * (L' : ℝ) * (2 * Real.pi)⁻¹ ≤ Λ)
    (hP' : ∀ p ∈ P', R' < (p : ℝ) ∧ (p : ℝ) ≤ R' * (1 + η') ^ L')
    (hcard : (P'.card : ℝ) ≤ 2 * cL) (hQ : R' * (1 + η') ^ L' ≤ 2 * cL) (hcl1 : 1 ≤ cL)
    (hclM : 3 * cL ≤ M) (hℓ1 : 1 ≤ ℓ) (hH : rangeHarmonic P' ≤ ℓ) (hA : 0 < A)
    (hAH : A ≤ rangeHarmonic P') (hW : 1 ≤ W) (hWM : W ≤ 2 * M)
    (hlogW : Real.log (2 + 2 * (2 * Real.pi * W)) ≤ ℓ)
    (hFC : plainKernelFarConst ⌊(M : ℝ) / R'⌋₊ (2 * Real.pi * W) ≤ K * Real.sqrt W)
    (hvol : 0 ≤ vol) :
    2 * (2 * (L' : ℝ) * ∑ j ∈ Finset.range L',
          (ρ' * ((geomBlock P' R' (1 + η') j).card : ℝ)) ^ (2 : ℕ)
            * ladderHMBoundRecip M R' η' W vol j
        + 2 * ∫ w in Set.Icc (-W) W, ‖ramareLadderError P' M R' η' L' w‖ ^ 2)
      + 2 * (∫ w in Set.Icc (-W) W,
          ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P' M) w‖ ^ 2)
    ≤ (M : ℝ) ^ 2 * (1848 * Λ * ρ' ^ 2 * ℓ ^ 3 + 240 * (η' + 6 / R') + 108 / A)
      + 126 * Λ * K * ℓ * cL * ρ' ^ 2 * M * (Real.sqrt W * vol) := by
  have hR0 : 0 < R' := by linarith
  have hM0 : (3 : ℝ) ≤ M := by linarith
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  have hpid : Real.pi < 3.15 := Real.pi_lt_d2
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hH0 : 0 ≤ rangeHarmonic P' := Finset.sum_nonneg fun p _ => by positivity
  -- the group
  have hgroup := largeLadderGroup_le (P := P') M hR0 hη.le hW hvol hL1 (ρ := ρ') hP'
  set S := (1 + η') * (M : ℝ) * rangeHarmonic P' with hSdef
  set B := R' * (1 + η') ^ L' * η' + 1 with hBdef
  set FC := plainKernelFarConst ⌊(M : ℝ) / R'⌋₊ (2 * Real.pi * W) with hFCdef
  have hS0 : 0 ≤ S := by positivity
  have hS : S ≤ 2 * M * ℓ := by
    have h1 : (1 + η') ≤ 2 := by linarith
    have h2 : (M : ℝ) * rangeHarmonic P' ≤ M * ℓ := mul_le_mul_of_nonneg_left hH (by linarith)
    calc S = (1 + η') * ((M : ℝ) * rangeHarmonic P') := by rw [hSdef]; ring
      _ ≤ 2 * ((M : ℝ) * ℓ) := mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ = 2 * M * ℓ := by ring
  have hB : B ≤ 3 * cL := by
    have : R' * (1 + η') ^ L' * η' ≤ R' * (1 + η') ^ L' :=
      mul_le_of_le_one_right (by positivity) hη1
    rw [hBdef]; linarith
  have hB0 : 0 ≤ B := by positivity
  have h2piW : 1 ≤ 2 * Real.pi * W := by nlinarith only [hW, hpi3]
  have hFC0 : 0 ≤ FC := plainKernelFarConst_nonneg _ h2piW
  have hlogW0 : 0 ≤ Real.log (2 + 2 * (2 * Real.pi * W)) := Real.log_nonneg (by linarith)
  have hΛ0 : 0 ≤ Λ := le_trans (by positivity) hΛ
  have hcL0 : 0 ≤ cL := by linarith
  have hfirst : (2 + 48 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * W)))
        * (S ^ (2 : ℕ) + B * S) ≤ 154 * ℓ * (6 * (M : ℝ) ^ 2 * ℓ ^ 2) := by
    have h1 : 2 + 48 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * W)) ≤ 154 * ℓ := by
      have a : 48 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * W)) ≤ 48 * Real.pi * ℓ :=
        mul_le_mul_of_nonneg_left hlogW (by positivity)
      have b : 48 * Real.pi * ℓ ≤ 152 * ℓ :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      linarith
    have h2 : S ^ (2 : ℕ) + B * S ≤ 6 * (M : ℝ) ^ 2 * ℓ ^ 2 := by
      have hS2 : S ^ (2 : ℕ) ≤ (2 * M * ℓ) ^ 2 := pow_le_pow_left₀ hS0 hS 2
      have hBS : B * S ≤ (3 * cL) * (2 * M * ℓ) := mul_le_mul hB hS hS0 (by positivity)
      have h3 : (3 * cL) * (2 * M * ℓ) ≤ M * (2 * M * ℓ) :=
        mul_le_mul_of_nonneg_right hclM (by positivity)
      have h4 : (M : ℝ) * (2 * M * ℓ) ≤ 2 * (M : ℝ) ^ 2 * ℓ ^ 2 := by
        have : ℓ ≤ ℓ ^ 2 := by nlinarith only [hℓ1]
        have hM2 : 0 ≤ 2 * (M : ℝ) ^ 2 := by positivity
        calc (M : ℝ) * (2 * M * ℓ) = 2 * (M : ℝ) ^ 2 * ℓ := by ring
          _ ≤ 2 * (M : ℝ) ^ 2 * ℓ ^ 2 := mul_le_mul_of_nonneg_left this hM2
      have h5 : (2 * (M : ℝ) * ℓ) ^ 2 = 4 * (M : ℝ) ^ 2 * ℓ ^ 2 := by ring
      linarith
    have hpos2 : 0 ≤ S ^ (2 : ℕ) + B * S := by positivity
    exact mul_le_mul h1 h2 hpos2 (by positivity)
  have hsecond : FC * (2 * Real.pi * vol) * (B * S + B * (P'.card : ℝ))
      ≤ (K * Real.sqrt W) * (2 * Real.pi * vol) * (9 * cL * M * ℓ) := by
    have h1 : B * S + B * (P'.card : ℝ) ≤ 9 * cL * M * ℓ := by
      have hcardM : (P'.card : ℝ) ≤ M * ℓ := by
        have : (M : ℝ) ≤ M * ℓ := le_mul_of_one_le_right (by linarith) hℓ1
        linarith
      have hSP : S + (P'.card : ℝ) ≤ 3 * M * ℓ := by linarith
      have := mul_le_mul hB hSP (by positivity) (by positivity)
      calc B * S + B * (P'.card : ℝ) = B * (S + (P'.card : ℝ)) := by ring
        _ ≤ 3 * cL * (3 * M * ℓ) := this
        _ = 9 * cL * M * ℓ := by ring
    have hK : 0 ≤ K * Real.sqrt W := le_trans hFC0 hFC
    have hBS0 : 0 ≤ B * S + B * (P'.card : ℝ) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_right hFC (by positivity)) h1 hBS0 (by positivity)
  have hG : 2 * (L' : ℝ) * ∑ j ∈ Finset.range L',
        (ρ' * ((geomBlock P' R' (1 + η') j).card : ℝ)) ^ (2 : ℕ)
          * ladderHMBoundRecip M R' η' W vol j
      ≤ 924 * Λ * ρ' ^ 2 * ℓ ^ 3 * (M : ℝ) ^ 2
        + 63 * Λ * K * ℓ * cL * ρ' ^ 2 * M * (Real.sqrt W * vol) := by
    refine hgroup.trans ?_
    have hL0 : 0 ≤ 2 * (L' : ℝ) * (2 * Real.pi)⁻¹ := by positivity
    have hρ2 : 0 ≤ ρ' ^ (2 : ℕ) := by positivity
    have hX0 : 0 ≤ (2 + 48 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * W)))
        * (S ^ (2 : ℕ) + B * S) := by positivity
    have hY0 : 0 ≤ FC * (2 * Real.pi * vol) * (B * S + B * (P'.card : ℝ)) := by positivity
    have h2L : 2 * (L' : ℝ) * (2 * Real.pi)⁻¹ * (2 * Real.pi) ≤ 7 * Λ := by
      calc 2 * (L' : ℝ) * (2 * Real.pi)⁻¹ * (2 * Real.pi)
          ≤ Λ * (2 * Real.pi) := mul_le_mul_of_nonneg_right hΛ (by positivity)
        _ ≤ Λ * 7 := mul_le_mul_of_nonneg_left (by linarith) hΛ0
        _ = 7 * Λ := by ring
    have hK0 : 0 ≤ (K * Real.sqrt W) * vol * (9 * cL * M * ℓ) := by
      have : 0 ≤ K * Real.sqrt W := le_trans hFC0 hFC
      positivity
    have t1 : 2 * (L' : ℝ) * (2 * Real.pi)⁻¹
          * (ρ' ^ (2 : ℕ) * ((2 + 48 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * W)))
            * (S ^ (2 : ℕ) + B * S)))
        ≤ Λ * (ρ' ^ (2 : ℕ) * (154 * ℓ * (6 * (M : ℝ) ^ 2 * ℓ ^ 2))) :=
      mul_le_mul hΛ (mul_le_mul_of_nonneg_left hfirst hρ2) (by positivity) hΛ0
    have t2 : 2 * (L' : ℝ) * (2 * Real.pi)⁻¹
          * (ρ' ^ (2 : ℕ) * (FC * (2 * Real.pi * vol) * (B * S + B * (P'.card : ℝ))))
        ≤ 7 * Λ * (ρ' ^ (2 : ℕ) * ((K * Real.sqrt W) * vol * (9 * cL * M * ℓ))) := by
      have hs := mul_le_mul_of_nonneg_left hsecond hρ2
      calc 2 * (L' : ℝ) * (2 * Real.pi)⁻¹
            * (ρ' ^ (2 : ℕ) * (FC * (2 * Real.pi * vol) * (B * S + B * (P'.card : ℝ))))
          ≤ 2 * (L' : ℝ) * (2 * Real.pi)⁻¹
            * (ρ' ^ (2 : ℕ) * ((K * Real.sqrt W) * (2 * Real.pi * vol) * (9 * cL * M * ℓ))) :=
            mul_le_mul_of_nonneg_left hs hL0
        _ = (2 * (L' : ℝ) * (2 * Real.pi)⁻¹ * (2 * Real.pi))
            * (ρ' ^ (2 : ℕ) * ((K * Real.sqrt W) * vol * (9 * cL * M * ℓ))) := by ring
        _ ≤ 7 * Λ * (ρ' ^ (2 : ℕ) * ((K * Real.sqrt W) * vol * (9 * cL * M * ℓ))) :=
            mul_le_mul_of_nonneg_right h2L (by positivity)
    have e0 : 2 * (L' : ℝ) * (2 * Real.pi)⁻¹
          * (ρ' ^ (2 : ℕ) * ((2 + 48 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * W)))
              * (S ^ (2 : ℕ) + B * S)
            + FC * (2 * Real.pi * vol) * (B * S + B * (P'.card : ℝ))))
        = 2 * (L' : ℝ) * (2 * Real.pi)⁻¹
            * (ρ' ^ (2 : ℕ) * ((2 + 48 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * W)))
              * (S ^ (2 : ℕ) + B * S)))
          + 2 * (L' : ℝ) * (2 * Real.pi)⁻¹
            * (ρ' ^ (2 : ℕ) * (FC * (2 * Real.pi * vol) * (B * S + B * (P'.card : ℝ)))) := by
      ring
    have e1 : Λ * (ρ' ^ (2 : ℕ) * (154 * ℓ * (6 * (M : ℝ) ^ 2 * ℓ ^ 2)))
        = 924 * Λ * ρ' ^ 2 * ℓ ^ 3 * (M : ℝ) ^ 2 := by ring
    have e2 : 7 * Λ * (ρ' ^ (2 : ℕ) * ((K * Real.sqrt W) * vol * (9 * cL * M * ℓ)))
        = 63 * Λ * K * ℓ * cL * ρ' ^ 2 * M * (Real.sqrt W * vol) := by ring
    rw [e0]
    linarith
  -- the error
  have herr := integral_normSq_ramareLadderError_le_sharp M hR1 hη.le hW L' hPprime
    (fun p hp => (hP' p hp).1)
  have hfl : ((⌊(M : ℝ) * (1 + η')⌋₊ : ℕ) : ℝ) ≤ 2 * M := by
    have := Nat.floor_le (show 0 ≤ (M : ℝ) * (1 + η') by positivity)
    have h2 : (M : ℝ) * η' ≤ M := mul_le_of_le_one_right (by linarith) hη1
    have h3 : (M : ℝ) * (1 + η') = M + M * η' := by ring
    linarith
  have herr' : (∫ w in Set.Icc (-W) W, ‖ramareLadderError P' M R' η' L' w‖ ^ 2)
      ≤ 60 * (M : ℝ) ^ 2 * (η' + 6 / R') := by
    refine herr.trans ?_
    have hpiW : Real.pi * W ≤ 3.15 * (2 * M) := mul_le_mul hpid.le hWM (by linarith) (by norm_num)
    have heM : Real.exp 1 * ((⌊(M : ℝ) * (1 + η')⌋₊ : ℕ) : ℝ) ≤ 2.7182818286 * (2 * M) :=
      mul_le_mul he.le hfl (Nat.cast_nonneg _) (by norm_num)
    have hc : 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) * (1 + η')⌋₊ : ℕ) : ℝ)
        ≤ 30 * M := by linarith
    have hsec : η' * M + 6 * M / R' = M * (η' + 6 / R') := by ring
    rw [hsec]
    have h0 : 0 ≤ (M : ℝ) * (η' + 6 / R') := by positivity
    calc 2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) * (1 + η')⌋₊ : ℕ) : ℝ))
          * ((M : ℝ) * (η' + 6 / R'))
        ≤ 2 * (30 * M) * ((M : ℝ) * (η' + 6 / R')) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) h0
      _ = 60 * (M : ℝ) ^ 2 * (η' + 6 / R') := by ring
  -- the rough class
  have hrough := integral_Icc_normSq_roughPoly_le_harmonic hPprime M hW (lt_of_lt_of_le hA hAH)
  have hrough' : (∫ w in Set.Icc (-W) W,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P' M) w‖ ^ 2)
      ≤ 54 * (M : ℝ) ^ 2 / A := by
    refine hrough.trans ?_
    have hHpos : 0 < rangeHarmonic P' := lt_of_lt_of_le hA hAH
    have hpiW : Real.pi * W ≤ 3.15 * (2 * M) := mul_le_mul hpid.le hWM (by linarith) (by norm_num)
    have heM : Real.exp 1 * (M : ℝ) ≤ 2.7182818286 * M :=
      mul_le_mul_of_nonneg_right he.le (Nat.cast_nonneg _)
    have hc : 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ) ≤ 23 * M := by linarith
    have hfrac : (M : ℝ) / rangeHarmonic P' + 2 * (P'.card : ℝ) / rangeHarmonic P'
        ≤ (7 / 3 * M) / A := by
      rw [← add_div]
      calc ((M : ℝ) + 2 * (P'.card : ℝ)) / rangeHarmonic P' ≤ (7 / 3 * M) / rangeHarmonic P' :=
            div_le_div_of_nonneg_right (by linarith) hHpos.le
        _ ≤ (7 / 3 * M) / A := div_le_div_of_nonneg_left (by positivity) hA hAH
    have hc0 : 0 ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ) := by positivity
    have hf0 : 0 ≤ (M : ℝ) / rangeHarmonic P' + 2 * (P'.card : ℝ) / rangeHarmonic P' := by
      positivity
    calc (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
          * ((M : ℝ) / rangeHarmonic P' + 2 * (P'.card : ℝ) / rangeHarmonic P')
        ≤ (23 * M) * ((7 / 3 * M) / A) := mul_le_mul hc hfrac hf0 (by positivity)
      _ = 161 / 3 * (M : ℝ) ^ 2 / A := by ring
      _ ≤ 54 * (M : ℝ) ^ 2 / A := by
          apply div_le_div_of_nonneg_right _ hA.le; linarith [sq_nonneg (M : ℝ)]
  have hA' : 0 ≤ 108 * (M : ℝ) ^ 2 / A := by positivity
  have hsplit : (M : ℝ) ^ 2 * (1848 * Λ * ρ' ^ 2 * ℓ ^ 3 + 240 * (η' + 6 / R') + 108 / A)
      = 2 * (924 * Λ * ρ' ^ 2 * ℓ ^ 3 * (M : ℝ) ^ 2) + 4 * (60 * (M : ℝ) ^ 2 * (η' + 6 / R'))
        + 2 * (54 * (M : ℝ) ^ 2 / A) := by ring
  rw [hsplit]
  linarith

/-- **The head window at one point.**  All ranges of the ladder, the exceptional set, the high
range and the disc, assembled. -/
theorem integral_head_le_ladder {ν T : ℝ} (hν : 3000 ≤ ν) (hc : 4 * mertensFirstConst + 1 ≤ ν)
    (hνT : ν ≤ T) (M : ℕ) (hMlo : T ^ 40 / 2 ≤ Real.log M) (hMhi : Real.log M ≤ T ^ 40)
    {W w₀ Bdisc : ℝ} (hW : 1 ≤ W) (hWM : W ≤ M) (hW0 : W * rangeLadderTopReal ν 0 ≤ M)
    (hdisc : (∫ w in Set.Icc (-w₀) w₀,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2) ≤ Bdisc)
    {P' : Finset ℕ} (hPprime : ∀ q ∈ P', q.Prime)
    {R' η' ℓ ρ' cL Λ K A : ℝ} {L' : ℕ} (hR1 : 1 ≤ R') (hη : 0 < η') (hη1 : η' ≤ 1)
    (hL1 : 1 ≤ L') (hΛ : 2 * (L' : ℝ) * (2 * Real.pi)⁻¹ ≤ Λ)
    (hP' : ∀ p ∈ P', R' < (p : ℝ) ∧ (p : ℝ) ≤ R' * (1 + η') ^ L')
    (hcard : (P'.card : ℝ) ≤ 2 * cL) (hQ : R' * (1 + η') ^ L' ≤ 2 * cL) (hcl1 : 1 ≤ cL)
    (hclM : 3 * cL ≤ M) (hℓ1 : 1 ≤ ℓ) (hH : rangeHarmonic P' ≤ ℓ) (hA : 0 < A)
    (hAH : A ≤ rangeHarmonic P')
    (hlogW : Real.log (2 + 2 * (2 * Real.pi * W)) ≤ ℓ)
    (hFC : plainKernelFarConst ⌊(M : ℝ) / R'⌋₊ (2 * Real.pi * W) ≤ K * Real.sqrt W)
    (hNj : ∀ j ∈ Finset.range L', 1 ≤ ⌊(M : ℝ) / (R' * (1 + η') ^ j)⌋₊)
    (hbound' : ∀ j ∈ Finset.range L', ∀ w ∈ annulusLarge (rangeUnionSmall (rangeLadderP ν)
        (rangeLadderR ν) (rangeLadderEta ν) (rangeLadderSteps ν)
        (powerThreshold (rangeLadderR ν) (rangeLadderEta ν) rangeLadderAlpha) W
        (rangeLadderLast ν T + 1)) W w₀,
      ‖primeBlockPoly (geomBlock P' R' (1 + η') j) w‖ ≤ ρ' * ((geomBlock P' R' (1 + η') j).card : ℝ))
    (hΛ0 : 0 ≤ Λ) (hK0 : 0 ≤ K) :
    (∫ w in Set.Icc (-W) W, ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
      ≤ Bdisc + 3000 * (M : ℝ) ^ 2 / Real.log ν
        + (M : ℝ) ^ 2 * (1848 * Λ * ρ' ^ 2 * ℓ ^ 3 + 240 * (η' + 6 / R') + 108 / A)
        + 126 * Λ * K * ℓ * cL * ρ' ^ 2 * (M : ℝ) ^ 2 * Real.exp (-(T ^ 40 / (8 * Real.log T))) := by
  have hν0 : 0 < ν := by linarith
  have hT : 3000 ≤ T := le_trans hν hνT
  have hT1 : 1 ≤ T := by linarith
  have hlogν : 0 < Real.log ν := by have := log_ge_four_of_ge hν; linarith
  have hlamM : 0 < Real.log (M : ℝ) := lt_of_lt_of_le (by positivity) hMlo
  have hM1 : (1 : ℝ) < M := by
    by_contra hcon
    rw [not_lt] at hcon
    have : Real.log (M : ℝ) ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) hcon
    linarith
  have hM : 0 < M := by exact_mod_cast (lt_trans zero_lt_one hM1)
  have hBdisc0 : 0 ≤ Bdisc := le_trans (MeasureTheory.setIntegral_nonneg measurableSet_Icc
    fun w _ => by positivity) hdisc
  set K' := rangeLadderLast ν T with hK'def
  -- the exceptional measure
  set U := annulusLarge (rangeUnionSmall (rangeLadderP ν) (rangeLadderR ν) (rangeLadderEta ν)
    (rangeLadderSteps ν) (powerThreshold (rangeLadderR ν) (rangeLadderEta ν) rangeLadderAlpha) W
    (K' + 1)) W w₀ with hUdef
  have hvol0 : 0 ≤ volume.real U := ENNReal.toReal_nonneg
  have hU := sqrt_mul_measureReal_rangeLadder_exceptional_le hν hνT hMlo hMhi hW hWM (w₀ := w₀)
  rw [← hK'def] at hU
  -- the high part
  have hhigh := highRange_costs_le hPprime M (vol := volume.real U) (ρ' := ρ') hR1 hη hη1 hL1 hΛ
    hP' hcard hQ hcl1 hclM hℓ1 hH hA hAH hW (by linarith) hlogW hFC hvol0
  -- the tops of the ranges
  have htop : ∀ j ∈ Finset.range (K' + 1), (rangeLadderTop ν j : ℝ) ≤ M := by
    intro j hj
    have hjK : j ≤ K' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    obtain ⟨-, hup⟩ := rangeLadderLast_spec (by linarith) hνT
    rw [← hK'def] at hup
    have hmono : rangeLadderNu ν j ≤ rangeLadderNu ν K' :=
      pow_le_pow_right₀ (by linarith) (Nat.pow_le_pow_right (by norm_num) hjK)
    have hlogQ := log_rangeLadderTopReal_le (by linarith : (2 : ℝ) ≤ ν) j
    have hj0 : 0 ≤ rangeLadderNu ν j := (rangeLadderNu_pos hν0 j).le
    have h5 : rangeLadderNu ν j ^ 5 ≤ T ^ 10 := by
      calc rangeLadderNu ν j ^ 5 ≤ (T ^ 2) ^ 5 := pow_le_pow_left₀ hj0 (hmono.trans hup) 5
        _ = T ^ 10 := by ring
    have hT40 : 3 * T ^ 10 ≤ T ^ 40 / 2 := by
      have h30 : 6 ≤ T ^ 30 := by
        have : (1 : ℝ) ≤ T ^ 30 := one_le_pow₀ hT1
        have h3 : T ≤ T ^ 30 := by
          calc T = T ^ 1 := (pow_one T).symm
            _ ≤ T ^ 30 := pow_le_pow_right₀ hT1 (by norm_num)
        linarith
      have : T ^ 40 = T ^ 10 * T ^ 30 := by ring
      have h10 : 0 ≤ T ^ 10 := by positivity
      nlinarith
    have hlogle : Real.log (rangeLadderTopReal ν j) ≤ Real.log (M : ℝ) := by linarith
    have hQM : rangeLadderTopReal ν j ≤ M :=
      (Real.log_le_log_iff (rangeLadderTopReal_pos hν0 j) (by linarith)).mp hlogle
    exact (Nat.floor_le (rangeLadderTopReal_pos hν0 j).le).trans hQM
  have hlow := rangeLadder_sum_le hν hc M (K' + 1) hW hWM htop
  -- the window
  by_cases hwW : w₀ ≤ W
  · have hmain := integral_Icc_normSq_logPoly_moebius_le_powerRanges (rangeLadderP ν)
      (rangeLadderR ν) (rangeLadderEta ν) rangeLadderAlpha (rangeLadderSteps ν) M (K' + 1) hM
      (P' := P') (R' := R') (η' := η') (w₀ := w₀) (Bdisc := Bdisc) hW hWM
      (fun j _ => one_lt_rangeLadderR hν0 j)
      (fun j _ => ⟨(rangeLadderEta_pos ν j).le, rangeLadderEta_le_one hν0.le j⟩)
      (fun j _ => one_le_rangeLadderSteps hν0 j) (fun j _ => rangeLadderAlpha_le j)
      (fun j _ => rangeLadderP_prime ν j) (fun j _ => rangeLadderP_bounds ν j)
      (fun v hv => by
        refine le_trans ?_ hW0
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        rw [rangeLadderTopReal]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by linarith [rangeLadderEta_pos ν 0]) (Finset.mem_range.mp hv).le)
          (rangeLadderR_pos hν0 0).le)
      (by linarith) hη.le hwW hL1 hPprime hP' (fun j => ρ' * ((geomBlock P' R' (1 + η') j).card : ℝ))
      hNj hbound' hdisc
    refine hmain.trans ?_
    have hexc : 126 * Λ * K * ℓ * cL * ρ' ^ 2 * M * (Real.sqrt W * volume.real U)
        ≤ 126 * Λ * K * ℓ * cL * ρ' ^ 2 * (M : ℝ) ^ 2
          * Real.exp (-(T ^ 40 / (8 * Real.log T))) := by
      have hcoef : 0 ≤ 126 * Λ * K * ℓ * cL * ρ' ^ 2 * M := by
        have : 0 ≤ cL := by linarith
        positivity
      calc 126 * Λ * K * ℓ * cL * ρ' ^ 2 * M * (Real.sqrt W * volume.real U)
          ≤ 126 * Λ * K * ℓ * cL * ρ' ^ 2 * M * (M * Real.exp (-(T ^ 40 / (8 * Real.log T)))) :=
            mul_le_mul_of_nonneg_left hU hcoef
        _ = 126 * Λ * K * ℓ * cL * ρ' ^ 2 * (M : ℝ) ^ 2
              * Real.exp (-(T ^ 40 / (8 * Real.log T))) := by ring
    linarith
  · rw [not_le] at hwW
    have hsub : (∫ w in Set.Icc (-W) W,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
        ≤ ∫ w in Set.Icc (-w₀) w₀, ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2 :=
      MeasureTheory.setIntegral_mono_set
        (((continuous_logPoly _ _).norm).pow 2).integrableOn_Icc
        (Filter.Eventually.of_forall fun w => by positivity)
        (Filter.Eventually.of_forall (Set.Icc_subset_Icc (by linarith) hwW.le))
    have hlow0 : 0 ≤ 3000 * (M : ℝ) ^ 2 / Real.log ν := by positivity
    have hA0 : 0 ≤ 108 / A := by positivity
    have hη0 : 0 ≤ 240 * (η' + 6 / R') := by
      have : 0 < R' := by linarith
      positivity
    have hmid : 0 ≤ (M : ℝ) ^ 2 * (1848 * Λ * ρ' ^ 2 * ℓ ^ 3 + 240 * (η' + 6 / R') + 108 / A) := by
      have : 0 ≤ 1848 * Λ * ρ' ^ 2 * ℓ ^ 3 := by positivity
      positivity
    have hlast : 0 ≤ 126 * Λ * K * ℓ * cL * ρ' ^ 2 * (M : ℝ) ^ 2
        * Real.exp (-(T ^ 40 / (8 * Real.log T))) := by
      have : 0 ≤ cL := by linarith
      positivity
    linarith

end

end RHTower.Sieve
