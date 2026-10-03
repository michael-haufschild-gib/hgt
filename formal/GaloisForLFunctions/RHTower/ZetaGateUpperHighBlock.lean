import GaloisForLFunctions.RHTower.ZetaGateFarHighBlock
import GaloisForLFunctions.RHTower.ZetaGateUpperRange

/-!
# The upper dyadic law for mollifiers of length up to `U^{21/50}`

With the pair-error envelope of `ZetaGateFarPairError` (`N ≤ u^{43}`), the high blocks
`U^{49/50} ≤ a ≤ v ≤ 2a ≤ 2U` accept real coefficients `|w| ≤ 1` of length
`N ≤ U^{21/50} ≤ a^{3/7} ≤ a^{43/100}` (`exists_highBlock_bound_of_mainTerm_upper`).  No block below
`U^{49/50}` is needed: the gate on the upper range (`ZetaGateUpperRange`) starts its window at
`U^{49/50}`, so this is the upper dyadic law `ZetaUpperDyadicMeanSquareLaw (49/50) R c`
(`zetaUpperDyadicMeanSquareLaw_of_highBlock`).
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset Filter Topology
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- **The high-block bound from a main-term bound, window form, mollifiers up to `U^{21/50}`.**
For `U` large, every admissible displacement `d` and every block `U^{49/50} ≤ a ≤ v ≤ 2a`,
`v ≤ U`, `∫_a^v ‖ζΨ(½−d+iτ)‖² dτ ≤ (c + ε)(v − a + 2a^{19/20})`. -/
theorem exists_highBlock_bound_of_mainTerm_upper_window {R c : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : Tendsto F atTop (𝓝 c)) (N : ℝ → ℕ) (w : ℝ → ℕ → ℝ)
    (hN : ∀ᶠ U in atTop, (N U : ℝ) ≤ U ^ ((21 : ℝ) / 50))
    (hw : ∀ U, ∀ n ∈ Finset.Icc 1 (N U), |w U n| ≤ 1)
    (hmain : ∀ᶠ U in atTop, ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U →
      d * Real.log (U - 1) ≤ R → ∀ a v η : ℝ, 0 < η → 4 ≤ a - η → a ≤ v → v ≤ U → η ≤ a →
      a / 2 ≤ a - η → U ^ ((1 : ℝ) / 8) ≤ a →
      gcdSum₂ d (N U) (w U) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
          * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
        ≤ (v - a + 2 * η) * F U) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop,
      ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U → d * Real.log (U - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → U ^ ((49 : ℝ) / 50) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
            * edPoly (fun n => ((w U n : ℝ) : ℂ)) (Finset.Icc 1 (N U)) (displacedLinePt d τ)‖ ^ 2)
          ≤ (c + ε) * (v - a + 2 * a ^ ((19 : ℝ) / 20)) := by
  obtain ⟨CA, hCA0, hCA⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 51) (by norm_num)
  obtain ⟨C₁, C₂, hC₁, hC₂, hsplit⟩ :=
    exists_tsum_dualOffDiagTerm_le_split 500 (K'' := 150) (by norm_num)
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_norm_smoothLeft_le_far 3
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_norm_dualLeft_le_far 3
  intro ε hε
  have hps := pairStarFar_nonneg hCA0 hC₁ hC₂ hK₁0
  filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 800),
    eventually_ge_atTop (Real.exp (200 + 40 * R)),
    (tendsto_order.1 hF).2 _ (show c < c + ε / 2 by linarith), hN, hmain,
    eventually_const_mul_rpow_neg_le (pairStarFar CA C₁ C₂ K₁ + 2 ^ 15 * K₂ * Real.exp (4 * R))
      ((49 : ℝ) / 1000) (by norm_num) (half_pos hε)]
    with U hU2 hUe hUA hNle hmainU hUerr
  intro d hd hd8 hRd hdU1 a v ha haU hav hv2 hvU
  have hU1 : (1 : ℝ) ≤ U := le_trans (one_le_pow₀ (by norm_num)) hU2
  have h2100 : (2 : ℝ) ^ 100 ≤ a := by
    have e : ((2 : ℝ) ^ 800) ^ ((1 : ℝ) / 2) = (2 : ℝ) ^ 400 := by
      rw [← Real.rpow_natCast (2 : ℝ) 800, ← Real.rpow_mul (by norm_num),
        show ((800 : ℕ) : ℝ) * (1 / 2) = ((400 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (2 : ℝ) ^ 100 ≤ (2 : ℝ) ^ 400 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      _ = ((2 : ℝ) ^ 800) ^ ((1 : ℝ) / 2) := e.symm
      _ ≤ U ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) hU2 (by norm_num)
      _ ≤ U ^ ((49 : ℝ) / 50) := Real.rpow_le_rpow_of_exponent_le
          (le_trans (one_le_pow₀ (by norm_num)) hU2) (by norm_num)
      _ ≤ a := haU
  clear hU2
  have hU0 : 0 < U := by linarith
  have hlogU : 200 + 40 * R ≤ Real.log U := by
    have := Real.log_le_log (Real.exp_pos _) hUe
    rwa [Real.log_exp] at this
  have hU3 : (3 : ℝ) ≤ U := by
    have : (3 : ℝ) ≤ Real.exp (200 + 40 * R) := by
      have := Real.add_one_le_exp (200 + 40 * R)
      linarith
    linarith
  have hdU : d * Real.log U ≤ 2 * R := by
    have hlog2U : Real.log U ≤ 2 * Real.log (U - 1) := by
      have h1 : U ≤ (U - 1) ^ 2 := by nlinarith
      have h2 : Real.log U ≤ Real.log ((U - 1) ^ 2) := Real.log_le_log hU0 h1
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith only [h2]
    have := mul_le_mul_of_nonneg_left hlog2U hd.le
    linarith only [this, hdU1]
  have hd20 : d ≤ 1 / 20 := by
    by_contra hcon
    push Not at hcon
    have h1 : (200 + 40 * R) / 20 < d * Real.log U := by
      calc (200 + 40 * R) / 20 = 1 / 20 * (200 + 40 * R) := by ring
        _ < d * (200 + 40 * R) := by
            apply mul_lt_mul_of_pos_right hcon
            linarith
        _ ≤ d * Real.log U := mul_le_mul_of_nonneg_left hlogU hd.le
    linarith
  -- the parameter `u = a^{1/100}`
  have ha0 : 0 < a := by linarith
  have haU8 : U ^ ((1 : ℝ) / 8) ≤ a :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)) haU
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = a ^ ((1 : ℝ) / 100) := ⟨_, rfl⟩
  have hu2 : 2 ≤ u := by
    have e : ((2 : ℝ) ^ 100) ^ ((1 : ℝ) / 100) = 2 := by
      rw [← Real.rpow_natCast (2 : ℝ) 100, ← Real.rpow_mul (by norm_num),
        show ((100 : ℕ) : ℝ) * (1 / 100) = (1 : ℝ) by norm_num, Real.rpow_one]
    rw [hudef, ← e]
    exact Real.rpow_le_rpow (by positivity) h2100 (by norm_num)
  have hu0 : 0 < u := by linarith
  have ha1 : (1 : ℝ) ≤ a := le_trans (one_le_pow₀ (by norm_num)) h2100
  have hNu : (N U : ℝ) ≤ u ^ 43 := by
    have hUa : U ≤ a ^ ((50 : ℝ) / 49) := by
      calc U = (U ^ ((49 : ℝ) / 50)) ^ ((50 : ℝ) / 49) := by
            rw [← Real.rpow_mul hU0.le]
            norm_num
        _ ≤ a ^ ((50 : ℝ) / 49) := Real.rpow_le_rpow (by positivity) haU (by norm_num)
    calc (N U : ℝ) ≤ U ^ ((21 : ℝ) / 50) := hNle
      _ ≤ (a ^ ((50 : ℝ) / 49)) ^ ((21 : ℝ) / 50) := Real.rpow_le_rpow hU0.le hUa (by norm_num)
      _ = a ^ ((3 : ℝ) / 7) := by
          rw [← Real.rpow_mul ha0.le]
          norm_num
      _ ≤ a ^ ((43 : ℝ) / 100) := Real.rpow_le_rpow_of_exponent_le ha1 (by norm_num)
      _ = u ^ 43 := by
          rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
          norm_num
  have hu5 : U ^ ((49 : ℝ) / 1000) ≤ u ^ 5 := by
    calc U ^ ((49 : ℝ) / 1000) = (U ^ ((49 : ℝ) / 50)) ^ ((1 : ℝ) / 100 * 5) := by
          rw [← Real.rpow_mul hU0.le]
          norm_num
      _ ≤ a ^ ((1 : ℝ) / 100 * 5) := Real.rpow_le_rpow (by positivity) haU (by norm_num)
      _ = u ^ 5 := by
          rw [hudef, Real.rpow_mul ha0.le, ← Real.rpow_natCast]
          norm_num
  -- the block parameters
  have hu100 : u ^ 100 = a := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
    norm_num
  have hp : a = u ^ 100 := hu100.symm
  have h95 : u ^ 95 ≤ u ^ 100 / 2 := by
    have h5 : 2 ≤ u ^ 5 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu2 5)
    have : u ^ 100 = u ^ 95 * u ^ 5 := by ring
    rw [this]
    nlinarith [pow_pos hu0 95]
  have hη : 0 < u ^ 95 := by positivity
  have h4 : (4 : ℝ) ≤ a - u ^ 95 := by
    have : (2 : ℝ) ^ 100 ≤ u ^ 100 := pow_le_pow_left₀ (by norm_num) hu2 100
    have h16 : (16 : ℝ) ≤ (2 : ℝ) ^ 100 := by norm_num
    linarith
  have hq2 : v ≤ 2 * u ^ 100 := by rw [← hp]; exact hv2
  have hηa : u ^ 95 ≤ a := by
    rw [hp]
    linarith [pow_pos hu0 100]
  have hlen : 0 ≤ v - a + 2 * u ^ 95 := by linarith
  set b : ℕ → ℂ := fun n => ((w U n : ℝ) : ℂ) with hb
  have hbn := norm_ofReal_coeff_le (hw U)
  -- Step A: window domination
  have hA := intervalIntegral_le_window_integral hη hav
    (continuousOn_normSq_zeta_mul_edPoly (d := d) (q := v) h4 b (N U))
    (fun t => by positivity)
  -- Step B: the block inequality
  have hB := integral_window_normSq_le hd hd8 (x := u ^ 100) (by positivity) hη h4 hav
    (N := N U) (b := b) (a := w U) (fun n _ => rfl)
  -- Step C: the main term
  have hmain := (hmainU d hd hd8 hRd hdU1 a v (u ^ 95) hη h4 hav hvU hηa
    (by rw [hp]; linarith only [h95]) haU8).trans (mul_le_mul_of_nonneg_left hUA.le hlen)
  -- Step D: the error
  have herr : ∑ h ∈ Finset.Icc 1 (N U), ∑ k ∈ Finset.Icc 1 (N U),
        ‖b h‖ * ‖b k‖
          * ‖pairError d (u ^ 100) a v (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
      ≤ (v - a + 2 * u ^ 95) * (ε / 2) := by
    have hLf : (1 + (a - u ^ 95)) ^ (2 * d) ≤ 2 * Real.exp (4 * R) :=
      rpow_two_mul_le_two_exp hd hd8 hU1 hdU (by linarith only [h4])
        (by linarith only [hav, hvU, hU1, hη])
    have hpair : ∀ h ∈ Finset.Icc 1 (N U), ∀ k ∈ Finset.Icc 1 (N U),
        ‖b h‖ * ‖b k‖
          * ‖pairError d (u ^ 100) a v (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
        ≤ (v - a + 2 * u ^ 95)
          * ((pairStarFar CA C₁ C₂ K₁ + 2 ^ 15 * K₂ * Real.exp (4 * R)) / u ^ 98) := by
      intro h hh k hk
      have hbd := norm_pairError_le_param_far hd hd20 hu2 hp hav hq2 hNu hh hk hCA0 hCA hC₁ hC₂
        hsplit hK₁0 hK₂0 hK₁ hK₂
      have h1 : ‖b h‖ * ‖b k‖ ≤ 1 := by
        calc ‖b h‖ * ‖b k‖ ≤ 1 * 1 :=
              mul_le_mul (hbn h hh) (hbn k hk) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      calc ‖b h‖ * ‖b k‖
            * ‖pairError d (u ^ 100) a v (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
          ≤ 1 * ((v - a + 2 * u ^ 95)
            * ((pairStarFar CA C₁ C₂ K₁ + 2 ^ 14 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d)) / u ^ 98)) :=
            mul_le_mul h1 hbd (norm_nonneg _) zero_le_one
        _ ≤ (v - a + 2 * u ^ 95)
            * ((pairStarFar CA C₁ C₂ K₁ + 2 ^ 15 * K₂ * Real.exp (4 * R)) / u ^ 98) := by
            rw [one_mul]
            have h2 : 2 ^ 14 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d)
                ≤ 2 ^ 14 * K₂ * (2 * Real.exp (4 * R)) :=
              mul_le_mul_of_nonneg_left hLf (by positivity)
            have : pairStarFar CA C₁ C₂ K₁ + 2 ^ 14 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d)
                ≤ pairStarFar CA C₁ C₂ K₁ + 2 ^ 15 * K₂ * Real.exp (4 * R) := by linarith only [h2]
            gcongr
    have hsum := Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun k hk => hpair h hh k hk
    refine hsum.trans ?_
    rw [Finset.sum_const, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, nsmul_eq_mul,
      Nat.add_sub_cancel]
    have hN86 : ((N U : ℝ)) * (N U : ℝ) ≤ u ^ 86 := by
      calc ((N U : ℝ)) * (N U : ℝ) ≤ u ^ 43 * u ^ 43 :=
            mul_le_mul hNu hNu (Nat.cast_nonneg _) (by positivity)
        _ = u ^ 86 := by ring
    have hK0 : 0 ≤ pairStarFar CA C₁ C₂ K₁ + 2 ^ 15 * K₂ * Real.exp (4 * R) := by positivity
    have hfin : (pairStarFar CA C₁ C₂ K₁ + 2 ^ 15 * K₂ * Real.exp (4 * R)) / u ^ 5 ≤ ε / 2 := by
      have h1 : (pairStarFar CA C₁ C₂ K₁ + 2 ^ 15 * K₂ * Real.exp (4 * R)) / u ^ 5
          ≤ (pairStarFar CA C₁ C₂ K₁ + 2 ^ 15 * K₂ * Real.exp (4 * R))
            * U ^ (-((49 : ℝ) / 1000)) := by
        rw [div_eq_mul_inv, Real.rpow_neg hU0.le]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hu5) hK0
      exact h1.trans hUerr
    calc (N U : ℝ) * ((N U : ℝ) * ((v - a + 2 * u ^ 95)
          * ((pairStarFar CA C₁ C₂ K₁ + 2 ^ 15 * K₂ * Real.exp (4 * R)) / u ^ 98)))
        = ((N U : ℝ) * (N U : ℝ)) * ((v - a + 2 * u ^ 95)
          * ((pairStarFar CA C₁ C₂ K₁ + 2 ^ 15 * K₂ * Real.exp (4 * R)) / u ^ 98)) := by ring
      _ ≤ u ^ 86 * ((v - a + 2 * u ^ 95)
          * ((pairStarFar CA C₁ C₂ K₁ + 2 ^ 15 * K₂ * Real.exp (4 * R)) / u ^ 98)) :=
          mul_le_mul_of_nonneg_right hN86 (mul_nonneg hlen (div_nonneg hK0 (by positivity)))
      _ = (v - a + 2 * u ^ 95)
          * ((pairStarFar CA C₁ C₂ K₁ + 2 ^ 15 * K₂ * Real.exp (4 * R)) / u ^ 12) := by
          have e : u ^ 86 * ((pairStarFar CA C₁ C₂ K₁ + 2 ^ 15 * K₂ * Real.exp (4 * R)) / u ^ 98)
              = (pairStarFar CA C₁ C₂ K₁ + 2 ^ 15 * K₂ * Real.exp (4 * R)) / u ^ 12 := by
            rw [mul_div_assoc', div_eq_div_iff (pow_ne_zero _ hu0.ne') (pow_ne_zero _ hu0.ne')]
            ring
          rw [← e]
          ring
      _ ≤ (v - a + 2 * u ^ 95) * (ε / 2) := by
          apply mul_le_mul_of_nonneg_left _ hlen
          refine le_trans ?_ hfin
          apply div_le_div_of_nonneg_left hK0 (by positivity)
          exact pow_le_pow_right₀ (by linarith) (by norm_num)
  -- Step E: combine
  have h95a : u ^ 95 = a ^ ((19 : ℝ) / 20) := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
    norm_num
  calc (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
          * edPoly b (Finset.Icc 1 (N U)) (displacedLinePt d τ)‖ ^ 2)
      ≤ ∫ t, blockWindow a v (u ^ 95) t * ‖riemannZeta (displacedLinePt d t)
          * edPoly b (Finset.Icc 1 (N U)) (displacedLinePt d t)‖ ^ 2 := hA
    _ ≤ _ := hB
    _ ≤ (v - a + 2 * u ^ 95) * (c + ε / 2) + (v - a + 2 * u ^ 95) * (ε / 2) :=
        add_le_add hmain herr
    _ = (c + ε) * (v - a + 2 * a ^ ((19 : ℝ) / 20)) := by rw [← h95a]; ring

/-- **The high-block bound from a main-term bound, mollifiers up to `U^{21/50}`.**
`∫_a^v ‖ζΨ(½−d+iτ)‖² dτ ≤ (c + ε)(v − a) + ε a` for `U` large and `a ≥ U^{49/50}`. -/
theorem exists_highBlock_bound_of_mainTerm_upper {R c : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : Tendsto F atTop (𝓝 c)) (N : ℝ → ℕ) (w : ℝ → ℕ → ℝ)
    (hN : ∀ᶠ U in atTop, (N U : ℝ) ≤ U ^ ((21 : ℝ) / 50))
    (hw : ∀ U, ∀ n ∈ Finset.Icc 1 (N U), |w U n| ≤ 1)
    (hmain : ∀ᶠ U in atTop, ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U →
      d * Real.log (U - 1) ≤ R → ∀ a v η : ℝ, 0 < η → 4 ≤ a - η → a ≤ v → v ≤ U → η ≤ a →
      a / 2 ≤ a - η → U ^ ((1 : ℝ) / 8) ≤ a →
      gcdSum₂ d (N U) (w U) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
          * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
        ≤ (v - a + 2 * η) * F U) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop,
      ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U → d * Real.log (U - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → U ^ ((49 : ℝ) / 50) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
            * edPoly (fun n => ((w U n : ℝ) : ℂ)) (Finset.Icc 1 (N U)) (displacedLinePt d τ)‖ ^ 2)
          ≤ (c + ε) * (v - a) + ε * a := by
  intro ε hε
  set K : ℝ := max (2 * (c + ε) / ε) 1 with hKdef
  have hK0 : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  filter_upwards [exists_highBlock_bound_of_mainTerm_upper_window hR hF N w hN hw hmain ε hε,
    eventually_ge_atTop (K ^ ((1000 : ℝ) / 49)), eventually_ge_atTop (1 : ℝ)]
    with U hU hUbig hU1
  intro d hd hd8 hRd hdU1 a v ha haU hav hv2 hvU
  have ha0 : 0 < a := by linarith
  have h1 : 2 * (c + ε) / ε ≤ U ^ ((49 : ℝ) / 1000) := by
    calc 2 * (c + ε) / ε ≤ K := le_max_left _ _
      _ = (K ^ ((1000 : ℝ) / 49)) ^ ((49 : ℝ) / 1000) := by
          rw [← Real.rpow_mul hK0.le]; norm_num
      _ ≤ U ^ ((49 : ℝ) / 1000) := Real.rpow_le_rpow (by positivity) hUbig (by norm_num)
  have h2 : U ^ ((49 : ℝ) / 1000) ≤ a ^ ((1 : ℝ) / 20) := by
    calc U ^ ((49 : ℝ) / 1000) = (U ^ ((49 : ℝ) / 50)) ^ ((1 : ℝ) / 20) := by
          rw [← Real.rpow_mul (by linarith)]; norm_num
      _ ≤ a ^ ((1 : ℝ) / 20) := Real.rpow_le_rpow (by positivity) haU (by norm_num)
  have h3 : (c + ε) * (2 * a ^ ((19 : ℝ) / 20)) ≤ ε * a := by
    have hsplit : a = a ^ ((19 : ℝ) / 20) * a ^ ((1 : ℝ) / 20) := by
      rw [← Real.rpow_add ha0]; norm_num
    have h4 : 2 * (c + ε) ≤ ε * a ^ ((1 : ℝ) / 20) := by
      have := (div_le_iff₀ hε).mp (h1.trans h2)
      linarith only [this]
    have h5 := mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg ha0.le ((19 : ℝ) / 20))
    calc (c + ε) * (2 * a ^ ((19 : ℝ) / 20)) = a ^ ((19 : ℝ) / 20) * (2 * (c + ε)) := by ring
      _ ≤ a ^ ((19 : ℝ) / 20) * (ε * a ^ ((1 : ℝ) / 20)) := h5
      _ = ε * (a ^ ((19 : ℝ) / 20) * a ^ ((1 : ℝ) / 20)) := by ring
      _ = ε * a := by rw [← hsplit]
  have := hU d hd hd8 hRd hdU1 a v ha haU hav hv2 hvU
  linarith only [this, h3]

/-- **The upper dyadic law from a high-block bound, mollifiers up to `U^{21/50}`.** -/
theorem zetaUpperDyadicMeanSquareLaw_of_highBlock {R c : ℝ} (hR : 0 < R)
    (N : ℝ → ℕ) (w : ℝ → ℕ → ℝ)
    (hN : ∀ᶠ U in atTop, 1 ≤ N U ∧ (N U : ℝ) ≤ U ^ ((21 : ℝ) / 50))
    (hw1 : ∀ U, w U 1 = 1) (hw : ∀ U, ∀ n ∈ Finset.Icc 1 (N U), |w U n| ≤ 1)
    (hblock : ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop,
      ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U → d * Real.log (U - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → U ^ ((49 : ℝ) / 50) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
            * edPoly (fun n => ((w U n : ℝ) : ℂ)) (Finset.Icc 1 (N U)) (displacedLinePt d τ)‖ ^ 2)
          ≤ (c + ε) * (v - a) + ε * a) :
    ZetaUpperDyadicMeanSquareLaw ((49 : ℝ) / 50) R c := by
  intro ε hε
  filter_upwards [hblock ε hε, hN, Filter.eventually_ge_atTop (Real.exp 2),
    Filter.eventually_ge_atTop (Real.exp (100 * R) + 1), Filter.eventually_ge_atTop (4 : ℝ)]
    with U hblockU hNU' hUe hUR hU4
  obtain ⟨hN1, hNle⟩ := hNU'
  set b : ℕ → ℂ := fun n => ((w U n : ℝ) : ℂ) with hb
  have hbn := norm_ofReal_coeff_le (hw U)
  have hU1 : (1 : ℝ) ≤ U := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith only [this, hUe]
  have hU0 : (0 : ℝ) < U := by linarith only [hU1]
  have hU3 : (3 : ℝ) ≤ U := by
    have : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ)
      linarith only [this]
    linarith only [this, hUe]
  have hlogU : 2 ≤ Real.log U := by
    have := Real.log_le_log (Real.exp_pos 2) hUe
    rwa [Real.log_exp] at this
  have hlogU1 : 100 * R ≤ Real.log (U - 1) := by
    have := Real.log_le_log (Real.exp_pos _) (by linarith : Real.exp (100 * R) ≤ U - 1)
    rwa [Real.log_exp] at this
  have hNU : (N U : ℝ) ≤ U - 1 := by
    have h1 : U ^ ((21 : ℝ) / 50) ≤ U ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)
    have h2 : U ^ ((1 : ℝ) / 2) ≤ U / 2 := by
      have hsq : U ^ ((1 : ℝ) / 2) * U ^ ((1 : ℝ) / 2) = U := by
        rw [← Real.rpow_add hU0]
        norm_num
      have h2' : (2 : ℝ) ≤ U ^ ((1 : ℝ) / 2) := by
        have e : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
          rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num]
          exact Real.sqrt_sq (by norm_num)
        calc (2 : ℝ) = (4 : ℝ) ^ ((1 : ℝ) / 2) := e.symm
          _ ≤ U ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by norm_num) hU4 (by norm_num)
      nlinarith [Real.rpow_nonneg hU0.le ((1 : ℝ) / 2)]
    linarith only [hNle, h1, h2, hU3]
  have hNpos : (1 : ℝ) ≤ (N U : ℝ) := by exact_mod_cast hN1
  refine ⟨(N U : ℝ) ^ (5 : ℕ), b, N U, hN1, by simp [hb, hw1], hbn,
    fun n _ => Complex.conj_ofReal _, one_le_pow₀ hNpos, sum_norm_mul_rpow_four_le hbn, ?_, ?_⟩
  · rw [Real.log_pow]
    push_cast
    have : Real.log (N U : ℝ) ≤ Real.log (U - 1) :=
      Real.log_le_log (by linarith only [hNpos]) hNU
    linarith only [this]
  intro σ₀ hσ₀ hσ₀' hR1 hR2 a v ha haU hav hv2 hvU
  have hlogpos : 0 < Real.log (U - 1) := by
    have : 0 < 100 * R := by positivity
    linarith only [this, hlogU1]
  have hd : 0 < 1 / 2 - σ₀ := by linarith only [hσ₀']
  have hd100 : 1 / 2 - σ₀ ≤ 1 / 100 := by
    by_contra hcon
    rw [not_le] at hcon
    have : R < (1 / 2 - σ₀) * Real.log (U - 1) := by
      calc R = (1 / 100) * (100 * R) := by ring
        _ ≤ (1 / 100) * Real.log (U - 1) := by gcongr
        _ < (1 / 2 - σ₀) * Real.log (U - 1) := by gcongr
    linarith only [this, hR2]
  have hd8 : 1 / 2 - σ₀ ≤ 1 / 8 := by linarith only [hd100]
  have hpt : ∀ t : ℝ, (σ₀ : ℂ) + (t : ℂ) * I = displacedLinePt (1 / 2 - σ₀) t := fun t =>
    (displacedLinePt_half_sub σ₀ t).symm
  simp_rw [hpt]
  have h := hblockU (1 / 2 - σ₀) hd hd8 hR1 hR2 a v ha haU hav hv2 hvU
  have hlogU0 : 0 < Real.log U := by linarith only [hlogU]
  have : ε * a ≤ ε * (a + U / Real.log U) := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    have : 0 ≤ U / Real.log U := by positivity
    linarith only [this]
  linarith only [h, this]

end RHTower.ZetaGateProductAFE

end
