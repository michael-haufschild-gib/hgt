import GaloisForLFunctions.RHTower.ZetaGateDeepPairError
import GaloisForLFunctions.RHTower.ZetaGateProductAFEWeightedHighBlock
import GaloisForLFunctions.RHTower.GaussSpikeMass

/-!
# The dyadic mean-square law for mollifiers of length up to `U^{1/9}`

With the deep pair-error envelope (`norm_pairError_le_param_deep`) the high blocks
`U^{7/8} ≤ a ≤ v ≤ 2a ≤ 2U` accept real coefficients `|w| ≤ 1` of length `N ≤ U^{1/9} ≤ a^{13/100}`
(`exists_highBlock_bound_of_mainTerm_deep`).  Below `U^{7/8}` the mollifier is bounded on the line
`Re s = ½ − d` by `‖Ψ‖ ≤ Σ_{n ≤ N} n^{−(½−d)} ≤ 3N^{½+d}`, so `‖Ψ‖² ≤ 9 e^{4R/9} N` there, and

* the middle blocks `U^{1/2} ≤ a < U^{7/8}` cost `≪ U^{1/9 + 7/8} log U = U^{71/72} log U`;
* the low blocks `a < U^{1/2}` cost `≪ U^{1/2 + 13/50 + 1/9}` by convexity;

both negligible against `U/log U`.  This is the dyadic mean-square law for any real coefficient
family of length `≤ U^{1/9}` whose high-block main term per unit length tends to `c`
(`zetaDyadicMeanSquareLaw_of_highBlock_deep`).
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset Filter Topology
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- **The high-block bound from a main-term bound, window form.**  Let `w_U` be real coefficients
with `|w_U| ≤ 1` on `[1, N(U)]`, `N(U) ≤ U^{1/9}`, whose block main term is at most
`(v − a + 2η) F(U)` with `F(U) → c`.  Then for `U` large, every displacement `d` with
`R ≤ d log U`, `d log(U − 1) ≤ R` and every block `U^{7/8} ≤ a ≤ v ≤ 2a`, `v ≤ U`,
`∫_a^v ‖ζΨ(½−d+iτ)‖² dτ ≤ (c + ε)(v − a + 2a^{19/20})`: the taper `a^{19/20}` is the only loss, so
windows of length `≫ a^{19/20}` carry the mean square `c` per unit length. -/
theorem exists_highBlock_bound_of_mainTerm_deep_window {R c : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : Tendsto F atTop (𝓝 c)) (N : ℝ → ℕ) (w : ℝ → ℕ → ℝ)
    (hN : ∀ᶠ U in atTop, (N U : ℝ) ≤ U ^ ((1 : ℝ) / 9))
    (hw : ∀ U, ∀ n ∈ Finset.Icc 1 (N U), |w U n| ≤ 1)
    (hmain : ∀ᶠ U in atTop, ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U →
      d * Real.log (U - 1) ≤ R → ∀ a v η : ℝ, 0 < η → 4 ≤ a - η → a ≤ v → v ≤ U → η ≤ a →
      a / 2 ≤ a - η → U ^ ((1 : ℝ) / 8) ≤ a →
      gcdSum₂ d (N U) (w U) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
          * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
        ≤ (v - a + 2 * η) * F U) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop,
      ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U → d * Real.log (U - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → U ^ ((7 : ℝ) / 8) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
            * edPoly (fun n => ((w U n : ℝ) : ℂ)) (Finset.Icc 1 (N U)) (displacedLinePt d τ)‖ ^ 2)
          ≤ (c + ε) * (v - a + 2 * a ^ ((19 : ℝ) / 20)) := by
  obtain ⟨CA, hCA0, hCA⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 20) (by norm_num)
  obtain ⟨C₁, C₂, hC₁, hC₂, hsplit⟩ :=
    exists_tsum_dualOffDiagTerm_le_split 20 (K'' := 40) (by norm_num)
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_norm_smoothLeft_le_deep
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_norm_dualLeft_le_deep
  intro ε hε
  have hps := pairStar_nonneg hCA0 hC₁ hC₂ hK₁0
  filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 800), eventually_ge_atTop (Real.exp (200 + 40 * R)),
    (tendsto_order.1 hF).2 _ (show c < c + ε / 2 by linarith), hN, hmain,
    eventually_const_mul_rpow_neg_le (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R))
      ((7 : ℝ) / 160) (by norm_num) (half_pos hε)]
    with U hU2 hUe hUA hNle hmainU hUerr
  intro d hd hd8 hRd hdU1 a v ha haU hav hv2 hvU
  -- consequences of `2^(800 : ℕ) ≤ U`; the hypothesis itself is cleared (its numeral is too large for
  -- the linear-arithmetic preprocessing)
  have hU1 : (1 : ℝ) ≤ U := le_trans (one_le_pow₀ (by norm_num)) hU2
  have h2100 : (2 : ℝ) ^ 100 ≤ a := by
    have e : ((2 : ℝ) ^ 800) ^ ((1 : ℝ) / 2) = (2 : ℝ) ^ 400 := by
      rw [← Real.rpow_natCast (2 : ℝ) 800, ← Real.rpow_mul (by norm_num),
        show ((800 : ℕ) : ℝ) * (1 / 2) = ((400 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (2 : ℝ) ^ 100 ≤ (2 : ℝ) ^ 400 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      _ = ((2 : ℝ) ^ 800) ^ ((1 : ℝ) / 2) := e.symm
      _ ≤ U ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) hU2 (by norm_num)
      _ ≤ U ^ ((7 : ℝ) / 8) := Real.rpow_le_rpow_of_exponent_le
          (le_trans (one_le_pow₀ (by norm_num)) hU2) (by norm_num)
      _ ≤ a := haU
  clear hU2
  -- facts about `U`
  have hU0 : 0 < U := by linarith
  have hexp200 : Real.exp 200 ≤ U :=
    le_trans (Real.exp_le_exp.mpr (by linarith)) hUe
  have hlogU : 200 + 40 * R ≤ Real.log U := by
    have := Real.log_le_log (Real.exp_pos _) hUe
    rwa [Real.log_exp] at this
  have hU3 : (3 : ℝ) ≤ U := by
    have : (3 : ℝ) ≤ Real.exp 200 := by
      have := Real.add_one_le_exp (200 : ℝ)
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
  have hNu : (N U : ℝ) ≤ u ^ 13 := by
    have hUa : U ≤ a ^ ((8 : ℝ) / 7) := by
      calc U = (U ^ ((7 : ℝ) / 8)) ^ ((8 : ℝ) / 7) := by
            rw [← Real.rpow_mul hU0.le]
            norm_num
        _ ≤ a ^ ((8 : ℝ) / 7) := Real.rpow_le_rpow (by positivity) haU (by norm_num)
    calc (N U : ℝ) ≤ U ^ ((1 : ℝ) / 9) := hNle
      _ ≤ (a ^ ((8 : ℝ) / 7)) ^ ((1 : ℝ) / 9) := Real.rpow_le_rpow hU0.le hUa (by norm_num)
      _ = a ^ ((8 : ℝ) / 63) := by
          rw [← Real.rpow_mul ha0.le]
          norm_num
      _ ≤ a ^ ((13 : ℝ) / 100) := Real.rpow_le_rpow_of_exponent_le ha1 (by norm_num)
      _ = u ^ 13 := by
          rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
          norm_num
  have hu5 : U ^ ((7 : ℝ) / 160) ≤ u ^ 5 := by
    calc U ^ ((7 : ℝ) / 160) = (U ^ ((7 : ℝ) / 8)) ^ ((1 : ℝ) / 100 * 5) := by
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
        ‖b h‖ * ‖b k‖ * ‖pairError d (u ^ 100) a v (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
      ≤ (v - a + 2 * u ^ 95) * (ε / 2) := by
    have hLf : (1 + (a - u ^ 95)) ^ (2 * d) ≤ 2 * Real.exp (4 * R) :=
      rpow_two_mul_le_two_exp hd hd8 hU1 hdU (by linarith only [h4])
        (by linarith only [hav, hvU, hU1, hη])
    have hpair : ∀ h ∈ Finset.Icc 1 (N U), ∀ k ∈ Finset.Icc 1 (N U),
        ‖b h‖ * ‖b k‖ * ‖pairError d (u ^ 100) a v (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
        ≤ (v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 33) := by
      intro h hh k hk
      have hbd := norm_pairError_le_param_deep hd hd20 hu2 hp hav hq2 hNu hh hk hCA0 hCA hC₁ hC₂ hsplit
        hK₁0 hK₂0 hK₁ hK₂
      have h1 : ‖b h‖ * ‖b k‖ ≤ 1 := by
        calc ‖b h‖ * ‖b k‖ ≤ 1 * 1 :=
              mul_le_mul (hbn h hh) (hbn k hk) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      calc ‖b h‖ * ‖b k‖
            * ‖pairError d (u ^ 100) a v (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
          ≤ 1 * ((v - a + 2 * u ^ 95)
            * ((pairStar CA C₁ C₂ K₁ + 2 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d)) / u ^ 33)) :=
            mul_le_mul h1 hbd (norm_nonneg _) zero_le_one
        _ ≤ (v - a + 2 * u ^ 95)
            * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 33) := by
            rw [one_mul]
            have h2 : 2 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d) ≤ 2 * K₂ * (2 * Real.exp (4 * R)) :=
              mul_le_mul_of_nonneg_left hLf (by positivity)
            have : pairStar CA C₁ C₂ K₁ + 2 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d)
                ≤ pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R) := by linarith only [h2]
            gcongr
    have hsum := Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun k hk => hpair h hh k hk
    refine hsum.trans ?_
    rw [Finset.sum_const, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, nsmul_eq_mul,
      Nat.add_sub_cancel]
    have hN16 : ((N U : ℝ)) * (N U : ℝ) ≤ u ^ 26 := by
      calc ((N U : ℝ)) * (N U : ℝ) ≤ u ^ 13 * u ^ 13 :=
            mul_le_mul hNu hNu (Nat.cast_nonneg _) (by positivity)
        _ = u ^ 26 := by ring
    have hK0 : 0 ≤ pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R) := by positivity
    have hfin : (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5 ≤ ε / 2 := by
      have h1 : (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5
          ≤ (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) * U ^ (-((7 : ℝ) / 160)) := by
        rw [div_eq_mul_inv, Real.rpow_neg hU0.le]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hu5) hK0
      exact h1.trans hUerr
    calc (N U : ℝ) * ((N U : ℝ) * ((v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 33)))
        = ((N U : ℝ) * (N U : ℝ)) * ((v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 33)) := by ring
      _ ≤ u ^ 26 * ((v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 33)) :=
          mul_le_mul_of_nonneg_right hN16 (mul_nonneg hlen (div_nonneg hK0 (by positivity)))
      _ = (v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 7) := by
          have e : u ^ 26 * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 33)
              = (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 7 := by
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

/-- **The high-block bound from a main-term bound, mollifiers up to `U^{1/9}`.**  Under the
hypotheses of `exists_highBlock_bound_of_mainTerm_deep_window`,
`∫_a^v ‖ζΨ(½−d+iτ)‖² dτ ≤ (c + ε)(v − a) + ε a` for `U` large: on `a ≥ U^{7/8}` the taper
`2(c + ε)a^{19/20}` is at most `ε a`. -/
theorem exists_highBlock_bound_of_mainTerm_deep {R c : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : Tendsto F atTop (𝓝 c)) (N : ℝ → ℕ) (w : ℝ → ℕ → ℝ)
    (hN : ∀ᶠ U in atTop, (N U : ℝ) ≤ U ^ ((1 : ℝ) / 9))
    (hw : ∀ U, ∀ n ∈ Finset.Icc 1 (N U), |w U n| ≤ 1)
    (hmain : ∀ᶠ U in atTop, ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U →
      d * Real.log (U - 1) ≤ R → ∀ a v η : ℝ, 0 < η → 4 ≤ a - η → a ≤ v → v ≤ U → η ≤ a →
      a / 2 ≤ a - η → U ^ ((1 : ℝ) / 8) ≤ a →
      gcdSum₂ d (N U) (w U) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
          * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
        ≤ (v - a + 2 * η) * F U) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop,
      ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U → d * Real.log (U - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → U ^ ((7 : ℝ) / 8) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
            * edPoly (fun n => ((w U n : ℝ) : ℂ)) (Finset.Icc 1 (N U)) (displacedLinePt d τ)‖ ^ 2)
          ≤ (c + ε) * (v - a) + ε * a := by
  intro ε hε
  set K : ℝ := max (2 * (c + ε) / ε) 1 with hKdef
  have hK0 : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  filter_upwards [exists_highBlock_bound_of_mainTerm_deep_window hR hF N w hN hw hmain ε hε,
    eventually_ge_atTop (K ^ ((160 : ℝ) / 7)), eventually_ge_atTop (1 : ℝ)]
    with U hU hUbig hU1
  intro d hd hd8 hRd hdU1 a v ha haU hav hv2 hvU
  have ha0 : 0 < a := by linarith
  -- `a^{1/20} ≥ U^{7/160} ≥ 2(c + ε)/ε`
  have h1 : 2 * (c + ε) / ε ≤ U ^ ((7 : ℝ) / 160) := by
    calc 2 * (c + ε) / ε ≤ K := le_max_left _ _
      _ = (K ^ ((160 : ℝ) / 7)) ^ ((7 : ℝ) / 160) := by
          rw [← Real.rpow_mul hK0.le]; norm_num
      _ ≤ U ^ ((7 : ℝ) / 160) := Real.rpow_le_rpow (by positivity) hUbig (by norm_num)
  have h2 : U ^ ((7 : ℝ) / 160) ≤ a ^ ((1 : ℝ) / 20) := by
    calc U ^ ((7 : ℝ) / 160) = (U ^ ((7 : ℝ) / 8)) ^ ((1 : ℝ) / 20) := by
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


/-! ## The mollifier on the displaced line -/

/-- `‖Ψ(½ − d + iτ)‖ ≤ 3 N^{½+d}` for coefficients of modulus at most one. -/
theorem norm_edPoly_displaced_le {b : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (hbn : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) {d : ℝ} (hd : 0 ≤ d) (hd4 : d ≤ 1 / 4) (τ : ℝ) :
    ‖edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ≤ 3 * (N : ℝ) ^ (1 / 2 + d) := by
  classical
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsum : ‖edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖
      ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 - d)) := by
    unfold edPoly
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [norm_mul]
    have hpow : ‖((n : ℝ) : ℂ) ^ (-(displacedLinePt d τ))‖ = (n : ℝ) ^ (-(1 / 2 - d)) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn1)]
      simp [displacedLinePt]
    rw [hpow]
    calc ‖b n‖ * (n : ℝ) ^ (-(1 / 2 - d)) ≤ 1 * (n : ℝ) ^ (-(1 / 2 - d)) :=
          mul_le_mul_of_nonneg_right (hbn n hn) (by positivity)
      _ = (n : ℝ) ^ (-(1 / 2 - d)) := one_mul _
  have hhead := sum_rpow_neg_head_le (c := 1 / 2 - d) (by linarith) (by linarith) N
  have hNp : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 + d) := Real.one_le_rpow hN1 (by linarith)
  have e : (N : ℝ) ^ (1 - (1 / 2 - d)) = (N : ℝ) ^ (1 / 2 + d) := by ring_nf
  rw [e] at hhead
  have h2 : (N : ℝ) ^ (1 / 2 + d) / (1 - (1 / 2 - d)) ≤ 2 * (N : ℝ) ^ (1 / 2 + d) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- `‖Ψ‖² ≤ 9 e^{4R/9} N` on the line, for `N ≤ U^{1/9}` and `d log U ≤ 2R`. -/
theorem normSq_edPoly_displaced_le {b : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (hbn : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) {d U R : ℝ} (hd : 0 ≤ d) (hd4 : d ≤ 1 / 4)
    (hU1 : 1 ≤ U) (hNU : (N : ℝ) ≤ U ^ ((1 : ℝ) / 9)) (hdU : d * Real.log U ≤ 2 * R) (τ : ℝ) :
    ‖edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2
      ≤ 9 * Real.exp (4 * R / 9) * U ^ ((1 : ℝ) / 9) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hU0 : 0 < U := by linarith
  have h := norm_edPoly_displaced_le hN hbn hd hd4 τ
  have hsq : ‖edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2
      ≤ (3 * (N : ℝ) ^ (1 / 2 + d)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have e1 : (3 * (N : ℝ) ^ (1 / 2 + d)) ^ 2 = 9 * ((N : ℝ) * (N : ℝ) ^ (2 * d)) := by
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (1 / 2 + d)) 2, ← Real.rpow_mul (by positivity),
      show (1 / 2 + d) * ((2 : ℕ) : ℝ) = 1 + 2 * d by push_cast; ring,
      Real.rpow_add (by positivity), Real.rpow_one]
    norm_num
  have hN2d : (N : ℝ) ^ (2 * d) ≤ Real.exp (4 * R / 9) := by
    calc (N : ℝ) ^ (2 * d) ≤ (U ^ ((1 : ℝ) / 9)) ^ (2 * d) :=
          Real.rpow_le_rpow (by positivity) hNU (by linarith)
      _ = Real.exp (Real.log U * (2 * d / 9)) := by
          rw [← Real.rpow_mul hU0.le, Real.rpow_def_of_pos hU0]
          ring_nf
      _ ≤ Real.exp (4 * R / 9) := by
          apply Real.exp_le_exp.mpr
          nlinarith
  calc ‖edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2
      ≤ 9 * ((N : ℝ) * (N : ℝ) ^ (2 * d)) := hsq.trans (le_of_eq e1)
    _ ≤ 9 * (U ^ ((1 : ℝ) / 9) * Real.exp (4 * R / 9)) := by
        gcongr
    _ = 9 * Real.exp (4 * R / 9) * U ^ ((1 : ℝ) / 9) := by ring

/-- **Blocks with a bounded mollifier.**  If `‖Ψ‖² ≤ B` on the line, then
`∫_a^v ‖ζΨ‖² ≤ B ∫_a^v ‖ζ‖²`. -/
theorem integral_normSq_zeta_mul_edPoly_le_of_normSq_le {d a v B : ℝ} (hd : 0 < d)
    (hav : a ≤ v) {b : ℕ → ℂ} {N : ℕ}
    (hB : ∀ τ : ℝ, ‖edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2 ≤ B) :
    (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ) *
        edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2) ≤
      B * ∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)‖ ^ 2 := by
  have hcont1 : Continuous (fun τ : ℝ => ‖riemannZeta (displacedLinePt d τ) *
      edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2) :=
    ((continuous_riemannZeta_displacedLinePt hd).mul
      (continuous_edPoly_displacedLinePt b N d)).norm.pow 2
  have hcont2 : Continuous (fun τ : ℝ => B * ‖riemannZeta (displacedLinePt d τ)‖ ^ 2) :=
    continuous_const.mul ((continuous_riemannZeta_displacedLinePt hd).norm.pow 2)
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hav (hcont1.intervalIntegrable a v)
    (hcont2.intervalIntegrable a v) fun τ _ => ?_
  rw [norm_mul, mul_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (hB τ) (sq_nonneg _)

/-- **Low blocks by convexity with a bounded mollifier.** -/
theorem integral_normSq_zeta_mul_edPoly_convexity_of_normSq_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ σ t : ℝ, -(1 / 100) ≤ σ → σ ≤ 1 + 1 / 100 → 8 ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * t ^ ((1 + 1 / 100 - σ) / 2))
    {d a v B : ℝ} (hd : 0 < d) (hd' : d ≤ 1 / 100) (ha : 8 ≤ a) (hav : a ≤ v)
    {b : ℕ → ℂ} {N : ℕ}
    (hB : ∀ τ : ℝ, ‖edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2 ≤ B) :
    (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ) *
        edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2) ≤
      (v - a) * ((C * v ^ ((13 : ℝ) / 50)) ^ 2 * B) := by
  have hv1 : 1 ≤ v := by linarith
  have hM0 : 0 ≤ C * v ^ ((13 : ℝ) / 50) := mul_nonneg hC0 (by positivity)
  have hpoint : ∀ τ ∈ Set.Icc a v,
      ‖riemannZeta (displacedLinePt d τ) * edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2 ≤
        (C * v ^ ((13 : ℝ) / 50)) ^ 2 * B := by
    intro τ hτ
    have hτ8 : 8 ≤ τ := by linarith [hτ.1]
    have hτ1 : 1 ≤ τ := by linarith
    have hζ : ‖riemannZeta (displacedLinePt d τ)‖ ≤ C * v ^ ((13 : ℝ) / 50) := by
      have h := hC (1 / 2 - d) τ (by linarith) (by linarith) hτ8
      have hpt : displacedLinePt d τ = (((1 / 2 - d : ℝ)) : ℂ) + (τ : ℂ) * I := rfl
      rw [hpt]
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hC0)
      calc τ ^ ((1 + 1 / 100 - (1 / 2 - d)) / 2) ≤ τ ^ ((13 : ℝ) / 50) :=
            Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith)
        _ ≤ v ^ ((13 : ℝ) / 50) := Real.rpow_le_rpow (by linarith) hτ.2 (by norm_num)
    rw [norm_mul, mul_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hζ 2) (hB τ) (sq_nonneg _) (sq_nonneg _)
  have hcont : Continuous (fun τ : ℝ => ‖riemannZeta (displacedLinePt d τ) *
      edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2) :=
    ((continuous_riemannZeta_displacedLinePt hd).mul
      (continuous_edPoly_displacedLinePt b N d)).norm.pow 2
  have hgint : IntervalIntegrable (fun _ : ℝ => (C * v ^ ((13 : ℝ) / 50)) ^ 2 * B) volume a v :=
    (continuous_const : Continuous (fun _ : ℝ =>
      (C * v ^ ((13 : ℝ) / 50)) ^ 2 * B)).intervalIntegrable a v
  have h := intervalIntegral.integral_mono_on hav (hcont.intervalIntegrable a v) hgint hpoint
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  exact h

/-- `(v − a)(C v^{13/50})² · B ≤ 4C²B U^{1/2 + 13/50}` on a low block `v ≤ 2U^{1/2}`. -/
theorem lowBlock_power_le_of_bound {C U a v B : ℝ} (hU1 : 1 ≤ U) (ha : 0 ≤ a) (hav : a ≤ v)
    (hB : 0 ≤ B) (hv : v ≤ 2 * U ^ ((1 : ℝ) / 2)) :
    (v - a) * ((C * v ^ ((13 : ℝ) / 50)) ^ 2 * B)
      ≤ 16 * C ^ 2 * B * U ^ ((1 : ℝ) / 2 + 13 / 50) := by
  have hU0 : 0 < U := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hv13 : v ^ ((13 : ℝ) / 50) ≤ 2 * U ^ ((13 : ℝ) / 100) := by
    calc v ^ ((13 : ℝ) / 50) ≤ (2 * U ^ ((1 : ℝ) / 2)) ^ ((13 : ℝ) / 50) :=
          Real.rpow_le_rpow hv0 hv (by norm_num)
      _ = 2 ^ ((13 : ℝ) / 50) * U ^ ((13 : ℝ) / 100) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hU0.le]
          norm_num
      _ ≤ 2 * U ^ ((13 : ℝ) / 100) := by
          have : (2 : ℝ) ^ ((13 : ℝ) / 50) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          rw [Real.rpow_one] at this
          exact mul_le_mul_of_nonneg_right this (by positivity)
  have hsq : (C * v ^ ((13 : ℝ) / 50)) ^ 2 ≤ 4 * C ^ 2 * U ^ ((13 : ℝ) / 50) := by
    have h1 : (C * v ^ ((13 : ℝ) / 50)) ^ 2 = C ^ 2 * (v ^ ((13 : ℝ) / 50)) ^ 2 := by ring
    have h2 : (v ^ ((13 : ℝ) / 50)) ^ 2 ≤ (2 * U ^ ((13 : ℝ) / 100)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hv13 2
    have h3 : (2 * U ^ ((13 : ℝ) / 100)) ^ 2 = 4 * U ^ ((13 : ℝ) / 50) := by
      rw [mul_pow, ← Real.rpow_natCast (U ^ ((13 : ℝ) / 100)) 2, ← Real.rpow_mul hU0.le]
      norm_num
    rw [h1]
    nlinarith [sq_nonneg C]
  have hva : v - a ≤ 2 * U ^ ((1 : ℝ) / 2) := by linarith
  have hsplit : U ^ ((1 : ℝ) / 2 + 13 / 50) = U ^ ((1 : ℝ) / 2) * U ^ ((13 : ℝ) / 50) :=
    Real.rpow_add hU0 _ _
  calc (v - a) * ((C * v ^ ((13 : ℝ) / 50)) ^ 2 * B)
      ≤ (2 * U ^ ((1 : ℝ) / 2)) * ((4 * C ^ 2 * U ^ ((13 : ℝ) / 50)) * B) :=
        mul_le_mul hva (mul_le_mul_of_nonneg_right hsq hB) (by positivity) (by positivity)
    _ ≤ 16 * C ^ 2 * B * U ^ ((1 : ℝ) / 2 + 13 / 50) := by
        rw [hsplit]
        have : 0 ≤ C ^ 2 * B * (U ^ ((1 : ℝ) / 2) * U ^ ((13 : ℝ) / 50)) := by positivity
        nlinarith

/-! ## The dyadic law -/

/-- **The dyadic mean-square law from a high-block bound, mollifiers up to `U^{1/9}`.** -/
theorem zetaDyadicMeanSquareLaw_of_highBlock_deep {R c : ℝ} (hR : 0 < R) (hc : 0 ≤ c)
    (N : ℝ → ℕ) (w : ℝ → ℕ → ℝ)
    (hN : ∀ᶠ U in atTop, 1 ≤ N U ∧ (N U : ℝ) ≤ U ^ ((1 : ℝ) / 9))
    (hw1 : ∀ U, w U 1 = 1) (hw : ∀ U, ∀ n ∈ Finset.Icc 1 (N U), |w U n| ≤ 1)
    (hblock : ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop,
      ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U → d * Real.log (U - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → U ^ ((7 : ℝ) / 8) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
            * edPoly (fun n => ((w U n : ℝ) : ℂ)) (Finset.Icc 1 (N U)) (displacedLinePt d τ)‖ ^ 2)
          ≤ (c + ε) * (v - a) + ε * a) :
    ZetaDyadicMeanSquareLaw R c := by
  obtain ⟨C, hC, hconv⟩ := exists_norm_riemannZeta_le_convexity (η := 1 / 100) (by norm_num)
    (by norm_num)
  obtain ⟨K, hK0, hzeta⟩ := exists_zetaBlock_meanSquare_le hR
  intro ε hε
  set E : ℝ := 9 * Real.exp (4 * R / 9) with hE
  have hE0 : 0 ≤ E := by positivity
  filter_upwards [hblock ε hε, hzeta, hN, Filter.eventually_ge_atTop (Real.exp 2),
    Filter.eventually_ge_atTop (Real.exp (100 * R) + 1),
    Filter.eventually_ge_atTop ((2 : ℝ) ^ 100),
    eventually_const_mul_rpow_neg_mul_log_pow_le (16 * C ^ 2 * E) ((29 : ℝ) / 225)
      (by norm_num) 1 hε,
    eventually_const_mul_rpow_neg_mul_log_pow_le (E * K) ((1 : ℝ) / 72) (by norm_num) 2 hε]
    with U hblockU hzetaU hNU' hUe hUR hU2 hlow hmidε
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
  have hU25 : (2 : ℝ) ≤ U ^ ((1 : ℝ) / 15) :=
    two_le_rpow_one_div_fifteen (le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hU2)
  have hNU : (N U : ℝ) ≤ U - 1 := by
    have h1 : U ^ ((1 : ℝ) / 9) ≤ U ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)
    have h2 : U ^ ((1 : ℝ) / 2) ≤ U / 2 := by
      have hsq : U ^ ((1 : ℝ) / 2) * U ^ ((1 : ℝ) / 2) = U := by
        rw [← Real.rpow_add hU0]
        norm_num
      have h4 : (2 : ℝ) ≤ U ^ ((1 : ℝ) / 2) :=
        le_trans hU25 (Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num))
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
  intro σ₀ hσ₀ hσ₀' hR1 hR2 a v ha hav hv2 hvU
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
  have hdU : (1 / 2 - σ₀) * Real.log U ≤ 2 * R := by
    have hlog2 : Real.log U ≤ 2 * Real.log (U - 1) := by
      have h1 : U ≤ (U - 1) ^ 2 := by
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ U - 3) hU0.le
        nlinarith [this]
      have h2 : Real.log U ≤ Real.log ((U - 1) ^ 2) := Real.log_le_log hU0 h1
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith only [h2]
    calc (1 / 2 - σ₀) * Real.log U ≤ (1 / 2 - σ₀) * (2 * Real.log (U - 1)) :=
          mul_le_mul_of_nonneg_left hlog2 hd.le
      _ = 2 * ((1 / 2 - σ₀) * Real.log (U - 1)) := by ring
      _ ≤ 2 * R := by linarith only [hR2]
  have hBline : ∀ τ : ℝ, ‖edPoly b (Finset.Icc 1 (N U)) (displacedLinePt (1 / 2 - σ₀) τ)‖ ^ 2
      ≤ E * U ^ ((1 : ℝ) / 9) := fun τ =>
    normSq_edPoly_displaced_le hN1 hbn hd.le (by linarith only [hd8]) hU1 hNle hdU τ
  have hB0 : 0 ≤ E * U ^ ((1 : ℝ) / 9) := by positivity
  have hva0 : 0 ≤ (c + ε) * (v - a) :=
    mul_nonneg (by positivity) (by linarith only [hav])
  have hUlog : ε * (U / Real.log U) ≤ ε * (a + U / Real.log U) := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    linarith only [ha]
  have hlogU0 : 0 < Real.log U := by linarith only [hlogU]
  rcases le_or_gt (U ^ ((7 : ℝ) / 8)) a with hhigh | hnhigh
  · have h := hblockU (1 / 2 - σ₀) hd hd8 hR1 hR2 a v ha hhigh hav hv2 hvU
    have : ε * a ≤ ε * (a + U / Real.log U) := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      have : 0 ≤ U / Real.log U := by positivity
      linarith only [this]
    linarith only [h, this]
  rcases le_or_gt (U ^ ((1 : ℝ) / 2)) a with hmid | hlow'
  · -- the middle blocks by the mean square of `ζ` and the bound on the mollifier
    have hU8a : U ^ ((1 : ℝ) / 8) ≤ a :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)) hmid
    have hz := hzetaU (1 / 2 - σ₀) hd hd8 hR1 hdU a v hU8a hav hv2 hvU
    have hm := integral_normSq_zeta_mul_edPoly_le_of_normSq_le hd hav hBline
    have hKa : K * Real.log U * a ≤ K * Real.log U * U ^ ((7 : ℝ) / 8) :=
      mul_le_mul_of_nonneg_left hnhigh.le (by positivity)
    have hint0 : 0 ≤ ∫ τ in a..v, ‖riemannZeta (displacedLinePt (1 / 2 - σ₀) τ)‖ ^ 2 :=
      intervalIntegral.integral_nonneg hav fun τ _ => by positivity
    have hstep : E * U ^ ((1 : ℝ) / 9)
          * ∫ τ in a..v, ‖riemannZeta (displacedLinePt (1 / 2 - σ₀) τ)‖ ^ 2
        ≤ E * U ^ ((1 : ℝ) / 9) * (K * Real.log U * U ^ ((7 : ℝ) / 8)) :=
      mul_le_mul_of_nonneg_left (hz.trans hKa) hB0
    have hsplit : E * U ^ ((1 : ℝ) / 9) * (K * Real.log U * U ^ ((7 : ℝ) / 8))
        = (E * K * (U ^ (-((1 : ℝ) / 72)) * Real.log U ^ 2)) * (U / Real.log U) := by
      have e : U ^ ((1 : ℝ) / 9) * U ^ ((7 : ℝ) / 8) = U ^ (-((1 : ℝ) / 72)) * U := by
        rw [← Real.rpow_add hU0, show (1 : ℝ) / 9 + 7 / 8 = -((1 : ℝ) / 72) + 1 by norm_num,
          Real.rpow_add hU0, Real.rpow_one]
      have e2 : E * U ^ ((1 : ℝ) / 9) * (K * Real.log U * U ^ ((7 : ℝ) / 8))
          = E * K * Real.log U * (U ^ ((1 : ℝ) / 9) * U ^ ((7 : ℝ) / 8)) := by ring
      rw [e2, e]
      field_simp
    have hmain : (E * K * (U ^ (-((1 : ℝ) / 72)) * Real.log U ^ 2)) * (U / Real.log U)
        ≤ ε * (U / Real.log U) := mul_le_mul_of_nonneg_right hmidε (by positivity)
    rw [hsplit] at hstep
    linarith only [hm, hstep, hmain, hUlog, hva0]
  · -- the low blocks by convexity and the bound on the mollifier
    have hcx := integral_normSq_zeta_mul_edPoly_convexity_of_normSq_le hC.le hconv hd hd100
      (by linarith only [ha]) hav hBline
    have hv : v ≤ 2 * U ^ ((1 : ℝ) / 2) := by linarith only [hv2, hlow']
    have hpw := lowBlock_power_le_of_bound (C := C) hU1 (by linarith only [ha]) hav hB0 hv
    have hsplit : 16 * C ^ 2 * (E * U ^ ((1 : ℝ) / 9)) * U ^ ((1 : ℝ) / 2 + 13 / 50) =
        (16 * C ^ 2 * E * (U ^ (-((29 : ℝ) / 225)) * Real.log U ^ 1)) * (U / Real.log U) := by
      rw [pow_one]
      have e : U ^ ((1 : ℝ) / 9) * U ^ ((1 : ℝ) / 2 + 13 / 50)
          = U ^ (-((29 : ℝ) / 225)) * U := by
        rw [← Real.rpow_add hU0, show (1 : ℝ) / 9 + (1 / 2 + 13 / 50) = -((29 : ℝ) / 225) + 1 by
          norm_num, Real.rpow_add hU0, Real.rpow_one]
      have e2 : 16 * C ^ 2 * (E * U ^ ((1 : ℝ) / 9)) * U ^ ((1 : ℝ) / 2 + 13 / 50)
          = 16 * C ^ 2 * E * (U ^ ((1 : ℝ) / 9) * U ^ ((1 : ℝ) / 2 + 13 / 50)) := by ring
      rw [e2, e]
      field_simp
    have hmain : 16 * C ^ 2 * (E * U ^ ((1 : ℝ) / 9)) * U ^ ((1 : ℝ) / 2 + 13 / 50)
        ≤ ε * (a + U / Real.log U) := by
      rw [hsplit]
      exact (mul_le_mul_of_nonneg_right hlow (by positivity)).trans hUlog
    linarith only [hcx, hpw, hmain, hva0]

end RHTower.ZetaGateProductAFE

end
