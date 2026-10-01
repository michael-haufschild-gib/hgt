import GaloisForLFunctions.RHTower.ZetaOffLineMomentExplicit

/-!
# The dyadic mean-square law for an arbitrary bounded real mollifier

The block inequality `integral_window_normSq_le` holds for every real coefficient vector.  For a
family of real coefficients `w_U` with `|w_U(n)| ≤ 1`, `w_U(1) = 1` and length `N(U) ≤ U^{1/15}`,
only the main term `S₂(w_U) · ‖ζ(1+2d)‖ · ‖∫ w χχ‖` depends on the coefficients beyond these
bounds.  If the main term per unit window mass is at most `F(U)` with `F(U) → c`, then

* `∫_a^v ‖ζΨ(½−d+it)‖² dt ≤ (c + ε)(v − a) + ε a` on every high block `U^{5/6} ≤ a ≤ v ≤ 2a ≤ 2U`
  (`exists_highBlock_bound_of_mainTerm`), and
* the dyadic mean-square law with constant `c` holds (`zetaDyadicMeanSquareLaw_of_highBlock`).

The pair errors, the window domination and the middle and low ranges are those of the
Barban–Vehov case, which only use `|w| ≤ 1` and `N ≤ U^{1/15}`.
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset Filter Topology
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

theorem norm_ofReal_coeff_le {w : ℕ → ℝ} {N : ℕ} (hw : ∀ n ∈ Finset.Icc 1 N, |w n| ≤ 1) :
    ∀ n ∈ Finset.Icc 1 N, ‖((w n : ℝ) : ℂ)‖ ≤ 1 := fun n hn => by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hw n hn

theorem sum_norm_mul_rpow_four_le {b : ℕ → ℂ} {N : ℕ} (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) :
    (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ (N : ℝ) ^ (5 : ℕ) := by
  have hterm : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ)) ≤ (N : ℝ) ^ (4 : ℕ) := by
    intro n hn
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc ‖b n‖ * ((n : ℝ) ^ (4 : ℝ)) ≤ 1 * ((N : ℝ) ^ (4 : ℝ)) :=
          mul_le_mul (hb n hn) (Real.rpow_le_rpow hn0 hnN (by norm_num)) (by positivity)
            zero_le_one
      _ = (N : ℝ) ^ (4 : ℕ) := by rw [one_mul, Real.rpow_ofNat]
  calc (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ)))
      ≤ ∑ _n ∈ Finset.Icc 1 N, (N : ℝ) ^ (4 : ℕ) := Finset.sum_le_sum hterm
    _ = (N : ℝ) * (N : ℝ) ^ (4 : ℕ) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp
    _ = (N : ℝ) ^ (5 : ℕ) := by ring

/-- **The high-block bound from a main-term bound.**  Let `w_U` be real coefficients with
`|w_U| ≤ 1` on `[1, N(U)]`, `N(U) ≤ U^{1/15}`, whose block main term is at most
`(v − a + 2η) F(U)` with `F(U) → c`.  Then for `U` large, every displacement `d` with
`R ≤ d log U`, `d log(U − 1) ≤ R` and every block `U^{5/6} ≤ a ≤ v ≤ 2a`, `v ≤ U`,
`∫_a^v ‖ζΨ(½−d+iτ)‖² dτ ≤ (c + ε)(v − a) + ε a`. -/
theorem exists_highBlock_bound_of_mainTerm {R c : ℝ} {F : ℝ → ℝ}
    (hF : Tendsto F atTop (𝓝 c)) (N : ℝ → ℕ) (w : ℝ → ℕ → ℝ)
    (hN : ∀ᶠ U in atTop, (N U : ℝ) ≤ U ^ ((1 : ℝ) / 15))
    (hw : ∀ U, ∀ n ∈ Finset.Icc 1 (N U), |w U n| ≤ 1)
    (hmain : ∀ᶠ U in atTop, ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U →
      d * Real.log (U - 1) ≤ R → ∀ a v η : ℝ, 0 < η → 4 ≤ a - η → a ≤ v → v ≤ U → η ≤ a →
      a / 2 ≤ a - η → U ^ ((1 : ℝ) / 8) ≤ a →
      gcdSum₂ d (N U) (w U) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
          * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
        ≤ (v - a + 2 * η) * F U) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop,
      ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U → d * Real.log (U - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → U ^ ((5 : ℝ) / 6) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
            * edPoly (fun n => ((w U n : ℝ) : ℂ)) (Finset.Icc 1 (N U)) (displacedLinePt d τ)‖ ^ 2)
          ≤ (c + ε) * (v - a) + ε * a := by
  obtain ⟨CA, hCA0, hCA⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 20) (by norm_num)
  obtain ⟨C₁, C₂, hC₁, hC₂, hsplit⟩ :=
    exists_tsum_dualOffDiagTerm_le_split 20 (K'' := 40) (by norm_num)
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_norm_smoothDiagonal_left_le
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_norm_dualDiagonal_left_le
  intro ε hε
  have hps := pairStar_nonneg hCA0 hC₁ hC₂ hK₁0
  filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 800), eventually_ge_atTop (Real.exp 200),
    (tendsto_order.1 hF).2 _ (show c < c + ε / 2 by linarith), hN, hmain,
    eventually_const_mul_rpow_neg_le (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R))
      ((1 : ℝ) / 160) (by norm_num) (half_pos hε),
    eventually_const_mul_rpow_neg_le (4 * (c + ε) / ε) ((1 : ℝ) / 160)
      (by norm_num) one_pos]
    with U hU2 hUe hUA hNle hmainU hUerr hUη
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
      _ ≤ U ^ ((5 : ℝ) / 6) := Real.rpow_le_rpow_of_exponent_le
          (le_trans (one_le_pow₀ (by norm_num)) hU2) (by norm_num)
      _ ≤ a := haU
  clear hU2
  -- facts about `U`
  have hU0 : 0 < U := by linarith
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
  have hNu : (N U : ℝ) ≤ u ^ 8 := by
    have hUa : U ≤ a ^ ((6 : ℝ) / 5) := by
      calc U = (U ^ ((5 : ℝ) / 6)) ^ ((6 : ℝ) / 5) := by
            rw [← Real.rpow_mul hU0.le]
            norm_num
        _ ≤ a ^ ((6 : ℝ) / 5) := Real.rpow_le_rpow (by positivity) haU (by norm_num)
    calc (N U : ℝ) ≤ U ^ ((1 : ℝ) / 15) := hNle
      _ ≤ (a ^ ((6 : ℝ) / 5)) ^ ((1 : ℝ) / 15) := Real.rpow_le_rpow hU0.le hUa (by norm_num)
      _ = u ^ 8 := by
          rw [hudef, ← Real.rpow_mul ha0.le, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
          norm_num
  have hu5 : U ^ ((1 : ℝ) / 160) ≤ u ^ 5 := by
    calc U ^ ((1 : ℝ) / 160) = (U ^ ((1 : ℝ) / 8)) ^ ((1 : ℝ) / 100 * 5) := by
          rw [← Real.rpow_mul hU0.le]
          norm_num
      _ ≤ a ^ ((1 : ℝ) / 100 * 5) := Real.rpow_le_rpow (by positivity) haU8 (by norm_num)
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
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21) := by
      intro h hh k hk
      have hbd := norm_pairError_le_param hd hd8 hu2 hp hav hq2 hNu hh hk hCA0 hCA hC₁ hC₂ hsplit
        hK₁0 hK₂0 hK₁ hK₂
      have h1 : ‖b h‖ * ‖b k‖ ≤ 1 := by
        calc ‖b h‖ * ‖b k‖ ≤ 1 * 1 :=
              mul_le_mul (hbn h hh) (hbn k hk) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      calc ‖b h‖ * ‖b k‖
            * ‖pairError d (u ^ 100) a v (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
          ≤ 1 * ((v - a + 2 * u ^ 95)
            * ((pairStar CA C₁ C₂ K₁ + 2 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d)) / u ^ 21)) :=
            mul_le_mul h1 hbd (norm_nonneg _) zero_le_one
        _ ≤ (v - a + 2 * u ^ 95)
            * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21) := by
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
    have hN16 : ((N U : ℝ)) * (N U : ℝ) ≤ u ^ 16 := by
      calc ((N U : ℝ)) * (N U : ℝ) ≤ u ^ 8 * u ^ 8 :=
            mul_le_mul hNu hNu (Nat.cast_nonneg _) (by positivity)
        _ = u ^ 16 := by ring
    have hK0 : 0 ≤ pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R) := by positivity
    have hfin : (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5 ≤ ε / 2 := by
      have h1 : (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5
          ≤ (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) * U ^ (-((1 : ℝ) / 160)) := by
        rw [div_eq_mul_inv, Real.rpow_neg hU0.le]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hu5) hK0
      exact h1.trans hUerr
    calc (N U : ℝ) * ((N U : ℝ) * ((v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21)))
        = ((N U : ℝ) * (N U : ℝ)) * ((v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21)) := by ring
      _ ≤ u ^ 16 * ((v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21)) :=
          mul_le_mul_of_nonneg_right hN16 (mul_nonneg hlen (div_nonneg hK0 (by positivity)))
      _ = (v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5) := by
          have e : u ^ 16 * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21)
              = (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5 := by
            rw [mul_div_assoc', div_eq_div_iff (pow_ne_zero _ hu0.ne') (pow_ne_zero _ hu0.ne')]
            ring
          rw [← e]
          ring
      _ ≤ (v - a + 2 * u ^ 95) * (ε / 2) := mul_le_mul_of_nonneg_left hfin hlen
  -- Step E: combine
  have hη' : (c + ε) * (2 * u ^ 95) ≤ ε * a := by
    have h1 : 4 * (c + ε) / ε * U ^ (-((1 : ℝ) / 160)) ≤ 1 := hUη
    have h2 : 4 * (c + ε) / ε ≤ U ^ ((1 : ℝ) / 160) := by
      rw [Real.rpow_neg hU0.le] at h1
      have hUp : 0 < U ^ ((1 : ℝ) / 160) := by positivity
      rwa [mul_inv_le_iff₀ hUp, one_mul] at h1
    have h3 : 4 * (c + ε) ≤ ε * u ^ 5 := by
      have := (div_le_iff₀ hε).mp (h2.trans hu5)
      linarith only [this]
    have h4' : (c + ε) * (2 * u ^ 95) ≤ (ε / 2) * (u ^ 95 * u ^ 5) := by
      have h5 := mul_le_mul_of_nonneg_right h3 (pow_pos hu0 95).le
      linarith only [h5]
    have hεa : 0 ≤ ε * a := mul_nonneg hε.le ha0.le
    calc (c + ε) * (2 * u ^ 95) ≤ (ε / 2) * (u ^ 95 * u ^ 5) := h4'
      _ = (ε / 2) * a := by rw [← hu100]; ring
      _ ≤ ε * a := by linarith only [hεa]
  calc (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
          * edPoly b (Finset.Icc 1 (N U)) (displacedLinePt d τ)‖ ^ 2)
      ≤ ∫ t, blockWindow a v (u ^ 95) t * ‖riemannZeta (displacedLinePt d t)
          * edPoly b (Finset.Icc 1 (N U)) (displacedLinePt d t)‖ ^ 2 := hA
    _ ≤ _ := hB
    _ ≤ (v - a + 2 * u ^ 95) * (c + ε / 2) + (v - a + 2 * u ^ 95) * (ε / 2) :=
        add_le_add hmain herr
    _ = (c + ε) * (v - a) + (c + ε) * (2 * u ^ 95) := by ring
    _ ≤ (c + ε) * (v - a) + ε * a := by linarith only [hη']

/-- **The dyadic mean-square law from a high-block bound**, for real coefficients `w_U` with
`w_U(1) = 1`, `|w_U| ≤ 1` and length `1 ≤ N(U) ≤ U^{1/15}`. -/
theorem zetaDyadicMeanSquareLaw_of_highBlock {R c : ℝ} (hR : 0 < R) (hc : 0 ≤ c)
    (N : ℝ → ℕ) (w : ℝ → ℕ → ℝ)
    (hN : ∀ᶠ U in atTop, 1 ≤ N U ∧ (N U : ℝ) ≤ U ^ ((1 : ℝ) / 15))
    (hw1 : ∀ U, w U 1 = 1) (hw : ∀ U, ∀ n ∈ Finset.Icc 1 (N U), |w U n| ≤ 1)
    (hblock : ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop,
      ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U → d * Real.log (U - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → U ^ ((5 : ℝ) / 6) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
            * edPoly (fun n => ((w U n : ℝ) : ℂ)) (Finset.Icc 1 (N U)) (displacedLinePt d τ)‖ ^ 2)
          ≤ (c + ε) * (v - a) + ε * a) :
    ZetaDyadicMeanSquareLaw R c := by
  obtain ⟨C, hC, hconv⟩ := exists_norm_riemannZeta_le_convexity (η := 1 / 100) (by norm_num)
    (by norm_num)
  obtain ⟨K, hK0, hzeta⟩ := exists_zetaBlock_meanSquare_le hR
  intro ε hε
  filter_upwards [hblock ε hε, hzeta, hN, Filter.eventually_ge_atTop (Real.exp 2),
    Filter.eventually_ge_atTop (Real.exp (100 * R) + 1),
    Filter.eventually_ge_atTop ((2 : ℝ) ^ 100),
    eventually_const_mul_rpow_neg_mul_log_pow_le (8 * C ^ 2) ((8 : ℝ) / 75)
      (by norm_num) 1 hε,
    eventually_const_mul_rpow_neg_mul_log_pow_le K ((1 : ℝ) / 30) (by norm_num) 2 hε]
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
    have h1 : U ^ ((1 : ℝ) / 15) ≤ U ^ ((1 : ℝ) / 2) :=
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
  have hva0 : 0 ≤ (c + ε) * (v - a) :=
    mul_nonneg (by positivity) (by linarith only [hav])
  have hUlog : ε * (U / Real.log U) ≤ ε * (a + U / Real.log U) := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    linarith only [ha]
  rcases le_or_gt (U ^ ((5 : ℝ) / 6)) a with hhigh | hnhigh
  · have h := hblockU (1 / 2 - σ₀) hd hd8 hR1 hR2 a v ha hhigh hav hv2 hvU
    have : ε * a ≤ ε * (a + U / Real.log U) := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      have : 0 ≤ U / Real.log U := by positivity
      linarith only [this]
    linarith only [h, this]
  rcases le_or_gt (U ^ ((1 : ℝ) / 2)) a with hmid | hlow'
  · -- the middle blocks by the mean square of `ζ`
    have hU8a : U ^ ((1 : ℝ) / 8) ≤ a :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)) hmid
    have hz := hzetaU (1 / 2 - σ₀) hd hd8 hR1 hdU a v hU8a hav hv2 hvU
    have hm := integral_normSq_zeta_mul_edPoly_le_sq_mul hd (by linarith only [hd100]) hav
      (b := b) (N := N U) hbn
    have hNsq : (N U : ℝ) ^ 2 ≤ U ^ ((2 : ℝ) / 15) := by
      calc (N U : ℝ) ^ 2 ≤ (U ^ ((1 : ℝ) / 15)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hNle 2
        _ = U ^ ((2 : ℝ) / 15) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
            norm_num
    have hKa : K * Real.log U * a ≤ K * Real.log U * U ^ ((5 : ℝ) / 6) :=
      mul_le_mul_of_nonneg_left hnhigh.le (by positivity)
    have hint0 : 0 ≤ ∫ τ in a..v, ‖riemannZeta (displacedLinePt (1 / 2 - σ₀) τ)‖ ^ 2 :=
      intervalIntegral.integral_nonneg hav fun τ _ => by positivity
    have hstep : (N U : ℝ) ^ 2
          * ∫ τ in a..v, ‖riemannZeta (displacedLinePt (1 / 2 - σ₀) τ)‖ ^ 2
        ≤ U ^ ((2 : ℝ) / 15) * (K * Real.log U * U ^ ((5 : ℝ) / 6)) :=
      mul_le_mul hNsq (hz.trans hKa) hint0 (by positivity)
    have hsplit : U ^ ((2 : ℝ) / 15) * (K * Real.log U * U ^ ((5 : ℝ) / 6))
        = (K * (U ^ (-((1 : ℝ) / 30)) * Real.log U ^ 2)) * (U / Real.log U) := by
      have e : U ^ ((2 : ℝ) / 15) * U ^ ((5 : ℝ) / 6) = U ^ (-((1 : ℝ) / 30)) * U := by
        rw [← Real.rpow_add hU0, show (2 : ℝ) / 15 + 5 / 6 = -((1 : ℝ) / 30) + 1 by norm_num,
          Real.rpow_add hU0, Real.rpow_one]
      have e2 : U ^ ((2 : ℝ) / 15) * (K * Real.log U * U ^ ((5 : ℝ) / 6))
          = K * Real.log U * (U ^ ((2 : ℝ) / 15) * U ^ ((5 : ℝ) / 6)) := by ring
      have hlogU0 : 0 < Real.log U := by linarith only [hlogU]
      rw [e2, e]
      field_simp
    have hmain : (K * (U ^ (-((1 : ℝ) / 30)) * Real.log U ^ 2)) * (U / Real.log U)
        ≤ ε * (U / Real.log U) := mul_le_mul_of_nonneg_right hmidε (by positivity)
    rw [hsplit] at hstep
    linarith only [hm, hstep, hmain, hUlog, hva0]
  · -- the low blocks by convexity
    have hcx := integral_normSq_zeta_mul_edPoly_convexity hC.le hconv hd hd100
      (by linarith only [ha]) hav (b := b) (N := N U) hbn
    have hv : v ≤ 2 * U ^ ((1 : ℝ) / 2) := by linarith only [hv2, hlow']
    have hpw := lowBlock_power_le hC.le hU1 (by linarith only [ha]) hav hv hNle
    have hsplit : 8 * C ^ 2 * U ^ ((67 : ℝ) / 75) =
        (8 * C ^ 2 * (U ^ (-((8 : ℝ) / 75)) * Real.log U ^ 1)) * (U / Real.log U) := by
      rw [pow_one]
      have e : U ^ ((67 : ℝ) / 75) = U ^ (-((8 : ℝ) / 75)) * U := by
        rw [show ((67 : ℝ) / 75) = -((8 : ℝ) / 75) + 1 by norm_num, Real.rpow_add hU0,
          Real.rpow_one]
      have hlogU0 : 0 < Real.log U := by linarith only [hlogU]
      rw [e]
      field_simp
    have hmain : 8 * C ^ 2 * U ^ ((67 : ℝ) / 75) ≤ ε * (a + U / Real.log U) := by
      rw [hsplit]
      exact (mul_le_mul_of_nonneg_right hlow (by positivity)).trans hUlog
    linarith only [hcx, hpw, hmain, hva0]

end RHTower.ZetaGateProductAFE

end
