import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheCompleteUpperProductTail
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PeriodicQuotientCancellation
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PiecewiseSmoothnessOfTheDyadicSpline

/-!
# The fifteen-sixteenths product window on square conductors

On any subquadratic product range detached from both spline support edges,
eighth-order periodic quotient cancellation bounds each product `q = pv` on
conductor `n` by `O(q⁷ / n¹⁵)`. Summing against `log p` upgrades the single-conductor
upper-product tail error from `U² (1 + log U) / n³` to `U⁸ (1 + log U) / n¹⁵`,
paying every product up to `⌊n^(15/8)⌋ = (n²)^(15/16)` within six logarithms.
-/

noncomputable section
open Finset ArithmeticFunction
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Coprime complementary factors in the product shell `V < pv ≤ W` with cap `v ≤ M`. -/
def shellFactors (M V W p : ℕ) : Finset ℕ :=
  (Ioc (V / p) (min (W / p) M)).filter (p.Coprime ·)

private theorem cappedSlice_sub_cappedSlice {k p V W : ℕ} (hVW : V ≤ W) (hWk : W ≤ k) (M : ℕ) :
    cappedCoprimeSlice 1 1 k V M p - cappedCoprimeSlice 1 1 k W M p =
      ∑ v ∈ shellFactors M V W p, innerJump 1 v * centeredPrimeWeight 1 (k / (p * v)) := by
  let S := (Ioc (V / p) (min (k / p) M)).filter (p.Coprime ·)
  let a (v : ℕ) := innerJump 1 v * centeredPrimeWeight 1 (k / (p * v))
  have hv : V / p ≤ W / p := Nat.div_le_div_right hVW
  have hk : W / p ≤ k / p := Nat.div_le_div_right hWk
  have lo : S.filter (fun v => v ≤ W / p) = shellFactors M V W p := by
    ext v; simp only [S, shellFactors, mem_filter, mem_Ioc, le_min_iff]
    exact ⟨fun h => ⟨⟨h.1.1.1, h.2, h.1.1.2.2⟩, h.1.2⟩,
      fun h => ⟨⟨⟨h.1.1, h.1.2.1.trans hk, h.1.2.2⟩, h.2⟩, h.1.2.1⟩⟩
  have hi : S.filter (fun v => ¬ v ≤ W / p) = (Ioc (W / p) (min (k / p) M)).filter (p.Coprime ·) := by
    ext v; simp only [S, mem_filter, mem_Ioc, not_le]
    exact ⟨fun h => ⟨⟨h.2, h.1.1.2⟩, h.1.2⟩, fun h => ⟨⟨⟨hv.trans_lt h.1.1, h.1.2⟩, h.2⟩, h.1.1⟩⟩
  have hs := sum_filter_add_sum_filter_not S (fun v => v ≤ W / p) a
  rw [lo, hi] at hs
  simp only [cappedCoprimeSlice, Nat.div_div_eq_div_mul]
  change (∑ v ∈ S, a v) - (∑ v ∈ _, a v) = ∑ v ∈ shellFactors M V W p, a v
  linarith only [hs]

/-- Exact horizon-prime exchange for any detached shell `V < pv ≤ W` and cofactor cap `M`. -/
theorem capped_shell_exchange {n V W : ℕ} (hn : 0 < n) (hVW : V ≤ W)
    (hbirth : (W : ℝ) + 1 < Real.exp (-8) * (n : ℝ) ^ 2)
    (hY : productLower 1 (splineHorizon n) ≤ V) (M : ℕ) :
    cappedUpperProductReading V M n - cappedUpperProductReading W M n =
      ordinaryFactorTail 4 W fun p =>
        ∑ v ∈ shellFactors M V W p, innerJump 1 v * unitHorizonPair n (p * v) := by
  let L := splineHorizon n
  let z (k : ℕ) := sampledSpline n k - sampledSpline n (k + 1)
  let slice (k p : ℕ) := ∑ v ∈ shellFactors M V W p,
    innerJump 1 v * centeredPrimeWeight 1 (k / (p * v))
  let row (k : ℕ) := ordinaryFactorTail 4 W (slice k)
  have hz (k : ℕ) (hk : k ≤ W) : z k = 0 := by
    have hh : (k : ℝ) ≤ W := by exact_mod_cast hk
    have hn1 : ((k + 1 : ℕ) : ℝ) < Real.exp (-8) * (n : ℝ) ^ 2 := by
      push_cast; linarith only [hbirth, hh]
    simp only [z, sampledSpline_eq_zero_before hn (by linarith only [hbirth, hh] : (k : ℝ) < _),
      sampledSpline_eq_zero_before hn hn1, sub_self]
  have ha : cappedUpperProductReading V M n - cappedUpperProductReading W M n =
      ∑ k ∈ Icc 1 L, z k * row k := by
    unfold cappedUpperProductReading splineCountReading
    rw [← sum_sub_distrib]
    apply sum_congr rfl; intro k hk
    rw [← sub_mul]
    change _ * z k = z k * row k
    by_cases h : k ≤ W
    · rw [hz k h, mul_zero, zero_mul]
    · rw [mul_comm (z k)]
      congr 1
      have hL := (mem_Icc.mp hk).2
      have hy : productLower 1 k ≤ V := (min_le_min hL (Nat.mul_le_mul_left _
        (Nat.floor_mono (Real.sqrt_le_sqrt (by exact_mod_cast hL))))).trans hY
      have ht : W ≤ k := by omega
      have hpad := unit_prime_padding ht (slice k) fun p hp => by
        have hh : min (W / p) M = 0 := by rw [Nat.div_eq_of_lt hp, zero_min]
        simp only [slice, shellFactors, hh, Ioc_eq_empty_of_le (Nat.zero_le _),
          filter_empty, sum_empty]
      dsimp only [row]
      rw [hpad]
      simp only [max_eq_right hy, max_eq_right (hy.trans hVW), ordinaryFactorTail, ← sum_sub_distrib]
      exact sum_congr rfl fun p _ => by rw [← mul_sub, cappedSlice_sub_cappedSlice hVW ht M]
  have hb : (∑ k ∈ Icc 1 L, z k * row k) = ∑ k ∈ range (L + 1), z k * row k := by
    apply sum_subset
    · intro k hk; exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hk).2)
    · intro k hk hx
      have he : k = 0 := by
        have hle := mem_range.mp hk
        by_contra! hnz
        exact hx (mem_Icc.mpr ⟨Nat.pos_of_ne_zero hnz, by omega⟩)
      subst k; rw [hz 0 (Nat.zero_le _), zero_mul]
  rw [ha, hb]
  simp only [row, ordinaryFactorTail, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro p _
  simp only [mul_left_comm (z _) (vonMangoldt p), ← mul_sum]
  congr 1
  simp only [slice, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro v _
  simp only [unitHorizonPair, z, L, mul_sum]
  exact sum_congr rfl fun k _ => by ring

/-- Setting the cofactor cap at the spline horizon recovers the uncapped upper reading. -/
theorem upperProductReading_eq_capped (U n : ℕ) :
    upperProductReading U n = cappedUpperProductReading U (splineHorizon n) n := by
  unfold upperProductReading cappedUpperProductReading splineCountReading coprimePrimeRow
    ordinaryFactorTail
  apply sum_congr rfl; intro k hk
  congr 1
  apply sum_congr rfl; intro p _
  congr 1
  unfold coprimeSlice cappedCoprimeSlice
  have hkL : k / p ≤ splineHorizon n := (Nat.div_le_self k p).trans (mem_Icc.mp hk).2
  rw [min_eq_left hkL]

private theorem fwdDiff_iter_div_const (k : ℕ) (f : ℝ → ℝ) (c h u : ℝ) :
    (fwdDiff h)^[k] (fun x => f x / c) u = ((fwdDiff h)^[k] f u) / c := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    dsimp only [fwdDiff]
    rw [ih (u + h), ih u, sub_div]

/-- Eighth-order single-product cancellation: each detached product `q` with
`7q < exp(-8) n²` costs at most `O(q⁷ / n¹⁵)`. -/
theorem unitHorizonPair_eighth_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {n q : ℕ}, 0 < n → 0 < q →
      7 * (q : ℝ) < Real.exp (-8) * (n : ℝ) ^ 2 →
      |unitHorizonPair n q| ≤ K * (q : ℝ) ^ 7 / (n : ℝ) ^ 15 := by
  obtain ⟨C6, hC6, hper⟩ := centeredPrimeWeight_periodic_iter 6
  obtain ⟨K8, hK8, hsum8⟩ := sum_fwdDiff_eight_dyadicSpline_le
  refine ⟨C6 * K8, mul_nonneg hC6 hK8, fun {n q} hn hq hbirth => ?_⟩
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  let L := splineHorizon n
  let b := L / q + 2
  have hb_gt : L < q * b := by
    have hdiv := Nat.div_add_mod L q
    have hmod := Nat.mod_lt L hq
    dsimp [b]; nlinarith
  rw [unitHorizonPair_eq_quotient_blocks hn hq hb_gt]
  let h := (q : ℝ) / (n : ℝ) ^ 2
  have hh : 0 < h := div_pos hq' (sq_pos_of_pos hn')
  have hh_lt : 7 * h < Real.exp (-8) := by
    dsimp [h]; rw [mul_div_assoc', div_lt_iff₀ (sq_pos_of_pos hn')]; exact hbirth
  have hh1 : h ≤ 1 := by
    have hexp : Real.exp (-8) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  let g := fun u : ℝ => dyadicSpline u / (n : ℝ)
  let x := fun j : ℕ => sampledSpline n (q * j) - sampledSpline n (q * (j + 1))
  have hx_eq : x = fun j : ℕ => g ((j : ℝ) * h) - g (((j + 1 : ℕ) : ℝ) * h) := by
    funext j
    dsimp [x, g, h, sampledSpline]
    have e1 : ((q * j : ℕ) : ℝ) / (n : ℝ) ^ 2 = (j : ℝ) * ((q : ℝ) / (n : ℝ) ^ 2) := by
      push_cast; ring
    have e2 : ((q * (j + 1) : ℕ) : ℝ) / (n : ℝ) ^ 2 =
        ((j + 1 : ℕ) : ℝ) * ((q : ℝ) / (n : ℝ) ^ 2) := by
      push_cast; ring
    rw [e1, e2]
  have hx0 : ∀ j < 6 + 1, x j = 0 := by
    intro j hj
    have hj1 : ((q * j : ℕ) : ℝ) < Real.exp (-8) * (n : ℝ) ^ 2 := by
      have : (j : ℝ) ≤ 7 := by exact_mod_cast hj.le
      push_cast; nlinarith [hq'.le]
    have hj2 : ((q * (j + 1) : ℕ) : ℝ) < Real.exp (-8) * (n : ℝ) ^ 2 := by
      have : ((j + 1 : ℕ) : ℝ) ≤ 7 := by exact_mod_cast hj
      push_cast at this ⊢; nlinarith [hq'.le]
    simp only [x, sampledSpline_eq_zero_before hn hj1, sampledSpline_eq_zero_before hn hj2, sub_self]
  have hxb : ∀ j, b ≤ j → x j = 0 := by
    intro j hj
    have hgt1 : L < q * j := hb_gt.trans_le (Nat.mul_le_mul_left q hj)
    have hgt2 : L < q * (j + 1) := hgt1.trans (Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self j) hq)
    simp only [x, sampledSpline_eq_zero_after hn hgt1, sampledSpline_eq_zero_after hn hgt2, sub_self]
  have hp := hper x b hx0 hxb
  refine hp.trans ?_
  have hdiff_eq : (∑ j ∈ range b, |GaloisForLFunctions.BezoutValuationIncidence.bdiff^[7] x j|) =
      (∑ j ∈ range b, |(fwdDiff h)^[8] dyadicSpline ((j : ℝ) * h)|) / (n : ℝ) := by
    rw [sum_div]
    refine sum_congr rfl fun j _ => ?_
    rw [hx_eq, abs_bdiff_iter_step_eq 7 g h j]
    dsimp only [g]
    rw [fwdDiff_iter_div_const 8 dyadicSpline (n : ℝ) h ((j : ℝ) * h), abs_div, abs_of_pos hn']
  change C6 * (∑ j ∈ range b, |GaloisForLFunctions.BezoutValuationIncidence.bdiff^[7] x j|) ≤ _
  rw [hdiff_eq]
  calc C6 * ((∑ j ∈ range b, |(fwdDiff h)^[8] dyadicSpline ((j : ℝ) * h)|) / (n : ℝ))
      ≤ C6 * ((K8 * h ^ 7) / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hsum8 hh hh1 b) hn'.le) hC6
    _ = C6 * K8 * (q : ℝ) ^ 7 / (n : ℝ) ^ 15 := by
        dsimp only [h]; rw [div_pow, mul_div_right_comm K8, div_div]; ring

/-- Uniform eighth-order bound for any detached shell `V < pv ≤ W`, uniformly in the
complementary-factor cap `M`. -/
theorem capped_interior_shell_eighth_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n V W : ℕ}, 0 < n → 1 ≤ W → V ≤ W →
      7 * (W : ℝ) < Real.exp (-8) * (n : ℝ) ^ 2 →
      productLower 1 (splineHorizon n) ≤ V → ∀ M : ℕ,
      |cappedUpperProductReading V M n - cappedUpperProductReading W M n| ≤
        C * (W : ℝ) ^ 8 * (1 + Real.log W) / (n : ℝ) ^ 15 := by
  obtain ⟨K, hK, hpair⟩ := unitHorizonPair_eighth_bound
  let G := 2 * (1 + mass (1 + 1))
  have hG : 0 ≤ G := (abs_nonneg _).trans (innerJump_pointwise_bound 1 0)
  let E := Real.log 4 + 4
  have hE : 0 ≤ E := by dsimp [E]; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity
  refine ⟨G * K * E, by positivity, fun {n V W} hn hW hVW hbirth hY M => ?_⟩
  have hW' : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hbirth1 : (W : ℝ) + 1 < Real.exp (-8) * (n : ℝ) ^ 2 := by linarith
  rw [capped_shell_exchange hn hVW hbirth1 hY M]
  suffices hrow : ∀ p ∈ (Ioc 4 W).filter Nat.Prime,
      |∑ v ∈ shellFactors M V W p, innerJump 1 v * unitHorizonPair n (p * v)| ≤
        (G * K * (W : ℝ) ^ 8 / (n : ℝ) ^ 15) / p by
    exact (ordinaryFactorTail_reciprocal hW (by positivity : 0 ≤ G * K * (W : ℝ) ^ 8 / (n : ℝ) ^ 15)
      hrow).trans_eq (by dsimp [E]; ring)
  intro p hp
  have hp0 := (mem_filter.mp hp).2.pos
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp0
  have hh (v : ℕ) (hmem : v ∈ shellFactors M V W p) :
      |innerJump 1 v * unitHorizonPair n (p * v)| ≤ G * (K * (W : ℝ) ^ 7 / (n : ℝ) ^ 15) := by
    obtain ⟨hl, hhi⟩ := mem_Ioc.mp (mem_filter.mp hmem).1
    have hprod : p * v ≤ W := by
      simpa only [Nat.mul_comm v p] using (Nat.le_div_iff_mul_le hp0).mp (hhi.trans (min_le_left _ _))
    have hprod' : ((p * v : ℕ) : ℝ) ≤ W := by exact_mod_cast hprod
    have hq_pos : 0 < p * v := Nat.mul_pos hp0 ((Nat.zero_le _).trans_lt hl)
    have hqb : 7 * ((p * v : ℕ) : ℝ) < Real.exp (-8) * (n : ℝ) ^ 2 := by linarith
    rw [abs_mul]
    refine mul_le_mul (innerJump_pointwise_bound 1 v) ((hpair hn hq_pos hqb).trans ?_)
      (abs_nonneg _) hG
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hprod' 7) hK)
      (by positivity)
  have hcard : (shellFactors M V W p).card ≤ W / p := by
    refine (card_le_card (filter_subset _ _)).trans ?_
    rw [Nat.card_Ioc]
    exact (Nat.sub_le _ _).trans (min_le_left _ _)
  have hc : ((shellFactors M V W p).card : ℝ) * p ≤ W := by
    exact_mod_cast (Nat.mul_le_mul_right p hcard).trans (Nat.div_mul_le_self W p)
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hh).trans ?_)
  rw [sum_const, nsmul_eq_mul, le_div_iff₀ hp']
  have he := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ G * (K * (W : ℝ) ^ 7 / (n : ℝ) ^ 15))
  linarith only [he]

/-- Upgraded full-range upper-product tail bound with eighth-order smoothing `(1 + log U) U⁸ / n¹⁵`. -/
theorem dyadicPrimeContact_upper_eighth_product_tail :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ {n U : ℕ}, 0 < n → 1 ≤ U →
      |dyadicPrimeContact n - upperProductReading U n| ≤
        A * (1 + Real.log (splineHorizon n)) ^ 6 +
          B * (1 + Real.log U) * (U : ℝ) ^ 8 / (n : ℝ) ^ 15 := by
  obtain ⟨A0, B0, hA0, hB0, hlow⟩ := dyadicPrimeContact_upper_product_tail
  obtain ⟨C8, hC8, hshell⟩ := capped_interior_shell_eighth_bound
  obtain ⟨T, hT, hwin⟩ := successorSquare_window_bound
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  let A := A0 + 4 * B0 * T ^ 2
  let B := max C8 (B0 * (7 * Real.exp 8) ^ 6)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := le_trans hC8 (le_max_left _ _)
  refine ⟨A, B, hA, hB, fun {n U} hn hU => ?_⟩
  let L := splineHorizon n
  let H := 1 + Real.log L
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hH1 : 1 ≤ H := le_add_of_nonneg_right (Real.log_natCast_nonneg L)
  have hH0 : 0 ≤ H := zero_le_one.trans hH1
  have hroot : Real.sqrt L ≤ T * n := by
    have hs := Real.sqrt_le_sqrt (hwin hn)
    rwa [Real.sqrt_sq (mul_nonneg hT0 hn'.le)] at hs
  let U0 := max 1 (productLower 1 L)
  have hU0_pos : 1 ≤ U0 := le_max_left _ _
  have hU0_le_L : U0 ≤ L := by
    have hL1 : 1 ≤ L := by
      obtain ⟨h1, _, h2⟩ := successorSquareWindowScale_bounds n
      have hw : 1 ≤ windowEnd ((2 * n + 1) ^ 2 + 1) := by
        have : (1 : ℝ) ≤ windowEnd ((2 * n + 1) ^ 2 + 1) :=
          (by norm_num : (1 : ℝ) ≤ (n : ℝ) ^ 2 + 0 |> fun _ => by positivity) |> fun _ =>
            (show (1 : ℝ) ≤ (n : ℝ) ^ 2 by nlinarith).trans (h1.trans h2)
        exact_mod_cast this
      exact hw.trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 3))
    exact max_le hL1 (min_le_left L _)
  have hU0_bound : (U0 : ℝ) ≤ 2 * T * n := by
    rcases max_choice 1 (productLower 1 L) with h1 | h2
    · rw [h1]; push_cast; nlinarith [hT, hn1]
    · rw [h2]
      have hp : (productLower 1 L : ℝ) ≤ 2 * Real.sqrt L := by
        refine (Nat.cast_le.mpr (min_le_right _ _)).trans ?_
        push_cast
        exact mul_le_mul_of_nonneg_left (Nat.floor_le (Real.sqrt_nonneg _)) (by norm_num)
      exact hp.trans (by linarith [hroot])
  have hbase_le : ∀ {V : ℕ}, 1 ≤ V → V ≤ U0 →
      |dyadicPrimeContact n - upperProductReading V n| ≤ A * H ^ 6 := by
    intro V hV hVU0
    have hVL : V ≤ L := hVU0.trans hU0_le_L
    have hlogV : 1 + Real.log V ≤ H := add_le_add le_rfl
      (Real.log_le_log (by exact_mod_cast hV) (by exact_mod_cast hVL))
    have hV_real : (V : ℝ) ≤ 2 * T * n := (Nat.cast_le.mpr hVU0).trans hU0_bound
    have hVsq : (V : ℝ) ^ 2 ≤ 4 * T ^ 2 * (n : ℝ) ^ 3 := by
      calc (V : ℝ) ^ 2 ≤ (2 * T * n) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg V) hV_real 2
        _ = 4 * T ^ 2 * (n : ℝ) ^ 2 := by ring
        _ ≤ 4 * T ^ 2 * (n : ℝ) ^ 3 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 (by decide : 2 ≤ 3)) (by positivity)
    have hdiv : B0 * (1 + Real.log V) * (V : ℝ) ^ 2 / (n : ℝ) ^ 3 ≤ 4 * B0 * T ^ 2 * H ^ 6 := by
      rw [div_le_iff₀ (pow_pos hn' 3)]
      have hH6 : H ≤ H ^ 6 := le_self_pow₀ hH1 (by decide : 6 ≠ 0)
      have h1 : B0 * (1 + Real.log V) ≤ B0 * H ^ 6 :=
        mul_le_mul_of_nonneg_left (hlogV.trans hH6) hB0
      calc B0 * (1 + Real.log V) * (V : ℝ) ^ 2
          ≤ (B0 * H ^ 6) * (4 * T ^ 2 * (n : ℝ) ^ 3) :=
            mul_le_mul h1 hVsq (sq_nonneg _) (by positivity)
        _ = 4 * B0 * T ^ 2 * H ^ 6 * (n : ℝ) ^ 3 := by ring
    exact (hlow hn hV).trans ((add_le_add le_rfl hdiv).trans_eq (by dsimp [A]; ring))
  by_cases hle : U ≤ U0
  · refine (hbase_le hU hle).trans ?_
    have hpos : 0 ≤ B * (1 + Real.log U) * (U : ℝ) ^ 8 / (n : ℝ) ^ 15 := by
      have := Real.log_natCast_nonneg U; positivity
    linarith
  · push_neg at hle
    by_cases hbirth : 7 * (U : ℝ) < Real.exp (-8) * (n : ℝ) ^ 2
    · have h1 := hbase_le hU0_pos le_rfl
      have h2 : |upperProductReading U0 n - upperProductReading U n| ≤
          B * (1 + Real.log U) * (U : ℝ) ^ 8 / (n : ℝ) ^ 15 := by
        rw [upperProductReading_eq_capped U0 n, upperProductReading_eq_capped U n]
        refine (hshell hn hU hle.le hbirth (le_max_right _ _) L).trans ?_
        have := Real.log_natCast_nonneg U
        have hCB : C8 ≤ B := le_max_left _ _
        calc C8 * (U : ℝ) ^ 8 * (1 + Real.log U) / (n : ℝ) ^ 15
            = C8 * ((1 + Real.log U) * (U : ℝ) ^ 8 / (n : ℝ) ^ 15) := by ring
          _ ≤ B * ((1 + Real.log U) * (U : ℝ) ^ 8 / (n : ℝ) ^ 15) :=
              mul_le_mul_of_nonneg_right hCB (by positivity)
          _ = B * (1 + Real.log U) * (U : ℝ) ^ 8 / (n : ℝ) ^ 15 := by ring
      have hid : dyadicPrimeContact n - upperProductReading U n =
          (dyadicPrimeContact n - upperProductReading U0 n) +
            (upperProductReading U0 n - upperProductReading U n) := by ring
      rw [hid]
      exact (abs_add_le _ _).trans (add_le_add h1 h2)
    · push_neg at hbirth
      refine (hlow hn hU).trans ?_
      have hA_le : A0 * H ^ 6 ≤ A * H ^ 6 :=
        mul_le_mul_of_nonneg_right (by dsimp [A]; positivity) (pow_nonneg hH0 6)
      have hratio : (n : ℝ) ^ 2 ≤ 7 * Real.exp 8 * U := by
        have := mul_le_mul_of_nonneg_left hbirth (Real.exp_pos 8).le
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at this
        linarith
      have hpow6 : (n : ℝ) ^ 12 ≤ (7 * Real.exp 8) ^ 6 * (U : ℝ) ^ 6 := by
        calc (n : ℝ) ^ 12 = ((n : ℝ) ^ 2) ^ 6 := by ring
          _ ≤ (7 * Real.exp 8 * U) ^ 6 := pow_le_pow_left₀ (sq_nonneg _) hratio 6
          _ = (7 * Real.exp 8) ^ 6 * (U : ℝ) ^ 6 := by ring
      have hB_le : B0 * (1 + Real.log U) * (U : ℝ) ^ 2 / (n : ℝ) ^ 3 ≤
          B * (1 + Real.log U) * (U : ℝ) ^ 8 / (n : ℝ) ^ 15 := by
        rw [div_le_div_iff₀ (pow_pos hn' 3) (pow_pos hn' 15)]
        have hlogU : 0 ≤ 1 + Real.log U := by have := Real.log_natCast_nonneg U; positivity
        have hBB : B0 * (7 * Real.exp 8) ^ 6 ≤ B := le_max_right _ _
        calc B0 * (1 + Real.log U) * (U : ℝ) ^ 2 * (n : ℝ) ^ 15
            = B0 * (1 + Real.log U) * (U : ℝ) ^ 2 * (n : ℝ) ^ 3 * (n : ℝ) ^ 12 := by ring
          _ ≤ B0 * (1 + Real.log U) * (U : ℝ) ^ 2 * (n : ℝ) ^ 3 *
                ((7 * Real.exp 8) ^ 6 * (U : ℝ) ^ 6) :=
              mul_le_mul_of_nonneg_left hpow6 (by positivity)
          _ = (B0 * (7 * Real.exp 8) ^ 6) * ((1 + Real.log U) * (U : ℝ) ^ 8 * (n : ℝ) ^ 3) := by ring
          _ ≤ B * ((1 + Real.log U) * (U : ℝ) ^ 8 * (n : ℝ) ^ 3) :=
              mul_le_mul_of_nonneg_right hBB (by positivity)
          _ = B * (1 + Real.log U) * (U : ℝ) ^ 8 * (n : ℝ) ^ 3 := by ring
      exact add_le_add hA_le hB_le

/-- Complete eighth-order two-cutoff approximation with product cutoff `U` and cofactor cap `M`. -/
theorem dyadicPrimeContact_capped_eighth_product_tail :
    ∃ A B C : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧ ∀ {n U : ℕ}, 0 < n → 1 ≤ U → ∀ M : ℕ,
      |dyadicPrimeContact n - cappedUpperProductReading U M n| ≤
        A * (1 + Real.log (splineHorizon n)) ^ 6 +
          B * (1 + Real.log U) * (U : ℝ) ^ 8 / (n : ℝ) ^ 15 +
          C * n * (1 + Real.log (splineHorizon n)) / (M + 1 : ℕ) := by
  obtain ⟨A, B, hA, hB, hupper⟩ := dyadicPrimeContact_upper_eighth_product_tail
  obtain ⟨K, hK, hlarge⟩ := large_complement_bound
  obtain ⟨J, _, hJ, _, hdiff⟩ := sampledSpline_differences
  obtain ⟨T, hT, hwin⟩ := successorSquare_window_bound
  refine ⟨A, B, 2 * K * J * T ^ 4, hA, hB, by positivity, fun {n U} hn hU M => ?_⟩
  let L := splineHorizon n
  let H := 1 + Real.log L
  let head (k : ℕ) := coprimePrimeRow 1 1 k (max (productLower 1 k) U)
  let cap (k : ℕ) := ordinaryFactorTail 4 k (cappedCoprimeSlice 1 1 k (max (productLower 1 k) U) M)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hm : (0 : ℝ) < (M + 1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos M)
  have hbound : (L : ℝ) ≤ (T * n) ^ 2 := hwin hn
  have hrow (k : ℕ) (hk : k ∈ Icc 1 L) :
      |head k - cap k| ≤ (2 * K) * ((T * n) ^ 2 / (M + 1 : ℕ)) * H := by
    obtain ⟨hk1, hkL⟩ := mem_Icc.mp hk
    have h := hlarge (D := 1) (R := 1) (F := 4) le_rfl le_rfl hk1 (by decide)
      (max (productLower 1 k) U) M
    change |head k - cap k| ≤ _ at h
    have hdiv : ((k / (M + 1) : ℕ) : ℝ) ≤ (T * n) ^ 2 / (M + 1 : ℕ) :=
      (Nat.cast_div_le ..).trans (div_le_div_of_nonneg_right
        ((by exact_mod_cast hkL : (k : ℝ) ≤ L).trans hbound) hm.le)
    have hlog := Real.log_le_log (by exact_mod_cast hk1 : (0 : ℝ) < k)
      (by exact_mod_cast hkL : (k : ℝ) ≤ L)
    refine h.trans ?_
    have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ 2 * K))
      (add_le_add le_rfl hlog) (by have := Real.log_natCast_nonneg k; positivity) (by positivity)
    calc _ = (2 * K) * ((k / (M + 1) : ℕ) : ℝ) * (1 + Real.log k) := by norm_num; ring
      _ ≤ _ := hprod
  have hdiff' : |upperProductReading U n - cappedUpperProductReading U M n| ≤
      (2 * K * J * T ^ 4) * n * H / (M + 1 : ℕ) := by
    change |(∑ k ∈ Icc 1 L, head k * (sampledSpline n k - sampledSpline n (k + 1))) -
      (∑ k ∈ Icc 1 L, cap k * (sampledSpline n k - sampledSpline n (k + 1)))| ≤ _
    rw [← sum_sub_distrib]
    simp_rw [← sub_mul]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _k ∈ Icc 1 L, ((2 * K) * ((T * n) ^ 2 / (M + 1 : ℕ)) * H) * (J / (n : ℝ) ^ 3) := by
            apply sum_le_sum; intro k hk
            rw [abs_mul]
            exact mul_le_mul (hrow k hk) (hdiff hn k).1 (abs_nonneg _) (by positivity)
      _ ≤ (T * n) ^ 2 * (((2 * K) * ((T * n) ^ 2 / (M + 1 : ℕ)) * H) * (J / (n : ℝ) ^ 3)) := by
            rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
            exact mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = _ := by field_simp; ring
  have he : dyadicPrimeContact n - cappedUpperProductReading U M n =
      (dyadicPrimeContact n - upperProductReading U n) +
        (upperProductReading U n - cappedUpperProductReading U M n) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (hupper hn hU) hdiff')

#print axioms capped_shell_exchange
#print axioms unitHorizonPair_eighth_bound
#print axioms capped_interior_shell_eighth_bound
#print axioms dyadicPrimeContact_upper_eighth_product_tail
#print axioms dyadicPrimeContact_capped_eighth_product_tail
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
