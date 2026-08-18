import GaloisForLFunctions.RHTower.Sieve.LinearMeanSquareGeneric

/-!
# The linear mean-square chain for coefficients of bounded size

`LinearMeanSquareGeneric` runs the chain for unit coefficients.  The Ramaré/Turán–Kubilius route
needs it for the `ω`-weighted Möbius coefficients, whose size is the number of designated primes
dividing the index — polylogarithmic, not one.  Carrying that size `C` through the chain replaces
the trivial excess cost `(εL+1)²` by `C²(εL+1)²`; nothing else changes.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Finset

/-- The per-block cost, for coefficients of size at most `C`. -/
def blockCostGC (L ε C G : ℝ) : ℝ := 2 * G + 2 * C ^ 2 * (ε * L + 1) ^ 2 * Real.log (1 + ε)

theorem blockCostGC_nonneg {L ε C G : ℝ} (hε : 0 ≤ ε) (hG : 0 ≤ G) :
    0 ≤ blockCostGC L ε C G := by
  have hlog : 0 ≤ Real.log (1 + ε) := Real.log_nonneg (by linarith)
  rw [blockCostGC]
  have : (0 : ℝ) ≤ 2 * C ^ 2 * (ε * L + 1) ^ 2 * Real.log (1 + ε) := by positivity
  linarith

/-- A sum of bounded coefficients is at most the size times the cardinality. -/
theorem norm_sum_le_card_bound (a : ℕ → ℂ) {C : ℝ} (ha : ∀ n : ℕ, ‖a n‖ ≤ C) (T : Finset ℕ) :
    ‖∑ n ∈ T, a n‖ ≤ C * (T.card : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ C fun n _ => ha n) ?_
  rw [nsmul_eq_mul]
  ring_nf
  exact le_rfl

/-- **The transfer, with the excess bounded by the size times the count.** -/
theorem normSq_linear_le_multiplicative_card_bound (a : ℕ → ℂ) (s : Finset ℕ) {C : ℝ}
    (hC0 : 0 ≤ C) (ha : ∀ n : ℕ, ‖a n‖ ≤ C) {x L y : ℝ} (hL : 0 ≤ L) (h : x + L ≤ y) :
    ‖∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + L), a n‖ ^ 2
      ≤ 2 * ‖∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ y), a n‖ ^ 2
        + 2 * C ^ 2 * ((s.filter (fun n : ℕ => x + L < (n : ℝ) ∧ (n : ℝ) ≤ y)).card : ℝ) ^ 2 := by
  classical
  refine le_trans (normSq_linear_le_multiplicative a s hL h) ?_
  have hcard := norm_sum_le_card_bound a ha (s.filter (fun n : ℕ => x + L < (n : ℝ) ∧ (n : ℝ) ≤ y))
  have h0 : (0 : ℝ) ≤ ‖∑ n ∈ s.filter (fun n : ℕ => x + L < (n : ℝ) ∧ (n : ℝ) ≤ y), a n‖ :=
    norm_nonneg _
  have hcard0 : (0 : ℝ) ≤ C * ((s.filter (fun n : ℕ => x + L < (n : ℝ) ∧ (n : ℝ) ≤ y)).card : ℝ) :=
    mul_nonneg hC0 (Nat.cast_nonneg _)
  nlinarith [hcard, h0, hcard0]

/-- **The transfer with the excess measured by its length, for coefficients of size `C`.** -/
theorem normSq_linear_le_multiplicative_length_bound (a : ℕ → ℂ) (s : Finset ℕ) {C : ℝ}
    (hC0 : 0 ≤ C) (ha : ∀ n : ℕ, ‖a n‖ ≤ C) {x L y : ℝ} (hx : 0 ≤ x) (hL : 0 ≤ L)
    (h : x + L ≤ y) :
    ‖∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + L), a n‖ ^ 2
      ≤ 2 * ‖∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ y), a n‖ ^ 2
        + 2 * C ^ 2 * (y - (x + L) + 1) ^ 2 := by
  classical
  refine le_trans (normSq_linear_le_multiplicative_card_bound a s hC0 ha hL h) ?_
  have hcard := card_window_le s (c := x + L) (y := y) (by linarith) h
  have h0 : (0 : ℝ) ≤ ((s.filter (fun n : ℕ => x + L < (n : ℝ) ∧ (n : ℝ) ≤ y)).card : ℝ) :=
    Nat.cast_nonneg _
  have hsq : ((s.filter (fun n : ℕ => x + L < (n : ℝ) ∧ (n : ℝ) ≤ y)).card : ℝ) ^ 2
      ≤ (y - (x + L) + 1) ^ 2 := by nlinarith [hcard, h0]
  nlinarith [hsq, sq_nonneg C]

/-- **The pointwise linear-to-logarithmic comparison, for coefficients of size `C`.** -/
theorem normSq_linWindowSum_le_logWindowSum_bound (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n) {C : ℝ} (hC0 : 0 ≤ C) (ha : ∀ n : ℕ, ‖a n‖ ≤ C)
    {L Y ε u : ℝ} (hL : 0 ≤ L) (hY : 0 < Y) (hε : 0 ≤ ε)
    (hu₁ : Real.log Y < u) (hu₂ : u ≤ Real.log (Y * (1 + ε))) :
    ‖linWindowSum a s L u‖ ^ 2
      ≤ 2 * ‖logWindowSum a s (Real.log (1 + L / Y)) u‖ ^ 2
        + 2 * C ^ 2 * (ε * L + 1) ^ 2 := by
  classical
  set δ : ℝ := Real.log (1 + L / Y) with hδdef
  have hratio : (0 : ℝ) < 1 + L / Y := by positivity
  have hexpδ : Real.exp δ = 1 + L / Y := Real.exp_log hratio
  set x : ℝ := Real.exp u with hxdef
  have hx0 : (0 : ℝ) < x := Real.exp_pos u
  have hxY : Y < x := by
    rw [hxdef, ← Real.exp_log hY]
    exact Real.exp_lt_exp.2 hu₁
  have hxup : x ≤ Y * (1 + ε) := by
    have hpos : (0 : ℝ) < Y * (1 + ε) := by positivity
    rw [hxdef, ← Real.exp_log hpos]
    exact Real.exp_le_exp.2 hu₂
  have hy : x * Real.exp δ = x + x * L / Y := by
    rw [hexpδ]
    field_simp
  have hle : x + L ≤ x * Real.exp δ := by
    rw [hy]
    have : L ≤ x * L / Y := by
      rw [le_div_iff₀ hY]
      nlinarith [hxY.le, hL]
    linarith
  have hexcess : x * Real.exp δ - (x + L) ≤ ε * L := by
    rw [hy]
    have : x * L / Y ≤ (1 + ε) * L := by
      rw [div_le_iff₀ hY]
      nlinarith [hxup, hL]
    linarith
  have hlin := linWindowSum_eq a s L u
  have hlog : logWindowSum a s δ u
      = ∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x * Real.exp δ), a n := by
    have h := logWindowSum_log a s hs δ hx0
    rwa [hxdef, Real.log_exp] at h
  rw [hlin, hlog]
  refine le_trans
    (normSq_linear_le_multiplicative_length_bound a s hC0 ha hx0.le hL hle) ?_
  have hsq : (x * Real.exp δ - (x + L) + 1) ^ 2 ≤ (ε * L + 1) ^ 2 := by
    have h0 : (0 : ℝ) ≤ x * Real.exp δ - (x + L) + 1 := by linarith
    nlinarith [hexcess, h0]
  nlinarith [hsq, sq_nonneg C]

/-- **The block estimate, for coefficients of size `C`.** -/
theorem setIntegral_normSq_linWindowSum_block_le_bound (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n) {C : ℝ} (hC0 : 0 ≤ C) (ha : ∀ n : ℕ, ‖a n‖ ≤ C)
    {L Y ε G : ℝ} (hL : 0 < L) (hY : 0 < Y) (hε : 0 ≤ ε)
    (hG : (∫ u in Set.Ioc (Real.log Y) (Real.log (Y * (1 + ε))),
        ‖logWindowSum a s (Real.log (1 + L / Y)) u‖ ^ 2) ≤ G) :
    (∫ u in Set.Ioc (Real.log Y) (Real.log (Y * (1 + ε))), ‖linWindowSum a s L u‖ ^ 2)
      ≤ 2 * G + 2 * C ^ 2 * (ε * L + 1) ^ 2
          * volume.real (Set.Ioc (Real.log Y) (Real.log (Y * (1 + ε)))) := by
  classical
  set δ : ℝ := Real.log (1 + L / Y) with hδdef
  set E : Set ℝ := Set.Ioc (Real.log Y) (Real.log (Y * (1 + ε))) with hEdef
  have hEfin : volume E ≠ ⊤ := by
    rw [hEdef]
    simp
  have hLHS : IntegrableOn (fun u : ℝ => ‖linWindowSum a s L u‖ ^ 2) E :=
    integrableOn_normSq_linWindowSum a s L hEfin
  have hRHS : IntegrableOn
      (fun u : ℝ => 2 * ‖logWindowSum a s δ u‖ ^ 2 + 2 * C ^ 2 * (ε * L + 1) ^ 2) E := by
    refine Integrable.add ?_ (integrableOn_const hEfin (by finiteness))
    exact ((integrable_normSq_logWindowSum a s δ).const_mul 2).integrableOn
  have hstep : (∫ u in E, ‖linWindowSum a s L u‖ ^ 2)
      ≤ ∫ u in E, (2 * ‖logWindowSum a s δ u‖ ^ 2 + 2 * C ^ 2 * (ε * L + 1) ^ 2) := by
    refine setIntegral_mono_on hLHS hRHS measurableSet_Ioc fun u hu => ?_
    rw [hEdef, Set.mem_Ioc] at hu
    exact normSq_linWindowSum_le_logWindowSum_bound a s hs hC0 ha hL.le hY hε hu.1 hu.2
  refine le_trans hstep ?_
  rw [MeasureTheory.integral_add
    (((integrable_normSq_logWindowSum a s δ).const_mul 2).integrableOn)
    (integrableOn_const hEfin (by finiteness)), integral_const_mul, setIntegral_const, smul_eq_mul]
  have hvol : (0 : ℝ) ≤ volume.real E := measureReal_nonneg
  nlinarith [hG, hvol, sq_nonneg (ε * L + 1), sq_nonneg C]


/-- **The range estimate, for coefficients of size `C`.** -/
theorem setIntegral_normSq_linWindowSum_range_le_bound (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n) {C : ℝ} (hC0 : 0 ≤ C) (ha : ∀ n : ℕ, ‖a n‖ ≤ C)
    {L Y ε G : ℝ} (hL : 0 < L) (hY : 0 < Y) (hε : 0 ≤ ε) (_hG0 : 0 ≤ G)
    (hG : ∀ Y' : ℝ, Y ≤ Y' → ∀ E : Set ℝ,
      (∫ u in E, ‖logWindowSum a s (Real.log (1 + L / Y')) u‖ ^ 2) ≤ G) (K : ℕ) :
    (∫ u in Set.Ioc (Real.log Y) (Real.log (Y * (1 + ε) ^ K)),
        ‖linWindowSum a s L u‖ ^ 2)
      ≤ (K : ℝ) * blockCostGC L ε C G := by
  classical
  have hone : (0 : ℝ) < 1 + ε := by linarith
  induction K with
  | zero => simp
  | succ K ih =>
      set Z : ℝ := Y * (1 + ε) ^ K with hZ
      have hZ0 : 0 < Z := by rw [hZ]; positivity
      have hZY : Y ≤ Z := by
        rw [hZ]
        nlinarith [one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + ε) (n := K), hY.le]
      have hnext : Y * (1 + ε) ^ (K + 1) = Z * (1 + ε) := by rw [hZ]; ring
      have hlogle : Real.log Y ≤ Real.log Z := Real.log_le_log hY hZY
      have hlogle2 : Real.log Z ≤ Real.log (Z * (1 + ε)) := by
        refine Real.log_le_log hZ0 ?_
        nlinarith [hZ0.le, hε]
      have hunion : Set.Ioc (Real.log Y) (Real.log Z) ∪
          Set.Ioc (Real.log Z) (Real.log (Z * (1 + ε)))
          = Set.Ioc (Real.log Y) (Real.log (Z * (1 + ε))) :=
        Set.Ioc_union_Ioc_eq_Ioc hlogle hlogle2
      have hdisj : Disjoint (Set.Ioc (Real.log Y) (Real.log Z))
          (Set.Ioc (Real.log Z) (Real.log (Z * (1 + ε)))) := by
        rw [Set.disjoint_left]
        intro x hx hx'
        exact absurd hx.2 (not_le.2 hx'.1)
      have hfin₁ : volume (Set.Ioc (Real.log Y) (Real.log Z)) ≠ ⊤ := by simp
      have hfin₂ : volume (Set.Ioc (Real.log Z) (Real.log (Z * (1 + ε)))) ≠ ⊤ := by simp
      have hsplit : (∫ u in Set.Ioc (Real.log Y) (Real.log (Z * (1 + ε))),
            ‖linWindowSum a s L u‖ ^ 2)
          = (∫ u in Set.Ioc (Real.log Y) (Real.log Z), ‖linWindowSum a s L u‖ ^ 2)
            + ∫ u in Set.Ioc (Real.log Z) (Real.log (Z * (1 + ε))),
                ‖linWindowSum a s L u‖ ^ 2 := by
        rw [← hunion]
        exact setIntegral_union hdisj measurableSet_Ioc
          (integrableOn_normSq_linWindowSum a s L hfin₁)
          (integrableOn_normSq_linWindowSum a s L hfin₂)
      have hblock := setIntegral_normSq_linWindowSum_block_le_bound a s hs hC0 ha
        (L := L) (Y := Z) (ε := ε) (G := G) hL hZ0 hε (hG Z hZY _)
      have hvol : volume.real (Set.Ioc (Real.log Z) (Real.log (Z * (1 + ε))))
          = Real.log (1 + ε) := by
        rw [measureReal_def, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith), Real.log_mul (ne_of_gt hZ0) (ne_of_gt hone)]
        ring
      rw [hvol] at hblock
      rw [hnext, hsplit]
      have hcost : (2 * G + 2 * C ^ 2 * (ε * L + 1) ^ 2 * Real.log (1 + ε))
          = blockCostGC L ε C G := by
        rw [blockCostGC]
      rw [hcost] at hblock
      have hIH := ih
      push_cast
      linarith [hIH, hblock]

/-- **The linear short-interval mean square over a range, for coefficients of size `C`.** -/
theorem integral_Ioc_normSq_linSum_range_le_bound (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n) {C : ℝ} (hC0 : 0 ≤ C) (ha : ∀ n : ℕ, ‖a n‖ ≤ C)
    {L Y ε G : ℝ} (hL : 0 < L) (hY : 0 < Y) (hε : 0 ≤ ε) (hG0 : 0 ≤ G)
    (hG : ∀ Y' : ℝ, Y ≤ Y' → ∀ E : Set ℝ,
      (∫ u in E, ‖logWindowSum a s (Real.log (1 + L / Y')) u‖ ^ 2) ≤ G) (K : ℕ) :
    (∫ x in Set.Ioc Y (Y * (1 + ε) ^ K), ‖linSum a s L x‖ ^ 2)
      ≤ (Y * (1 + ε) ^ K) * ((K : ℝ) * blockCostGC L ε C G) := by
  have hZ0 : (0 : ℝ) < Y * (1 + ε) ^ K := by positivity
  have hYexp : Real.exp (Real.log Y) = Y := Real.exp_log hY
  have hZexp : Real.exp (Real.log (Y * (1 + ε) ^ K)) = Y * (1 + ε) ^ K := Real.exp_log hZ0
  have hstep := integral_Ioc_normSq_linSum_le a s L (Real.log Y) (Real.log (Y * (1 + ε) ^ K))
  rw [hYexp, hZexp] at hstep
  refine le_trans hstep ?_
  have hrange := setIntegral_normSq_linWindowSum_range_le_bound a s hs hC0 ha hL hY hε hG0 hG K
  exact mul_le_mul_of_nonneg_left hrange hZ0.le

/-- **The discrete short-interval mean square, for coefficients of size `C`.** -/
theorem sum_normSq_window_le_bound (c : ℕ → ℂ) {C : ℝ} (hC0 : 0 ≤ C) (hc : ∀ n : ℕ, ‖c n‖ ≤ C)
    {L Y K M K' : ℕ} {ε G : ℝ}
    (hL : 0 < L) (hY : 0 < Y) (hε : 0 ≤ ε) (hG0 : 0 ≤ G)
    (hM : Y + K + L < M + 1)
    (hcover : (Y : ℝ) + (K : ℝ) ≤ (Y : ℝ) * (1 + ε) ^ K')
    (hG : ∀ Y' : ℝ, (Y : ℝ) ≤ Y' → ∀ E : Set ℝ,
      (∫ u in E, ‖logWindowSum c (Finset.Icc 1 M) (Real.log (1 + (L : ℝ) / Y')) u‖ ^ 2) ≤ G) :
    ∑ k ∈ Finset.range K, ‖∑ n ∈ Finset.Ioc (Y + k) (Y + k + L), c n‖ ^ 2
      ≤ ((Y : ℝ) * (1 + ε) ^ K') * ((K' : ℝ) * blockCostGC (L : ℝ) ε C G) := by
  classical
  have hY0 : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  set s : Finset ℕ := Finset.Icc 1 M with hs
  have hspos : ∀ n ∈ s, 0 < n := by
    intro n hn
    rw [hs, Finset.mem_Icc] at hn
    omega
  have hdisc := integral_realWindow_eq_sum c L Y K (M + 1) hM
  have hcongr : (∫ x in (Y : ℝ)..((Y : ℝ) + (K : ℝ)), ‖∑ n ∈ realWindow x L (M + 1), c n‖ ^ 2)
      = ∫ x in (Y : ℝ)..((Y : ℝ) + (K : ℝ)), ‖linSum c s (L : ℝ) x‖ ^ 2 := by
    refine intervalIntegral.integral_congr_uIoo ?_
    intro x hx
    rw [Set.uIoo_of_le (by
      have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      linarith), Set.mem_Ioo] at hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_of_lt_of_le hY0 hx.1.le)
    show ‖∑ n ∈ realWindow x L (M + 1), c n‖ ^ 2 = ‖linSum c s (L : ℝ) x‖ ^ 2
    rw [sum_realWindow_eq_linSum c hx0 L M]
  have hnonneg : ∀ x : ℝ, (0 : ℝ) ≤ ‖linSum c s (L : ℝ) x‖ ^ 2 := fun x => by positivity
  have hsub : Set.Ioc (Y : ℝ) ((Y : ℝ) + (K : ℝ))
      ⊆ Set.Ioc (Y : ℝ) ((Y : ℝ) * (1 + ε) ^ K') :=
    Set.Ioc_subset_Ioc_right hcover
  have hbig : IntegrableOn (fun x : ℝ => ‖linSum c s (L : ℝ) x‖ ^ 2)
      (Set.Ioc (Y : ℝ) ((Y : ℝ) * (1 + ε) ^ K')) :=
    integrableOn_normSq_linSum c s (L : ℝ) measure_Ioc_lt_top.ne
  have hmono : (∫ x in Set.Ioc (Y : ℝ) ((Y : ℝ) + (K : ℝ)), ‖linSum c s (L : ℝ) x‖ ^ 2)
      ≤ ∫ x in Set.Ioc (Y : ℝ) ((Y : ℝ) * (1 + ε) ^ K'), ‖linSum c s (L : ℝ) x‖ ^ 2 := by
    refine setIntegral_mono_set hbig ?_ (LE.le.eventuallyLE hsub)
    exact Filter.Eventually.of_forall hnonneg
  have hIval : (∫ x in (Y : ℝ)..((Y : ℝ) + (K : ℝ)), ‖linSum c s (L : ℝ) x‖ ^ 2)
      = ∫ x in Set.Ioc (Y : ℝ) ((Y : ℝ) + (K : ℝ)), ‖linSum c s (L : ℝ) x‖ ^ 2 :=
    intervalIntegral.integral_of_le (by
      have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      linarith)
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hfinal := integral_Ioc_normSq_linSum_range_le_bound c s hspos hC0 hc hLR hY0 hε hG0 hG K'
  rw [← hdisc, hcongr, hIval]
  exact le_trans hmono hfinal

/-- **The dyadic mean square, for coefficients of size `C`.** -/
theorem dyadicMeanSquare_le_bound (f : ℕ → ℝ) {C : ℝ} (hC0 : 0 ≤ C) (hf : ∀ n, |f n| ≤ C)
    {ℓ A B M K' : ℕ} {ε G : ℝ}
    (hℓ : 0 < ℓ) (hA : 0 < A) (hAB : A ≤ B + 1) (hε : 0 ≤ ε) (hG0 : 0 ≤ G)
    (hM : B + 1 + ℓ < M + 1)
    (hcover : (A : ℝ) + ((B + 1 - A : ℕ) : ℝ) ≤ (A : ℝ) * (1 + ε) ^ K')
    (hG : ∀ Y' : ℝ, (A : ℝ) ≤ Y' → ∀ E : Set ℝ,
      (∫ u in E, ‖logWindowSum (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M)
        (Real.log (1 + (ℓ : ℝ) / Y')) u‖ ^ 2) ≤ G) :
    dyadicMeanSquare f ℓ A B
      ≤ ((A : ℝ) * (1 + ε) ^ K') * ((K' : ℝ) * blockCostGC (ℓ : ℝ) ε C G) := by
  classical
  set c : ℕ → ℂ := fun n => ((f n : ℝ) : ℂ) with hc
  have hcnorm : ∀ n : ℕ, ‖c n‖ ≤ C := by
    intro n
    rw [hc, Complex.norm_real, Real.norm_eq_abs]
    exact hf n
  have hreindex : dyadicMeanSquare f ℓ A B
      = ∑ k ∈ Finset.range (B + 1 - A), ‖∑ n ∈ Finset.Ioc (A + k) (A + k + ℓ), c n‖ ^ 2 := by
    rw [dyadicMeanSquare, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fixedWindowSq_eq_normSq f hℓ (A + k)]
  rw [hreindex]
  have hMle : A + (B + 1 - A) + ℓ < M + 1 := by omega
  exact sum_normSq_window_le_bound c hC0 hcnorm hℓ hA hε hG0 hMle hcover hG

end RHTower.Sieve

end
