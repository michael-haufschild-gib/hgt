import GaloisForLFunctions.RHTower.Sieve.DyadicMeanSquareGallagher
import GaloisForLFunctions.RHTower.Sieve.GallagherSplitIntegral

/-!
# The linear mean-square chain, over an abstract Gallagher budget

`LinearBlockEstimate` … `DyadicMeanSquareGallagher` are built on the *pointwise* Gallagher split,
which needs a bound `M₁` on `‖logPoly a s w‖²` for every `|w| ≤ W`.  That is the zero-free-region
interface, and it caps at long windows.  The large-values interface supplies instead a bound on the
frequency **mean square** `∫_{|w| ≤ W} ‖logPoly a s w‖²`, through
`setIntegral_normSq_logWindowSum_le_integral`.

Both are consumed at exactly one place: a bound on `∫_E ‖logWindowSum a s δ u‖²` at
`δ = log(1 + L/Y')`.  Carrying that bound as a parameter `G` runs the whole chain once, and
`dyadicMeanSquare_le_largeValues` instantiates it at the mean-square split:

```text
dyadicMeanSquare f ℓ A B ≤ A(1+ε)^{K'} · K' · ( 2·(2 log(1+ℓ/A)²·I + M₂·2/(π²W))
                                                  + 2(εℓ+1)² log(1+ε) ) .
```

The `log(1+ℓ/A)²` in place of `M₁·log(1+ℓ/A)` is the whole gain: at `A ≍ √x` and `ℓ ≤ h` it is
`(ℓ/√x)²`, so the frequency mean square is multiplied by `ℓ²/x` rather than the pointwise size by
`ℓ/√x`.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Finset

/-- The per-block cost, over an abstract Gallagher budget. -/
def blockCostG (L ε G : ℝ) : ℝ := 2 * G + 2 * (ε * L + 1) ^ 2 * Real.log (1 + ε)

theorem blockCostG_nonneg {L ε G : ℝ} (hε : 0 ≤ ε) (hG : 0 ≤ G) : 0 ≤ blockCostG L ε G := by
  have hlog : 0 ≤ Real.log (1 + ε) := Real.log_nonneg (by linarith)
  rw [blockCostG]
  have : (0 : ℝ) ≤ 2 * (ε * L + 1) ^ 2 * Real.log (1 + ε) := by positivity
  linarith

/-- **The block estimate, over an abstract Gallagher budget.** -/
theorem setIntegral_normSq_linWindowSum_block_le_gen (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n) (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {L Y ε G : ℝ} (hL : 0 < L) (hY : 0 < Y) (hε : 0 ≤ ε)
    (hG : (∫ u in Set.Ioc (Real.log Y) (Real.log (Y * (1 + ε))),
        ‖logWindowSum a s (Real.log (1 + L / Y)) u‖ ^ 2) ≤ G) :
    (∫ u in Set.Ioc (Real.log Y) (Real.log (Y * (1 + ε))), ‖linWindowSum a s L u‖ ^ 2)
      ≤ 2 * G + 2 * (ε * L + 1) ^ 2
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
      (fun u : ℝ => 2 * ‖logWindowSum a s δ u‖ ^ 2 + 2 * (ε * L + 1) ^ 2) E := by
    refine Integrable.add ?_ (integrableOn_const hEfin (by finiteness))
    exact ((integrable_normSq_logWindowSum a s δ).const_mul 2).integrableOn
  have hstep : (∫ u in E, ‖linWindowSum a s L u‖ ^ 2)
      ≤ ∫ u in E, (2 * ‖logWindowSum a s δ u‖ ^ 2 + 2 * (ε * L + 1) ^ 2) := by
    refine setIntegral_mono_on hLHS hRHS measurableSet_Ioc fun u hu => ?_
    rw [hEdef, Set.mem_Ioc] at hu
    exact normSq_linWindowSum_le_logWindowSum a s hs ha hL.le hY hε hu.1 hu.2
  refine le_trans hstep ?_
  rw [MeasureTheory.integral_add
    (((integrable_normSq_logWindowSum a s δ).const_mul 2).integrableOn)
    (integrableOn_const hEfin (by finiteness)), integral_const_mul, setIntegral_const, smul_eq_mul]
  have hvol : (0 : ℝ) ≤ volume.real E := measureReal_nonneg
  nlinarith [hG, hvol, sq_nonneg (ε * L + 1)]

/-- **The range estimate, over an abstract Gallagher budget.** -/
theorem setIntegral_normSq_linWindowSum_range_le_gen (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n) (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {L Y ε G : ℝ} (hL : 0 < L) (hY : 0 < Y) (hε : 0 ≤ ε) (_hG0 : 0 ≤ G)
    (hG : ∀ Y' : ℝ, Y ≤ Y' → ∀ E : Set ℝ,
      (∫ u in E, ‖logWindowSum a s (Real.log (1 + L / Y')) u‖ ^ 2) ≤ G) (K : ℕ) :
    (∫ u in Set.Ioc (Real.log Y) (Real.log (Y * (1 + ε) ^ K)),
        ‖linWindowSum a s L u‖ ^ 2)
      ≤ (K : ℝ) * blockCostG L ε G := by
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
      have hblock := setIntegral_normSq_linWindowSum_block_le_gen a s hs ha (L := L) (Y := Z)
        (ε := ε) (G := G) hL hZ0 hε (hG Z hZY _)
      have hvol : volume.real (Set.Ioc (Real.log Z) (Real.log (Z * (1 + ε))))
          = Real.log (1 + ε) := by
        rw [measureReal_def, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith), Real.log_mul (ne_of_gt hZ0) (ne_of_gt hone)]
        ring
      rw [hvol] at hblock
      rw [hnext, hsplit]
      have hcost : (2 * G + 2 * (ε * L + 1) ^ 2 * Real.log (1 + ε)) = blockCostG L ε G := by
        rw [blockCostG]
      rw [hcost] at hblock
      have hIH := ih
      push_cast
      linarith [hIH, hblock]

/-- **The linear short-interval mean square over a range, over an abstract budget.** -/
theorem integral_Ioc_normSq_linSum_range_le_gen (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n) (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {L Y ε G : ℝ} (hL : 0 < L) (hY : 0 < Y) (hε : 0 ≤ ε) (hG0 : 0 ≤ G)
    (hG : ∀ Y' : ℝ, Y ≤ Y' → ∀ E : Set ℝ,
      (∫ u in E, ‖logWindowSum a s (Real.log (1 + L / Y')) u‖ ^ 2) ≤ G) (K : ℕ) :
    (∫ x in Set.Ioc Y (Y * (1 + ε) ^ K), ‖linSum a s L x‖ ^ 2)
      ≤ (Y * (1 + ε) ^ K) * ((K : ℝ) * blockCostG L ε G) := by
  have hone : (0 : ℝ) < 1 + ε := by linarith
  have hZ0 : (0 : ℝ) < Y * (1 + ε) ^ K := by positivity
  have hYexp : Real.exp (Real.log Y) = Y := Real.exp_log hY
  have hZexp : Real.exp (Real.log (Y * (1 + ε) ^ K)) = Y * (1 + ε) ^ K := Real.exp_log hZ0
  have hstep := integral_Ioc_normSq_linSum_le a s L (Real.log Y) (Real.log (Y * (1 + ε) ^ K))
  rw [hYexp, hZexp] at hstep
  refine le_trans hstep ?_
  have hrange := setIntegral_normSq_linWindowSum_range_le_gen a s hs ha hL hY hε hG0 hG K
  exact mul_le_mul_of_nonneg_left hrange hZ0.le

/-- **The discrete short-interval mean square, over an abstract budget.** -/
theorem sum_normSq_window_le_gen (c : ℕ → ℂ) (hc : ∀ n : ℕ, ‖c n‖ ≤ 1)
    {L Y K M K' : ℕ} {ε G : ℝ}
    (hL : 0 < L) (hY : 0 < Y) (hε : 0 ≤ ε) (hG0 : 0 ≤ G)
    (hM : Y + K + L < M + 1)
    (hcover : (Y : ℝ) + (K : ℝ) ≤ (Y : ℝ) * (1 + ε) ^ K')
    (hG : ∀ Y' : ℝ, (Y : ℝ) ≤ Y' → ∀ E : Set ℝ,
      (∫ u in E, ‖logWindowSum c (Finset.Icc 1 M) (Real.log (1 + (L : ℝ) / Y')) u‖ ^ 2) ≤ G) :
    ∑ k ∈ Finset.range K, ‖∑ n ∈ Finset.Ioc (Y + k) (Y + k + L), c n‖ ^ 2
      ≤ ((Y : ℝ) * (1 + ε) ^ K') * ((K' : ℝ) * blockCostG (L : ℝ) ε G) := by
  classical
  have hY0 : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
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
    rw [Set.uIoo_of_le (by linarith), Set.mem_Ioo] at hx
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
    intervalIntegral.integral_of_le (by linarith)
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hfinal := integral_Ioc_normSq_linSum_range_le_gen c s hspos hc hLR hY0 hε hG0 hG K'
  rw [← hdisc, hcongr, hIval]
  exact le_trans hmono hfinal

/-- **The dyadic mean square, over an abstract budget.** -/
theorem dyadicMeanSquare_le_gen (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {ℓ A B M K' : ℕ} {ε G : ℝ}
    (hℓ : 0 < ℓ) (hA : 0 < A) (hAB : A ≤ B + 1) (hε : 0 ≤ ε) (hG0 : 0 ≤ G)
    (hM : B + 1 + ℓ < M + 1)
    (hcover : (A : ℝ) + ((B + 1 - A : ℕ) : ℝ) ≤ (A : ℝ) * (1 + ε) ^ K')
    (hG : ∀ Y' : ℝ, (A : ℝ) ≤ Y' → ∀ E : Set ℝ,
      (∫ u in E, ‖logWindowSum (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M)
        (Real.log (1 + (ℓ : ℝ) / Y')) u‖ ^ 2) ≤ G) :
    dyadicMeanSquare f ℓ A B
      ≤ ((A : ℝ) * (1 + ε) ^ K') * ((K' : ℝ) * blockCostG (ℓ : ℝ) ε G) := by
  classical
  set c : ℕ → ℂ := fun n => ((f n : ℝ) : ℂ) with hc
  have hcnorm : ∀ n : ℕ, ‖c n‖ ≤ 1 := by
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
  exact sum_normSq_window_le_gen c hcnorm hℓ hA hε hG0 hMle hcover hG

/-- **The dyadic mean square, from a frequency mean square.**  This is the large-values interface:
no pointwise bound on `‖logPoly‖` is used, only its integral over `|w| ≤ W`. -/
theorem dyadicMeanSquare_le_largeValues (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {ℓ A B M K' : ℕ} {ε M₂ W I : ℝ}
    (hℓ : 0 < ℓ) (hA : 0 < A) (hAB : A ≤ B + 1) (hε : 0 ≤ ε) (hW : 0 < W) (hM₂ : 0 ≤ M₂)
    (hI0 : 0 ≤ I) (hM : B + 1 + ℓ < M + 1)
    (hcover : (A : ℝ) + ((B + 1 - A : ℕ) : ℝ) ≤ (A : ℝ) * (1 + ε) ^ K')
    (hI : (∫ w in Set.Icc (-W) W,
      ‖logPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2) ≤ I)
    (h₂ : ∀ w : ℝ, ‖logPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2 ≤ M₂) :
    dyadicMeanSquare f ℓ A B
      ≤ ((A : ℝ) * (1 + ε) ^ K')
          * ((K' : ℝ) * blockCostG (ℓ : ℝ) ε
              (2 * Real.log (1 + (ℓ : ℝ) / (A : ℝ)) ^ 2 * I
                + M₂ * (2 / (Real.pi ^ 2 * W)))) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  set G : ℝ := 2 * Real.log (1 + (ℓ : ℝ) / (A : ℝ)) ^ 2 * I
      + M₂ * (2 / (Real.pi ^ 2 * W)) with hGdef
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    have h1 : (0 : ℝ) ≤ 2 * Real.log (1 + (ℓ : ℝ) / (A : ℝ)) ^ 2 * I :=
      mul_nonneg (by positivity) hI0
    have h2 : (0 : ℝ) ≤ M₂ * (2 / (Real.pi ^ 2 * W)) := by positivity
    linarith
  refine dyadicMeanSquare_le_gen f hf hℓ hA hAB hε hG0 hM hcover ?_
  intro Y' hY' E
  have hY'0 : (0 : ℝ) < Y' := lt_of_lt_of_le hA0 hY'
  have hδ0 : 0 < Real.log (1 + (ℓ : ℝ) / Y') := by
    refine Real.log_pos ?_
    have : (0 : ℝ) < (ℓ : ℝ) / Y' := by positivity
    linarith
  have hbase := setIntegral_normSq_logWindowSum_le_integral
    (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M) hδ0 hW hM₂ hI h₂ E
  refine le_trans hbase ?_
  have hmono : Real.log (1 + (ℓ : ℝ) / Y') ≤ Real.log (1 + (ℓ : ℝ) / (A : ℝ)) := by
    refine Real.log_le_log (by positivity) ?_
    have : (ℓ : ℝ) / Y' ≤ (ℓ : ℝ) / (A : ℝ) := by
      exact div_le_div_of_nonneg_left hℓ0.le hA0 hY'
    linarith
  have hsq : Real.log (1 + (ℓ : ℝ) / Y') ^ 2 ≤ Real.log (1 + (ℓ : ℝ) / (A : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hδ0.le hmono 2
  rw [hGdef]
  nlinarith [hsq, hI0]

/-- **The range estimate with the Gallagher budget kept per block.**  `..._range_le_gen` pays one
whole budget `G` in every one of the `K` blocks, because each block carries its own window width
`log(1 + L/Y(1+ε)^k)` and Gallagher's identity is a whole-line identity.  Keeping the per-block
budgets separate makes that factor `K` visible and removable by anyone who can bound their *sum* —
for equal widths the blocks are disjoint and the sum telescopes into a single line integral. -/
theorem setIntegral_normSq_linWindowSum_range_le_sum (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n) (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {L Y ε : ℝ} (hL : 0 < L) (hY : 0 < Y) (hε : 0 ≤ ε) {g : ℕ → ℝ}
    (hg : ∀ k : ℕ,
      (∫ u in Set.Ioc (Real.log (Y * (1 + ε) ^ k)) (Real.log (Y * (1 + ε) ^ k * (1 + ε))),
        ‖logWindowSum a s (Real.log (1 + L / (Y * (1 + ε) ^ k))) u‖ ^ 2) ≤ g k) (K : ℕ) :
    (∫ u in Set.Ioc (Real.log Y) (Real.log (Y * (1 + ε) ^ K)),
        ‖linWindowSum a s L u‖ ^ 2)
      ≤ 2 * (∑ k ∈ Finset.range K, g k)
          + (K : ℝ) * (2 * (ε * L + 1) ^ 2 * Real.log (1 + ε)) := by
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
      have hblock := setIntegral_normSq_linWindowSum_block_le_gen a s hs ha (L := L) (Y := Z)
        (ε := ε) (G := g K) hL hZ0 hε (hg K)
      have hvol : volume.real (Set.Ioc (Real.log Z) (Real.log (Z * (1 + ε))))
          = Real.log (1 + ε) := by
        rw [measureReal_def, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith), Real.log_mul (ne_of_gt hZ0) (ne_of_gt hone)]
        ring
      rw [hvol] at hblock
      rw [hnext, hsplit, Finset.sum_range_succ]
      push_cast
      linarith [ih, hblock]

end RHTower.Sieve

end
