import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AsymmetricTwoRegionConductorReserve
import Zeta23.FromPNTPlus.Mertens

/-!
# The prime self-form of the overlapping top costs `c (1 + log c)`

Let `M = N / L_c` with `L_c = linearDefectCutoff c`, and let `y` live on the top `(M, N]`. Two top
atoms are paired by the prime lag `log k` only when their log-ratio is within `w = c/N` of
`log k`; then `k ≤ e^w N/(M+1) ≍ c`, and the integers `n` with `kn` within `R` of a point number at
most `2R/k + 1` (`card_mul_near_le`). A Schur test with the Perron weights `n^{−1/2}`, applied to
the full lag window (the ratio lag and the non-ratio lags together), bounds the prime form of the
top atomic test by `topPrimeRow w M N` per unit mass (`abs_primeSum_top_le`), and
`topPrimeRow (c/N) M N ≤ C c (1 + log c)` (`topPrimeRow_le`). The non-ratio top rows alone were
previously paid at `O(c²)`: a prime power `k > 2ec` meets a window of width `2ec` at most once.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset ArithmeticFunction RHTower

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

/-! ### Counting naturals in a window -/

theorem card_filter_mem_Icc_real_le (s : Finset ℕ) {A B : ℝ} (hAB : A ≤ B) :
    ((s.filter fun n : ℕ => A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B).card : ℝ) ≤ B - A + 1 := by
  rcases lt_or_ge B 0 with hB | hB
  · have hempty : (s.filter fun n : ℕ => A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B) = ∅ :=
      filter_eq_empty_iff.mpr fun n _ h => absurd (h.2.trans_lt hB) (not_lt.mpr n.cast_nonneg)
    rw [hempty, card_empty, Nat.cast_zero]; linarith
  have hsub : (s.filter fun n : ℕ => A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B) ⊆ Icc ⌈A⌉₊ ⌊B⌋₊ := fun n hn =>
    mem_Icc.mpr ⟨Nat.ceil_le.mpr (mem_filter.mp hn).2.1, Nat.le_floor (mem_filter.mp hn).2.2⟩
  have hcard : ((s.filter fun n : ℕ => A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B).card : ℝ) ≤
      ((⌊B⌋₊ + 1 - ⌈A⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans_eq (Nat.card_Icc _ _)
  have hceil : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
  have hfloor : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hB
  refine hcard.trans ?_
  rcases le_or_gt ⌈A⌉₊ (⌊B⌋₊ + 1) with h | h
  · rw [Nat.cast_sub h]; push_cast; linarith
  · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]; linarith

theorem card_mul_near_le (s : Finset ℕ) {k : ℕ} (hk : 1 ≤ k) (a : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ((s.filter fun n : ℕ => |(k : ℝ) * n - a| ≤ R).card : ℝ) ≤ 2 * R / k + 1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hAB : (a - R) / k ≤ (a + R) / k := div_le_div_of_nonneg_right (by linarith) hk0.le
  have hsub : (s.filter fun n : ℕ => |(k : ℝ) * n - a| ≤ R) ⊆
      s.filter fun n : ℕ => (a - R) / k ≤ (n : ℝ) ∧ (n : ℝ) ≤ (a + R) / k := by
    intro n hn
    obtain ⟨hs, h⟩ := mem_filter.mp hn
    obtain ⟨h1, h2⟩ := abs_le.mp h
    refine mem_filter.mpr ⟨hs, ?_, ?_⟩
    · rw [div_le_iff₀ hk0]; linarith
    · rw [le_div_iff₀ hk0]; linarith
  refine (Nat.cast_le.mpr (card_le_card hsub)).trans
    ((card_filter_mem_Icc_real_le s hAB).trans_eq ?_)
  field_simp
  ring

variable {g : ℝ → ℝ} {w : ℝ}

/-- The full lag window: `log(n/m)` within `w` of `log k`, the ratio `n = km` included. -/
def lagWin (w : ℝ) (k m n : ℕ) : ℝ :=
  if |Real.log k - (Real.log n - Real.log m)| ≤ w then 1 else 0

theorem lagWin_nonneg (w : ℝ) (k m n : ℕ) : 0 ≤ lagWin w k m n := by
  unfold lagWin; split_ifs <;> norm_num

private theorem abs_bumpCorr_le_win (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (t : ℝ) :
    |bumpCorr g t| ≤ (∫ u, g u ^ 2) * (if |t| ≤ w then 1 else 0) := by
  split_ifs with h
  · rw [mul_one]; exact abs_bumpCorr_le hg hgc t
  · rw [mul_zero, bumpCorr_eq_zero hgsupp (not_le.mp h), abs_zero]

/-- **A lag form by its full windows.** -/
theorem abs_lagForm_le_lagWin (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N k : ℕ) (x : ℕ → ℝ) :
    |lagForm g N k x| ≤ (∫ u, g u ^ 2) * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      |x m| * |x n| * (lagWin w k m n + lagWin w k n m) := by
  unfold lagForm
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => ?_)
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
  have hneg : bumpCorr g (-Real.log k - (Real.log n - Real.log m)) =
      bumpCorr g (Real.log k - (Real.log m - Real.log n)) := by
    rw [← bumpCorr_neg]; congr 1; ring
  rw [hneg, abs_mul, abs_mul]
  have h1 := abs_bumpCorr_le_win hg hgc hgsupp (Real.log k - (Real.log m - Real.log n))
  have h2 := abs_bumpCorr_le_win hg hgc hgsupp (Real.log k - (Real.log n - Real.log m))
  have hxx : 0 ≤ |x m| * |x n| := by positivity
  calc |x m| * |x n| * |bumpCorr g (Real.log k - (Real.log m - Real.log n)) +
        bumpCorr g (Real.log k - (Real.log n - Real.log m))|
      ≤ |x m| * |x n| * ((∫ u, g u ^ 2) * lagWin w k n m + (∫ u, g u ^ 2) * lagWin w k m n) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h1 h2)) hxx
    _ = (∫ u, g u ^ 2) * (|x m| * |x n| * (lagWin w k m n + lagWin w k n m)) := by ring

/-- Mertens' bound on an integer cutoff: `Σ_{k ≤ ⌊x⌋} Λ(k)/k ≤ log x + log 4 + 4` for `x ≥ 1`. -/
theorem sum_vonMangoldt_div_Icc_floor_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ k ∈ Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ) / k ≤ Real.log x + (Real.log 4 + 4) := by
  have h := (abs_le.mp (Mertens.sum_mangoldt_div_eq_log hx)).2
  have hIoc : Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  rw [hIoc] at h
  linarith

/-- **The up row of the full window.** Each order `k ≤ N e^w/m` meets at most `2km(e^w − 1) + 1`
indices `n` near `km`, each with weight `√(m/n) ≤ e^{w/2}/√k`. -/
theorem top_up_row_le (hw0 : 0 ≤ w) {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) (K : ℕ) :
    ∑ k ∈ range K, vonMangoldtAtom k *
        ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * lagWin w k m n ≤
      Real.exp (w / 2) * (2 * (Real.log 4 + 4) * Real.exp w * ((Real.exp w - 1) * N) +
        (Real.log ((N : ℝ) * Real.exp w / m) + (Real.log 4 + 4))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hm.trans hmN
  have hew : 0 ≤ Real.exp w - 1 := by linarith [Real.add_one_le_exp w]
  set k₁ := ⌊(N : ℝ) * Real.exp w / m⌋₊
  have hx1 : 1 ≤ (N : ℝ) * Real.exp w / m := by
    rw [le_div_iff₀ hm0, one_mul]
    exact (by exact_mod_cast hmN : (m : ℝ) ≤ N).trans (le_mul_of_one_le_right hN0.le
      (Real.one_le_exp hw0))
  have hk : ∀ k ∈ range K, vonMangoldtAtom k *
      ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * lagWin w k m n ≤
        if k ∈ Icc 1 k₁ then (ArithmeticFunction.vonMangoldt k : ℝ) *
          (Real.exp (w / 2) * (2 * m * (Real.exp w - 1) + 1 / k)) else 0 := by
    intro k _
    rcases lt_or_ge k 2 with hk2 | hk2
    · rw [vonMangoldtAtom_eq_zero_of_lt_two hk2, zero_mul]
      split_ifs
      · have hk1 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
      · exact le_rfl
    have hk1 : 1 ≤ k := by omega
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
    set R := ((k * m : ℕ) : ℝ) * (Real.exp w - 1)
    have hR : 0 ≤ R := by positivity
    have hinner : ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * lagWin w k m n ≤
        ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => |((1 : ℕ) : ℝ) * n - (k * m : ℕ)| ≤ R),
          Real.exp (w / 2) / Real.sqrt k := by
      rw [sum_filter]
      refine sum_le_sum fun n hn => ?_
      have hn1 := (mem_Icc.mp hn).1
      unfold lagWin
      split_ifs with h1 h2
      · rw [mul_one]; exact (upWin_bounds hk1 hm hn1 h1).1
      · exact absurd (by rw [Nat.cast_one, one_mul]; exact (upWin_bounds hk1 hm hn1 h1).2.1) h2
      · rw [mul_zero]; positivity
      · rw [mul_zero]
    rw [sum_const, nsmul_eq_mul] at hinner
    have hcard := card_mul_near_le (Icc 1 N) le_rfl ((k * m : ℕ) : ℝ) hR
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := k)
    by_cases hkK : k ∈ Icc 1 k₁
    · rw [if_pos hkK, vonMangoldtAtom_eq hk2]
      calc (ArithmeticFunction.vonMangoldt k : ℝ) / Real.sqrt k *
            ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * lagWin w k m n
          ≤ (ArithmeticFunction.vonMangoldt k : ℝ) / Real.sqrt k *
              ((2 * R / ((1 : ℕ) : ℝ) + 1) * (Real.exp (w / 2) / Real.sqrt k)) :=
            mul_le_mul_of_nonneg_left (hinner.trans
              (mul_le_mul_of_nonneg_right hcard (by positivity))) (by positivity)
        _ = (ArithmeticFunction.vonMangoldt k : ℝ) *
              (Real.exp (w / 2) * (2 * m * (Real.exp w - 1) + 1 / k)) := by
            have hkk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0.le
            dsimp only [R]
            push_cast
            field_simp
            rw [Real.sq_sqrt hk0.le]
    · rw [if_neg hkK]
      have hbig : (N : ℝ) * Real.exp w / m < k := by
        have : k₁ < k := by
          by_contra hle
          exact hkK (mem_Icc.mpr ⟨hk1, by omega⟩)
        exact Nat.lt_of_floor_lt this
      have hzero : ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * lagWin w k m n = 0 := by
        refine sum_eq_zero fun n hn => ?_
        obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
        unfold lagWin
        split_ifs with h1
        · exfalso
          have hle := (upWin_bounds hk1 hm hn1 h1).2.2
          have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
          rw [div_lt_iff₀ hm0] at hbig
          have he : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add]; simp
          nlinarith [Real.exp_pos w, Real.exp_pos (-w)]
        · rw [mul_zero]
      rw [hzero, mul_zero]
  refine (sum_le_sum hk).trans ?_
  rw [← sum_filter]
  have hsub : (range K).filter (fun k => k ∈ Icc 1 k₁) ⊆ Icc 1 k₁ := fun k hk => (mem_filter.mp hk).2
  have hnn : ∀ k ∈ Icc 1 k₁, 0 ≤ (ArithmeticFunction.vonMangoldt k : ℝ) *
      (Real.exp (w / 2) * (2 * m * (Real.exp w - 1) + 1 / k)) := fun k _ => by
    have := ArithmeticFunction.vonMangoldt_nonneg (n := k); positivity
  refine (sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => hnn k hk).trans ?_
  have hsplit : ∑ k ∈ Icc 1 k₁, (ArithmeticFunction.vonMangoldt k : ℝ) *
      (Real.exp (w / 2) * (2 * m * (Real.exp w - 1) + 1 / k)) =
      Real.exp (w / 2) * (2 * m * (Real.exp w - 1) * ∑ k ∈ Icc 1 k₁,
        (ArithmeticFunction.vonMangoldt k : ℝ) +
        ∑ k ∈ Icc 1 k₁, (ArithmeticFunction.vonMangoldt k : ℝ) / k) := by
    rw [mul_sum, ← sum_add_distrib, mul_sum]
    exact sum_congr rfl fun k _ => by ring
  rw [hsplit]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hcheb := sum_vonMangoldt_Icc_le k₁
  have hk₁ : (k₁ : ℝ) ≤ (N : ℝ) * Real.exp w / m := Nat.floor_le (by positivity)
  have hmert := sum_vonMangoldt_div_Icc_floor_le hx1
  have hA : 2 * m * (Real.exp w - 1) * ∑ k ∈ Icc 1 k₁, (ArithmeticFunction.vonMangoldt k : ℝ) ≤
      2 * (Real.log 4 + 4) * Real.exp w * ((Real.exp w - 1) * N) := by
    calc 2 * m * (Real.exp w - 1) * ∑ k ∈ Icc 1 k₁, (ArithmeticFunction.vonMangoldt k : ℝ)
        ≤ 2 * m * (Real.exp w - 1) * ((Real.log 4 + 4) * ((N : ℝ) * Real.exp w / m)) :=
          mul_le_mul_of_nonneg_left (hcheb.trans (mul_le_mul_of_nonneg_left hk₁ (by positivity)))
            (by positivity)
      _ = 2 * (Real.log 4 + 4) * Real.exp w * ((Real.exp w - 1) * N) := by
          field_simp
  linarith

/-- **The down row of the full window on the top.** For `m` and `n` both above `M`, the order
`k ≤ e^w N/(M+1)`, and the integers `n` with `kn` near `m` number at most `2m(e^w − 1)/k + 1`. -/
theorem top_down_row_le (hw0 : 0 ≤ w) {M m N : ℕ} (hMm : M < m) (hmN : m ≤ N) (K : ℕ) :
    ∑ k ∈ range K, vonMangoldtAtom k *
        ∑ n ∈ Ioc M N, Real.sqrt ((m : ℝ) / n) * lagWin w k n m ≤
      Real.exp (w / 2) * (2 * ((Real.exp w - 1) * N) *
          (Real.log (Real.exp w * N / (M + 1)) + (Real.log 4 + 4)) +
        (Real.log 4 + 4) * (Real.exp w * N / (M + 1))) := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hew : 0 ≤ Real.exp w - 1 := by linarith [Real.add_one_le_exp w]
  set X := Real.exp w * N / (M + 1)
  set k₂ := ⌊X⌋₊
  have hX1 : 1 ≤ X := by
    rw [le_div_iff₀ hM1, one_mul]
    have : (M : ℝ) + 1 ≤ N := by exact_mod_cast (show M + 1 ≤ N by omega)
    exact this.trans (le_mul_of_one_le_left (Nat.cast_nonneg N) (Real.one_le_exp hw0))
  have hk : ∀ k ∈ range K, vonMangoldtAtom k *
      ∑ n ∈ Ioc M N, Real.sqrt ((m : ℝ) / n) * lagWin w k n m ≤
        if k ∈ Icc 1 k₂ then (ArithmeticFunction.vonMangoldt k : ℝ) *
          (Real.exp (w / 2) * (2 * m * (Real.exp w - 1) / k + 1)) else 0 := by
    intro k _
    rcases lt_or_ge k 2 with hk2 | hk2
    · rw [vonMangoldtAtom_eq_zero_of_lt_two hk2, zero_mul]
      split_ifs
      · have hk1 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
      · exact le_rfl
    have hk1 : 1 ≤ k := by omega
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
    set R := (m : ℝ) * (Real.exp w - 1)
    have hR : 0 ≤ R := by positivity
    have hinner : ∑ n ∈ Ioc M N, Real.sqrt ((m : ℝ) / n) * lagWin w k n m ≤
        ∑ n ∈ (Ioc M N).filter (fun n : ℕ => |(k : ℝ) * n - m| ≤ R),
          Real.exp (w / 2) * Real.sqrt k := by
      rw [sum_filter]
      refine sum_le_sum fun n hn => ?_
      have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
      unfold lagWin
      split_ifs with h1 h2
      · rw [mul_one]; exact (downWin_bounds hk1 hm1 hn1 h1).1
      · exact absurd (by
          have h3 := (downWin_bounds hk1 hm1 hn1 h1).2
          push_cast at h3
          exact h3) h2
      · rw [mul_zero]; positivity
      · rw [mul_zero]
    rw [sum_const, nsmul_eq_mul] at hinner
    have hcard := card_mul_near_le (Ioc M N) hk1 (m : ℝ) hR
    by_cases hkK : k ∈ Icc 1 k₂
    · rw [if_pos hkK, vonMangoldtAtom_eq hk2]
      calc (ArithmeticFunction.vonMangoldt k : ℝ) / Real.sqrt k *
            ∑ n ∈ Ioc M N, Real.sqrt ((m : ℝ) / n) * lagWin w k n m
          ≤ (ArithmeticFunction.vonMangoldt k : ℝ) / Real.sqrt k *
              ((2 * R / k + 1) * (Real.exp (w / 2) * Real.sqrt k)) :=
            mul_le_mul_of_nonneg_left (hinner.trans
              (mul_le_mul_of_nonneg_right hcard (by positivity))) (by positivity)
        _ = (ArithmeticFunction.vonMangoldt k : ℝ) *
              (Real.exp (w / 2) * (2 * m * (Real.exp w - 1) / k + 1)) := by
            dsimp only [R]
            field_simp
    · rw [if_neg hkK]
      have hbig : X < k := by
        have : k₂ < k := by
          by_contra hle
          exact hkK (mem_Icc.mpr ⟨hk1, by omega⟩)
        exact Nat.lt_of_floor_lt this
      have hzero : ∑ n ∈ Ioc M N, Real.sqrt ((m : ℝ) / n) * lagWin w k n m = 0 := by
        refine sum_eq_zero fun n hn => ?_
        obtain ⟨hMn, hnN⟩ := mem_Ioc.mp hn
        have hn1 : 1 ≤ n := by omega
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        unfold lagWin
        split_ifs with h1
        · exfalso
          have hlog : Real.log k ≤ Real.log m - Real.log n + w := by linarith [(abs_le.mp h1).2]
          have hkle : (k : ℝ) * n ≤ m * Real.exp w := by
            have h2 : Real.log ((k : ℝ) * n) ≤ Real.log m + w := by
              rw [Real.log_mul hk0.ne' hn0.ne']; linarith
            have h3 := Real.exp_le_exp.mpr h2
            rwa [Real.exp_log (by positivity), Real.exp_add, Real.exp_log hm0] at h3
          have hMn' : (M : ℝ) + 1 ≤ n := by exact_mod_cast hMn
          have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
          have hXk : X * ((M : ℝ) + 1) = Real.exp w * N := by
            dsimp only [X]; field_simp
          nlinarith [Real.exp_pos w]
        · rw [mul_zero]
      rw [hzero, mul_zero]
  refine (sum_le_sum hk).trans ?_
  rw [← sum_filter]
  have hsub : (range K).filter (fun k => k ∈ Icc 1 k₂) ⊆ Icc 1 k₂ := fun k hk => (mem_filter.mp hk).2
  have hnn : ∀ k ∈ Icc 1 k₂, 0 ≤ (ArithmeticFunction.vonMangoldt k : ℝ) *
      (Real.exp (w / 2) * (2 * m * (Real.exp w - 1) / k + 1)) := fun k _ => by
    have := ArithmeticFunction.vonMangoldt_nonneg (n := k); positivity
  refine (sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => hnn k hk).trans ?_
  have hsplit : ∑ k ∈ Icc 1 k₂, (ArithmeticFunction.vonMangoldt k : ℝ) *
      (Real.exp (w / 2) * (2 * m * (Real.exp w - 1) / k + 1)) =
      Real.exp (w / 2) * (2 * m * (Real.exp w - 1) * ∑ k ∈ Icc 1 k₂,
        (ArithmeticFunction.vonMangoldt k : ℝ) / k +
        ∑ k ∈ Icc 1 k₂, (ArithmeticFunction.vonMangoldt k : ℝ)) := by
    rw [mul_sum, ← sum_add_distrib, mul_sum]
    exact sum_congr rfl fun k _ => by ring
  rw [hsplit]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hcheb := sum_vonMangoldt_Icc_le k₂
  have hk₂ : (k₂ : ℝ) ≤ X := Nat.floor_le (by positivity)
  have hmert := sum_vonMangoldt_div_Icc_floor_le hX1
  have hmN' : 2 * m * (Real.exp w - 1) ≤ 2 * ((Real.exp w - 1) * N) := by
    have : (m : ℝ) ≤ N := by exact_mod_cast hmN
    nlinarith
  have hmert0 : 0 ≤ ∑ k ∈ Icc 1 k₂, (ArithmeticFunction.vonMangoldt k : ℝ) / k :=
    sum_nonneg fun k _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
  have hlogX : 0 ≤ Real.log X + (Real.log 4 + 4) := by
    have := Real.log_nonneg hX1
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  have hA : 2 * m * (Real.exp w - 1) * ∑ k ∈ Icc 1 k₂, (ArithmeticFunction.vonMangoldt k : ℝ) / k ≤
      2 * ((Real.exp w - 1) * N) * (Real.log X + (Real.log 4 + 4)) :=
    mul_le_mul hmN' hmert hmert0 (by positivity)
  have hB : ∑ k ∈ Icc 1 k₂, (ArithmeticFunction.vonMangoldt k : ℝ) ≤ (Real.log 4 + 4) * X :=
    hcheb.trans (mul_le_mul_of_nonneg_left hk₂ (by positivity))
  linarith

/-- The row constant of the top prime self-form (`O(c(1 + log c))` at `w = c/N`, `N/(M+1) ≍ c`). -/
def topPrimeRow (w : ℝ) (M N : ℕ) : ℝ :=
  Real.exp (w / 2) * (2 * (Real.log 4 + 4) * Real.exp w * ((Real.exp w - 1) * N) +
      (Real.log (Real.exp w * N / (M + 1)) + (Real.log 4 + 4))) +
    Real.exp (w / 2) * (2 * ((Real.exp w - 1) * N) *
        (Real.log (Real.exp w * N / (M + 1)) + (Real.log 4 + 4)) +
      (Real.log 4 + 4) * (Real.exp w * N / (M + 1)))

/-- **The prime self-form of the top.** For `y` supported on `(M, N]`, ratio and non-ratio lags
together cost at most `topPrimeRow w M N` per unit mass. -/
theorem abs_primeSum_top_le (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 ≤ w) {M N : ℕ} (hMN : M < N)
    (y : ℕ → ℝ) (hy : ∀ n ∈ Icc 1 M, y n = 0) :
    |primeSum (atomicTest N y g)| ≤
      (∫ u, g u ^ 2) * topPrimeRow w M N * ∑ n ∈ Icc 1 N, y n ^ 2 := by
  set G := ∫ u, g u ^ 2
  have hG : 0 ≤ G := integral_nonneg fun u => sq_nonneg _
  set K := ⌈(N : ℝ) * Real.exp w⌉₊ + 1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfin : primeSum (atomicTest N y g) =
      ∑ k ∈ range K, vonMangoldtAtom k * lagForm g N k y := by
    rw [primeSum_atomicTest_eq_lags hg hgc]
    refine tsum_eq_sum fun k hk => ?_
    simp only [mem_range, not_lt] at hk
    have hbig : (N : ℝ) * Real.exp w < k := by
      have := Nat.le_ceil ((N : ℝ) * Real.exp w)
      have h2 : ((⌈(N : ℝ) * Real.exp w⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
      push_cast at h2
      linarith
    have hlog : Real.log N + w < Real.log k := by
      rw [← Real.log_exp w, ← Real.log_mul hN0.ne' (Real.exp_pos w).ne']
      exact Real.log_lt_log (by positivity) hbig
    rw [lagForm_eq_zero_of_log_lt hgsupp hw0 hlog, mul_zero]
  set V : ℕ → ℕ → ℝ := fun m n =>
    ∑ k ∈ range K, vonMangoldtAtom k * (lagWin w k m n + lagWin w k n m)
  have hV0 : ∀ m n, 0 ≤ V m n := fun m n => sum_nonneg fun k _ =>
    mul_nonneg (SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k) (add_nonneg (lagWin_nonneg _ _ _ _) (lagWin_nonneg _ _ _ _))
  have h1 : |primeSum (atomicTest N y g)| ≤
      G * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |y m| * |y n| * V m n := by
    rw [hfin]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ range K, |vonMangoldtAtom k * lagForm g N k y|
        ≤ ∑ k ∈ range K, vonMangoldtAtom k * (G * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
            |y m| * |y n| * (lagWin w k m n + lagWin w k n m)) := by
          refine sum_le_sum fun k _ => ?_
          rw [abs_mul, abs_of_nonneg (SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k)]
          exact mul_le_mul_of_nonneg_left (abs_lagForm_le_lagWin hg hgc hgsupp N k y)
            (SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k)
      _ = G * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |y m| * |y n| * V m n := by
          simp only [V, mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun m _ => ?_
          rw [sum_comm]
          exact sum_congr rfl fun n _ => sum_congr rfl fun k _ => by ring
  set S := Ioc M N
  set V' : ℕ → ℕ → ℝ := fun m n => if m ∈ S ∧ n ∈ S then V m n else 0
  have hV'0 : ∀ m n, 0 ≤ V' m n := fun m n => by
    dsimp only [V']; split_ifs
    · exact hV0 m n
    · exact le_rfl
  have hV'sym : ∀ m n, V' m n = V' n m := fun m n => by
    dsimp only [V', V]
    by_cases h : m ∈ S ∧ n ∈ S
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩]; exact sum_congr rfl fun k _ => by ring
    · rw [if_neg h, if_neg fun h' => h ⟨h'.2, h'.1⟩]
  have hyS : ∀ n ∈ Icc 1 N, n ∉ S → y n = 0 := fun n hn hnS =>
    hy n (mem_Icc.mpr ⟨(mem_Icc.mp hn).1, by
      by_contra h; exact hnS (mem_Ioc.mpr ⟨not_le.mp h, (mem_Icc.mp hn).2⟩)⟩)
  have hrestrict : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |y m| * |y n| * V m n =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |y m| * |y n| * V' m n := by
    refine sum_congr rfl fun m hm => sum_congr rfl fun n hn => ?_
    dsimp only [V']
    by_cases h : m ∈ S ∧ n ∈ S
    · rw [if_pos h]
    · rw [if_neg h]
      rcases not_and_or.mp h with hm' | hn'
      · rw [hyS m hm hm', abs_zero]; ring
      · rw [hyS n hn hn', abs_zero]; ring
  have hschur := sum_abs_mul_le_schur N y V' hV'0 hV'sym
  have hSsub : S ⊆ Icc 1 N := fun n hn =>
    mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
  have hrow : ∀ m ∈ Icc 1 N, y m ^ 2 * ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * V' m n ≤
      y m ^ 2 * topPrimeRow w M N := by
    intro m hm
    by_cases hmS : m ∈ S
    · refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      obtain ⟨hMm, hmN⟩ := mem_Ioc.mp hmS
      have hm1 : 1 ≤ m := by omega
      have hV'row : ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * V' m n =
          ∑ n ∈ S, Real.sqrt ((m : ℝ) / n) * V m n := by
        rw [← sum_subset hSsub fun n _ hnS => by
          dsimp only [V']; rw [if_neg fun h => hnS h.2, mul_zero]]
        refine sum_congr rfl fun n hn => ?_
        dsimp only [V']; rw [if_pos ⟨hmS, hn⟩]
      have hswap : ∑ n ∈ S, Real.sqrt ((m : ℝ) / n) * V m n =
          ∑ k ∈ range K, vonMangoldtAtom k * ∑ n ∈ S, Real.sqrt ((m : ℝ) / n) * lagWin w k m n +
          ∑ k ∈ range K, vonMangoldtAtom k * ∑ n ∈ S, Real.sqrt ((m : ℝ) / n) * lagWin w k n m := by
        simp only [V, mul_sum, ← sum_add_distrib]
        rw [sum_comm]
        exact sum_congr rfl fun k _ => sum_congr rfl fun n _ => by ring
      have hup_sub : ∑ k ∈ range K, vonMangoldtAtom k *
            ∑ n ∈ S, Real.sqrt ((m : ℝ) / n) * lagWin w k m n ≤
          ∑ k ∈ range K, vonMangoldtAtom k *
            ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * lagWin w k m n :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg hSsub fun n _ _ =>
            mul_nonneg (Real.sqrt_nonneg _) (lagWin_nonneg _ _ _ _)) (SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k)
      have hup := top_up_row_le hw0 hm1 hmN K
      have hdown := top_down_row_le hw0 hMm hmN K
      have hlogm : Real.log ((N : ℝ) * Real.exp w / m) ≤ Real.log (Real.exp w * N / (M + 1)) := by
        have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
        refine Real.log_le_log (by positivity) ?_
        rw [mul_comm (N : ℝ)]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (by exact_mod_cast (show M + 1 ≤ m by omega))
      rw [hV'row, hswap]
      unfold topPrimeRow
      have he : 0 ≤ Real.exp (w / 2) := (Real.exp_pos _).le
      nlinarith [mul_le_mul_of_nonneg_left hlogm he]
    · have hy0 : y m = 0 := hyS m hm hmS
      rw [hy0]; simp
  calc |primeSum (atomicTest N y g)| ≤ G * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |y m| * |y n| * V m n := h1
    _ ≤ G * ∑ m ∈ Icc 1 N, y m ^ 2 * topPrimeRow w M N := by
        rw [hrestrict]
        exact mul_le_mul_of_nonneg_left (hschur.trans (sum_le_sum hrow)) hG
    _ = G * topPrimeRow w M N * ∑ n ∈ Icc 1 N, y n ^ 2 := by
        rw [← sum_mul]; ring

/-! ### The row constant at overlap `c` -/

/-- The constant of `topPrimeRow_le`. -/
def topPrimeConstant : ℝ :=
  Real.exp (1 / 2) * (2 * (Real.log 4 + 4) * Real.exp 1 ^ 2 +
    2 * (Real.log (Real.exp 1 * (256 * Real.exp 2 + 4)) + (Real.log 4 + 4)) +
    2 * Real.exp 1 * (Real.log (Real.exp 1 * (256 * Real.exp 2 + 4)) + (Real.log 4 + 4) + 1) +
    (Real.log 4 + 4) * Real.exp 1 * (256 * Real.exp 2 + 4) + 1)

/-- **At overlap `c` the top prime row is `O(c (1 + log c))`.** -/
theorem topPrimeRow_le {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hLN : linearDefectCutoff c ≤ N) :
    topPrimeRow (c / N) (N / linearDefectCutoff c) N ≤ topPrimeConstant * c * (1 + Real.log c) := by
  obtain ⟨hL3, h4c, -, hLup⟩ := linearDefectCutoff_bounds hc
  set L := linearDefectCutoff c
  set M := N / L
  set A := 256 * Real.exp 2 + 4
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLR : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hcN : 4 * c ≤ N := h4c.trans hLR
  set w := c / (N : ℝ)
  have hw0 : 0 ≤ w := div_nonneg hc0.le hN0.le
  have hw1 : w ≤ 1 := (div_le_one hN0).mpr (by linarith)
  have he1 : Real.exp w ≤ Real.exp 1 := Real.exp_le_exp.mpr hw1
  have he2 : Real.exp (w / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
  have hew : 0 ≤ Real.exp w - 1 := by linarith [Real.add_one_le_exp w]
  have hD : (Real.exp w - 1) * N ≤ Real.exp 1 * c := by
    have h := exp_sub_one_le_mul_exp (w := w)
    have hwN : w * N = c := by dsimp only [w]; field_simp
    calc (Real.exp w - 1) * N ≤ w * Real.exp w * N := mul_le_mul_of_nonneg_right h hN0.le
      _ = c * Real.exp w := by rw [mul_right_comm, hwN]
      _ ≤ c * Real.exp 1 := mul_le_mul_of_nonneg_left he1 hc0.le
      _ = Real.exp 1 * c := mul_comm _ _
  have hM1N : (M : ℝ) + 1 ≤ N := by
    have : M + 1 ≤ N := by
      have : M ≤ N / 3 := Nat.div_le_div_left hL3 (by norm_num)
      omega
    exact_mod_cast this
  have hNML : (N : ℝ) < ((M : ℝ) + 1) * L := by
    have ht : N < (M + 1) * L := by
      simpa only [M, Nat.mul_comm] using Nat.lt_mul_div_succ N (show 0 < L by omega)
    exact_mod_cast ht
  set X := Real.exp w * N / (M + 1)
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hX1 : 1 ≤ X := by
    rw [le_div_iff₀ hM1, one_mul]
    exact hM1N.trans (le_mul_of_one_le_left hN0.le (Real.one_le_exp hw0))
  have hXup : X ≤ Real.exp 1 * A * c := by
    have h1 : (N : ℝ) / (M + 1) ≤ L := by rw [div_le_iff₀ hM1]; linarith
    calc X = Real.exp w * (N / (M + 1)) := by dsimp only [X]; ring
      _ ≤ Real.exp 1 * (A * c) :=
          mul_le_mul he1 (h1.trans hLup) (by positivity) (Real.exp_pos 1).le
      _ = Real.exp 1 * A * c := by ring
  have hA1 : 1 ≤ Real.exp 1 * A := by
    have := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
    have := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)
    dsimp only [A]; nlinarith
  have hlogX : Real.log X ≤ Real.log (Real.exp 1 * A) + Real.log c := by
    rw [← Real.log_mul (by positivity) hc0.ne']
    exact Real.log_le_log (by positivity) hXup
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hC4 : 0 ≤ Real.log 4 + 4 := by have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  set B := Real.log (Real.exp 1 * A) + (Real.log 4 + 4)
  have hB : 0 ≤ B := by have := Real.log_nonneg hA1; dsimp only [B]; linarith
  have hE : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hlc1 : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos hc0
  set Y := c * (1 + Real.log c)
  have hY1 : 1 ≤ Y := by
    have := mul_le_mul hc (show (1 : ℝ) ≤ 1 + Real.log c by linarith) zero_le_one hc0.le
    simpa only [one_mul, Y] using this
  have hcY : c ≤ Y := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + Real.log c by linarith) hc0.le
    simpa only [mul_one, Y] using this
  have hlcY : Real.log c ≤ Y := by linarith
  have hclcY : c * Real.log c ≤ Y := by dsimp only [Y]; linarith [mul_nonneg hc0.le hlc]
  -- the two half-rows
  have hED : Real.exp w * ((Real.exp w - 1) * N) ≤ Real.exp 1 ^ 2 * c :=
    (mul_le_mul he1 hD (by positivity) hE).trans_eq (by ring)
  have hT1 : 2 * (Real.log 4 + 4) * Real.exp w * ((Real.exp w - 1) * N) +
      (Real.log X + (Real.log 4 + 4)) ≤ 2 * (Real.log 4 + 4) * Real.exp 1 ^ 2 * c + (B + Real.log c) := by
    have h1 := mul_le_mul_of_nonneg_left hED (show 0 ≤ 2 * (Real.log 4 + 4) by positivity)
    dsimp only [B]
    linarith
  have hT2 : 2 * ((Real.exp w - 1) * N) * (Real.log X + (Real.log 4 + 4)) + (Real.log 4 + 4) * X ≤
      2 * Real.exp 1 * c * (B + Real.log c) + (Real.log 4 + 4) * (Real.exp 1 * A * c) := by
    have h1 : 2 * ((Real.exp w - 1) * N) * (Real.log X + (Real.log 4 + 4)) ≤
        2 * (Real.exp 1 * c) * (B + Real.log c) :=
      mul_le_mul (by linarith) (by dsimp only [B]; linarith) (by positivity) (by positivity)
    have h2 := mul_le_mul_of_nonneg_left hXup hC4
    linarith
  have hrow : topPrimeRow w M N ≤ Real.exp (1 / 2) * ((2 * (Real.log 4 + 4) * Real.exp 1 ^ 2 * c +
      (B + Real.log c)) + (2 * Real.exp 1 * c * (B + Real.log c) +
        (Real.log 4 + 4) * (Real.exp 1 * A * c))) := by
    have he0 : 0 ≤ Real.exp (w / 2) := (Real.exp_pos _).le
    have hP1 : 0 ≤ 2 * (Real.log 4 + 4) * Real.exp 1 ^ 2 * c + (B + Real.log c) := by positivity
    have hP2 : 0 ≤ 2 * Real.exp 1 * c * (B + Real.log c) + (Real.log 4 + 4) * (Real.exp 1 * A * c) := by
      dsimp only [A]; positivity
    have k1 := mul_le_mul he2 hT1 (by
      have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * (Real.log 4 + 4)) (Real.exp_pos w).le)
        (mul_nonneg hew hN0.le)
      linarith) (Real.exp_pos _).le
    have k2 := mul_le_mul he2 hT2 (by
      have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hew hN0.le))
        (show 0 ≤ Real.log X + (Real.log 4 + 4) by linarith)
      have := mul_nonneg hC4 (zero_le_one.trans hX1)
      linarith) (Real.exp_pos _).le
    unfold topPrimeRow
    linarith
  have hK : (2 * (Real.log 4 + 4) * Real.exp 1 ^ 2 * c + (B + Real.log c)) +
      (2 * Real.exp 1 * c * (B + Real.log c) + (Real.log 4 + 4) * (Real.exp 1 * A * c)) ≤
      (2 * (Real.log 4 + 4) * Real.exp 1 ^ 2 + 2 * B + 2 * Real.exp 1 * (B + 1) +
        (Real.log 4 + 4) * Real.exp 1 * A + 1) * Y := by
    have k1 := mul_le_mul_of_nonneg_left hcY (show 0 ≤ 2 * (Real.log 4 + 4) * Real.exp 1 ^ 2 by positivity)
    have k2 := mul_le_mul_of_nonneg_left hY1 hB
    have k3 := mul_le_mul_of_nonneg_left hcY (show 0 ≤ 2 * Real.exp 1 * B by positivity)
    have k4 := mul_le_mul_of_nonneg_left hclcY (show 0 ≤ 2 * Real.exp 1 by positivity)
    have k5 := mul_le_mul_of_nonneg_left hcY
      (show 0 ≤ (Real.log 4 + 4) * Real.exp 1 * A by dsimp only [A]; positivity)
    have k6 := mul_le_mul_of_nonneg_left hY1 hB
    nlinarith [k1, k2, k3, k4, k5, k6, hlcY]
  calc topPrimeRow w M N ≤ _ := hrow
    _ ≤ Real.exp (1 / 2) * ((2 * (Real.log 4 + 4) * Real.exp 1 ^ 2 + 2 * B + 2 * Real.exp 1 * (B + 1) +
        (Real.log 4 + 4) * Real.exp 1 * A + 1) * Y) := mul_le_mul_of_nonneg_left hK (Real.exp_pos _).le
    _ = topPrimeConstant * c * (1 + Real.log c) := by
        unfold topPrimeConstant; dsimp only [B, A, Y]; ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
