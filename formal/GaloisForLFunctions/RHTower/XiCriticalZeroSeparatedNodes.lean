import GaloisForLFunctions.RHTower.HardyTwoSeventhCensus
import GaloisForLFunctions.RHTower.HardyZThetaTrace
import GaloisForLFunctions.RHTower.XiWindowZeroCount
import GaloisForLFunctions.RHTower.XiCanonicalProduct

/-!
# Separated critical zeros at polynomial height

**Theorem** (`exists_separated_Xi_zeros`).  There is `K ≥ 1` such that for every `d` there are
`d + 1` real zeros `t_0, …, t_d` of `Ξ` with `1 ≤ t_i ≤ 2 (K (d + 1))^{63}` and `|t_i − t_j| ≥ 1`
for `i ≠ j`.

Proof.  The Hardy census gives at least `c T^{2/7}/(1 + log T)^9` distinct critical zeros in
`(T, 2T]` (`exists_many_distinct_line_zeros_dyadic_twoSeventh`).  A unit interval `[k, k + 1)`
contains at most `10 (A + log(k + 5))` of them, by the window count
(`ncard_xiOrdinateWindow_le_log`).  So at least `c T^{2/7}/((1 + log T)^9 m(T))` unit intervals
are occupied.  Keeping one zero in every occupied interval of one parity gives a `1`-separated
family.  With `T = u^{63}` and `u = K (d + 1)` the count exceeds `d + 1`.
-/

open Complex Finset

namespace RHTower

noncomputable section

/-- A critical zero of `ζ` at ordinate `τ` is a real zero of `Ξ`. -/
theorem Xi_eq_zero_of_riemannZeta_linePt_eq_zero {τ : ℝ} (h : riemannZeta (linePt τ) = 0) :
    Xi τ = 0 :=
  (Xi_eq_zero_iff_hardyZ τ).2 ((riemannZeta_line_eq_zero_iff_hardyZ τ).1 h)

/-- A real zero of `Ξ` is the ordinate of a zero copy. -/
theorem exists_xiZeroCopy_im_eq_of_Xi_eq_zero {τ : ℝ} (h : Xi τ = 0) :
    ∃ q : XiZeroCopy, xiSpectralPoint q = (τ : ℂ) ∧ ((q.1 : ℂ)).im = τ := by
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (τ : ℂ)).1 (by rw [XiC_ofReal, h,
    ofReal_zero])
  refine ⟨q, hq, ?_⟩
  have h1 : ((q.1 : ℂ) - 1 / 2) * (-I) = (τ : ℂ) := hq
  have h2 : (q.1 : ℂ) = 1 / 2 + (τ : ℂ) * I := by
    linear_combination I * h1 + ((q.1 : ℂ) - 1 / 2) * I_sq
  rw [h2]
  simp

/-- At most `10 (A + log(k + 5))` distinct critical zeros lie in `[k, k + 1)`. -/
theorem card_filter_floor_eq_le {S : Finset ℝ} (hS : ∀ τ ∈ S, 0 ≤ τ ∧ Xi τ = 0) (k : ℕ) :
    ((S.filter fun τ => ⌊τ⌋₊ = k).card : ℝ) ≤
      10 * (xiLineTwoLogDerivConstant + Real.log (k + 5)) := by
  classical
  set W := xiOrdinateWindow (1 / 2) (k + 1 / 2) with hW
  have hfin := finite_xiOrdinateWindow (1 / 2) ((k : ℝ) + 1 / 2)
  have hcardle : (S.filter fun τ => ⌊τ⌋₊ = k).card ≤ hfin.toFinset.card := by
    rcases (S.filter fun τ => ⌊τ⌋₊ = k).eq_empty_or_nonempty with he | ⟨τ₀, hτ₀⟩
    · rw [he, Finset.card_empty]; exact Nat.zero_le _
    haveI : Nonempty XiZeroCopy := by
      obtain ⟨q, -, -⟩ := exists_xiZeroCopy_im_eq_of_Xi_eq_zero
        (hS τ₀ (Finset.mem_filter.1 hτ₀).1).2
      exact ⟨q⟩
    have hcopy : ∀ τ ∈ S, ∃ q : XiZeroCopy, ((q.1 : ℂ)).im = τ := fun τ hτ => by
      obtain ⟨q, -, hq⟩ := exists_xiZeroCopy_im_eq_of_Xi_eq_zero (hS τ hτ).2
      exact ⟨q, hq⟩
    choose! g hg using hcopy
    have hmaps : ∀ τ ∈ S.filter fun τ => ⌊τ⌋₊ = k, g τ ∈ hfin.toFinset := by
      intro τ hτ
      rw [Finset.mem_filter] at hτ
      rw [Set.Finite.mem_toFinset, mem_xiOrdinateWindow_iff, hg τ hτ.1]
      have h0 := (hS τ hτ.1).1
      have hlo : (k : ℝ) ≤ τ := by
        have := Nat.floor_le h0
        rwa [hτ.2] at this
      have hhi : τ < k + 1 := by
        have := Nat.lt_floor_add_one τ
        rwa [hτ.2] at this
      rw [abs_le]
      constructor <;> linarith
    have hinj : Set.InjOn g ↑(S.filter fun τ => ⌊τ⌋₊ = k) := by
      intro τ hτ τ' hτ' h
      have h1 := hg τ (Finset.mem_filter.1 hτ).1
      have h2 := hg τ' (Finset.mem_filter.1 hτ').1
      rw [← h1, ← h2, h]
    exact Finset.card_le_card_of_injOn g hmaps hinj
  have hW := ncard_xiOrdinateWindow_le_log (1 / 2) ((k : ℝ) + 1 / 2)
  rw [Set.ncard_eq_toFinset_card _ hfin] at hW
  have habs : |(k : ℝ) + 1 / 2| + 4 = k + 9 / 2 := by
    rw [abs_of_nonneg (by positivity)]; ring
  rw [habs] at hW
  have hlog : Real.log ((k : ℝ) + 9 / 2) ≤ Real.log (k + 5) :=
    Real.log_le_log (by positivity) (by linarith)
  calc ((S.filter fun τ => ⌊τ⌋₊ = k).card : ℝ) ≤ hfin.toFinset.card := by exact_mod_cast hcardle
    _ ≤ 8 * (1 + (1 / 2) ^ 2) * (xiLineTwoLogDerivConstant + Real.log (k + 9 / 2)) := hW
    _ ≤ 10 * (xiLineTwoLogDerivConstant + Real.log (k + 5)) := by
        have hpos : 0 ≤ xiLineTwoLogDerivConstant + Real.log (k + 9 / 2) := by
          have := hW
          have h0 : (0 : ℝ) ≤ hfin.toFinset.card := Nat.cast_nonneg _
          nlinarith
        nlinarith

/-- **Separation from bins.**  If a finite set `S ⊆ [0, ∞)` meets at least `2 (d + 1)` distinct
unit bins `[k, k + 1)`, it contains `d + 1` points pairwise at distance `≥ 1`. -/
theorem exists_separated_of_card_image_floor {S : Finset ℝ} (hS : ∀ τ ∈ S, 0 ≤ τ) {d : ℕ}
    (hB : 2 * (d + 1) ≤ (S.image fun τ => ⌊τ⌋₊).card) :
    ∃ t : Fin (d + 1) → ℝ, (∀ i, t i ∈ S) ∧ ∀ i j, i ≠ j → 1 ≤ |t i - t j| := by
  classical
  set B := S.image fun τ => ⌊τ⌋₊ with hBdef
  -- one parity class carries at least half of the bins
  obtain ⟨p, hp⟩ : ∃ p : ℕ, d + 1 ≤ (B.filter fun k => k % 2 = p).card := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := B) (fun k => k % 2 = 0)
    by_cases h0 : d + 1 ≤ (B.filter fun k => k % 2 = 0).card
    · exact ⟨0, h0⟩
    · refine ⟨1, ?_⟩
      have hneg : (B.filter fun k => ¬ k % 2 = 0) = B.filter fun k => k % 2 = 1 :=
        Finset.filter_congr fun k _ => Nat.mod_two_ne_zero
      rw [hneg] at hsplit
      omega
  set Bp := B.filter fun k => k % 2 = p with hBp
  -- a representative in each bin
  have hrep : ∀ k ∈ Bp, ∃ τ ∈ S, ⌊τ⌋₊ = k := fun k hk => by
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hk).1
    exact ⟨τ, hτ, rfl⟩
  choose! r hrS hrk using hrep
  -- an embedding of `Fin (d + 1)` into `Bp`
  obtain ⟨Bs, hBs, hBscard⟩ := Finset.exists_subset_card_eq hp
  obtain ⟨f, hfmem, hfinj⟩ : ∃ f : Fin (d + 1) → ℕ, (∀ i, f i ∈ Bs) ∧ Function.Injective f :=
    ⟨fun i => Bs.orderEmbOfFin hBscard i, fun i => Finset.orderEmbOfFin_mem Bs hBscard i,
      (Bs.orderEmbOfFin hBscard).injective⟩
  refine ⟨fun i => r (f i), fun i => hrS _ (hBs (hfmem i)), fun i j hij => ?_⟩
  have hi := hBs (hfmem i)
  have hj := hBs (hfmem j)
  have hki := hrk _ hi
  have hkj := hrk _ hj
  have hne : f i ≠ f j := fun h => hij (hfinj h)
  have hpi := (Finset.mem_filter.1 hi).2
  have hpj := (Finset.mem_filter.1 hj).2
  have hgap : 2 ≤ (f i : ℤ) - f j ∨ 2 ≤ (f j : ℤ) - f i := by omega
  have h0i := hS _ (hrS _ hi)
  have h0j := hS _ (hrS _ hj)
  have hli : ((f i : ℕ) : ℝ) ≤ r (f i) := by
    have := Nat.floor_le h0i
    rwa [hki] at this
  have hui : r (f i) < (f i : ℕ) + 1 := by
    have := Nat.lt_floor_add_one (r (f i))
    rwa [hki] at this
  have hlj : ((f j : ℕ) : ℝ) ≤ r (f j) := by
    have := Nat.floor_le h0j
    rwa [hkj] at this
  have huj : r (f j) < (f j : ℕ) + 1 := by
    have := Nat.lt_floor_add_one (r (f j))
    rwa [hkj] at this
  rcases hgap with hg | hg
  · have : (2 : ℝ) ≤ ((f i : ℕ) : ℝ) - (f j : ℕ) := by exact_mod_cast hg
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (2 : ℝ) ≤ ((f j : ℕ) : ℝ) - (f i : ℕ) := by exact_mod_cast hg
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- **Separated critical zeros at polynomial height.** -/
theorem exists_separated_Xi_zeros :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ d : ℕ, ∃ t : Fin (d + 1) → ℝ, (∀ i, Xi (t i) = 0) ∧ (∀ i, 1 ≤ t i) ∧
      (∀ i, t i ≤ 2 * (K * (d + 1)) ^ 63) ∧ ∀ i j, i ≠ j → 1 ≤ |t i - t j| := by
  classical
  obtain ⟨c, hc, T₁, hT₁, hcen⟩ := exists_many_distinct_line_zeros_dyadic_twoSeventh
  obtain ⟨A, hA⟩ : ∃ A, A = xiLineTwoLogDerivConstant := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 1 + T₁ + 1400 * 64 ^ 9 * (|A| + 1) / c := ⟨_, rfl⟩
  have hq0 : 0 ≤ 1400 * 64 ^ 9 * (|A| + 1) / c := by positivity
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  refine ⟨K, hK1, fun d => ?_⟩
  -- the scale
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = K * (d + 1) := ⟨_, rfl⟩
  have hd1 : (1 : ℝ) ≤ d + 1 := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have hu1 : 1 ≤ u := by rw [hu]; nlinarith
  have hu0 : 0 < u := by linarith
  have huT₁ : T₁ ≤ u := by rw [hu, hK]; nlinarith
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = u ^ 63 := ⟨_, rfl⟩
  have huT : u ≤ T := by rw [hT]; exact le_self_pow₀ hu1 (by norm_num)
  have hT1 : 1 ≤ T := hu1.trans huT
  obtain ⟨τS, hτS, hcard⟩ := hcen T (huT₁.trans huT)
  have hτpos : ∀ τ ∈ τS, 0 ≤ τ ∧ Xi τ = 0 := fun τ hτ =>
    ⟨by linarith [(hτS τ hτ).1], Xi_eq_zero_of_riemannZeta_linePt_eq_zero (hτS τ hτ).2.2⟩
  -- the fiber bound
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈10 * (|A| + Real.log (2 * T + 5))⌉₊ := ⟨_, rfl⟩
  have hfib : ∀ k ∈ τS.image (fun τ => ⌊τ⌋₊), (τS.filter fun τ => ⌊τ⌋₊ = k).card ≤ n := by
    intro k hk
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hk
    have h1 := card_filter_floor_eq_le hτpos ⌊τ⌋₊
    rw [← hA] at h1
    have hkle : (⌊τ⌋₊ : ℝ) ≤ 2 * T := (Nat.floor_le (hτpos τ hτ).1).trans (hτS τ hτ).2.1
    have hlog : Real.log ((⌊τ⌋₊ : ℝ) + 5) ≤ Real.log (2 * T + 5) :=
      Real.log_le_log (by positivity) (by linarith)
    have h2 : ((τS.filter fun τ' => ⌊τ'⌋₊ = ⌊τ⌋₊).card : ℝ) ≤
        10 * (|A| + Real.log (2 * T + 5)) := by
      have := le_abs_self A
      linarith
    have h3 := h2.trans (Nat.le_ceil _)
    rw [← hn] at h3
    exact_mod_cast h3
  have hcardB := Finset.card_le_mul_card_image τS n hfib
  -- the count beats `2 (d + 1) n`
  have hnle : (n : ℝ) ≤ 700 * (|A| + 1) * u := by
    have hlogT : Real.log (2 * T + 5) ≤ 6 + 63 * u := by
      have h7 : 2 * T + 5 ≤ 7 * T := by linarith
      have hl7 : Real.log 7 ≤ 6 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 7)
        linarith
      calc Real.log (2 * T + 5) ≤ Real.log (7 * T) := Real.log_le_log (by positivity) h7
        _ = Real.log 7 + 63 * Real.log u := by
            rw [Real.log_mul (by norm_num) (by positivity), hT, Real.log_pow]; push_cast; ring
        _ ≤ 6 + 63 * u := by linarith [Real.log_le_self hu0.le]
    have hceil : (n : ℝ) ≤ 10 * (|A| + Real.log (2 * T + 5)) + 1 := by
      rw [hn]
      exact (Nat.ceil_lt_add_one (by
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * T + 5)
        positivity)).le
    have hA0 := abs_nonneg A
    nlinarith
  have hpow : c * T ^ ((2 : ℝ) / 7) / (1 + Real.log T) ^ 9 ≥ c * u ^ 9 / 64 ^ 9 := by
    have hT27 : T ^ ((2 : ℝ) / 7) = u ^ 18 := by
      rw [hT, ← Real.rpow_natCast u 63, ← Real.rpow_mul hu0.le]
      norm_num
    have hlog : 1 + Real.log T ≤ 64 * u := by
      rw [hT, Real.log_pow]
      push_cast
      have := Real.log_le_sub_one_of_pos hu0
      nlinarith
    have hlog0 : 0 < 1 + Real.log T := by
      have := Real.log_nonneg hT1
      linarith
    rw [hT27, ge_iff_le, div_le_div_iff₀ (by positivity) (by positivity)]
    have h9 : (1 + Real.log T) ^ 9 ≤ (64 * u) ^ 9 := pow_le_pow_left₀ hlog0.le hlog 9
    calc c * u ^ 9 * (1 + Real.log T) ^ 9 ≤ c * u ^ 9 * (64 * u) ^ 9 :=
          mul_le_mul_of_nonneg_left h9 (by positivity)
      _ = c * u ^ 18 * 64 ^ 9 := by ring
  have hbig : 2 * (d + 1) * (700 * (|A| + 1) * u) ≤ c * u ^ 9 / 64 ^ 9 := by
    rw [le_div_iff₀ (by positivity)]
    have hu8 : u ≤ u ^ 8 := le_self_pow₀ hu1 (by norm_num)
    have hKd : 1400 * 64 ^ 9 * (|A| + 1) / c * (d + 1) ≤ u := by
      rw [hu, hK]
      have : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      nlinarith
    have hKd' : 1400 * 64 ^ 9 * (|A| + 1) * (d + 1) ≤ c * u := by
      have := mul_le_mul_of_nonneg_left hKd hc.le
      rw [show c * (1400 * 64 ^ 9 * (|A| + 1) / c * (d + 1)) =
        1400 * 64 ^ 9 * (|A| + 1) * (d + 1) by field_simp] at this
      exact this
    have hcu : c * u ≤ c * u ^ 8 := mul_le_mul_of_nonneg_left hu8 hc.le
    nlinarith [mul_pos hu0 hc]
  have hB : 2 * (d + 1) ≤ (τS.image fun τ => ⌊τ⌋₊).card := by
    have hτc : (τS.card : ℝ) ≥ 2 * (d + 1) * n := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h1 : 2 * (d + 1) * (n : ℝ) ≤ 2 * (d + 1) * (700 * (|A| + 1) * u) :=
        mul_le_mul_of_nonneg_left hnle (by positivity)
      linarith
    have hn1 : 1 ≤ n := by
      by_contra h0
      push Not at h0
      have : n = 0 := by omega
      rw [this, zero_mul] at hcardB
      have : (τS.card : ℝ) = 0 := by exact_mod_cast Nat.le_zero.1 hcardB
      have hpos : 0 < c * u ^ 9 / 64 ^ 9 := by positivity
      linarith
    have : 2 * (d + 1) * n ≤ n * (τS.image fun τ => ⌊τ⌋₊).card := by
      have h := hcardB
      have h' : 2 * (d + 1) * n ≤ τS.card := by exact_mod_cast hτc
      linarith
    have := Nat.le_of_mul_le_mul_left (by linarith : n * (2 * (d + 1)) ≤
      n * (τS.image fun τ => ⌊τ⌋₊).card) (by omega : 0 < n)
    exact this
  obtain ⟨t, htS, hsep⟩ := exists_separated_of_card_image_floor (fun τ hτ => (hτpos τ hτ).1) hB
  refine ⟨t, fun i => (hτpos _ (htS i)).2, fun i => by linarith [(hτS _ (htS i)).1],
    fun i => ?_, hsep⟩
  have := (hτS _ (htS i)).2.1
  rw [hT, hu] at this
  exact this

end

end RHTower
