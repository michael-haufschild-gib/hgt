import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenSliceTokens
import GaloisForLFunctions.RHTower.RouteECofactorParityBalance

/-!
# The row supply of the all-interval `E₃` theorem across dyadic slices

For large `y`, the interval `(y, y + H]`, `H = √y (log y)^{31/20}`, contains `≫ H/(log y)²` distinct
`E₃` numbers `p₁p₂n` with `p₁` in a polylogarithmic band and `p₂ ≠ n` large primes
(`eventually_card_bandTokens_ge`).  Each dyadic slice `P = 2^k ∈ [(log 2y)^{1.0999}, (log y)^{1.1}/4]`
covers `(y, y + H]` by `⌊H/s⌋` disjoint natural windows `(x_i, x_i + √(x_iP) log x_i]`,
`x_i = y + is`, `s = √(2yP) log 2y`, each carrying `≫ √(yP) log y/(log P (log y)²)` slice tokens;
a slice thus gives `≫ H/(log log y (log y)²)`, the `≫ log log y` slices are disjoint (a token's
small prime fixes its slice), and the `log log y` losses cancel.
-/

namespace RHTower.Sieve

open Finset Filter

noncomputable section

open Classical in
/-- The `E₃` numbers `p₁p₂n ∈ (y, y + H]` with `p₁` in the band `[z₀, z]` and `p₂ ≠ n` primes above
`T`. -/
def bandTokens (z₀ z T : ℕ) (y H : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊y⌋₊ ⌊y + H⌋₊).filter fun m => ∃ p₁ p₂ n : ℕ, p₁.Prime ∧ p₂.Prime ∧ n.Prime ∧
    p₂ ≠ n ∧ z₀ ≤ p₁ ∧ p₁ ≤ z ∧ T < p₂ ∧ T < n ∧ m = p₁ * p₂ * n

/-- **The shape of a slice token.**  With `4PR² = x`, a token of the slice `(P, 2P] × (R, 2R]` in the
window `(x, x+h]` is `p₁p₂n` with `P < p₁ ≤ 2P`, `R < p₂ ≤ 2R`, `n ≠ p₂` prime above `R`. -/
theorem mem_sliceTokens_facts {P R x h : ℝ} {m : ℕ} (hP : 0 < P) (hR : 0 < R)
    (hPRx : 4 * P * R ^ 2 = x)
    (hm : m ∈ sliceTokens ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime)
      ((Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊).filter Nat.Prime) x h) :
    ∃ p₁ p₂ n : ℕ, p₁.Prime ∧ p₂.Prime ∧ n.Prime ∧ p₂ ≠ n ∧ P < p₁ ∧ (p₁ : ℝ) ≤ 2 * P ∧
      R < p₂ ∧ (p₂ : ℝ) ≤ 2 * R ∧ R < n ∧ m = p₁ * p₂ * n ∧ x < (m : ℝ) ∧ (m : ℝ) ≤ x + h := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hm
  obtain ⟨hmem, hnp, hne, h1, h2⟩ := Finset.mem_filter.1 ht
  obtain ⟨ht1, hmem2⟩ := Finset.mem_product.1 hmem
  obtain ⟨ht2, -⟩ := Finset.mem_product.1 hmem2
  obtain ⟨hp₁, hp₁l, hp₁u⟩ := (mem_primes_Ioc_floor_iff hP.le).1 ht1
  obtain ⟨hp₂, hp₂l, hp₂u⟩ := (mem_primes_Ioc_floor_iff hR.le).1 ht2
  refine ⟨t.1, t.2.1, t.2.2, hp₁, hp₂, hnp, fun h => hne h.symm, hp₁l, hp₁u, hp₂l, hp₂u, ?_, rfl,
    h1, h2⟩
  -- `x < p₁p₂n ≤ 4PR n`, so `n > x/(4PR) = R`
  push_cast at h1
  have hq : (t.1 : ℝ) * t.2.1 ≤ 4 * P * R := by
    have := mul_le_mul hp₁u hp₂u (Nat.cast_nonneg _) (by linarith)
    linarith
  have hn0 : (0 : ℝ) ≤ t.2.2 := Nat.cast_nonneg _
  have h3 : x < 4 * P * R * t.2.2 := lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_right hq hn0)
  rw [← hPRx] at h3
  have h4 : 4 * P * R * R < 4 * P * R * t.2.2 := by nlinarith
  exact lt_of_mul_lt_mul_left h4 (by positivity)

/-- A slice token lies in the band tokens of `(y, y + H]` when its window does, `z₀ ≤ P`, `2P ≤ z`
and `T ≤ R`. -/
theorem sliceTokens_subset_bandTokens {P R x h y H : ℝ} {z₀ z T : ℕ} (hP : 0 < P) (hR : 0 < R)
    (hPRx : 4 * P * R ^ 2 = x) (hy : 0 ≤ y) (hyx : y ≤ x) (hxH : x + h ≤ y + H)
    (hz₀ : (z₀ : ℝ) ≤ P) (hz : 2 * P ≤ z) (hT : (T : ℝ) ≤ R) :
    sliceTokens ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime)
      ((Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊).filter Nat.Prime) x h ⊆ bandTokens z₀ z T y H := by
  classical
  intro m hm
  obtain ⟨p₁, p₂, n, h₁, h₂, h₃, hne, hp₁l, hp₁u, hp₂l, -, hnR, rfl, hlo, hhi⟩ :=
    mem_sliceTokens_facts hP hR hPRx hm
  unfold bandTokens
  refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨?_, ?_⟩, p₁, p₂, n, h₁, h₂, h₃, hne, ?_, ?_, ?_, ?_,
    rfl⟩
  · exact (Nat.floor_lt hy).2 (by linarith)
  · exact Nat.le_floor (by linarith)
  · exact_mod_cast hz₀.trans hp₁l.le
  · exact_mod_cast hp₁u.trans hz
  · exact_mod_cast hT.trans_lt hp₂l
  · exact_mod_cast hT.trans_lt hnR

/-- **Disjoint windows add up.**  If `S i ⊆ (x₀ + is, x₀ + (i+1)s]` and `#S i ≥ c` for `i < K`, the
union has at least `Kc` elements. -/
theorem le_card_biUnion_windows {S : ℕ → Finset ℕ} {x₀ s c : ℝ} {K : ℕ} (hs : 0 < s)
    (hS : ∀ i < K, ∀ m ∈ S i, x₀ + i * s < (m : ℝ) ∧ (m : ℝ) ≤ x₀ + (i + 1) * s)
    (hc : ∀ i < K, c ≤ ((S i).card : ℝ)) :
    K * c ≤ (((Finset.range K).biUnion S).card : ℝ) := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range K) : Set ℕ) S := by
    intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_left]
    intro m hmi hmj
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    obtain ⟨a1, a2⟩ := hS i hi' m hmi
    obtain ⟨b1, b2⟩ := hS j hj' m hmj
    rcases lt_or_gt_of_ne hij with h | h
    · have : ((i : ℕ) : ℝ) + 1 ≤ j := by exact_mod_cast h
      nlinarith
    · have : ((j : ℕ) : ℝ) + 1 ≤ i := by exact_mod_cast h
      nlinarith
  rw [Finset.card_biUnion hdisj]
  push_cast
  calc (K : ℝ) * c = ∑ _i ∈ Finset.range K, c := by rw [Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    _ ≤ ∑ i ∈ Finset.range K, ((S i).card : ℝ) :=
        Finset.sum_le_sum fun i hi => hc i (Finset.mem_range.1 hi)

/-- The slice tokens of one dyadic slice `P` over the windows `x_i = y + is`, `i < ⌊H/s⌋`. -/
def sliceWindowTokens (P y H s : ℝ) : Finset ℕ :=
  (Finset.range ⌊H / s⌋₊).biUnion fun i =>
    sliceTokens ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime)
      ((Finset.Ioc ⌊Real.sqrt ((y + i * s) / P) / 2⌋₊
        ⌊2 * (Real.sqrt ((y + i * s) / P) / 2)⌋₊).filter Nat.Prime) (y + i * s)
      (Real.sqrt ((y + i * s) * P) * Real.log (y + i * s))

/-- **One slice across the common interval.**  If every natural window `(x, x + h(x)]`,
`h(x) = √(xP) log x ≤ s`, with `x ∈ [y, y + H]` carries at least `c` slice tokens, then the windows
`x_i = y + is` give at least `⌊H/s⌋ c` tokens in `(y, y + H]`, all band tokens when `z₀ ≤ P`,
`2P ≤ z`, `T ≤ √(y/P)/2`. -/
theorem sliceWindowTokens_facts {P y H s c : ℝ} {z₀ z T : ℕ} (hP : 0 < P) (hy : 0 < y)
    (hs : 0 < s) (hc : ∀ x, y ≤ x → x ≤ y + H → c ≤ ((sliceTokens ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter
      Nat.Prime) ((Finset.Ioc ⌊Real.sqrt (x / P) / 2⌋₊ ⌊2 * (Real.sqrt (x / P) / 2)⌋₊).filter
        Nat.Prime) x (Real.sqrt (x * P) * Real.log x)).card : ℝ))
    (hstep : ∀ x, y ≤ x → x ≤ y + H → 0 ≤ Real.sqrt (x * P) * Real.log x ∧
      Real.sqrt (x * P) * Real.log x ≤ s)
    (hz₀ : (z₀ : ℝ) ≤ P) (hz : 2 * P ≤ z) (hT : (T : ℝ) ≤ Real.sqrt (y / P) / 2) :
    (⌊H / s⌋₊ : ℝ) * c ≤ ((sliceWindowTokens P y H s).card : ℝ) ∧
      sliceWindowTokens P y H s ⊆ bandTokens z₀ z T y H := by
  classical
  have hK : ∀ i < ⌊H / s⌋₊, y ≤ y + i * s ∧ y + i * s ≤ y + H ∧ y + (i + 1) * s ≤ y + H := by
    intro i hi
    have hi' : ((i : ℕ) : ℝ) + 1 ≤ ⌊H / s⌋₊ := by exact_mod_cast hi
    have hHs : 0 ≤ H / s := by
      by_contra hneg; push Not at hneg
      have : ⌊H / s⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith)
      omega
    have hfl : (⌊H / s⌋₊ : ℝ) * s ≤ H := by
      have := Nat.floor_le hHs
      rwa [le_div_iff₀ hs] at this
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  have hR : ∀ x, 0 < x → 4 * P * (Real.sqrt (x / P) / 2) ^ 2 = x := by
    intro x hx
    rw [div_pow, Real.sq_sqrt (by positivity)]; field_simp; ring
  refine ⟨le_card_biUnion_windows (x₀ := y) hs ?_ ?_, ?_⟩
  · intro i hi m hm
    obtain ⟨h1, h2, h3⟩ := hK i hi
    have hx0 : 0 < y + i * s := by linarith
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hlo, hhi⟩ := mem_sliceTokens_facts hP
      (by positivity) (hR _ hx0) hm
    obtain ⟨-, hle⟩ := hstep _ h1 h2
    constructor
    · exact hlo
    · linarith
  · intro i hi
    obtain ⟨h1, h2, -⟩ := hK i hi
    exact hc _ h1 h2
  · intro m hm
    obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.1 hm
    have hi' := Finset.mem_range.1 hi
    obtain ⟨h1, h2, h3⟩ := hK i hi'
    have hx0 : 0 < y + i * s := by linarith
    obtain ⟨h0, hle⟩ := hstep _ h1 h2
    refine sliceTokens_subset_bandTokens hP (by positivity) (hR _ hx0) hy.le h1 ?_ hz₀ hz ?_ hmi
    · linarith
    · refine hT.trans ?_
      have : Real.sqrt (y / P) ≤ Real.sqrt ((y + i * s) / P) :=
        Real.sqrt_le_sqrt (div_le_div_of_nonneg_right h1 hP.le)
      linarith

/-- A prime in two dyadic ranges `(2^k, 2^{k+1}]` and `(2^{k'}, 2^{k'+1}]` forces `k = k'`. -/
theorem zpow_two_eq_of_mem {k k' : ℤ} {p : ℝ} (h1 : (2 : ℝ) ^ k < p) (h2 : p ≤ 2 * (2 : ℝ) ^ k)
    (h1' : (2 : ℝ) ^ k' < p) (h2' : p ≤ 2 * (2 : ℝ) ^ k') : k = k' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ k' := zpow_le_zpow_right₀ (by norm_num) h
    rw [zpow_add_one₀ (by norm_num)] at this
    linarith
  · have : (2 : ℝ) ^ (k' + 1) ≤ (2 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) h
    rw [zpow_add_one₀ (by norm_num)] at this
    linarith

/-- **Distinct slices give distinct tokens.**  A token's prime factor below `2B` determines its
dyadic slice, when all slices lie below `B` and `2B < √(y/B)/2`. -/
theorem sliceWindowTokens_disjoint {k k' : ℤ} {y H s s' B : ℝ} (hkk : k ≠ k') (hy : 0 < y)
    (hs : 0 < s) (hs' : 0 < s') (hk : (2 : ℝ) ^ k ≤ B) (hk' : (2 : ℝ) ^ k' ≤ B)
    (hB : 2 * B < Real.sqrt (y / B) / 2) :
    Disjoint (sliceWindowTokens ((2 : ℝ) ^ k) y H s) (sliceWindowTokens ((2 : ℝ) ^ k') y H s') := by
  classical
  rw [Finset.disjoint_left]
  intro m hm hm'
  have hP : (0 : ℝ) < 2 ^ k := zpow_pos (by norm_num) k
  have hP' : (0 : ℝ) < 2 ^ k' := zpow_pos (by norm_num) k'
  have hB0 : 0 < B := lt_of_lt_of_le hP hk
  have hR : ∀ x P : ℝ, 0 < x → 0 < P → 4 * P * (Real.sqrt (x / P) / 2) ^ 2 = x := by
    intro x P hx hP
    rw [div_pow, Real.sq_sqrt (by positivity)]; field_simp; ring
  have hRmin : ∀ (x P : ℝ), y ≤ x → 0 < P → P ≤ B → Real.sqrt (y / B) / 2 ≤ Real.sqrt (x / P) / 2 := by
    intro x P hx hP hPB
    have : y / B ≤ x / P := div_le_div₀ (by linarith) hx hP hPB
    have := Real.sqrt_le_sqrt this
    linarith
  obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.1 hm
  obtain ⟨i', hi', hmi'⟩ := Finset.mem_biUnion.1 hm'
  have hx : y ≤ y + i * s := by have : (0 : ℝ) ≤ i := Nat.cast_nonneg _; nlinarith
  have hx' : y ≤ y + i' * s' := by have : (0 : ℝ) ≤ i' := Nat.cast_nonneg _; nlinarith
  obtain ⟨p₁, p₂, n, h₁, h₂, h₃, -, hp₁l, hp₁u, hp₂l, -, hnR, hm1, -, -⟩ :=
    mem_sliceTokens_facts hP (by positivity) (hR _ _ (by linarith) hP) hmi
  obtain ⟨p₁', p₂', n', h₁', h₂', h₃', -, hp₁l', hp₁u', hp₂l', -, hnR', hm1', -, -⟩ :=
    mem_sliceTokens_facts hP' (by positivity) (hR _ _ (by linarith) hP') hmi'
  have hR1 := hRmin _ _ hx hP hk
  have hR1' := hRmin _ _ hx' hP' hk'
  have lt : ∀ {a b : ℕ}, (a : ℝ) ≤ 2 * B → Real.sqrt (y / B) / 2 < b → a < b := by
    intro a b ha hb
    exact_mod_cast (show (a : ℝ) < b by linarith)
  have hsm : (p₁ : ℝ) ≤ 2 * B := by linarith
  have hsm' : (p₁' : ℝ) ≤ 2 * B := by linarith
  obtain ⟨e1, -⟩ := threePrime_eq_of_mul_eq h₁ h₂ h₁' h₂' h₃' (lt hsm (by linarith))
    (lt hsm (by linarith)) (lt hsm' (by linarith)) (lt hsm' (by linarith)) (hm1.symm.trans hm1')
  subst e1
  exact hkk (zpow_two_eq_of_mem hp₁l hp₁u hp₁l' hp₁u')

/-- **One slice's share.**  With `L = log y ≥ 14`, `2 ≤ P ≤ L^{11/10}/4`, `H = √y L^{31/20}`,
`s = √(2yP) log 2y` and `c = √(yP) L/(72000 log P (log 2y)²)`: `s ≤ H` and
`⌊H/s⌋ c ≥ H/(300000 log L · L²)`. -/
theorem slice_share_ge {y P : ℝ} (hy : 1 < y) (hL : 14 ≤ Real.log y) (hP2 : 2 ≤ P)
    (hPB : P ≤ Real.log y ^ (11 / 10 : ℝ) / 4) :
    Real.sqrt (2 * y * P) * Real.log (2 * y) ≤ Real.sqrt y * Real.log y ^ (31 / 20 : ℝ) ∧
      Real.sqrt y * Real.log y ^ (31 / 20 : ℝ) / (300000 * Real.log (Real.log y) * Real.log y ^ 2) ≤
        (⌊Real.sqrt y * Real.log y ^ (31 / 20 : ℝ) / (Real.sqrt (2 * y * P) * Real.log (2 * y))⌋₊ : ℝ) *
          (Real.sqrt (y * P) * Real.log y /
            (72000 * Real.log P * Real.log (2 * y) ^ 2)) := by
  have hy0 : 0 < y := by linarith
  have hL0 : 0 < Real.log y := by linarith
  have hP0 : 0 < P := by linarith
  generalize hLg : Real.log y = L at *
  have hl2 : Real.log (2 * y) = Real.log 2 + L := by rw [Real.log_mul (by norm_num) hy0.ne', hLg]
  have hlog2 := Real.log_two_lt_d9
  have hlog2' := Real.log_two_gt_d9
  have h2y : Real.log (2 * y) ≤ 21 / 20 * L := by rw [hl2]; linarith
  have h2y0 : 0 < Real.log (2 * y) := by rw [hl2]; linarith
  have hLP : L ^ (11 / 10 : ℝ) = L ^ (11 / 20 : ℝ) * L ^ (11 / 20 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  have hL31 : L ^ (31 / 20 : ℝ) = L ^ (11 / 20 : ℝ) * L := by
    rw [show (31 / 20 : ℝ) = 11 / 20 + 1 by norm_num, Real.rpow_add hL0, Real.rpow_one]
  have hLa : 0 < L ^ (11 / 20 : ℝ) := by positivity
  have hsP : Real.sqrt P ≤ L ^ (11 / 20 : ℝ) / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    calc P ≤ L ^ (11 / 10 : ℝ) / 4 := hPB
      _ = (L ^ (11 / 20 : ℝ) / 2) ^ 2 := by rw [hLP]; ring
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hsP0 : 0 < Real.sqrt P := Real.sqrt_pos.2 hP0
  have hs_eq : Real.sqrt (2 * y * P) = Real.sqrt 2 * Real.sqrt y * Real.sqrt P := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
  have hsqrt2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hsqrt2' : 0 < Real.sqrt 2 := by positivity
  set H := Real.sqrt y * L ^ (31 / 20 : ℝ) with hHdef
  set s := Real.sqrt (2 * y * P) * Real.log (2 * y) with hsdef
  have hs0 : 0 < s := by rw [hsdef]; positivity
  have hH0 : 0 < H := by rw [hHdef]; positivity
  have hsH : s ≤ H := by
    calc s = Real.sqrt 2 * Real.sqrt y * Real.sqrt P * Real.log (2 * y) := by rw [hsdef, hs_eq]
      _ ≤ (3 / 2) * Real.sqrt y * (L ^ (11 / 20 : ℝ) / 2) * (21 / 20 * L) := by gcongr
      _ = 63 / 80 * (Real.sqrt y * (L ^ (11 / 20 : ℝ) * L)) := by ring
      _ ≤ Real.sqrt y * (L ^ (11 / 20 : ℝ) * L) := by
          have : 0 ≤ Real.sqrt y * (L ^ (11 / 20 : ℝ) * L) := by positivity
          linarith
      _ = H := by rw [hHdef, hL31]
  refine ⟨hsH, ?_⟩
  have hHs1 : 1 ≤ H / s := by rw [le_div_iff₀ hs0]; linarith
  have hfl : H / (2 * s) ≤ (⌊H / s⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (H / s)
    have h1 : (1 : ℝ) ≤ ⌊H / s⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hHs1)
    have e : H / (2 * s) = H / s / 2 := by field_simp
    rw [e]; linarith
  have hlogP : Real.log P ≤ 11 / 10 * Real.log L := by
    have h1 := Real.log_le_log hP0 hPB
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hL0] at h1
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  have hlogP0 : 0 < Real.log P := Real.log_pos (by linarith)
  have hlL : 0 < Real.log L := Real.log_pos (by linarith)
  set c := Real.sqrt (y * P) * L / (72000 * Real.log P * Real.log (2 * y) ^ 2) with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  set D := 2 * Real.sqrt 2 * 72000 * Real.log P * Real.log (2 * y) ^ 3 with hDdef
  have hD0 : 0 < D := by rw [hDdef]; positivity
  have hshare : H / (2 * s) * c = H * L / D := by
    rw [hcdef, hDdef, hsdef, hs_eq, Real.sqrt_mul hy0.le]
    field_simp
  have hden : D ≤ 300000 * Real.log L * L ^ 2 * L := by
    have h1 : Real.log (2 * y) ^ 3 ≤ (21 / 20 * L) ^ 3 := pow_le_pow_left₀ h2y0.le h2y 3
    calc D ≤ 2 * (3 / 2) * 72000 * (11 / 10 * Real.log L) * (21 / 20 * L) ^ 3 := by
          rw [hDdef]; gcongr
      _ = 3 * 72000 * (11 / 10) * (21 / 20) ^ 3 * (Real.log L * L ^ 3) := by ring
      _ ≤ 300000 * (Real.log L * L ^ 3) := by
          have : 0 ≤ Real.log L * L ^ 3 := by positivity
          nlinarith
      _ = 300000 * Real.log L * L ^ 2 * L := by ring
  calc H / (300000 * Real.log L * L ^ 2) = H * L / (300000 * Real.log L * L ^ 2 * L) := by
        field_simp
    _ ≤ H * L / D := div_le_div_of_nonneg_left (by positivity) hD0 hden
    _ = H / (2 * s) * c := hshare.symm
    _ ≤ (⌊H / s⌋₊ : ℝ) * c := mul_le_mul_of_nonneg_right hfl hc0
/-- The dyadic slices `2^k ∈ [(log 2y)^{1.0999}, (log y)^{1.1}/4]` number at least
`log log y/20000` once `log log y ≥ 60000`. -/
theorem card_dyadic_band_ge {y : ℝ} (hy0 : 0 < y) (hL : 14 ≤ Real.log y)
    (hLL : 60000 ≤ Real.log (Real.log y)) :
    Real.log (Real.log y) / 20000 ≤
      ((Finset.Icc ⌈Real.log (Real.log (2 * y) ^ (10999 / 10000 : ℝ)) / Real.log 2⌉
        ⌊Real.log (Real.log y ^ (11 / 10 : ℝ) / 4) / Real.log 2⌋).card : ℝ) := by
  set L := Real.log y with hLdef
  have hL0 : 0 < L := by linarith
  have hl2 : Real.log (2 * y) = Real.log 2 + L := by rw [Real.log_mul (by norm_num) hy0.ne']
  have hlog2 := Real.log_two_lt_d9
  have hlog2' := Real.log_two_gt_d9
  have h2y : Real.log (2 * y) ≤ 21 / 20 * L := by rw [hl2]; linarith
  have h2y0 : 0 < Real.log (2 * y) := by rw [hl2]; linarith
  have hA : Real.log (Real.log (2 * y) ^ (10999 / 10000 : ℝ)) ≤
      10999 / 10000 * (Real.log L + 1 / 20) := by
    rw [Real.log_rpow h2y0]
    have h1 : Real.log (Real.log (2 * y)) ≤ Real.log (21 / 20 * L) := Real.log_le_log h2y0 h2y
    rw [Real.log_mul (by norm_num) hL0.ne'] at h1
    have h2 : Real.log (21 / 20 : ℝ) ≤ 1 / 20 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 21 / 20 by norm_num); linarith
    nlinarith
  have hB : Real.log (L ^ (11 / 10 : ℝ) / 4) = 11 / 10 * Real.log L - Real.log 4 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hL0]
  have h4 : Real.log 4 < 3 / 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hcard := CofactorParity.le_card_dyadicSlices (A := Real.log (2 * y) ^ (10999 / 10000 : ℝ))
    (B := L ^ (11 / 10 : ℝ) / 4)
  have hdiff : Real.log (L ^ (11 / 10 : ℝ) / 4) - Real.log (Real.log (2 * y) ^ (10999 / 10000 : ℝ))
      ≥ Real.log L / 10000 - 2 := by
    rw [hB]; nlinarith
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : (Real.log L / 10000 - 2) / Real.log 2 - 1 ≥ Real.log L / 20000 := by
    rw [ge_iff_le, le_sub_iff_add_le, le_div_iff₀ hl2pos]
    nlinarith
  have hmono : (Real.log L / 10000 - 2) / Real.log 2 ≤ (Real.log (L ^ (11 / 10 : ℝ) / 4) -
      Real.log (Real.log (2 * y) ^ (10999 / 10000 : ℝ))) / Real.log 2 :=
    div_le_div_of_nonneg_right hdiff hl2pos.le
  linarith

/-- **One slice's contribution to the band tokens.**  For a slice `P` with
`(log 2y)^{1.0999} ≤ P ≤ (log y)^{1.1}/4`, the natural windows across `(y, y + H]`,
`H = √y (log y)^{31/20} ≤ y`, give at least `H/(300000 log log y · (log y)²)` band tokens. -/
theorem slice_union_facts {y x₀ P : ℝ} {z₀ z T : ℕ}
    (hslice : ∀ x, x₀ ≤ x → ∀ P : ℝ, Real.log x ^ (10999 / 10000 : ℝ) ≤ P →
      P ≤ Real.log x ^ (11 / 10 : ℝ) →
      Real.sqrt (x * P) * Real.log x / (72000 * Real.log P * Real.log x ^ 2) ≤
        ((sliceTokens ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime)
          ((Finset.Ioc ⌊Real.sqrt (x / P) / 2⌋₊ ⌊2 * (Real.sqrt (x / P) / 2)⌋₊).filter Nat.Prime) x
          (Real.sqrt (x * P) * Real.log x)).card : ℝ))
    (hy : x₀ ≤ y) (hy1 : 1 < y) (hL : 14 ≤ Real.log y)
    (hHy : Real.sqrt y * Real.log y ^ (31 / 20 : ℝ) ≤ y)
    (hPA : Real.log (2 * y) ^ (10999 / 10000 : ℝ) ≤ P) (hPB : P ≤ Real.log y ^ (11 / 10 : ℝ) / 4)
    (hz₀ : (z₀ : ℝ) ≤ Real.log (2 * y) ^ (10999 / 10000 : ℝ))
    (hz : Real.log y ^ (11 / 10 : ℝ) / 2 ≤ z) (hT : (T : ℝ) ≤ Real.sqrt y / Real.log y ^ 2) :
    Real.sqrt y * Real.log y ^ (31 / 20 : ℝ) / (300000 * Real.log (Real.log y) * Real.log y ^ 2) ≤
        ((sliceWindowTokens P y (Real.sqrt y * Real.log y ^ (31 / 20 : ℝ))
          (Real.sqrt (2 * y * P) * Real.log (2 * y))).card : ℝ) ∧
      sliceWindowTokens P y (Real.sqrt y * Real.log y ^ (31 / 20 : ℝ))
          (Real.sqrt (2 * y * P) * Real.log (2 * y)) ⊆
        bandTokens z₀ z T y (Real.sqrt y * Real.log y ^ (31 / 20 : ℝ)) := by
  have hy0 : 0 < y := by linarith
  have hL0 : 0 < Real.log y := by linarith
  have hl2 : Real.log (2 * y) = Real.log 2 + Real.log y := Real.log_mul (by norm_num) hy0.ne'
  have hlog2 := Real.log_two_gt_d9
  have h2y0 : 1 < Real.log (2 * y) := by rw [hl2]; linarith
  have hA2 : 2 ≤ Real.log (2 * y) ^ (10999 / 10000 : ℝ) := by
    have h1 : Real.log (2 * y) ^ (1 : ℝ) ≤ Real.log (2 * y) ^ (10999 / 10000 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h2y0.le (by norm_num)
    rw [Real.rpow_one] at h1
    rw [hl2] at h1 ⊢; linarith
  have hP2 : 2 ≤ P := hA2.trans hPA
  have hP0 : 0 < P := by linarith
  obtain ⟨hsH, hshare⟩ := slice_share_ge hy1 hL hP2 hPB
  have hwin := sliceWindowTokens_facts (z₀ := z₀) (z := z) (T := T) (P := P) (y := y)
    (H := Real.sqrt y * Real.log y ^ (31 / 20 : ℝ)) (s := Real.sqrt (2 * y * P) * Real.log (2 * y))
    (c := Real.sqrt (y * P) * Real.log y / (72000 * Real.log P * Real.log (2 * y) ^ 2)) hP0 hy0
    (by positivity) ?_ ?_ (hz₀.trans hPA) (by linarith) ?_
  · exact ⟨hshare.trans hwin.1, hwin.2⟩
  · -- the slice count at each window start
    intro x hx1 hx2
    have hx2y : x ≤ 2 * y := by linarith
    have hx0 : 0 < x := by linarith
    have hlx : Real.log y ≤ Real.log x := Real.log_le_log hy0 hx1
    have hlx2 : Real.log x ≤ Real.log (2 * y) := Real.log_le_log hx0 hx2y
    have hlx0 : 0 < Real.log x := by linarith
    have hPlo : Real.log x ^ (10999 / 10000 : ℝ) ≤ P :=
      (Real.rpow_le_rpow hlx0.le hlx2 (by norm_num)).trans hPA
    have hPhi : P ≤ Real.log x ^ (11 / 10 : ℝ) := by
      refine hPB.trans ?_
      have := Real.rpow_le_rpow hL0.le hlx (by norm_num : (0 : ℝ) ≤ 11 / 10)
      have h0 : 0 ≤ Real.log y ^ (11 / 10 : ℝ) := by positivity
      linarith
    refine le_trans ?_ (hslice x (hy.trans hx1) P hPlo hPhi)
    have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
    have hnum : Real.sqrt (y * P) * Real.log y ≤ Real.sqrt (x * P) * Real.log x :=
      mul_le_mul (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hx1 hP0.le)) hlx hL0.le
        (Real.sqrt_nonneg _)
    have hden : 72000 * Real.log P * Real.log x ^ 2 ≤ 72000 * Real.log P * Real.log (2 * y) ^ 2 := by
      gcongr
    calc Real.sqrt (y * P) * Real.log y / (72000 * Real.log P * Real.log (2 * y) ^ 2)
        ≤ Real.sqrt (x * P) * Real.log x / (72000 * Real.log P * Real.log (2 * y) ^ 2) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ Real.sqrt (x * P) * Real.log x / (72000 * Real.log P * Real.log x ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  · intro x hx1 hx2
    have hx2y : x ≤ 2 * y := by linarith
    have hx0 : 0 < x := by linarith
    have hlx2 : Real.log x ≤ Real.log (2 * y) := Real.log_le_log hx0 hx2y
    have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    refine ⟨by positivity, mul_le_mul (Real.sqrt_le_sqrt ?_) hlx2 hlx0 (Real.sqrt_nonneg _)⟩
    nlinarith
  · -- `T ≤ √y/L² ≤ √(y/B)/2 ≤ √(y/P)/2`
    refine hT.trans ?_
    have hB0 : 0 < Real.log y ^ (11 / 10 : ℝ) / 4 := by positivity
    have h1 : Real.sqrt (y / (Real.log y ^ (11 / 10 : ℝ) / 4)) ≤ Real.sqrt (y / P) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hy0.le hP0 hPB)
    have h2 : Real.sqrt (y / (Real.log y ^ (11 / 10 : ℝ) / 4)) =
        2 * Real.sqrt y / Real.log y ^ (11 / 20 : ℝ) := by
      rw [Real.sqrt_div hy0.le, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
        Real.sqrt_eq_rpow (Real.log y ^ (11 / 10 : ℝ)), ← Real.rpow_mul hL0.le]
      rw [show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      norm_num
      field_simp
    have h3 : Real.log y ^ (11 / 20 : ℝ) ≤ Real.log y ^ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ Real.log y)
        (by norm_num : (11 / 20 : ℝ) ≤ 2)
      rwa [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    have h4 : Real.sqrt y / Real.log y ^ 2 ≤ Real.sqrt y / Real.log y ^ (11 / 20 : ℝ) :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) h3
    rw [h2] at h1
    have h5 : Real.sqrt y / Real.log y ^ (11 / 20 : ℝ) = (2 * Real.sqrt y / Real.log y ^ (11 / 20 : ℝ)) / 2 := by
      ring
    linarith

/-- **The row supply `(6b)` at one `y`.**  Summing the slice contributions over the
`≥ log log y/20000` dyadic slices in `[(log 2y)^{1.0999}, (log y)^{1.1}/4]` — whose tokens are
disjoint, a token's small prime fixing its slice — gives at least `H/(6·10⁹ (log y)²)` band tokens
in `(y, y + H]`, `H = √y (log y)^{31/20}`. -/
theorem card_bandTokens_ge_of {y x₀ : ℝ} {z₀ z T : ℕ}
    (hslice : ∀ x, x₀ ≤ x → ∀ P : ℝ, Real.log x ^ (10999 / 10000 : ℝ) ≤ P →
      P ≤ Real.log x ^ (11 / 10 : ℝ) →
      Real.sqrt (x * P) * Real.log x / (72000 * Real.log P * Real.log x ^ 2) ≤
        ((sliceTokens ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime)
          ((Finset.Ioc ⌊Real.sqrt (x / P) / 2⌋₊ ⌊2 * (Real.sqrt (x / P) / 2)⌋₊).filter Nat.Prime) x
          (Real.sqrt (x * P) * Real.log x)).card : ℝ))
    (hy : x₀ ≤ y) (hy1 : 1 < y) (hL : 14 ≤ Real.log y) (hLL : 60000 ≤ Real.log (Real.log y))
    (hHy : Real.sqrt y * Real.log y ^ (31 / 20 : ℝ) ≤ y)
    (hBR : 2 * (Real.log y ^ (11 / 10 : ℝ) / 4) <
      Real.sqrt (y / (Real.log y ^ (11 / 10 : ℝ) / 4)) / 2)
    (hz₀ : (z₀ : ℝ) ≤ Real.log (2 * y) ^ (10999 / 10000 : ℝ))
    (hz : Real.log y ^ (11 / 10 : ℝ) / 2 ≤ z) (hT : (T : ℝ) ≤ Real.sqrt y / Real.log y ^ 2) :
    Real.sqrt y * Real.log y ^ (31 / 20 : ℝ) / (6 * 10 ^ 9 * Real.log y ^ 2) ≤
      ((bandTokens z₀ z T y (Real.sqrt y * Real.log y ^ (31 / 20 : ℝ))).card : ℝ) := by
  classical
  have hy0 : 0 < y := by linarith
  have hL0 : 0 < Real.log y := by linarith
  set H := Real.sqrt y * Real.log y ^ (31 / 20 : ℝ) with hHdef
  set A := Real.log (2 * y) ^ (10999 / 10000 : ℝ) with hAdef
  set B := Real.log y ^ (11 / 10 : ℝ) / 4 with hBdef
  have hl2 : Real.log (2 * y) = Real.log 2 + Real.log y := Real.log_mul (by norm_num) hy0.ne'
  have hlog2 := Real.log_two_gt_d9
  have hA0 : 0 < A := by
    have : 0 < Real.log (2 * y) := by rw [hl2]; linarith
    positivity
  have hB0 : 0 < B := by positivity
  set J := Finset.Icc ⌈Real.log A / Real.log 2⌉ ⌊Real.log B / Real.log 2⌋ with hJdef
  have hJmem : ∀ k ∈ J, A ≤ (2 : ℝ) ^ k ∧ (2 : ℝ) ^ k ≤ B := fun k hk =>
    (CofactorParity.dyadic_mem_iff hA0 hB0 k).2 ((CofactorParity.mem_dyadicSlices k).1 hk)
  set U : ℤ → Finset ℕ := fun k => sliceWindowTokens ((2 : ℝ) ^ k) y H
    (Real.sqrt (2 * y * (2 : ℝ) ^ k) * Real.log (2 * y)) with hUdef
  have hUk : ∀ k ∈ J, H / (300000 * Real.log (Real.log y) * Real.log y ^ 2) ≤ ((U k).card : ℝ) ∧
      U k ⊆ bandTokens z₀ z T y H := fun k hk =>
    slice_union_facts hslice hy hy1 hL hHy (hJmem k hk).1 (hJmem k hk).2 hz₀ hz hT
  have hdisj : Set.PairwiseDisjoint (↑J : Set ℤ) U := by
    intro k hk k' hk' hkk
    have hs : 0 < Real.sqrt (2 * y * (2 : ℝ) ^ k) * Real.log (2 * y) := by
      have : 0 < Real.log (2 * y) := by rw [hl2]; linarith
      have : (0 : ℝ) < 2 ^ k := zpow_pos (by norm_num) k
      positivity
    have hs' : 0 < Real.sqrt (2 * y * (2 : ℝ) ^ k') * Real.log (2 * y) := by
      have : 0 < Real.log (2 * y) := by rw [hl2]; linarith
      have : (0 : ℝ) < 2 ^ k' := zpow_pos (by norm_num) k'
      positivity
    exact sliceWindowTokens_disjoint hkk hy0 hs hs' (hJmem k hk).2 (hJmem k' hk').2 hBR
  have hsub : J.biUnion U ⊆ bandTokens z₀ z T y H := by
    intro m hm
    obtain ⟨k, hk, hmk⟩ := Finset.mem_biUnion.1 hm
    exact (hUk k hk).2 hmk
  have hcardJ := card_dyadic_band_ge hy0 hL hLL
  have hlL : 0 < Real.log (Real.log y) := by linarith
  calc H / (6 * 10 ^ 9 * Real.log y ^ 2)
      = Real.log (Real.log y) / 20000 * (H / (300000 * Real.log (Real.log y) * Real.log y ^ 2)) := by
        field_simp; ring
    _ ≤ (J.card : ℝ) * (H / (300000 * Real.log (Real.log y) * Real.log y ^ 2)) :=
        mul_le_mul_of_nonneg_right hcardJ (by positivity)
    _ = ∑ _k ∈ J, H / (300000 * Real.log (Real.log y) * Real.log y ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ J, ((U k).card : ℝ) := Finset.sum_le_sum fun k hk => (hUk k hk).1
    _ = ((J.biUnion U).card : ℝ) := by rw [Finset.card_biUnion hdisj]; push_cast; rfl
    _ ≤ ((bandTokens z₀ z T y H).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub

/-- **The row supply `(6b)`.**  Assume `(E1)` and `(E2)`.  For all large `y`, every band `[z₀, z]`
containing `[(log 2y)^{1.0999}, (log y)^{1.1}/2]` and every threshold `T ≤ √y/(log y)²`, the
interval `(y, y + √y (log y)^{31/20}]` contains at least `√y (log y)^{31/20}/(6·10⁹ (log y)²)`
distinct `E₃` numbers `p₁p₂n` with `p₁` in the band and `p₂ ≠ n` primes above `T`. -/
theorem eventually_card_bandTokens_ge (hDI : MTDeshouillersIwaniecBound) (hW : MTWattBound) :
    ∀ᶠ y : ℝ in atTop, ∀ z₀ z T : ℕ, (z₀ : ℝ) ≤ Real.log (2 * y) ^ (10999 / 10000 : ℝ) →
      Real.log y ^ (11 / 10 : ℝ) / 2 ≤ z → (T : ℝ) ≤ Real.sqrt y / Real.log y ^ 2 →
      Real.sqrt y * Real.log y ^ (31 / 20 : ℝ) / (6 * 10 ^ 9 * Real.log y ^ 2) ≤
        ((bandTokens z₀ z T y (Real.sqrt y * Real.log y ^ (31 / 20 : ℝ))).card : ℝ) := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (eventually_card_sliceTokens_ge hDI hW)
  filter_upwards [eventually_ge_atTop (max x₀ 2), Real.tendsto_log_atTop.eventually_ge_atTop 14,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 60000,
    eventually_polylog_le_rpow 2 (C := 1) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2)]
    with y hy hL hLL hpoly
  intro z₀ z T hz₀ hz hT
  have hy1 : 1 < y := by linarith [le_max_right x₀ 2]
  have hy0 : 0 < y := by linarith
  have hL0 : 0 < Real.log y := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log y := by linarith
  have hle : Real.log y ≤ 1 + Real.log (24 * y) := by
    rw [Real.log_mul (by norm_num) hy0.ne']
    have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
    linarith
  have hL2 : Real.log y ^ 2 ≤ Real.sqrt y := by
    rw [Real.sqrt_eq_rpow]
    have := pow_le_pow_left₀ hL0.le hle 2
    linarith
  have hpow : ∀ r : ℝ, r ≤ 2 → Real.log y ^ r ≤ Real.log y ^ 2 := fun r hr => by
    have := Real.rpow_le_rpow_of_exponent_le hL1 hr
    rwa [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  have hHy : Real.sqrt y * Real.log y ^ (31 / 20 : ℝ) ≤ y := by
    have h1 := hpow (31 / 20) (by norm_num)
    have hs : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
    calc Real.sqrt y * Real.log y ^ (31 / 20 : ℝ) ≤ Real.sqrt y * Real.sqrt y :=
          mul_le_mul_of_nonneg_left (h1.trans hL2) (Real.sqrt_nonneg _)
      _ = y := hs
  have hBR : 2 * (Real.log y ^ (11 / 10 : ℝ) / 4) <
      Real.sqrt (y / (Real.log y ^ (11 / 10 : ℝ) / 4)) / 2 := by
    have e : Real.sqrt (y / (Real.log y ^ (11 / 10 : ℝ) / 4)) =
        2 * Real.sqrt y / Real.log y ^ (11 / 20 : ℝ) := by
      rw [Real.sqrt_div hy0.le, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
        Real.sqrt_eq_rpow (Real.log y ^ (11 / 10 : ℝ)), ← Real.rpow_mul hL0.le]
      rw [show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      norm_num
      field_simp
    rw [e]
    have hLa : 0 < Real.log y ^ (11 / 20 : ℝ) := by positivity
    rw [lt_div_iff₀ (by norm_num), ← mul_div_assoc, lt_div_iff₀ hLa]
    have e2 : Real.log y ^ (11 / 10 : ℝ) * Real.log y ^ (11 / 20 : ℝ) = Real.log y ^ (33 / 20 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    have h3 := hpow (33 / 20) (by norm_num)
    have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
    nlinarith
  exact card_bandTokens_ge_of (fun x hx P h1 h2 => hx₀ x hx P h1 h2) (le_trans (le_max_left _ _) hy)
    hy1 hL hLL hHy hBR hz₀ hz hT

end

end RHTower.Sieve
