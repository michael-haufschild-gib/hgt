import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheCoefficientMassOfAProducer
import GaloisForLFunctions.RHTower.CenteredFractCorrelation

/-!
# The carry of the floor

Over `𝔽_q[T]` the count of monic polynomials obeys `N(q x) = q N(x) + 1`: multiplication by `q` is an exact
self-similarity of the count, and this is what Frobenius does to a stencil. Over `ℤ` the same comparison has a
remainder:

`⌊k x⌋ − k ⌊x⌋ = ⌊k {x}⌋ = Σ_{j<k} (⌊x + j/k⌋ − ⌊x⌋)`.

This is the **carry**. It takes every value in `[0, k)`, so it is not constant for any `k ≥ 2`, and it is exactly a
sum of additive shifts: over `ℤ` a dilation of the count is an average over translations. All multiplicity of a
stencil lives in carries.

**A self-similar count is quantized.** If a count with integer norms obeys `N(k x) = k N(x) + C` for all
`x ≥ 1`, then `a` vanishes off the multiples of `k` beyond `k`, and `a(k n) = k a(n)` for `n ≥ 2`. Its support lies in
finitely many geometric progressions `k^i n₀`, with `n₀ ≤ k`, and its multiplicities grow like `k^i`. So a count
with bounded multiplicities has no Frobenius. This is the exact sense in which quantized norms and Frobenius
are one property.

**Every integer is a cut.** A stencil with `c(1) ≠ 0` jumps at every `r` prime to its period, a set of density
`φ(L)/L`, against a logarithmically sparse set under quantization. So nothing linear removes the sawtooth.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-! ### The carry -/

/-- **The carry.** `⌊k x⌋ − k ⌊x⌋ = ⌊k {x}⌋`. -/
theorem floor_mul_sub_mul_floor (k : ℕ) (x : ℝ) :
    ⌊(k : ℝ) * x⌋ - (k : ℤ) * ⌊x⌋ = ⌊(k : ℝ) * Int.fract x⌋ := by
  have hx : (k : ℝ) * x = (((k : ℤ) * ⌊x⌋ : ℤ) : ℝ) + (k : ℝ) * Int.fract x := by
    have := Int.floor_add_fract x
    push_cast
    nth_rewrite 1 [← this]
    ring
  rw [hx, Int.floor_intCast_add]
  ring

/-- The carry lies in `[0, k)`. -/
theorem carry_mem {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    0 ≤ ⌊(k : ℝ) * Int.fract x⌋ ∧ ⌊(k : ℝ) * Int.fract x⌋ < (k : ℤ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · exact Int.floor_nonneg.mpr (mul_nonneg hk0.le (Int.fract_nonneg x))
  · refine Int.floor_lt.mpr ?_
    push_cast
    calc (k : ℝ) * Int.fract x < (k : ℝ) * 1 := mul_lt_mul_of_pos_left (Int.fract_lt_one x) hk0
      _ = k := mul_one _

/-- The carry takes every value in `[0, k)`. -/
theorem carry_at_div {k j : ℕ} (hj : j < k) :
    ⌊(k : ℝ) * ((j : ℝ) / k)⌋ - (k : ℤ) * ⌊(j : ℝ) / k⌋ = j := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have h1 : (k : ℝ) * ((j : ℝ) / k) = j := by field_simp
  have h2 : ⌊(j : ℝ) / k⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one hk0]
    exact_mod_cast hj
  rw [h1, h2, Int.floor_natCast]
  ring

/-- **Over `ℤ` the carry is not constant.** No `k ≥ 2` acts on `⌊·⌋` by a Frobenius. -/
theorem not_exists_constant_carry {k : ℕ} (hk : 2 ≤ k) :
    ¬ ∃ C : ℤ, ∀ x : ℝ, ⌊(k : ℝ) * x⌋ = (k : ℤ) * ⌊x⌋ + C := by
  rintro ⟨C, hC⟩
  have h0 := carry_at_div (k := k) (j := 0) (by omega)
  have h1 := carry_at_div (k := k) (j := 1) (by omega)
  have e0 := hC (((0 : ℕ) : ℝ) / k)
  have e1 := hC (((1 : ℕ) : ℝ) / k)
  rw [e0] at h0
  rw [e1] at h1
  simp only [add_sub_cancel_left] at h0 h1
  omega

/-- **The carry is a sum of additive shifts.** Over `ℤ` a dilation of the count is an average over
translations. -/
theorem carry_eq_sum_shifts {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    ⌊(k : ℝ) * x⌋ - (k : ℤ) * ⌊x⌋ = ∑ j ∈ range k, (⌊x + (j : ℝ) / k⌋ - ⌊x⌋) := by
  rw [sum_sub_distrib, RHTower.sum_floor_add_div_eq_floor_mul hk x]
  simp

/-! ### A self-similar count is quantized -/

/-- The count of a multiplicity function with integer norms. -/
def countOf (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, a n

theorem countOf_natCast (a : ℕ → ℝ) (n : ℕ) : countOf a n = ∑ m ∈ Ioc 0 n, a m := by
  rw [countOf, Nat.floor_natCast]

/-- `a` has a Frobenius at `k`: `N(k x) = k N(x) + C` for all `x ≥ 1`. -/
def HasFrobenius (a : ℕ → ℝ) (k : ℕ) (C : ℝ) : Prop :=
  ∀ x : ℝ, 1 ≤ x → countOf a ((k : ℝ) * x) = (k : ℝ) * countOf a x + C

variable {a : ℕ → ℝ} {k : ℕ} {C : ℝ}

private lemma countOf_succ_sub (a : ℕ → ℝ) (m : ℕ) :
    countOf a ((m + 1 : ℕ) : ℝ) - countOf a (m : ℝ) = a (m + 1) := by
  rw [countOf_natCast, countOf_natCast, sum_Ioc_succ_top (Nat.zero_le m)]
  ring

/-- Off the multiples of `k`, the multiplicity vanishes beyond `k`. -/
theorem eq_zero_of_not_dvd (h : HasFrobenius a k C) (hk : 2 ≤ k) {m : ℕ} (hm : k < m)
    (hd : ¬ k ∣ m) : a m = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hx1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / k := by
    rw [le_div_iff₀ hk0, one_mul]
    exact_mod_cast hm.le
  have hx2 : (1 : ℝ) ≤ (n : ℝ) / k := by
    rw [le_div_iff₀ hk0, one_mul]
    exact_mod_cast (by omega : k ≤ n)
  have e1 := h _ hx1
  have e2 := h _ hx2
  rw [mul_div_cancel₀ _ hk0.ne'] at e1 e2
  have hfloor : ⌊((n + 1 : ℕ) : ℝ) / k⌋₊ = ⌊(n : ℝ) / k⌋₊ := by
    rw [Nat.floor_div_eq_div, Nat.floor_div_eq_div, Nat.succ_div, if_neg hd, add_zero]
  have hcount : countOf a (((n + 1 : ℕ) : ℝ) / k) = countOf a ((n : ℝ) / k) := by
    simp only [countOf, hfloor]
  have := countOf_succ_sub a n
  rw [e1, e2, hcount] at this
  linarith

/-- On the multiples of `k`, the multiplicity is multiplied by `k`. -/
theorem eq_mul_of_dvd (h : HasFrobenius a k C) (hk : 2 ≤ k) {n : ℕ} (hn : 2 ≤ n) :
    a (k * n) = k * a n := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpos : 1 ≤ k * n := Nat.mul_pos (by omega) (by omega)
  obtain ⟨M, hM⟩ : ∃ M, k * n = M + 1 := ⟨k * n - 1, by omega⟩
  have hkM : k ≤ M := by
    have : k * 2 ≤ k * n := Nat.mul_le_mul_left k hn
    omega
  have hx1 : (1 : ℝ) ≤ (M : ℝ) / k := by
    rw [le_div_iff₀ hk0, one_mul]
    exact_mod_cast hkM
  have e1 := h (n : ℝ) (by exact_mod_cast (by omega : 1 ≤ n))
  have e2 := h _ hx1
  rw [mul_div_cancel₀ _ hk0.ne'] at e2
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hfloor : ⌊(M : ℝ) / k⌋₊ = n' := by
    rw [Nat.floor_div_eq_div]
    have h1 : M = k * n' + (k - 1) := by
      rw [Nat.mul_succ] at hM
      omega
    rw [h1, Nat.mul_add_div (by omega : 0 < k), Nat.div_eq_of_lt (by omega), add_zero]
  have hcount : countOf a ((M : ℝ) / k) = countOf a (n' : ℝ) := by
    rw [countOf, hfloor, countOf_natCast]
  have hkn : (k : ℝ) * ((n' + 1 : ℕ) : ℝ) = ((M + 1 : ℕ) : ℝ) := by
    exact_mod_cast hM
  rw [hkn] at e1
  have h1 := countOf_succ_sub a M
  have h2 := countOf_succ_sub a n'
  rw [e1, e2, hcount] at h1
  rw [hM, ← h1, ← h2]
  ring

/-- **The support of a self-similar count lies in finitely many geometric progressions.** -/
theorem exists_pow_mul_of_ne_zero (h : HasFrobenius a k C) (hk : 2 ≤ k) {m : ℕ} (hm : 1 ≤ m)
    (ha : a m ≠ 0) : ∃ i n₀ : ℕ, 1 ≤ n₀ ∧ n₀ ≤ k ∧ m = k ^ i * n₀ := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hle : m ≤ k
    · exact ⟨0, m, hm, hle, by simp⟩
    · have hlt : k < m := not_le.mp hle
      by_cases hd : k ∣ m
      · obtain ⟨n, rfl⟩ := hd
        have hn2 : 2 ≤ n := by
          by_contra hn
          have : n ≤ 1 := by omega
          have : k * n ≤ k * 1 := Nat.mul_le_mul_left k this
          omega
        have hmul := eq_mul_of_dvd h hk hn2
        have han : a n ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hmul
          exact ha hmul
        have hnlt : n < k * n := by nlinarith
        obtain ⟨i, n₀, h1, h2, h3⟩ := ih n hnlt (by omega) han
        exact ⟨i + 1, n₀, h1, h2, by rw [h3, pow_succ]; ring⟩
      · exact absurd (eq_zero_of_not_dvd h hk hlt hd) ha

/-- **The support is logarithmically sparse.** -/
theorem card_support_le (h : HasFrobenius a k C) (hk : 2 ≤ k) (x : ℕ) :
    ((Ioc 0 x).filter fun m => a m ≠ 0).card ≤ (Nat.log k x + 1) * k := by
  classical
  have hsub : ((Ioc 0 x).filter fun m => a m ≠ 0) ⊆
      ((range (Nat.log k x + 1)) ×ˢ (Icc 1 k)).image fun y => k ^ y.1 * y.2 := by
    intro m hm
    obtain ⟨hI, ha⟩ := mem_filter.mp hm
    obtain ⟨h0, hx⟩ := mem_Ioc.mp hI
    obtain ⟨i, n₀, h1, h2, h3⟩ := exists_pow_mul_of_ne_zero h hk h0 ha
    refine mem_image.mpr ⟨(i, n₀), mem_product.mpr ⟨mem_range.mpr ?_, mem_Icc.mpr ⟨h1, h2⟩⟩, h3.symm⟩
    have hpow : k ^ i ≤ x := by
      calc k ^ i ≤ k ^ i * n₀ := Nat.le_mul_of_pos_right _ h1
        _ = m := h3.symm
        _ ≤ x := hx
    have hxpos : x ≠ 0 := by omega
    exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by omega) hpow)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_image_le
    _ = _ := by simp

/-- **Bounded multiplicities have no Frobenius.** A self-similar count has `a(k^i n) = k^i a(n)` for `n ≥ 2`, so a
nonzero multiplicity at `n ≥ 2` grows without bound along the orbit. -/
theorem not_hasFrobenius_of_bounded {A : ℝ} (hb : ∀ n, |a n| ≤ A) {n : ℕ} (hn : 2 ≤ n) (ha : a n ≠ 0)
    (hk : 2 ≤ k) : ¬ HasFrobenius a k C := by
  intro h
  have hpow : ∀ i, a (k ^ i * n) = (k : ℝ) ^ i * a n := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hn' : 2 ≤ k ^ i * n := hn.trans (Nat.le_mul_of_pos_left n (pow_pos (by omega) i))
      have h1 := eq_mul_of_dvd h hk hn'
      rw [show k ^ (i + 1) * n = k * (k ^ i * n) by ring, h1, ih, pow_succ]
      ring
  have hpos : 0 < |a n| := abs_pos.mpr ha
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (A / |a n|) hk1
  have h1 := hb (k ^ i * n)
  rw [hpow, abs_mul, abs_of_pos (pow_pos (by linarith) i)] at h1
  have h2 := (div_lt_iff₀ hpos).mp hi
  linarith

/-- The floor itself has no Frobenius, in the count form. -/
theorem not_hasFrobenius_one (hk : 2 ≤ k) : ¬ HasFrobenius (fun _ => 1) k C :=
  not_hasFrobenius_of_bounded (A := 1) (fun _ => by simp) (le_refl 2) one_ne_zero hk

/-! ### Every integer is a cut -/

open GaloisForLFunctions.ArithmeticAuxiliaryDynamics in
/-- **Every integer prime to the period is a cut.** A stencil with `c(1) ≠ 0` has a nonzero increment at each of
the `φ(L)` residues prime to its period `L` in a period. -/
theorem totient_le_card_cuts {c : ℕ →₀ ℤ} (h1 : c 1 ≠ 0) (hc0 : c 0 = 0) :
    Nat.totient (IsProducer.period c) ≤
      ((Ioc 0 (IsProducer.period c)).filter fun r => increment c r ≠ 0).card := by
  classical
  set L := IsProducer.period c with hL
  have hL0 : 0 < L := prod_pos fun k hk => Nat.pos_of_ne_zero fun h => by
    subst h
    exact Finsupp.mem_support_iff.mp hk hc0
  rw [Nat.totient_eq_card_coprime]
  have hL1 : ∀ r, r.Coprime L → IsRough c r := by
    intro r hr k hk hk1 hd
    have hdL : k ∣ L := IsProducer.dvd_period k hk
    have : k ∣ Nat.gcd r L := Nat.dvd_gcd hd hdL
    rw [hr] at this
    exact hk1 (Nat.dvd_one.mp this)
  refine card_le_card_of_injOn (fun r => if r = 0 then L else r) ?_ ?_
  · intro r hr
    have hr' : r < L ∧ L.Coprime r := by simpa using hr
    obtain ⟨hlt, hco⟩ := hr'
    by_cases h0 : r = 0
    · subst h0
      have hL11 : L = 1 := by simpa using hco
      simp only [if_true]
      refine mem_coe.mpr (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hL0, le_rfl⟩, ?_⟩)
      have : IsRough c L := hL1 L (by rw [hL11]; exact Nat.coprime_one_left 1)
      rw [increment_of_isRough this]
      exact h1
    · simp only [if_neg h0]
      refine mem_coe.mpr (mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h0, hlt.le⟩, ?_⟩)
      rw [increment_of_isRough (hL1 r hco.symm)]
      exact h1
  · intro r hr s hs he
    have hr' : r < L := (mem_coe.mp hr |> mem_filter.mp).1 |> mem_range.mp
    have hs' : s < L := (mem_coe.mp hs |> mem_filter.mp).1 |> mem_range.mp
    simp only at he
    split_ifs at he <;> omega

end GaloisForLFunctions.RigidArithmeticOfCuts
