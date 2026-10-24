import GaloisForLFunctions.ArithmeticIncidencePositivity.DyadicWindowIncidence

/-!
# Multi-scale coupling between dyadic windows

Mechanism 14 (`DyadicWindowIncidence`) classifies the arithmetic incidence inside a single dyadic
window `W(X) = (X/2, 2X)`: internal divisor relations are only `b = 2a` and `b = 3a`, internal
crossing prime-power pairs are only `(p^i, p^{i+1})` with `p ∈ {2, 3}`, and every internal crossing
atom is below `2 log 3 / X`.

This module resolves **Open Problem 5** ("Windows across scales") by giving the complete structural
and quantitative description of the coupling graph between two dyadic windows `W(X)` and `W(Y)` at
scales `0 < X ≤ Y`:

1. **Exact scale-suppression law (`productAtom_eq_ratioAtom_div_of_isPrimePow`,
   `productAtom_le_ratioAtom_div`).** Whenever `a < b` and `ab` is a prime power `p^{i+j}`, the
   factor `p^{2i} = a²` inside `√(p^{i+j}) = p^i √(p^{j−i})` yields the exact factorization
   `productAtom a b = ratioAtom a b / a`. For all `1 ≤ a < b`,
   `productAtom a b ≤ ratioAtom a b / a` and `(1 − 1/a) ratioAtom a b ≤ netAtom a b`. Consequently,
   on any support `S ⊆ [A, ∞)`, `productEnergy S c ≤ (1/A) ratioEnergy S c` and
   `skeletonEnergy S c ≥ (1 − 1/A) ratioEnergy S c`.
2. **The inter-window ratio coupling graph (`InRatioBand`, `inRatioBand_of_inDyadicWindows_dvd`).**
   A divisor relation `b = m a` between `a ∈ W(X)` and `b ∈ W(Y)` requires the multiplier `m` to lie
   in the open ratio band `Y / (4X) < m < 4Y / X`. Small multipliers decouple as the scales separate
   (`m ≥ 3` for `Y ≥ 8X`, `m ≥ 4` for `Y ≥ 12X`, `m ≥ 5` for `Y ≥ 16X`). Any two powers `p^i ≤ p^j`
   of one prime in `InRatioBand X Y` satisfy `p^{j−i} < 16`, so `j − i ≤ 3` for `p = 2`,
   `j − i ≤ 2` for `p = 3`, `j − i ≤ 1` for `5 ≤ p ≤ 13`, and `i = j` (at most one ratio edge per
   source) for every prime `p ≥ 17`. When `Y ≥ 4X`, every ratio atom between `W(X)` and `W(Y)`
   decays at the square-root scale-separation rate:
   `ratioAtom a b < 2 log(4Y/X) √(X/Y)` (`ratioAtom_lt_of_inDyadicWindows`).
3. **The inter-window crossing coupling graph (`exists_prime_pow_of_inDyadicWindows_isPrimePow_mul`,
   `unique_crossing_pair_of_five_le`, `productAtom_lt_of_inDyadicWindows_of_two_le`).** Every
   crossing edge between `W(X)` and `W(Y)` lies on a single prime-power tower `(p^i, p^j)`. When
   `X ≥ 2`, the prime base satisfies the horizon bound `p < 2X` (primes `p ≥ 2X` never create
   crossing edges out of `W(X)`), every prime `p ≥ 5` contributes at most one crossing edge between
   `W(X)` and `W(Y)`, and every crossing atom satisfies
   `productAtom a b < 2 log(2X) / √(XY)` as well as `productAtom a b ≤ (2/X) ratioAtom a b`.
4. **Partial-matching Schur bounds (`two_mul_abs_interWindowRatioForm_le`,
   `two_mul_abs_interWindowProductForm_le`).** Decomposing the inter-window ratio matrix into
   partial matchings `b = m a` over `m ∈ ratioBandFinset X Y` bounds the bilinear ratio and product
   couplings between `A ⊆ W(X)` and `B ⊆ W(Y)` by the band sum `∑_{m ∈ ratioBandFinset X Y} Λ(m)/√m`
   and `(2/X) ∑_{m ∈ ratioBandFinset X Y} Λ(m)/√m`.
-/

open ArithmeticFunction RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### Part I: Exact scale-suppression law for crossing vs. ratio atoms -/

/-- **Exact crossing-to-ratio factorization.** On any prime-power crossing pair `a < b`
(`IsPrimePow (a * b)`), the crossing atom equals the same-side ratio atom divided by `a`:
`Λ(ab)/√(ab) = (Λ(b/a)/√(b/a)) / a`. -/
theorem productAtom_eq_ratioAtom_div_of_isPrimePow {a b : ℕ} (hab : a < b)
    (h : IsPrimePow (a * b)) :
    productAtom a b = ratioAtom a b / a := by
  obtain ⟨p, i, j, hp, rfl, rfl, hij⟩ := exists_prime_pow_of_isPrimePow_mul h
  have hlt : i < j := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hab
  rw [productAtom_pow_pow hp hij, ratioAtom_pow_pow hp hlt, div_div]
  congr 1
  have hexp : i + j = (j - i) + 2 * i := by omega
  have hpow : ((p ^ (i + j) : ℕ) : ℝ) = ((p ^ (j - i) : ℕ) : ℝ) * (((p ^ i : ℕ) : ℝ) ^ 2) := by
    rw [hexp, pow_add, pow_mul']
    push_cast
    ring
  have hpos_ji : (0 : ℝ) ≤ ((p ^ (j - i) : ℕ) : ℝ) := by positivity
  have hpos_i : (0 : ℝ) ≤ ((p ^ i : ℕ) : ℝ) := by positivity
  rw [hpow, Real.sqrt_mul hpos_ji, Real.sqrt_sq hpos_i]

/-- **Scale-suppressed dominance law.** For every `1 ≤ a < b`,
`productAtom a b ≤ ratioAtom a b / a`. -/
theorem productAtom_le_ratioAtom_div {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    productAtom a b ≤ ratioAtom a b / a := by
  by_cases h : IsPrimePow (a * b)
  · rw [productAtom_eq_ratioAtom_div_of_isPrimePow hab h]
  · rw [productAtom_eq_zero_of_not_isPrimePow h]
    have ha0 : (0 : ℝ) ≤ a := by positivity
    exact div_nonneg (ratioAtom_nonneg a b) ha0

/-- **Strict net-atom coercivity.** For every `1 ≤ a < b`,
`(1 − 1/a) · ratioAtom a b ≤ netAtom a b`. -/
theorem netAtom_ge_one_sub_inv_mul_ratioAtom {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    (1 - 1 / (a : ℝ)) * ratioAtom a b ≤ netAtom a b := by
  unfold netAtom
  have h := productAtom_le_ratioAtom_div ha hab
  have heq : (1 - 1 / (a : ℝ)) * ratioAtom a b = ratioAtom a b - ratioAtom a b / a := by ring
  linarith

/-- On a support `S` bounded below by `A > 0`, the crossing energy is at most `(1/A)` times the
same-side ratio energy. -/
theorem productEnergy_le_inv_mul_ratioEnergy {S : Finset ℕ} {A : ℝ} (hA : 0 < A)
    (hS : ∀ a ∈ S, A ≤ a) (c : ℕ → ℝ) :
    productEnergy S c ≤ (1 / A) * ratioEnergy S c := by
  unfold productEnergy ratioEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a ha => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  split_ifs with hab
  · have haA : A ≤ a := hS a ha
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | hpos
      · simp at haA; linarith
      · exact hpos
    have hdiv : productAtom a b ≤ (1 / A) * ratioAtom a b := by
      calc productAtom a b ≤ ratioAtom a b / a := productAtom_le_ratioAtom_div ha1 hab
        _ ≤ ratioAtom a b / A := div_le_div_of_nonneg_left (ratioAtom_nonneg a b) hA haA
        _ = (1 / A) * ratioAtom a b := by ring
    calc productAtom a b * (c a - c b) ^ 2
        ≤ ((1 / A) * ratioAtom a b) * (c a - c b) ^ 2 :=
          mul_le_mul_of_nonneg_right hdiv (sq_nonneg _)
      _ = 1 / A * (ratioAtom a b * (c a - c b) ^ 2) := by ring
  · simp

/-- On a support `S` bounded below by `A > 0`, the net prime skeleton energy is at least
`1 − 1/A` times the ratio energy. -/
theorem skeletonEnergy_ge_one_sub_inv_mul_ratioEnergy {S : Finset ℕ} {A : ℝ} (hA : 0 < A)
    (hS : ∀ a ∈ S, A ≤ a) (c : ℕ → ℝ) :
    (1 - 1 / A) * ratioEnergy S c ≤ skeletonEnergy S c := by
  rw [skeletonEnergy_eq_sub]
  have h := productEnergy_le_inv_mul_ratioEnergy hA hS c
  linarith

/-! ### Part II: The inter-window ratio coupling graph -/

/-- Any non-empty dyadic window has positive scale `X > 0` and positive elements `a ≥ 1`. -/
theorem pos_of_inDyadicWindow {X : ℝ} {a : ℕ} (ha : InDyadicWindow X a) :
    0 < X ∧ 1 ≤ a := by
  obtain ⟨ha1, ha2⟩ := ha
  have hX : 0 < X := by linarith
  have ha_pos : (0 : ℝ) < a := by linarith
  have ha_nat : 0 < a := by exact_mod_cast ha_pos
  exact ⟨hX, ha_nat⟩

/-- The admissible band of multipliers `m` coupling `W(X)` to `W(Y)`:
`Y < 4 X m` and `m X < 4 Y` (i.e. `Y / (4X) < m < 4Y / X`). -/
def InRatioBand (X Y : ℝ) (m : ℕ) : Prop := Y < 4 * X * m ∧ (m : ℝ) * X < 4 * Y

/-- **Ratio-band admissibility.** If `a ∈ W(X)`, `b ∈ W(Y)`, and `a ∣ b`, then the multiplier
`m = b / a` lies in `InRatioBand X Y`. -/
theorem inRatioBand_of_inDyadicWindows_dvd {X Y : ℝ} {a b : ℕ}
    (ha : InDyadicWindow X a) (hb : InDyadicWindow Y b) (hdvd : a ∣ b) :
    InRatioBand X Y (b / a) := by
  obtain ⟨hX, ha1⟩ := pos_of_inDyadicWindow ha
  obtain ⟨hY, hb1⟩ := pos_of_inDyadicWindow hb
  set m := b / a
  have hba : b = m * a := (Nat.div_mul_cancel hdvd).symm
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · rw [hm0, zero_mul] at hba; omega
    · exact hpos
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm1
  have ha_pos : (0 : ℝ) < a := by exact_mod_cast ha1
  have hbR : (b : ℝ) = (m : ℝ) * (a : ℝ) := by exact_mod_cast hba
  constructor
  · have h1 : Y / 2 < (m : ℝ) * (a : ℝ) := by linarith [hb.1]
    have h2 : (m : ℝ) * (a : ℝ) < (m : ℝ) * (2 * X) := mul_lt_mul_of_pos_left ha.2 hm_pos
    linarith
  · have h1 : (m : ℝ) * (X / 2) < (m : ℝ) * (a : ℝ) := mul_lt_mul_of_pos_left ha.1 hm_pos
    have h2 : (m : ℝ) * (a : ℝ) < 2 * Y := by linarith [hb.2]
    linarith

/-- If `b / a` does not lie in `InRatioBand X Y`, then `ratioAtom a b = 0` for `a ∈ W(X)`,
`b ∈ W(Y)`. -/
theorem ratioAtom_eq_zero_of_not_inRatioBand {X Y : ℝ} {a b : ℕ}
    (ha : InDyadicWindow X a) (hb : InDyadicWindow Y b) (hm : ¬ InRatioBand X Y (b / a)) :
    ratioAtom a b = 0 := by
  unfold ratioAtom
  split_ifs with hdvd
  · exact False.elim (hm (inRatioBand_of_inDyadicWindows_dvd ha hb hdvd))
  · rfl

/-- **Scale separation decouples small multipliers.**
- When `8 X ≤ Y`, every divisor relation between `W(X)` and `W(Y)` has `b / a ≥ 3` (`2` decouples).
- When `12 X ≤ Y`, every divisor relation has `b / a ≥ 4` (`2` and `3` decouple).
- When `16 X ≤ Y`, every divisor relation has `b / a ≥ 5` (`2, 3, 4` decouple). -/
theorem le_div_of_inDyadicWindows_dvd {X Y : ℝ} {k a b : ℕ}
    (hXY : 4 * (k : ℝ) * X ≤ Y) (ha : InDyadicWindow X a) (hb : InDyadicWindow Y b)
    (hdvd : a ∣ b) :
    k + 1 ≤ b / a := by
  have hX := (pos_of_inDyadicWindow ha).1
  have hband := (inRatioBand_of_inDyadicWindows_dvd ha hb hdvd).1
  have hlt : (k : ℝ) * (4 * X) < ((b / a : ℕ) : ℝ) * (4 * X) := by linarith
  have hklt : (k : ℝ) < ((b / a : ℕ) : ℝ) := lt_of_mul_lt_mul_right hlt (by positivity)
  have hk_nat : k < b / a := by exact_mod_cast hklt
  omega

/-- When `12 X ≤ Y`, the intra-window multipliers `2` and `3` are completely decoupled between
`W(X)` and `W(Y)`: every divisor relation has `4 ≤ b / a`. -/
theorem four_le_div_of_inDyadicWindows_dvd {X Y : ℝ} (hXY : 12 * X ≤ Y) {a b : ℕ}
    (ha : InDyadicWindow X a) (hb : InDyadicWindow Y b) (hdvd : a ∣ b) :
    4 ≤ b / a :=
  le_div_of_inDyadicWindows_dvd (k := 3) (by push_cast; linarith) ha hb hdvd

/-- **Ratio-band tower bound (`p^{j−i} < 16`).** Any two powers `p^i ≤ p^j` of a prime `p` in
`InRatioBand X Y` (`0 < X`, `0 < Y`) have ratio strictly below `16`. -/
theorem pow_sub_lt_sixteen_of_inRatioBand {X Y : ℝ} (hX : 0 < X) (_hY : 0 < Y)
    {p i j : ℕ} (hp : p.Prime) (hij : i ≤ j)
    (hi : InRatioBand X Y (p ^ i)) (hj : InRatioBand X Y (p ^ j)) :
    p ^ (j - i) < 16 := by
  have hpi_pos : (0 : ℝ) < (p : ℝ) ^ i := pow_pos (by exact_mod_cast hp.pos) i
  have h1 : ((p ^ j : ℕ) : ℝ) * X < 4 * Y := hj.2
  have h2 : Y < 4 * X * ((p ^ i : ℕ) : ℝ) := hi.1
  have h3 : ((p ^ j : ℕ) : ℝ) * X < 16 * X * ((p ^ i : ℕ) : ℝ) := by linarith
  have h4 : (p : ℝ) ^ j < 16 * (p : ℝ) ^ i := by
    refine lt_of_mul_lt_mul_right ?_ hX.le
    push_cast at h3
    linarith
  have heq : (p : ℝ) ^ j = (p : ℝ) ^ (j - i) * (p : ℝ) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hij]
  rw [heq] at h4
  have h5 : (p : ℝ) ^ (j - i) < 16 := lt_of_mul_lt_mul_right h4 hpi_pos.le
  exact_mod_cast h5

/-- For any prime `p`, two powers `p^i, p^j` in `InRatioBand X Y` satisfy `j ≤ i + 3`
(at most `4` powers of `2` can couple `W(X)` and `W(Y)`). -/
theorem exponent_sub_le_three_of_inRatioBand {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {p i j : ℕ} (hp : p.Prime)
    (hi : InRatioBand X Y (p ^ i)) (hj : InRatioBand X Y (p ^ j)) :
    j ≤ i + 3 := by
  rcases le_or_gt i j with hij | hij
  · have hlt := pow_sub_lt_sixteen_of_inRatioBand hX hY hp hij hi hj
    by_contra hc
    have h4 : 4 ≤ j - i := by omega
    have hpow : 16 ≤ p ^ (j - i) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (j - i) := Nat.pow_le_pow_right (by norm_num) h4
        _ ≤ p ^ (j - i) := Nat.pow_le_pow_left hp.two_le _
    omega
  · omega

/-- For any odd prime `p ≥ 3`, two powers `p^i, p^j` in `InRatioBand X Y` satisfy `j ≤ i + 2`
(at most `3` powers of `3` can couple `W(X)` and `W(Y)`). -/
theorem exponent_sub_le_two_of_inRatioBand_of_three_le {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {p i j : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hi : InRatioBand X Y (p ^ i)) (hj : InRatioBand X Y (p ^ j)) :
    j ≤ i + 2 := by
  rcases le_or_gt i j with hij | hij
  · have hlt := pow_sub_lt_sixteen_of_inRatioBand hX hY hp hij hi hj
    by_contra hc
    have h3 : 3 ≤ j - i := by omega
    have hpow : 27 ≤ p ^ (j - i) := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ (j - i) := Nat.pow_le_pow_right (by norm_num) h3
        _ ≤ p ^ (j - i) := Nat.pow_le_pow_left hp3 _
    omega
  · omega

/-- For any prime `p ≥ 5`, two powers `p^i, p^j` in `InRatioBand X Y` satisfy `j ≤ i + 1`
(at most `2` powers of `p ∈ {5, 7, 11, 13}` can couple `W(X)` and `W(Y)`). -/
theorem exponent_sub_le_one_of_inRatioBand_of_five_le {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {p i j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hi : InRatioBand X Y (p ^ i)) (hj : InRatioBand X Y (p ^ j)) :
    j ≤ i + 1 := by
  rcases le_or_gt i j with hij | hij
  · have hlt := pow_sub_lt_sixteen_of_inRatioBand hX hY hp hij hi hj
    by_contra hc
    have h2 : 2 ≤ j - i := by omega
    have hpow : 25 ≤ p ^ (j - i) := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ 5 ^ (j - i) := Nat.pow_le_pow_right (by norm_num) h2
        _ ≤ p ^ (j - i) := Nat.pow_le_pow_left hp5 _
    omega
  · omega

/-- **Uniqueness of prime-power ratio exponent for `p ≥ 17`.** Any prime `p ≥ 17` has at most one
power in `InRatioBand X Y`. -/
theorem exponent_eq_of_inRatioBand_of_seventeen_le {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {p i j : ℕ} (hp : p.Prime) (hp17 : 17 ≤ p)
    (hi : InRatioBand X Y (p ^ i)) (hj : InRatioBand X Y (p ^ j)) :
    i = j := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hj hi (by omega)).symm
  have hlt := pow_sub_lt_sixteen_of_inRatioBand hX hY hp hij hi hj
  by_contra hne
  have h1 : 1 ≤ j - i := by omega
  have hpow : 17 ≤ p ^ (j - i) := by
    calc 17 ≤ p := hp17
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (j - i) := Nat.pow_le_pow_right hp.pos h1
  omega

/-- **Square-root scale-decay of inter-window ratio edges.** For `0 < X`, `4 X ≤ Y`, and any
`a ∈ W(X)`, `b ∈ W(Y)`,
`ratioAtom a b < 2 log(4Y / X) √(X / Y)`. -/
theorem ratioAtom_lt_of_inDyadicWindows {X Y : ℝ} (hX : 0 < X) (hXY : 4 * X ≤ Y)
    {a b : ℕ} (ha : InDyadicWindow X a) (hb : InDyadicWindow Y b) :
    ratioAtom a b < 2 * Real.log (4 * Y / X) * Real.sqrt (X / Y) := by
  have hY : 0 < Y := by linarith
  have h4YX : 16 ≤ 4 * Y / X := by rw [le_div_iff₀ hX]; linarith
  have hlog_pos : 0 < Real.log (4 * Y / X) := Real.log_pos (by linarith)
  have hsqrt_pos : 0 < Real.sqrt (X / Y) := Real.sqrt_pos.mpr (div_pos hX hY)
  unfold ratioAtom
  split_ifs with hdvd
  · set m := b / a
    obtain ⟨hm_lo, hm_hi⟩ := inRatioBand_of_inDyadicWindows_dvd ha hb hdvd
    have hm_gt1 : 1 < (m : ℝ) := by
      have : (4 * X) * 1 < (4 * X) * (m : ℝ) := by linarith
      exact lt_of_mul_lt_mul_left this (by positivity)
    have hm2 : 2 ≤ m := by
      have : 1 < m := by exact_mod_cast hm_gt1
      omega
    have hm_pos : (0 : ℝ) < m := by positivity
    unfold vonMangoldtAtom
    rw [if_pos hm2]
    have hΛ : vonMangoldt m ≤ Real.log m := vonMangoldt_le_log
    have hlog_lt : Real.log m < Real.log (4 * Y / X) := by
      refine Real.log_lt_log hm_pos ?_
      rw [lt_div_iff₀ hX]
      exact hm_hi
    have hsqrt_gt : Real.sqrt (Y / (4 * X)) < Real.sqrt m := by
      refine Real.sqrt_lt_sqrt (by positivity) ?_
      rw [div_lt_iff₀ (by positivity)]
      linarith
    have hsqrt_pos' : 0 < Real.sqrt (Y / (4 * X)) := Real.sqrt_pos.mpr (by positivity)
    have hinv : (Real.sqrt (Y / (4 * X)))⁻¹ = 2 * Real.sqrt (X / Y) := by
      have heq : Y / (4 * X) = (Y / X) / 4 := by ring
      rw [heq, Real.sqrt_div (by positivity),
        show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
        inv_div, div_eq_mul_inv, ← Real.sqrt_inv, inv_div]
    calc vonMangoldt m / Real.sqrt m
        ≤ Real.log m / Real.sqrt m :=
          div_le_div_of_nonneg_right hΛ (Real.sqrt_nonneg _)
      _ < Real.log (4 * Y / X) / Real.sqrt (Y / (4 * X)) :=
          div_lt_div₀ hlog_lt hsqrt_gt.le (Real.log_nonneg (by linarith)) hsqrt_pos'
      _ = Real.log (4 * Y / X) * (Real.sqrt (Y / (4 * X)))⁻¹ := div_eq_mul_inv _ _
      _ = 2 * Real.log (4 * Y / X) * Real.sqrt (X / Y) := by rw [hinv]; ring
  · positivity

/-! ### Part III: The inter-window crossing (product-atom) coupling graph -/

/-- **Prime horizon for inter-window crossing edges.** If `X ≥ 2`, `a ∈ W(X)`, `b ∈ W(Y)` with
`a < b`, and `ab` is a prime power, then `a = p^i` and `b = p^j` for a single prime `p < 2X` with
`1 ≤ i < j`. In particular, no prime `p ≥ 2X` ever produces a crossing edge out of `W(X)`. -/
theorem exists_prime_pow_of_inDyadicWindows_isPrimePow_mul {X Y : ℝ} (hX : 2 ≤ X)
    {a b : ℕ} (ha : InDyadicWindow X a) (hb : InDyadicWindow Y b) (hab : a < b)
    (h : IsPrimePow (a * b)) :
    ∃ p i j : ℕ, p.Prime ∧ (p : ℝ) < 2 * X ∧ 1 ≤ i ∧ i < j ∧ a = p ^ i ∧ b = p ^ j := by
  obtain ⟨p, i, j, hp, rfl, rfl, -⟩ := exists_prime_pow_of_isPrimePow_mul h
  have hij : i < j := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hab
  have ha_gt1 : 1 < ((p ^ i : ℕ) : ℝ) := by linarith [ha.1]
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp at ha_gt1
    · exact hpos
  have hp_le : p ≤ p ^ i := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos hi1
  have hp_lt : (p : ℝ) < 2 * X := by
    have : (p : ℝ) ≤ ((p ^ i : ℕ) : ℝ) := by exact_mod_cast hp_le
    linarith [ha.2]
  exact ⟨p, i, j, hp, hp_lt, hi1, hij, rfl, rfl⟩

/-- **Uniqueness of inter-window crossing edges per prime `p ≥ 5`.** A prime `p ≥ 5` contributes at
most one crossing edge between `W(X)` and `W(Y)`. -/
theorem unique_crossing_pair_of_five_le {X Y : ℝ} {p i₁ j₁ i₂ j₂ : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hi₁ : InDyadicWindow X (p ^ i₁)) (hj₁ : InDyadicWindow Y (p ^ j₁))
    (hi₂ : InDyadicWindow X (p ^ i₂)) (hj₂ : InDyadicWindow Y (p ^ j₂)) :
    i₁ = i₂ ∧ j₁ = j₂ :=
  ⟨exponent_eq_of_inDyadicWindow_of_five_le hp hp5 hi₁ hi₂,
   exponent_eq_of_inDyadicWindow_of_five_le hp hp5 hj₁ hj₂⟩

/-- **Geometric scale-decay of inter-window crossing atoms (`X ≥ 2`).** For `X ≥ 2`, `Y > 0`, and
any `a ∈ W(X)`, `b ∈ W(Y)` with `a < b`,
`productAtom a b < 2 log(2X) / √(XY)`. -/
theorem productAtom_lt_of_inDyadicWindows_of_two_le {X Y : ℝ} (hX : 2 ≤ X) (hY : 0 < Y)
    {a b : ℕ} (ha : InDyadicWindow X a) (hb : InDyadicWindow Y b) (hab : a < b) :
    productAtom a b < 2 * Real.log (2 * X) / Real.sqrt (X * Y) := by
  have hlog_pos : 0 < Real.log (2 * X) := Real.log_pos (by linarith)
  have hsqrt_pos : 0 < Real.sqrt (X * Y) := Real.sqrt_pos.mpr (by positivity)
  by_cases h : IsPrimePow (a * b)
  · obtain ⟨p, i, j, hp, hp_lt, hi1, hij, rfl, rfl⟩ :=
      exists_prime_pow_of_inDyadicWindows_isPrimePow_mul hX ha hb hab h
    rw [productAtom_pow_pow hp (by omega)]
    have hlogp : Real.log p < Real.log (2 * X) :=
      Real.log_lt_log (by exact_mod_cast hp.pos) hp_lt
    have hsqrt_gt : Real.sqrt (X * Y) / 2 < Real.sqrt ((p ^ (i + j) : ℕ) : ℝ) := by
      have h1 : X / 2 < ((p ^ i : ℕ) : ℝ) := ha.1
      have h2 : Y / 2 < ((p ^ j : ℕ) : ℝ) := hb.1
      have h3 : (X / 2) * (Y / 2) < ((p ^ i : ℕ) : ℝ) * ((p ^ j : ℕ) : ℝ) :=
        mul_lt_mul'' h1 h2 (by positivity) (by positivity)
      have h4 : (Real.sqrt (X * Y) / 2) ^ 2 < ((p ^ (i + j) : ℕ) : ℝ) := by
        rw [div_pow, Real.sq_sqrt (by positivity), pow_add]
        push_cast at h3 ⊢
        linarith
      exact (Real.lt_sqrt (by positivity)).mpr h4
    calc Real.log p / Real.sqrt ((p ^ (i + j) : ℕ) : ℝ)
        < Real.log (2 * X) / (Real.sqrt (X * Y) / 2) :=
          div_lt_div₀ hlogp hsqrt_gt.le hlog_pos.le (by positivity)
      _ = 2 * Real.log (2 * X) / Real.sqrt (X * Y) := by ring
  · rw [productAtom_eq_zero_of_not_isPrimePow h]
    positivity

/-- For `a ∈ W(X)` (`X > 0`) and `a < b`, the crossing atom is suppressed by `2 / X` relative to the
same-side ratio atom: `productAtom a b ≤ (2 / X) · ratioAtom a b`. -/
theorem productAtom_le_two_div_mul_ratioAtom_of_inDyadicWindow {X : ℝ} {a b : ℕ}
    (ha : InDyadicWindow X a) (hab : a < b) :
    productAtom a b ≤ (2 / X) * ratioAtom a b := by
  obtain ⟨hX, ha1⟩ := pos_of_inDyadicWindow ha
  calc productAtom a b ≤ ratioAtom a b / a := productAtom_le_ratioAtom_div ha1 hab
    _ ≤ ratioAtom a b / (X / 2) :=
        div_le_div_of_nonneg_left (ratioAtom_nonneg a b) (by positivity) ha.1.le
    _ = (2 / X) * ratioAtom a b := by ring

/-! ### Part IV: Partial-matching decomposition and Schur bounds for inter-window forms -/

/-- The partial-matching bilinear form `∑_{a ∈ A} ∑_{b ∈ B} 1_{b = m a} u(a) v(b)` at a fixed
multiplier `m`. -/
def multiplierCoupling (m : ℕ) (A B : Finset ℕ) (u v : ℕ → ℝ) : ℝ :=
  ∑ a ∈ A, ∑ b ∈ B, if b = m * a then u a * v b else 0

/-- **Partial-matching Schur bound.** For every multiplier `m ≥ 1`, the partial matching `b = m a`
has row and column degree at most `1`, so
`2 |multiplierCoupling m A B u v| ≤ ∑_{a ∈ A} u(a)² + ∑_{b ∈ B} v(b)²`. -/
theorem two_mul_abs_multiplierCoupling_le {m : ℕ} (hm : 1 ≤ m) (A B : Finset ℕ) (u v : ℕ → ℝ) :
    2 * |multiplierCoupling m A B u v| ≤ ∑ a ∈ A, u a ^ 2 + ∑ b ∈ B, v b ^ 2 := by
  unfold multiplierCoupling
  have h1 : 2 * |∑ a ∈ A, ∑ b ∈ B, if b = m * a then u a * v b else 0| ≤
      ∑ a ∈ A, ∑ b ∈ B, if b = m * a then 2 * |u a * v b| else 0 := by
    calc 2 * |∑ a ∈ A, ∑ b ∈ B, if b = m * a then u a * v b else 0|
        ≤ 2 * ∑ a ∈ A, ∑ b ∈ B, |if b = m * a then u a * v b else 0| := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ a ∈ A, ∑ b ∈ B, if b = m * a then 2 * |u a * v b| else 0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          split_ifs <;> simp
  have h2 : ∑ a ∈ A, ∑ b ∈ B, (if b = m * a then 2 * |u a * v b| else 0) ≤
      ∑ a ∈ A, ∑ b ∈ B, (if b = m * a then u a ^ 2 + v b ^ 2 else 0) := by
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    split_ifs
    · rw [abs_mul]
      have hsq : 0 ≤ (|u a| - |v b|) ^ 2 := sq_nonneg _
      have hu2 : |u a| ^ 2 = u a ^ 2 := sq_abs _
      have hv2 : |v b| ^ 2 = v b ^ 2 := sq_abs _
      nlinarith
    · exact le_rfl
  have hrow : ∑ a ∈ A, ∑ b ∈ B, (if b = m * a then u a ^ 2 else 0) ≤ ∑ a ∈ A, u a ^ 2 := by
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  have hcol : ∑ a ∈ A, ∑ b ∈ B, (if b = m * a then v b ^ 2 else 0) ≤ ∑ b ∈ B, v b ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun b _ => ?_
    by_cases hdiv : ∃ a ∈ A, b = m * a
    · obtain ⟨a₀, ha₀, rfl⟩ := hdiv
      have heq : ∀ a ∈ A, (if m * a₀ = m * a then v (m * a₀) ^ 2 else 0) =
          if a = a₀ then v (m * a₀) ^ 2 else 0 := by
        intro a _
        have hiff : m * a₀ = m * a ↔ a = a₀ := by
          rw [mul_eq_mul_left_iff, or_iff_left (by omega), eq_comm]
        simp only [hiff]
      rw [Finset.sum_congr rfl heq, Finset.sum_ite_eq', if_pos ha₀]
    · push Not at hdiv
      have hz : ∀ a ∈ A, (if b = m * a then v b ^ 2 else 0) = 0 := fun a ha =>
        if_neg (hdiv a ha)
      rw [Finset.sum_eq_zero hz]
      exact sq_nonneg _
  have hsplit : ∑ a ∈ A, ∑ b ∈ B, (if b = m * a then u a ^ 2 + v b ^ 2 else 0) =
      (∑ a ∈ A, ∑ b ∈ B, if b = m * a then u a ^ 2 else 0) +
      (∑ a ∈ A, ∑ b ∈ B, if b = m * a then v b ^ 2 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  linarith

/-- The finite set of multipliers `m` in the ratio band `(Y/(4X), 4Y/X)`:
`Finset.Icc (⌊Y / (4X)⌋₊ + 1) ⌈4Y / X⌉₊`. -/
def ratioBandFinset (X Y : ℝ) : Finset ℕ :=
  Finset.Icc (⌊Y / (4 * X)⌋₊ + 1) ⌈4 * Y / X⌉₊

/-- Every multiplier `m` satisfying `InRatioBand X Y m` (`0 < X`) belongs to
`ratioBandFinset X Y`. -/
theorem mem_ratioBandFinset_of_inRatioBand {X Y : ℝ} (hX : 0 < X) {m : ℕ}
    (hm : InRatioBand X Y m) :
    m ∈ ratioBandFinset X Y := by
  rw [ratioBandFinset, Finset.mem_Icc]
  obtain ⟨hm1, hm2⟩ := hm
  have hm_pos : (0 : ℝ) < m := by
    by_contra hc
    have hm0 : (m : ℝ) ≤ 0 := not_lt.mp hc
    have h1 : 4 * X * (m : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hm0
    have h2 : (m : ℝ) * X ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hm0 hX.le
    linarith
  have hY : 0 < Y := by linarith [mul_pos hX hm_pos]
  constructor
  · have hlt : Y / (4 * X) < m := by rw [div_lt_iff₀ (by positivity)]; linarith
    have hfl : (⌊Y / (4 * X)⌋₊ : ℝ) ≤ Y / (4 * X) := Nat.floor_le (by positivity)
    have hfl_lt : (⌊Y / (4 * X)⌋₊ : ℝ) < m := hfl.trans_lt hlt
    have hnat : ⌊Y / (4 * X)⌋₊ < m := by exact_mod_cast hfl_lt
    omega
  · have hle : (m : ℝ) ≤ 4 * Y / X := (le_div_iff₀ hX).mpr hm2.le
    exact_mod_cast hle.trans (Nat.le_ceil _)

/-- Every multiplier in `ratioBandFinset X Y` is at least `1`. -/
theorem one_le_of_mem_ratioBandFinset {X Y : ℝ} {m : ℕ} (hm : m ∈ ratioBandFinset X Y) :
    1 ≤ m := by
  have := (Finset.mem_Icc.mp hm).1
  omega

/-- Pointwise multiplier expansion of `ratioAtom a b` for `a ∈ W(X)` and `b ∈ W(Y)`. -/
theorem ratioAtom_mul_eq_sum_ratioBandFinset {X Y : ℝ} {a b : ℕ}
    (ha : InDyadicWindow X a) (hb : InDyadicWindow Y b) (z : ℝ) :
    ratioAtom a b * z =
      ∑ m ∈ ratioBandFinset X Y, vonMangoldtAtom m * (if b = m * a then z else 0) := by
  obtain ⟨hX, ha1⟩ := pos_of_inDyadicWindow ha
  unfold ratioAtom
  split_ifs with hdvd
  · set m₀ := b / a
    have hm₀_band : InRatioBand X Y m₀ := inRatioBand_of_inDyadicWindows_dvd ha hb hdvd
    have hm₀_mem : m₀ ∈ ratioBandFinset X Y := mem_ratioBandFinset_of_inRatioBand hX hm₀_band
    have hba : b = m₀ * a := (Nat.div_mul_cancel hdvd).symm
    rw [Finset.sum_eq_single m₀]
    · rw [if_pos hba]
    · intro m _ hne
      have hne_mul : b ≠ m * a := by
        intro heq
        rw [hba, mul_eq_mul_right_iff] at heq
        rcases heq with rfl | ha0
        · exact hne rfl
        · omega
      rw [if_neg hne_mul, mul_zero]
    · intro hnot
      exact False.elim (hnot hm₀_mem)
  · rw [zero_mul]
    symm
    refine Finset.sum_eq_zero fun m _ => ?_
    have hne : b ≠ m * a := fun heq => hdvd ⟨m, by rw [heq, mul_comm]⟩
    rw [if_neg hne, mul_zero]

/-- The inter-window ratio bilinear form `∑_{a ∈ A} ∑_{b ∈ B} ratioAtom(a, b) u(a) v(b)`. -/
def interWindowRatioForm (A B : Finset ℕ) (u v : ℕ → ℝ) : ℝ :=
  ∑ a ∈ A, ∑ b ∈ B, ratioAtom a b * (u a * v b)

/-- The inter-window crossing (product) bilinear form
`∑_{a ∈ A} ∑_{b ∈ B} productAtom(a, b) u(a) v(b)`. -/
def interWindowProductForm (A B : Finset ℕ) (u v : ℕ → ℝ) : ℝ :=
  ∑ a ∈ A, ∑ b ∈ B, productAtom a b * (u a * v b)

/-- The inter-window net bilinear form `∑_{a ∈ A} ∑_{b ∈ B} netAtom(a, b) u(a) v(b)`. -/
def interWindowNetForm (A B : Finset ℕ) (u v : ℕ → ℝ) : ℝ :=
  ∑ a ∈ A, ∑ b ∈ B, netAtom a b * (u a * v b)

/-- **Exact partial-matching decomposition of the inter-window ratio form.** For `A ⊆ W(X)` and
`B ⊆ W(Y)`, the inter-window ratio form decomposes into the partial matchings `multiplierCoupling m`
over `m ∈ ratioBandFinset X Y`. -/
theorem interWindowRatioForm_eq_sum_ratioBandFinset {X Y : ℝ} {A B : Finset ℕ}
    (hA : ∀ a ∈ A, InDyadicWindow X a) (hB : ∀ b ∈ B, InDyadicWindow Y b) (u v : ℕ → ℝ) :
    interWindowRatioForm A B u v =
      ∑ m ∈ ratioBandFinset X Y, vonMangoldtAtom m * multiplierCoupling m A B u v := by
  unfold interWindowRatioForm multiplierCoupling
  have h1 : ∀ a ∈ A, ∑ b ∈ B, ratioAtom a b * (u a * v b) =
      ∑ m ∈ ratioBandFinset X Y, ∑ b ∈ B,
        vonMangoldtAtom m * (if b = m * a then u a * v b else 0) := by
    intro a ha
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b hb => ratioAtom_mul_eq_sum_ratioBandFinset (hA a ha) (hB b hb) _
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]

/-- **Inter-window ratio Schur bound.** For `A ⊆ W(X)` and `B ⊆ W(Y)`,
`2 |interWindowRatioForm A B u v| ≤ (∑_{m ∈ ratioBandFinset X Y} Λ(m)/√m) (∑_{a ∈ A} u(a)² + ∑_{b ∈ B} v(b)²)`. -/
theorem two_mul_abs_interWindowRatioForm_le {X Y : ℝ} {A B : Finset ℕ}
    (hA : ∀ a ∈ A, InDyadicWindow X a) (hB : ∀ b ∈ B, InDyadicWindow Y b) (u v : ℕ → ℝ) :
    2 * |interWindowRatioForm A B u v| ≤
      (∑ m ∈ ratioBandFinset X Y, vonMangoldtAtom m) *
        (∑ a ∈ A, u a ^ 2 + ∑ b ∈ B, v b ^ 2) := by
  rw [interWindowRatioForm_eq_sum_ratioBandFinset hA hB u v, Finset.sum_mul]
  calc 2 * |∑ m ∈ ratioBandFinset X Y, vonMangoldtAtom m * multiplierCoupling m A B u v|
      ≤ 2 * ∑ m ∈ ratioBandFinset X Y, |vonMangoldtAtom m * multiplierCoupling m A B u v| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ m ∈ ratioBandFinset X Y, vonMangoldtAtom m * (2 * |multiplierCoupling m A B u v|) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg m)]
        ring
    _ ≤ ∑ m ∈ ratioBandFinset X Y, vonMangoldtAtom m * (∑ a ∈ A, u a ^ 2 + ∑ b ∈ B, v b ^ 2) := by
        refine Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_left
          (two_mul_abs_multiplierCoupling_le (one_le_of_mem_ratioBandFinset hm) A B u v)
          (vonMangoldtAtom_nonneg m)

/-- **Inter-window crossing (product) Schur bound.** For `0 < X`, `4 X ≤ Y`, `A ⊆ W(X)`, and
`B ⊆ W(Y)`, the crossing bilinear form is suppressed by `2 / X` relative to the ratio band weight:
`2 |interWindowProductForm A B u v| ≤ (2 / X) (∑_{m ∈ ratioBandFinset X Y} Λ(m)/√m) (∑_{a ∈ A} u(a)² + ∑_{b ∈ B} v(b)²)`. -/
theorem two_mul_abs_interWindowProductForm_le {X Y : ℝ} (hX : 0 < X) (hXY : 4 * X ≤ Y)
    {A B : Finset ℕ} (hA : ∀ a ∈ A, InDyadicWindow X a) (hB : ∀ b ∈ B, InDyadicWindow Y b)
    (u v : ℕ → ℝ) :
    2 * |interWindowProductForm A B u v| ≤
      (2 / X) * (∑ m ∈ ratioBandFinset X Y, vonMangoldtAtom m) *
        (∑ a ∈ A, u a ^ 2 + ∑ b ∈ B, v b ^ 2) := by
  have hdom : |interWindowProductForm A B u v| ≤
      (2 / X) * interWindowRatioForm A B (fun a => |u a|) (fun b => |v b|) := by
    unfold interWindowProductForm interWindowRatioForm
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a ha => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b hb => ?_)
    have hab : a < b := by
      have ha2 := (hA a ha).2
      have hb1 := (hB b hb).1
      have hlt : (a : ℝ) < (b : ℝ) := by linarith
      exact_mod_cast hlt
    rw [abs_mul, abs_mul, abs_of_nonneg (productAtom_nonneg a b)]
    have hp := productAtom_le_two_div_mul_ratioAtom_of_inDyadicWindow (hA a ha) hab
    calc productAtom a b * (|u a| * |v b|)
        ≤ ((2 / X) * ratioAtom a b) * (|u a| * |v b|) :=
          mul_le_mul_of_nonneg_right hp (by positivity)
      _ = 2 / X * (ratioAtom a b * (|u a| * |v b|)) := by ring
  have hrat := two_mul_abs_interWindowRatioForm_le hA hB (fun a => |u a|) (fun b => |v b|)
  have hrat_nn : 0 ≤ interWindowRatioForm A B (fun a => |u a|) (fun b => |v b|) := by
    unfold interWindowRatioForm
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      mul_nonneg (ratioAtom_nonneg a b) (by positivity)
  rw [abs_of_nonneg hrat_nn] at hrat
  simp only [sq_abs] at hrat
  calc 2 * |interWindowProductForm A B u v|
      ≤ (2 / X) * (2 * interWindowRatioForm A B (fun a => |u a|) (fun b => |v b|)) := by
        have := mul_le_mul_of_nonneg_left hdom (show (0 : ℝ) ≤ 2 by norm_num)
        linarith
    _ ≤ (2 / X) * ((∑ m ∈ ratioBandFinset X Y, vonMangoldtAtom m) *
          (∑ a ∈ A, u a ^ 2 + ∑ b ∈ B, v b ^ 2)) :=
        mul_le_mul_of_nonneg_left hrat (by positivity)
    _ = (2 / X) * (∑ m ∈ ratioBandFinset X Y, vonMangoldtAtom m) *
          (∑ a ∈ A, u a ^ 2 + ∑ b ∈ B, v b ^ 2) := by ring

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
