import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.DigitImbalanceLaw

/-!
# All-refinement periodic-digit spike impossibility theorem

Three consecutive refinements `j, j + 1, j + 2` eliminate both the `X^(1-w)/(1-w)` counterterm and
the `K C^(-4Kw)` logarithmic spike along aligned radix shells `X = C^(4K)`. A natural question is
whether combining sufficiently many refinements `j, j + 1, ..., j + M` at a common cutoff `X` can
cancel the `O(X^(-Re w) log X)` digit-imbalance oscillation across **all** integer cutoffs `X ≥ 1`.

This module proves that no nonzero finite linear combination can do so:

1. Repeating any `2^(M+1)`-digit base-`C` block `B ∈ [C^(2^(M+1)-1), C^(2^(M+1)))` `K` times yields
   exact linear growth `Δ_{C^(2^r)}(X_K(B)) = K (2^(M+1-r) - 2 s_{C^(2^r)}(B) / (C^(2^r) - 1))`
   simultaneously across every refinement `0 ≤ r ≤ M`.
2. Comparing `B₀ = C^(2^(M+1)-1)` against the `M + 1` two-term blocks `B_m = C^(2^(M+1)-1) + C^(s_m)`
   (`s_0 = 0`, `s_m = 2^(m-1)`) produces an `(M + 1) × (M + 1)` digit-shift matrix that becomes
   upper triangular with nonzero diagonal `(1, C - 1, C^2 - 1, ..., C^(2^(M-1)) - 1)` after
   subtracting row `0`.
3. Consequently, for **every** `M ≥ 0` and **every** nonzero tuple `α : Fin (M + 1) → ℂ`, there is
   an explicit periodic-digit cutoff sequence `X_K` along which
   `∑_{r=0}^M α_r renormalizedCutoff t (j + r) X_K w - limit` is asymptotic to a nonzero multiple
   `κ_α(B) ≠ 0` of `K X_K^(-w)`. At every zero of `ζ(w)` in `Re w > 0`, every nonzero finite
   combination of refinements retains an `Ω(X^(-Re w) log X)` oscillation spike.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation

open AntipodalSpectrum Complex Filter
open scoped Topology

/-- Iterated clock halving raises `tailRadix` to `2^r`. -/
theorem tailRadix_add_pow_two (t : ExceptionalTime) (j r : ℕ) :
    (tailRadix t (j + r)).val = (tailRadix t j).val ^ (2 ^ r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hsucc : (tailRadix t ((j + r) + 1)).val = (tailRadix t (j + r)).val ^ 2 := by
      rw [← PNat.pow_coe, ← radix_sq]
      change ((block t) ^ (windingOrder (refined t ((j + r) + 1)) / 2)).val = _
      rw [(refined_parameters t ((j + r) + 1)).2.2, (refined_parameters t (j + r)).2.2,
        pow_succ' 2 (j + r), Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
      rfl
    rw [← Nat.add_assoc, hsucc, ih, ← pow_mul, ← pow_succ]

/-! ### Exact base-`b` digit sums of sparse and periodic integers -/

private theorem digits_sum_mul_pow {b : ℕ} (hb : 1 < b) (m n : ℕ) :
    (b.digits (b ^ m * n)).sum = (b.digits n).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hne : b ^ m * n ≠ 0 := Nat.mul_ne_zero (pow_ne_zero m (by omega)) hn.ne'
      have hstep : b ^ (m + 1) * n = 0 + b * (b ^ m * n) := by
        rw [pow_succ', mul_assoc, zero_add]
      rw [hstep, Nat.digits_add b hb 0 (b ^ m * n) (by omega) (Or.inr hne),
        List.sum_cons, zero_add, ih]

private theorem digits_sum_single_mul_pow {b : ℕ} (hb : 1 < b) {d : ℕ} (hd : d < b) (q : ℕ) :
    (b.digits (d * b ^ q)).sum = d := by
  rw [mul_comm, digits_sum_mul_pow hb q]
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · simp
  · have hd_eq : d = d + b * 0 := by simp
    rw [hd_eq, Nat.digits_add b hb d 0 hd (Or.inl hd0.ne')]
    simp

private theorem digits_sum_two_terms {b : ℕ} (hb : 1 < b) {p q d₀ d₁ : ℕ}
    (hpq : p < q) (hd₀ : d₀ < b) (hd₁0 : 1 ≤ d₁) (hd₁ : d₁ < b) :
    (b.digits (d₁ * b ^ q + d₀ * b ^ p)).sum = d₁ + d₀ := by
  have hinner_ne : b ^ (q - p - 1) * d₁ ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (by omega)
  have hrew : d₁ * b ^ q + d₀ * b ^ p = b ^ p * (d₀ + b * (b ^ (q - p - 1) * d₁)) := by
    have hq : q = p + (1 + (q - p - 1)) := by omega
    rw [hq, pow_add, pow_add, pow_one]
    ring
  rw [hrew, digits_sum_mul_pow hb p,
    Nat.digits_add b hb d₀ (b ^ (q - p - 1) * d₁) hd₀ (Or.inr hinner_ne),
    List.sum_cons, mul_comm (b ^ (q - p - 1)) d₁,
    digits_sum_single_mul_pow hb hd₁ (q - p - 1), add_comm]

private theorem digits_sum_block_shift {b : ℕ} (hb : 1 < b) :
    ∀ Q B Y : ℕ, B < b ^ Q → (b.digits (B + b ^ Q * Y)).sum = (b.digits B).sum + (b.digits Y).sum
  | 0, B, Y, hB => by
    have hB0 : B = 0 := by simpa using hB
    subst B; simp
  | Q + 1, B, Y, hB => by
    rcases Nat.eq_zero_or_pos Y with rfl | hY
    · simp
    · set d := B % b
      set B' := B / b
      have hd_lt : d < b := Nat.mod_lt B (by omega)
      have hdm : d + b * B' = B := by rw [add_comm]; exact Nat.div_add_mod B b
      have hB'_lt : B' < b ^ Q := by
        by_contra! hge
        have hmul := Nat.mul_le_mul_left b hge
        rw [← pow_succ'] at hmul
        omega
      have hrew : B + b ^ (Q + 1) * Y = d + b * (B' + b ^ Q * Y) := by
        calc B + b ^ (Q + 1) * Y = (d + b * B') + b * (b ^ Q * Y) := by
              rw [hdm, pow_succ', mul_assoc]
          _ = d + b * (B' + b ^ Q * Y) := by ring
      have hne_rhs : B' + b ^ Q * Y ≠ 0 := by
        have hpos : 0 < b ^ Q * Y := Nat.mul_pos (pow_pos (by omega) Q) hY
        omega
      rw [hrew, Nat.digits_add b hb d _ hd_lt (Or.inr hne_rhs), List.sum_cons,
        digits_sum_block_shift hb Q B' Y hB'_lt]
      rcases Nat.eq_zero_or_pos B with rfl | _
      · simp [d, B']
      · have hd_or : d ≠ 0 ∨ B' ≠ 0 := by
          by_contra! h
          rw [h.1, h.2] at hdm
          omega
        conv_rhs => rw [← hdm, Nat.digits_add b hb d B' hd_lt hd_or, List.sum_cons]
        ring

/-- `K`-fold base-`P` repetition `B ∑_{u=0}^{K-1} P^u` of a block `B`. -/
def periodicCutoff (P B : ℕ) : ℕ → ℕ
  | 0 => 0
  | K + 1 => B + P * periodicCutoff P B K

theorem periodicCutoff_bounds {b Q B : ℕ} (hb : 1 < b) (hQ : 1 ≤ Q)
    (hBlo : b ^ (Q - 1) ≤ B) (hBhi : B < b ^ Q) {K : ℕ} (hK : 1 ≤ K) :
    b ^ (K * Q - 1) ≤ periodicCutoff (b ^ Q) B K ∧ periodicCutoff (b ^ Q) B K < b ^ (K * Q) := by
  induction K with
  | zero => omega
  | succ K ih =>
    rcases Nat.eq_zero_or_pos K with rfl | hKpos
    · simpa [periodicCutoff] using ⟨hBlo, hBhi⟩
    · obtain ⟨hlo, hhi⟩ := ih hKpos
      change b ^ ((K + 1) * Q - 1) ≤ B + b ^ Q * periodicCutoff (b ^ Q) B K ∧
        B + b ^ Q * periodicCutoff (b ^ Q) B K < b ^ ((K + 1) * Q)
      have hKQ_pos : 1 ≤ K * Q := Nat.mul_pos hKpos hQ
      have hexp1 : (K + 1) * Q - 1 = Q + (K * Q - 1) := by
        rw [Nat.add_mul, one_mul]; omega
      have hexp2 : (K + 1) * Q = Q + K * Q := by ring
      constructor
      · rw [hexp1, pow_add]
        exact le_trans (Nat.mul_le_mul_left (b ^ Q) hlo) (Nat.le_add_left _ B)
      · rw [hexp2, pow_add]
        have hstep : periodicCutoff (b ^ Q) B K + 1 ≤ b ^ (K * Q) := hhi
        calc B + b ^ Q * periodicCutoff (b ^ Q) B K
            < b ^ Q + b ^ Q * periodicCutoff (b ^ Q) B K := by omega
          _ = b ^ Q * (periodicCutoff (b ^ Q) B K + 1) := by ring
          _ ≤ b ^ Q * b ^ (K * Q) := Nat.mul_le_mul_left (b ^ Q) hstep

theorem digitImbalance_periodicCutoff {b Q B : ℕ} (hb : 1 < b) (hQ : 1 ≤ Q)
    (hBlo : b ^ (Q - 1) ≤ B) (hBhi : B < b ^ Q) {K : ℕ} (hK : 1 ≤ K) :
    digitImbalance b (periodicCutoff (b ^ Q) B K) =
      (K : ℝ) * ((Q : ℝ) - 2 * ((b.digits B).sum : ℝ) / ((b : ℝ) - 1)) := by
  have hdsum : ∀ m : ℕ, (b.digits (periodicCutoff (b ^ Q) B m)).sum = m * (b.digits B).sum := by
    intro m
    induction m with
    | zero => simp [periodicCutoff]
    | succ m ih =>
      change (b.digits (B + b ^ Q * periodicCutoff (b ^ Q) B m)).sum = (m + 1) * (b.digits B).sum
      rw [digits_sum_block_shift hb Q B _ hBhi, ih]
      ring
  obtain ⟨hlo, hhi⟩ := periodicCutoff_bounds hb hQ hBlo hBhi hK
  have hKQ_pos : 1 ≤ K * Q := Nat.mul_pos hK hQ
  have hX_pos : 0 < periodicCutoff (b ^ Q) B K :=
    lt_of_lt_of_le (pow_pos (by omega) _) hlo
  have hlog : Nat.log b (periodicCutoff (b ^ Q) B K) = K * Q - 1 := by
    rw [Nat.log_eq_iff (Or.inr ⟨hb, hX_pos.ne'⟩)]
    exact ⟨hlo, by simpa only [Nat.sub_add_cancel hKQ_pos] using hhi⟩
  have hbr1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hb_sub : (b : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hbr1.ne'
  unfold digitImbalance
  rw [hlog, Nat.sub_add_cancel hKQ_pos, hdsum K, Nat.cast_mul, Nat.cast_mul]
  field_simp [hb_sub]
  ring

/-! ### Triangular nonsingularity of the multi-refinement spike slope -/

/-- Linear growth slope in `K` of `∑_{r=0}^M α_r Δ_{C^(2^r)}(X_K(B))` for a `2^(M+1)`-digit block `B`. -/
def refinementSpikeSlope (C M : ℕ) (α : Fin (M + 1) → ℂ) (B : ℕ) : ℂ :=
  ∑ r : Fin (M + 1),
    α r * (((2 ^ (M + 1 - r.val) : ℕ) : ℂ) -
      2 * (((C ^ (2 ^ r.val)).digits B).sum : ℂ) / (((C ^ (2 ^ r.val) : ℕ) : ℂ) - 1))

/-- For every radix `C > 1`, depth `M ≥ 0`, and nonzero coefficient tuple `α : Fin (M + 1) → ℂ`,
some `2^(M+1)`-digit base-`C` block `B` has `refinementSpikeSlope C M α B ≠ 0`. -/
theorem exists_block_refinementSpikeSlope_ne_zero {C M : ℕ} (hC : 1 < C)
    {α : Fin (M + 1) → ℂ} (hα : ∃ r : Fin (M + 1), α r ≠ 0) :
    ∃ B : ℕ, C ^ (2 ^ (M + 1) - 1) ≤ B ∧ B < C ^ (2 ^ (M + 1)) ∧
      refinementSpikeSlope C M α B ≠ 0 := by
  classical
  set N := 2 ^ (M + 1)
  have hN2 : 2 ≤ N := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (M + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set B₀ := C ^ (N - 1)
  let sPos (m : Fin (M + 1)) : ℕ := if m.val = 0 then 0 else 2 ^ (m.val - 1)
  let Bm (m : Fin (M + 1)) : ℕ := C ^ (N - 1) + C ^ (sPos m)
  have hs_lt_half : ∀ m : Fin (M + 1), sPos m < 2 ^ M := by
    intro m
    dsimp only [sPos]
    split_ifs with hm0
    · exact pow_pos (by norm_num) M
    · exact (Nat.pow_lt_pow_iff_right (by norm_num)).mpr (by omega)
  have hs_le_N2 : ∀ m : Fin (M + 1), sPos m ≤ N - 2 := by
    intro m
    have hlt := hs_lt_half m
    have h2M : 2 * 2 ^ M = N := by dsimp only [N]; rw [pow_succ']
    have hpos2M : 1 ≤ 2 ^ M := Nat.one_le_pow M 2 (by norm_num)
    omega
  have hB0_bounds : C ^ (N - 1) ≤ B₀ ∧ B₀ < C ^ N :=
    ⟨le_rfl, (Nat.pow_lt_pow_iff_right hC).mpr (by omega)⟩
  have hBm_bounds : ∀ m : Fin (M + 1), C ^ (N - 1) ≤ Bm m ∧ Bm m < C ^ N := by
    intro m
    refine ⟨Nat.le_add_right _ _, ?_⟩
    have hsm_lt : C ^ (sPos m) < C ^ (N - 1) :=
      (Nat.pow_lt_pow_iff_right hC).mpr (by have := hs_le_N2 m; omega)
    have hN_split : C ^ N = C * C ^ (N - 1) := by
      conv_lhs => rw [show N = (N - 1) + 1 by omega, pow_succ']
    calc C ^ (N - 1) + C ^ (sPos m)
        < C ^ (N - 1) + C ^ (N - 1) := by omega
      _ = 2 * C ^ (N - 1) := by ring
      _ ≤ C * C ^ (N - 1) := Nat.mul_le_mul_right _ hC
      _ = C ^ N := hN_split.symm
  -- Assume for contradiction that `B₀` and all `Bm m` have zero slope.
  by_contra! hall
  have hzero0 : refinementSpikeSlope C M α B₀ = 0 := hall B₀ hB0_bounds.1 hB0_bounds.2
  have hzerom : ∀ m : Fin (M + 1), refinementSpikeSlope C M α (Bm m) = 0 :=
    fun m => hall (Bm m) (hBm_bounds m).1 (hBm_bounds m).2
  -- Evaluate `(b_r.digits B₀).sum` and `(b_r.digits (Bm m)).sum`.
  have hdig_diff : ∀ (m r : Fin (M + 1)),
      (((C ^ (2 ^ r.val)).digits (Bm m)).sum : ℂ) -
        (((C ^ (2 ^ r.val)).digits B₀).sum : ℂ) =
        ((C ^ (sPos m % 2 ^ r.val) : ℕ) : ℂ) := by
    intro m r
    set twoR := 2 ^ r.val
    have htwoR_pos : 1 ≤ twoR := Nat.one_le_pow _ 2 (by norm_num)
    set b := C ^ twoR
    have hb : 1 < b := one_lt_pow₀ hC (by positivity)
    set Q := 2 ^ (M + 1 - r.val)
    have hQ2 : 2 ≤ Q := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (M + 1 - r.val) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hQ_mul : Q * twoR = N := by
      dsimp only [Q, twoR, N]
      rw [← pow_add, show M + 1 - r.val + r.val = M + 1 by omega]
    have hN1_eq : N - 1 = (twoR - 1) + twoR * (Q - 1) := by
      have h1 : (Q - 1) * twoR + twoR = N := by
        calc (Q - 1) * twoR + twoR = ((Q - 1) + 1) * twoR := by ring
          _ = Q * twoR := by rw [Nat.sub_add_cancel (by omega)]
          _ = N := hQ_mul
      rw [mul_comm twoR (Q - 1)]
      omega
    have hB0_eq : B₀ = C ^ (twoR - 1) * b ^ (Q - 1) := by
      dsimp only [B₀, b]
      rw [hN1_eq, pow_add, pow_mul]
    have hd1_lt : C ^ (twoR - 1) < b :=
      (Nat.pow_lt_pow_iff_right hC).mpr (by omega)
    have hd1_pos : 1 ≤ C ^ (twoR - 1) := Nat.one_le_pow _ C (by omega)
    have hsum0 : (b.digits B₀).sum = C ^ (twoR - 1) := by
      rw [hB0_eq]
      exact digits_sum_single_mul_pow hb hd1_lt (Q - 1)
    set p := sPos m / twoR
    have hp_lt : p < Q - 1 := by
      have hs_lt_prod : sPos m < (Q - 1) * twoR := by
        have h2r_le : twoR ≤ 2 ^ M :=
          Nat.pow_le_pow_right (by norm_num) (Nat.lt_succ_iff.mp r.isLt)
        have hprod : (Q - 1) * twoR = N - twoR := by
          have h1 : (Q - 1) * twoR + twoR = N := by
            calc (Q - 1) * twoR + twoR = ((Q - 1) + 1) * twoR := by ring
              _ = N := by rw [Nat.sub_add_cancel (by omega), hQ_mul]
          omega
        have h2M : 2 * 2 ^ M = N := by dsimp only [N]; rw [pow_succ']
        have hslt := hs_lt_half m
        omega
      by_contra! hge
      have hmul := Nat.mul_le_mul_right twoR hge
      have hdm := Nat.div_add_mod (sPos m) twoR
      dsimp only [p] at hmul
      rw [mul_comm _ twoR] at hmul
      omega
    have hsm_eq : C ^ (sPos m) = C ^ (sPos m % twoR) * b ^ p := by
      dsimp only [b, p]
      conv_lhs => rw [← Nat.div_add_mod (sPos m) twoR, add_comm, pow_add, pow_mul]
      rw [mul_comm (twoR) _]
    have hd0_lt : C ^ (sPos m % twoR) < b :=
      (Nat.pow_lt_pow_iff_right hC).mpr (Nat.mod_lt _ htwoR_pos)
    have hsum_m : (b.digits (Bm m)).sum = C ^ (twoR - 1) + C ^ (sPos m % twoR) := by
      dsimp only [Bm]
      rw [show C ^ (N - 1) = B₀ from rfl, hB0_eq, hsm_eq]
      exact digits_sum_two_terms hb hp_lt hd0_lt hd1_pos hd1_lt
    rw [hsum_m, hsum0, Nat.cast_add, add_sub_cancel_left]
  -- Define `β r = 2 * α r / (C^(2^r) - 1)` and extract the homogeneous linear system.
  let β (r : Fin (M + 1)) : ℂ :=
    2 * α r / (((C ^ (2 ^ r.val) : ℕ) : ℂ) - 1)
  have hsys : ∀ m : Fin (M + 1),
      ∑ r : Fin (M + 1), β r * ((C ^ (sPos m % 2 ^ r.val) : ℕ) : ℂ) = 0 := by
    intro m
    have hdiff : refinementSpikeSlope C M α B₀ - refinementSpikeSlope C M α (Bm m) =
        ∑ r : Fin (M + 1), β r * ((C ^ (sPos m % 2 ^ r.val) : ℕ) : ℂ) := by
      unfold refinementSpikeSlope
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      have hb_ne : (((C ^ (2 ^ r.val) : ℕ) : ℂ) - 1) ≠ 0 := by
        have hb1 : 1 < C ^ (2 ^ r.val) := one_lt_pow₀ hC (by positivity)
        exact sub_ne_zero.mpr (by exact_mod_cast hb1.ne')
      have hd := hdig_diff m r
      dsimp only [β]
      field_simp [hb_ne]
      linear_combination 2 * α r * hd
    rw [← hdiff, hzero0, hzerom m, sub_self]
  -- Prove by upward induction on `k ≤ M + 1` that `∑_{r : k ≤ r.val} β r = 0`.
  have htail : ∀ k : ℕ, k ≤ M + 1 →
      (∑ r ∈ Finset.univ.filter (fun r : Fin (M + 1) => k ≤ r.val), β r) = 0 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · have huniv : Finset.univ.filter (fun r : Fin (M + 1) => 0 ≤ r.val) = Finset.univ :=
        Finset.filter_true_of_mem fun _ _ => Nat.zero_le _
      rw [huniv]
      have hm0 := hsys ⟨0, Nat.succ_pos M⟩
      simpa only [sPos, ↓reduceIte, Nat.zero_mod, pow_zero, Nat.cast_one, mul_one] using hm0
    · rcases eq_or_lt_of_le hk with rfl | hk_lt
      · have hemp : Finset.univ.filter (fun r : Fin (M + 1) => M + 1 ≤ r.val) = ∅ := by
          ext r; simp [Nat.not_le.mpr r.isLt]
        rw [hemp, Finset.sum_empty]
      · -- `1 ≤ k ≤ M`: subtract row `0` from row `k`.
        have hsum_all : (∑ r : Fin (M + 1), β r) = 0 := by
          have hm0 := hsys ⟨0, Nat.succ_pos M⟩
          simpa only [sPos, ↓reduceIte, Nat.zero_mod, pow_zero, Nat.cast_one, mul_one] using hm0
        have hmk := hsys ⟨k, hk_lt⟩
        have hsplit : (∑ r : Fin (M + 1),
            β r * (((C ^ (sPos ⟨k, hk_lt⟩ % 2 ^ r.val) : ℕ) : ℂ) - 1)) = 0 := by
          calc (∑ r : Fin (M + 1), β r * (((C ^ (sPos ⟨k, hk_lt⟩ % 2 ^ r.val) : ℕ) : ℂ) - 1))
              = (∑ r : Fin (M + 1), β r * ((C ^ (sPos ⟨k, hk_lt⟩ % 2 ^ r.val) : ℕ) : ℂ)) -
                  ∑ r : Fin (M + 1), β r := by
                rw [← Finset.sum_sub_distrib]
                exact Finset.sum_congr rfl fun r _ => by ring
            _ = 0 := by rw [hmk, hsum_all, sub_self]
        have hs_k : sPos ⟨k, hk_lt⟩ = 2 ^ (k - 1) := by
          dsimp only [sPos]; simp [hk_pos.ne']
        have hterm : ∀ r : Fin (M + 1),
            β r * (((C ^ (sPos ⟨k, hk_lt⟩ % 2 ^ r.val) : ℕ) : ℂ) - 1) =
              if k ≤ r.val then β r * (((C ^ (2 ^ (k - 1)) : ℕ) : ℂ) - 1) else 0 := by
          intro r
          rw [hs_k]
          split_ifs with hkr
          · have hlt_pow : 2 ^ (k - 1) < 2 ^ r.val :=
              (Nat.pow_lt_pow_iff_right (by norm_num)).mpr (by omega)
            rw [Nat.mod_eq_of_lt hlt_pow]
          · have hdvd : 2 ^ r.val ∣ 2 ^ (k - 1) :=
              Nat.pow_dvd_pow 2 (by omega)
            rw [Nat.mod_eq_zero_of_dvd hdvd, pow_zero, Nat.cast_one, sub_self, mul_zero]
        simp_rw [hterm] at hsplit
        rw [← Finset.sum_filter, ← Finset.sum_mul] at hsplit
        have hck_ne : (((C ^ (2 ^ (k - 1)) : ℕ) : ℂ) - 1) ≠ 0 := by
          have hgt : 1 < C ^ (2 ^ (k - 1)) := one_lt_pow₀ hC (by positivity)
          exact sub_ne_zero.mpr (by exact_mod_cast hgt.ne')
        exact (mul_eq_zero.mp hsplit).resolve_right hck_ne
  -- Conclude `β r = 0` and hence `α r = 0` for every `r`.
  obtain ⟨r₀, hr₀_ne⟩ := hα
  have hβ0 : β r₀ = 0 := by
    have ht1 := htail r₀.val (le_of_lt r₀.isLt)
    have ht2 := htail (r₀.val + 1) r₀.isLt
    have hins : Finset.univ.filter (fun r : Fin (M + 1) => r₀.val ≤ r.val) =
        insert r₀ (Finset.univ.filter (fun r : Fin (M + 1) => r₀.val + 1 ≤ r.val)) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hle
        rcases eq_or_lt_of_le hle with heq | hlt
        · exact Or.inl (Fin.ext heq.symm)
        · exact Or.inr hlt
      · rintro (rfl | hlt) <;> omega
    have hnot_mem : r₀ ∉ Finset.univ.filter (fun r : Fin (M + 1) => r₀.val + 1 ≤ r.val) := by
      simp
    rw [hins, Finset.sum_insert hnot_mem, ht2, add_zero] at ht1
    exact ht1
  have hb_ne : (((C ^ (2 ^ r₀.val) : ℕ) : ℂ) - 1) ≠ 0 := by
    have hb1 : 1 < C ^ (2 ^ r₀.val) := one_lt_pow₀ hC (by positivity)
    exact sub_ne_zero.mpr (by exact_mod_cast hb1.ne')
  dsimp only [β] at hβ0
  have h2α : 2 * α r₀ = 0 := (div_eq_zero_iff.mp hβ0).resolve_right hb_ne
  exact hr₀_ne ((mul_eq_zero.mp h2α).resolve_left two_ne_zero)

/-- All-refinement spike impossibility theorem: for every `M ≥ 0` and every nonzero coefficient
tuple `α : Fin (M + 1) → ℂ`, there exists an explicit `2^(M+1)`-periodic base-`C` cutoff sequence
`X_K` along which `∑_{r=0}^M α_r renormalizedCutoff t (j + r) X_K w - limit` grows with nonzero
asymptotic coefficient `refinementSpikeSlope C M α B` against `(K + 1) X_K^(-w)`. -/
theorem exists_periodic_spike_for_refinement_combination
    (t : ExceptionalTime) (j M : ℕ) {α : Fin (M + 1) → ℂ}
    (hα : ∃ r : Fin (M + 1), α r ≠ 0) {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    let C := (tailRadix t j).val
    let N := 2 ^ (M + 1)
    ∃ B : ℕ, C ^ (N - 1) ≤ B ∧ B < C ^ N ∧ refinementSpikeSlope C M α B ≠ 0 ∧
      Tendsto (fun K : ℕ =>
        ((∑ r : Fin (M + 1),
            α r * renormalizedCutoff t (j + r.val) (periodicCutoff (C ^ N) B (K + 1)) w) -
          ∑ r : Fin (M + 1),
            α r * (2 * heat w (tailRadix t (j + r.val)) * riemannZeta w /
              (1 - heat w (tailRadix t (j + r.val))))) /
          (((K + 1 : ℕ) : ℂ) * ((periodicCutoff (C ^ N) B (K + 1) : ℕ) : ℂ) ^ (-w)))
        atTop (𝓝 (refinementSpikeSlope C M α B)) := by
  dsimp only
  set C := (tailRadix t j).val
  have hC1 : 1 < C := radix_gt_one t j
  set N := 2 ^ (M + 1)
  obtain ⟨B, hBlo, hBhi, hslope_ne⟩ := exists_block_refinementSpikeSlope_ne_zero hC1 hα
  refine ⟨B, hBlo, hBhi, hslope_ne, ?_⟩
  let Xseq (K : ℕ) : ℕ := periodicCutoff (C ^ N) B (K + 1)
  -- For every `K` and `r`, `Xseq K` has exact linear `digitImbalance` in base `C^(2^r)`.
  have hX_pos_1 : ∀ K : ℕ, 1 ≤ Xseq K := by
    intro K
    obtain ⟨hlo, _⟩ := periodicCutoff_bounds hC1 (Nat.one_le_pow _ 2 (by norm_num))
      hBlo hBhi (Nat.succ_pos K)
    exact (Nat.one_le_pow _ C (by omega)).trans hlo
  have hdimb_sum : ∀ K : ℕ,
      (∑ r : Fin (M + 1),
          α r * ((digitImbalance (tailRadix t (j + r.val)).val (Xseq K) : ℂ) *
            ((Xseq K : ℕ) : ℂ) ^ (-w))) =
        refinementSpikeSlope C M α B * (((K + 1 : ℕ) : ℂ) * ((Xseq K : ℕ) : ℂ) ^ (-w)) := by
    intro K
    unfold refinementSpikeSlope
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    set b := C ^ (2 ^ r.val)
    set Q := 2 ^ (M + 1 - r.val)
    have hb1 : 1 < b := one_lt_pow₀ hC1 (by positivity)
    have hQ1 : 1 ≤ Q := Nat.one_le_pow _ 2 (by norm_num)
    have hQ_mul : 2 ^ r.val * Q = N := by
      dsimp only [Q, N]; rw [← pow_add, show r.val + (M + 1 - r.val) = M + 1 by omega]
    have hbQ : b ^ Q = C ^ N := by dsimp only [b]; rw [← pow_mul, hQ_mul]
    have hBlo_r : b ^ (Q - 1) ≤ B := by
      have hexp : 2 ^ r.val * (Q - 1) ≤ N - 1 := by
        have hpos2r : 1 ≤ 2 ^ r.val := Nat.one_le_pow _ 2 (by norm_num)
        have h1 : 2 ^ r.val * (Q - 1) + 2 ^ r.val = N := by
          calc 2 ^ r.val * (Q - 1) + 2 ^ r.val = 2 ^ r.val * ((Q - 1) + 1) := by ring
            _ = N := by rw [Nat.sub_add_cancel hQ1, hQ_mul]
        omega
      calc b ^ (Q - 1) = C ^ (2 ^ r.val * (Q - 1)) := (pow_mul C _ _).symm
        _ ≤ C ^ (N - 1) := Nat.pow_le_pow_right (by omega) hexp
        _ ≤ B := hBlo
    have hBhi_r : B < b ^ Q := hbQ.symm ▸ hBhi
    have hd := digitImbalance_periodicCutoff hb1 hQ1 hBlo_r hBhi_r (Nat.succ_pos K)
    have hrad : (tailRadix t (j + r.val)).val = b := tailRadix_add_pow_two t j r.val
    dsimp only [Xseq]
    rw [hrad, ← hbQ, hd]
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  -- Bound the remainder after subtracting `digitImbalance` by `const / (K + 1) → 0`.
  let Etotal : ℝ := ∑ r : Fin (M + 1), ‖α r‖ * digitImbalanceErrorConst t (j + r.val) w
  let rem (K : ℕ) : ℂ :=
    ((∑ r : Fin (M + 1),
        α r * digitBalancedCutoff t (j + r.val) (Xseq K) w) -
      ∑ r : Fin (M + 1),
        α r * (2 * heat w (tailRadix t (j + r.val)) * riemannZeta w /
          (1 - heat w (tailRadix t (j + r.val))))) /
      (((K + 1 : ℕ) : ℂ) * ((Xseq K : ℕ) : ℂ) ^ (-w))
  have hrem0 : Tendsto rem atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h0 : Tendsto (fun K : ℕ => Etotal / ((K + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      have htop : Tendsto (fun K : ℕ => ((K + 1 : ℕ) : ℝ)) atTop atTop := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      exact tendsto_const_nhds.div_atTop htop
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
    refine Eventually.of_forall fun K => ?_
    have hX1 : 1 ≤ Xseq K := hX_pos_1 K
    have hXpos : (0 : ℝ) < Xseq K := Nat.cast_pos.mpr hX1
    have hnum_le : ‖(∑ r : Fin (M + 1), α r * digitBalancedCutoff t (j + r.val) (Xseq K) w) -
        ∑ r : Fin (M + 1), α r * (2 * heat w (tailRadix t (j + r.val)) * riemannZeta w /
          (1 - heat w (tailRadix t (j + r.val))))‖ ≤
        Etotal * ((Xseq K : ℕ) : ℝ) ^ (-w.re) := by
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      dsimp only [Etotal]
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun r _ => ?_
      rw [← mul_sub, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (norm_renormalizedCutoff_sub_digitImbalance_le t (j + r.val) hX1 hw hw1) (norm_nonneg _)
    have hXw_norm : ‖((Xseq K : ℕ) : ℂ) ^ (-w)‖ = ((Xseq K : ℕ) : ℝ) ^ (-w.re) := by
      rw [show ((Xseq K : ℕ) : ℂ) = (((Xseq K : ℕ) : ℝ) : ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hXpos, Complex.neg_re]
    have hrp_pos : 0 < ((Xseq K : ℕ) : ℝ) ^ (-w.re) := Real.rpow_pos_of_pos hXpos _
    have hK_pos : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
    dsimp only [rem]
    rw [norm_div, norm_mul, Complex.norm_natCast, hXw_norm]
    calc _ ≤ (Etotal * ((Xseq K : ℕ) : ℝ) ^ (-w.re)) /
            (((K + 1 : ℕ) : ℝ) * ((Xseq K : ℕ) : ℝ) ^ (-w.re)) :=
          div_le_div_of_nonneg_right hnum_le (mul_pos hK_pos hrp_pos).le
      _ = Etotal / ((K + 1 : ℕ) : ℝ) := by field_simp [hrp_pos.ne', hK_pos.ne']
  have hlim := hrem0.add (tendsto_const_nhds (x := refinementSpikeSlope C M α B))
  rw [zero_add] at hlim
  refine hlim.congr fun K => ?_
  have hXpos : (0 : ℝ) < Xseq K := Nat.cast_pos.mpr (hX_pos_1 K)
  have hXw_ne : ((Xseq K : ℕ) : ℂ) ^ (-w) ≠ 0 := by
    rw [← norm_pos_iff, show ((Xseq K : ℕ) : ℂ) = (((Xseq K : ℕ) : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
    exact Real.rpow_pos_of_pos hXpos _
  have hK_ne : ((K + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero K)
  have hsplit_sum : (∑ r : Fin (M + 1), α r * renormalizedCutoff t (j + r.val) (Xseq K) w) =
      (∑ r : Fin (M + 1), α r * digitBalancedCutoff t (j + r.val) (Xseq K) w) +
        refinementSpikeSlope C M α B * (((K + 1 : ℕ) : ℂ) * ((Xseq K : ℕ) : ℂ) ^ (-w)) := by
    rw [← hdimb_sum K, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold digitBalancedCutoff
    ring
  dsimp only [rem, Xseq] at hsplit_sum ⊢
  rw [hsplit_sum]
  field_simp [hK_ne, hXw_ne]
  ring

/-- Corollary at `ζ` zeros: no nonzero finite linear combination of refinements
`renormalizedCutoff t (j + r) X w` (`0 ≤ r ≤ M`) can decay as `o(X^(-Re w) log X)` across all `X`. -/
theorem exists_zeta_zero_log_spike_for_refinement_combination
    (t : ExceptionalTime) (j M : ℕ) {α : Fin (M + 1) → ℂ}
    (hα : ∃ r : Fin (M + 1), α r ≠ 0) {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1)
    (hz : riemannZeta w = 0) :
    let C := (tailRadix t j).val
    let N := 2 ^ (M + 1)
    ∃ B : ℕ, C ^ (N - 1) ≤ B ∧ B < C ^ N ∧ refinementSpikeSlope C M α B ≠ 0 ∧
      Tendsto (fun K : ℕ =>
        (∑ r : Fin (M + 1),
          α r * renormalizedCutoff t (j + r.val) (periodicCutoff (C ^ N) B (K + 1)) w) /
          (((K + 1 : ℕ) : ℂ) * ((periodicCutoff (C ^ N) B (K + 1) : ℕ) : ℂ) ^ (-w)))
        atTop (𝓝 (refinementSpikeSlope C M α B)) := by
  dsimp only
  obtain ⟨B, hBlo, hBhi, hne, hlim⟩ :=
    exists_periodic_spike_for_refinement_combination t j M hα hw hw1
  refine ⟨B, hBlo, hBhi, hne, ?_⟩
  simpa only [hz, mul_zero, zero_div, Finset.sum_const_zero, sub_zero] using hlim

#print axioms tailRadix_add_pow_two
#print axioms digitImbalance_periodicCutoff
#print axioms exists_block_refinementSpikeSlope_ne_zero
#print axioms exists_periodic_spike_for_refinement_combination
#print axioms exists_zeta_zero_log_spike_for_refinement_combination

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation
