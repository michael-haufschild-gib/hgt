import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIICellBounds
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedDivisorMoment

/-!
# The Type-II factors of Matomäki–Teräväinen §5.3 as Perron polynomials

For a Proposition-2.2 Type-II datum, with `F₁` the short prime-block factor and `F₂` the long
factor on `(M₂, 2M₂]`:

* at the paper width the block dilation is `(1+δ)^R ≤ 2`;
* `F₁^5` is the Perron polynomial of the fifth convolution power, supported on
  `(M₁^5, (2M₁)^5]` with coefficients `≤ d(n)^4`;
* `|F₂(1+it)| ≤ 3(1 + log 3M₂)^{31}` when `|β| ≤ d^5`;
* both are supported on explicit dyadic ranges `(N, N·2^R]` with `R = 6`, resp. `R = 2`;
* divisor powers are `≤ X^η` on `[1, X²]`, eventually;
* the Lemma 3.4 bracket times `k!²` is `≤ 128 X^{4η}(1 + X^{1/a}/N)` under the amplifier facts.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Filter Topology

noncomputable section

/-- **The amplified Heath-Brown bracket.**  With `k!·|𝓜| ≤ M X^η`, `k! ≤ M^{1/a}`,
`X^{1-η} ≤ M` and `1 ≤ a ≤ 4/3`, `k!²` times the Lemma 3.4 bracket is `≤ 128 X^{4η}(1 + X^{1/a}/N)`;
the `|𝓜|^{7/4}T^{3/4}` term is absorbed because `3/4 ≤ 1/a`. -/
theorem factorial_sq_mul_heathBrownLemma34Bracket_le {X M A F N L a η : ℝ} (hX : 1 ≤ X)
    (hM1 : 1 ≤ M) (hMlo : X ^ (1 - η) ≤ M) (hA : 0 ≤ A) (hF : 1 ≤ F)
    (hFA : F * A ≤ M * X ^ η) (hFM : F ≤ M ^ (1 / a)) (ha1 : 1 ≤ a) (ha43 : a ≤ 4 / 3)
    (hN : 1 ≤ N) (hL0 : 0 ≤ L) (hL : L ≤ 64 * X) (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    F ^ 2 * heathBrownLemma34Bracket A M N L X η ≤
      128 * X ^ (4 * η) * (1 + X ^ (1 / a) / N) := by
  unfold heathBrownLemma34Bracket
  have hX0 : 0 < X := by linarith
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hF0 : 0 < F := by linarith
  have ha0 : 0 < a := by linarith
  have hFM' : F / M ≤ X ^ (1 / a) * X ^ η / X := by
    have hMpow : M ^ (1 / a) / M = M ^ (1 / a - 1) := by
      rw [Real.rpow_sub hM0, Real.rpow_one]
    have hexp : 1 / a - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one ha0]; exact ha1
    have h1 : M ^ (1 / a - 1) ≤ (X ^ (1 - η)) ^ (1 / a - 1) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hX0 _) hMlo hexp
    have h3 : X ^ (1 / a) * X ^ η / X = X ^ (1 / a + η - 1) := by
      rw [Real.rpow_sub hX0, Real.rpow_add hX0, Real.rpow_one]
    have h2 : (X ^ (1 - η)) ^ (1 / a - 1) ≤ X ^ (1 / a) * X ^ η / X := by
      rw [← Real.rpow_mul hX0.le, h3]
      apply Real.rpow_le_rpow_of_exponent_le hX
      have : 0 ≤ η * (1 / a) := by positivity
      nlinarith
    calc F / M ≤ M ^ (1 / a) / M := div_le_div_of_nonneg_right hFM hM0.le
      _ = M ^ (1 / a - 1) := hMpow
      _ ≤ X ^ (1 / a) * X ^ η / X := h1.trans h2
  have hXη : 1 ≤ X ^ η := Real.one_le_rpow hX hη
  obtain ⟨E, hE⟩ : ∃ E, E = X ^ η := ⟨_, rfl⟩
  rw [← hE] at hFA hFM' hXη
  -- `(F A / M) ≤ E`
  have hr : F * A / M ≤ E := by rw [div_le_iff₀ hM0]; linarith
  have hr0 : 0 ≤ F * A / M := by positivity
  -- first term
  have t1 : F ^ 2 * (A / M) ^ 2 ≤ E ^ 2 := by
    have : F ^ 2 * (A / M) ^ 2 = (F * A / M) ^ 2 := by ring
    rw [this]; exact pow_le_pow_left₀ hr0 hr 2
  -- second term: `F² A X / (M² N) = (F A / M)(F/M) X / N ≤ E² X^{1/a}/N`
  have t2 : F ^ 2 * (A * X / (M ^ 2 * N)) ≤ E ^ 2 * (X ^ (1 / a) / N) := by
    have heq : F ^ 2 * (A * X / (M ^ 2 * N)) = (F * A / M) * (F / M) * X / N := by
      field_simp
    rw [heq]
    have hFM0 : 0 ≤ F / M := by positivity
    calc F * A / M * (F / M) * X / N ≤ E * (X ^ (1 / a) * E / X) * X / N := by
          gcongr
      _ = E ^ 2 * (X ^ (1 / a) / N) := by field_simp
  -- third term: `F² A^{7/4} X^{3/4}/(M² N) ≤ E^{7/4} X^{3/4}/N ≤ E² X^{1/a}/N`
  have t3 : F ^ 2 * (A ^ (7 / 4 : ℝ) * X ^ (3 / 4 : ℝ) / (M ^ 2 * N)) ≤
      E ^ 2 * (X ^ (1 / a) / N) := by
    have hA74 : F ^ 2 * A ^ (7 / 4 : ℝ) / M ^ 2 ≤ E ^ (7 / 4 : ℝ) := by
      -- `F² A^{7/4}/M² = (FA/M)^{7/4} · (F/M)^{1/4}` and `F ≤ M`
      have hFleM : F ≤ M := by
        calc F ≤ M ^ (1 / a) := hFM
          _ ≤ M ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1
              (by rw [div_le_one ha0]; exact ha1)
          _ = M := Real.rpow_one M
      have hsplit : F ^ 2 * A ^ (7 / 4 : ℝ) / M ^ 2 =
          (F * A / M) ^ (7 / 4 : ℝ) * (F / M) ^ (1 / 4 : ℝ) := by
        rw [Real.div_rpow (by positivity) hM0.le, Real.div_rpow hF0.le hM0.le,
          Real.mul_rpow hF0.le hA]
        have hF2 : F ^ 2 = F ^ (7 / 4 : ℝ) * F ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_add hF0]; norm_num
        have hM2 : M ^ 2 = M ^ (7 / 4 : ℝ) * M ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_add hM0]; norm_num
        rw [hF2, hM2]
        field_simp
      rw [hsplit]
      have hq : (F / M) ^ (1 / 4 : ℝ) ≤ 1 :=
        Real.rpow_le_one (by positivity) (by rw [div_le_one hM0]; exact hFleM) (by norm_num)
      calc (F * A / M) ^ (7 / 4 : ℝ) * (F / M) ^ (1 / 4 : ℝ) ≤ (F * A / M) ^ (7 / 4 : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hq (by positivity)
        _ ≤ E ^ (7 / 4 : ℝ) := by
            rw [mul_one]; exact Real.rpow_le_rpow hr0 hr (by norm_num)
    have hE74 : E ^ (7 / 4 : ℝ) ≤ E ^ 2 := by
      rw [show (E ^ 2 : ℝ) = E ^ (2 : ℝ) by norm_cast]
      exact Real.rpow_le_rpow_of_exponent_le hXη (by norm_num)
    have hX34 : X ^ (3 / 4 : ℝ) ≤ X ^ (1 / a) := by
      apply Real.rpow_le_rpow_of_exponent_le hX
      rw [le_div_iff₀ ha0]; linarith
    have heq : F ^ 2 * (A ^ (7 / 4 : ℝ) * X ^ (3 / 4 : ℝ) / (M ^ 2 * N)) =
        (F ^ 2 * A ^ (7 / 4 : ℝ) / M ^ 2) * X ^ (3 / 4 : ℝ) / N := by
      field_simp
    rw [heq]
    calc F ^ 2 * A ^ (7 / 4 : ℝ) / M ^ 2 * X ^ (3 / 4 : ℝ) / N
        ≤ E ^ 2 * X ^ (1 / a) / N := by
          gcongr
          · exact hA74.trans hE74
      _ = E ^ 2 * (X ^ (1 / a) / N) := by ring
  -- the loss factor `(L X)^η ≤ 64 X^{2η}`
  have hLX : (L * X) ^ η ≤ 64 * E ^ 2 := by
    have h1 : (L * X) ^ η ≤ (64 * X ^ 2) ^ η :=
      Real.rpow_le_rpow (by positivity) (by nlinarith) hη
    have h2 : (64 * X ^ 2) ^ η = (64 : ℝ) ^ η * E ^ 2 := by
      rw [Real.mul_rpow (by norm_num) (by positivity), hE, ← Real.rpow_natCast,
        ← Real.rpow_mul hX0.le, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
      ring_nf
    have h3 : (64 : ℝ) ^ η ≤ 64 := by
      calc (64 : ℝ) ^ η ≤ 64 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hη1
        _ = 64 := Real.rpow_one 64
    rw [h2] at h1
    nlinarith [sq_nonneg E]
  have hE4 : X ^ (4 * η) = E ^ 4 := by
    rw [hE, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; ring_nf
  rw [hE4]
  have hbr0 : 0 ≤ X ^ (1 / a) / N := by positivity
  have hLX0 : 0 ≤ (L * X) ^ η := Real.rpow_nonneg (by positivity) _
  have hE1 : 1 ≤ E ^ 2 := one_le_pow₀ hXη
  calc F ^ 2 * ((A / M) ^ 2 + (L * X) ^ η *
        (A * X / (M ^ 2 * N) + A ^ (7 / 4 : ℝ) * X ^ (3 / 4 : ℝ) / (M ^ 2 * N)))
      = F ^ 2 * (A / M) ^ 2 + (L * X) ^ η * (F ^ 2 * (A * X / (M ^ 2 * N)) +
          F ^ 2 * (A ^ (7 / 4 : ℝ) * X ^ (3 / 4 : ℝ) / (M ^ 2 * N))) := by ring
    _ ≤ E ^ 2 + (64 * E ^ 2) * (E ^ 2 * (X ^ (1 / a) / N) + E ^ 2 * (X ^ (1 / a) / N)) := by
        gcongr
    _ ≤ 128 * E ^ 4 * (1 + X ^ (1 / a) / N) := by
        nlinarith [mul_nonneg (sq_nonneg E) hbr0, sq_nonneg (E ^ 2)]

/-- **Powers of a finitely supported arithmetic function.**  The Perron polynomial of `F^j` at
cutoff `K^j` is the `j`-th power of that of `F`. -/
theorem perronPoly_pow_arithmeticFunction (F : ArithmeticFunction ℂ) {K : ℕ}
    (hF : ∀ n, F n ≠ 0 → n ∈ Finset.Icc 1 K) (σ t : ℝ) (j : ℕ) :
    (∀ n, (F ^ j) n ≠ 0 → n ∈ Finset.Icc 1 (K ^ j)) ∧
      perronPoly (fun n => (F ^ j) n) (K ^ j) σ t = (perronPoly (fun n => F n) K σ t) ^ j := by
  induction j with
  | zero =>
    refine ⟨fun n hn => ?_, ?_⟩
    · rw [pow_zero] at hn ⊢
      by_contra hmem
      apply hn
      have : n ≠ 1 := fun h => hmem (by subst h; simp)
      simp [ArithmeticFunction.one_apply_ne this]
    · simp [perronPoly]
  | succ j ih =>
    obtain ⟨hsupp, hpoly⟩ := ih
    have hsupp' : ∀ n, (F ^ (j + 1)) n ≠ 0 → n ∈ Finset.Icc 1 (K ^ (j + 1)) := by
      intro n hn
      rw [pow_succ F j] at hn
      rw [pow_succ K j]
      exact convolution_mem_Icc_of_support_mul hsupp hF
        (arithmeticFunction_mul_eq_lseriesConvolution (F ^ j) F ▸ hn)
    refine ⟨hsupp', ?_⟩
    have h := perronPoly_arithmeticFunction_mul (F ^ j) F hsupp hF σ t
    rw [← pow_succ, ← pow_succ, hpoly] at h
    rw [h, pow_succ]

/-- Uniform divisor bounds of convolution powers: `|F^{j+1}| ≤ d^j` if `|F| ≤ 1`. -/
theorem MTUniformDivisorBounded.pow_succ_of_zero {F : ArithmeticFunction ℂ}
    (hF : MTUniformDivisorBounded 0 fun n => F n) (j : ℕ) :
    MTUniformDivisorBounded j fun n => (F ^ (j + 1)) n := by
  induction j with
  | zero => simpa using hF
  | succ j ih =>
    have := ih.arithmeticFunction_mul hF
    rw [← pow_succ] at this
    simpa using this

/-- Real-scale supports of convolution powers. -/
theorem MTRealScaleSupported.pow_succ {F : ArithmeticFunction ℂ} {L U : ℝ}
    (hF : MTRealScaleSupported F L U) (hL : 0 ≤ L) (j : ℕ) :
    MTRealScaleSupported (F ^ (j + 1)) (L ^ (j + 1)) (U ^ (j + 1)) := by
  induction j with
  | zero =>
    intro n hn
    simp only [zero_add, pow_one] at hn ⊢
    exact hF hn
  | succ j ih =>
    have h : MTRealScaleSupported (F ^ (j + 1) * F) (L ^ (j + 1) * L) (U ^ (j + 1) * U) :=
      @MTRealScaleSupported.mul _ _ _ _ _ _ ih hF (pow_nonneg hL _) hL
    rw [← _root_.pow_succ, ← _root_.pow_succ, ← _root_.pow_succ] at h
    intro n hn
    exact h hn

/-- **The block dilation at the paper width is at most two.** -/
theorem eventually_one_add_mtPaperWidth_pow_card_le_two {A : ℕ} (hA : 1 ≤ A) :
    ∀ᶠ X : ℝ in atTop, ∀ {Y z ε : ℝ}
      (data : MTTypeIIPieceData X Y (mtLowerCutoff X) z (mtPaperWidth A X) ε),
      z ≤ X → (1 + mtPaperWidth A X) ^ data.indices.card ≤ 2 := by
  have he : -((10 * A : ℕ) : ℝ) < 0 := by
    have : (0 : ℝ) < ((10 * A : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 10 * A)
    linarith
  have hlim := tendsto_logRpow_mul_logLogPow he 3
  filter_upwards [hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1),
    eventually_gt_atTop (1 : ℝ)] with X hsmall hlogX hX1
  intro Y z ε data hzX
  have hδ0 : 0 ≤ mtPaperWidth A X := data.δ_nonneg
  refine one_add_pow_le_two_of_nat_mul_le_half hδ0 _ ?_
  have hL0 : 0 < Real.log X := Real.log_pos hX1
  have hLL : 1 ≤ Real.log (Real.log X) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hlogX
  have hcut : 0 < mtLowerLogCutoff X := by unfold mtLowerLogCutoff; positivity
  have hz0 : Real.log (mtLowerCutoff X) = mtLowerLogCutoff X := by
    rw [mtLowerCutoff, Real.log_exp]
  have hR : (data.indices.card : ℝ) ≤ Real.log (Real.log X) ^ 3 := by
    have h1 := data.R_le
    rw [hz0] at h1
    have h2 : (data.indices.card : ℝ) ≤ ⌊Real.log z / mtLowerLogCutoff X⌋₊ := by exact_mod_cast h1
    refine h2.trans ?_
    rcases le_or_gt (Real.log z / mtLowerLogCutoff X) 0 with hneg | hpos
    · rw [Nat.floor_of_nonpos hneg]; push_cast; positivity
    · refine (Nat.floor_le hpos.le).trans ?_
      have hzpos : 0 < z :=
        (Real.rpow_pos_of_pos (by linarith) _).trans_le (data.M₁_mem.1.trans data.M₁_mem.2)
      have hlz : Real.log z ≤ Real.log X := Real.log_le_log hzpos hzX
      calc Real.log z / mtLowerLogCutoff X ≤ Real.log X / mtLowerLogCutoff X :=
            div_le_div_of_nonneg_right hlz hcut.le
        _ = Real.log (Real.log X) ^ 3 := by
            unfold mtLowerLogCutoff; field_simp
  calc (data.indices.card : ℝ) * mtPaperWidth A X
      ≤ Real.log (Real.log X) ^ 3 * mtPaperWidth A X := mul_le_mul_of_nonneg_right hR hδ0
    _ = Real.log X ^ (-((10 * A : ℕ) : ℝ)) * Real.log (Real.log X) ^ 3 := by
        rw [mtPaperWidth]; ring
    _ ≤ 1 / 2 := hsmall

/-- **Divisor powers are `X^{o(1)}` on `[1, X²]`.** -/
theorem eventually_card_divisors_pow_le_rpow (K : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop, ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X ^ 2 →
      (n.divisors.card : ℝ) ^ K ≤ X ^ η := by
  set η' : ℝ := η / (4 * ((K : ℝ) + 1)) with hη'
  have hη'0 : 0 < η' := by positivity
  set C := divisorBoundConst η' with hC
  have hC0 : 0 < C := divisorBoundConst_pos hη'0
  have hbig : ∀ᶠ X : ℝ in atTop, C ^ K ≤ X ^ (η / 2) :=
    (tendsto_rpow_atTop (by positivity : 0 < η / 2)).eventually_ge_atTop _
  filter_upwards [hbig, eventually_ge_atTop (1 : ℝ)] with X hXC hX1 n hn hnX
  have hX0 : 0 < X := by linarith
  have hd := card_divisors_le_rpow hη'0 hn.ne'
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnη : (n : ℝ) ^ η' ≤ X ^ (2 * η') := by
    calc (n : ℝ) ^ η' ≤ (X ^ 2) ^ η' := Real.rpow_le_rpow hn0 hnX hη'0.le
      _ = X ^ (2 * η') := by rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hd' : (n.divisors.card : ℝ) ≤ C * X ^ (2 * η') :=
    hd.trans (mul_le_mul_of_nonneg_left hnη hC0.le)
  have hexp : (K : ℝ) * (2 * η') ≤ η / 2 := by
    rw [hη']
    have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    rw [show (K : ℝ) * (2 * (η / (4 * ((K : ℝ) + 1)))) = η / 2 * ((K : ℝ) / ((K : ℝ) + 1)) by
      field_simp; ring]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one hK1).2 (by linarith))
  calc (n.divisors.card : ℝ) ^ K ≤ (C * X ^ (2 * η')) ^ K :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hd' K
    _ = C ^ K * X ^ ((K : ℝ) * (2 * η')) := by
        rw [mul_pow, ← Real.rpow_natCast (X ^ (2 * η')), ← Real.rpow_mul hX0.le, mul_comm (2 * η')]
    _ ≤ X ^ (η / 2) * X ^ (η / 2) :=
        mul_le_mul hXC (Real.rpow_le_rpow_of_exponent_le hX1 hexp) (by positivity) (by positivity)
    _ = X ^ η := by rw [← Real.rpow_add hX0]; ring_nf

/-- The long Type-II factor `∑_{M₂ < m ≤ 2M₂} β_m m^{-s}` on the line `Re s = σ`. -/
def mtTypeIILongFactor {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    (σ t : ℝ) : ℂ :=
  perronPoly (fun n => mtRealIntervalAF data.β data.M₂ (2 * data.M₂) n) ⌈2 * data.M₂⌉₊ σ t

theorem continuous_mtTypeIILongFactor {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    (σ : ℝ) : Continuous (mtTypeIILongFactor data σ) :=
  continuous_perronPoly _ _ σ

/-- Dyadic support of the long factor: `(⌊M₂⌋, 4⌊M₂⌋]`. -/
theorem mtTypeIILongFactor_coeff_support {X Y z₀ z δ ε : ℝ}
    (data : MTTypeIIPieceData X Y z₀ z δ ε) (hM₂ : 1 ≤ data.M₂) (n : ℕ)
    (hn : mtRealIntervalAF data.β data.M₂ (2 * data.M₂) n ≠ 0) :
    n ≤ ⌈2 * data.M₂⌉₊ ∧ ⌊data.M₂⌋₊ < n ∧ n ≤ ⌊data.M₂⌋₊ * 2 ^ 2 := by
  obtain ⟨hn0, hlo, hhi⟩ := mtRealIntervalAF_scaleSupported data.β data.M₂ (2 * data.M₂) hn
  have hfl := Nat.floor_le (by linarith : 0 ≤ data.M₂)
  have hfl1 := Nat.lt_floor_add_one data.M₂
  have hF1 : 1 ≤ ⌊data.M₂⌋₊ := Nat.le_floor (by exact_mod_cast hM₂)
  refine ⟨Nat.cast_le.1 (hhi.trans (Nat.le_ceil _)) |> fun h => by exact_mod_cast h, ?_, ?_⟩
  · exact_mod_cast hfl.trans_lt hlo
  · have h1 : (n : ℝ) < 2 * ((⌊data.M₂⌋₊ : ℝ) + 1) := by linarith
    have h2 : (n : ℝ) < ((2 * (⌊data.M₂⌋₊ + 1) : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_lt.1 h2
    omega

theorem norm_mtRealIntervalAF_le_of_uniform {α : ℕ → ℂ} {K : ℕ} (hα : MTUniformDivisorBounded K α)
    (L U : ℝ) (n : ℕ) :
    ‖mtRealIntervalAF α L U n‖ ≤ (n.divisors.card : ℝ) ^ K := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [mtRealIntervalAF]
  · exact hα.realInterval L U hn

/-- **The long factor is polylogarithmically bounded on the one-line.** -/
theorem norm_mtTypeIILongFactor_le {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    (hM₂ : 1 ≤ data.M₂) (hβ : MTUniformDivisorBounded 5 data.β) (t : ℝ) :
    ‖mtTypeIILongFactor data 1 t‖ ≤ 3 * (1 + Real.log (3 * data.M₂)) ^ 31 := by
  set K := ⌈2 * data.M₂⌉₊ with hK
  have hK1 : 1 ≤ K := by
    rw [hK]; exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hKle : (K : ℝ) ≤ 3 * data.M₂ := by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ 2 * data.M₂)
    rw [hK]; linarith
  have hM₂0 : 0 < data.M₂ := by linarith
  have hterm : ∀ n ∈ Finset.Icc 1 K,
      ‖mtRealIntervalAF data.β data.M₂ (2 * data.M₂) n *
        (n : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ ≤
        (n.divisors.card : ℝ) ^ 5 / data.M₂ := by
    intro n hn
    have hn1 := (Finset.mem_Icc.1 hn).1
    rw [norm_mul, norm_natCast_cpow_one_add_mul_I (by omega) t]
    by_cases hc : mtRealIntervalAF data.β data.M₂ (2 * data.M₂) n = 0
    · rw [hc, norm_zero, zero_mul]; positivity
    · obtain ⟨_, hlo, _⟩ := mtRealIntervalAF_scaleSupported data.β data.M₂ (2 * data.M₂) hc
      have hb := norm_mtRealIntervalAF_le_of_uniform hβ data.M₂ (2 * data.M₂) n
      calc ‖mtRealIntervalAF data.β data.M₂ (2 * data.M₂) n‖ * (1 / (n : ℝ))
          ≤ (n.divisors.card : ℝ) ^ 5 * (1 / data.M₂) :=
            mul_le_mul hb (one_div_le_one_div_of_le hM₂0 hlo.le) (by positivity) (by positivity)
        _ = (n.divisors.card : ℝ) ^ 5 / data.M₂ := by ring
  have hsum := sum_card_divisors_pow_le_polylog 5 K hK1
  norm_num at hsum
  have hlogK : Real.log K ≤ Real.log (3 * data.M₂) :=
    Real.log_le_log (by exact_mod_cast hK1) hKle
  have hlog0 : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK1)
  calc ‖mtTypeIILongFactor data 1 t‖
      ≤ ∑ n ∈ Finset.Icc 1 K, ‖mtRealIntervalAF data.β data.M₂ (2 * data.M₂) n *
          (n : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ := by
        unfold mtTypeIILongFactor perronPoly; exact norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 K, (n.divisors.card : ℝ) ^ 5 / data.M₂ := Finset.sum_le_sum hterm
    _ = (∑ n ∈ Finset.Icc 1 K, (n.divisors.card : ℝ) ^ 5) / data.M₂ := by rw [Finset.sum_div]
    _ ≤ (K : ℝ) * (1 + Real.log K) ^ 31 / data.M₂ :=
        div_le_div_of_nonneg_right hsum hM₂0.le
    _ ≤ 3 * data.M₂ * (1 + Real.log (3 * data.M₂)) ^ 31 / data.M₂ := by
        gcongr
    _ = 3 * (1 + Real.log (3 * data.M₂)) ^ 31 := by field_simp

/-- The short factor's coefficient function. -/
def mtTypeIIShortAF {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε) :
    ArithmeticFunction ℂ :=
  mtRealIntervalAF (mtTypeIIPrimeCoefficient data.indices data.block) data.M₁
    ((1 + δ) ^ data.indices.card * data.M₁)

theorem mtTypeIIPrimeFactor_eq_perronPoly_shortAF {X Y z₀ z δ ε : ℝ}
    (data : MTTypeIIPieceData X Y z₀ z δ ε) (σ t : ℝ) :
    mtTypeIIPrimeFactor data σ t =
      perronPoly (fun n => mtTypeIIShortAF data n) ⌈(1 + δ) ^ data.indices.card * data.M₁⌉₊ σ t :=
  rfl

/-- **The fifth power of the short factor** as a Perron polynomial. -/
theorem mtTypeIIPrimeFactor_pow_five {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    (σ t : ℝ) :
    mtTypeIIPrimeFactor data σ t ^ 5 =
      perronPoly (fun n => (mtTypeIIShortAF data ^ 5) n)
        (⌈(1 + δ) ^ data.indices.card * data.M₁⌉₊ ^ 5) σ t := by
  rw [mtTypeIIPrimeFactor_eq_perronPoly_shortAF]
  exact ((perronPoly_pow_arithmeticFunction _ (mtRealIntervalAF_support_nat _ _ _) σ t 5).2).symm

theorem mtTypeIIShortAF_pow_five_support_nat {X Y z₀ z δ ε : ℝ}
    (data : MTTypeIIPieceData X Y z₀ z δ ε) (n : ℕ) (hn : (mtTypeIIShortAF data ^ 5) n ≠ 0) :
    n ∈ Finset.Icc 1 (⌈(1 + δ) ^ data.indices.card * data.M₁⌉₊ ^ 5) :=
  (perronPoly_pow_arithmeticFunction _ (mtRealIntervalAF_support_nat _ _ _) 0 0 5).1 n hn

/-- Dyadic support of the fifth power: `(⌊M₁^5⌋, 64⌊M₁^5⌋]` when the dilation is `≤ 2`. -/
theorem mtTypeIIShortAF_pow_five_dyadic {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    (hM₁ : 1 ≤ data.M₁) (hdil : (1 + δ) ^ data.indices.card ≤ 2) (n : ℕ)
    (hn : (mtTypeIIShortAF data ^ 5) n ≠ 0) :
    n ≤ ⌈(1 + δ) ^ data.indices.card * data.M₁⌉₊ ^ 5 ∧ ⌊data.M₁ ^ 5⌋₊ < n ∧
      n ≤ ⌊data.M₁ ^ 5⌋₊ * 2 ^ 6 := by
  have hsupp : MTRealScaleSupported (mtTypeIIShortAF data ^ (4 + 1)) (data.M₁ ^ (4 + 1))
      (((1 + δ) ^ data.indices.card * data.M₁) ^ (4 + 1)) :=
    @MTRealScaleSupported.pow_succ _ _ _ (mtRealIntervalAF_scaleSupported _ _ _) (by linarith) 4
  obtain ⟨_, hlo, hhi⟩ := hsupp hn
  refine ⟨(Finset.mem_Icc.1 (mtTypeIIShortAF_pow_five_support_nat data n hn)).2, ?_, ?_⟩
  · have hfl := Nat.floor_le (by positivity : 0 ≤ data.M₁ ^ 5)
    exact_mod_cast hfl.trans_lt hlo
  · have hM5 : 1 ≤ data.M₁ ^ 5 := one_le_pow₀ hM₁
    have hF1 : 1 ≤ ⌊data.M₁ ^ 5⌋₊ := Nat.le_floor (by exact_mod_cast hM5)
    have hfl1 := Nat.lt_floor_add_one (data.M₁ ^ 5)
    have hup : ((1 + δ) ^ data.indices.card * data.M₁) ^ (4 + 1) ≤ 32 * data.M₁ ^ 5 := by
      rw [mul_pow, show (4 + 1 : ℕ) = 5 by rfl]
      have h32 : ((1 + δ) ^ data.indices.card) ^ 5 ≤ 2 ^ 5 :=
        pow_le_pow_left₀ (pow_nonneg (by linarith [data.δ_nonneg]) _) hdil 5
      have : (0 : ℝ) ≤ data.M₁ ^ 5 := by positivity
      nlinarith
    have h1 : (n : ℝ) < ((64 * ⌊data.M₁ ^ 5⌋₊ : ℕ) : ℝ) := by
      have hF1' : (1 : ℝ) ≤ ⌊data.M₁ ^ 5⌋₊ := by exact_mod_cast hF1
      push_cast
      calc (n : ℝ) ≤ 32 * data.M₁ ^ 5 := hhi.trans hup
        _ < 32 * ((⌊data.M₁ ^ 5⌋₊ : ℝ) + 1) := by linarith
        _ ≤ 64 * (⌊data.M₁ ^ 5⌋₊ : ℝ) := by linarith
    have := Nat.cast_lt.1 h1
    omega

/-- Coefficients of the fifth power are `≤ d(n)^4`. -/
theorem norm_mtTypeIIShortAF_pow_five_le {X Y z₀ z δ ε : ℝ} (data : MTTypeIIPieceData X Y z₀ z δ ε)
    (hprime : MTUniformDivisorBounded 0 (mtTypeIIPrimeCoefficient data.indices data.block))
    (n : ℕ) : ‖(mtTypeIIShortAF data ^ 5) n‖ ≤ (n.divisors.card : ℝ) ^ 4 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (MTUniformDivisorBounded.pow_succ_of_zero (hprime.realInterval _ _) 4) hn

end

end RHTower.Sieve
