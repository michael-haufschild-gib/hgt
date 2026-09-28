import GaloisForLFunctions.RHTower.Sieve.HeathBrownLemma34PerronPoly

/-!
# The prime-power amplifier of Matomäki–Teräväinen §5.3

For a finite set `B` of primes in `(P, 2P]` and `k ≥ 1`, the amplifier
`𝓜(s) = (∑_{p ∈ B} p^{-s})^k / k! = ∑_m ε_m m^{-s}` has `|ε_m| ≤ 1` and support in
`(P^k, (2P)^k]`.  With `k = ⌊log X / log 2P⌋` and `(log X)^a ≤ P ≤ (log X)^{6/5}` (`a > 1`):

* `(2P)^k ≤ X < (2P)^{k+1}`, so `M = P^k ≥ X^{1-η}` eventually;
* `k! · |supp 𝓜| ≤ (P+k)^k ≤ M X^η` eventually (stars and bars, `k²/P = o(log X)`);
* `k! ≤ M^{1/a}` (`k ≤ log X ≤ P^{1/a}`);
* if `|∑_{p∈B} p^{-1-it}| ≥ P^{-ε/10}` then `1 ≤ k!² M^{ε/5} |𝓜(1+it)|²`.
-/

namespace RHTower.Sieve

open Finset Filter Topology

noncomputable section

/-- Normalized amplifier coefficients `c_k(m)/k!`. -/
def primeSetAmplifierCoeff (B : Finset ℕ) (k m : ℕ) : ℂ :=
  (primeSetCount B k m : ℂ) / (k.factorial : ℂ)

theorem mem_primeSetSupport_of_amplifierCoeff_ne_zero {B : Finset ℕ} {k m : ℕ}
    (h : primeSetAmplifierCoeff B k m ≠ 0) : m ∈ primeSetSupport B k := by
  by_contra hm
  apply h
  simp [primeSetAmplifierCoeff, primeSetCount_eq_zero_of_not_mem hm]

theorem norm_primeSetAmplifierCoeff_le_one {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) (k m : ℕ) :
    ‖primeSetAmplifierCoeff B k m‖ ≤ 1 := by
  rw [primeSetAmplifierCoeff, norm_div, Complex.norm_natCast, Complex.norm_natCast,
    div_le_one (by exact_mod_cast k.factorial_pos)]
  exact_mod_cast primeSetCount_le_factorial hB k m

/-- The amplifier as a truncated Dirichlet polynomial on the one-line. -/
theorem perronPoly_primeSetAmplifierCoeff {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {k K : ℕ}
    (hK : ∀ m ∈ primeSetSupport B k, m ≤ K) (t : ℝ) :
    perronPoly (primeSetAmplifierCoeff B k) K 1 t =
      (∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) ^ k / k.factorial := by
  rw [sum_cpow_pow_eq_sum_primeSetCount, perronPoly, Finset.sum_div]
  have hsub : primeSetSupport B k ⊆ Finset.Icc 1 K := fun m hm =>
    Finset.mem_Icc.2 ⟨pos_of_mem_primeSetSupport hB hm, hK m hm⟩
  rw [← Finset.sum_subset hsub fun n _ hn => by
    rw [primeSetAmplifierCoeff, primeSetCount_eq_zero_of_not_mem hn]; simp]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [primeSetAmplifierCoeff]
  ring

theorem card_filter_primeSetAmplifierCoeff_le (B : Finset ℕ) (k K : ℕ) :
    ((Finset.Icc 1 K).filter fun m => primeSetAmplifierCoeff B k m ≠ 0).card ≤
      (primeSetSupport B k).card :=
  Finset.card_le_card fun _ hm =>
    mem_primeSetSupport_of_amplifierCoeff_ne_zero (Finset.mem_filter.1 hm).2

/-- A set of naturals in `(P, 2P]` has at most `P + 1` elements. -/
theorem card_le_of_subset_Ioc_real {B : Finset ℕ} {P : ℝ} (hP : 0 ≤ P)
    (hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) : (B.card : ℝ) ≤ P + 1 := by
  have hsub : B ⊆ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊ := fun p hp =>
    Finset.mem_Ioc.2 ⟨(Nat.floor_lt hP).2 (hB p hp).1, Nat.le_floor (hB p hp).2⟩
  have h := Finset.card_le_card hsub
  rw [Nat.card_Ioc] at h
  have h1 : ((⌊2 * P⌋₊ - ⌊P⌋₊ : ℕ) : ℝ) ≤ P + 1 := by
    rcases le_total ⌊2 * P⌋₊ ⌊P⌋₊ with hle | hle
    · rw [Nat.sub_eq_zero_of_le hle]; push_cast; linarith
    · rw [Nat.cast_sub hle]
      have ha := Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 * P)
      have hb := Nat.lt_floor_add_one P
      linarith
  exact (Nat.cast_le.2 h).trans h1

/-- Stars and bars against the factorial: `k! · |supp| ≤ (P + k)^k`. -/
theorem factorial_mul_card_primeSetSupport_le {B : Finset ℕ} {P : ℝ} (hP : 0 ≤ P)
    (hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) (k : ℕ) :
    (k.factorial : ℝ) * (primeSetSupport B k).card ≤ (P + k) ^ k := by
  rw [mul_comm]
  refine (card_primeSetSupport_mul_factorial_le B k).trans ?_
  refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ k
  have hc := card_le_of_subset_Ioc_real hP hB
  rcases Nat.eq_zero_or_pos (B.card + k) with h0 | hpos
  · rw [show B.card + k - 1 = 0 by omega]; push_cast; positivity
  · rw [Nat.cast_sub (by omega)]; push_cast; linarith

/-- The amplifier degree `k = ⌊log X / log 2P⌋`. -/
def amplifierDegree (X P : ℝ) : ℕ := ⌊Real.log X / Real.log (2 * P)⌋₊

theorem log_two_mul_pos {P : ℝ} (hP : 1 ≤ P) : 0 < Real.log (2 * P) :=
  Real.log_pos (by linarith)

theorem one_le_amplifierDegree {X P : ℝ} (hP : 1 ≤ P) (hX : 2 * P ≤ X) :
    1 ≤ amplifierDegree X P := by
  rw [amplifierDegree, Nat.one_le_floor_iff, one_le_div (log_two_mul_pos hP)]
  exact Real.log_le_log (by linarith) hX

theorem two_mul_pow_amplifierDegree_le {X P : ℝ} (hP : 1 ≤ P) (hX : 1 ≤ X) :
    (2 * P) ^ amplifierDegree X P ≤ X := by
  have hl := log_two_mul_pos hP
  have hk : (amplifierDegree X P : ℝ) ≤ Real.log X / Real.log (2 * P) :=
    Nat.floor_le (div_nonneg (Real.log_nonneg hX) hl.le)
  rw [le_div_iff₀ hl] at hk
  have h2P : 0 < 2 * P := by linarith
  calc (2 * P) ^ amplifierDegree X P
      = Real.exp (Real.log ((2 * P) ^ amplifierDegree X P)) := (Real.exp_log (pow_pos h2P _)).symm
    _ = Real.exp (amplifierDegree X P * Real.log (2 * P)) := by rw [Real.log_pow]
    _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.2 hk
    _ = X := Real.exp_log (by linarith)

theorem lt_two_mul_pow_amplifierDegree_succ {X P : ℝ} (hP : 1 ≤ P) (hX : 0 < X) :
    X < (2 * P) ^ (amplifierDegree X P + 1) := by
  have hl := log_two_mul_pos hP
  have hk := Nat.lt_floor_add_one (Real.log X / Real.log (2 * P))
  rw [div_lt_iff₀ hl] at hk
  have h2P : 0 < 2 * P := by linarith
  calc X = Real.exp (Real.log X) := (Real.exp_log hX).symm
    _ < Real.exp (((amplifierDegree X P + 1 : ℕ) : ℝ) * Real.log (2 * P)) :=
        Real.exp_lt_exp.2 (by rw [amplifierDegree]; push_cast; linarith)
    _ = (2 * P) ^ (amplifierDegree X P + 1) := by
        rw [← Real.log_pow, Real.exp_log (pow_pos h2P _)]

theorem amplifierDegree_le_log {X P : ℝ} (hP : Real.exp 1 ≤ 2 * P) (hX : 1 ≤ X) :
    (amplifierDegree X P : ℝ) ≤ Real.log X := by
  have hl1 : 1 ≤ Real.log (2 * P) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hP
  have hl := (zero_lt_one.trans_le hl1)
  have hk : (amplifierDegree X P : ℝ) ≤ Real.log X / Real.log (2 * P) :=
    Nat.floor_le (div_nonneg (Real.log_nonneg hX) hl.le)
  exact hk.trans (div_le_self (Real.log_nonneg hX) hl1)

/-- `k! ≤ (P^k)^{1/a}` as soon as `k ≤ P^{1/a}`. -/
theorem factorial_le_pow_rpow_inv {P a : ℝ} (hP : 0 ≤ P) {k : ℕ}
    (hk : (k : ℝ) ≤ P ^ (1 / a)) :
    (k.factorial : ℝ) ≤ (P ^ k) ^ (1 / a) := by
  calc (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
    _ ≤ (P ^ (1 / a)) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hk k
    _ = (P ^ k) ^ (1 / a) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hP, ← Real.rpow_mul hP,
          mul_comm]

/-- On the set where the prime polynomial is not small, the amplifier is not small. -/
theorem one_le_factorial_sq_mul_rpow_mul_normSq {P ε : ℝ} (hP : 0 < P) {S : ℂ} {k : ℕ}
    (hS : P ^ (-ε / 10) ≤ ‖S‖) :
    1 ≤ (k.factorial : ℝ) ^ 2 * (P ^ k) ^ (ε / 5) * ‖S ^ k / k.factorial‖ ^ 2 := by
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [norm_div, norm_pow, Complex.norm_natCast, div_pow, ← pow_mul]
  have hpow : (P ^ (-ε / 10)) ^ (k * 2) ≤ ‖S‖ ^ (k * 2) :=
    pow_le_pow_left₀ (Real.rpow_nonneg hP.le _) hS _
  have hid : (P ^ k) ^ (ε / 5) * (P ^ (-ε / 10)) ^ (k * 2) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hP.le, ← Real.rpow_mul hP.le,
      ← Real.rpow_add hP]
    push_cast
    rw [show (k : ℝ) * (ε / 5) + -ε / 10 * ((k : ℝ) * 2) = 0 by ring, Real.rpow_zero]
  have hPk : 0 ≤ (P ^ k) ^ (ε / 5) := Real.rpow_nonneg (pow_nonneg hP.le k) _
  calc (1 : ℝ) = (P ^ k) ^ (ε / 5) * (P ^ (-ε / 10)) ^ (k * 2) := hid.symm
    _ ≤ (P ^ k) ^ (ε / 5) * ‖S‖ ^ (k * 2) := mul_le_mul_of_nonneg_left hpow hPk
    _ = (k.factorial : ℝ) ^ 2 * (P ^ k) ^ (ε / 5) * (‖S‖ ^ (k * 2) / (k.factorial : ℝ) ^ 2) := by
        field_simp

/-- The scalar facts about the amplifier degree, from four conditions on `L = log X`. -/
theorem amplifier_scale_of_log {X P a₀ η : ℝ} (hX : 1 < X) (ha₀ : 1 < a₀)
    (hL : Real.exp 1 ≤ Real.log X)
    (hc2 : Real.log 2 + 6 / 5 * Real.log (Real.log X) ≤ Real.log X)
    (hc3 : Real.log 2 * Real.log X / Real.log (Real.log X) + 2 * Real.log 2 +
      6 / 5 * Real.log (Real.log X) ≤ η * Real.log X)
    (hc4 : Real.log X ^ (2 - a₀) ≤ η * Real.log X)
    (hP₁ : Real.log X ^ a₀ ≤ P) (hP₂ : P ≤ Real.log X ^ (6 / 5 : ℝ)) :
    1 ≤ amplifierDegree X P ∧ X ^ (1 - η) ≤ P ^ amplifierDegree X P ∧
      (P + amplifierDegree X P) ^ amplifierDegree X P ≤ P ^ amplifierDegree X P * X ^ η ∧
      (amplifierDegree X P : ℝ) ≤ Real.log X := by
  set L := Real.log X with hLdef
  set k := amplifierDegree X P with hkdef
  have hX0 : 0 < X := by linarith
  have he1 : 1 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hL1 : 1 ≤ L := he1.trans hL
  have hL0 : 0 < L := by linarith
  have hlogL : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hL
  have hLP : L ≤ P := by
    calc L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
      _ ≤ L ^ a₀ := Real.rpow_le_rpow_of_exponent_le hL1 ha₀.le
      _ ≤ P := hP₁
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have h2P : Real.exp 1 ≤ 2 * P := by linarith
  have hLpow : L ^ (6 / 5 : ℝ) = Real.exp (6 / 5 * Real.log L) := by
    rw [Real.rpow_def_of_pos hL0, mul_comm]
  have h2PX : 2 * P ≤ X := by
    calc 2 * P ≤ 2 * L ^ (6 / 5 : ℝ) := by linarith
      _ = Real.exp (Real.log 2 + 6 / 5 * Real.log L) := by
          rw [hLpow, Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ Real.exp L := Real.exp_le_exp.2 hc2
      _ = X := Real.exp_log hX0
  have hk1 : 1 ≤ k := one_le_amplifierDegree hP1 h2PX
  have hkL : (k : ℝ) ≤ L := amplifierDegree_le_log h2P hX.le
  -- `k ≤ L / log L`
  have hlog2P : Real.log L ≤ Real.log (2 * P) := by
    calc Real.log L ≤ a₀ * Real.log L := le_mul_of_one_le_left (by linarith) ha₀.le
      _ = Real.log (L ^ a₀) := (Real.log_rpow hL0 a₀).symm
      _ ≤ Real.log P := Real.log_le_log (Real.rpow_pos_of_pos hL0 _) hP₁
      _ ≤ Real.log (2 * P) := Real.log_le_log hP0 (by linarith)
  have hk_ratio : (k : ℝ) ≤ L / Real.log L := by
    have hk : (k : ℝ) ≤ L / Real.log (2 * P) :=
      Nat.floor_le (div_nonneg hL0.le (log_two_mul_pos hP1).le)
    exact hk.trans (div_le_div_of_nonneg_left hL0.le (by linarith) hlog2P)
  -- `2P · 2^k ≤ X^η`
  have h2k : (2 : ℝ) ^ k ≤ Real.exp (Real.log 2 * L / Real.log L) := by
    calc (2 : ℝ) ^ k = Real.exp (k * Real.log 2) := by
          rw [← Real.log_pow, Real.exp_log (by positivity)]
      _ ≤ Real.exp (Real.log 2 * L / Real.log L) := by
          refine Real.exp_le_exp.2 ?_
          have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          calc (k : ℝ) * Real.log 2 ≤ L / Real.log L * Real.log 2 :=
                mul_le_mul_of_nonneg_right hk_ratio hl2
            _ = Real.log 2 * L / Real.log L := by ring
  have hXη : X ^ η = Real.exp (η * L) := by rw [Real.rpow_def_of_pos hX0, mul_comm]
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsmall : 2 * P * 2 ^ k ≤ X ^ η := by
    calc 2 * P * 2 ^ k ≤ Real.exp (Real.log 2 + 6 / 5 * Real.log L) *
          Real.exp (Real.log 2 * L / Real.log L) := by
          refine mul_le_mul ?_ h2k (by positivity) (Real.exp_pos _).le
          rw [Real.exp_add, Real.exp_log (by norm_num), ← hLpow]; linarith
      _ ≤ Real.exp (η * L) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
      _ = X ^ η := hXη.symm
  have hPk0 : 0 < P ^ k := pow_pos hP0 k
  have hlower : X ^ (1 - η) ≤ P ^ k := by
    have hXlt := lt_two_mul_pow_amplifierDegree_succ hP1 hX0
    rw [← hkdef] at hXlt
    have hsplit : (2 * P) ^ (k + 1) = 2 * P * 2 ^ k * P ^ k := by rw [pow_succ, mul_pow]; ring
    rw [hsplit] at hXlt
    have hXη0 : 0 < X ^ η := Real.rpow_pos_of_pos hX0 η
    rw [Real.rpow_sub hX0, Real.rpow_one, div_le_iff₀ hXη0]
    calc X ≤ 2 * P * 2 ^ k * P ^ k := hXlt.le
      _ ≤ X ^ η * P ^ k := mul_le_mul_of_nonneg_right hsmall hPk0.le
      _ = P ^ k * X ^ η := mul_comm _ _
  -- `(P + k)^k ≤ P^k X^η`
  have hstars : (P + k) ^ k ≤ P ^ k * X ^ η := by
    have h1 : P + k ≤ P * Real.exp (k / P) := by
      have := Real.add_one_le_exp (k / P)
      calc P + k = P * (k / P + 1) := by field_simp; ring
        _ ≤ P * Real.exp (k / P) := mul_le_mul_of_nonneg_left this hP0.le
    have hkk : (k : ℝ) * (k / P) ≤ η * L := by
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hsq : (k : ℝ) * (k / P) ≤ L * L / L ^ a₀ := by
        rw [mul_div_assoc']
        exact div_le_div₀ (by positivity) (mul_le_mul hkL hkL hk0 hL0.le)
          (Real.rpow_pos_of_pos hL0 _) hP₁
      have hpow : L * L / L ^ a₀ = L ^ (2 - a₀) := by
        rw [Real.rpow_sub hL0, Real.rpow_two, sq]
      linarith
    calc (P + k) ^ k ≤ (P * Real.exp (k / P)) ^ k :=
          pow_le_pow_left₀ (by positivity) h1 k
      _ = P ^ k * Real.exp (k * (k / P)) := by rw [mul_pow, ← Real.exp_nat_mul]
      _ ≤ P ^ k * Real.exp (η * L) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hkk) hPk0.le
      _ = P ^ k * X ^ η := by rw [hXη]
  exact ⟨hk1, hlower, hstars, hkL⟩

/-- **The amplifier scale, eventually.**  For `a₀ > 1`, `η > 0`, eventually in `X`, every
`P ∈ [(log X)^{a₀}, (log X)^{6/5}]` has `k = ⌊log X/log 2P⌋ ≥ 1`, `X^{1-η} ≤ P^k`,
`(P+k)^k ≤ P^k X^η` and `k ≤ log X`. -/
theorem eventually_amplifier_scale {a₀ η : ℝ} (ha₀ : 1 < a₀) (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop, ∀ P : ℝ, Real.log X ^ a₀ ≤ P → P ≤ Real.log X ^ (6 / 5 : ℝ) →
      1 ≤ amplifierDegree X P ∧ X ^ (1 - η) ≤ P ^ amplifierDegree X P ∧
        (P + amplifierDegree X P) ^ amplifierDegree X P ≤ P ^ amplifierDegree X P * X ^ η ∧
        (amplifierDegree X P : ℝ) ≤ Real.log X := by
  have hlo := Real.isLittleO_log_id_atTop
  have hL : ∀ᶠ L : ℝ in atTop, Real.exp 1 ≤ L ∧
      Real.log 2 + 6 / 5 * Real.log L ≤ L ∧
      Real.log 2 * L / Real.log L + 2 * Real.log 2 + 6 / 5 * Real.log L ≤ η * L ∧
      L ^ (2 - a₀) ≤ η * L := by
    have hb1 := hlo.bound (c := 5 / 12) (by norm_num)
    have hb2 := hlo.bound (c := 5 * η / 18) (by positivity)
    have hlogbig : ∀ᶠ L : ℝ in atTop, 3 * Real.log 2 / η ≤ Real.log L :=
      Real.tendsto_log_atTop.eventually_ge_atTop _
    have hrpow : ∀ᶠ L : ℝ in atTop, L ^ (-(a₀ - 1)) ≤ η :=
      (tendsto_rpow_neg_atTop (by linarith : 0 < a₀ - 1)).eventually (ge_mem_nhds hη)
    filter_upwards [hb1, hb2, hlogbig, hrpow, eventually_ge_atTop (Real.exp 1),
      eventually_ge_atTop (2 * Real.log 2), eventually_ge_atTop (6 * Real.log 2 / η),
      eventually_gt_atTop (0 : ℝ)]
      with L h1 h2 h3 h4 h5 h6 h7 h8
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have he1 : 1 ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have hlogL : 1 ≤ Real.log L := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) h5
    have hlogL0 : 0 ≤ Real.log L := by linarith
    rw [Real.norm_of_nonneg hlogL0, id, Real.norm_of_nonneg h8.le] at h1 h2
    refine ⟨h5, by linarith, ?_, ?_⟩
    · have ht1 : Real.log 2 * L / Real.log L ≤ η * L / 3 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        rw [div_le_iff₀ hη] at h3
        nlinarith
      have ht2 : 2 * Real.log 2 ≤ η * L / 3 := by
        rw [div_le_iff₀ hη] at h7
        linarith
      nlinarith
    · have : L ^ (2 - a₀) = L ^ (-(a₀ - 1)) * L := by
        rw [← Real.rpow_add_one h8.ne']; ring_nf
      rw [this]
      exact mul_le_mul_of_nonneg_right h4 h8.le
  filter_upwards [Real.tendsto_log_atTop.eventually hL, eventually_gt_atTop (1 : ℝ)]
    with X ⟨h1, h2, h3, h4⟩ hX P hP₁ hP₂
  exact amplifier_scale_of_log hX ha₀ h1 h2 h3 h4 hP₁ hP₂

end

end RHTower.Sieve
