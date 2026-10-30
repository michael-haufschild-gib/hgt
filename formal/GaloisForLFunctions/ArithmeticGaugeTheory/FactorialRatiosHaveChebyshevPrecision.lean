import GaloisForLFunctions.ArithmeticGaugeTheory.FactorialRatiosHaveBoundedMultiplicity
import GaloisForLFunctions.ArithmeticKreinLangerTheory.IntegralityProducesLinearCounts
import GaloisForLFunctions.RHTower.ThetaPrimeScheduleSpectralObservation
import GaloisForLFunctions.RHTower.XiMassShellPrimeMass
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Factorial ratios have Chebyshev precision

A producer for the primes of `(n, 2n]` is an integer `A_n` with `v_p(A_n) ≥ m` on them. The Bézout
ledger bounds its size from below by `m` times the mass of the window, so the *precision* of a
producer is its size divided by its multiplicity. Raising the multiplicity is free (take powers); the
question is whether the precision can approach the mass of the window.

For a balanced factorial ratio `A_n ∏_j (b_j n)! = ∏_i (a_i n)!` the valuation above `√n` is the
**Landau count** `L(n, p) = Σ_i ⌊a_i n/p⌋ − Σ_j ⌊b_j n/p⌋` (`padicValNat_eq_landauCount`), and balance
makes it periodic: `L(n + kp, p) = L(n, p)` (`landauCount_add_mul`). Multiplicity `m` on `(n, 2n]` for
every `n` therefore forces multiplicity `m` on every **ghost window**, the primes with
`n/p ∈ [k + 1/2, k + 1)` (`le_landauCount_of_mem_ghostWindow`).

* **The ghost ledger** (`ghost_ledger`). `m Σ_{k < K} Σ_{p ∈ ghost window k} log p ≤ log A_n`.
* **Chebyshev precision** (`factorialRatio_precision`). By the prime number theorem the `k`-th ghost
  window has mass `≈ (2/(2k + 1) − 1/(k + 1)) n`, and these masses sum to `2 log 2 · n`
  (`tendsto_ghostConstant`). Hence `log A_n ≥ (2 log 2 − ε) m n` eventually: the precision is at least
  `2 log 2` times the mass `≈ n` of the window, at every multiplicity.
* **The binomial is optimal** (`centralBinom_producer`). `C(2n, n)` has multiplicity one on `(n, 2n]` and
  size at most `2 log 2 · n`, so the constant `2 log 2` is attained.

No balanced factorial ratio, and no product of them at commensurable scales, gets below linear
precision loss `(2 log 2 − 1) m n` on `(n, 2n]`. A producer with square-root precision must have
valuations that are not a periodic function of `n` modulo `p`.
-/

open Finset Filter Topology Nat

namespace GaloisForLFunctions.ArithmeticGaugeTheory

variable {ι κ : Type*} (S : Finset ι) (T : Finset κ) (a : ι → ℕ) (b : κ → ℕ)

/-- The Landau count `Σ_i ⌊a_i n/p⌋ − Σ_j ⌊b_j n/p⌋` of a factorial ratio. -/
def landauCount (n p : ℕ) : ℤ :=
  ∑ i ∈ S, ((a i * n / p : ℕ) : ℤ) - ∑ j ∈ T, ((b j * n / p : ℕ) : ℤ)

variable {S T a b}

/-- **Periodicity of the Landau count.** For a balanced ratio, `L(n + kp, p) = L(n, p)`. -/
theorem landauCount_add_mul (hbal : ∑ i ∈ S, a i = ∑ j ∈ T, b j) (n k : ℕ) {p : ℕ} (hp : 0 < p) :
    landauCount S T a b (n + k * p) p = landauCount S T a b n p := by
  have hshift : ∀ c : ℕ, c * (n + k * p) / p = c * n / p + c * k := fun c => by
    rw [show c * (n + k * p) = c * n + c * k * p by ring, Nat.add_mul_div_right _ _ hp]
  simp only [landauCount, hshift]
  push_cast
  rw [sum_add_distrib, sum_add_distrib, ← sum_mul, ← sum_mul]
  have : ((∑ i ∈ S, a i : ℕ) : ℤ) = ((∑ j ∈ T, b j : ℕ) : ℤ) := by rw [hbal]
  push_cast at this
  rw [this]
  ring

/-- **Above the square root the valuation is the Landau count.** -/
theorem padicValNat_eq_landauCount {A n p : ℕ} [Fact p.Prime]
    (hA : A * ∏ j ∈ T, (b j * n) ! = ∏ i ∈ S, (a i * n) !)
    (ha : ∀ i ∈ S, a i * n < p ^ 2) (hb : ∀ j ∈ T, b j * n < p ^ 2) :
    (padicValNat p A : ℤ) = landauCount S T a b n p := by
  have hden : ∏ j ∈ T, (b j * n) ! ≠ 0 := prod_ne_zero_iff.mpr fun j _ => factorial_ne_zero _
  have hA0 : A ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hA
    exact (prod_ne_zero_iff.mpr fun i _ => factorial_ne_zero _) hA.symm
  have hval := congrArg (padicValNat p) hA
  rw [padicValNat.mul hA0 hden, padicValNat_prod_factorial, padicValNat_prod_factorial,
    sum_congr rfl fun i hi => padicValNat_factorial_of_lt_sq (ha i hi),
    sum_congr rfl fun j hj => padicValNat_factorial_of_lt_sq (hb j hj)] at hval
  rw [landauCount]
  have hcast := congrArg (Nat.cast : ℕ → ℤ) hval
  rw [Nat.cast_add, Nat.cast_sum, Nat.cast_sum] at hcast
  linarith

/-! ### Ghost windows -/

/-- The `k`-th ghost window of `(n, 2n]`: the primes `p` with `n/p ∈ [k + 1/2, k + 1)`. For `k = 0` it
is the window itself. -/
def ghostWindow (n k : ℕ) : Finset ℕ := (Ioc (n / (k + 1)) (2 * n / (2 * k + 1))).filter Nat.Prime

theorem mem_ghostWindow {n k p : ℕ} :
    p ∈ ghostWindow n k ↔ p.Prime ∧ n < p * (k + 1) ∧ p * (2 * k + 1) ≤ 2 * n := by
  simp only [ghostWindow, mem_filter, mem_Ioc, Nat.div_lt_iff_lt_mul (Nat.succ_pos k),
    Nat.le_div_iff_mul_le (Nat.succ_pos (2 * k))]
  tauto

/-- **Multiplicity reaches the ghost windows.** If the Landau count is at least `m` on every window
`(n', 2n']`, it is at least `m` on every ghost window. -/
theorem le_landauCount_of_mem_ghostWindow (hbal : ∑ i ∈ S, a i = ∑ j ∈ T, b j) {m : ℕ}
    (hm : ∀ n' p, n' < p → p ≤ 2 * n' → (m : ℤ) ≤ landauCount S T a b n' p) {n k p : ℕ}
    (hp : p ∈ ghostWindow n k) : (m : ℤ) ≤ landauCount S T a b n p := by
  obtain ⟨hpp, h1, h2⟩ := mem_ghostWindow.mp hp
  have hkp : k * p ≤ n := by nlinarith
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + k * p := ⟨n - k * p, by omega⟩
  rw [landauCount_add_mul hbal n' k hpp.pos]
  exact hm n' p (by nlinarith) (by nlinarith)

/-- Ghost windows are pairwise disjoint. -/
theorem ghostWindow_disjoint {n k k' : ℕ} (hkk : k ≠ k') :
    Disjoint (ghostWindow n k) (ghostWindow n k') := by
  refine disjoint_left.mpr fun p hp hp' => hkk ?_
  obtain ⟨-, h1, h2⟩ := mem_ghostWindow.mp hp
  obtain ⟨-, h1', h2'⟩ := mem_ghostWindow.mp hp'
  have hlt : ∀ {k k'}, p * (2 * k' + 1) ≤ 2 * n → n < p * (k + 1) → k' ≤ k := by
    intro k k' ha hb
    by_contra hc
    push Not at hc
    have : p * (2 * k + 3) ≤ p * (2 * k' + 1) := Nat.mul_le_mul_left p (by omega)
    nlinarith
  exact le_antisymm (hlt h2 h1') (hlt h2' h1)

/-- **The ghost ledger.** If the coefficients are at most `c` and `c K² ≤ n`, then
`m Σ_{k < K} Σ_{p ∈ ghost window k} log p ≤ log A_n`. -/
theorem ghost_ledger (hbal : ∑ i ∈ S, a i = ∑ j ∈ T, b j) {m : ℕ}
    (hm : ∀ n' p, n' < p → p ≤ 2 * n' → (m : ℤ) ≤ landauCount S T a b n' p) {A n c K : ℕ}
    (hA : A * ∏ j ∈ T, (b j * n) ! = ∏ i ∈ S, (a i * n) !) (hac : ∀ i ∈ S, a i ≤ c)
    (hbc : ∀ j ∈ T, b j ≤ c) (hn : c * K ^ 2 ≤ n) :
    (m : ℝ) * ∑ k ∈ range K, ∑ p ∈ ghostWindow n k, Real.log p ≤ Real.log A := by
  classical
  have hA0 : A ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hA
    exact (prod_ne_zero_iff.mpr fun i _ => factorial_ne_zero _) hA.symm
  -- A prime of a ghost window `k < K` exceeds `n/K`, so `c n < p²`.
  have hsq : ∀ k ∈ range K, ∀ p ∈ ghostWindow n k, c * n < p ^ 2 := by
    intro k hk p hp
    obtain ⟨-, h1, -⟩ := mem_ghostWindow.mp hp
    have hkK : k + 1 ≤ K := mem_range.mp hk
    have h3 : n < p * K := lt_of_lt_of_le h1 (Nat.mul_le_mul_left p hkK)
    have h4 : n * n < p * K * (p * K) := Nat.mul_self_lt_mul_self h3
    nlinarith
  have hdisj : (↑(range K) : Set ℕ).PairwiseDisjoint (ghostWindow n) :=
    fun k _ k' _ hkk => ghostWindow_disjoint hkk
  have hprime : ∀ p ∈ (range K).biUnion (ghostWindow n), p.Prime := fun p hp => by
    obtain ⟨k, -, hpk⟩ := mem_biUnion.mp hp
    exact (mem_ghostWindow.mp hpk).1
  have hdvd : ∀ p ∈ (range K).biUnion (ghostWindow n), p ^ m ∣ A := by
    intro p hp
    obtain ⟨k, hk, hpk⟩ := mem_biUnion.mp hp
    haveI : Fact p.Prime := ⟨(mem_ghostWindow.mp hpk).1⟩
    have hval := padicValNat_eq_landauCount (p := p) hA
      (fun i hi => lt_of_le_of_lt (Nat.mul_le_mul_right n (hac i hi)) (hsq k hk p hpk))
      (fun j hj => lt_of_le_of_lt (Nat.mul_le_mul_right n (hbc j hj)) (hsq k hk p hpk))
    have hle : m ≤ padicValNat p A := by
      have := le_landauCount_of_mem_ghostWindow hbal hm hpk
      omega
    exact (pow_dvd_pow p hle).trans pow_padicValNat_dvd
  have h := ArithmeticKreinLangerTheory.sum_mul_log_le_log_of_dvd hA0 hprime (fun _ => m) hdvd
  rwa [sum_biUnion hdisj, ← sum_congr rfl fun k _ => mul_sum _ _ _, ← mul_sum] at h

/-! ### The ghost constant -/

/-- The ghost constant `Σ_{k < K} (2/(2k + 1) − 1/(k + 1))`: the mass of the first `K` ghost windows
divided by `n`. -/
noncomputable def ghostConstant (K : ℕ) : ℝ :=
  ∑ k ∈ range K, (2 / (2 * (k : ℝ) + 1) - 1 / ((k : ℝ) + 1))

/-- The ghost constant is twice a harmonic difference: `2 (H_{2K} − H_K)`. -/
theorem ghostConstant_eq (K : ℕ) :
    ghostConstant K = 2 * ((harmonic (2 * K) : ℝ) - (harmonic K : ℝ)) := by
  induction K with
  | zero => simp [ghostConstant]
  | succ K ih =>
    rw [ghostConstant, Finset.sum_range_succ, ← ghostConstant, ih,
      show 2 * (K + 1) = 2 * K + 1 + 1 by ring, harmonic_succ, harmonic_succ, harmonic_succ]
    push_cast
    field_simp
    ring

/-- **The ghost windows carry `2 log 2`.** -/
theorem tendsto_ghostConstant : Tendsto ghostConstant atTop (𝓝 (2 * Real.log 2)) := by
  have h2K : Tendsto (fun K : ℕ => 2 * K) atTop atTop :=
    tendsto_atTop_atTop.mpr fun B => ⟨B, fun K hK => by omega⟩
  have hdiff := (Real.tendsto_harmonic_sub_log.comp h2K).sub Real.tendsto_harmonic_sub_log
  rw [sub_self] at hdiff
  have hlim := (hdiff.add_const (Real.log 2)).const_mul 2
  rw [zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with K hK
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK
  simp only [Function.comp_apply, ghostConstant_eq]
  push_cast
  rw [Real.log_mul two_ne_zero hK']
  ring

/-! ### Chebyshev precision -/

/-- The mass of the `k`-th ghost window is `θ(2n/(2k + 1)) − θ(n/(k + 1))`. -/
theorem sum_ghostWindow_eq_theta (n k : ℕ) :
    ∑ p ∈ ghostWindow n k, Real.log p =
      Chebyshev.theta (2 * n / (2 * k + 1)) - Chebyshev.theta (n / (k + 1)) := by
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hk2 : (0 : ℝ) < 2 * k + 1 := by positivity
  have hC : (1 : ℝ) ≤ (2 * k + 2) / (2 * k + 1) := (one_le_div hk2).mpr (by linarith)
  have hCx : (2 * k + 2) / (2 * k + 1) * ((n : ℝ) / (k + 1)) = 2 * n / (2 * k + 1) := by
    field_simp
  have e1 : ⌊(n : ℝ) / (k + 1)⌋₊ = n / (k + 1) := by
    have := Nat.floor_div_eq_div (K := ℝ) n (k + 1)
    push_cast at this
    exact this
  have e2 : ⌊2 * (n : ℝ) / (2 * k + 1)⌋₊ = 2 * n / (2 * k + 1) := by
    have := Nat.floor_div_eq_div (K := ℝ) (2 * n) (2 * k + 1)
    push_cast at this
    exact this
  rw [← hCx, RHTower.theta_sub_eq_sum_primeWindow (by positivity) hC,
    RHTower.multiplicativePrimeWindow, hCx, e1, e2, ghostWindow]

/-- Each ghost window eventually has mass at least `(2/(2k + 1) − 1/(k + 1) − 3η) n`. -/
theorem eventually_sum_ghostWindow_ge (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, (2 / (2 * (k : ℝ) + 1) - 1 / ((k : ℝ) + 1) - 3 * η) * n ≤
      ∑ p ∈ ghostWindow n k, Real.log p := by
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hk2 : (0 : ℝ) < 2 * k + 1 := by positivity
  have hθ := RHTower.chebyshevTheta_eventually_relative hη
  have hup := (tendsto_natCast_atTop_atTop.atTop_div_const hk1).eventually hθ
  have hdown :=
    ((tendsto_natCast_atTop_atTop.const_mul_atTop two_pos).atTop_div_const hk2).eventually hθ
  filter_upwards [hup, hdown] with n h1' h2'
  rw [sum_ghostWindow_eq_theta]
  rw [abs_le] at h1' h2'
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hb1 : (n : ℝ) / (k + 1) ≤ n := div_le_self hn (by linarith)
  have hb2 : 2 * (n : ℝ) / (2 * k + 1) ≤ 2 * n := div_le_self (by positivity) (by linarith)
  have e1 : (n : ℝ) / (k + 1) = 1 / ((k : ℝ) + 1) * n := by ring
  have e2 : 2 * (n : ℝ) / (2 * k + 1) = 2 / (2 * (k : ℝ) + 1) * n := by ring
  nlinarith

/-- **Chebyshev precision of factorial ratios.** A balanced factorial-ratio producer with
multiplicity `m` on every window `(n', 2n']` has `log A_n ≥ (2 log 2 − ε) m n` for large `n`. -/
theorem factorialRatio_precision (hbal : ∑ i ∈ S, a i = ∑ j ∈ T, b j) {m : ℕ}
    (hm : ∀ n' p, n' < p → p ≤ 2 * n' → (m : ℤ) ≤ landauCount S T a b n' p) (A : ℕ → ℕ)
    (hA : ∀ n, A n * ∏ j ∈ T, (b j * n) ! = ∏ i ∈ S, (a i * n) !) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (2 * Real.log 2 - ε) * m * n ≤ Real.log (A n) := by
  classical
  -- Enough ghost windows to carry `2 log 2 − ε/2`.
  obtain ⟨K, hK⟩ := (tendsto_ghostConstant.eventually (lt_mem_nhds
    (show 2 * Real.log 2 - ε / 2 < 2 * Real.log 2 by linarith))).exists
  set η : ℝ := ε / (6 * ((K : ℝ) + 1)) with hηdef
  have hη : 0 < η := by positivity
  set c : ℕ := ∑ i ∈ S, a i + ∑ j ∈ T, b j with hc
  have hac : ∀ i ∈ S, a i ≤ c := fun i hi =>
    (single_le_sum (fun _ _ => Nat.zero_le _) hi).trans (Nat.le_add_right _ _)
  have hbc : ∀ j ∈ T, b j ≤ c := fun j hj =>
    (single_le_sum (fun _ _ => Nat.zero_le _) hj).trans (Nat.le_add_left _ _)
  have hwin : ∀ᶠ n : ℕ in atTop, ∀ k ∈ range K,
      (2 / (2 * (k : ℝ) + 1) - 1 / ((k : ℝ) + 1) - 3 * η) * n ≤
        ∑ p ∈ ghostWindow n k, Real.log p :=
    (eventually_all_finset _).mpr fun k _ => eventually_sum_ghostWindow_ge k hη
  filter_upwards [hwin, eventually_ge_atTop (c * K ^ 2)] with n hn hnK
  have hled := ghost_ledger hbal hm (hA n) hac hbc hnK
  have hsum : (ghostConstant K - 3 * η * K) * n ≤
      ∑ k ∈ range K, ∑ p ∈ ghostWindow n k, Real.log p := by
    calc (ghostConstant K - 3 * η * K) * n
        = ∑ k ∈ range K, (2 / (2 * (k : ℝ) + 1) - 1 / ((k : ℝ) + 1) - 3 * η) * n := by
          rw [← sum_mul, sum_sub_distrib, ghostConstant, sum_const, card_range, nsmul_eq_mul]
          ring
      _ ≤ _ := sum_le_sum hn
  have hηK : 3 * η * K ≤ ε / 2 := by
    rw [hηdef]
    have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    rw [show 3 * (ε / (6 * ((K : ℝ) + 1))) * K = ε / 2 * (K / ((K : ℝ) + 1)) by field_simp; ring]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one hK1).mpr (by linarith))
  have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hlow : (2 * Real.log 2 - ε) * n ≤ ∑ k ∈ range K, ∑ p ∈ ghostWindow n k, Real.log p := by
    refine le_trans ?_ hsum
    exact mul_le_mul_of_nonneg_right (by linarith) hn0
  calc (2 * Real.log 2 - ε) * m * n = m * ((2 * Real.log 2 - ε) * n) := by ring
    _ ≤ m * ∑ k ∈ range K, ∑ p ∈ ghostWindow n k, Real.log p :=
        mul_le_mul_of_nonneg_left hlow hm0
    _ ≤ Real.log (A n) := hled

/-- **The binomial is optimal.** `C(2n, n)` is a balanced factorial ratio with Landau count one on
every window `(n', 2n']` and size `log C(2n, n) ≤ 2 log 2 · n`. -/
theorem centralBinom_producer :
    (∀ n, centralBinom n * ∏ _j ∈ (univ : Finset (Fin 2)), (1 * n) ! =
        ∏ _i ∈ (univ : Finset (Fin 1)), (2 * n) !) ∧
      (∀ n' p, n' < p → p ≤ 2 * n' →
        ((1 : ℕ) : ℤ) ≤ landauCount (univ : Finset (Fin 1)) (univ : Finset (Fin 2))
          (fun _ => 2) (fun _ => 1) n' p) ∧
      ∀ n, Real.log (centralBinom n) ≤ 2 * Real.log 2 * n := by
  refine ⟨fun n => ?_, fun n' p h1 h2 => ?_, fun n => ?_⟩
  · simp only [one_mul, prod_const, Finset.card_fin, pow_one]
    rw [sq, ← mul_assoc, centralBinom_eq_two_mul_choose]
    have h := choose_mul_factorial_mul_factorial (n := 2 * n) (k := n) (by omega)
    rwa [show 2 * n - n = n by omega] at h
  · have hp : 0 < p := by omega
    have hq1 : 2 * n' / p = 1 := by
      have hlo : 1 ≤ 2 * n' / p := (Nat.le_div_iff_mul_le hp).mpr (by omega)
      have hhi : 2 * n' / p < 2 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
      omega
    have hq0 : n' / p = 0 := Nat.div_eq_of_lt h1
    simp [landauCount, hq1, hq0]
  · have hpos : (0 : ℝ) < centralBinom n := by exact_mod_cast centralBinom_pos n
    calc Real.log (centralBinom n) ≤ Real.log ((4 : ℝ) ^ n) :=
          Real.log_le_log hpos (by exact_mod_cast centralBinom_le_four_pow n)
      _ = 2 * Real.log 2 * n := by
          rw [Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          push_cast
          ring

end GaloisForLFunctions.ArithmeticGaugeTheory
