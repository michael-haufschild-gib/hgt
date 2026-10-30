import GaloisForLFunctions.ArithmeticGaugeTheory.TheDivisorCollapse
import GaloisForLFunctions.ArithmeticGaugeTheory.TheGaugeExponentIsATailInvariant
import GaloisForLFunctions.RHTower.DirichletCharacterPartialSumBound

/-!
# The Dirichlet points cancel through periodicity

Read the constant source `a ≡ 1` at a gauge point: its partial sums are `Σ_{n ≤ N} χ_x(n)`. At the
trivial point they are `N + 1`, the coherent excess that is the pole (`gaugeExponent_one_trivial`,
exponent `1`). At Haar-almost every point they are `O(N^{1/2 + ε})`. At the gauge point of a
nonprincipal Dirichlet character they are polylogarithmic, so the exponent is `0`
(`gaugeExponent_one_dirichletGauge`): the special points are better than typical.

* **Descent over one prime** (`coprimeTwistSum_eq_split`, `coprimeTwistSum_eq_sum`). With
  `B_P(N) = Σ_{n ≤ N, p ∤ n ∀ p ∈ P} χ_x(n)`, adding a prime `p ∉ P` gives
  `B_P(N) = B_{P ∪ {p}}(N) + χ_x(p) B_P(⌊N/p⌋)`, hence `B_P(N) = Σ_k χ_x(p)^k B_{P ∪ {p}}(⌊N/p^k⌋)`.
* **Logarithmic loss** (`norm_coprimeTwistSum_le_of_insert`). Each descent costs a factor
  `log₂ N + 1`, the number of powers of `p` below `N`.
* **The coprime sum is a character sum** (`norm_coprimeTwistSum_primeFactors_le`). On the integers
  prime to `q` the Dirichlet gauge point is its character, and character sums are bounded by `q + 1`.
* **Polylogarithmic sums** (`norm_coprimeTwistSum_le_of_subset`,
  `gaugePowerBound_one_dirichletGauge`). Descending through the primes of `q` gives
  `|Σ_{1 ≤ n ≤ N} χ_x(n)| ≤ (q + 1)(log₂ N + 1)^{ω(q)}`, which is `O_δ(N^δ)` for every `δ > 0`.
* **Exponents** (`gaugeExponent_one_dirichletGauge`, `gaugeExponent_one_trivial`). The constant source
  has exponent `0` at every nonprincipal Dirichlet gauge point and `1` at the trivial point.

Both points are special: each carries additive structure. Periodicity with a nonprincipal character
produces cancellation; the trivial point's invariance under the successor produces the pole. For the
constant source the trivial point is the one special point where additive structure is coherent
instead of cancelling. This is a typicality theorem for special points of the simplest kind, proved by
the mechanism the programme asks for: additive structure at the point itself.
-/

open MeasureTheory Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-! ### Descent over one prime -/

/-- The twisted constant source over the integers in `[1, N]` divisible by no prime of `P`. -/
def coprimeTwistSum (P : Finset ℕ) (y : GaugeTorus) (N : ℕ) : ℂ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => ∀ r ∈ P, ¬ r ∣ n), twist y n

@[simp] theorem coprimeTwistSum_zero (P : Finset ℕ) (y : GaugeTorus) :
    coprimeTwistSum P y 0 = 0 := by
  simp [coprimeTwistSum]

/-- A prime outside `P` does not change divisibility by the primes of `P`. -/
theorem forall_not_dvd_prime_mul {P : Finset ℕ} (hP : ∀ r ∈ P, r.Prime) {p : ℕ} (hp : p.Prime)
    (hpP : p ∉ P) (m : ℕ) : (∀ r ∈ P, ¬ r ∣ p * m) ↔ ∀ r ∈ P, ¬ r ∣ m := by
  refine forall₂_congr fun r hr => not_congr ⟨fun h => ?_, fun h => h.mul_left p⟩
  rcases (Nat.Prime.dvd_mul (hP r hr)).mp h with hrp | hrm
  · have := (Nat.prime_dvd_prime_iff_eq (hP r hr) hp).mp hrp
    exact absurd (this ▸ hr) hpP
  · exact hrm

/-- **Descent.** `B_P(N) = B_{P ∪ {p}}(N) + χ(p) B_P(⌊N/p⌋)` for a prime `p ∉ P`. -/
theorem coprimeTwistSum_eq_split {P : Finset ℕ} (hP : ∀ r ∈ P, r.Prime) {p : ℕ} (hp : p.Prime)
    (hpP : p ∉ P) (y : GaugeTorus) (N : ℕ) :
    coprimeTwistSum P y N = coprimeTwistSum (insert p P) y N +
      twist y p * coprimeTwistSum P y (N / p) := by
  classical
  have hsplit := sum_filter_add_sum_filter_not ((Icc 1 N).filter (fun n => ∀ r ∈ P, ¬ r ∣ n))
    (fun n => p ∣ n) (fun n => twist y n)
  rw [filter_filter, filter_filter] at hsplit
  have hnot : (Icc 1 N).filter (fun n => (∀ r ∈ P, ¬ r ∣ n) ∧ ¬ p ∣ n) =
      (Icc 1 N).filter (fun n => ∀ r ∈ insert p P, ¬ r ∣ n) := by
    refine filter_congr fun n _ => ?_
    simp only [mem_insert, forall_eq_or_imp]
    exact and_comm
  have hmult : ∑ n ∈ (Icc 1 N).filter (fun n => (∀ r ∈ P, ¬ r ∣ n) ∧ p ∣ n), twist y n =
      twist y p * coprimeTwistSum P y (N / p) := by
    rw [show (Icc 1 N).filter (fun n => (∀ r ∈ P, ¬ r ∣ n) ∧ p ∣ n) =
        ((Icc 1 N).filter (fun n => p ∣ n)).filter (fun n => ∀ r ∈ P, ¬ r ∣ n) by
          rw [filter_filter]; exact filter_congr fun n _ => and_comm,
      ← image_mul_Icc hp.pos, filter_image,
      sum_image fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hp.pos hab,
      coprimeTwistSum, mul_sum]
    have hcongr : (Icc 1 (N / p)).filter (fun m => ∀ r ∈ P, ¬ r ∣ p * m) =
        (Icc 1 (N / p)).filter (fun m => ∀ r ∈ P, ¬ r ∣ m) :=
      filter_congr fun m _ => forall_not_dvd_prime_mul hP hp hpP m
    rw [hcongr]
    refine sum_congr rfl fun m hm => ?_
    have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_Icc.mp (mem_filter.mp hm).1).1
    rw [twist_mul y hp.ne_zero hm0]
  rw [coprimeTwistSum, coprimeTwistSum, ← hsplit, hmult, hnot, add_comm]

/-- **Inversion.** `B_P(N) = Σ_{k ≤ N} χ(p)^k B_{P ∪ {p}}(⌊N/p^k⌋)`. -/
theorem coprimeTwistSum_eq_sum {P : Finset ℕ} (hP : ∀ r ∈ P, r.Prime) {p : ℕ} (hp : p.Prime)
    (hpP : p ∉ P) (y : GaugeTorus) (N : ℕ) :
    coprimeTwistSum P y N = ∑ k ∈ range (N + 1),
      twist y p ^ k * coprimeTwistSum (insert p P) y (N / p ^ k) := by
  have hpartial : ∀ K : ℕ, coprimeTwistSum P y N =
      ∑ k ∈ range K, twist y p ^ k * coprimeTwistSum (insert p P) y (N / p ^ k) +
        twist y p ^ K * coprimeTwistSum P y (N / p ^ K) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      have hs := coprimeTwistSum_eq_split hP hp hpP y (N / p ^ K)
      rw [Nat.div_div_eq_div_mul, ← pow_succ] at hs
      rw [ih, Finset.sum_range_succ, pow_succ]
      linear_combination (twist y p ^ K) * hs
  have hlt : N < p ^ (N + 1) :=
    (Nat.lt_pow_self hp.one_lt (n := N)).trans (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self N))
  rw [hpartial (N + 1), Nat.div_eq_of_lt hlt, coprimeTwistSum_zero, mul_zero, add_zero]

/-- **Logarithmic loss.** A bound `C (log₂ M + 1)^t` for `B_{P ∪ {p}}` gives `C (log₂ N + 1)^{t+1}`
for `B_P`. -/
theorem norm_coprimeTwistSum_le_of_insert {P : Finset ℕ} (hP : ∀ r ∈ P, r.Prime) {p : ℕ}
    (hp : p.Prime) (hpP : p ∉ P) (y : GaugeTorus) {C : ℝ} (hC : 0 ≤ C) {t : ℕ}
    (hB : ∀ M, ‖coprimeTwistSum (insert p P) y M‖ ≤ C * ((Nat.log 2 M : ℝ) + 1) ^ t) (N : ℕ) :
    ‖coprimeTwistSum P y N‖ ≤ C * ((Nat.log 2 N : ℝ) + 1) ^ (t + 1) := by
  classical
  rw [coprimeTwistSum_eq_sum hP hp hpP y N]
  set L : ℝ := (Nat.log 2 N : ℝ) + 1 with hL
  have hL1 : 1 ≤ L := by rw [hL]; linarith [(Nat.log 2 N).cast_nonneg (α := ℝ)]
  -- Only the powers `p^k ≤ N` contribute.
  have hzero : ∀ k ∈ range (N + 1), k ∉ (range (N + 1)).filter (fun k => p ^ k ≤ N) →
      twist y p ^ k * coprimeTwistSum (insert p P) y (N / p ^ k) = 0 := by
    intro k hk hkf
    have hgt : N < p ^ k := by
      by_contra hle
      exact hkf (mem_filter.mpr ⟨hk, not_lt.mp hle⟩)
    rw [Nat.div_eq_of_lt hgt, coprimeTwistSum_zero, mul_zero]
  rw [← sum_subset (filter_subset _ _) hzero]
  have hcard : (#((range (N + 1)).filter (fun k => p ^ k ≤ N)) : ℝ) ≤ L := by
    have hsub : (range (N + 1)).filter (fun k => p ^ k ≤ N) ⊆ range (Nat.log p N + 1) := by
      intro k hk
      obtain ⟨-, hpk⟩ := mem_filter.mp hk
      rw [mem_range, Nat.lt_succ_iff]
      exact Nat.le_log_of_pow_le hp.one_lt hpk
    have h1 := card_le_card hsub
    rw [card_range] at h1
    have h2 : Nat.log p N ≤ Nat.log 2 N := Nat.log_anti_left (by norm_num) hp.two_le
    rw [hL]
    exact_mod_cast (h1.trans (Nat.succ_le_succ h2))
  have hterm : ∀ k ∈ (range (N + 1)).filter (fun k => p ^ k ≤ N),
      ‖twist y p ^ k * coprimeTwistSum (insert p P) y (N / p ^ k)‖ ≤ C * L ^ t := by
    intro k _
    rw [norm_mul, norm_pow, norm_twist, one_pow, one_mul]
    refine (hB _).trans (mul_le_mul_of_nonneg_left ?_ hC)
    have hlog : Nat.log 2 (N / p ^ k) ≤ Nat.log 2 N := Nat.log_mono_right (Nat.div_le_self N _)
    have : ((Nat.log 2 (N / p ^ k) : ℕ) : ℝ) + 1 ≤ L := by
      rw [hL]
      exact_mod_cast Nat.succ_le_succ hlog
    exact pow_le_pow_left₀ (by positivity) this t
  calc ‖∑ k ∈ (range (N + 1)).filter (fun k => p ^ k ≤ N),
        twist y p ^ k * coprimeTwistSum (insert p P) y (N / p ^ k)‖
      ≤ ∑ k ∈ (range (N + 1)).filter (fun k => p ^ k ≤ N),
          ‖twist y p ^ k * coprimeTwistSum (insert p P) y (N / p ^ k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ (range (N + 1)).filter (fun k => p ^ k ≤ N), C * L ^ t := sum_le_sum hterm
    _ = (#((range (N + 1)).filter (fun k => p ^ k ≤ N)) : ℝ) * (C * L ^ t) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ L * (C * L ^ t) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = C * L ^ (t + 1) := by ring

/-! ### The Dirichlet gauge point -/

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- Integers prime to `q` are those divisible by no prime of `q`. -/
theorem coprime_iff_forall_primeFactors {n : ℕ} :
    Nat.Coprime n q ↔ ∀ r ∈ q.primeFactors, ¬ r ∣ n := by
  constructor
  · intro h r hr hrn
    have h1 : r ∣ 1 := by
      have := Nat.dvd_gcd hrn (Nat.dvd_of_mem_primeFactors hr)
      rwa [h.gcd_eq_one] at this
    exact (Nat.prime_of_mem_primeFactors hr).one_lt.ne' (Nat.dvd_one.mp h1)
  · intro h
    refine Nat.coprime_of_dvd fun r hr hrn hrq => h r ?_ hrn
    exact Nat.mem_primeFactors.mpr ⟨hr, hrq, NeZero.ne q⟩

/-- Splitting off the index `0`: `Σ_{n ≤ N} f(n) = f(0) + Σ_{1 ≤ n ≤ N} f(n)`. -/
theorem sum_range_succ_eq_add_Icc (f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ range (N + 1), f n = f 0 + ∑ n ∈ Icc 1 N, f n := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos N), Nat.succ_eq_add_one,
    Finset.Ico_add_one_right_eq_Icc, zero_add]

/-- **The coprime sum is a character sum**, bounded by `q + 1`. -/
theorem norm_coprimeTwistSum_primeFactors_le (hχ : χ ≠ 1) (N : ℕ) :
    ‖coprimeTwistSum q.primeFactors (dirichletGauge χ) N‖ ≤ (q : ℝ) + 1 := by
  classical
  -- Off the integers prime to `q` the character vanishes.
  have hsplit : ∑ n ∈ Icc 1 N, χ (n : ZMod q) =
      ∑ n ∈ (Icc 1 N).filter (fun n => ∀ r ∈ q.primeFactors, ¬ r ∣ n), χ (n : ZMod q) := by
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    split_ifs with h
    · rfl
    · have hncop : ¬ Nat.Coprime n q := fun hc => h (coprime_iff_forall_primeFactors.mp hc)
      exact MulChar.map_nonunit χ fun hu => hncop ((ZMod.isUnit_iff_coprime n q).mp hu)
  have heq : coprimeTwistSum q.primeFactors (dirichletGauge χ) N =
      ∑ n ∈ range (N + 1), χ (n : ZMod q) - χ ((0 : ℕ) : ZMod q) := by
    rw [sum_range_succ_eq_add_Icc (fun n => χ (n : ZMod q)), hsplit, add_sub_cancel_left,
      coprimeTwistSum]
    refine sum_congr rfl fun n hn => ?_
    obtain ⟨hnI, hnr⟩ := mem_filter.mp hn
    exact twist_dirichletGauge χ (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hnI).1)
      (coprime_iff_forall_primeFactors.mpr hnr)
  rw [heq]
  calc ‖∑ n ∈ range (N + 1), χ (n : ZMod q) - χ ((0 : ℕ) : ZMod q)‖
      ≤ ‖∑ n ∈ range (N + 1), χ (n : ZMod q)‖ + ‖χ ((0 : ℕ) : ZMod q)‖ := norm_sub_le _ _
    _ ≤ q + 1 := add_le_add (RHTower.norm_dirichletCharacter_sum_range_le χ hχ (N + 1))
        (RHTower.norm_dirichletCharacter_le_one χ _)

/-- **Polylogarithmic sums.** Removing the primes of `q` one at a time:
`|B_T(N)| ≤ (q + 1) (log₂ N + 1)^{#(primes of q outside T)}`. -/
theorem norm_coprimeTwistSum_le_of_subset (hχ : χ ≠ 1) :
    ∀ k : ℕ, ∀ T : Finset ℕ, T ⊆ q.primeFactors → #(q.primeFactors \ T) = k → ∀ N,
      ‖coprimeTwistSum T (dirichletGauge χ) N‖ ≤ ((q : ℝ) + 1) * ((Nat.log 2 N : ℝ) + 1) ^ k := by
  classical
  intro k
  induction k with
  | zero =>
    intro T hT hk N
    have hTeq : T = q.primeFactors :=
      Subset.antisymm hT (sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp hk))
    rw [hTeq, pow_zero, mul_one]
    exact norm_coprimeTwistSum_primeFactors_le χ hχ N
  | succ k ih =>
    intro T hT hk N
    obtain ⟨p, hp⟩ : (q.primeFactors \ T).Nonempty := card_pos.mp (by omega)
    obtain ⟨hpq, hpT⟩ := mem_sdiff.mp hp
    have hins : insert p T ⊆ q.primeFactors := insert_subset hpq hT
    have hcard : #(q.primeFactors \ insert p T) = k := by
      rw [show q.primeFactors \ insert p T = (q.primeFactors \ T).erase p by
        ext r; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto,
        card_erase_of_mem hp, hk, Nat.add_sub_cancel]
    exact norm_coprimeTwistSum_le_of_insert (fun r hr => Nat.prime_of_mem_primeFactors (hT hr))
      (Nat.prime_of_mem_primeFactors hpq) hpT _ (by positivity) (ih _ hins hcard) N

/-! ### The constant source -/

/-- The constant source `a ≡ 1`. -/
def oneSource : ℕ → ℂ := fun _ => 1

theorem norm_oneSource_le (n : ℕ) : ‖oneSource n‖ ≤ 1 := by simp [oneSource]

theorem sum_range_oneSource (y : GaugeTorus) (N : ℕ) :
    ∑ n ∈ range (N + 1), oneSource n * twist y n = 1 + coprimeTwistSum ∅ y N := by
  simp only [oneSource, one_mul]
  rw [sum_range_succ_eq_add_Icc, twist_at_zero, coprimeTwistSum]
  simp

/-- `log₂ N + 1` is at most a constant times any positive power of `N + 1`. -/
theorem natLog_two_add_one_le_rpow {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    (Nat.log 2 N : ℝ) + 1 ≤ (1 / (ε * Real.log 2) + 1) * ((N : ℝ) + 1) ^ ε := by
  have hX : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [N.cast_nonneg (α := ℝ)]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpow : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
    exact_mod_cast Nat.pow_log_le_add_one 2 N
  -- `k log 2 = log 2^k ≤ log (N + 1) ≤ (N + 1)^ε / ε`.
  have hk : (Nat.log 2 N : ℝ) * Real.log 2 ≤ ((N : ℝ) + 1) ^ ε / ε := by
    rw [← Real.log_pow, ← Nat.cast_ofNat, ← Nat.cast_pow]
    exact (Real.log_le_log (by positivity) hpow).trans (Real.log_le_rpow_div (by linarith) hε)
  have hk' : (Nat.log 2 N : ℝ) ≤ 1 / (ε * Real.log 2) * ((N : ℝ) + 1) ^ ε := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    have := (le_div_iff₀ hε).mp hk
    linarith
  have h1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ ε := Real.one_le_rpow hX hε.le
  linarith

/-- **The constant source cancels at a nonprincipal Dirichlet gauge point:** its partial sums are
`O_δ((N + 1)^δ)` for every `δ > 0`. -/
theorem gaugePowerBound_one_dirichletGauge (hχ : χ ≠ 1) {δ : ℝ} (hδ : 0 < δ) :
    GaugePowerBound oneSource (dirichletGauge χ) δ := by
  classical
  set t := #q.primeFactors with ht
  set ε : ℝ := δ / ((t : ℝ) + 1) with hε
  have hεpos : 0 < ε := by positivity
  set A : ℝ := 1 / (ε * Real.log 2) + 1 with hA
  have hA0 : 0 ≤ A := by have := Real.log_pos one_lt_two; positivity
  refine ⟨1 + ((q : ℝ) + 1) * A ^ t, by positivity, fun N => ?_⟩
  have hX : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [N.cast_nonneg (α := ℝ)]
  have hB := norm_coprimeTwistSum_le_of_subset χ hχ t ∅ (empty_subset _)
    (by rw [sdiff_empty]) N
  -- `(log₂ N + 1)^t ≤ A^t (N + 1)^{εt} ≤ A^t (N + 1)^δ`.
  have hL : ((Nat.log 2 N : ℝ) + 1) ^ t ≤ A ^ t * ((N : ℝ) + 1) ^ δ := by
    calc ((Nat.log 2 N : ℝ) + 1) ^ t ≤ (A * ((N : ℝ) + 1) ^ ε) ^ t :=
          pow_le_pow_left₀ (by positivity) (natLog_two_add_one_le_rpow hεpos N) t
      _ = A ^ t * ((N : ℝ) + 1) ^ (ε * t) := by
          rw [mul_pow, Real.rpow_mul (by positivity), Real.rpow_natCast]
      _ ≤ A ^ t * ((N : ℝ) + 1) ^ δ := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX ?_) (by positivity)
          rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  have h1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ δ := Real.one_le_rpow hX hδ.le
  rw [sum_range_oneSource]
  calc ‖1 + coprimeTwistSum ∅ (dirichletGauge χ) N‖
      ≤ 1 + ‖coprimeTwistSum ∅ (dirichletGauge χ) N‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_one]
    _ ≤ 1 + ((q : ℝ) + 1) * (A ^ t * ((N : ℝ) + 1) ^ δ) := by
        gcongr
        exact hB.trans (mul_le_mul_of_nonneg_left hL (by positivity))
    _ ≤ (1 + ((q : ℝ) + 1) * A ^ t) * ((N : ℝ) + 1) ^ δ := by nlinarith

/-- **Exponent zero at the Dirichlet points.** -/
theorem gaugeExponent_one_dirichletGauge (hχ : χ ≠ 1) :
    gaugeExponent oneSource (dirichletGauge χ) = 0 :=
  le_antisymm (gaugeExponent_le_of_forall le_rfl fun δ hδ => by
      rw [zero_add]; exact gaugePowerBound_one_dirichletGauge χ hχ hδ)
    (gaugeExponent_nonneg norm_oneSource_le)

/-- **Exponent one at the trivial point:** there the partial sums are `N + 1`. -/
theorem gaugeExponent_one_trivial : gaugeExponent oneSource 0 = 1 := by
  refine le_antisymm (gaugeExponent_le_one norm_oneSource_le) ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨θ, hθ1, hθ2⟩ := exists_between hlt
  obtain ⟨C, -, hb⟩ := gaugePowerBound_of_gaugeExponent_lt norm_oneSource_le hθ1
  have hgrow : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (1 - θ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  obtain ⟨N, hN⟩ := (hgrow.eventually_gt_atTop C).exists
  have hX : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hS : ‖∑ n ∈ range (N + 1), oneSource n * twist 0 n‖ = (N : ℝ) + 1 := by
    simp only [oneSource, twist_trivialPoint, sum_const, card_range, nsmul_eq_mul,
      mul_one]
    rw [Complex.norm_natCast]
    push_cast
    ring
  have h := hb N
  rw [hS] at h
  have hsplit : ((N : ℝ) + 1) ^ θ * ((N : ℝ) + 1) ^ (1 - θ) = (N : ℝ) + 1 := by
    rw [← Real.rpow_add hX, add_sub_cancel, Real.rpow_one]
  have hpow : 0 < ((N : ℝ) + 1) ^ θ := Real.rpow_pos_of_pos hX θ
  nlinarith

end GaloisForLFunctions.ArithmeticGaugeTheory
