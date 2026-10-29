import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.IndexCarriersOfFiniteSpectra
import GaloisForLFunctions.RHTower.GelfondSchneider

/-!
# The Bézout theorem of the multiplicative group of `ℚ`

Over `𝔽_q` Stepanov's method rests on two facts about an auxiliary polynomial: it can be made to
vanish to high order at the rational points (linear algebra made cheap by `x^q = x`), and it cannot
vanish at more points than its degree allows (Bézout). This file proves the second fact for the
auxiliaries of `ℚ_{>0}`: Dirichlet polynomials.

The **points** are the primes, seen through their Frobenius progressions
`s_j = 2πij/log p`, `j ∈ ℤ`, where the local Euler factor `1 − p^{−s}` vanishes. The **degree** of
`D(s) = Σ_{n≤N} a_n n^{−s}` is `log N`.

> **Bézout** (`prod_pow_le_of_vanishesAlong`). If a nonzero Dirichlet polynomial of length `N`
> with complex coefficients vanishes to order `m_p` at all but finitely many points of the
> progression of `p`, for each `p` in a finite set of primes, then `∏ p^{m_p} ≤ N`, i.e.
> `Σ m_p log p ≤ log N`. The bound is attained by `1 − p^{−s}` (`eulerFactor_vanishesAlong`).

* **Exponential sums on `ℤ`** (`fiber_sum_eq_zero`). At `s_j` one has `n^{−s_j} = ω_p(n)^j` with
  `ω_p(n) = e^{−2πi log n/log p}`, and `ω_p(n) = ω_p(n')` iff `n/n'` is a power of `p`. A finite
  exponential sum vanishing at all large `j` has vanishing coefficients (Lagrange interpolation), so
  vanishing on the progression is the vanishing of every `p`-tower sum `Σ_k a(p^k n)`.
* **Division by the Euler factor** (`towerQuot_sub`, `towerQuot_eq_zero`). Then the partial sums
  `F(m) = Σ_{l ≤ v_p(m)} a(m/p^l)` down the towers have length `N/p` and `a = F − F(·/p)`:
  `D(s) = (1 − p^{−s}) F(s)`.
* **Multiplicity** (`dirDeriv_quot`). The derivatives satisfy
  `D^{(i)} = F^{(i)} − p^{−s} Σ_{l≤i} C(i,l)(−log p)^{i−l} F^{(l)}`; on the progression of `p` this
  lowers the order by one, off it (`p^{−s} ≠ 1`, which holds at `s_j(q)`, `j ≠ 0`, by the
  irrationality of `log q/log p`) it keeps the order.

Distinct primes have distinct progressions, apart from `s = 0`, because of unique factorization;
over `𝔽_q` all places of one degree share a progression. The theorem gives the trivial count:
vanishing at all primes up to `y` costs length `e^{θ(y)}`. What a producer needs beyond Bézout is
an identity making the vanishing conditions cheap.
-/

open Complex Finset Filter
open scoped Real

noncomputable section

namespace GaloisForLFunctions.EffectiveArithmeticHodgeTheory

/-! ### Frobenius progressions -/

/-- `ω_p(n) = e^{−2πi log n/log p}`, the value of `n^{−s}` at the first point of the progression of
`p`. -/
def frobRoot (p n : ℕ) : ℂ := cexp (-(2 * π * I) * (Real.log n : ℂ) / (Real.log p : ℂ))

/-- The **Frobenius progression** of `p`: the points `s_j = 2πij/log p`, where `p^{−s} = 1`. -/
def frobPoint (p : ℕ) (j : ℤ) : ℂ := 2 * π * I * j / (Real.log p : ℂ)

theorem frobRoot_ne_zero (p n : ℕ) : frobRoot p n ≠ 0 := Complex.exp_ne_zero _

theorem cpow_neg_frobPoint {n : ℕ} (hn : n ≠ 0) (p : ℕ) (j : ℤ) :
    (n : ℂ) ^ (-frobPoint p j) = frobRoot p n ^ j := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), ← Complex.natCast_log, frobRoot,
    ← Complex.exp_int_mul]
  congr 1
  simp only [frobPoint]
  ring

theorem log_prime_ne_zero {p : ℕ} (hp : p.Prime) : (Real.log p : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'

/-- `p^{−s} = 1` on the progression of `p`. -/
theorem cpow_neg_frobPoint_self {p : ℕ} (hp : p.Prime) (j : ℤ) :
    (p : ℂ) ^ (-frobPoint p j) = 1 := by
  rw [cpow_neg_frobPoint hp.ne_zero, frobRoot, mul_div_assoc, div_self (log_prime_ne_zero hp),
    mul_one, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, one_zpow]

/-- Equal roots of unity force `log n − log n' ∈ ℤ log p`. -/
theorem exists_int_of_frobRoot_eq {p n n' : ℕ} (hp : p.Prime) (h : frobRoot p n = frobRoot p n') :
    ∃ k : ℤ, Real.log n - Real.log n' = k * Real.log p := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hL := log_prime_ne_zero hp
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  refine ⟨-k, ?_⟩
  have h2 : -(2 * π * I) * (((Real.log n : ℂ) - Real.log n') / Real.log p) =
      -(2 * π * I) * (-k) := by
    rw [mul_div_assoc] at hk
    linear_combination hk
  have h3 := mul_left_cancel₀ (neg_ne_zero.mpr hπ) h2
  rw [div_eq_iff hL] at h3
  exact_mod_cast h3

/-- Two progressions meet only at `s = 0`: `p^{−s_j(q)} ≠ 1` for primes `p ≠ q` and `j ≠ 0`. -/
theorem cpow_neg_frobPoint_ne_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {j : ℤ}
    (hj : j ≠ 0) : (p : ℂ) ^ (-frobPoint q j) ≠ 1 := by
  rw [cpow_neg_frobPoint hp.ne_zero, frobRoot, ← Complex.exp_int_mul]
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hb := log_prime_ne_zero hq
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have h2 : (j : ℂ) * (-(2 * π * I) * (Real.log p : ℂ) / Real.log q) * Real.log q =
      (j : ℂ) * (-(2 * π * I) * Real.log p) := by
    rw [mul_assoc, div_mul_cancel₀ _ hb]
  have h3 : (j : ℂ) * (-(2 * π * I) * Real.log p) = n * (2 * π * I) * Real.log q := by
    rw [← h2, hn]
  have h4 : (2 * π * I) * ((j : ℂ) * Real.log p + n * Real.log q) = 0 := by
    linear_combination -h3
  have h5 : (j : ℂ) * Real.log p + n * Real.log q = 0 := (mul_eq_zero.mp h4).resolve_left hπ
  have h6 : (j : ℝ) * Real.log p + n * Real.log q = 0 := by exact_mod_cast h5
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, zero_mul, add_zero, mul_eq_zero, Int.cast_eq_zero] at h6
    exact h6.elim hj (fun h => hlp.ne' h)
  have hirr := RHTower.irrational_log_ratio hp hq hpq
  exact hirr ⟨(j : ℚ) / (-n), by
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    push_cast
    field_simp
    linarith⟩

/-! ### Exponential sums on `ℤ` -/

/-- **Exponential sums on `ℤ`.** If `Σ_{i ∈ s} c_i ω_i^j = 0` for all but finitely many `j ∈ ℤ`, with
`ω_i ≠ 0`, every fibre sum `Σ_{ω_i = w} c_i` vanishes. -/
theorem fiber_sum_eq_zero {ι : Type*} [DecidableEq ι] {s : Finset ι} {c ω : ι → ℂ}
    (hω : ∀ i ∈ s, ω i ≠ 0)
    (h : ∀ᶠ j in (cofinite : Filter ℤ), ∑ i ∈ s, c i * ω i ^ j = 0) (w : ℂ) :
    ∑ i ∈ s with ω i = w, c i = 0 := by
  classical
  set T := s.image ω
  by_cases hw : w ∈ T
  swap
  · refine Finset.sum_eq_zero fun i hi => absurd ?_ hw
    obtain ⟨his, hiw⟩ := Finset.mem_filter.mp hi
    exact hiw ▸ Finset.mem_image_of_mem ω his
  -- the exceptional set is bounded above
  obtain ⟨B, hB⟩ := (Filter.eventually_cofinite.mp h).bddAbove
  obtain ⟨J, hJdef⟩ : ∃ J : ℤ, J = B + 1 := ⟨_, rfl⟩
  have hJ : ∀ k : ℕ, ∑ i ∈ s, c i * ω i ^ (J + k) = 0 := fun k => by
    by_contra hne
    have := hB hne
    omega
  set C : T → ℂ := fun t => ∑ i ∈ s with ω i = t, c i
  have hT0 : ∀ t : T, (t : ℂ) ≠ 0 := fun t => by
    obtain ⟨i, hi, hit⟩ := Finset.mem_image.mp t.2
    rw [← hit]; exact hω i hi
  have hgroup : ∀ j : ℤ, ∑ i ∈ s, c i * ω i ^ j = ∑ t : T, C t * (t : ℂ) ^ j := fun j => by
    rw [← Finset.sum_fiberwise_of_maps_to (t := T) (g := ω)
      (fun i hi => Finset.mem_image_of_mem ω hi), ← Finset.sum_coe_sort T]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
  set u : T → ℂ := fun t => C t * (t : ℂ) ^ J
  let L : (T → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun v => ∑ t, u t * v t
      map_add' := fun v v' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring }
  have hspan := span_pow_eq_top (w := fun t : T => (t : ℂ)) Subtype.val_injective
    (n := Fintype.card T) le_rfl
  have hker : Submodule.span ℂ (Set.range fun k : Fin (Fintype.card T) =>
      fun t : T => (t : ℂ) ^ (k : ℕ)) ≤ LinearMap.ker L := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    show ∑ t, u t * (t : ℂ) ^ (k : ℕ) = 0
    have := hJ k
    rw [hgroup] at this
    rw [← this]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [u]
    rw [zpow_add₀ (hT0 t) J ((k : ℕ) : ℤ), zpow_natCast]
    ring
  rw [hspan] at hker
  have hδ := hker (Submodule.mem_top (x := fun t : T => if t = ⟨w, hw⟩ then (1 : ℂ) else 0))
  simp only [LinearMap.mem_ker] at hδ
  change ∑ t, u t * (if t = ⟨w, hw⟩ then (1 : ℂ) else 0) = 0 at hδ
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, u] at hδ
  exact (mul_eq_zero.mp hδ).resolve_right (zpow_ne_zero _ (hT0 ⟨w, hw⟩))

/-! ### Division by the Euler factor -/

/-- The **tower quotient** `F(m) = Σ_{l ≤ v_p(m)} a(m/p^l)`: partial sums of `a` down the `p`-tower
of `m`. -/
def towerQuot (a : ℕ → ℂ) (p m : ℕ) : ℂ := ∑ l ∈ range (m.factorization p + 1), a (m / p ^ l)

/-- `a = F − F(·/p)`: the tower quotient divides `a` by the Euler factor `1 − p^{−s}`. -/
theorem towerQuot_sub (a : ℕ → ℂ) {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    a m = towerQuot a p m - if p ∣ m then towerQuot a p (m / p) else 0 := by
  by_cases hpm : p ∣ m
  · rw [if_pos hpm]
    have hv : m.factorization p = (m / p).factorization p + 1 := by
      have h1 := Nat.factorization_div hpm
      have h2 : (m / p).factorization p = m.factorization p - 1 := by
        rw [h1, Finsupp.tsub_apply, hp.factorization_self]
      have h3 : 1 ≤ m.factorization p := hp.factorization_pos_of_dvd hm hpm
      omega
    rw [towerQuot, hv, Finset.sum_range_succ', towerQuot]
    simp only [pow_zero, Nat.div_one]
    have : ∀ l ∈ range ((m / p).factorization p + 1), a (m / p ^ (l + 1)) = a (m / p / p ^ l) :=
      fun l _ => by rw [Nat.div_div_eq_div_mul, ← pow_succ']
    rw [Finset.sum_congr rfl this]
    ring
  · rw [if_neg hpm, towerQuot, Nat.factorization_eq_zero_of_not_dvd hpm]
    simp

/-- Equal roots force the two integers into one `p`-tower. -/
theorem eq_mul_pow_of_frobRoot_eq {p n m : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hm : m ≠ 0)
    (h : frobRoot p n = frobRoot p m) : (∃ K : ℕ, n = m * p ^ K) ∨ ∃ K : ℕ, m = n * p ^ K := by
  obtain ⟨k, hk⟩ := exists_int_of_frobRoot_eq hp h
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rcases Int.eq_nat_or_neg k with ⟨K, rfl | rfl⟩
  · left
    refine ⟨K, ?_⟩
    have : Real.log n = Real.log ((m * p ^ K : ℕ) : ℝ) := by
      push_cast
      rw [Real.log_mul hm'.ne' (pow_pos hp' K).ne', Real.log_pow]
      push_cast at hk ⊢
      linarith
    exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr hn') (Set.mem_Ioi.mpr (by
      exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero hm) (pow_pos hp.pos K))) this
  · right
    refine ⟨K, ?_⟩
    have : Real.log m = Real.log ((n * p ^ K : ℕ) : ℝ) := by
      push_cast
      rw [Real.log_mul hn'.ne' (pow_pos hp' K).ne', Real.log_pow]
      push_cast at hk ⊢
      linarith
    exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr hm') (Set.mem_Ioi.mpr (by
      exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero hn) (pow_pos hp.pos K))) this

/-- The `i`-th derivative `Σ_{n≤N} a_n (−log n)^i n^{−s}` of the Dirichlet polynomial of `a`. -/
def dirDeriv (a : ℕ → ℂ) (N i : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, a n * (-(Real.log n : ℂ)) ^ i * (n : ℂ) ^ (-s)

/-- **Vanishing on the progression is the vanishing of the towers.** If the Dirichlet polynomial of
`a`, of length `N`, vanishes at all but finitely many points of the progression of `p`, the tower
quotient vanishes at every `m` with `pm > N`: it has length `N/p`. -/
theorem towerQuot_eq_zero {a : ℕ → ℂ} {N p : ℕ} (hp : p.Prime) (ha0 : ∀ n, N < n → a n = 0)
    (hvan : ∀ᶠ j in (cofinite : Filter ℤ), dirDeriv a N 0 (frobPoint p j) = 0)
    {m : ℕ} (hm : m ≠ 0) (hpm : N < p * m) : towerQuot a p m = 0 := by
  classical
  have hvan' : ∀ᶠ j in (cofinite : Filter ℤ), ∑ n ∈ Icc 1 N, a n * frobRoot p n ^ j = 0 := by
    filter_upwards [hvan] with j hj
    rw [← hj, dirDeriv]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [pow_zero, mul_one, cpow_neg_frobPoint (by have := (Finset.mem_Icc.mp hn).1; omega)]
  have hfib := fiber_sum_eq_zero (fun n _ => frobRoot_ne_zero p n) hvan' (frobRoot p m)
  rw [← hfib, towerQuot]
  set v := m.factorization p
  refine Finset.sum_bij_ne_zero (fun l _ _ => m / p ^ l) ?_ ?_ ?_ (fun _ _ _ => rfl)
  · intro l hl hne
    have hdvd : p ^ l ∣ m := (hp.pow_dvd_iff_le_factorization hm).mpr
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))
    have hpos : 0 < m / p ^ l := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd)
      (pow_pos hp.pos l)
    have hle : m / p ^ l ≤ N := by
      by_contra hgt; exact hne (ha0 _ (not_le.mp hgt))
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, hle⟩, ?_⟩
    have hmq : m = m / p ^ l * p ^ l := (Nat.div_mul_cancel hdvd).symm
    -- `ω_p(m/p^l) = ω_p(m)`
    have hlog : Real.log (m / p ^ l : ℕ) = Real.log m - l * Real.log p := by
      have hq : (0 : ℝ) < (m / p ^ l : ℕ) := by exact_mod_cast hpos
      have : Real.log m = Real.log (m / p ^ l : ℕ) + l * Real.log p := by
        conv_lhs => rw [hmq]
        push_cast
        rw [Real.log_mul hq.ne' (pow_pos (by exact_mod_cast hp.pos : (0 : ℝ) < p) l).ne',
          Real.log_pow]
      linarith
    rw [frobRoot, frobRoot, hlog, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨l, ?_⟩
    have hL := log_prime_ne_zero hp
    rw [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast]
    field_simp
    push_cast
    ring
  · intro l₁ hl₁ _ l₂ hl₂ _ h
    have hd₁ : p ^ l₁ ∣ m := (hp.pow_dvd_iff_le_factorization hm).mpr
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl₁))
    have hd₂ : p ^ l₂ ∣ m := (hp.pow_dvd_iff_le_factorization hm).mpr
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl₂))
    have h1 : m / p ^ l₁ * p ^ l₁ = m / p ^ l₂ * p ^ l₂ := by
      rw [Nat.div_mul_cancel hd₁, Nat.div_mul_cancel hd₂]
    have hq0 : m / p ^ l₁ ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hd₁)
      (pow_pos hp.pos l₁)).ne'
    rw [h] at h1
    exact Nat.pow_right_injective hp.two_le (Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero (h ▸ hq0)) h1)
  · intro n hn hna
    obtain ⟨hnI, hnw⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnI
    rcases eq_mul_pow_of_frobRoot_eq hp (by omega) hm hnw with ⟨K, hK⟩ | ⟨K, hK⟩
    · rcases Nat.eq_zero_or_pos K with rfl | hK0
      · have hnm : n = m := by simpa using hK
        refine ⟨0, Finset.mem_range.mpr (Nat.succ_pos _), ?_, ?_⟩
        · rw [pow_zero, Nat.div_one, ← hnm]; exact hna
        · rw [pow_zero, Nat.div_one, hnm]
      · exfalso
        have : p * m ≤ n := by
          rw [hK, mul_comm]
          exact Nat.mul_le_mul_left m (Nat.le_self_pow hK0.ne' p)
        omega
    · have hdvd : p ^ K ∣ m := ⟨n, by rw [hK, mul_comm]⟩
      have hKv : K ≤ v := (hp.pow_dvd_iff_le_factorization hm).mp hdvd
      refine ⟨K, Finset.mem_range.mpr (Nat.lt_succ_of_le hKv), ?_, ?_⟩
      · rw [show m / p ^ K = n by rw [hK, Nat.mul_div_cancel _ (pow_pos hp.pos K)]]
        exact hna
      · rw [hK, Nat.mul_div_cancel _ (pow_pos hp.pos K)]

/-! ### Derivatives -/

/-- `Σ_{n ≤ N, p | n} g(n) = Σ_{n' ≤ N/p} g(pn')`. -/
theorem sum_Icc_dvd (g : ℕ → ℂ) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (if p ∣ n then g n else 0) = ∑ n ∈ Icc 1 (N / p), g (p * n) := by
  rw [← Finset.sum_filter (fun n => p ∣ n) g]
  have himg : (Icc 1 N).filter (p ∣ ·) = (Icc 1 (N / p)).image (p * ·) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp at h1
        · exact hk
      · exact (Nat.le_div_iff_mul_le hp).mpr (by rw [mul_comm]; exact h2)
    · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right p k⟩
      have := (Nat.le_div_iff_mul_le hp).mp h2
      linarith [mul_comm k p]
  rw [himg, Finset.sum_image fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp h]

/-- **The derivatives of a quotient.** If `a = F − F(·/p)` with `F` of length `N/p`, then
`D_a^{(i)} = D_F^{(i)} − p^{−s} Σ_{l≤i} C(i,l)(−log p)^{i−l} D_F^{(l)}`. -/
theorem dirDeriv_quot {a F : ℕ → ℂ} {N p : ℕ} (hp : p.Prime)
    (ha : ∀ m, m ≠ 0 → a m = F m - if p ∣ m then F (m / p) else 0)
    (hF0 : ∀ m, N / p < m → F m = 0) (i : ℕ) (s : ℂ) :
    dirDeriv a N i s = dirDeriv F (N / p) i s - (p : ℂ) ^ (-s) *
      ∑ l ∈ range (i + 1), (i.choose l : ℂ) * (-(Real.log p : ℂ)) ^ (i - l) *
        dirDeriv F (N / p) l s := by
  set T : ℕ → ℂ := fun n => (-(Real.log n : ℂ)) ^ i * (n : ℂ) ^ (-s)
  have hsplit : dirDeriv a N i s = ∑ n ∈ Icc 1 N, F n * T n -
      ∑ n ∈ Icc 1 N, (if p ∣ n then F (n / p) * T n else 0) := by
    rw [dirDeriv, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [ha n (by have := (Finset.mem_Icc.mp hn).1; omega)]
    simp only [T]
    split_ifs <;> ring
  have h1 : ∑ n ∈ Icc 1 N, F n * T n = dirDeriv F (N / p) i s := by
    rw [dirDeriv]
    simp only [T, ← mul_assoc]
    symm
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.div_le_self N p)) fun n _ hn => ?_
    have : N / p < n := by
      by_contra h
      exact hn (Finset.mem_Icc.mpr ⟨by simp_all, not_lt.mp h⟩)
    rw [hF0 n this]; ring
  have h2 : ∑ n ∈ Icc 1 N, (if p ∣ n then F (n / p) * T n else 0) =
      (p : ℂ) ^ (-s) * ∑ l ∈ range (i + 1), (i.choose l : ℂ) * (-(Real.log p : ℂ)) ^ (i - l) *
        dirDeriv F (N / p) l s := by
    rw [sum_Icc_dvd (fun n => F (n / p) * T n) hp.pos]
    simp only [Nat.mul_div_cancel_left _ hp.pos, dirDeriv, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    simp only [T]
    rw [show ((p * n : ℕ) : ℂ) = (p : ℂ) * n by push_cast; ring, Complex.natCast_mul_natCast_cpow]
    have hlog : (Real.log ((p * n : ℕ) : ℝ) : ℂ) = (Real.log p : ℂ) + Real.log n := by
      push_cast
      rw [Real.log_mul hp0.ne' hn0.ne']
      push_cast; ring
    rw [show ((p * n : ℕ) : ℝ) = ((p * n : ℕ) : ℝ) from rfl, hlog,
      show -((Real.log p : ℂ) + Real.log n) = -(Real.log n : ℂ) + -(Real.log p : ℂ) by ring,
      add_pow, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => by ring
  rw [hsplit, h1, h2]

/-- **Off the progression of `p` the quotient keeps the order.** -/
theorem dirDeriv_quot_eq_zero_of_ne_one {a F : ℕ → ℂ} {N p : ℕ} (hp : p.Prime)
    (ha : ∀ m, m ≠ 0 → a m = F m - if p ∣ m then F (m / p) else 0)
    (hF0 : ∀ m, N / p < m → F m = 0) {s : ℂ} (hs : (p : ℂ) ^ (-s) ≠ 1) {k : ℕ}
    (hD : ∀ i < k, dirDeriv a N i s = 0) : ∀ i < k, dirDeriv F (N / p) i s = 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hik
    have h := dirDeriv_quot hp ha hF0 i s
    rw [hD i hik, Finset.sum_range_succ, Finset.sum_eq_zero fun l hl =>
      by rw [ih l (Finset.mem_range.mp hl) (by have := Finset.mem_range.mp hl; omega), mul_zero],
      zero_add, Nat.choose_self, Nat.sub_self, pow_zero] at h
    push_cast at h
    have h' : (1 - (p : ℂ) ^ (-s)) * dirDeriv F (N / p) i s = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (Ne.symm hs))

/-- **On the progression of `p` the quotient loses one order.** -/
theorem dirDeriv_quot_eq_zero_of_eq_one {a F : ℕ → ℂ} {N p : ℕ} (hp : p.Prime)
    (ha : ∀ m, m ≠ 0 → a m = F m - if p ∣ m then F (m / p) else 0)
    (hF0 : ∀ m, N / p < m → F m = 0) {s : ℂ} (hs : (p : ℂ) ^ (-s) = 1) {k : ℕ}
    (hD : ∀ i < k + 1, dirDeriv a N i s = 0) : ∀ l < k, dirDeriv F (N / p) l s = 0 := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    intro hlk
    have h := dirDeriv_quot hp ha hF0 (l + 1) s
    rw [hD (l + 1) (by omega), hs, one_mul, Finset.sum_range_succ, Nat.choose_self, Nat.sub_self,
      pow_zero, Finset.sum_range_succ, Finset.sum_eq_zero fun l' hl' => by
        rw [ih l' (Finset.mem_range.mp hl') (by have := Finset.mem_range.mp hl'; omega),
          mul_zero], zero_add, Nat.choose_succ_self_right, show l + 1 - l = 1 by omega,
      pow_one] at h
    simp only [Nat.cast_add, Nat.cast_one, one_mul] at h
    have hL := log_prime_ne_zero hp
    have h' : ((l : ℂ) + 1) * (Real.log p : ℂ) * dirDeriv F (N / p) l s = 0 := by
      linear_combination (-1 : ℂ) * h
    rcases mul_eq_zero.mp h' with h'' | h''
    · rcases mul_eq_zero.mp h'' with h3 | h3
      · exact absurd h3 (by exact_mod_cast Nat.succ_ne_zero l)
      · exact absurd h3 hL
    · exact h''

/-! ### Bézout -/

/-- The Dirichlet polynomial of `a`, of length `N`, **vanishes to order `m` along `p`**: its first `m`
derivatives vanish at all but finitely many points of the progression of `p`. -/
def VanishesAlong (a : ℕ → ℂ) (N p m : ℕ) : Prop :=
  ∀ i < m, ∀ᶠ j in (cofinite : Filter ℤ), dirDeriv a N i (frobPoint p j) = 0

/-- One division step: the tower quotient of a polynomial vanishing along `p` has length `N/p`,
vanishes one order less along `p` and to the same orders along every other prime. -/
theorem towerQuot_vanishes {a : ℕ → ℂ} {N p : ℕ} (hp : p.Prime) (ha0 : ∀ n, N < n → a n = 0)
    {mp : ℕ} (hvp : VanishesAlong a N p (mp + 1)) :
    (∀ n, N / p < n → towerQuot a p n = 0) ∧ VanishesAlong (towerQuot a p) (N / p) p mp ∧
      ∀ q, q.Prime → q ≠ p → ∀ k, VanishesAlong a N q k →
        VanishesAlong (towerQuot a p) (N / p) q k := by
  have hF0 : ∀ n, N / p < n → towerQuot a p n = 0 := fun n hn =>
    towerQuot_eq_zero hp ha0 (hvp 0 (by omega)) (lt_of_le_of_lt (Nat.zero_le _) hn).ne'
      (by rw [mul_comm]; exact (Nat.div_lt_iff_lt_mul hp.pos).mp hn)
  have ha : ∀ m, m ≠ 0 → a m = towerQuot a p m - if p ∣ m then towerQuot a p (m / p) else 0 :=
    fun m hm => towerQuot_sub a hp hm
  refine ⟨hF0, ?_, ?_⟩
  · intro i hi
    have hall : ∀ᶠ j in (cofinite : Filter ℤ), ∀ i' ∈ range (mp + 1),
        dirDeriv a N i' (frobPoint p j) = 0 :=
      (Filter.eventually_all_finset _).mpr fun i' hi' => hvp i' (Finset.mem_range.mp hi')
    filter_upwards [hall] with j hj
    exact dirDeriv_quot_eq_zero_of_eq_one hp ha hF0 (cpow_neg_frobPoint_self hp j)
      (fun i' hi' => hj i' (Finset.mem_range.mpr hi')) i hi
  · intro q hq hqp k hvq i hi
    have hall : ∀ᶠ j in (cofinite : Filter ℤ), j ≠ 0 ∧ ∀ i' ∈ range k,
        dirDeriv a N i' (frobPoint q j) = 0 :=
      (Filter.eventually_cofinite_ne 0).and
        ((Filter.eventually_all_finset _).mpr fun i' hi' => hvq i' (Finset.mem_range.mp hi'))
    filter_upwards [hall] with j ⟨hj0, hj⟩
    exact dirDeriv_quot_eq_zero_of_ne_one hp ha hF0
      (cpow_neg_frobPoint_ne_one hp hq (Ne.symm hqp) hj0)
      (fun i' hi' => hj i' (Finset.mem_range.mpr hi')) i hi

/-- The tower quotient of a nonzero polynomial vanishing along `p` is nonzero. -/
theorem towerQuot_ne_zero {a : ℕ → ℂ} {N p : ℕ} (hp : p.Prime) (ha0 : ∀ n, N < n → a n = 0)
    (hne : ∃ n ∈ Icc 1 N, a n ≠ 0) (hF0 : ∀ n, N / p < n → towerQuot a p n = 0) :
    ∃ n ∈ Icc 1 (N / p), towerQuot a p n ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨n, hn, han⟩ := hne
  have hF : ∀ m, towerQuot a p m = 0 ∨ m = 0 := fun m => by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Or.inr rfl
    by_cases hmN : m ≤ N / p
    · exact Or.inl (hall m (Finset.mem_Icc.mpr ⟨hm, hmN⟩))
    · exact Or.inl (hF0 m (not_le.mp hmN))
  apply han
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  rw [towerQuot_sub a hp hn0, (hF n).resolve_right hn0]
  split_ifs with hpn
  · have hq : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn)
      hp.pos).ne'
    rw [(hF (n / p)).resolve_right hq]; ring
  · ring

/-- **The Bézout theorem of `𝔾_m(ℚ)`.** A nonzero Dirichlet polynomial of length `N` vanishing to
order `m_p` along the Frobenius progression of `p`, for every `p` in a finite set `S` of primes,
has `∏_{p∈S} p^{m_p} ≤ N`. -/
theorem prod_pow_le_of_vanishesAlong {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∀ (k : ℕ) (mult : ℕ → ℕ) (a : ℕ → ℂ) (N : ℕ), ∑ p ∈ S, mult p ≤ k →
      (∀ n, N < n → a n = 0) → (∃ n ∈ Icc 1 N, a n ≠ 0) →
      (∀ p ∈ S, VanishesAlong a N p (mult p)) → ∏ p ∈ S, p ^ mult p ≤ N := by
  classical
  intro k
  induction k with
  | zero =>
    intro mult a N hk _ hne _
    have hm0 : ∀ p ∈ S, mult p = 0 := fun p hp =>
      Nat.eq_zero_of_le_zero ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp).trans hk)
    rw [Finset.prod_eq_one fun p hp => by rw [hm0 p hp, pow_zero]]
    obtain ⟨n, hn, -⟩ := hne
    exact (Finset.mem_Icc.mp hn).1.trans (Finset.mem_Icc.mp hn).2
  | succ k ih =>
    intro mult a N hk ha0 hne hvan
    by_cases hall : ∀ p ∈ S, mult p = 0
    · rw [Finset.prod_eq_one fun p hp => by rw [hall p hp, pow_zero]]
      obtain ⟨n, hn, -⟩ := hne
      exact (Finset.mem_Icc.mp hn).1.trans (Finset.mem_Icc.mp hn).2
    push Not at hall
    obtain ⟨p, hpS, hmp⟩ := hall
    have hp := hS p hpS
    obtain ⟨mp, hmp'⟩ : ∃ mp, mult p = mp + 1 := ⟨mult p - 1, by omega⟩
    obtain ⟨hF0, hFp, hFq⟩ := towerQuot_vanishes hp ha0 (hmp' ▸ hvan p hpS)
    have hFne := towerQuot_ne_zero hp ha0 hne hF0
    set mult' := Function.update mult p mp
    have hsum : ∑ q ∈ S, mult' q + 1 = ∑ q ∈ S, mult q := by
      rw [← Finset.add_sum_erase _ _ hpS, ← Finset.add_sum_erase _ _ hpS]
      have : ∑ q ∈ S.erase p, mult' q = ∑ q ∈ S.erase p, mult q :=
        Finset.sum_congr rfl fun q hq => Function.update_of_ne (Finset.ne_of_mem_erase hq) _ _
      rw [this]
      simp only [mult', Function.update_self, hmp']
      ring
    have hih := ih mult' (towerQuot a p) (N / p) (by omega) hF0 hFne fun q hq => by
      by_cases hqp : q = p
      · subst hqp; simp only [mult', Function.update_self]; exact hFp
      · simp only [mult', Function.update_of_ne hqp]
        exact hFq q (hS q hq) hqp _ (hvan q hq)
    have hprod : ∏ q ∈ S, q ^ mult q = p * ∏ q ∈ S, q ^ mult' q := by
      rw [← Finset.mul_prod_erase _ _ hpS, ← Finset.mul_prod_erase _ _ hpS]
      have : ∏ q ∈ S.erase p, q ^ mult' q = ∏ q ∈ S.erase p, q ^ mult q :=
        Finset.prod_congr rfl fun q hq => by
          simp only [mult', Function.update_of_ne (Finset.ne_of_mem_erase hq)]
      rw [this]
      simp only [mult', Function.update_self, hmp', pow_succ]
      ring
    rw [hprod]
    calc p * ∏ q ∈ S, q ^ mult' q ≤ p * (N / p) := Nat.mul_le_mul_left p hih
      _ ≤ N := Nat.mul_div_le N p

/-- **The ledger form**: `Σ_{p∈S} m_p log p ≤ log N`. -/
theorem sum_mul_log_le_of_vanishesAlong {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (mult : ℕ → ℕ) {a : ℕ → ℂ} {N : ℕ} (ha0 : ∀ n, N < n → a n = 0)
    (hne : ∃ n ∈ Icc 1 N, a n ≠ 0) (hvan : ∀ p ∈ S, VanishesAlong a N p (mult p)) :
    ∑ p ∈ S, (mult p : ℝ) * Real.log p ≤ Real.log N := by
  have h := prod_pow_le_of_vanishesAlong hS _ mult a N le_rfl ha0 hne hvan
  have hpos : (0 : ℝ) < ∏ p ∈ S, (p : ℝ) ^ mult p :=
    Finset.prod_pos fun p hp => pow_pos (by exact_mod_cast (hS p hp).pos) _
  have h' : (∏ p ∈ S, (p : ℝ) ^ mult p) ≤ N := by exact_mod_cast h
  have hlog := Real.log_le_log hpos h'
  rw [Real.log_prod (fun p hp => (pow_pos (by exact_mod_cast (hS p hp).pos) _).ne')] at hlog
  simpa only [Real.log_pow] using hlog

/-! ### Sharpness -/

/-- The Euler factor `1 − p^{−s}` as a coefficient sequence. -/
def eulerFactor (p : ℕ) (n : ℕ) : ℂ := if n = 1 then 1 else if n = p then -1 else 0

/-- **Bézout is attained**: `1 − p^{−s}` has length `p` and vanishes on the whole progression of
`p`. -/
theorem eulerFactor_vanishesAlong {p : ℕ} (hp : p.Prime) : VanishesAlong (eulerFactor p) p p 1 := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  refine Eventually.of_forall fun j => ?_
  have hp1 : 1 < p := hp.one_lt
  rw [dirDeriv, ← Finset.sum_subset (s₁ := {1, p}) (fun n hn => by
      rcases Finset.mem_insert.mp hn with rfl | hn
      · exact Finset.mem_Icc.mpr ⟨le_rfl, hp1.le⟩
      · rw [Finset.mem_singleton.mp hn]; exact Finset.mem_Icc.mpr ⟨hp1.le, le_rfl⟩)
    fun n _ hn => by
      have h1 : n ≠ 1 := fun h => hn (by simp [h])
      have h2 : n ≠ p := fun h => hn (by simp [h])
      simp [eulerFactor, h1, h2],
    Finset.sum_pair (ne_of_lt hp1), eulerFactor, eulerFactor, cpow_neg_frobPoint_self hp]
  simp [hp1.ne']

end GaloisForLFunctions.EffectiveArithmeticHodgeTheory
