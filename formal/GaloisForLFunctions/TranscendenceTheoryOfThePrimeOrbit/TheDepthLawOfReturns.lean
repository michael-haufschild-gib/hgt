import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.TheReturnFormDuality
import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.LinearFormsWithExplicitDependenceOnTheirNumber

/-!
# The depth law of returns

A `δ`-return of two primes `p ≠ q` at height `t ≥ 1` makes the binary form
`n_p log q − n_q log p`, `n = round(t log/2π)`, of size `≤ δ log pq` with coefficients `≍ t`
(`abs_round_mul_sub_round_mul_le`). The explicit Baker bound for two logarithms
(`abs_primeLogForm_ge_of_le`) then bounds `t` below by a power of `1/δ`:

`t ≥ e^{−2}(2δ log y)^{−1/C(y)}/(2 log y)`,  `C(y) = bakerExponent 1 ⌈2 log y⌉`,

for every pair of distinct primes `≤ y` (`le_of_isDeltaReturn_pair`), hence for every set of at
least two primes `≤ y`, in particular every heavy subset (`le_of_isDeltaReturn_of_two_mem`).
`C(y)` is a power of `log y`. Dirichlet's box principle gives the matching upper law
`R(P, δ) ≤ ⌈π/2δ⌉^{|P|}` (`exists_isDeltaReturn_le_pow`).

So on the depth axis returns obey a polynomial law in `1/δ`, with exponent between `1/C(y)` and
`|P|`, uniformly over the subsets of the primes `≤ y`. At constant `δ` the lower bound is a constant:
transcendence of the logarithms bounds the depth of a return, not its breadth.
-/

open Real Finset

namespace GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit

noncomputable section

open PrimeTorusTheory (dist01)
open TailArithmeticOfThePrimeOrbit (IsReturn)
open RHTower.Matveev (primeLogForm coeffHeight)

variable {ι : Type*}

/-! ## The two normalizations of a return -/

/-- A return in the cosine normalization at `η = 8δ²` is a `δ`-return. -/
theorem isDeltaReturn_of_isReturn {s : Finset ι} {ℓ : ι → ℝ} {δ t : ℝ} (hδ : 0 ≤ δ)
    (h : IsReturn s ℓ (8 * δ ^ 2) t) : IsDeltaReturn s ℓ δ t := fun i hi => by
  have h8 := PrimeTorusTheory.eight_mul_sq_le_one_sub_cos (t * ℓ i / (2 * π))
  have e : 2 * π * (t * ℓ i / (2 * π)) = t * ℓ i := by field_simp
  rw [e] at h8
  have hsq : dist01 (t * ℓ i / (2 * π)) ^ 2 ≤ δ ^ 2 := by linarith [h i hi]
  exact (pow_le_pow_iff_left₀ (PrimeTorusTheory.dist01_nonneg _) hδ (by norm_num)).mp hsq

/-- **Dirichlet's box principle.** For `Q ≥ 1` with `π ≤ 2δQ` there is a `δ`-return in
`[1, Q^{|s|}]`. -/
theorem exists_isDeltaReturn_le_pow [DecidableEq ι] (s : Finset ι) (ℓ : ι → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) {Q : ℕ} (hQ : 1 ≤ Q) (hδQ : π ≤ 2 * δ * Q) :
    ∃ t, 1 ≤ t ∧ t ≤ (Q : ℝ) ^ s.card ∧ IsDeltaReturn s ℓ δ t := by
  have hηQ : 2 * π ^ 2 ≤ 8 * δ ^ 2 * (Q : ℝ) ^ 2 := by
    have hpi := Real.pi_pos
    nlinarith
  obtain ⟨t, ht1, htQ, ht⟩ := TailArithmeticOfThePrimeOrbit.exists_isReturn_le_pow s ℓ hQ hηQ
  exact ⟨t, ht1, htQ, isDeltaReturn_of_isReturn hδ ht⟩

/-! ## The binary form of a return of two primes -/

/-- At a return of precision `δ ≤ 1/10` and height `t ≥ 1`, the phase of a prime is not rounded
to `0`. -/
theorem round_ne_zero_of_le {p : ℕ} (hp : p.Prime) {δ t : ℝ} (hδ : δ ≤ 1 / 10) (ht : 1 ≤ t)
    (hd : dist01 (t * Real.log p / (2 * π)) ≤ δ) : round (t * Real.log p / (2 * π)) ≠ 0 := by
  intro h0
  have hlog2 : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  have hl2 := Real.log_two_gt_d9
  have hpi := Real.pi_lt_d2
  have hx : 1 / 10 < t * Real.log p / (2 * π) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  unfold dist01 at hd
  rw [h0, Int.cast_zero, sub_zero, abs_of_pos (by linarith)] at hd
  linarith

/-- **The depth inequality.** A `δ`-return `t ≥ 1` of two distinct primes `≤ y`, `δ ≤ 1/10`,
satisfies `exp(−C(log(2t log y) + 2)) ≤ 2δ log y`, `C = bakerExponent 1 ⌈2 log y⌉`. -/
theorem exp_le_of_isDeltaReturn_pair {p q y : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpy : p ≤ y) (hqy : q ≤ y) {δ t : ℝ} (hδ : δ ≤ 1 / 10) (ht : 1 ≤ t)
    (hret : IsDeltaReturn {p, q} (fun n : ℕ => Real.log n) δ t) :
    Real.exp (-(bakerExponent 1 ⌈(1 + 1 : ℝ) * Real.log y⌉₊ *
      (Real.log (2 * t * Real.log y) + 2))) ≤ 2 * δ * Real.log y := by
  set C := bakerExponent 1 ⌈(1 + 1 : ℝ) * Real.log y⌉₊
  set np := round (t * Real.log p / (2 * π))
  set nq := round (t * Real.log q / (2 * π))
  have hpmem : p ∈ ({p, q} : Finset ℕ) := mem_insert_self _ _
  have hqmem : q ∈ ({p, q} : Finset ℕ) := mem_insert_of_mem (mem_singleton_self _)
  have hform := abs_round_mul_sub_round_mul_le hret hpmem hqmem
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  rw [abs_of_pos hlp, abs_of_pos hlq] at hform
  have hy3 : (3 : ℝ) ≤ y := by
    have h2 := hp.two_le; have h2' := hq.two_le
    have : 3 ≤ y := by omega
    exact_mod_cast this
  have hly : Real.log p ≤ Real.log y := Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpy)
  have hlqy : Real.log q ≤ Real.log y := Real.log_le_log (by exact_mod_cast hq.pos) (by exact_mod_cast hqy)
  have hly1 : 1 ≤ Real.log y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hnp : np ≠ 0 := round_ne_zero_of_le hp hδ ht (hret p hpmem)
  -- the integer vector `(n_p, −n_q)` on the primes `(q, p)`
  set ν : Fin 2 → ℤ := ![np, -nq]
  set P : Fin 2 → ℕ := ![q, p]
  have hPinj : Function.Injective P := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [P]
  have hPprime : ∀ i, (P i).Prime := by intro i; fin_cases i <;> simp [P, hp, hq]
  have hPy : ∀ i, P i ≤ y := by intro i; fin_cases i <;> simp [P, hpy, hqy]
  have hν : ν ≠ 0 := by
    intro h; have := congrFun h 0; simp [ν] at this; exact hnp this
  have hΛ : primeLogForm P ν = np * Real.log q - nq * Real.log p := by
    simp [primeLogForm, ν, P, Fin.sum_univ_two]; ring
  have hbaker := abs_primeLogForm_ge_of_le (m := 1) P hPinj hPprime hPy ν hν
  rw [hΛ] at hbaker
  -- the height of `ν` is at most `2t log y`
  have hround : ∀ x : ℝ, |(round x : ℝ)| ≤ |x| + 1 / 2 := fun x => by
    have := abs_sub_round x
    calc |(round x : ℝ)| = |x - (x - round x)| := by ring_nf
      _ ≤ |x| + |x - round x| := abs_sub _ _
      _ ≤ |x| + 1 / 2 := by linarith
  have hpi := Real.pi_gt_three
  have hH : (coeffHeight ν : ℝ) ≤ 2 * t * Real.log y := by
    have e : (coeffHeight ν : ℝ) = |(np : ℝ)| + |(nq : ℝ)| := by
      simp [coeffHeight, ν, Fin.sum_univ_two, Nat.cast_natAbs, Int.cast_abs]
    rw [e]
    have ht0 : 0 < t := by linarith
    have h1 := hround (t * Real.log p / (2 * π))
    have h2 := hround (t * Real.log q / (2 * π))
    rw [abs_of_pos (div_pos (mul_pos ht0 hlp) (by positivity))] at h1
    rw [abs_of_pos (div_pos (mul_pos ht0 hlq) (by positivity))] at h2
    have hb : 0 ≤ t * Real.log y := by positivity
    have h3 : t * Real.log p / (2 * π) ≤ t * Real.log y / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      calc t * Real.log p * 6 ≤ t * Real.log y * 6 := by nlinarith
        _ ≤ t * Real.log y * (2 * π) := mul_le_mul_of_nonneg_left (by linarith) hb
    have h4 : t * Real.log q / (2 * π) ≤ t * Real.log y / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      calc t * Real.log q * 6 ≤ t * Real.log y * 6 := by nlinarith
        _ ≤ t * Real.log y * (2 * π) := mul_le_mul_of_nonneg_left (by linarith) hb
    have : 1 ≤ t * Real.log y := by nlinarith
    linarith
  have hH1 : (1 : ℝ) ≤ coeffHeight ν := by
    have : 1 ≤ coeffHeight ν := by
      have hle : (ν 0).natAbs ≤ coeffHeight ν :=
        single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (mem_univ 0)
      have : (ν 0).natAbs ≠ 0 := by simp [ν, hnp]
      omega
    exact_mod_cast this
  have hC0 : 0 ≤ C := by unfold C bakerExponent; positivity
  have hmono : Real.exp (-(C * (Real.log (2 * t * Real.log y) + 2))) ≤
      Real.exp (-(C * (Real.log (coeffHeight ν) + 2))) := by
    apply Real.exp_le_exp.mpr; apply neg_le_neg
    exact mul_le_mul_of_nonneg_left (by linarith [Real.log_le_log (by linarith) hH]) hC0
  have hcast : ((1 : ℕ) + 1 : ℝ) = (1 + 1 : ℝ) := by norm_num
  calc Real.exp (-(C * (Real.log (2 * t * Real.log y) + 2)))
      ≤ |(np : ℝ) * Real.log q - nq * Real.log p| := hmono.trans (by simpa [C] using hbaker)
    _ ≤ δ * (Real.log p + Real.log q) := hform
    _ ≤ 2 * δ * Real.log y := by
        have hδ0 : 0 ≤ δ := (PrimeTorusTheory.dist01_nonneg _).trans (hret p hpmem)
        nlinarith

/-- **The depth law for two primes.** A `δ`-return `t ≥ 1` of two distinct primes `≤ y`,
`δ ≤ 1/10`, satisfies `t ≥ e^{−2}(2δ log y)^{−1/C}/(2 log y)`. -/
theorem le_of_isDeltaReturn_pair {p q y : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpy : p ≤ y) (hqy : q ≤ y) {δ t : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 10) (ht : 1 ≤ t)
    (hret : IsDeltaReturn {p, q} (fun n : ℕ => Real.log n) δ t) :
    Real.exp (-2) * (2 * δ * Real.log y) ^ (-(bakerExponent 1 ⌈(1 + 1 : ℝ) * Real.log y⌉₊)⁻¹) /
      (2 * Real.log y) ≤ t := by
  set C := bakerExponent 1 ⌈(1 + 1 : ℝ) * Real.log y⌉₊
  have h := exp_le_of_isDeltaReturn_pair hp hq hpq hpy hqy hδ ht hret
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hp.two_le.trans hpy
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hC : 0 < C := by
    unfold C bakerExponent
    have : 0 < baseU 1 (⌈(1 + 1 : ℝ) * Real.log y⌉₊ + 1) := by unfold baseU; positivity
    positivity
  have hA : 0 < 2 * δ * Real.log y := by positivity
  have hT : 0 < 2 * t * Real.log y := by positivity
  -- take logarithms: `−C(log(2t log y) + 2) ≤ log(2δ log y)`
  have hlog := Real.log_le_log (Real.exp_pos _) h
  rw [Real.log_exp] at hlog
  have h2 : -Real.log (2 * δ * Real.log y) / C ≤ Real.log (2 * t * Real.log y) + 2 := by
    rw [div_le_iff₀ hC]; linarith
  have hL : -2 - Real.log (2 * δ * Real.log y) / C ≤ Real.log (2 * t * Real.log y) := by
    rw [neg_div] at h2; linarith
  have key : Real.exp (-2) * (2 * δ * Real.log y) ^ (-C⁻¹) =
      Real.exp (-2 - Real.log (2 * δ * Real.log y) / C) := by
    rw [Real.rpow_def_of_pos hA, ← Real.exp_add]; congr 1; ring
  rw [div_le_iff₀ (by positivity), key]
  calc Real.exp (-2 - Real.log (2 * δ * Real.log y) / C) ≤ Real.exp (Real.log (2 * t * Real.log y)) :=
        Real.exp_le_exp.mpr hL
    _ = t * (2 * Real.log y) := by rw [Real.exp_log hT]; ring

/-- **Every set of at least two primes obeys the depth law**, in particular every heavy subset of
the primes `≤ y`. -/
theorem le_of_isDeltaReturn_of_two_mem {y : ℕ} {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ p ≤ y)
    {p q : ℕ} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) {δ t : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 10)
    (ht : 1 ≤ t) (hret : IsDeltaReturn S (fun n : ℕ => Real.log n) δ t) :
    Real.exp (-2) * (2 * δ * Real.log y) ^ (-(bakerExponent 1 ⌈(1 + 1 : ℝ) * Real.log y⌉₊)⁻¹) /
      (2 * Real.log y) ≤ t := by
  refine le_of_isDeltaReturn_pair (hS p hp).1 (hS q hq).1 hpq (hS p hp).2 (hS q hq).2 hδ0 hδ ht ?_
  intro i hi
  rcases mem_insert.mp hi with rfl | hi
  · exact hret _ hp
  · rw [mem_singleton.mp hi]; exact hret _ hq

end

end GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit
