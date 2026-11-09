import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.LinearFormsWithExplicitDependenceOnTheirNumber
import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.TheReturnFormDuality
import GaloisForLFunctions.RHTower.GelfondSchneider
import GaloisForLFunctions.RHTower.SixExponentials.PrimePowers

/-!
# Survival at a deep return

An integer auxiliary is a Dirichlet polynomial `A(s) = Σ_{n∈N} c_n n^{−s}`, `c_n ∈ ℤ`, on integers
smooth over primes `p_0, …, p_{d−1}`. Its jets at a height `t` are
`A^{(j)}(it) = Σ c_n (−log n)^j n^{−it}`; at `t = 0` they are integer forms of degree `j` in the
`log p_i`.

* **Jets at a return** (`norm_auxJet_sub_le`). At a `δ`-return of the primes,
  `‖A^{(j)}(it) − A^{(j)}(0)‖ ≤ 2πδ M_j`, `M_j = Σ|c_n|(log n)^j Ω(n)`: the jet at `0` is copied to
  the return, to precision `δ`. The return is an approximate group: `mt` is an `mδ`-return
  (`isDeltaReturn_nsmul`), so the copy extends to the multiples of `t` (`norm_auxJet_nsmul_sub_le`).
* **Order 0 survives at constant precision** (`sum_coeff_eq_zero_of_small`). `A(0) = Σ c_n ∈ ℤ`; if
  `|A(it)| + 2πδM₀ < 1` then `A(0) = 0` exactly.
* **Order 1 survives below the Baker threshold** (`firstMoment_eq_zero_of_small`). `A′(0) = −Λ_μ` for
  the integer first-moment vector `μ_i = Σ_n c_n v_{p_i}(n)` (`auxJet_one_zero`). If
  `|A′(it)| + 2πδM₁ < exp(−C(log|μ|₁ + 2))`, `C` the explicit Baker exponent, then `μ = 0`: all
  first moments vanish exactly. Dirichlet's pigeonhole (`exists_small_primeLogForm`) gives forms with
  `|Λ_μ| ≤ W/H^{d−1}` at height `H`, so no threshold above that size works.
* **Order 2 at two primes** (`quadratic_log_form_eq_zero`). An integer quadratic form in
  `log p, log q` vanishes only trivially (Gelfond–Schneider), so exact vanishing of the second jet is
  the vanishing of three integer moments. A threshold for approximate vanishing needs a measure of
  transcendence of `log q/log p` against quadratic polynomials; for three primes even exact vanishing
  is the algebraic independence of the logarithms.
* **No algebraic point on the orbit** (`not_isAlgebraic_orbit`). For `t ≠ 0` the numbers
  `p^{−it}, q^{−it}, r^{−it}` of three primes are not all algebraic (six exponentials), so the norm of
  an integer auxiliary is never available on the orbit away from `t = 0`.

Survival costs depth: order `0` at precision `≍ 1/M₀`, order `1` at precision exponentially small in
`C log|μ|₁`, order `2` at no known precision.
-/

open Real Finset

namespace GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit

noncomputable section

open PrimeTorusTheory (dist01)
open RHTower.Matveev (primeLogForm coeffHeight totalLogSum)

variable {d : ℕ}

/-! ## Smooth integers and their exponent vectors -/

/-- `n` is a positive integer whose prime factors lie among `p_0, …, p_{d−1}`. -/
def IsSmoothOver (p : Fin d → ℕ) (n : ℕ) : Prop := n ≠ 0 ∧ ∀ q ∈ n.primeFactors, ∃ i, p i = q

/-- The exponent vector `(v_{p_i}(n))_i`. -/
def expVec (p : Fin d → ℕ) (n : ℕ) : Fin d → ℤ := fun i => (n.factorization (p i) : ℤ)

/-- The number `Σ_i v_{p_i}(n)` of prime factors of a smooth `n`. -/
def smoothHeight (p : Fin d → ℕ) (n : ℕ) : ℕ := formHeight univ (expVec p n)

theorem log_eq_linForm {p : Fin d → ℕ} (hp : Function.Injective p) {n : ℕ}
    (hn : IsSmoothOver p n) :
    Real.log n = linForm univ (fun i => Real.log (p i)) (expVec p n) := by
  classical
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  have hsub : n.primeFactors ⊆ univ.image p := fun q hq => by
    obtain ⟨i, hi⟩ := hn.2 q hq; exact mem_image.mpr ⟨i, mem_univ _, hi⟩
  rw [sum_subset hsub fun q _ hq => by
    rw [Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization]), Nat.cast_zero,
      zero_mul], sum_image fun i _ j _ h => hp h]
  unfold linForm expVec
  simp

/-- **The phase of a smooth integer at a return.** At a `δ`-return of the primes, a smooth `n`
has phase within `Ω(n)δ` of `ℤ`. -/
theorem dist01_phase_le {p : Fin d → ℕ} (hp : Function.Injective p) {n : ℕ}
    (hn : IsSmoothOver p n) {δ t : ℝ}
    (hret : IsDeltaReturn univ (fun i => Real.log (p i)) δ t) :
    dist01 (t * Real.log n / (2 * π)) ≤ smoothHeight p n * δ := by
  rw [log_eq_linForm hp hn]; exact dist01_linForm_le hret _

/-- `|e^{−iθ} − 1| ≤ 2π‖θ/2π‖`. -/
theorem norm_exp_neg_sub_one_le (θ : ℝ) :
    ‖Complex.exp (-(θ : ℂ) * Complex.I) - 1‖ ≤ 2 * π * dist01 (θ / (2 * π)) := by
  set k := round (θ / (2 * π))
  set x : ℝ := -(θ - 2 * π * k)
  have e : Complex.exp (-(θ : ℂ) * Complex.I) = Complex.exp (Complex.I * x) := by
    have : Complex.I * x = -(θ : ℂ) * Complex.I + (k : ℂ) * (2 * π * Complex.I) := by
      simp only [x]; push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [e]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans (le_of_eq ?_)
  have hpi : 0 < 2 * π := by positivity
  simp only [x, Real.norm_eq_abs, abs_neg]
  unfold dist01
  rw [show θ - 2 * π * k = 2 * π * (θ / (2 * π) - k) by field_simp, abs_mul,
    abs_of_pos hpi]

/-! ## Jets of integer auxiliaries -/

/-- The `j`-th jet at height `t` of `A(s) = Σ_{n∈N} c_n n^{−s}`: `Σ c_n (−log n)^j n^{−it}`. -/
def auxJet (N : Finset ℕ) (c : ℕ → ℤ) (j : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ N, (((c n : ℝ) * (-Real.log n) ^ j : ℝ) : ℂ) *
    Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)

/-- The jet mass `M_j = Σ |c_n| (log n)^j Ω(n)`. -/
def jetMass (p : Fin d → ℕ) (N : Finset ℕ) (c : ℕ → ℤ) (j : ℕ) : ℝ :=
  ∑ n ∈ N, |(c n : ℝ)| * Real.log n ^ j * smoothHeight p n

theorem auxJet_zero (N : Finset ℕ) (c : ℕ → ℤ) (j : ℕ) :
    auxJet N c j 0 = ((∑ n ∈ N, (c n : ℝ) * (-Real.log n) ^ j : ℝ) : ℂ) := by
  simp [auxJet]

/-- **The jet at a return is the jet at `0`, to precision `δ`.** -/
theorem norm_auxJet_sub_le {p : Fin d → ℕ} (hp : Function.Injective p) {N : Finset ℕ}
    (hN : ∀ n ∈ N, IsSmoothOver p n) (c : ℕ → ℤ) (j : ℕ) {δ t : ℝ}
    (hret : IsDeltaReturn univ (fun i => Real.log (p i)) δ t) :
    ‖auxJet N c j t - auxJet N c j 0‖ ≤ 2 * π * δ * jetMass p N c j := by
  unfold auxJet jetMass
  rw [← sum_sub_distrib, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  simp only [zero_mul, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [← mul_sub_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
    abs_of_nonneg hlog]
  have hexp := norm_exp_neg_sub_one_le (t * Real.log n)
  have hph := dist01_phase_le hp (hN n hn) hret
  have hc : 0 ≤ |(c n : ℝ)| * Real.log n ^ j := by positivity
  calc |(c n : ℝ)| * Real.log n ^ j * ‖Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I) - 1‖
      ≤ |(c n : ℝ)| * Real.log n ^ j * (2 * π * (smoothHeight p n * δ)) :=
        mul_le_mul_of_nonneg_left (hexp.trans (by gcongr)) hc
    _ = 2 * π * δ * (|(c n : ℝ)| * Real.log n ^ j * smoothHeight p n) := by ring

/-- `t` is a `δ`-return ⇒ `mt` is an `mδ`-return: returns form an approximate group. -/
theorem isDeltaReturn_nsmul {ι : Type*} {s : Finset ι} {ℓ : ι → ℝ} {δ t : ℝ}
    (hret : IsDeltaReturn s ℓ δ t) (m : ℕ) : IsDeltaReturn s ℓ (m * δ) (m * t) := fun i hi => by
  have h := dist01_intCast_mul_le (m : ℤ) (t * ℓ i / (2 * π))
  have e : ((m : ℤ) : ℝ) * (t * ℓ i / (2 * π)) = m * t * ℓ i / (2 * π) := by push_cast; ring
  rw [e] at h
  refine h.trans ?_
  have : |((m : ℤ) : ℝ)| = m := by push_cast; exact abs_of_nonneg (Nat.cast_nonneg m)
  rw [this]
  exact mul_le_mul_of_nonneg_left (hret i hi) (Nat.cast_nonneg m)

/-- **Extrapolation along the approximate group.** The jet at `0` is copied to every multiple of
a return, to precision `mδ`. -/
theorem norm_auxJet_nsmul_sub_le {p : Fin d → ℕ} (hp : Function.Injective p) {N : Finset ℕ}
    (hN : ∀ n ∈ N, IsSmoothOver p n) (c : ℕ → ℤ) (j : ℕ) {δ t : ℝ}
    (hret : IsDeltaReturn univ (fun i => Real.log (p i)) δ t) (m : ℕ) :
    ‖auxJet N c j (m * t) - auxJet N c j 0‖ ≤ 2 * π * (m * δ) * jetMass p N c j :=
  norm_auxJet_sub_le hp hN c j (isDeltaReturn_nsmul hret m)

/-! ## Order 0: integrality -/

/-- **Order `0` survives at constant precision.** If `|A(it)| + 2πδM₀ < 1` at a `δ`-return, then
`A(0) = Σ c_n = 0`. -/
theorem sum_coeff_eq_zero_of_small {p : Fin d → ℕ} (hp : Function.Injective p) {N : Finset ℕ}
    (hN : ∀ n ∈ N, IsSmoothOver p n) (c : ℕ → ℤ) {δ t : ℝ}
    (hret : IsDeltaReturn univ (fun i => Real.log (p i)) δ t)
    (hsmall : ‖auxJet N c 0 t‖ + 2 * π * δ * jetMass p N c 0 < 1) : ∑ n ∈ N, c n = 0 := by
  have hdiff := norm_auxJet_sub_le hp hN c 0 hret
  have h0 : ‖auxJet N c 0 0‖ < 1 := by
    have := norm_sub_le (auxJet N c 0 0 - auxJet N c 0 t) (-auxJet N c 0 t)
    rw [norm_neg, sub_neg_eq_add, sub_add_cancel, norm_sub_rev] at this
    linarith
  rw [auxJet_zero] at h0
  simp only [pow_zero, mul_one, Complex.norm_real, Real.norm_eq_abs] at h0
  have hint : |((∑ n ∈ N, c n : ℤ) : ℝ)| < 1 := by push_cast; exact h0
  rw [← Int.cast_abs] at hint
  have : |∑ n ∈ N, c n| < 1 := by exact_mod_cast hint
  exact Int.abs_lt_one_iff.mp this

/-! ## Order 1: linear forms in logarithms -/

/-- The integer first-moment vector `μ_i = Σ_n c_n v_{p_i}(n)`. -/
def firstMoment (p : Fin d → ℕ) (N : Finset ℕ) (c : ℕ → ℤ) : Fin d → ℤ :=
  fun i => ∑ n ∈ N, c n * (n.factorization (p i) : ℤ)

/-- `A′(0) = −Λ_μ`: the first jet at `0` is the linear form of the first moments. -/
theorem auxJet_one_zero {p : Fin d → ℕ} (hp : Function.Injective p) {N : Finset ℕ}
    (hN : ∀ n ∈ N, IsSmoothOver p n) (c : ℕ → ℤ) :
    auxJet N c 1 0 = ((-primeLogForm p (firstMoment p N c) : ℝ) : ℂ) := by
  rw [auxJet_zero]
  congr 1
  have h : ∀ n ∈ N, (c n : ℝ) * (-Real.log n) ^ 1 =
      -∑ i, (c n : ℝ) * (n.factorization (p i) : ℝ) * Real.log (p i) := fun n hn => by
    rw [pow_one, mul_neg, log_eq_linForm hp (hN n hn)]
    unfold linForm expVec
    rw [mul_sum]; congr 1; refine sum_congr rfl fun i _ => ?_
    push_cast; ring
  rw [sum_congr rfl h, sum_neg_distrib]
  unfold primeLogForm firstMoment
  rw [sum_comm]
  congr 1; refine sum_congr rfl fun i _ => ?_
  push_cast; rw [sum_mul]

/-- **Order `1` survives below the Baker threshold.** At a `δ`-return of `m + 1` distinct primes
with `Σ log p ≤ W`, if `|A′(it)| + 2πδM₁ < exp(−C(log|μ|₁ + 2))`, `C = bakerExponent m W`, then
every first moment `μ_i = Σ_n c_n v_{p_i}(n)` vanishes. -/
theorem firstMoment_eq_zero_of_small {m : ℕ} (p : Fin (m + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) {Wb : ℕ} (hW : totalLogSum p ≤ Wb) {N : Finset ℕ}
    (hN : ∀ n ∈ N, IsSmoothOver p n) (c : ℕ → ℤ) {δ t : ℝ}
    (hret : IsDeltaReturn univ (fun i => Real.log (p i)) δ t)
    (hsmall : ‖auxJet N c 1 t‖ + 2 * π * δ * jetMass p N c 1 <
      Real.exp (-(bakerExponent m Wb * (Real.log (coeffHeight (firstMoment p N c)) + 2)))) :
    firstMoment p N c = 0 := by
  by_contra hμ
  have hbaker := abs_primeLogForm_ge_explicit p hp hprime hW _ hμ
  have hdiff := norm_auxJet_sub_le hp hN c 1 hret
  have h0 : ‖auxJet N c 1 0‖ ≤ ‖auxJet N c 1 t‖ + 2 * π * δ * jetMass p N c 1 := by
    have := norm_sub_le (auxJet N c 1 0 - auxJet N c 1 t) (-auxJet N c 1 t)
    rw [norm_neg, sub_neg_eq_add, sub_add_cancel, norm_sub_rev] at this
    linarith
  rw [auxJet_one_zero hp hN, Complex.norm_real, Real.norm_eq_abs, abs_neg] at h0
  linarith

/-! ## Order 2 at two primes -/

/-- **An integer quadratic form in two prime logarithms vanishes only trivially**
(Gelfond–Schneider: `log q/log p` is transcendental). -/
theorem quadratic_log_form_eq_zero {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {a b c : ℤ}
    (h : (a : ℝ) * Real.log p ^ 2 + b * Real.log p * Real.log q + c * Real.log q ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hT := RHTower.log_ratio_transcendental hp hq hpq
  set β := Real.log q / Real.log p
  have hlp : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hβ : (a : ℝ) + b * β + c * β ^ 2 = 0 := by
    have e : (a : ℝ) + b * β + c * β ^ 2 =
        ((a : ℝ) * Real.log p ^ 2 + b * Real.log p * Real.log q + c * Real.log q ^ 2) /
          Real.log p ^ 2 := by
      simp only [β]; field_simp
    rw [e, h, zero_div]
  by_contra hne
  apply hT
  refine ⟨Polynomial.C (c : ℚ) * Polynomial.X ^ 2 + Polynomial.C (b : ℚ) * Polynomial.X +
    Polynomial.C (a : ℚ), ?_, ?_⟩
  · intro h0
    apply hne
    have h2 := congrArg (fun P => Polynomial.coeff P 2) h0
    have h1 := congrArg (fun P => Polynomial.coeff P 1) h0
    have h00 := congrArg (fun P => Polynomial.coeff P 0) h0
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_zero] at h2 h1 h00
    norm_num at h2 h1 h00
    exact ⟨by exact_mod_cast h00, by exact_mod_cast h1, by exact_mod_cast h2⟩
  · simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, eq_ratCast,
      Rat.cast_intCast]
    linear_combination hβ

/-! ## Algebraic points of the orbit -/

/-- **No algebraic point on the orbit.** For `t ≠ 0` and three distinct primes, the numbers
`p^{−it}, q^{−it}, r^{−it}` are not all algebraic (six exponentials). -/
theorem not_isAlgebraic_orbit {t : ℝ} (ht : t ≠ 0) {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ¬ (IsAlgebraic ℚ ((p : ℂ) ^ (-(t : ℂ) * Complex.I)) ∧
      IsAlgebraic ℚ ((q : ℂ) ^ (-(t : ℂ) * Complex.I)) ∧
      IsAlgebraic ℚ ((r : ℂ) ^ (-(t : ℂ) * Complex.I))) :=
  RHTower.SixExponentials.not_all_three_prime_cpow_isAlgebraic (by simpa using ht) hp hq hr hpq hpr hqr

end

end GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit
