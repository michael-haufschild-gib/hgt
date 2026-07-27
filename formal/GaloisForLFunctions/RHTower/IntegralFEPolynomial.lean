/-
Degree-zero structure theorem for integral multiplicative functional-equation data.

A member of `IntegralMultiplicativeFEClass` is the `L`-series of an integer-valued multiplicative
arithmetic function `a`, with the representation `f s = ∑' n, a n · n^{-s}` valid at **every** `s`
(the `L`-series is a `tsum`, taking its junk value `0` wherever the coefficient family is not
summable), together with an exact degree-zero functional equation `f s = Q^{1−2s}·f (1−s)` for some
conductor `Q ≥ 2`.

The structure theorem says that such data is rigid: every member is either identically zero or a
Dirichlet polynomial in finitely many prime columns.

* Integrality forces a dichotomy (`integralMultiplicativeFEClass_finite_or_zero`).  If the
  coefficient support is infinite, then along `Re s ≤ 0` the terms `a n · n^{-s}` have norm `≥ 1` on
  the infinite support (a nonzero integer has modulus `≥ 1` and `n^{−Re s} ≥ 1`), so they cannot tend
  to zero: the family is not summable and the junk value pins `f` to `0` on that half-plane.  The
  functional equation transports this to `Re s ≥ 1`.  Hence `f` vanishes for all large real
  arguments, and since a converging `L`-series tends to its first coefficient `a 1 = 1` as the real
  part grows, convergence anywhere is impossible; the abscissa of absolute convergence is `⊤`, so the
  junk value forces `f ≡ 0`.  Integrality is what replaces the finite-order growth axiom of the
  classical degree-zero classification: `‖a n‖ ≥ 1` off the support is the sole ingredient.

* Finite support factors through prime columns (`finiteSupport_multiplicative_columnForm`).  A
  finite-support multiplicative coefficient stream is, via its Euler product over the primes below a
  support bound, a finite product `∏_{p} (∑_{k} a(p^k)·(p^{-s})^k)`; each factor depends on `s` only
  through the single exponential `p^{-s}`, i.e. it is of Ostrowski column form.

* Consequently the divisor is a union of vertical arithmetic progressions
  (`integralMultiplicativeFEClass_zero_periodic`): a zero of any member propagates along the
  imaginary-direction progression of period `2π/log p` of the prime column responsible for it, unless
  the member is identically zero.  In particular the class contains no hypertranscendental member: its
  divisor is never vertically aperiodic.
-/
import GaloisForLFunctions.RHTower.DegreeZeroOffline
import GaloisForLFunctions.RHTower.DAColumnDivisor
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.Exponential

noncomputable section

namespace RHTower

open Complex Filter

/-- For a positive natural base `n`, raising the exponential `n^{-s}` to a natural power `k` is the
same as evaluating the exponential at the power base: `(n^{-s})^k = (n^k)^{-s}`.  The identity is
unconditional because `n^{-s} = exp(log n · (−s))` with `log n` real, so natural powers merely scale
the exponent by `k`, matched by `log (n^k) = k · log n`. -/
private theorem natCast_cpow_neg_pow (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (k : ℕ) :
    ((n : ℂ) ^ (-s)) ^ k = ((n ^ k : ℕ) : ℂ) ^ (-s) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show (0 : ℕ) < n from hn).ne'
  have hnk0 : ((n ^ k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pow_ne_zero k (show n ≠ 0 by omega))
  have hlogn : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ (n : ℝ)), Complex.ofReal_natCast]
  have hlognk : Complex.log ((n ^ k : ℕ) : ℂ) = (k : ℂ) * Complex.log (n : ℂ) := by
    have h1 : Complex.log ((n ^ k : ℕ) : ℂ) = ((Real.log ((n ^ k : ℕ) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_log (by positivity), Complex.ofReal_natCast]
    rw [h1, hlogn, show ((n ^ k : ℕ) : ℝ) = (n : ℝ) ^ k by push_cast; ring, Real.log_pow]
    push_cast; ring
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_nat_mul, Complex.cpow_def_of_ne_zero hnk0]
  congr 1
  rw [hlognk]; ring

/-- **An integral arithmetic function with infinite support has no summable L-series on the closed
left half-plane.**  Each nonzero coefficient is a nonzero integer, so `‖a n‖ ≥ 1`, while
`n ^ Re z ≤ 1` there; infinitely many terms therefore have norm at least one and cannot tend to
zero.  By the `LSeries` convention the value is `0`. -/
theorem LSeries_eq_zero_of_re_nonpos_of_int_of_infinite_support
    {a : ArithmeticFunction ℂ} (hint : ∀ n, ∃ k : ℤ, a n = (k : ℂ))
    (hinf : (Function.support (fun n => a n)).Infinite)
    {z : ℂ} (hz : z.re ≤ 0) : LSeries (fun n => a n) z = 0 := by
  apply LSeries.eq_zero_of_not_LSeriesSummable
  intro hsum
  have hbound : ∀ n ∈ Function.support (fun n => a n),
      (1 : ℝ) ≤ ‖LSeries.term (fun n => a n) z n‖ := by
    intro n hn
    have hane : a n ≠ 0 := hn
    have hn0 : n ≠ 0 := by rintro rfl; exact hane a.map_zero
    obtain ⟨k, hk⟩ := hint n
    have hk0 : k ≠ 0 := by rintro rfl; exact hane (by rw [hk]; norm_num)
    have hanorm : (1 : ℝ) ≤ ‖a n‖ := by
      rw [hk, Complex.norm_intCast]; exact_mod_cast Int.one_le_abs hk0
    have hnrepos : (0 : ℝ) < (n : ℝ) ^ z.re :=
      Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn0) _
    have hnre1 : (n : ℝ) ^ z.re ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0) hz
    rw [LSeries.norm_term_eq, if_neg hn0, one_le_div hnrepos]
    exact hnre1.trans hanorm
  have htend : Tendsto (LSeries.term (fun n => a n) z) atTop (nhds 0) :=
    hsum.tendsto_atTop_zero
  have hev1 : ∀ᶠ n in atTop, ‖LSeries.term (fun n => a n) z n‖ < 1 := by
    have hmem : ∀ᶠ n in atTop, LSeries.term (fun n => a n) z n ∈ Metric.ball (0 : ℂ) 1 :=
      htend.eventually_mem (Metric.ball_mem_nhds 0 one_pos)
    filter_upwards [hmem] with n hn
    simpa [Metric.mem_ball, dist_zero_right] using hn
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev1
  obtain ⟨b, hbS, hMb⟩ := hinf.exists_gt M
  exact absurd (hbound b hbS) (not_le.mpr (hM b hMb.le))

/-- **From vanishing on the closed right half-plane to vanishing everywhere.**  If `f` is the
L-series of `a` and vanishes for `1 ≤ Re z`, then the series vanishes along the real axis at
infinity; with infinite coefficient support the only alternative to identically-zero coefficients
is an infinite abscissa of absolute convergence, and then `f` vanishes identically. -/
theorem eq_zero_of_int_of_infinite_support_of_eq_zero_of_one_le_re
    {f : ℂ → ℂ} {a : ArithmeticFunction ℂ}
    (hrep : ∀ s, f s = LSeries (fun n => a n) s)
    (hinf : (Function.support (fun n => a n)).Infinite)
    (hge1 : ∀ z : ℂ, 1 ≤ z.re → f z = 0) :
    ∀ s, f s = 0 := by
have hev : (fun x : ℝ => LSeries (fun n => a n) x) =ᶠ[atTop] 0 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simp only [Pi.zero_apply]
  rw [← hrep (x : ℂ)]
  exact hge1 (x : ℂ) (by rw [Complex.ofReal_re]; exact hx)
rcases LSeries_eventually_eq_zero_iff'.mp hev with hall | htop
· exfalso
  apply hinf
  have hsupp : Function.support (fun n => a n) = ∅ := by
    ext n
    simp only [Function.mem_support, Set.mem_empty_iff_false, iff_false, not_not]
    rcases eq_or_ne n 0 with rfl | hn0
    · exact a.map_zero
    · exact hall n hn0
  rw [hsupp]; exact Set.finite_empty
· intro z
  rw [hrep z]
  exact congrFun (LSeries_eq_zero_of_abscissaOfAbsConv_eq_top htop) z

/-- **Integrality forces finite support or collapse.**  A member of the integral multiplicative
functional-equation class is either identically zero or is the `L`-series of an integer-valued
multiplicative arithmetic function with **finite** coefficient support.

If the support is infinite, then for `Re s ≤ 0` the term family has norm `≥ 1` on the infinite
support (nonzero integers have modulus `≥ 1`, and `n^{−Re s} ≥ 1`), so it is not summable and the
`tsum` junk value gives `f s = 0`; the functional equation carries this to `Re s ≥ 1`, so `f`
vanishes for all large real arguments.  A converging `L`-series tends to its first coefficient
`a 1 = 1` as the argument grows, so it cannot vanish identically at infinity; hence the abscissa of
absolute convergence is `⊤` and the junk value forces `f ≡ 0`. -/
theorem integralMultiplicativeFEClass_finite_or_zero {f : ℂ → ℂ}
    (hf : IntegralMultiplicativeFEClass f) :
    (∀ s, f s = 0) ∨ ∃ a : ArithmeticFunction ℂ, a.IsMultiplicative ∧
      (∀ n, ∃ k : ℤ, a n = (k : ℂ)) ∧ (∀ s, f s = LSeries (fun n => a n) s) ∧
      (Function.support (fun n => a n)).Finite := by
  obtain ⟨a, hmul, hint, hrep, Q, _hQ2, hFE⟩ := hf
  by_cases hfin : (Function.support (fun n => a n)).Finite
  · exact Or.inr ⟨a, hmul, hint, hrep, hfin⟩
  · left
    have hinf : (Function.support (fun n => a n)).Infinite := hfin
    -- `f` vanishes on the closed left half-plane `Re s ≤ 0` by non-summability.
    have hle0 : ∀ z : ℂ, z.re ≤ 0 → f z = 0 := fun z hz => by
      rw [hrep z]
      exact LSeries_eq_zero_of_re_nonpos_of_int_of_infinite_support hint hinf hz
    -- The functional equation transports vanishing to the right half-plane `Re s ≥ 1`.
    have hge1 : ∀ z : ℂ, 1 ≤ z.re → f z = 0 := by
      intro z hz
      rw [hFE z, hle0 (1 - z) (by rw [Complex.sub_re, Complex.one_re]; linarith), mul_zero]
    -- Hence `LSeries a` vanishes for all large real arguments.
    exact eq_zero_of_int_of_infinite_support_of_eq_zero_of_one_le_re hrep hinf hge1

/-- **Finite-support multiplicative series factor through prime columns.**  If `a` is multiplicative
with finite coefficient support, then `LSeries a` is of Ostrowski column form: a finite product
`∏_{p} Ψ_p(p^{-s})` over the primes below a support bound `N`, with
`Ψ_p(u) = ∑_{k ≤ N} a(p^k)·u^k`.  The identity is the finite Euler product for the multiplicative
term function `n ↦ a n · n^{-s}`: the product over primes equals the sum over the numbers factored by
those primes, which for a bound covering the support is the full `L`-series. -/
theorem finiteSupport_multiplicative_columnForm {a : ArithmeticFunction ℂ}
    (hmul : a.IsMultiplicative) (hfin : (Function.support (fun n => a n)).Finite) :
    ∃ (t : Finset ℕ) (Ψ : ℕ → ℂ → ℂ), (∀ i ∈ t, 2 ≤ i) ∧
      ColumnForm t Ψ (fun s => LSeries (fun n => a n) s) := by
  obtain ⟨N, hN⟩ := hfin.bddAbove
  have haN : ∀ m, a m ≠ 0 → m ≤ N := fun m hm => hN (Function.mem_support.mpr hm)
  -- A prime power exceeding `N` has vanishing coefficient.
  have hapow : ∀ (p : ℕ), Nat.Prime p → ∀ n ∉ Finset.range (N + 1), a (p ^ n) = 0 := by
    intro p hp n hn
    rw [Finset.mem_range, not_lt] at hn
    by_contra h
    have hlt : N < p ^ n := by
      calc N < N + 1 := Nat.lt_succ_self N
        _ ≤ n := hn
        _ < 2 ^ n := n.lt_two_pow_self
        _ ≤ p ^ n := Nat.pow_le_pow_left hp.two_le n
    exact absurd (haN _ h) (by omega)
  refine ⟨(Finset.range (N + 1)).filter Nat.Prime,
          fun p u => ∑ k ∈ Finset.range (N + 1), a (p ^ k) * u ^ k, ?_, ?_⟩
  · intro i hi; exact (Finset.mem_filter.mp hi).2.two_le
  · intro s
    set f : ℕ → ℂ := LSeries.term (fun n => a n) s with hf
    have hterm : ∀ m, f m = a m * ((m : ℂ) ^ (-s)) := by
      intro m; rw [hf, LSeries.term_def₀ (by simp [a.map_zero]) s]
    have hf1 : f 1 = 1 := by rw [hterm]; simp [hmul.map_one]
    have hfmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
      intro m n hcop
      simp only [hterm]
      rw [hmul.map_mul_of_coprime hcop, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]; ring
    have hsummable : Summable (fun x => ‖f x‖) := by
      apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
      intro n hn
      rw [hterm]
      have : a n = 0 := by
        by_contra h; rw [Finset.mem_range, not_lt] at hn; exact absurd (haN n h) (by omega)
      rw [this]; simp
    have hEP := EulerProduct.prod_filter_prime_tsum_eq_tsum_factoredNumbers hf1 hfmul hsummable
      (Finset.range (N + 1))
    have hsub : Function.support f ⊆ Nat.factoredNumbers (Finset.range (N + 1)) := by
      intro n hn
      rw [Function.mem_support] at hn
      have hane : a n ≠ 0 := by intro h; apply hn; rw [hterm, h]; simp
      have hn0 : n ≠ 0 := by rintro rfl; exact hane a.map_zero
      rw [Nat.mem_factoredNumbers]
      refine ⟨hn0, fun p hp => ?_⟩
      rw [Finset.mem_range]
      have hple : p ≤ n :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_primeFactorsList hp)
      have := haN n hane
      omega
    show LSeries (fun n => a n) s = _
    rw [show LSeries (fun n => a n) s = ∑' n, f n from rfl,
        ← tsum_subtype_eq_of_support_subset hsub, ← hEP]
    apply Finset.prod_congr rfl
    intro i hi
    have hip : Nat.Prime i := (Finset.mem_filter.mp hi).2
    rw [tsum_eq_sum (s := Finset.range (N + 1))
        (fun n hn => by rw [hterm, hapow i hip n hn]; simp)]
    apply Finset.sum_congr rfl
    intro k _
    rw [hterm, natCast_cpow_neg_pow i hip.pos s k]

/-- **Zero-periodicity for the whole class.**  Every zero of a member of the integral multiplicative
functional-equation class either belongs to an identically-zero member, or propagates along a
vertical arithmetic progression: there is a period `T = 2π/log i > 0` (`i` the prime column
responsible for the zero) with `f (s₀ + k·T·i) = 0` for all integers `k`.  The divisor of a member is
thus a union of vertical progressions, and no member is hypertranscendental. -/
theorem integralMultiplicativeFEClass_zero_periodic {f : ℂ → ℂ}
    (hf : IntegralMultiplicativeFEClass f) {s₀ : ℂ} (h0 : f s₀ = 0) :
    (∀ s, f s = 0) ∨ ∃ T : ℝ, 0 < T ∧ ∀ k : ℤ, f (s₀ + (k * T) * Complex.I) = 0 := by
  rcases integralMultiplicativeFEClass_finite_or_zero hf with hz | ⟨a, hmul, _hint, hrep, hfin⟩
  · exact Or.inl hz
  · right
    obtain ⟨t, Ψ, ht2, hCF⟩ := finiteSupport_multiplicative_columnForm hmul hfin
    have hCFf : ColumnForm t Ψ f := fun s => (hrep s).trans (hCF s)
    obtain ⟨i, hi, hall⟩ := columnForm_zero_periodic hCFf ht2 h0
    have hi2 : 2 ≤ i := ht2 i hi
    refine ⟨2 * Real.pi / Real.log i,
      div_pos (by positivity) (Real.log_pos (by exact_mod_cast (show 1 < i by omega))), ?_⟩
    intro k
    have hcast : ((2 * Real.pi / Real.log i : ℝ) : ℂ)
        = 2 * (Real.pi : ℂ) / (Real.log i : ℂ) := by push_cast; ring
    rw [hcast]
    exact hall k

end RHTower
