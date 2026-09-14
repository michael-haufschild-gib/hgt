import GaloisForLFunctions.HTGeometry.KroneckerFlow
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Nonzero unconditional completion of integer Dirichlet prime words

For a complex parameter with nonzero real part, an unconditional product
of integer powers of the individual prime letters `p^(-s)` has a nonzero
limit exactly when only finitely many exponents are nonzero. Its value is
one exactly for the empty word.

The finite formula follows from exponential periodicity and unique
factorization. For the infinite statement, log modulus turns the product
net into a convergent sum of integer multiples of prime logarithms. Such
terms have a uniform gap from zero, so the term convergence test forces
finite support. A one-prime return on the imaginary axis shows that the
real-part restriction is necessary.

Convergence uses the usual complex topology and the net indexed by
finite prime subsets. The statements do not concern Euler
factors, grouped products, regularized products, or zero-valued limits.
-/

noncomputable section

open GaloisForLFunctions Filter Topology
open scoped BigOperators

namespace RHTower

/-- A finite product of integer powers of Dirichlet prime letters has its exact prime-log exponent. -/
theorem primeDirichletProduct_eq_exp (s : ℂ) (m : Nat.Primes → ℤ) (S : Finset Nat.Primes) :
    (∏ p ∈ S, (((p : ℕ) : ℂ) ^ (-s)) ^ (m p)) =
      Complex.exp (-s * ((∑ p ∈ S, (m p : ℝ) * Real.log (p : ℕ) : ℝ) : ℂ)) := by
  rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro p _
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast p.property.ne_zero),
    ← Complex.exp_int_mul]
  congr 1
  simp only [← Complex.natCast_log, Complex.ofReal_mul, Complex.ofReal_intCast]
  ring

/-- The character of a finitely supported integer prime word is the exponential of its prime-log frequency. -/
theorem primeDirichletWord_eq_exp (s : ℂ) (m : Nat.Primes →₀ ℤ) :
    m.prod (fun p k => ((p : ℂ) ^ (-s)) ^ k) =
      Complex.exp (-s * (primeLogFrequency m : ℂ)) := by
  exact primeDirichletProduct_eq_exp s m m.support

/-- Away from the imaginary axis, a finite Dirichlet prime word has value one exactly when it is empty. -/
theorem primeDirichletWord_eq_one_iff {s : ℂ} (hs : s.re ≠ 0) (m : Nat.Primes →₀ ℤ) :
    m.prod (fun p k => ((p : ℂ) ^ (-s)) ^ k) = 1 ↔ m = 0 := by
  rw [primeDirichletWord_eq_exp]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
    have hr := congrArg Complex.re hk
    simp [Complex.mul_re] at hr
    exact (primeLogFrequency_eq_zero_iff m).mp (hr.resolve_left hs)
  · rintro rfl
    simp [primeLogFrequency]

/-- Log modulus of a finite prime-word product is its real weighted prime-log sum. -/
theorem log_norm_primeDirichletProduct (s : ℂ) (m : Nat.Primes → ℤ) (S : Finset Nat.Primes) :
    Real.log ‖∏ p ∈ S, (((p : ℕ) : ℂ) ^ (-s)) ^ (m p)‖ =
      -s.re * ∑ p ∈ S, (m p : ℝ) * Real.log (p : ℕ) := by
  rw [primeDirichletProduct_eq_exp, Complex.norm_exp, Real.log_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero]

/-- A summable integer prime-log family has finite support: every nonzero term has magnitude at least `log 2`. -/
theorem finite_support_of_summable_primeIntLog (m : Nat.Primes → ℤ)
    (h : Summable (fun p => (m p : ℝ) * Real.log (p : ℕ))) :
    (Function.support m).Finite := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have hsmall := (Metric.tendsto_nhds.mp h.tendsto_cofinite_zero)
    (Real.log 2) hlog2
  have hzero : ∀ᶠ p in Filter.cofinite, m p = 0 := by
    filter_upwards [hsmall] with p hp
    by_contra hm
    have hi : (1 : ℝ) ≤ |(m p : ℝ)| := by exact_mod_cast Int.one_le_abs hm
    have hlogp : Real.log (2 : ℝ) ≤ Real.log (p : ℕ) :=
      Real.log_le_log zero_lt_two (by exact_mod_cast p.property.two_le)
    have hlower : Real.log 2 ≤ ‖(m p : ℝ) * Real.log (p : ℕ)‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos p.property.log_pos]
      exact hlogp.trans (le_mul_of_one_le_left (hlog2.le.trans hlogp) hi)
    exact (not_lt_of_ge hlower) (by simpa only [dist_zero_right] using hp)
  exact Filter.eventually_cofinite.mp hzero

/-- A nonzero unconditional product limit forces finite support when the exponent has nonzero real part. -/
theorem finite_support_of_hasProd_primeDirichletWord {s a : ℂ} (hs : s.re ≠ 0) (ha : a ≠ 0)
    (m : Nat.Primes → ℤ)
    (h : HasProd (fun p : Nat.Primes => (((p : ℕ) : ℂ) ^ (-s)) ^ (m p)) a) :
    (Function.support m).Finite := by
  have hprod : Filter.Tendsto
      (fun S : Finset Nat.Primes => ∏ p ∈ S, (((p : ℕ) : ℂ) ^ (-s)) ^ (m p))
      Filter.atTop (𝓝 a) := h
  have hlog := ((hprod.norm).log (norm_ne_zero_iff.mpr ha)).div_const (-s.re)
  have hsum : HasSum (fun p => (m p : ℝ) * Real.log (p : ℕ))
      (Real.log ‖a‖ / (-s.re)) := by
    refine hlog.congr' (Filter.Eventually.of_forall fun S => ?_)
    rw [log_norm_primeDirichletProduct]
    exact mul_div_cancel_left₀ _ (neg_ne_zero.mpr hs)
  exact finite_support_of_summable_primeIntLog m hsum.summable

/-- A finitely supported prime word has its finite product as an unconditional product. -/
theorem primeDirichletWord_hasProd (s : ℂ) (m : Nat.Primes →₀ ℤ) :
    HasProd (fun p : Nat.Primes => (((p : ℕ) : ℂ) ^ (-s)) ^ (m p))
      (m.prod (fun p k => (((p : ℕ) : ℂ) ^ (-s)) ^ k)) := by
  classical
  apply hasProd_prod_of_ne_finset_one (s := m.support)
  intro p hp
  rw [Finsupp.notMem_support_iff.mp hp, zpow_zero]

/-- Nonzero unconditional product limits exist exactly for finitely supported integer prime words. -/
theorem exists_nonzero_hasProd_primeDirichletWord_iff {s : ℂ} (hs : s.re ≠ 0)
    (m : Nat.Primes → ℤ) :
    (∃ a : ℂ, a ≠ 0 ∧ HasProd
      (fun p : Nat.Primes => (((p : ℕ) : ℂ) ^ (-s)) ^ (m p)) a) ↔
      (Function.support m).Finite := by
  constructor
  · rintro ⟨a, ha, hp⟩
    exact finite_support_of_hasProd_primeDirichletWord hs ha m hp
  · intro hm
    let mf := Finsupp.ofSupportFinite m hm
    refine ⟨mf.prod (fun p k => (((p : ℕ) : ℂ) ^ (-s)) ^ k), ?_, primeDirichletWord_hasProd s mf⟩
    change (∏ p ∈ mf.support, (((p : ℕ) : ℂ) ^ (-s)) ^ (mf p)) ≠ 0
    apply Finset.prod_ne_zero_iff.mpr
    intro p _
    exact zpow_ne_zero _ (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (by exact_mod_cast p.property.ne_zero)))

/-- The only integer prime word with unconditional product one off the imaginary axis is the empty word. -/
theorem hasProd_primeDirichletWord_one_iff {s : ℂ} (hs : s.re ≠ 0)
    (m : Nat.Primes → ℤ) :
    HasProd (fun p : Nat.Primes => (((p : ℕ) : ℂ) ^ (-s)) ^ (m p)) 1 ↔ m = 0 := by
  constructor
  · intro h
    have hm := finite_support_of_hasProd_primeDirichletWord hs one_ne_zero m h
    let mf := Finsupp.ofSupportFinite m hm
    have heq := (primeDirichletWord_hasProd s mf).unique h
    have hmf := (primeDirichletWord_eq_one_iff hs mf).mp heq
    funext p
    exact congrArg (fun v : Nat.Primes →₀ ℤ => v p) hmf
  · rintro rfl
    simpa only [Pi.zero_apply, zpow_zero] using
      (hasProd_one : HasProd (fun _ : Nat.Primes => (1 : ℂ)) 1)

/-- Each prime supplies a nonempty word with value one at a nonzero purely imaginary parameter. -/
theorem exists_imaginary_primeDirichletWord_return (p : Nat.Primes) :
    ∃ s : ℂ, s ≠ 0 ∧ s.re = 0 ∧
      (Finsupp.single p (1 : ℤ)).prod
        (fun q k => (((q : ℕ) : ℂ) ^ (-s)) ^ k) = 1 := by
  let b : ℂ := (Real.log (p : ℕ) : ℂ)
  have hb : b ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.log_ne_zero
  let s : ℂ := -(2 * Real.pi * Complex.I) / b
  refine ⟨s, div_ne_zero (neg_ne_zero.mpr Complex.two_pi_I_ne_zero) hb, ?_, ?_⟩
  · dsimp only [s, b]
    rw [Complex.div_ofReal_re]
    simp
  · rw [primeDirichletWord_eq_exp, primeLogFrequency_single]
    simp only [Int.cast_one, one_mul]
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨1, ?_⟩
    simp only [Int.cast_one, one_mul]
    change -(-(2 * Real.pi * Complex.I) / b) * b = 2 * Real.pi * Complex.I
    rw [neg_div, neg_neg, div_mul_cancel₀ _ hb]

end RHTower
