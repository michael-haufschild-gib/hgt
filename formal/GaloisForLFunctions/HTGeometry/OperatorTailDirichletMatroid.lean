import GaloisForLFunctions.HTGeometry.PrimeExpLogFiberRigidity
import GaloisForLFunctions.HTGeometry.ArithmeticFunctionJacobianCriterion
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The operator-tail Dirichlet matroid capstone

This module carries the operator-tail rank geometry across the Dirichlet transform and fuses the two
engines of the branch.  On the Dirichlet-convolution algebra `𝒜 = ArithmeticFunction ℂ` the ring
product *is* the Dirichlet convolution, so the transform respects convolution definitionally.  The
two symmetries of the Dirichlet variable are realized as coefficient operators:

* the multiplicative weight `n ↦ n^{-a}` — the **shift** `dirichletShift a`, a ring endomorphism of
  `𝒜` implementing the translation `s ↦ s + a` of the Dirichlet variable;
* the additive weight `n ↦ log n` — the **log derivation** `logWeight`, a derivation of `𝒜` whose
  `k`-th iterate is the `(log n)^k` weight `(-1)^k dᵏ/dsᵏ`.

Coefficient determinacy (`dirichlet_ext`) is Dirichlet uniqueness; `primeDeriv_smul_of_annihilated`
is the clearing of finite-prime denominators (kernel elements act as scalars on the chosen
derivations).

The capstone `operatorTail_algebraicIndependence` fuses:

* Task 1 (`primeCompleteShiftJetTailIndependent_iff`): every finite operator-tail rectangle has full
  tail rank *iff* the finite-range source columns are scalar tail-independent; and
* Task 2 (`algebraicIndependent_arithmeticColumns_of_tailIndependent`): scalar tail independence
  forces algebraic independence of the realized arithmetic functions.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Finset

noncomputable section

/-! ## Dirichlet uniqueness -/

/-- **Dirichlet uniqueness.**  An arithmetic function is determined by its coefficient sequence: the
Dirichlet transform is injective on coefficients. -/
theorem dirichlet_ext {f g : ArithmeticFunction ℂ} (h : ∀ n, f n = g n) : f = g := by
  ext n; exact h n

/-- The ring product on `𝒜` is the Dirichlet convolution: the transform respects convolution. -/
theorem dirichlet_mul_apply (f g : ArithmeticFunction ℂ) (n : ℕ) :
    (f * g) n = ∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2 :=
  ArithmeticFunction.mul_apply

/-! ## The multiplicative shift `n ↦ n^{-a}` -/

/-- The completely multiplicative weight `n ↦ n^{-a}`. -/
def cpowWeight (a : ℂ) (n : ℕ) : ℂ := (n : ℂ) ^ (-a)

theorem cpowWeight_mul (a : ℂ) (d e : ℕ) :
    cpowWeight a (d * e) = cpowWeight a d * cpowWeight a e := by
  simp only [cpowWeight, Nat.cast_mul]
  exact Complex.natCast_mul_natCast_cpow d e (-a)

/-- The **Dirichlet shift** `(dirichletShift a f)(n) = n^{-a} f(n)`, implementing the translation
`s ↦ s + a` of the Dirichlet variable. -/
def dirichletShift (a : ℂ) (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ where
  toFun n := cpowWeight a n * f n
  map_zero' := by simp

@[simp] theorem dirichletShift_apply (a : ℂ) (f : ArithmeticFunction ℂ) (n : ℕ) :
    dirichletShift a f n = cpowWeight a n * f n := rfl

theorem dirichletShift_add (a : ℂ) (f g : ArithmeticFunction ℂ) :
    dirichletShift a (f + g) = dirichletShift a f + dirichletShift a g := by
  ext n; simp [mul_add]

/-- The shift respects Dirichlet convolution: `dirichletShift a` is a ring endomorphism.  This is
the `n^{-a}` translation of the Dirichlet series. -/
theorem dirichletShift_mul (a : ℂ) (f g : ArithmeticFunction ℂ) :
    dirichletShift a (f * g) = dirichletShift a f * dirichletShift a g := by
  ext n
  rw [dirichletShift_apply, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Nat.mem_divisorsAntidiagonal] at hx
  rw [dirichletShift_apply, dirichletShift_apply, ← hx.1, cpowWeight_mul]
  ring

/-! ## The logarithmic derivation `n ↦ (log n) f(n)` -/

/-- The **log weight** `(logWeight f)(n) = (log n) f(n)`; a derivation of `𝒜` whose `k`-th iterate is
the `(log n)^k` weight, i.e. `(-1)^k dᵏ/dsᵏ` on the Dirichlet series. -/
def logWeight (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ where
  toFun n := (Real.log n : ℂ) * f n
  map_zero' := by simp

@[simp] theorem logWeight_apply (f : ArithmeticFunction ℂ) (n : ℕ) :
    logWeight f n = (Real.log n : ℂ) * f n := rfl

theorem logWeight_add (f g : ArithmeticFunction ℂ) :
    logWeight (f + g) = logWeight f + logWeight g := by
  ext n; simp [mul_add]

theorem logWeight_smul (r : ℂ) (f : ArithmeticFunction ℂ) :
    logWeight (r • f) = r • logWeight f := by
  ext n
  simp only [logWeight_apply, ArithmeticFunction.smul_map, smul_eq_mul]
  ring

/-- **Leibniz rule for the log derivation.**  `logWeight` is a derivation of the Dirichlet-convolution
algebra, because `log` is additive on the divisor antidiagonal. -/
theorem logWeight_leibniz (f g : ArithmeticFunction ℂ) :
    logWeight (f * g) = logWeight f * g + f * logWeight g := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [logWeight_apply, ArithmeticFunction.add_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Nat.mem_divisorsAntidiagonal] at hx
  obtain ⟨hprod, hn0⟩ := hx
  have hx1 : (x.1 : ℝ) ≠ 0 := by
    have : x.1 ≠ 0 := by rintro h; rw [h, zero_mul] at hprod; exact hn0 hprod.symm
    exact_mod_cast this
  have hx2 : (x.2 : ℝ) ≠ 0 := by
    have : x.2 ≠ 0 := by rintro h; rw [h, mul_zero] at hprod; exact hn0 hprod.symm
    exact_mod_cast this
  rw [logWeight_apply, logWeight_apply, ← hprod]
  push_cast [Real.log_mul hx1 hx2]
  ring

/-- The `k`-th iterate of the log derivation is the `(log n)^k` coefficient weight. -/
theorem logWeight_iterate_apply (k : ℕ) (f : ArithmeticFunction ℂ) (n : ℕ) :
    (logWeight^[k] f) n = (Real.log n : ℂ) ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', logWeight_apply, ih]
      ring

/-! ## Clearing finite-prime denominators -/

/-- **Clearing finite-prime denominators.**  A coefficient annihilated by a prime derivation is a
scalar for that derivation: `∂_q (s · f) = s · ∂_q f` whenever `∂_q s = 0`.  Together with
`primeDeriv_eq_zero_of_not_dvd_support` (finite-prime coefficients away from `q` are annihilated),
this makes finite-prime coefficients act as constants on the chosen derivations. -/
theorem primeDeriv_smul_of_annihilated (q : ℕ) (hq : q.Prime) (s f : ArithmeticFunction ℂ)
    (hs : primeDeriv q s = 0) :
    primeDeriv q (s * f) = s * primeDeriv q f := by
  rw [primeDeriv_mul q hq, hs, mul_zero, add_zero]

/-! ## The capstone -/

/-- **Operator-tail Dirichlet matroid capstone.**  For a finite-range family of prime coefficient
columns `a` and a finite shift palette `alpha` of pairwise-distinct real parts:

* full tail rank of *every* finite shift--jet operator rectangle is equivalent to scalar tail
  independence of the source columns (the operator-tail matroid collapses to the coefficient
  matroid); and
* that full operator-tail rank forces algebraic independence of the realized
  Dirichlet-convolution arithmetic functions `arithmeticOfPrimeColumn ∘ a`.

The first fact is Task 1; the second composes it with the Task 2 Jacobian bridge. -/
theorem operatorTail_algebraicIndependence
    {I : Type*} [Fintype I] [DecidableEq I] {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (a : I → Nat.Primes → ℂ) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun k => (alpha k).re))
    (hrange : (Set.range (coefficientPattern a)).Finite) :
    (CompleteShiftJetTailIndependent a (fun k p => primeShiftFactor (alpha k) p) primeLogClock
        ↔ TailCoefficientIndependent a) ∧
      (CompleteShiftJetTailIndependent a (fun k p => primeShiftFactor (alpha k) p) primeLogClock →
        AlgebraicIndependent ℂ (fun i => arithmeticOfPrimeColumn (a i))) := by
  have hiff := primeCompleteShiftJetTailIndependent_iff a alpha hdistinct hrange
  refine ⟨hiff, fun hfull => ?_⟩
  exact algebraicIndependent_arithmeticColumns_of_tailIndependent a (hiff.mp hfull)

/-- The realized arithmetic functions are in particular linearly independent over `ℂ` once the
operator-tail rank is full: a specialization of the capstone through algebraic independence. -/
theorem operatorTail_linearIndependent
    {I : Type*} [Fintype I] [DecidableEq I] {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (a : I → Nat.Primes → ℂ) (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun k => (alpha k).re))
    (hrange : (Set.range (coefficientPattern a)).Finite)
    (hfull : CompleteShiftJetTailIndependent a
      (fun k p => primeShiftFactor (alpha k) p) primeLogClock) :
    LinearIndependent ℂ (fun i => arithmeticOfPrimeColumn (a i)) :=
  ((operatorTail_algebraicIndependence a alpha hdistinct hrange).2 hfull).linearIndependent

end

end GaloisForLFunctions.HTGeometry
