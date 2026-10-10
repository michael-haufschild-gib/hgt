import GaloisForLFunctions.RHTower.JointAncestryLagAggregatePositivityAbscissa

/-!
# Bernoulli tests of the dressed JAS aggregate

The `σ`-dressed lag aggregate is the zero sum

`N_σ(n) = Σ_ρ C_ρ(n) / (ρ(1-ρ))`,   `C_ρ(n) = ∏_p A_p^{n_p⁺} B_p^{n_p⁻}`,

with dressed local parameters `A_p = p^{-(ρ + c)}`, `B_p = p^{-(1 - ρ + c)}`, `c = σ - 1/2`.

Testing positive semidefiniteness on the squarefree characters `d | ∏_{p ∈ P} p` with
multiplicative weights `∏_{p | d} z_p` factorizes prime by prime: the quadratic form becomes

`Σ_ρ (1/(ρ(1-ρ))) ∏_{p ∈ P} (1 + z_p A_p + z̄_p B_p + |z_p|²)`.

Hence positivity of the dressed aggregate forces positivity of these Bernoulli products summed over
the zeros, for every finite prime set and every choice of local weights.  This turns the abstract
positivity condition into pointwise inequalities to which the single-sector phase and amplitude
laws apply zero by zero.
-/

open Complex
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

/-! ## Dressed coefficients -/

/-- Local coefficient with independent forward and backward parameters. -/
def jasDressedLocalCoeff (s₁ s₂ : ℂ) (p : Nat.Primes) (k : ℤ) : ℂ :=
  if 0 ≤ k then jasHoloA s₁ p ^ k.toNat else jasHoloB s₂ p ^ (-k).toNat

/-- Coefficient `u^{-s₁} v^{-(1-s₂)}` at the rational character `n = u/v`. -/
def jasDressedCoeff (s₁ s₂ : ℂ) (n : Nat.Primes →₀ ℤ) : ℂ :=
  n.prod fun p k => jasDressedLocalCoeff s₁ s₂ p k

theorem jasDressedLocalCoeff_eq_exp (s₁ s₂ : ℂ) (p : Nat.Primes) (k : ℤ) :
    jasDressedLocalCoeff s₁ s₂ p k =
      cexp (-s₁ * ((k.toNat : ℝ) * Real.log p : ℝ) -
        (1 - s₂) * (((-k).toNat : ℝ) * Real.log p : ℝ)) := by
  unfold jasDressedLocalCoeff jasHoloA jasHoloB
  split
  · rename_i hk
    have : (-k).toNat = 0 := by omega
    rw [this, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  · rename_i hk
    have : k.toNat = 0 := by omega
    rw [this, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

theorem jasDressedCoeff_eq_exp (s₁ s₂ : ℂ) (n : Nat.Primes →₀ ℤ) :
    jasDressedCoeff s₁ s₂ n = cexp (-s₁ * (jasLogPos n : ℂ) - (1 - s₂) * (jasLogNeg n : ℂ)) := by
  unfold jasDressedCoeff jasLogPos jasLogNeg Finsupp.prod Finsupp.sum
  simp_rw [jasDressedLocalCoeff_eq_exp]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- Dressing by `μ_c` shifts the forward parameter to `ρ + c` and the backward one to `ρ - c`. -/
theorem exp_mul_jasHoloCoeff (c : ℝ) (ρ : ℂ) (n : Nat.Primes →₀ ℤ) :
    (Real.exp (-c * jasLogSize n) : ℂ) * jasHoloCoeff ρ n =
      jasDressedCoeff (ρ + c) (ρ - c) n := by
  rw [jasHoloCoeff_eq_exp, jasDressedCoeff_eq_exp, Complex.ofReal_exp, ← Complex.exp_add,
    jasLogSize]
  congr 1
  push_cast
  ring

theorem jasDressedLagAggregate_eq_tsum (σ : ℝ) (n : Nat.Primes →₀ ℤ) :
    jasDressedLagAggregate σ n = ∑' q : XiZeroCopy,
      jasDressedCoeff ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) n /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := by
  have h : jasDressedLagAggregate σ n =
      (Real.exp (-(σ - 1 / 2) * jasLogSize n) : ℂ) * jasLagAggregate n := by
    rw [jasLagAggregate_eq, jasDressedLagAggregate, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.exp_add, jasLogSize]
    congr 3
    ring
  rw [h, jasLagAggregate, ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [← mul_div_assoc, exp_mul_jasHoloCoeff]

theorem summable_jasDressedCoeff_term (σ : ℝ) (n : Nat.Primes →₀ ℤ) :
    Summable (fun q : XiZeroCopy =>
      jasDressedCoeff ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) n /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
  refine ((summable_jasLagAggregate_term n).mul_left
    (Real.exp (-(σ - 1 / 2) * jasLogSize n) : ℂ)).congr fun q => ?_
  rw [← mul_div_assoc, exp_mul_jasHoloCoeff]

/-! ## Squarefree characters -/

/-- The squarefree character `∏_{p ∈ P, x_p} p`. -/
def jasBernoulliChar (P : Finset Nat.Primes) (x : P → Bool) : Nat.Primes →₀ ℤ :=
  Finsupp.onFinset P (fun p => if h : p ∈ P then (if x ⟨p, h⟩ then 1 else 0) else 0) (by
    intro p hp
    by_contra h
    simp [h] at hp)

theorem jasBernoulliChar_apply_mem (P : Finset Nat.Primes) (x : P → Bool) (p : P) :
    jasBernoulliChar P x p = if x p then 1 else 0 := by
  simp [jasBernoulliChar, p.2]

theorem jasBernoulliChar_apply_not_mem (P : Finset Nat.Primes) (x : P → Bool) {p : Nat.Primes}
    (hp : p ∉ P) : jasBernoulliChar P x p = 0 := by
  simp [jasBernoulliChar, hp]

theorem jasBernoulliChar_injective (P : Finset Nat.Primes) :
    Function.Injective (jasBernoulliChar P) := by
  intro x y h
  funext p
  have := congrArg (fun n : Nat.Primes →₀ ℤ => n p) h
  simp only [jasBernoulliChar_apply_mem] at this
  cases hx : x p <;> cases hy : y p <;> simp_all

/-- Coefficients of a difference of squarefree characters factor over `P`. -/
theorem jasDressedCoeff_bernoulliChar_sub (s₁ s₂ : ℂ) (P : Finset Nat.Primes) (x y : P → Bool) :
    jasDressedCoeff s₁ s₂ (jasBernoulliChar P x - jasBernoulliChar P y) =
      ∏ p : P, jasDressedLocalCoeff s₁ s₂ p
        ((if x p then 1 else 0) - (if y p then 1 else 0)) := by
  rw [jasDressedCoeff, Finsupp.prod_of_support_subset _ (s := P)]
  · rw [← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [Finsupp.sub_apply, jasBernoulliChar_apply_mem, jasBernoulliChar_apply_mem]
  · intro p hp
    by_contra h
    apply Finsupp.mem_support_iff.mp hp
    rw [Finsupp.sub_apply, jasBernoulliChar_apply_not_mem _ _ h,
      jasBernoulliChar_apply_not_mem _ _ h, sub_zero]
  · intro p _
    simp [jasDressedLocalCoeff]

/-! ## Factorization of the Bernoulli quadratic form -/

/-- The local Bernoulli factor `1 + zA + z̄B + |z|²`. -/
def jasBernoulliFactor (A B z : ℂ) : ℂ := 1 + z * A + conj z * B + z * conj z

/-- Multiplicative weight of a squarefree character. -/
def jasBernoulliWeight (P : Finset Nat.Primes) (z : Nat.Primes → ℂ) (x : P → Bool) : ℂ :=
  ∏ p : P, if x p then z p else 1

theorem sum_sum_prod_eq_prod_sum_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Bool → Bool → ℂ) :
    ∑ x : ι → Bool, ∑ y : ι → Bool, ∏ i, F i (x i) (y i) = ∏ i, ∑ a, ∑ b, F i a b := by
  rw [Fintype.prod_sum]
  refine Fintype.sum_congr _ _ fun x => ?_
  rw [Fintype.prod_sum]

theorem jasBernoulliLocal_sum (A B z : ℂ) :
    ∑ a : Bool, ∑ b : Bool, (if a then z else 1) * conj (if b then z else 1) *
      (if 0 ≤ ((if a then 1 else 0) - (if b then 1 else 0) : ℤ)
        then A ^ ((if a then 1 else 0) - (if b then 1 else 0) : ℤ).toNat
        else B ^ (-((if a then 1 else 0) - (if b then 1 else 0)) : ℤ).toNat) =
      jasBernoulliFactor A B z := by
  simp [jasBernoulliFactor]
  ring

/-- **Bernoulli factorization.**  On squarefree characters with multiplicative weights the
quadratic form of a dressed coefficient is a product of local Bernoulli factors. -/
theorem sum_sum_bernoulli_jasDressedCoeff (s₁ s₂ : ℂ) (P : Finset Nat.Primes)
    (z : Nat.Primes → ℂ) :
    ∑ x : P → Bool, ∑ y : P → Bool, jasBernoulliWeight P z x * conj (jasBernoulliWeight P z y) *
      jasDressedCoeff s₁ s₂ (jasBernoulliChar P x - jasBernoulliChar P y) =
      ∏ p ∈ P, jasBernoulliFactor (jasHoloA s₁ p) (jasHoloB s₂ p) (z p) := by
  classical
  have hterm : ∀ x y : P → Bool, jasBernoulliWeight P z x * conj (jasBernoulliWeight P z y) *
      jasDressedCoeff s₁ s₂ (jasBernoulliChar P x - jasBernoulliChar P y) =
      ∏ p : P, ((if x p then z p else 1) * conj (if y p then z p else 1) *
        jasDressedLocalCoeff s₁ s₂ p ((if x p then 1 else 0) - (if y p then 1 else 0))) := by
    intro x y
    rw [jasDressedCoeff_bernoulliChar_sub, jasBernoulliWeight, jasBernoulliWeight, map_prod,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  simp_rw [hterm]
  rw [sum_sum_prod_eq_prod_sum_sum (fun (p : P) a b => (if a then z p else 1) *
      conj (if b then z p else 1) *
      jasDressedLocalCoeff s₁ s₂ p ((if a then 1 else 0) - (if b then 1 else 0))),
    ← Finset.prod_coe_sort P]
  refine Finset.prod_congr rfl fun p _ => ?_
  exact jasBernoulliLocal_sum _ _ _

/-- **Bernoulli positivity.**  If the `σ`-dressed aggregate is positive semidefinite then for every
finite prime set `P` and all local weights `z_p`,

`Re Σ_ρ (1/(ρ(1-ρ))) ∏_{p ∈ P} (1 + z_p p^{-(ρ+c)} + z̄_p p^{-(1-ρ+c)} + |z_p|²) ≥ 0`. -/
theorem jasBernoulliAggregate_nonneg {σ : ℝ} (h : JasDressedPSD σ) (P : Finset Nat.Primes)
    (z : Nat.Primes → ℂ) :
    0 ≤ (∑' q : XiZeroCopy,
      (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  classical
  have hPSD := h (P → Bool) Finset.univ (jasBernoulliWeight P z) (jasBernoulliChar P)
    ((jasBernoulliChar_injective P).injOn)
  have heq : ∑ x ∈ (Finset.univ : Finset (P → Bool)), ∑ y ∈ (Finset.univ : Finset (P → Bool)),
      jasBernoulliWeight P z x * conj (jasBernoulliWeight P z y) *
        jasDressedLagAggregate σ (jasBernoulliChar P x - jasBernoulliChar P y) =
      ∑' q : XiZeroCopy,
        (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
          (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := by
    set c : ℝ := σ - 1 / 2
    have hs : ∀ x y : P → Bool, Summable (fun q : XiZeroCopy =>
        jasBernoulliWeight P z x * conj (jasBernoulliWeight P z y) *
          (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c)
            (jasBernoulliChar P x - jasBernoulliChar P y) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))) :=
      fun x y => (summable_jasDressedCoeff_term σ _).mul_left _
    calc _ = ∑ x : P → Bool, ∑ y : P → Bool, ∑' q : XiZeroCopy,
          jasBernoulliWeight P z x * conj (jasBernoulliWeight P z y) *
            (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c)
              (jasBernoulliChar P x - jasBernoulliChar P y) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
          simp_rw [jasDressedLagAggregate_eq_tsum, ← tsum_mul_left]
          rfl
      _ = ∑ x : P → Bool, ∑' q : XiZeroCopy, ∑ y : P → Bool,
          jasBernoulliWeight P z x * conj (jasBernoulliWeight P z y) *
            (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c)
              (jasBernoulliChar P x - jasBernoulliChar P y) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) :=
          Finset.sum_congr rfl fun x _ => (Summable.tsum_finsetSum fun y _ => hs x y).symm
      _ = ∑' q : XiZeroCopy, ∑ x : P → Bool, ∑ y : P → Bool,
          jasBernoulliWeight P z x * conj (jasBernoulliWeight P z y) *
            (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c)
              (jasBernoulliChar P x - jasBernoulliChar P y) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) :=
          (Summable.tsum_finsetSum fun x _ => summable_sum fun y _ => hs x y).symm
      _ = _ := by
          refine tsum_congr fun q => ?_
          rw [← sum_sum_bernoulli_jasDressedCoeff, Finset.sum_div]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
  rw [heq] at hPSD
  exact hPSD

end

end RHTower
