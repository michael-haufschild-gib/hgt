import GaloisForLFunctions.RHTower.Sieve.EulerExpansion

/-!
# The damped sum indexed by integers

The subset sum of the Euler expansion becomes a Dirichlet sum over integers once each subset factor
is collapsed:

`∏_{p ∈ T} f(p) p^{-it}/p = f(n) n^{-it}/n`,  `n = ∏_{p ∈ T} p`,

using multiplicativity of `f` across the distinct primes of `T`, additivity of `log` on the product,
and `∏_{p ∈ T} 1/p = 1/n`.  Since `T ↦ ∏_{p ∈ T} p` is injective on subsets of a set of primes, the
reindexed sum runs over distinct squarefree `P`-smooth integers and

`‖∑_{n squarefree, P-smooth} f(n) n^{-it}/n‖ ≤ exp(∑_{p ∈ P} 1/p + ∑_{p ∈ P} 1/p² - D(f,t;P)²)`.
-/

namespace RHTower.Sieve

open Finset

/-- A multiplicative function on a product of distinct primes. -/
theorem prod_eq_of_multiplicative {f : ℕ → ℂ}
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) (h1 : f 1 = 1) :
    ∀ {T : Finset ℕ}, (∀ p ∈ T, p.Prime) → ∏ p ∈ T, f p = f (∏ p ∈ T, p) := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty => intro _; simpa using h1.symm
  | insert a S ha ih =>
      intro hT
      have hS : ∀ p ∈ S, p.Prime := fun p hp => hT p (Finset.mem_insert_of_mem hp)
      have hap : a.Prime := hT a (Finset.mem_insert_self a S)
      have hcop : Nat.Coprime a (∏ p ∈ S, p) := by
        refine Nat.Coprime.prod_right fun q hq => ?_
        exact (Nat.coprime_primes hap (hS q hq)).mpr fun h => ha (h ▸ hq)
      rw [Finset.prod_insert ha, Finset.prod_insert ha, hmul a _ hcop, ih hS]

/-- The subset factor is the integer term. -/
theorem prod_term_eq {f : ℕ → ℂ} (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    (h1 : f 1 = 1) (t : ℝ) {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) :
    ∏ p ∈ T, (((1 / (p : ℝ) : ℝ) : ℂ)
        * (f p * Complex.exp (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I)))
      = ((1 / ((∏ p ∈ T, p : ℕ) : ℝ) : ℝ) : ℂ)
        * (f (∏ p ∈ T, p)
          * Complex.exp (((-(t * Real.log ((∏ p ∈ T, p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) := by
  classical
  have hpos : ∀ p ∈ T, (0 : ℝ) < (p : ℝ) := fun p hp => by
    exact_mod_cast (hT p hp).pos
  have hlog : Real.log ((∏ p ∈ T, p : ℕ) : ℝ) = ∑ p ∈ T, Real.log (p : ℝ) := by
    rw [Nat.cast_prod]
    exact Real.log_prod fun p hp => ne_of_gt (hpos p hp)
  have hrecip : ∏ p ∈ T, ((1 / (p : ℝ) : ℝ) : ℂ)
      = ((1 / ((∏ p ∈ T, p : ℕ) : ℝ) : ℝ) : ℂ) := by
    push_cast
    rw [Finset.prod_div_distrib, Finset.prod_const_one]
  have hf : ∏ p ∈ T, f p = f (∏ p ∈ T, p) := prod_eq_of_multiplicative hmul h1 hT
  have hexp : ∏ p ∈ T, Complex.exp (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((-(t * Real.log ((∏ p ∈ T, p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_sum, ← Finset.sum_mul, hlog]
    congr 2
    push_cast
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
  calc ∏ p ∈ T, (((1 / (p : ℝ) : ℝ) : ℂ)
        * (f p * Complex.exp (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I)))
      = (∏ p ∈ T, ((1 / (p : ℝ) : ℝ) : ℂ)) * ((∏ p ∈ T, f p)
          * ∏ p ∈ T, Complex.exp (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ = ((1 / ((∏ p ∈ T, p : ℕ) : ℝ) : ℝ) : ℂ)
        * (f (∏ p ∈ T, p)
          * Complex.exp (((-(t * Real.log ((∏ p ∈ T, p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) := by
        rw [hrecip, hf, hexp]

/-- **The Dirichlet sum over squarefree `P`-smooth integers, damped by the distance.** -/
theorem norm_sum_smooth_le_exp {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) (h1 : f 1 = 1) (t : ℝ)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    ‖∑ n ∈ P.powerset.image (fun T => ∏ p ∈ T, p), ((1 / (n : ℝ) : ℝ) : ℂ)
        * (f n * Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I))‖
      ≤ Real.exp ((∑ p ∈ P, 1 / (p : ℝ)) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) - mulDistSq f t P) := by
  classical
  have hinj : ∀ S ∈ P.powerset, ∀ T ∈ P.powerset,
      (∏ p ∈ S, p) = (∏ p ∈ T, p) → S = T := by
    intro S hS T hT hST
    exact prod_injOn_powerset hP (by simpa using hS) (by simpa using hT) hST
  rw [Finset.sum_image hinj]
  have hterm : ∀ T ∈ P.powerset,
      ((1 / ((∏ p ∈ T, p : ℕ) : ℝ) : ℝ) : ℂ)
        * (f (∏ p ∈ T, p)
          * Complex.exp (((-(t * Real.log ((∏ p ∈ T, p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))
      = ∏ p ∈ T, (((1 / (p : ℝ) : ℝ) : ℂ)
          * (f p * Complex.exp (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I))) := by
    intro T hT
    exact (prod_term_eq hmul h1 t fun p hp => hP p (Finset.mem_powerset.mp hT hp)).symm
  rw [Finset.sum_congr rfl hterm]
  exact norm_sum_powerset_le_exp hf t fun p hp => (hP p hp).pos

end RHTower.Sieve
