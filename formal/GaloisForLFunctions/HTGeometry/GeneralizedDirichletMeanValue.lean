import Mathlib

/-!
# Mean value of a generalized Dirichlet polynomial with arbitrary real frequencies

A *generalized Dirichlet polynomial* is a finite exponential sum
`P(t) = ∑_{n ∈ s} a n · exp(i λ_n t)` with complex coefficients `a n` and arbitrary real
frequencies `λ_n`.  Its mean square over an interval splits into a diagonal term, proportional to
the length of the interval and to `∑ |a n|²`, and an explicit off-diagonal double sum of oscillatory
integrals indexed by the frequency differences `λ_m − λ_n`.

The classical Dirichlet-polynomial case is `λ_n = log n`, where the frequency differences are
`log(m/n)`.  The case `λ_n = n^{1/d}` is the one attached to the degree-`d` exponential twist of a
Dirichlet series with a functional equation of degree `d`; there the frequency differences satisfy
`|m^{1/d} − n^{1/d}| ≍ |m − n| · max(m,n)^{1/d − 1}`, so the diagonal is isolated only for `d = 1`.

Everything here is unconditional and exact: no asymptotic estimate is used, only the exact
evaluation of `∫ exp(i·0·t) dt` on the diagonal.
-/

open Finset Complex

namespace HTGeometry

noncomputable section

/-- A generalized Dirichlet polynomial: a finite exponential sum with arbitrary real
frequencies. -/
def genPoly (a : ℕ → ℂ) (lam : ℕ → ℝ) (s : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ s, a n * Complex.exp (Complex.I * (lam n * t))

/-- The oscillatory integral attached to a frequency difference `δ` over `[T, T+U]`. -/
def oscInt (δ T U : ℝ) : ℂ :=
  ∫ t in T..(T + U), Complex.exp (Complex.I * ((δ : ℂ) * t))

/-- At frequency zero the oscillatory integral is the length of the interval. -/
theorem oscInt_zero (T U : ℝ) : oscInt 0 T U = (U : ℂ) := by
  simp [oscInt]

/-- Exact expansion of the modulus square of a generalized Dirichlet polynomial as a double sum
over frequency differences. -/
theorem genPoly_mul_conj (a : ℕ → ℂ) (lam : ℕ → ℝ) (s : Finset ℕ) (t : ℝ) :
    genPoly a lam s t * (starRingEnd ℂ) (genPoly a lam s t)
      = ∑ n ∈ s, ∑ m ∈ s,
          a m * (starRingEnd ℂ) (a n)
            * Complex.exp (Complex.I * (((lam m - lam n : ℝ) : ℂ) * t)) := by
  have hc : ∀ r : ℝ, (starRingEnd ℂ) (Complex.I * ((r : ℂ) * (t : ℂ)))
      = -(Complex.I * ((r : ℂ) * (t : ℂ))) := by intro r; simp
  simp only [genPoly, map_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, ← Complex.exp_conj, hc]
  rw [show a m * Complex.exp (Complex.I * ((lam m : ℂ) * (t : ℂ)))
        * ((starRingEnd ℂ) (a n) * Complex.exp (-(Complex.I * ((lam n : ℂ) * (t : ℂ)))))
      = a m * (starRingEnd ℂ) (a n)
        * (Complex.exp (Complex.I * ((lam m : ℂ) * (t : ℂ)))
            * Complex.exp (-(Complex.I * ((lam n : ℂ) * (t : ℂ))))) from by ring,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Mean value of a generalized Dirichlet polynomial.**  The mean square over `[T, T+U]` is the
interval length times the diagonal energy `∑ a n · conj (a n)`, plus the exact off-diagonal double
sum of oscillatory integrals indexed by the frequency differences.  No hypothesis on the
frequencies is needed. -/
theorem genPoly_meanValue (a : ℕ → ℂ) (lam : ℕ → ℝ) (s : Finset ℕ) (T U : ℝ) :
    (∫ t in T..(T + U), genPoly a lam s t * (starRingEnd ℂ) (genPoly a lam s t))
      = (U : ℂ) * (∑ n ∈ s, a n * (starRingEnd ℂ) (a n))
        + ∑ n ∈ s, ∑ m ∈ s.erase n,
            a m * (starRingEnd ℂ) (a n) * oscInt (lam m - lam n) T U := by
  have hcont : ∀ n m : ℕ, IntervalIntegrable
      (fun t : ℝ => a m * (starRingEnd ℂ) (a n)
        * Complex.exp (Complex.I * (((lam m - lam n : ℝ) : ℂ) * t)))
      MeasureTheory.volume T (T + U) := by
    intro n m; apply Continuous.intervalIntegrable; fun_prop
  have hcont2 : ∀ n : ℕ, IntervalIntegrable
      (fun t : ℝ => ∑ m ∈ s, a m * (starRingEnd ℂ) (a n)
        * Complex.exp (Complex.I * (((lam m - lam n : ℝ) : ℂ) * t)))
      MeasureTheory.volume T (T + U) := by
    intro n
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ (fun m _ => by fun_prop)
  have hterm : ∀ n m : ℕ,
      (∫ t in T..(T + U), a m * (starRingEnd ℂ) (a n)
          * Complex.exp (Complex.I * (((lam m - lam n : ℝ) : ℂ) * t)))
        = a m * (starRingEnd ℂ) (a n) * oscInt (lam m - lam n) T U := by
    intro n m; rw [oscInt]; exact intervalIntegral.integral_const_mul _ _
  rw [intervalIntegral.integral_congr (fun t _ => genPoly_mul_conj a lam s t)]
  rw [intervalIntegral.integral_finsetSum (f := fun n t =>
        ∑ m ∈ s, a m * (starRingEnd ℂ) (a n)
          * Complex.exp (Complex.I * (((lam m - lam n : ℝ) : ℂ) * t)))
      (fun n _ => hcont2 n)]
  have hinner : ∀ n ∈ s,
      (∫ t in T..(T + U), ∑ m ∈ s, a m * (starRingEnd ℂ) (a n)
          * Complex.exp (Complex.I * (((lam m - lam n : ℝ) : ℂ) * t)))
        = a n * (starRingEnd ℂ) (a n) * (U : ℂ)
          + ∑ m ∈ s.erase n, a m * (starRingEnd ℂ) (a n) * oscInt (lam m - lam n) T U := by
    intro n hn
    rw [intervalIntegral.integral_finsetSum (f := fun m t =>
          a m * (starRingEnd ℂ) (a n)
            * Complex.exp (Complex.I * (((lam m - lam n : ℝ) : ℂ) * t)))
        (fun m _ => hcont n m),
      ← Finset.add_sum_erase _ _ hn]
    congr 1
    · rw [hterm n n, sub_self, oscInt_zero]
    · exact Finset.sum_congr rfl fun m _ => hterm n m
  rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun n _ => by ring

end

end HTGeometry
