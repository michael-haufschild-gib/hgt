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

/-- Closed form of the oscillatory integral at a non-zero frequency. -/
theorem oscInt_eq (δ T U : ℝ) (hδ : δ ≠ 0) :
    oscInt δ T U
      = (Complex.exp (Complex.I * (δ : ℂ) * ((T + U : ℝ) : ℂ))
          - Complex.exp (Complex.I * (δ : ℂ) * (T : ℂ))) / (Complex.I * (δ : ℂ)) := by
  have hc : Complex.I * (δ : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, hδ]
  have := integral_exp_mul_complex (a := T) (b := T + U) hc
  rw [oscInt]
  rw [show (fun t : ℝ => Complex.exp (Complex.I * ((δ : ℂ) * t)))
      = (fun t : ℝ => Complex.exp (Complex.I * (δ : ℂ) * t)) from by
    funext t; ring_nf]
  rw [this]

/-- **Uniform bound on the oscillatory integral.**  At a non-zero frequency the integral is bounded
by `2/|δ|` *independently of the length of the interval*: only the diagonal accumulates. -/
theorem oscInt_norm_le (δ T U : ℝ) (hδ : δ ≠ 0) : ‖oscInt δ T U‖ ≤ 2 / |δ| := by
  rw [oscInt_eq δ T U hδ, norm_div]
  have h1 : ‖Complex.exp (Complex.I * (δ : ℂ) * ((T + U : ℝ) : ℂ))‖ = 1 := by
    rw [show Complex.I * (δ : ℂ) * ((T + U : ℝ) : ℂ)
        = ((δ * (T + U) : ℝ) : ℂ) * Complex.I from by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have h2 : ‖Complex.exp (Complex.I * (δ : ℂ) * (T : ℂ))‖ = 1 := by
    rw [show Complex.I * (δ : ℂ) * (T : ℂ) = ((δ * T : ℝ) : ℂ) * Complex.I from by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hden : ‖Complex.I * (δ : ℂ)‖ = |δ| := by
    simp [Complex.norm_I]
  have hnum : ‖Complex.exp (Complex.I * (δ : ℂ) * ((T + U : ℝ) : ℂ))
      - Complex.exp (Complex.I * (δ : ℂ) * (T : ℂ))‖ ≤ 2 := by
    calc _ ≤ ‖Complex.exp (Complex.I * (δ : ℂ) * ((T + U : ℝ) : ℂ))‖
            + ‖Complex.exp (Complex.I * (δ : ℂ) * (T : ℂ))‖ := norm_sub_le _ _
      _ = 2 := by rw [h1, h2]; norm_num
  have hpos : 0 < |δ| := abs_pos.2 hδ
  rw [hden]
  gcongr

/-- **Bohr–Parseval with an explicit interval-independent error.**  For a generalized Dirichlet
polynomial with pairwise distinct frequencies, the mean square over `[T, T+U]` differs from `U`
times the diagonal energy by an amount bounded independently of `T` and `U`.  Dividing by `U` and
letting `U → ∞` therefore isolates the diagonal exactly: this is the mechanism that extracts the
Rankin–Selberg diagonal from a horizontal mean of an exponential twist. -/
theorem genPoly_meanValue_error (a : ℕ → ℂ) (lam : ℕ → ℝ) (s : Finset ℕ) (T U : ℝ)
    (hlam : ∀ n ∈ s, ∀ m ∈ s, m ≠ n → lam m - lam n ≠ 0) :
    ‖(∫ t in T..(T + U), genPoly a lam s t * (starRingEnd ℂ) (genPoly a lam s t))
        - (U : ℂ) * (∑ n ∈ s, a n * (starRingEnd ℂ) (a n))‖
      ≤ ∑ n ∈ s, ∑ m ∈ s.erase n, ‖a m‖ * ‖a n‖ * (2 / |lam m - lam n|) := by
  rw [genPoly_meanValue a lam s T U, add_sub_cancel_left]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n hn => ?_)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m hm => ?_)
  have hne : lam m - lam n ≠ 0 :=
    hlam n hn m (Finset.mem_of_mem_erase hm) (Finset.ne_of_mem_erase hm)
  rw [norm_mul, norm_mul, RCLike.norm_conj]
  exact mul_le_mul_of_nonneg_left (oscInt_norm_le _ T U hne) (by positivity)

end

end HTGeometry
