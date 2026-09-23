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

Relation to `GaloisForLFunctions.HTGeometry.WeylEquidistribution.trig_time_average`, which gives the
`T → ∞` Cesàro limit of the same phase sum, namely `∑_{θ_i = 0} c_i`.  That statement is the
asymptotic diagonal extraction; what is proved here is the **exact identity at finite interval
length** together with error bounds that are uniform in the interval and its position
(`oscInt_norm_le`, `genPoly_meanValue_error`, `genPoly_meanValue_error_of_gap`).  The uniform bounds
are what a quantitative statement about the required averaging length needs, and they do not follow
from the limit form.
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

/-- Pointwise expansion of a product of two generalized Dirichlet polynomials with *different*
frequency families. -/
theorem genPoly_mul_conj_bilinear (a c : ℕ → ℂ) (lam mu : ℕ → ℝ) (s u : Finset ℕ) (t : ℝ) :
    genPoly a lam s t * (starRingEnd ℂ) (genPoly c mu u t)
      = ∑ n ∈ s, ∑ m ∈ u,
          a n * (starRingEnd ℂ) (c m)
            * Complex.exp (Complex.I * (((lam n - mu m : ℝ) : ℂ) * t)) := by
  have hc : ∀ r : ℝ, (starRingEnd ℂ) (Complex.I * ((r : ℂ) * (t : ℂ)))
      = -(Complex.I * ((r : ℂ) * (t : ℂ))) := by intro r; simp
  simp only [genPoly, map_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, ← Complex.exp_conj, hc]
  rw [show a n * Complex.exp (Complex.I * ((lam n : ℂ) * (t : ℂ)))
        * ((starRingEnd ℂ) (c m) * Complex.exp (-(Complex.I * ((mu m : ℂ) * (t : ℂ)))))
      = a n * (starRingEnd ℂ) (c m)
        * (Complex.exp (Complex.I * ((lam n : ℂ) * (t : ℂ)))
            * Complex.exp (-(Complex.I * ((mu m : ℂ) * (t : ℂ))))) from by ring,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Bilinear mean value.**  The correlation of two generalized Dirichlet polynomials over
`[T, T+U]` is the exact double sum of oscillatory integrals indexed by the frequency differences
`λ_n − μ_m`.  Dividing by `U` and letting `U → ∞` keeps exactly the *matched* pairs `λ_n = μ_m`:
this is the mechanism that turns a correlation of two exponential twists into a shifted convolution
of their coefficients. -/
theorem genPoly_meanValue_bilinear (a c : ℕ → ℂ) (lam mu : ℕ → ℝ) (s u : Finset ℕ) (T U : ℝ) :
    (∫ t in T..(T + U), genPoly a lam s t * (starRingEnd ℂ) (genPoly c mu u t))
      = ∑ n ∈ s, ∑ m ∈ u,
          a n * (starRingEnd ℂ) (c m) * oscInt (lam n - mu m) T U := by
  have hcont : ∀ n m : ℕ, IntervalIntegrable
      (fun t : ℝ => a n * (starRingEnd ℂ) (c m)
        * Complex.exp (Complex.I * (((lam n - mu m : ℝ) : ℂ) * t)))
      MeasureTheory.volume T (T + U) := by
    intro n m; apply Continuous.intervalIntegrable; fun_prop
  have hcont2 : ∀ n : ℕ, IntervalIntegrable
      (fun t : ℝ => ∑ m ∈ u, a n * (starRingEnd ℂ) (c m)
        * Complex.exp (Complex.I * (((lam n - mu m : ℝ) : ℂ) * t)))
      MeasureTheory.volume T (T + U) := by
    intro n
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ (fun m _ => by fun_prop)
  rw [intervalIntegral.integral_congr (fun t _ => genPoly_mul_conj_bilinear a c lam mu s u t)]
  rw [intervalIntegral.integral_finsetSum (f := fun n t =>
        ∑ m ∈ u, a n * (starRingEnd ℂ) (c m)
          * Complex.exp (Complex.I * (((lam n - mu m : ℝ) : ℂ) * t)))
      (fun n _ => hcont2 n)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_finsetSum (f := fun m t =>
        a n * (starRingEnd ℂ) (c m)
          * Complex.exp (Complex.I * (((lam n - mu m : ℝ) : ℂ) * t)))
      (fun m _ => hcont n m)]
  exact Finset.sum_congr rfl fun m _ => by rw [oscInt]; exact intervalIntegral.integral_const_mul _ _

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

/-- **Diagonal extraction under a uniform frequency gap.**  If the frequencies of a generalized
Dirichlet polynomial are separated by at least `g > 0`, then its mean square over any interval equals
the interval length times the diagonal energy, up to an error bounded by `(2/g)(∑‖a n‖)²`
**independently of the interval, its length and its position**.  Dividing by the length `U` and
letting `U → ∞` therefore isolates the diagonal, at averaging length `U ≫ (∑‖a n‖)²/(g·diagonal)`.

This is the rigorous core of the Bohr method: a uniform frequency gap converts a mean square into a
diagonal sum with an error that does not grow.  Frequencies `λ_n = n` (an additive twist) have gap
`1`; frequencies `λ_n = n^{1/d}` with `d ≥ 2` have gaps tending to `0`, and no such uniform statement
is available — which is exactly where the degree barrier lives. -/
theorem genPoly_meanValue_error_of_gap (a : ℕ → ℂ) (lam : ℕ → ℝ) (s : Finset ℕ) (T U g : ℝ)
    (hg : 0 < g) (hgap : ∀ n ∈ s, ∀ m ∈ s, m ≠ n → g ≤ |lam m - lam n|) :
    ‖(∫ t in T..(T + U), genPoly a lam s t * (starRingEnd ℂ) (genPoly a lam s t))
        - (U : ℂ) * (∑ n ∈ s, a n * (starRingEnd ℂ) (a n))‖
      ≤ (2 / g) * (∑ n ∈ s, ‖a n‖) ^ (2 : ℕ) := by
  have hne : ∀ n ∈ s, ∀ m ∈ s, m ≠ n → lam m - lam n ≠ 0 := by
    intro n hn m hm hmn h0
    have := hgap n hn m hm hmn
    rw [h0] at this
    simp at this
    linarith
  refine le_trans (genPoly_meanValue_error a lam s T U hne) ?_
  have hbound : ∀ n ∈ s, ∑ m ∈ s.erase n, ‖a m‖ * ‖a n‖ * (2 / |lam m - lam n|)
      ≤ ∑ m ∈ s, ‖a m‖ * ‖a n‖ * (2 / g) := by
    intro n hn
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun m _ _ => by positivity)) (Finset.sum_le_sum fun m hm => ?_)
    rcases eq_or_ne m n with rfl | hmn
    · simp
      positivity
    · have hgn := hgap n hn m hm hmn
      have habs : (0 : ℝ) < |lam m - lam n| := lt_of_lt_of_le hg hgn
      have : (2 : ℝ) / |lam m - lam n| ≤ 2 / g := by
        apply div_le_div_of_nonneg_left (by norm_num) hg hgn
      exact mul_le_mul_of_nonneg_left this (by positivity)
  refine le_trans (Finset.sum_le_sum hbound) ?_
  have h1 : ∀ n : ℕ, ∑ m ∈ s, ‖a m‖ * ‖a n‖ * (2 / g)
      = (‖a n‖ * (2 / g)) * ∑ m ∈ s, ‖a m‖ := by
    intro n
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  have h2 : ∑ n ∈ s, ∑ m ∈ s, ‖a m‖ * ‖a n‖ * (2 / g)
      = (2 / g) * (∑ n ∈ s, ‖a n‖) ^ (2 : ℕ) := by
    simp only [h1, ← Finset.sum_mul]
    rw [sq]
    ring
  exact le_of_eq h2

end


/-- **Almost-orthonormality of an exponential family on a long interval.**  With the normalised
form `B(u,v) = U⁻¹∫_T^{T+U} u \bar v`, the family `t ↦ exp(i λᵢ t)` has Gram entries within
`2/(g·U)` of the identity matrix, where `g` is the minimal gap between the frequencies.

Combined with `HTGeometry.bessel_of_almost_orthogonal` this is the finite-interval form of Bessel's
inequality for Fourier–Bohr coefficients: the sum of squared correlations of any function with the
tones `λᵢ` is at most `(1 + card·2/(g·U))` times its own mean square.  Letting `U → ∞` with the
frequencies fixed recovers exact orthonormality. -/
theorem oscInt_gram_bound {ι : Type*} [DecidableEq ι] (lam : ι → ℝ) (T U g : ℝ)
    (hU : 0 < U) (hg : 0 < g) (hgap : ∀ i j : ι, i ≠ j → g ≤ |lam i - lam j|) (i j : ι) :
    ‖((U : ℂ))⁻¹ * oscInt (lam i - lam j) T U - (if i = j then (1 : ℂ) else 0)‖ ≤ 2 / (g * U) := by
  by_cases h : i = j
  · subst h
    have hUne : ((U : ℂ)) ≠ 0 := by
      simpa using ne_of_gt hU
    simp [oscInt_zero, inv_mul_cancel₀ hUne]
    positivity
  · have hδ : lam i - lam j ≠ 0 := by
      intro hzero
      have := hgap i j h
      rw [hzero, abs_zero] at this
      linarith
    have hb := oscInt_norm_le (lam i - lam j) T U hδ
    have hgle : g ≤ |lam i - lam j| := hgap i j h
    have hUne : ((U : ℂ)) ≠ 0 := by simpa using ne_of_gt hU
    rw [if_neg h, sub_zero, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hU]
    have h1 : ‖oscInt (lam i - lam j) T U‖ ≤ 2 / g := by
      refine le_trans hb ?_
      exact div_le_div_of_nonneg_left (by norm_num) hg hgle
    calc U⁻¹ * ‖oscInt (lam i - lam j) T U‖ ≤ U⁻¹ * (2 / g) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hU))
      _ = 2 / (g * U) := by field_simp

end HTGeometry
