import GaloisForLFunctions.RHTower.VanDerCorput

/-!
# The oscillatory cross of two Dirichlet polynomials

Levinson's mollified mean square splits into a direct×direct term, a dual×dual term and a cross
term.  The cross carries the archimedean phase of `χ`, so each of its `#S · #T` frequencies is
`g′(τ) + log n − log m`.  When the mollifier length is `T^θ` with `θ < 1/2` **strictly**, the
saddle `τ = 2π m/n` has left the window and every one of those frequencies is bounded below by
`(1/2 − θ) log T − O(1)`.  The first-derivative test then bounds each oscillatory integral by
`2/λ`, and the whole cross by the product of the two `ℓ¹` masses divided by `λ`.

This file is the general estimate; the arithmetic input — the frequency lower bound — is a
hypothesis, discharged downstream from the mollifier length.
-/

open Complex MeasureTheory Set intervalIntegral
open scoped Interval

noncomputable section

namespace RHTower

/-- **The oscillatory cross bound.**  With every combined frequency bounded below by `lam > 0` and
the phase derivative nondecreasing, the cross of two Dirichlet polynomials against `exp(i g)` is at
most `2/lam` times the product of the coefficient `ℓ¹` masses. -/
theorem norm_integral_dirichletCross_cexp_le
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (e f : ℕ → ℂ) (S T : Finset ℕ)
    {g g' g'' : ℝ → ℝ}
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc a b, HasDerivAt g' (g'' x) x)
    (hg''c : ContinuousOn g'' (Set.uIcc a b))
    (hmono : ∀ x ∈ Set.uIcc a b, 0 ≤ g'' x)
    (hpos : ∀ m ∈ S, ∀ n ∈ T, ∀ x ∈ Set.uIcc a b,
      lam ≤ g' x + (Real.log n - Real.log m)) :
    ‖∫ τ in a..b,
        (∑ m ∈ S, e m * Complex.exp (((-(Real.log m) * τ : ℝ) : ℂ) * I))
          * (starRingEnd ℂ) (∑ n ∈ T, f n * Complex.exp (((-(Real.log n) * τ : ℝ) : ℂ) * I))
          * Complex.exp (((g τ : ℝ) : ℂ) * I)‖
      ≤ (∑ m ∈ S, ‖e m‖) * (∑ n ∈ T, ‖f n‖) * (2 / lam) := by
  classical
  have hgcont : ContinuousOn g (Set.uIcc a b) := fun x hx =>
    (hg x hx).continuousAt.continuousWithinAt
  -- the integrand is a finite double sum of pure oscillations
  have hpoint : ∀ τ : ℝ,
      (∑ m ∈ S, e m * Complex.exp (((-(Real.log m) * τ : ℝ) : ℂ) * I))
        * (starRingEnd ℂ) (∑ n ∈ T, f n * Complex.exp (((-(Real.log n) * τ : ℝ) : ℂ) * I))
        * Complex.exp (((g τ : ℝ) : ℂ) * I)
      = ∑ m ∈ S, ∑ n ∈ T, (e m * (starRingEnd ℂ) (f n)) *
          Complex.exp ((((g τ + τ * (Real.log n - Real.log m)) : ℝ) : ℂ) * I) := by
    intro τ
    rw [map_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hconj : (starRingEnd ℂ) ((((-(Real.log n) * τ : ℝ)) : ℂ) * I)
        = (((Real.log n * τ : ℝ)) : ℂ) * I := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [map_mul, ← Complex.exp_conj, hconj]
    rw [show e m * Complex.exp (((-(Real.log m) * τ : ℝ) : ℂ) * I)
          * ((starRingEnd ℂ) (f n) * Complex.exp (((Real.log n * τ : ℝ) : ℂ) * I))
          * Complex.exp (((g τ : ℝ) : ℂ) * I)
        = (e m * (starRingEnd ℂ) (f n)) *
          (Complex.exp (((-(Real.log m) * τ : ℝ) : ℂ) * I)
            * Complex.exp (((Real.log n * τ : ℝ) : ℂ) * I)
            * Complex.exp (((g τ : ℝ) : ℂ) * I)) from by ring]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast; ring
  -- each pure oscillation is bounded by the first-derivative test
  have hterm : ∀ m ∈ S, ∀ n ∈ T,
      ‖∫ τ in a..b, (e m * (starRingEnd ℂ) (f n)) *
        Complex.exp ((((g τ + τ * (Real.log n - Real.log m)) : ℝ) : ℂ) * I)‖
        ≤ ‖e m‖ * ‖f n‖ * (2 / lam) := by
    intro m hm n hn
    set G : ℝ → ℝ := fun τ => g τ + τ * (Real.log n - Real.log m) with hG
    set G' : ℝ → ℝ := fun τ => g' τ + (Real.log n - Real.log m) with hG'
    have hGd : ∀ x ∈ Set.uIcc a b, HasDerivAt G (G' x) x := by
      intro x hx
      have h1 := hg x hx
      have h2 : HasDerivAt (fun τ : ℝ => τ * (Real.log n - Real.log m))
          (Real.log n - Real.log m) x := by
        simpa using (hasDerivAt_id x).mul_const (Real.log n - Real.log m)
      exact h1.add h2
    have hG'd : ∀ x ∈ Set.uIcc a b, HasDerivAt G' (g'' x) x := by
      intro x hx
      rw [hG']
      exact (hg' x hx).add_const (Real.log n - Real.log m)
    have hbase := norm_integral_cexp_ofReal_mul_I_le_mono (a := a) (b := b) (lam := lam)
      hab hlam hGd hG'd hg''c (fun x hx => hpos m hm n hn x hx) hmono
    rw [intervalIntegral.integral_const_mul, norm_mul]
    have hc : ‖e m * (starRingEnd ℂ) (f n)‖ = ‖e m‖ * ‖f n‖ := by
      rw [norm_mul, RCLike.norm_conj]
    rw [hc]
    exact mul_le_mul_of_nonneg_left hbase (by positivity)
  -- assemble
  have hcont : ∀ (m n : ℕ), IntervalIntegrable
      (fun τ : ℝ => (e m * (starRingEnd ℂ) (f n)) *
        Complex.exp ((((g τ + τ * (Real.log n - Real.log m)) : ℝ) : ℂ) * I)) volume a b := by
    intro m n
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul ?_
    refine Complex.continuous_exp.comp_continuousOn ?_
    refine ContinuousOn.mul ?_ continuousOn_const
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact hgcont.add (continuousOn_id.mul continuousOn_const)
  have hsumint : ∀ m : ℕ, IntervalIntegrable
      (fun τ : ℝ => ∑ n ∈ T, (e m * (starRingEnd ℂ) (f n)) *
        Complex.exp ((((g τ + τ * (Real.log n - Real.log m)) : ℝ) : ℂ) * I)) volume a b := by
    intro m
    have h := IntervalIntegrable.sum T (fun n (_ : n ∈ T) => hcont m n)
    have heq : (∑ n ∈ T, fun τ : ℝ => (e m * (starRingEnd ℂ) (f n)) *
        Complex.exp ((((g τ + τ * (Real.log n - Real.log m)) : ℝ) : ℂ) * I))
        = fun τ : ℝ => ∑ n ∈ T, (e m * (starRingEnd ℂ) (f n)) *
          Complex.exp ((((g τ + τ * (Real.log n - Real.log m)) : ℝ) : ℂ) * I) := by
      funext τ
      simp [Finset.sum_apply]
    rwa [heq] at h
  rw [intervalIntegral.integral_congr (fun τ _ => hpoint τ)]
  rw [intervalIntegral.integral_finsetSum (μ := volume) (a := a) (b := b) (s := S)
    (f := fun m τ => ∑ n ∈ T, (e m * (starRingEnd ℂ) (f n)) *
      Complex.exp ((((g τ + τ * (Real.log n - Real.log m)) : ℝ) : ℂ) * I))
    (fun m _ => hsumint m)]
  refine le_trans (norm_sum_le _ _) ?_
  have hstep : ∀ m ∈ S, ‖∫ τ in a..b, ∑ n ∈ T, (e m * (starRingEnd ℂ) (f n)) *
      Complex.exp ((((g τ + τ * (Real.log n - Real.log m)) : ℝ) : ℂ) * I)‖
      ≤ ‖e m‖ * ((∑ n ∈ T, ‖f n‖) * (2 / lam)) := by
    intro m hm
    rw [intervalIntegral.integral_finsetSum (μ := volume) (a := a) (b := b) (s := T)
      (f := fun n τ => (e m * (starRingEnd ℂ) (f n)) *
        Complex.exp ((((g τ + τ * (Real.log n - Real.log m)) : ℝ) : ℂ) * I))
      (fun n _ => hcont m n)]
    refine le_trans (norm_sum_le _ _) ?_
    have hb : ∀ n ∈ T, ‖∫ τ in a..b, (e m * (starRingEnd ℂ) (f n)) *
        Complex.exp ((((g τ + τ * (Real.log n - Real.log m)) : ℝ) : ℂ) * I)‖
        ≤ ‖e m‖ * (2 / lam) * ‖f n‖ := by
      intro n hn
      have := hterm m hm n hn
      linarith [this]
    refine le_trans (Finset.sum_le_sum hb) ?_
    rw [← Finset.mul_sum]
    ring_nf
    exact le_of_eq rfl
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.sum_mul]
  ring_nf
  exact le_of_eq rfl


/-- **The saddle has left the window.**  If every direct index is at most `x`, every dual index is
at least `1`, and `2π·x·K ≤ τ`, then the combined cross frequency at height `τ` is at least
`log K`.  With `x ≍ T^{1/2+θ}` and `τ ≍ T` this gives `K ≍ T^{1/2−θ}`, hence a frequency lower
bound `(1/2 − θ) log T − O(1)`: the hypothesis of `norm_integral_dirichletCross_cexp_le`. -/
theorem log_freq_lower_bound {τ x K : ℝ} {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmx : (m : ℝ) ≤ x) (hK : 0 < K)
    (hτ : 2 * Real.pi * x * K ≤ τ) :
    Real.log K ≤ Real.log (τ / (2 * Real.pi)) + (Real.log n - Real.log m) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hx1 : (1 : ℝ) ≤ x := le_trans hm1 hmx
  have hx0 : (0 : ℝ) < x := by linarith
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hprod : (0 : ℝ) < 2 * Real.pi * x * K := by positivity
  have hτ0 : (0 : ℝ) < τ := by linarith
  have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hstep : K ≤ τ / (2 * Real.pi * (m : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hmx, hK, hπ]
  have hlog : Real.log K ≤ Real.log (τ / (2 * Real.pi * (m : ℝ))) :=
    Real.log_le_log hK hstep
  have hsplit : Real.log (τ / (2 * Real.pi * (m : ℝ)))
      = Real.log (τ / (2 * Real.pi)) - Real.log (m : ℝ) := by
    rw [show τ / (2 * Real.pi * (m : ℝ)) = (τ / (2 * Real.pi)) / (m : ℝ) by ring,
      Real.log_div (by positivity) (by positivity)]
  rw [hsplit] at hlog
  linarith

end RHTower

end
