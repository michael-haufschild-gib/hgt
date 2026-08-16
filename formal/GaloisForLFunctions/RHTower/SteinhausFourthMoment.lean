import GaloisForLFunctions.RHTower.SteinhausModel

/-!
# The fourth correlation of the Steinhaus characters

Complete multiplicativity turns a four-fold correlation into a two-fold one,

```text
X_p · conj(X_q) · X_r · conj(X_t)  =  X_{pr} · conj(X_{qt}) ,
```

so orthonormality gives

```text
E[ X_p conj(X_q) X_r conj(X_t) ]  =  [ p r = q t ] .
```

This is the identity behind the fourth moment of a random Dirichlet polynomial.  Over general
integer indices the resulting diagonal `pr = qt` is a divisor correlation; over primes it is exactly
two diagonals, and the four-fold sum collapses.
-/

noncomputable section

open MeasureTheory

namespace GaloisForLFunctions.RHTower

open _root_.RHTower.SteinhausModel

/-- Complete multiplicativity collapses the four-fold product to a two-fold one. -/
theorem X_four_eq {p q r t : ℕ} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (ht : t ≠ 0)
    (ω : Omega) :
    X p ω * (starRingEnd ℂ) (X q ω) * X r ω * (starRingEnd ℂ) (X t ω)
      = X (p * r) ω * (starRingEnd ℂ) (X (q * t) ω) := by
  rw [X_mul hp hr, X_mul hq ht, map_mul]
  ring

/-- **The fourth correlation of the Steinhaus characters.** -/
theorem integral_X_four {p q r t : ℕ} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (ht : t ≠ 0) :
    ∫ ω, X p ω * (starRingEnd ℂ) (X q ω) * X r ω * (starRingEnd ℂ) (X t ω) ∂steinhausMeasure
      = if p * r = q * t then 1 else 0 := by
  have hcongr : ∀ ω : Omega,
      X p ω * (starRingEnd ℂ) (X q ω) * X r ω * (starRingEnd ℂ) (X t ω)
        = X (p * r) ω * (starRingEnd ℂ) (X (q * t) ω) := X_four_eq hp hq hr ht
  rw [integral_congr_ae (Filter.Eventually.of_forall hcongr)]
  exact integral_X_mul_conj (Nat.mul_ne_zero hp hr) (Nat.mul_ne_zero hq ht)

/-- The four-fold product is integrable: it is a product of unimodular factors. -/
theorem integrable_X_four (p q r t : ℕ) :
    Integrable (fun ω => X p ω * (starRingEnd ℂ) (X q ω) * X r ω * (starRingEnd ℂ) (X t ω))
      steinhausMeasure := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · exact ((((measurable_X p).mul
      (continuous_star.measurable.comp (measurable_X q))).mul (measurable_X r)).mul
      (continuous_star.measurable.comp (measurable_X t))).aestronglyMeasurable
  · filter_upwards with ω
    rw [norm_mul, norm_mul, norm_mul, norm_X, RCLike.norm_conj, norm_X, RCLike.norm_conj,
      norm_X, norm_X, one_mul, one_mul, one_mul]

/-- The scaled four-fold product is integrable. -/
theorem integrable_smul_X_four (c : ℂ) (p q r t : ℕ) :
    Integrable (fun ω => c *
        (X p ω * (starRingEnd ℂ) (X q ω) * X r ω * (starRingEnd ℂ) (X t ω)))
      steinhausMeasure :=
  (integrable_X_four p q r t).const_mul c

/-- **The fourth moment of a Steinhaus Dirichlet polynomial.**  It is the four-fold sum over the
divisor diagonal `p r = q t`. -/
theorem integral_normSq_sq_dpoly (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ≠ 0) :
    ∫ ω, ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ 4 ∂steinhausMeasure
      = ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, ∑ t ∈ s,
          (if p * r = q * t then a p * a q * a r * a t else 0) := by
  classical
  have hconj : ∀ ω : Omega, (starRingEnd ℂ) (∑ n ∈ s, (a n : ℂ) * X n ω)
      = ∑ n ∈ s, (a n : ℂ) * (starRingEnd ℂ) (X n ω) := by
    intro ω
    simp only [map_sum, map_mul, Complex.conj_ofReal]
  have hpoint : ∀ ω : Omega, ((‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ 4 : ℝ) : ℂ)
      = ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, ∑ t ∈ s,
          ((a p * a q * a r * a t : ℝ) : ℂ)
            * (X t ω * (starRingEnd ℂ) (X r ω) * X q ω * (starRingEnd ℂ) (X p ω)) := by
    intro ω
    have h1 : ((‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ 4 : ℝ) : ℂ)
        = ((∑ n ∈ s, (a n : ℂ) * X n ω) * (starRingEnd ℂ) (∑ n ∈ s, (a n : ℂ) * X n ω))
          * ((∑ n ∈ s, (a n : ℂ) * X n ω) * (starRingEnd ℂ) (∑ n ∈ s, (a n : ℂ) * X n ω)) := by
      rw [Complex.mul_conj']
      push_cast
      ring
    rw [h1, hconj]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => ?_
    push_cast
    ring
  have hI1 : ∀ p q r : ℕ, Integrable (fun ω : Omega => ∑ t ∈ s,
      ((a p * a q * a r * a t : ℝ) : ℂ)
        * (X t ω * (starRingEnd ℂ) (X r ω) * X q ω * (starRingEnd ℂ) (X p ω)))
      steinhausMeasure :=
    fun p q r => integrable_finsetSum _ fun t _ => integrable_smul_X_four _ t r q p
  have hI2 : ∀ p q : ℕ, Integrable (fun ω : Omega => ∑ r ∈ s, ∑ t ∈ s,
      ((a p * a q * a r * a t : ℝ) : ℂ)
        * (X t ω * (starRingEnd ℂ) (X r ω) * X q ω * (starRingEnd ℂ) (X p ω)))
      steinhausMeasure :=
    fun p q => integrable_finsetSum _ fun r _ => hI1 p q r
  have hI3 : ∀ p : ℕ, Integrable (fun ω : Omega => ∑ q ∈ s, ∑ r ∈ s, ∑ t ∈ s,
      ((a p * a q * a r * a t : ℝ) : ℂ)
        * (X t ω * (starRingEnd ℂ) (X r ω) * X q ω * (starRingEnd ℂ) (X p ω)))
      steinhausMeasure :=
    fun p => integrable_finsetSum _ fun q _ => hI2 p q
  have hcast : ((∫ ω, ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ 4 ∂steinhausMeasure : ℝ) : ℂ)
      = ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, ∑ t ∈ s,
          ((if p * r = q * t then a p * a q * a r * a t else 0 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, integral_congr_ae (Filter.Eventually.of_forall hpoint),
      integral_finsetSum _ fun p _ => hI3 p]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [integral_finsetSum _ fun q _ => hI2 p q]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [integral_finsetSum _ fun r _ => hI1 p q r]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [integral_finsetSum _ fun t _ => integrable_smul_X_four _ t r q p]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [integral_const_mul, integral_X_four (hs t ht) (hs r hr) (hs q hq) (hs p hp)]
    have hc : (t * q = r * p) ↔ (p * r = q * t) := by
      rw [mul_comm p r, mul_comm q t]
      exact eq_comm
    simp only [hc]
    split_ifs <;> simp
  have hpush : ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, ∑ t ∈ s,
        ((if p * r = q * t then a p * a q * a r * a t else 0 : ℝ) : ℂ)
      = ((∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, ∑ t ∈ s,
          (if p * r = q * t then a p * a q * a r * a t else 0) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hpush] at hcast
  exact_mod_cast hcast

end GaloisForLFunctions.RHTower

end
