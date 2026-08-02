import Mathlib

/-!
# Pointed Cartan conservation for seminormed descent

For a vector carrying one exponential flow character, every seminorm sees
the exact real Cartan slope.  The reflected two-sided condition growth is
`exp (t * |Re z|)`.  An invariant seminorm therefore has only two options:
the Cartan slope is zero, or the vector lies in its radical.

This is the primal counterpart of the invariant-gauge dichotomy for
eigenfunctionals.  It does not assume a topology, completeness, a divisor,
or the Riemann hypothesis.
-/

open Complex Real Filter Topology

namespace RHTower

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- The maximum of reciprocal real exponential characters is governed by
the absolute Cartan slope. -/
theorem max_exp_reflected_eq_exp_abs (t μ : ℝ) (ht : 0 ≤ t) :
    max (Real.exp (t * μ)) (Real.exp (-t * μ)) =
      Real.exp (t * |μ|) := by
  rcases le_total 0 μ with hμ | hμ
  · rw [abs_of_nonneg hμ, max_eq_left]
    rw [Real.exp_le_exp]
    nlinarith
  · rw [abs_of_nonpos hμ]
    have hle : Real.exp (t * μ) ≤ Real.exp (-t * μ) := by
      rw [Real.exp_le_exp]
      nlinarith
    rw [max_eq_right hle]
    congr 1
    ring

/-- A seminorm reads the real part of an exponential eigencharacter
exactly. -/
theorem seminorm_exponential_eigenvector
    (p : Seminorm ℂ E) (V : ℝ → E →ₗ[ℂ] E) (x : E) (z : ℂ)
    (hchar : ∀ t : ℝ, V t x = Complex.exp ((t : ℂ) * z) • x)
    (t : ℝ) :
    p (V t x) = Real.exp (t * z.re) * p x := by
  rw [hchar]
  calc
    p (Complex.exp ((t : ℂ) * z) • x) =
        ‖Complex.exp ((t : ℂ) * z)‖ * p x :=
      p.smul' _ _
    _ = Real.exp (t * z.re) * p x := by
      rw [Complex.norm_exp]
      congr 2
      simp

/-- The exact reflected conditioning law: every nonzero seminormed copy of
the character grows in one of the two time directions with exponent
`|Re z|`. -/
theorem seminorm_reflected_condition_exact
    (p : Seminorm ℂ E) (V : ℝ → E →ₗ[ℂ] E) (x : E) (z : ℂ)
    (hchar : ∀ t : ℝ, V t x = Complex.exp ((t : ℂ) * z) • x)
    (t : ℝ) (ht : 0 ≤ t) :
    max (p (V t x)) (p (V (-t) x)) =
      Real.exp (t * |z.re|) * p x := by
  rw [seminorm_exponential_eigenvector p V x z hchar t,
    seminorm_exponential_eigenvector p V x z hchar (-t)]
  have hneg : (-t) * z.re = -(t * z.re) := by ring
  rw [hneg]
  calc
    max (Real.exp (t * z.re) * p x)
        (Real.exp (-(t * z.re)) * p x) =
      max (Real.exp (t * z.re)) (Real.exp (-(t * z.re))) * p x :=
        (max_mul_of_nonneg _ _ (apply_nonneg p x)).symm
    _ = Real.exp (t * |z.re|) * p x := by
      have hm := max_exp_reflected_eq_exp_abs t z.re ht
      rw [show -(t * z.re) = (-t) * z.re by ring, hm]

/-- **Primal Cartan alternative.**  An invariant seminorm either kills an
exponential eigenvector or its real Cartan slope is zero. -/
theorem invariantSeminorm_eigenvector_radical_or_zeroCartan
    (p : Seminorm ℂ E) (V : ℝ → E →ₗ[ℂ] E) (x : E) (z : ℂ)
    (hchar : ∀ t : ℝ, V t x = Complex.exp ((t : ℂ) * z) • x)
    (hinv : ∀ t : ℝ, p (V t x) = p x) :
    p x = 0 ∨ z.re = 0 := by
  by_cases hp : p x = 0
  · exact Or.inl hp
  · right
    have hgrowth := seminorm_exponential_eigenvector p V x z hchar 1
    rw [one_mul, hinv 1] at hgrowth
    have hcancel : Real.exp z.re = 1 := by
      apply mul_right_cancel₀ hp
      simpa using hgrowth.symm
    exact (Real.exp_eq_one_iff z.re).mp hcancel

/-- A nonzero-Cartan eigenvector belongs to the radical of every invariant
seminorm. -/
theorem invariantSeminorm_eigenvector_mem_radical_of_nonzeroCartan
    (p : Seminorm ℂ E) (V : ℝ → E →ₗ[ℂ] E) (x : E) (z : ℂ)
    (hchar : ∀ t : ℝ, V t x = Complex.exp ((t : ℂ) * z) • x)
    (hinv : ∀ t : ℝ, p (V t x) = p x) (hz : z.re ≠ 0) :
    p x = 0 := by
  exact (invariantSeminorm_eigenvector_radical_or_zeroCartan
    p V x z hchar hinv).resolve_right hz

/-- Rescaled source transport along the dual Cartan direction.  The time
`n * Re z` makes its invariant capacity decay quadratically in the slope,
while a dual character of exponent `z` has constant output. -/
def dualCartanGraphNullSequence
    (V : ℝ → E →ₗ[ℂ] E) (x : E) (z : ℂ) (n : ℕ) : E :=
  Complex.exp
      (-((((n : ℝ) * z.re : ℝ) : ℂ) * z)) •
    V ((n : ℝ) * z.re) x

/-- Every dual exponential character is constant on its Cartan graph-null
sequence. -/
theorem dualCartanGraphNullSequence_evaluation
    (L : E →ₗ[ℂ] ℂ) (V : ℝ → E →ₗ[ℂ] E) (x : E) (z : ℂ)
    (hchar : ∀ (t : ℝ) (u : E),
      L (V t u) = Complex.exp ((t : ℂ) * z) * L u)
    (n : ℕ) :
    L (dualCartanGraphNullSequence V x z n) = L x := by
  rw [dualCartanGraphNullSequence, map_smul, hchar]
  change Complex.exp (-((((n : ℝ) * z.re : ℝ) : ℂ) * z)) *
      (Complex.exp (((((n : ℝ) * z.re : ℝ) : ℂ)) * z) * L x) = L x
  rw [← mul_assoc, ← Complex.exp_add]
  have hzero :
      -((((n : ℝ) * z.re : ℝ) : ℂ) * z) +
          ((((n : ℝ) * z.re : ℝ) : ℂ) * z) = 0 := by ring
  rw [hzero, Complex.exp_zero, one_mul]

/-- Exact invariant-capacity decay of the Cartan graph-null sequence. -/
theorem seminorm_dualCartanGraphNullSequence
    (p : Seminorm ℂ E) (V : ℝ → E →ₗ[ℂ] E) (x : E) (z : ℂ)
    (hinv : ∀ (t : ℝ) (u : E), p (V t u) = p u)
    (n : ℕ) :
    p (dualCartanGraphNullSequence V x z n) =
      Real.exp (-((n : ℝ) * z.re ^ 2)) * p x := by
  rw [dualCartanGraphNullSequence]
  calc
    p (Complex.exp (-((((n : ℝ) * z.re : ℝ) : ℂ) * z)) •
        V ((n : ℝ) * z.re) x) =
        ‖Complex.exp (-((((n : ℝ) * z.re : ℝ) : ℂ) * z))‖ *
          p (V ((n : ℝ) * z.re) x) := p.smul' _ _
    _ = Real.exp (-((n : ℝ) * z.re ^ 2)) * p x := by
      rw [hinv, Complex.norm_exp]
      congr 2
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      ring

/-- A nonzero dual Cartan slope produces an explicit source sequence whose
invariant capacity tends to zero while its dual-character output stays
fixed.  This is the universal mechanism behind off-axis graph
verticalization. -/
theorem seminorm_dualCartanGraphNullSequence_tendsto_zero
    (p : Seminorm ℂ E) (V : ℝ → E →ₗ[ℂ] E) (x : E) (z : ℂ)
    (hinv : ∀ (t : ℝ) (u : E), p (V t u) = p u)
    (hz : z.re ≠ 0) :
    Filter.Tendsto (fun n => p (dualCartanGraphNullSequence V x z n))
      Filter.atTop (nhds 0) := by
  have hsq : 0 < z.re ^ 2 := sq_pos_of_ne_zero hz
  have htop :
      Filter.Tendsto (fun n : ℕ => (n : ℝ) * z.re ^ 2)
        Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hsq
  have hdecay :
      Filter.Tendsto
        (fun n : ℕ => Real.exp (-((n : ℝ) * z.re ^ 2)))
        Filter.atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp htop)
  have hmul := hdecay.const_mul (p x)
  simpa only [seminorm_dualCartanGraphNullSequence p V x z hinv,
    mul_zero, zero_mul, mul_comm] using hmul

end

end RHTower
