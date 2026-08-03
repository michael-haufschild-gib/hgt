import GaloisForLFunctions.RHTower.Sieve.DistancePointwise

/-!
# The triangle inequality for the multiplicative distance

For unimodular `f, g` on a set of primes `P` put

`D(f, g; P)² = ∑_{p ∈ P} (1 - Re(f(p) conj g(p)))/p`.

Since `1 - Re(u conj v) = ‖u - v‖²/2` on the unit circle, `D(f, g; P)` is exactly the Euclidean norm
of the vector `p ↦ (f(p) - g(p))/√(2p)`.  That vector is additive in the middle argument —
`(f - g) + (g - h) = f - h` — so the triangle inequality for the distance is the triangle inequality
for a norm:

**`D(f, h; P) ≤ D(f, g; P) + D(g, h; P)`.**

This is the Granville–Soundararajan triangle inequality.  It is what makes "close to a character"
a transitive notion, and hence what lets a Halász-type argument pass from one character to another.
-/

namespace RHTower.Sieve

open Finset

/-- The squared distance between two functions on a set of primes. -/
noncomputable def mulDistSqPair (f g : ℕ → ℂ) (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, (1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ)

/-- The Euclidean vector realising the distance. -/
noncomputable def distVec (f g : ℕ → ℂ) (P : Finset ℕ) : EuclideanSpace ℂ {x // x ∈ P} :=
  WithLp.toLp 2 fun p => (f p.1 - g p.1) / ((Real.sqrt (2 * (p.1 : ℝ)) : ℝ) : ℂ)

@[simp] theorem distVec_apply (f g : ℕ → ℂ) (P : Finset ℕ) (p : {x // x ∈ P}) :
    distVec f g P p = (f p.1 - g p.1) / ((Real.sqrt (2 * (p.1 : ℝ)) : ℝ) : ℂ) := rfl

/-- **The vector is additive in the middle argument.** -/
theorem distVec_add (f g h : ℕ → ℂ) (P : Finset ℕ) :
    distVec f g P + distVec g h P = distVec f h P := by
  ext p
  simp only [PiLp.add_apply, distVec_apply, ← add_div]
  ring_nf

/-- Each coordinate of the vector has the right size. -/
theorem norm_distVec_term_sq {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {p : ℕ} (hp : 0 < p) :
    ‖(u - v) / ((Real.sqrt (2 * (p : ℝ)) : ℝ) : ℂ)‖ ^ 2
      = (1 - (u * (starRingEnd ℂ) v).re) / (p : ℝ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h2p : (0 : ℝ) ≤ 2 * (p : ℝ) := by positivity
  have hsq : Real.sqrt (2 * (p : ℝ)) ^ 2 = 2 * (p : ℝ) := Real.sq_sqrt h2p
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), hsq, one_sub_re_eq_half_normSq hu hv]
  field_simp

/-- **The distance is the norm of the vector.** -/
theorem norm_distVec {f g : ℕ → ℂ} {P : Finset ℕ} (hf : ∀ p ∈ P, ‖f p‖ = 1)
    (hg : ∀ p ∈ P, ‖g p‖ = 1) (hP : ∀ p ∈ P, 0 < p) :
    ‖distVec f g P‖ = Real.sqrt (mulDistSqPair f g P) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [mulDistSqPair, ← Finset.sum_coe_sort P
    fun p => (1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [distVec_apply]
  exact norm_distVec_term_sq (hf p.1 p.2) (hg p.1 p.2) (hP p.1 p.2)

/-- **The Granville–Soundararajan triangle inequality for the multiplicative distance.** -/
theorem sqrt_mulDistSqPair_triangle {f g h : ℕ → ℂ} {P : Finset ℕ} (hf : ∀ p ∈ P, ‖f p‖ = 1)
    (hg : ∀ p ∈ P, ‖g p‖ = 1) (hh : ∀ p ∈ P, ‖h p‖ = 1) (hP : ∀ p ∈ P, 0 < p) :
    Real.sqrt (mulDistSqPair f h P)
      ≤ Real.sqrt (mulDistSqPair f g P) + Real.sqrt (mulDistSqPair g h P) := by
  rw [← norm_distVec hf hh hP, ← norm_distVec hf hg hP, ← norm_distVec hg hh hP,
    ← distVec_add f g h P]
  exact norm_add_le _ _

/-- The distance is nonnegative, being a sum of squares in disguise. -/
theorem mulDistSqPair_nonneg {f g : ℕ → ℂ} {P : Finset ℕ} (hf : ∀ p ∈ P, ‖f p‖ = 1)
    (hg : ∀ p ∈ P, ‖g p‖ = 1) (hP : ∀ p ∈ P, 0 < p) : 0 ≤ mulDistSqPair f g P := by
  refine Finset.sum_nonneg fun p hp => ?_
  have := norm_distVec_term_sq (hf p hp) (hg p hp) (hP p hp)
  rw [← this]
  positivity

end RHTower.Sieve
