import GaloisForLFunctions.RHTower.Sieve.DistanceDiscTriangle

/-!
# At most one character can be close

The distance between two characters is explicit:

`D(n^{it}, n^{iu}; P)² = ∑_{p ∈ P} (1 - cos((t-u) log p))/p`,

so the triangle inequality turns closeness of a multiplicative function to two characters into
closeness of the two characters to each other:

if `D(f, n^{it}; P) ≤ δ` and `D(f, n^{iu}; P) ≤ δ` then `∑_{p ∈ P}(1 - cos((t-u) log p))/p ≤ 4δ²`.

This is the structural reason a Halász-type argument only ever has to consider one distinguished
frequency: the set of characters within `δ` of a given `f` has diameter `2δ` in the distance, and the
explicit form above converts that into a genuine constraint on `t - u`.
-/

namespace RHTower.Sieve

open Finset

/-- The pairwise distance is symmetric. -/
theorem mulDistSqPair_comm (f g : ℕ → ℂ) (P : Finset ℕ) :
    mulDistSqPair f g P = mulDistSqPair g f P := by
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : (g p * (starRingEnd ℂ) (f p)) = (starRingEnd ℂ) (f p * (starRingEnd ℂ) (g p)) := by
    simp [map_mul, mul_comm]
  rw [h, Complex.conj_re]

/-- **The distance between two characters.** -/
theorem mulDistSqPair_charFn (t u : ℝ) (P : Finset ℕ) :
    mulDistSqPair (charFn t) (charFn u) P
      = ∑ p ∈ P, (1 - Real.cos ((t - u) * Real.log (p : ℝ))) / (p : ℝ) := by
  refine Finset.sum_congr rfl fun p _ => ?_
  have hcomb : ((t * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I
      + ((-(u * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I
      = (((t - u) * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [conj_charFn, charFn, ← Complex.exp_add, hcomb, Complex.exp_ofReal_mul_I_re]

/-- **Two characters close to the same function are close to each other.** -/
theorem char_separation_of_close {f : ℕ → ℂ} {P : Finset ℕ} (hf : ∀ p ∈ P, ‖f p‖ ≤ 1)
    (hP : ∀ p ∈ P, 0 < p) {t u δ : ℝ}
    (ht : Real.sqrt (mulDistSqPair f (charFn t) P) ≤ δ)
    (hu : Real.sqrt (mulDistSqPair f (charFn u) P) ≤ δ) :
    Real.sqrt (∑ p ∈ P, (1 - Real.cos ((t - u) * Real.log (p : ℝ))) / (p : ℝ)) ≤ 2 * δ := by
  have hchar : ∀ v : ℝ, ∀ p ∈ P, ‖charFn v p‖ ≤ 1 := fun v p _ => (norm_charFn v p).le
  have htri := sqrt_mulDistSqPair_triangle_disc (f := charFn t) (g := f) (h := charFn u)
    (hchar t) hf (hchar u) hP
  rw [mulDistSqPair_charFn] at htri
  have hsym : mulDistSqPair (charFn t) f P = mulDistSqPair f (charFn t) P :=
    mulDistSqPair_comm _ _ _
  rw [hsym] at htri
  linarith

/-- **The separation in explicit form**: two `δ`-close frequencies satisfy a cosine constraint. -/
theorem sum_one_sub_cos_le_of_close {f : ℕ → ℂ} {P : Finset ℕ} (hf : ∀ p ∈ P, ‖f p‖ ≤ 1)
    (hP : ∀ p ∈ P, 0 < p) {t u δ : ℝ}
    (ht : Real.sqrt (mulDistSqPair f (charFn t) P) ≤ δ)
    (hu : Real.sqrt (mulDistSqPair f (charFn u) P) ≤ δ) :
    ∑ p ∈ P, (1 - Real.cos ((t - u) * Real.log (p : ℝ))) / (p : ℝ) ≤ 4 * δ ^ (2 : ℕ) := by
  have hsep := char_separation_of_close hf hP ht hu
  have hnonneg : 0 ≤ ∑ p ∈ P, (1 - Real.cos ((t - u) * Real.log (p : ℝ))) / (p : ℝ) := by
    refine Finset.sum_nonneg fun p hp => ?_
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hP p hp
    have hcos := Real.cos_le_one ((t - u) * Real.log (p : ℝ))
    positivity
  have hsq : (Real.sqrt (∑ p ∈ P, (1 - Real.cos ((t - u) * Real.log (p : ℝ))) / (p : ℝ))) ^ (2 : ℕ)
      = ∑ p ∈ P, (1 - Real.cos ((t - u) * Real.log (p : ℝ))) / (p : ℝ) := Real.sq_sqrt hnonneg
  have h2 : (Real.sqrt (∑ p ∈ P, (1 - Real.cos ((t - u) * Real.log (p : ℝ))) / (p : ℝ))) ^ (2 : ℕ)
      ≤ (2 * δ) ^ (2 : ℕ) := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsep 2
  rw [hsq] at h2
  nlinarith [h2]

end RHTower.Sieve
