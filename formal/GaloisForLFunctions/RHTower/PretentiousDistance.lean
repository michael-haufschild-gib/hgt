import GaloisForLFunctions.RHTower.Sieve.DistanceDiscTriangle
import GaloisForLFunctions.RHTower.Sieve.MertensSecondSharp

/-!
# The real reflection of the pretentious distance

A real prime sequence is equidistant from an archimedean character and from its conjugate, so the
Granville–Soundararajan triangle inequality costs exactly the factor four:

```text
D_x(n^{-iα}, n^{iα})² ≤ 4 D_x(g, n^{iα})²      for real `g`.
```

The distance, its triangle inequality and the character are the corpus objects `mulDistSqPair`,
`sqrt_mulDistSqPair_triangle_disc` and `charFn`; only the reflection law is new.
-/

open Filter Topology Finset

namespace RHTower

open Sieve

noncomputable section

/-- The squared pretentious distance over the prime window `{p ≤ x}`. -/
def pretentiousDistSq (f g : ℕ → ℂ) (x : ℝ) : ℝ :=
  mulDistSqPair f g (Nat.primesLE ⌊x⌋₊)

/-- The archimedean character `n ↦ n^{iα}`. -/
def primeChar (α : ℝ) : ℕ → ℂ := charFn α

theorem primeWindow_pos (x : ℝ) : ∀ p ∈ Nat.primesLE ⌊x⌋₊, 0 < p :=
  fun _ hp => (Nat.prime_of_mem_primesLE hp).pos

@[simp]
theorem norm_primeChar (α : ℝ) (n : ℕ) : ‖primeChar α n‖ = 1 := norm_charFn α n

theorem norm_primeChar_le_one (α : ℝ) (n : ℕ) : ‖primeChar α n‖ ≤ 1 := (norm_charFn α n).le

theorem norm_ofReal_le_one {r : ℕ → ℝ} (hr : ∀ n, |r n| ≤ 1) (n : ℕ) : ‖((r n : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hr n

theorem pretentiousDistSq_nonneg {f g : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (x : ℝ) : 0 ≤ pretentiousDistSq f g x :=
  mulDistSqPair_nonneg_disc (fun p _ => hf p) (fun p _ => hg p) (primeWindow_pos x)

/-- **The pretentious triangle inequality**, in the window form. -/
theorem sqrt_pretentiousDistSq_triangle {f g h : ℕ → ℂ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (hh : ∀ n, ‖h n‖ ≤ 1) (x : ℝ) :
    Real.sqrt (pretentiousDistSq f g x)
      ≤ Real.sqrt (pretentiousDistSq f h x) + Real.sqrt (pretentiousDistSq h g x) :=
  sqrt_mulDistSqPair_triangle_disc (fun p _ => hf p) (fun p _ => hh p) (fun p _ => hg p)
    (primeWindow_pos x)

/-- The squared distance between the two conjugate characters is the cosine defect at the doubled
frequency. -/
theorem pretentiousDistSq_primeChar (α x : ℝ) :
    pretentiousDistSq (primeChar (-α)) (primeChar α) x
      = ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 - Real.cos (2 * α * Real.log p)) / p := by
  rw [pretentiousDistSq, mulDistSqPair]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 2
  rw [primeChar, primeChar, charFn, conj_charFn]
  have harg : ((-α * Real.log p : ℝ) : ℂ) * Complex.I
      + ((-(α * Real.log p) : ℝ) : ℂ) * Complex.I
      = ((-(2 * α * Real.log p) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [← Complex.exp_add, harg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- **(Z9) The real reflection identity.**  A real prime sequence is equidistant from a character
and from its conjugate. -/
theorem pretentiousDistSq_real_reflect {r : ℕ → ℝ} (α x : ℝ) :
    pretentiousDistSq (primeChar (-α)) (fun n => (r n : ℂ)) x
      = pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x := by
  rw [pretentiousDistSq, pretentiousDistSq, mulDistSqPair, mulDistSqPair]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 2
  rw [primeChar, primeChar, charFn, conj_charFn, Complex.conj_ofReal]
  have hleft : (Complex.exp (((-α * Real.log p : ℝ) : ℂ) * Complex.I) * (r p : ℂ)).re
      = r p * Real.cos (α * Real.log p) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    have hcos : Real.cos (-α * Real.log p) = Real.cos (α * Real.log p) := by
      rw [show -α * Real.log p = -(α * Real.log p) by ring, Real.cos_neg]
    rw [hcos]
    ring
  have hright : ((r p : ℂ) * Complex.exp (((-(α * Real.log p) : ℝ) : ℂ) * Complex.I)).re
      = r p * Real.cos (α * Real.log p) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    rw [Real.cos_neg]
    ring
  rw [hleft, hright]

/-- **(Z10) The reflection costs exactly a factor four.** -/
theorem pretentiousDistSq_primeChar_le_four_mul {r : ℕ → ℝ} (hr : ∀ n, |r n| ≤ 1) (α x : ℝ) :
    pretentiousDistSq (primeChar (-α)) (primeChar α) x
      ≤ 4 * pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x := by
  have hreal : ∀ n, ‖((r n : ℂ))‖ ≤ 1 := norm_ofReal_le_one hr
  have htri := sqrt_pretentiousDistSq_triangle (f := primeChar (-α)) (g := primeChar α)
    (h := fun n => (r n : ℂ)) (norm_primeChar_le_one (-α)) (norm_primeChar_le_one α) hreal x
  rw [pretentiousDistSq_real_reflect (r := r)] at htri
  have hnn : 0 ≤ pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x :=
    pretentiousDistSq_nonneg hreal (norm_primeChar_le_one α) x
  have hlhs : 0 ≤ pretentiousDistSq (primeChar (-α)) (primeChar α) x :=
    pretentiousDistSq_nonneg (norm_primeChar_le_one (-α)) (norm_primeChar_le_one α) x
  have hsq := mul_self_le_mul_self (Real.sqrt_nonneg _) htri
  rw [Real.mul_self_sqrt hlhs] at hsq
  have hval : (Real.sqrt (pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x)
      + Real.sqrt (pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x))
      * (Real.sqrt (pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x)
        + Real.sqrt (pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x))
      = 4 * pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x := by
    have hs := Real.mul_self_sqrt hnn
    nlinarith [hs]
  rw [hval] at hsq
  exact hsq

end

end RHTower
