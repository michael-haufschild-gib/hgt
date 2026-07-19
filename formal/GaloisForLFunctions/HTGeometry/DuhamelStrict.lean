import GaloisForLFunctions.HTGeometry.DiscreteGronwall

/-!
# The Duhamel identity has a strictly partial inner sum

`monicOrthoC_duhamel` writes the inner sums over `j ≤ n`.  The two `j = n` contributions are

`Qₙ(z) · Qₙ(w)Rₙ(z)/hₙ − Rₙ(z) · Qₙ(w)Qₙ(z)/hₙ`,

which cancel identically.  So the identity holds with the sums over `j < n`, and the resulting
estimate is a genuine recursion in `n` rather than one with `K_w(n)` on both sides.

That is what makes `discrete_gronwall` applicable without an absorption step, and hence what removes
the finite radius.
-/

open scoped BigOperators

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The Duhamel identity with a strictly partial inner sum.** -/
theorem monicOrthoC_duhamel_lt (h : PositiveMomentForm s) (n : ℕ) (z w : ℂ) :
    monicOrthoC s n w
      = monicOrthoC s n z
        - (w - z) * ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
          (monicOrthoC s n z *
              (∑ j ∈ Finset.range n, monicOrthoC s j w * secondKindC s j z /
                ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
            - secondKindC s n z *
              (∑ j ∈ Finset.range n, monicOrthoC s j w * monicOrthoC s j z /
                ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))) := by
  have hfull := monicOrthoC_duhamel h n z w
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at hfull
  rw [hfull]
  ring

/-- **The second-kind Duhamel identity with a strictly partial inner sum.**  The `j = n` terms are
`Qₙ(z)·Rₙ(w)Rₙ(z)/hₙ` and `Rₙ(z)·Qₙ(z)Rₙ(w)/hₙ`, which cancel exactly as in the first-kind case. -/
theorem secondKindC_duhamel_lt (h : PositiveMomentForm s) (n : ℕ) (z w : ℂ) :
    secondKindC s n w
      = secondKindC s n z
        - (w - z) * ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) *
          (monicOrthoC s n z *
              (∑ j ∈ Finset.range n, secondKindC s j w * secondKindC s j z /
                ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))
            - secondKindC s n z *
              (∑ j ∈ Finset.range n, monicOrthoC s j z * secondKindC s j w /
                ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ))) := by
  have hfull := secondKindC_duhamel h n z w
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at hfull
  rw [hfull]
  ring

end HTGeometry
