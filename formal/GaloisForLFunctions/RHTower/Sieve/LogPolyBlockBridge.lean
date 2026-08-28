import GaloisForLFunctions.RHTower.Sieve.LogPolyDyadicSplit
import GaloisForLFunctions.RHTower.Sieve.HuxleyDirichletLargeValues

/-!
# The dyadic blocks of an initial segment are Huxley blocks

`LogPolyDyadicSplit` writes a `logPoly` over `[1, M]` as the sum of its dyadic blocks; the corpus's
large-values machinery (`HuxleyDirichletLargeValues`, `HalaszMontgomeryDyadic`) is stated for
`blockPoly N c σ t`, the Dirichlet block over `[N, 2N)` with phase `exp(−it log n)`.

The two differ only by a normalisation of the frequency: `logPoly` uses `exp(2πi w log n)`, so the
identification is `t = −2πw`, `σ = 0`, `N = 2^j`, with the coefficients extended by zero off the
block.  With this identity every estimate proved for `blockPoly` applies to the dyadic pieces of a
Möbius-cofactor polynomial, and `inner_dyadicDirRow_blockCoeff` turns them into Gram rows.

* `restrictCoeff`, `logPoly_eq_blockPoly_of_subset` — the general bridge;
* `dyadicSegmentBlock_subset_Ico`;
* `logPoly_dyadicSegmentBlock_eq_blockPoly`;
* `logPoly_dyadicSegmentBlock_eq_inner` — the Gram-row form.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

noncomputable section

theorem dyadicSegmentBlock_subset_Ico (M j : ℕ) :
    dyadicSegmentBlock M j ⊆ Finset.Ico (2 ^ j) (2 * 2 ^ j) := by
  intro n hn
  obtain ⟨h1, h2⟩ := mem_dyadicSegmentBlock hn
  refine Finset.mem_Ico.mpr ⟨h1, ?_⟩
  calc n < 2 ^ (j + 1) := h2
    _ = 2 * 2 ^ j := by ring

/-- The coefficients of a finite set, extended by zero. -/
def restrictCoeff (a : ℕ → ℂ) (s : Finset ℕ) : ℕ → ℂ :=
  fun n => if n ∈ s then a n else 0

/-- **A `logPoly` supported in a dyadic range is a Huxley `blockPoly`.**  The only content is the
frequency normalisation `t = −2πw` at `σ = 0`. -/
theorem logPoly_eq_blockPoly_of_subset {N : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Finset.Ico N (2 * N)) (a : ℕ → ℂ) (w : ℝ) :
    logPoly a s w = blockPoly N (restrictCoeff a s) 0 (-(2 * Real.pi * w)) := by
  classical
  have hzero : ∀ n ∈ Finset.Ico N (2 * N), n ∉ s →
      restrictCoeff a s n * (((n : ℝ) ^ (-(0 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (((-(-(2 * Real.pi * w) * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I) = 0 := by
    intro n _ hn
    simp only [restrictCoeff, if_neg hn, zero_mul]
  rw [blockPoly, ← Finset.sum_subset hs hzero, logPoly]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hexp : (2 * Real.pi * (w * Real.log (n : ℝ)))
      = -(-(2 * Real.pi * w) * Real.log (n : ℝ)) := by ring
  simp only [restrictCoeff, if_pos hn, neg_zero, Real.rpow_zero, Complex.ofReal_one,
    mul_one, hexp]

/-- The coefficients of a dyadic block, extended by zero. -/
def dyadicSegmentCoeff (a : ℕ → ℂ) (M j : ℕ) : ℕ → ℂ :=
  restrictCoeff a (dyadicSegmentBlock M j)

/-- **A dyadic block of an initial-segment `logPoly` is a Huxley `blockPoly`.** -/
theorem logPoly_dyadicSegmentBlock_eq_blockPoly (a : ℕ → ℂ) (M j : ℕ) (w : ℝ) :
    logPoly a (dyadicSegmentBlock M j) w
      = blockPoly (2 ^ j) (dyadicSegmentCoeff a M j) 0 (-(2 * Real.pi * w)) :=
  logPoly_eq_blockPoly_of_subset (dyadicSegmentBlock_subset_Ico M j) a w

/-- **The Gram-row form.**  Every dyadic piece of an initial-segment Dirichlet polynomial is an
inner product against a dyadic Dirichlet row, which is what the Halász–Montgomery and Huxley
estimates bound over one-spaced frequency sets. -/
theorem logPoly_dyadicSegmentBlock_eq_inner (a : ℕ → ℂ) (M j : ℕ) (w : ℝ) :
    logPoly a (dyadicSegmentBlock M j) w
      = ⟪dyadicDirRow (2 ^ j) (-(2 * Real.pi * w)),
          blockCoeff (2 ^ j) (dyadicSegmentCoeff a M j) 0⟫_ℂ := by
  rw [inner_dyadicDirRow_blockCoeff, logPoly_dyadicSegmentBlock_eq_blockPoly]

end

end RHTower.Sieve
