import GaloisForLFunctions.HTGeometry.EntryUniformLimit
import GaloisForLFunctions.HTGeometry.NevanlinnaRealMatrix

/-!
# Uniform convergence of the truncated entries on the real line

The truncated real entries are the complex partial sums evaluated along `Complex.ofReal`, and the
limiting real entries are the complex sums there, so the uniform estimate on a ball transfers to a
uniform estimate on a real interval.  The linear factor `h₀·x` is bounded there, which is all that is
needed to carry the bound across.
-/

open scoped BigOperators
open Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- A finite measure vanishing on every compact subset of an open set vanishes on it. -/
theorem measure_open_eq_zero_of_compacts (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsFiniteMeasure μ] {U : Set ℝ} (hU : IsOpen U)
    (hK : ∀ K : Set ℝ, IsCompact K → K ⊆ U → μ K = 0) : μ U = 0 := by
  rw [hU.measure_eq_iSup_isCompact μ]
  refine le_antisymm ?_ zero_le
  exact iSup_le fun K => iSup_le fun hKU => iSup_le fun hKc => le_of_eq (hK K hKc hKU)

/-- The complex embedding of a real bilinear partial sum. -/
theorem ofReal_bilinear_finsetSum (s : ℕ → ℝ) (f g : ℕ → ℝ) (N : ℕ) :
    ((∑ k ∈ Finset.range N,
        f k * g k / momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
      = ∑ k ∈ Finset.range N, ((f k : ℝ) : ℂ) * ((g k : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
  push_cast
  rfl

/-- The truncated `B` entry is the complex partial sum along the real embedding. -/
theorem nevBreal_ofReal_partial (s : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    ((nevBreal s n x : ℝ) : ℂ)
      = -1 + ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * (x : ℂ) *
          bilinearPartialSum s (fun k => secondKindC s k 0)
            (fun z k => monicOrthoC s k z) (n + 1) ((x : ℝ) : ℂ) := by
  rw [bilinearPartialSum_secondKind_comm, nevBreal]
  push_cast [ofReal_bilinear_finsetSum]
  have hterm : ∀ k : ℕ,
      ((Polynomial.eval x (monicOrtho s k) : ℝ) : ℂ) *
          ((Polynomial.eval 0 (secondKind s k) : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
        = monicOrthoC s k ((x : ℝ) : ℂ) * secondKindC s k 0 /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
    intro k
    rw [monicOrthoC_ofReal, secondKindC_at_zero]
  rw [Finset.sum_congr rfl fun k _ => hterm k]

/-- The truncated `D` entry is the complex partial sum along the real embedding. -/
theorem nevDreal_ofReal_partial (s : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    ((nevDreal s n x : ℝ) : ℂ)
      = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * (x : ℂ) *
          bilinearPartialSum s (fun k => monicOrthoC s k 0)
            (fun z k => monicOrthoC s k z) (n + 1) ((x : ℝ) : ℂ) := by
  rw [bilinearPartialSum, nevDreal]
  push_cast [ofReal_bilinear_finsetSum]
  have hterm : ∀ k : ℕ,
      ((Polynomial.eval 0 (monicOrtho s k) : ℝ) : ℂ) *
          ((Polynomial.eval x (monicOrtho s k) : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)
        = monicOrthoC s k 0 * monicOrthoC s k ((x : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
    intro k
    rw [monicOrthoC_ofReal, monicOrthoC_at_zero]
  rw [Finset.sum_congr rfl fun k _ => hterm k]

/-- The limiting `B` entry in the order the bilinear machinery produces. -/
theorem nevBinf_comm_tsum (s : ℕ → ℝ) (z : ℂ) :
    nevBinf s z
      = -1 + ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
          ∑' k, secondKindC s k 0 * monicOrthoC s k z /
            ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
  rw [nevBinf]
  exact congrArg _ (congrArg _ (tsum_congr fun k => by ring))

theorem nevDinf_tsum (s : ℕ → ℝ) (z : ℂ) :
    nevDinf s z
      = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
          ∑' k, monicOrthoC s k 0 * monicOrthoC s k z /
            ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := rfl

end HTGeometry
