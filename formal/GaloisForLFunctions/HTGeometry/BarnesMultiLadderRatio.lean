import GaloisForLFunctions.HTGeometry.BarnesLadderPolynomial
import GaloisForLFunctions.HTGeometry.BarnesSliceReindex
import GaloisForLFunctions.HTGeometry.BarnesLadderDecomposition
import GaloisForLFunctions.HTGeometry.BarnesFieldLadderOrderOne

/-!
# The multi-period Barnes ladder is a ratio of polynomials

Combining the three pieces the corpus already owns — the ladder decomposition, the correction series
as an explicit atom plus polynomial, and the slice as the deleted-frame lower source minus a
monomial — the defect

```text
Ψ_ω(z + ω_j) - Ψ_ω(z) + Ψ_{ω^{(j)}}(z)
```

is, off the poles, a single ratio of polynomials with the linear denominator `z + ω_j`.  The only
non-polynomial contribution is the order-`N` atom of the deleted direction.

This is the form the punctured-representative machinery consumes: a correction with a rational
representative is an element of the coordinate field, hence differentially algebraic.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The convergent coefficient sums of the ladder correction. -/
def barnesLadderCoeffSum (ω : ι → ℂ) (j : ι) (k : ℕ) : ℂ :=
  ∑' n : ι → ℕ, barnesLadderCoefficient ω j k n

/-- The polynomial part of the multi-period ladder defect. -/
def barnesLadderCorrectionPoly (ω : ι → ℂ) (j : ι) : Polynomial ℂ :=
  (∑ k ∈ Finset.range (Fintype.card ι),
      Polynomial.C ((-1) ^ (Fintype.card ι - 1) * barnesLadderCoeffSum ω j k) *
        ((Polynomial.X + Polynomial.C (ω j)) ^ k * Polynomial.X ^ (Fintype.card ι - 1 - k)))
    + Polynomial.C ((-1) ^ Fintype.card {i : ι // i ≠ j} * coneZeta (deletedFrame ω j)) *
        Polynomial.X ^ Fintype.card {i : ι // i ≠ j}

/-- The numerator of the multi-period ladder defect over the linear denominator. -/
def barnesLadderNumerator (ω : ι → ℂ) (j : ι) : Polynomial ℂ :=
  barnesLadderCorrectionPoly ω j * (Polynomial.X + Polynomial.C (ω j))
    - Polynomial.C (((-1) / ω j) ^ Fintype.card ι) * Polynomial.X ^ Fintype.card ι

omit [Nonempty ι] in
theorem barnesLadderCorrectionPoly_eval (ω : ι → ℂ) (j : ι) (z : ℂ) :
    (barnesLadderCorrectionPoly ω j).eval z
      = (∑ k ∈ Finset.range (Fintype.card ι),
          ((-1) ^ (Fintype.card ι - 1) * (z + ω j) ^ k * z ^ (Fintype.card ι - 1 - k)) *
            barnesLadderCoeffSum ω j k)
        + (-1) ^ Fintype.card {i : ι // i ≠ j} * z ^ Fintype.card {i : ι // i ≠ j} *
            coneZeta (deletedFrame ω j) := by
  rw [barnesLadderCorrectionPoly]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_finsetSum]
  exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => by ring) (by ring)

/-- **The multi-period ladder defect is a ratio of polynomials.** -/
theorem barnesSource_ladder_ratio (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (j : ι)
    [Nonempty {i : ι // i ≠ j}] {z : ℂ}
    (hpole : ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + z ≠ 0)
    (hpole' : ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + (z + ω j) ≠ 0)
    (hpoleD : ∀ g : {i : ι // i ≠ j} → ℕ, g ≠ 0 → conePeriod (deletedFrame ω j) g + z ≠ 0) :
    logDeriv (barnesConeProduct ω) (z + ω j) - logDeriv (barnesConeProduct ω) z
        + logDeriv (barnesConeProduct (deletedFrame ω j)) z
      = (barnesLadderNumerator ω j).eval z /
        (Polynomial.X + Polynomial.C (ω j)).eval z := by
  have hωj : ω j ≠ 0 := by
    intro hcon
    have hj := hω j
    rw [hcon] at hj
    simp at hj
  have hne : z + ω j ≠ 0 := by
    have hp := hpole (Pi.single j 1) (piSingle_ne_zero j)
    rw [conePeriod_piSingle] at hp
    intro hcon
    exact hp (by linear_combination hcon)
  have hlad := barnesSource_ladder_decomposition ω hω j hpole hpole'
  have hcorr := tsum_barnesLadderCorrection_eq ω hω j hpole
  have hslice := tsum_barnesAtom_slice_eq_lower ω hω j hpoleD
  have hlower := logDeriv_barnesConeProduct_eq_tsum_barnesAtom (deletedFrame ω j)
    (deletedFrame_im_pos hω j) hpoleD
  have hatom : barnesAtom ω (Pi.single j 1) z
      = ((-1) / ω j) ^ Fintype.card ι * z ^ Fintype.card ι / (z + ω j) := by
    have h1 : (-(z / ω j)) ^ Fintype.card ι
        = ((-1) / ω j) ^ Fintype.card ι * z ^ Fintype.card ι := by
      rw [← mul_pow]
      congr 1
      field_simp
    rw [barnesAtom, if_neg (piSingle_ne_zero j), conePeriod_piSingle, h1, add_comm (ω j) z]
  have hLHS : logDeriv (barnesConeProduct ω) (z + ω j) - logDeriv (barnesConeProduct ω) z
      + logDeriv (barnesConeProduct (deletedFrame ω j)) z
      = -barnesAtom ω (Pi.single j 1) z
        + (∑ k ∈ Finset.range (Fintype.card ι),
            ((-1) ^ (Fintype.card ι - 1) * (z + ω j) ^ k * z ^ (Fintype.card ι - 1 - k)) *
              barnesLadderCoeffSum ω j k)
        + (-1) ^ Fintype.card {i : ι // i ≠ j} * z ^ Fintype.card {i : ι // i ≠ j} *
            coneZeta (deletedFrame ω j) := by
    simp only [barnesLadderCoeffSum]
    rw [hlad, hcorr, hslice, ← hlower]
    ring
  rw [hLHS, hatom, barnesLadderNumerator]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  rw [barnesLadderCorrectionPoly_eval]
  field_simp
  ring

end

end GaloisForLFunctions
