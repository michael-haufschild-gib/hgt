import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Finite Fourier truncation on the circle

Splitting an `L²(ℝ/ℤ)` vector at a finite set of frequencies,

`w = w_S + (w - w_S)`,   `w_S = ∑_{j ∈ S} ŵ(j) e_j`,

is the device that turns a coefficient estimate into an operator estimate without any convolution
theorem: the truncated part is a *finite* linear combination of exponential monomials, so the
Fourier coefficients of `c · w_S` are the finite sum `∑_{j ∈ S} ĉ(l - j) ŵ(j)` for any bounded
multiplier `c`, while the discarded part is measured by its coefficient tail through Parseval.

The three basic facts — coefficients as inner products, Parseval, and the coefficients of a
truncation — are stated here once, in their `AddCircle 1` form, for reuse.
-/

open MeasureTheory Filter Topology

namespace GaloisForLFunctions

noncomputable section

/-! ## Coefficients as inner products -/

/-- The `n`-th Fourier coefficient is the pairing against the `n`-th exponential monomial. -/
theorem inner_fourierLp_eq_fourierCoeff (n : ℤ)
    (v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    inner ℂ (fourierLp 2 n) v = fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) n := by
  rw [← fourierBasis_repr]
  have h := (fourierBasis (T := (1 : ℝ))).repr_apply_apply v n
  rw [h, coe_fourierBasis]

theorem norm_fourierLp_eq_one (n : ℤ) :
    ‖(fourierLp (T := (1 : ℝ)) 2 n : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))‖ = 1 := by
  rw [← coe_fourierBasis]
  exact (fourierBasis (T := (1 : ℝ))).orthonormal.1 n

/-- The exponential monomials are orthonormal. -/
theorem inner_fourierLp_fourierLp (l j : ℤ) :
    (inner ℂ (fourierLp (T := (1 : ℝ)) 2 l) (fourierLp (T := (1 : ℝ)) 2 j) : ℂ)
      = if l = j then 1 else 0 := by
  rw [← coe_fourierBasis]
  rcases eq_or_ne l j with h | h
  · subst h
    rw [if_pos rfl]
    have := (fourierBasis (T := (1 : ℝ))).orthonormal.1 l
    rw [inner_self_eq_norm_sq_to_K, this]
    norm_num
  · rw [if_neg h]
    exact (fourierBasis (T := (1 : ℝ))).orthonormal.2 h

/-! ## Parseval -/

/-- **Parseval** on the circle, in the form used throughout: the squared `L²` norm is the total
squared coefficient mass. -/
theorem norm_sq_eq_tsum_fourierCoeff (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ‖u‖ ^ (2 : ℝ) = ∑' j : ℤ, ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ) := by
  have hiso : ‖(fourierBasis (T := (1 : ℝ))).repr u‖ = ‖u‖ :=
    (fourierBasis (T := (1 : ℝ))).repr.norm_map u
  have hlp := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℤ => ℂ) (by norm_num)
    ((fourierBasis (T := (1 : ℝ))).repr u)
  simp only [ENNReal.toReal_ofNat] at hlp
  rw [← hiso, hlp]
  exact tsum_congr fun j => by rw [fourierBasis_repr]

/-! ## The truncation -/

/-- The finite Fourier truncation of an `L²` vector to the frequencies in `S`. -/
def fourierTruncate (S : Finset ℤ) (w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  ∑ j ∈ S, fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j • fourierLp (T := (1 : ℝ)) 2 j

/-- **The coefficients of a truncation.** -/
theorem fourierCoeff_fourierTruncate (S : Finset ℤ)
    (w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (l : ℤ) :
    fourierCoeff ((fourierTruncate S w : AddCircle (1 : ℝ) → ℂ)) l
      = if l ∈ S then fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l else 0 := by
  rw [← inner_fourierLp_eq_fourierCoeff, fourierTruncate, inner_sum]
  have hterm : ∀ j ∈ S,
      (inner ℂ (fourierLp (T := (1 : ℝ)) 2 l)
        (fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j • fourierLp (T := (1 : ℝ)) 2 j) : ℂ)
        = if l = j then fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l else 0 := by
    intro j _
    rw [inner_smul_right, inner_fourierLp_fourierLp]
    rcases eq_or_ne l j with h | h
    · subst h
      rw [if_pos rfl, if_pos rfl, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  by_cases hl : l ∈ S
  · rw [if_pos hl, Finset.sum_ite_eq S l
      (fun _ => fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l), if_pos hl]
  · rw [if_neg hl, Finset.sum_ite_eq S l
      (fun _ => fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l), if_neg hl]

/-- The coefficients of the discarded part. -/
theorem fourierCoeff_sub_fourierTruncate (S : Finset ℤ)
    (w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (l : ℤ) :
    fourierCoeff (((w - fourierTruncate S w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))) :
        AddCircle (1 : ℝ) → ℂ) l
      = if l ∈ S then 0 else fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l := by
  rw [← inner_fourierLp_eq_fourierCoeff, inner_sub_right, inner_fourierLp_eq_fourierCoeff,
    inner_fourierLp_eq_fourierCoeff, fourierCoeff_fourierTruncate]
  by_cases hl : l ∈ S
  · rw [if_pos hl, if_pos hl, sub_self]
  · rw [if_neg hl, if_neg hl, sub_zero]

/-- **The truncation error is the coefficient tail.** -/
theorem norm_sub_fourierTruncate_sq (S : Finset ℤ)
    (w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    ‖w - fourierTruncate S w‖ ^ (2 : ℝ)
      = ∑' j : ℤ, (if j ∈ S then 0
          else ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2 : ℝ)) := by
  rw [norm_sq_eq_tsum_fourierCoeff]
  refine tsum_congr fun j => ?_
  rw [fourierCoeff_sub_fourierTruncate]
  by_cases hj : j ∈ S
  · rw [if_pos hj, if_pos hj, norm_zero]
    exact Real.zero_rpow (by norm_num)
  · rw [if_neg hj, if_neg hj]

end

end GaloisForLFunctions
