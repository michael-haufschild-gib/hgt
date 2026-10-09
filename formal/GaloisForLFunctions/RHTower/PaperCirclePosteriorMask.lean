import GaloisForLFunctions.RHTower.PaperCirclePosteriorFringe
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Capture.Mask

/-! # Band-limited cell tests under actual native posteriors

The source constructs bounded spectral masks for the two children of every cell.
The native posterior's support and paid fringe estimates turn its pointwise
approximation into expectation, probability and Fourier-test error bounds.
-/

open scoped BigOperators NNReal Classical
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

def paperCircleHistoryCellMask (l r j n : ℕ) (i : Fin (2^l)) (b : Bool) :
    Grid (l+(reach j+r)+10) → ℝ :=
  Classical.choose (Capture.make_mask (M:=l+(reach j+r)+10)
    (paperCircleObservationCell l i) i.isLt
    (by change l < l+(reach j+r)+10; omega) b j n)

private theorem mask_spec (l r j n : ℕ) (i : Fin (2^l)) (b : Bool) :
    Capture.limitR (paperCircleHistoryCellMask l r j n i b)
      (Capture.band (paperCircleObservationCell l i) j n) ∧
    (∀ x, 0 ≤ paperCircleHistoryCellMask l r j n i b x ∧
      paperCircleHistoryCellMask l r j n i b x ≤ 1) ∧
    (∀ x, x ∈ (paperCircleObservationCell l i).block (l+(reach j+r)+10) →
      ¬ (lanes (paperCircleObservationCell l i) j (l+(reach j+r)+10) ∧
        flanked (paperCircleObservationCell l i) j x) →
      |(if x ∈ ((paperCircleObservationCell l i).child b).block (l+(reach j+r)+10)
        then (1:ℝ) else 0) - paperCircleHistoryCellMask l r j n i b x| ≤ Period.side n) ∧
    expU (fun x => if x ∈ (paperCircleObservationCell l i).block (l+(reach j+r)+10)
      then 0 else paperCircleHistoryCellMask l r j n i b x) ≤
        (paperCircleObservationCell l i).len * Period.side n :=
  Classical.choose_spec (Capture.make_mask (M:=l+(reach j+r)+10)
    (paperCircleObservationCell l i) i.isLt
    (by change l < l+(reach j+r)+10; omega) b j n)

theorem paperCircleHistoryCellMask_bandlimited (l r j n : ℕ) (i : Fin (2^l)) (b : Bool) :
    Capture.limitR (paperCircleHistoryCellMask l r j n i b)
      (Capture.band (paperCircleObservationCell l i) j n) :=
  (mask_spec l r j n i b).1

theorem paperCircleHistoryCellMask_bounds (l r j n : ℕ) (i : Fin (2^l)) (b : Bool)
    (x : Grid (l+(reach j+r)+10)) :
    0 ≤ paperCircleHistoryCellMask l r j n i b x ∧
      paperCircleHistoryCellMask l r j n i b x ≤ 1 :=
  (mask_spec l r j n i b).2.1 x

theorem paperCircleHistoryCellMask_leakage (l r j n : ℕ) (i : Fin (2^l)) (b : Bool) :
    expU (fun x => if x ∈ (paperCircleObservationCell l i).block (l+(reach j+r)+10)
      then 0 else paperCircleHistoryCellMask l r j n i b x) ≤
        (paperCircleObservationCell l i).len * Period.side n :=
  (mask_spec l r j n i b).2.2.2

/-- Native posterior support pays the pointwise mask's cell-membership requirement. -/
theorem paperCircleHistoryCellMask_posterior_error (a : ι → CCMCircleBoundedSymbol)
    (l r k j n : ℕ) (i : Fin (2^l)) (b : Bool)
    (s : List (ℝ≥0 × Grid (l+(reach j+r)+10))) :
    (paperCircleHistoryCellPosterior a l (reach j+r) k i s).Ex (fun x =>
      |(if x ∈ ((paperCircleObservationCell l i).child b).block (l+(reach j+r)+10)
        then (1:ℝ) else 0) - paperCircleHistoryCellMask l r j n i b x|) ≤
      Period.side n + (paperCircleHistoryCellPosterior a l (reach j+r) k i s).prob
        (flanked (paperCircleObservationCell l i) j) := by
  classical
  let P := paperCircleHistoryCellPosterior a l (reach j+r) k i s
  have hpoint (x : Grid (l+(reach j+r)+10)) (hx : 0 < P x) :
      |(if x ∈ ((paperCircleObservationCell l i).child b).block (l+(reach j+r)+10)
        then (1:ℝ) else 0) - paperCircleHistoryCellMask l r j n i b x| ≤
        Period.side n + if flanked (paperCircleObservationCell l i) j x then 1 else 0 := by
    have hmem := (paperCircleHistoryCellPosterior_pos_iff a l (reach j+r) k i s x).mp hx
    by_cases hfr : flanked (paperCircleObservationCell l i) j x
    · rw [if_pos hfr]
      have hb := paperCircleHistoryCellMask_bounds l r j n i b x
      have he : |(if x ∈ ((paperCircleObservationCell l i).child b).block
          (l+(reach j+r)+10) then (1:ℝ) else 0) -
            paperCircleHistoryCellMask l r j n i b x| ≤ 1 := by
        split_ifs <;> rw [abs_le] <;> constructor <;> linarith
      linarith [Period.side_pos n]
    rw [if_neg hfr, add_zero]
    exact (mask_spec l r j n i b).2.2.1 x hmem (fun h => hfr h.2)
  calc
    _ ≤ P.Ex (fun x => Period.side n +
        if flanked (paperCircleObservationCell l i) j x then 1 else 0) :=
      P.Ex_mono_mem hpoint
    _ = _ := by rw [Law.Ex_add, Law.Ex_const]; rfl

theorem paperCircleHistoryCellMask_posterior_error_geometry (a : ι → CCMCircleBoundedSymbol)
    (l r k j n : ℕ) (i : Fin (2^l)) (b : Bool)
    (s : List (ℝ≥0 × Grid (l+(reach j+r)+10))) :
    (paperCircleHistoryCellPosterior a l (reach j+r) k i s).Ex (fun x =>
      |(if x ∈ ((paperCircleObservationCell l i).child b).block (l+(reach j+r)+10)
        then (1:ℝ) else 0) - paperCircleHistoryCellMask l r j n i b x|) ≤
      Period.side n + 4 * Period.side (reach j) * (paperCircleObservationCell l i).len /
        paperCircleHistoryCellEvidence a l (reach j+r) k i s :=
  (paperCircleHistoryCellMask_posterior_error a l r k j n i b s).trans
    (add_le_add le_rfl (paperCircleHistoryCellPosterior_fringe a l r k j i s))

/-- The actual history energy pays the evidence denominator as well. -/
theorem paperCircleHistoryCellMask_posterior_error_energy (a : ι → CCMCircleBoundedSymbol)
    (l r k j n : ℕ) (i : Fin (2^l)) (b : Bool)
    (s : List (ℝ≥0 × Grid (l+(reach j+r)+10))) :
    (paperCircleHistoryCellPosterior a l (reach j+r) k i s).Ex (fun x =>
      |(if x ∈ ((paperCircleObservationCell l i).child b).block (l+(reach j+r)+10)
        then (1:ℝ) else 0) - paperCircleHistoryCellMask l r j n i b x|) ≤
      Period.side n + 16 * Period.side (reach j) * (paperCircleObservationCell l i).len *
        Real.exp (2 * Thermal.sumE (paperCircleObservationProfile a (l+(reach j+r)+10) k s)
          ((paperCircleObservationCell l i).start (l+(reach j+r)+10)) +
            Thermal.F (paperCircleHistoryComparisonForm a l (reach j+r) k i s)) :=
  (paperCircleHistoryCellMask_posterior_error a l r k j n i b s).trans
    (add_le_add le_rfl (paperCircleHistoryCellPosterior_fringe_exp a l r k j i s))

/-- One mask controls every character probe with the same paid posterior error. -/
theorem paperCircleHistoryCellMask_posterior_frequency_error
    (a : ι → CCMCircleBoundedSymbol) (l r k j n : ℕ) (i : Fin (2^l)) (b : Bool)
    (s : List (ℝ≥0 × Grid (l+(reach j+r)+10))) (u : Grid (l+(reach j+r)+10)) :
    ‖(paperCircleHistoryCellPosterior a l (reach j+r) k i s).Cx (fun x =>
      (((if x ∈ ((paperCircleObservationCell l i).child b).block (l+(reach j+r)+10)
        then (1:ℝ) else 0) - paperCircleHistoryCellMask l r j n i b x : ℝ) : ℂ) * chi u x)‖ ≤
      Period.side n + 4 * Period.side (reach j) * (paperCircleObservationCell l i).len /
        paperCircleHistoryCellEvidence a l (reach j+r) k i s := by
  have h := (paperCircleHistoryCellPosterior a l (reach j+r) k i s).Cx_norm (fun x =>
    (((if x ∈ ((paperCircleObservationCell l i).child b).block (l+(reach j+r)+10)
      then (1:ℝ) else 0) - paperCircleHistoryCellMask l r j n i b x : ℝ) : ℂ) * chi u x)
  simp only [norm_mul, norm_chi, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  exact h.trans (paperCircleHistoryCellMask_posterior_error_geometry a l r k j n i b s)

/-- The masked posterior expectation estimates the actual child probability. -/
theorem paperCircleHistoryCellMask_posterior_mass_error
    (a : ι → CCMCircleBoundedSymbol) (l r k j n : ℕ) (i : Fin (2^l)) (b : Bool)
    (s : List (ℝ≥0 × Grid (l+(reach j+r)+10))) :
    |(paperCircleHistoryCellPosterior a l (reach j+r) k i s).prob
        (fun x => x ∈ ((paperCircleObservationCell l i).child b).block (l+(reach j+r)+10)) -
      (paperCircleHistoryCellPosterior a l (reach j+r) k i s).Ex
        (paperCircleHistoryCellMask l r j n i b)| ≤
      Period.side n + 4 * Period.side (reach j) * (paperCircleObservationCell l i).len /
        paperCircleHistoryCellEvidence a l (reach j+r) k i s := by
  have h := paperCircleHistoryCellMask_posterior_frequency_error a l r k j n i b s 0
  simp only [chi_zero_left, mul_one, Law.Cx_ofReal, Complex.norm_real, Real.norm_eq_abs,
    Law.Ex_sub] at h
  exact h

end
end RHTower
