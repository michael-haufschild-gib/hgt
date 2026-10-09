import GaloisForLFunctions.RHTower.PaperCircleSubgridProbability
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Thermal.Power

/-! # Even-moment majorants for actual native Gibbs frequency polynomials

The conditional native frequency law supplies positive coefficients. Arbitrary real
phases cannot increase any even moment under the actual localized Gibbs law. The
positive-coefficient moment is exactly the source compression heat moment.
-/

open scoped BigOperators NNReal
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

def paperCirclePhasePolynomial (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0)
    (θ : Grid (paperCircleSubgridLevel M k) → ℝ) (y : Grid M) : ℂ :=
  Thermal.ply (paperCircleSubgrid_le M k) (paperCircleSubgridLaw a M k t)
    (fun x => Complex.exp ((θ x : ℂ) * Complex.I)) y

theorem paperCirclePhasePolynomial_norm_le (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) (y : Grid M) :
    ‖paperCirclePhasePolynomial a M k t θ y‖ ≤ 1 :=
  Thermal.ply_unit _ _ _ (fun x => (Complex.norm_exp_ofReal_mul_I (θ x)).le) y

theorem paperCirclePhasePolynomial_zero_phase (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) :
    paperCirclePhasePolynomial a M k t (fun _ => 0) =
      Thermal.ply (paperCircleSubgrid_le M k) (paperCircleSubgridLaw a M k t) 1 := by
  unfold paperCirclePhasePolynomial
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  rfl

def paperCirclePhaseMoment (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0)
    (θ : Grid (paperCircleSubgridLevel M k) → ℝ) (N : ℕ) : ℝ :=
  (paperCircleLocalizedLaw a M k t).Ex (fun y => ‖paperCirclePhasePolynomial a M k t θ y‖ ^ (2 * N))

theorem paperCirclePhaseMoment_zero_phase (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (N : ℕ) :
    paperCirclePhaseMoment a M k t (fun _ => 0) N =
      Thermal.HeatM (paperCircleSubgrid_le M k) (paperCircleLocalizedForm a M k t)
        (paperCircleSubgridLaw a M k t) N := by
  unfold paperCirclePhaseMoment
  rw [paperCirclePhasePolynomial_zero_phase]
  rfl

theorem paperCirclePhaseMoment_zero_order (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) :
    paperCirclePhaseMoment a M k t θ 0 = 1 := by
  simp only [paperCirclePhaseMoment, mul_zero, pow_zero, Law.Ex_const]

theorem paperCirclePhaseMoment_nonneg (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) (N : ℕ) :
    0 ≤ paperCirclePhaseMoment a M k t θ N :=
  Law.Ex_nonneg _ (fun _ => pow_nonneg (norm_nonneg _) _)

/-- Every even moment is largest when all native frequency coefficients have zero phase. -/
theorem paperCirclePhaseMoment_majorant (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) (N : ℕ) :
    paperCirclePhaseMoment a M k t θ N ≤ paperCirclePhaseMoment a M k t (fun _ => 0) N := by
  let A := paperCircleLocalizedForm a M k t
  have H := Thermal.weighted_envelope N (paperCircleSubgrid_le M k) A
    (paperCircleSubgridLaw a M k t) (fun x => Complex.exp ((θ x : ℂ) * Complex.I))
    (fun x => (Complex.norm_exp_ofReal_mul_I (θ x)).le) (Thermal.K A) 1 (by
      intro u
      rw [← Thermal.label_cx, ← Thermal.cred_eq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Thermal.cred_nonneg (paperCircleLocalizedForm_nonneg a M k t) u), one_mul])
  rw [← Thermal.label_ex, one_mul] at H
  rw [paperCirclePhaseMoment_zero_phase]
  exact H

theorem paperCirclePhaseMoment_le_one (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) (N : ℕ) :
    paperCirclePhaseMoment a M k t θ N ≤ 1 := by
  apply (paperCirclePhaseMoment_majorant a M k t θ N).trans
  rw [paperCirclePhaseMoment_zero_phase]
  exact (Thermal.HeatM_bounds _ _ _ _).2

/-- The positive-coefficient moment never vanishes, at any finite order. -/
theorem paperCirclePhaseMoment_zero_phase_pos (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (N : ℕ) :
    0 < paperCirclePhaseMoment a M k t (fun _ => 0) N := by
  rw [paperCirclePhaseMoment_zero_phase]
  exact (Thermal.HeatM_bounds _ _ _ _).1

theorem antitone_paperCirclePhaseMoment (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (θ : Grid (paperCircleSubgridLevel M k) → ℝ) :
    Antitone (paperCirclePhaseMoment a M k t θ) := by
  intro m n h
  exact Law.Ex_mono _ (fun y => pow_le_pow_of_le_one (norm_nonneg _)
    (paperCirclePhasePolynomial_norm_le a M k t θ y) (Nat.mul_le_mul_left 2 h))

/-- The source compression moment is paid by the actual native polynomial and Gibbs law. -/
theorem paperCirclePhaseMoment_compression_identity (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (N : ℕ) :
    Compress.heatMoment (Fin N) (paperCircleSubgridLaw a M k t) id
      (paperCircleSubgridCost a M k t) = paperCirclePhaseMoment a M k t (fun _ => 0) N := by
  have H := Thermal.selected_heat N (paperCircleSubgrid_le M k)
    (paperCircleLocalizedForm a M k t) (fun x => div_pos
      (paperCircleLocalizedHeat_pos a M k t x) (Thermal.q_origin_pos _))
    (paperCircleSubgridLaw a M k t) (fun x => x)
  rw [Law.send_id] at H
  rw [paperCirclePhaseMoment_zero_phase]
  exact H

def paperCirclePhaseMomentCost (a : ι → CCMCircleBoundedSymbol) (M k : ℕ) (t : ℝ≥0)
    (N : ℕ) : ℝ := -Real.log (paperCirclePhaseMoment a M k t (fun _ => 0) N)

theorem paperCirclePhaseMomentCost_nonneg (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (N : ℕ) : 0 ≤ paperCirclePhaseMomentCost a M k t N :=
  neg_nonneg.mpr (Real.log_nonpos (paperCirclePhaseMoment_zero_phase_pos a M k t N).le
    (paperCirclePhaseMoment_le_one a M k t _ N))

theorem paperCirclePhaseMomentCost_exp (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) (N : ℕ) :
    Real.exp (-paperCirclePhaseMomentCost a M k t N) =
      paperCirclePhaseMoment a M k t (fun _ => 0) N := by
  rw [paperCirclePhaseMomentCost, neg_neg,
    Real.exp_log (paperCirclePhaseMoment_zero_phase_pos a M k t N)]

theorem monotone_paperCirclePhaseMomentCost (a : ι → CCMCircleBoundedSymbol)
    (M k : ℕ) (t : ℝ≥0) : Monotone (paperCirclePhaseMomentCost a M k t) := by
  intro m n h
  exact neg_le_neg (Real.log_le_log (paperCirclePhaseMoment_zero_phase_pos a M k t n)
    (antitone_paperCirclePhaseMoment a M k t (fun _ => 0) h))

end
end RHTower
