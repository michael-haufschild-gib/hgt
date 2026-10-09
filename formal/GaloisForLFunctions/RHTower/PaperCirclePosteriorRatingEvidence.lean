import GaloisForLFunctions.RHTower.PaperCirclePosteriorRating

/-! # Evidence pays the native adaptive rating budget

The actual history likelihood is at most one. Transferring the source's uniform
score budget through its exact posterior density therefore costs only inverse
evidence. This removes the procedure height and scale from the eventual rating
budget and its exponential tail.
-/

open Filter
open scoped Topology BigOperators NNReal
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- The exact native evidence normalizes the exponential rating into a unit budget. -/
theorem paperCircleHistoryRatedRoad_evidence_exponential_budget
    (a : ι → CCMCircleBoundedSymbol) (J k : ℕ)
    (s : List (ℝ≥0 × Grid (J+10))) :
    ∀ᶠ j : ℕ in atTop,
      paperCircleHistoryEvidence a (J+10) k s *
        (paperCircleHistoryPosterior a (J+10) k s).Ex (fun x =>
          Real.exp (Road.rating (paperCircleHistoryBegin a (J+10) k s)
            ((paperCircleHistoryRatedRoad a J k s j).hike x))) ≤ 1 := by
  filter_upwards [paperCircleHistoryRatedRoad_certified a J k s,
    Road.stake_upper, Road.stake_lower] with j hj hupper hlower
  let c := paperCircleHistoryBegin a (J+10) k s
  let road : Road j (J+10) c := paperCircleHistoryRatedRoad a J k s j
  let m := Road.prior (J+10)
  let P := paperCircleHistoryPosterior a (J+10) k s
  let E := paperCircleHistoryEvidence a (J+10) k s
  have he : 0 < E := paperCircleHistoryEvidence_pos a (J+10) k s
  have hactor : c.actor = P := paperCircleHistoryBegin_actor a (J+10) k s
  have hgrid : 1000 * (2:ℝ)^J ≤ 2^(J+10) := by
    rw [pow_add]
    have hpow : 0 ≤ (2:ℝ)^J := by positivity
    norm_num
    nlinarith
  have hready : m.Ready j c.fund := Road.prior_ready j (J+10)
  have hu : expU (Road.score road m) ≤ 1 := by
    have h := hupper (J+10) J hgrid c
      (paperCircleHistoryLikelihood a (J+10) k s) road hj.trusted m hready
    have hpref : Thermal.prefixE m.profile c.here = fun _ => 1 :=
      funext Road.prior_weight
    simp_rw [hpref, one_mul, expU_ex, Law.Ex_const] at h
    exact (expU_ex _).le.trans h
  have hpay (x : Grid (J+10)) :
      Real.exp (Road.rating c (road.hike x)) ≤ Road.score road m x :=
    hlower (J+10) J c (paperCircleHistoryLikelihood a (J+10) k s) road hj.trusted
      m hready (paperCircleHistoryBegin_mass_pos a (J+10) k s) x
      (by rw [hactor]; exact paperCircleHistoryPosterior_pos a (J+10) k s x)
      (Road.prior_tempered j (paperCircleHistoryLikelihood a (J+10) k s) x)
  have hweighted : E * P.Ex (Road.score road m) ≤ 1 := by
    calc
      _ = ∑ x, Period.side (J+10) * paperCircleHistoryLikelihood a (J+10) k s x *
          Road.score road m x := by
        unfold Law.Ex
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        dsimp only [P, E]
        rw [paperCircleHistoryPosterior_apply]
        field_simp [(paperCircleHistoryEvidence_pos a (J+10) k s).ne']
      _ ≤ ∑ x, Period.side (J+10) * Road.score road m x := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right (Period.side_pos (J+10)).le
            (paperCircleHistoryLikelihood_le_one a (J+10) k s x))
          (Road.score_nonneg road m x)
      _ = expU (Road.score road m) := by
        simp only [expU, smul_eq_mul, Finset.mul_sum]
      _ ≤ 1 := hu
  exact (mul_le_mul_of_nonneg_left (P.Ex_mono hpay) he.le).trans hweighted

theorem paperCircleHistoryRatedRoad_exponential_le_inverse_evidence
    (a : ι → CCMCircleBoundedSymbol) (J k : ℕ)
    (s : List (ℝ≥0 × Grid (J+10))) :
    ∀ᶠ j : ℕ in atTop,
      (paperCircleHistoryPosterior a (J+10) k s).Ex (fun x =>
        Real.exp (Road.rating (paperCircleHistoryBegin a (J+10) k s)
          ((paperCircleHistoryRatedRoad a J k s j).hike x))) ≤
        1 / paperCircleHistoryEvidence a (J+10) k s := by
  filter_upwards [paperCircleHistoryRatedRoad_evidence_exponential_budget a J k s] with j hj
  apply (le_div_iff₀ (paperCircleHistoryEvidence_pos a (J+10) k s)).mpr
  simpa only [mul_comm] using hj

/-- The actual evidence also pays the expected rating itself. -/
theorem paperCircleHistoryRatedRoad_mean_rating_le_evidence
    (a : ι → CCMCircleBoundedSymbol) (J k : ℕ)
    (s : List (ℝ≥0 × Grid (J+10))) :
    ∀ᶠ j : ℕ in atTop,
      (paperCircleHistoryPosterior a (J+10) k s).Ex (fun x =>
        Road.rating (paperCircleHistoryBegin a (J+10) k s)
          ((paperCircleHistoryRatedRoad a J k s j).hike x)) ≤
        -Real.log (paperCircleHistoryEvidence a (J+10) k s) := by
  filter_upwards [paperCircleHistoryRatedRoad_evidence_exponential_budget a J k s] with j hj
  let P := paperCircleHistoryPosterior a (J+10) k s
  let E := paperCircleHistoryEvidence a (J+10) k s
  let Y := fun x => Road.rating (paperCircleHistoryBegin a (J+10) k s)
    ((paperCircleHistoryRatedRoad a J k s j).hike x)
  have he : 0 < E := paperCircleHistoryEvidence_pos a (J+10) k s
  have h := P.Ex_mono (fun x => Real.add_one_le_exp (Y x + Real.log E))
  simp_rw [Real.exp_add, Real.exp_log he] at h
  rw [Law.Ex_add, Law.Ex_add, Law.Ex_const, Law.Ex_const, Law.Ex_mul] at h
  change E * P.Ex (fun x => Real.exp (Y x)) ≤ 1 at hj
  change P.Ex Y ≤ -Real.log E
  nlinarith

/-- A scale-independent eventual tail offset, paid by the actual history evidence. -/
theorem paperCircleHistoryRatedRoad_evidence_rating_tail
    (a : ι → CCMCircleBoundedSymbol) (J k : ℕ)
    (s : List (ℝ≥0 × Grid (J+10))) :
    ∀ᶠ j : ℕ in atTop, ∀ u : ℝ,
      (paperCircleHistoryPosterior a (J+10) k s).prob (fun x =>
        -Real.log (paperCircleHistoryEvidence a (J+10) k s) + u ≤
          Road.rating (paperCircleHistoryBegin a (J+10) k s)
            ((paperCircleHistoryRatedRoad a J k s j).hike x)) ≤ Real.exp (-u) := by
  filter_upwards [paperCircleHistoryRatedRoad_exponential_le_inverse_evidence a J k s]
    with j hj u
  let P := paperCircleHistoryPosterior a (J+10) k s
  let E := paperCircleHistoryEvidence a (J+10) k s
  let Y := fun x => Road.rating (paperCircleHistoryBegin a (J+10) k s)
    ((paperCircleHistoryRatedRoad a J k s j).hike x)
  let v := -Real.log E + u
  have htail := P.upperTail (fun x => v ≤ Y x) (fun x => Real.exp (Y x))
    (fun x => (Real.exp_pos (Y x)).le) (Real.exp v)
    (fun x hx => Real.exp_le_exp.mpr hx)
  have h := htail.trans hj
  have hid : Real.exp v * Real.exp (-u) = 1 / E := by
    rw [← Real.exp_add]
    dsimp [v]
    rw [show -Real.log E + u + -u = -Real.log E by ring,
      Real.exp_neg, Real.exp_log (paperCircleHistoryEvidence_pos a (J+10) k s), one_div]
  rw [← hid] at h
  exact le_of_mul_le_mul_left h (Real.exp_pos v)

end
end RHTower
