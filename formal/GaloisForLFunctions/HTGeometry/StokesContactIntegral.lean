import GaloisForLFunctions.HTGeometry.StokesContactProfile

/-!
# Analytic step-integral realization of complementary contact

The reciprocal-ramification loss in `ContactTower` is not merely a formal finite sum.  This file
constructs its consecutive real intervals and proves that the sum of their genuine interval
integrals equals the recursively defined loss.  Thus complementary contact is exactly top height
minus the analytic reciprocal-index path integral.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

/-- One constant reciprocal-ramification interval. -/
structure ContactSegment where
  lower : ℝ
  upper : ℝ
  ramification : ℕ

namespace ContactSegment

/-- Genuine interval integral of reciprocal ramification on one segment. -/
noncomputable def integral (s : ContactSegment) : ℝ :=
  ∫ _u : ℝ in s.lower..s.upper, (1 : ℝ) / (s.ramification : ℝ)

/-- Evaluation of a constant reciprocal-ramification interval integral. -/
theorem integral_eq (s : ContactSegment) :
    s.integral = (s.upper - s.lower) / (s.ramification : ℝ) := by
  rw [integral, intervalIntegral.integral_const]
  simp
  ring

end ContactSegment

namespace ContactTower

/-- Consecutive analytic segments, with `scale` the ramification accumulated above this tower. -/
def segments : ContactTower → ℕ → List ContactSegment
  | .leaf _, _ => []
  | .step level factor tail, scale =>
      { lower := tail.top
        upper := level
        ramification := scale * factor } :: tail.segments (scale * factor)

/-- Analytic reciprocal-ramification path integral, evaluated segment by segment. -/
noncomputable def analyticLoss (t : ContactTower) (scale : ℕ := 1) : ℝ :=
  (t.segments scale).map ContactSegment.integral |>.sum

/-- Exact analytic evaluation at arbitrary positive accumulated ramification. -/
theorem analyticLoss_eq_loss_div (t : ContactTower) (hvalid : t.Valid)
    {scale : ℕ} (hscale : 0 < scale) :
    t.analyticLoss scale = (t.loss : ℝ) / (scale : ℝ) := by
  induction t generalizing scale with
  | leaf height => simp [analyticLoss, segments, loss]
  | step level factor tail ih =>
      simp only [Valid] at hvalid
      have hfactor : 0 < factor := Nat.zero_lt_of_lt hvalid.1
      have hscaleFactor : 0 < scale * factor := Nat.mul_pos hscale hfactor
      rw [analyticLoss, segments]
      simp only [List.map_cons, List.sum_cons]
      rw [ContactSegment.integral_eq]
      change (((level : ℝ) - (tail.top : ℝ)) / ((scale * factor : ℕ) : ℝ) +
        tail.analyticLoss (scale * factor)) = ((ContactTower.step level factor tail).loss : ℝ) /
          (scale : ℝ)
      rw [ih hvalid.2.2 hscaleFactor]
      simp only [loss, top]
      push_cast
      have hs : (scale : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hscale)
      have hf : (factor : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hfactor)
      field_simp

/-- At unit initial scale, analytic step integration is exactly the rational path loss. -/
theorem analyticLoss_eq_loss (t : ContactTower) (hvalid : t.Valid) :
    t.analyticLoss = (t.loss : ℝ) := by
  simpa using t.analyticLoss_eq_loss_div hvalid Nat.zero_lt_one

/-- Every nontrivial valid continuation contributes a strictly positive analytic integral. -/
theorem analyticLoss_step_pos {level : ℚ} {factor : ℕ} {tail : ContactTower}
    (hvalid : (ContactTower.step level factor tail).Valid) :
    0 < (ContactTower.step level factor tail).analyticLoss := by
  rw [(ContactTower.step level factor tail).analyticLoss_eq_loss hvalid]
  exact_mod_cast ContactTower.loss_step_pos hvalid

/-- Analytic complementary-contact law. -/
theorem contact_eq_top_sub_analyticLoss (t : ContactTower) (hvalid : t.Valid) :
    (t.contact : ℝ) = (t.top : ℝ) - t.analyticLoss := by
  rw [t.analyticLoss_eq_loss hvalid]
  exact_mod_cast t.contact_eq_top_sub_loss

/-- Complementary contact written with an arbitrary reference height `eta`: the unramified
segment above the first level has reciprocal index one. -/
noncomputable def etaAnalyticContact (t : ContactTower) (eta : ℝ) : ℝ :=
  eta - ((∫ _u : ℝ in (t.top : ℝ)..eta, (1 : ℝ)) + t.analyticLoss)

/-- The analytic complementary contact is independent of the reference height `eta`. -/
theorem etaAnalyticContact_eq_contact (t : ContactTower) (hvalid : t.Valid) (eta : ℝ) :
    t.etaAnalyticContact eta = (t.contact : ℝ) := by
  rw [etaAnalyticContact, intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  rw [t.contact_eq_top_sub_analyticLoss hvalid]
  ring

theorem etaAnalyticContact_independent (t : ContactTower) (hvalid : t.Valid)
    (eta eta' : ℝ) :
    t.etaAnalyticContact eta = t.etaAnalyticContact eta' := by
  rw [t.etaAnalyticContact_eq_contact hvalid, t.etaAnalyticContact_eq_contact hvalid]

end ContactTower

end IrregularStokes
end GaloisForLFunctions
