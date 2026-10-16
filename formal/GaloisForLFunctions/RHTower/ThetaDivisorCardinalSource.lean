import GaloisForLFunctions.RHTower.ThetaDivisorDecayClass
import GaloisForLFunctions.RHTower.ThetaEndpointDivisorClassification

/-!
# Full-multiplicity cardinal sources without an auxiliary rational filter

The polynomial polar notch fits inside the admissible numerator degree. Thus the
normalized cardinal packet is a literal smooth theta-relative source, including
at multiple Xi zeros, and has no artificial poles outside the critical strip.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower

def fullDivisionList (a : ℂ) : List ℂ := List.replicate (xiZeroMult a) a

theorem thetaDivisionList_full {a : ℂ} (ha : 0 < a.re) :
    ThetaDivisionList (fullDivisionList a) := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hb
    exact ha
  · simp only [fullDivisionList, count_replicate_eq]
    split_ifs with h
    · subst b
      exact (xiZeroMult_eq a).le
    · simp

theorem xiZeroMult_pos_of_zero {a : ℂ} (hz : XiC a = 0) : 0 < xiZeroMult a := by
  apply Nat.pos_of_ne_zero
  intro h
  have ho : analyticOrderAt XiC a = 0 := by rw [← xiZeroMult_eq, h]; rfl
  exact ((XiC_differentiable.analyticAt a).analyticOrderAt_eq_zero.mp ho) hz

theorem fullDivisionList_divisor_ne_zero {a z : ℂ} (ha : 0 < a.re)
    (hza : z ≠ a) (hzna : z ≠ -a) : listDivisor (fullDivisionList a) z ≠ 0 := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  rw [fullDivisionList, listDivisor_replicate]
  apply pow_ne_zero
  intro h
  have hs : z ^ 2 = a ^ 2 :=
    (div_eq_one_iff_eq (pow_ne_zero 2 ha0)).mp (sub_eq_zero.mp h).symm
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp hs).elim hza hzna

/-- Removing the complete multiplicity makes a nonvanishing numerator visible at its center. -/
theorem fullDivision_sourceTransform_ne_zero {a : ℂ} (ha : 0 < a.re)
    (e : Polynomial ℂ) (he : e.natDegree ≤ (fullDivisionList a).length)
    (heval : e.eval (a ^ 2) ≠ 0) :
    sourceTransform (listComb thetaListDivision (fullDivisionList a) e) a ≠ 0 := by
  have hL := thetaDivisionList_full ha
  obtain ⟨hs, _, _, hT, _⟩ := listComb_spec hL e he
  have hH := hs.differentiable_sourceTransform.analyticAt a
  have hE : AnalyticAt ℂ (fun z : ℂ => e.eval (z ^ 2)) a :=
    (e.differentiable.comp (differentiable_id.pow 2)).analyticAt a
  have heq : sourceTransform (listComb thetaListDivision (fullDivisionList a) e) *
      listDivisor (fullDivisionList a) = XiC * (fun z => e.eval (z ^ 2)) := funext hT
  have hord : analyticOrderAt
      (sourceTransform (listComb thetaListDivision (fullDivisionList a) e)) a +
        (xiZeroMult a : ℕ∞) = (xiZeroMult a : ℕ∞) := by
    have hP : analyticOrderAt (listDivisor (fullDivisionList a)) a = (xiZeroMult a : ℕ∞) := by
      rw [analyticOrderAt_listDivisor ha _ hL.1]
      simp [fullDivisionList]
    conv_lhs => rhs; rw [← hP]
    rw [← analyticOrderAt_mul hH ((differentiable_listDivisor _).analyticAt a)]
    rw [heq, analyticOrderAt_mul (XiC_differentiable.analyticAt a) hE,
      hE.analyticOrderAt_eq_zero.mpr heval, add_zero, xiZeroMult_eq]
  apply hH.analyticOrderAt_eq_zero.mp
  apply ENat.add_left_injective_of_ne_top (n := (xiZeroMult a : ℕ∞)) (by simp)
  simpa only [zero_add] using hord

def cardinalNotch : Polynomial ℂ := Polynomial.X + Polynomial.C (1/4)

theorem cardinalNotch_eval (z : ℂ) : cardinalNotch.eval (z^2) = z^2 + 1/4 := by
  simp [cardinalNotch]

theorem cardinalNotch_eval_ne_zero {a : ℂ} (ha : 0 < a.re) :
    cardinalNotch.eval (a^2) ≠ 0 := by
  rw [cardinalNotch_eval]
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] at hre him
  norm_num at hre him
  have hai : a.im = 0 := by nlinarith
  rw [hai] at hre
  nlinarith [sq_nonneg a.re]

def notchedDivisorSource (a : ℂ) : ℝ → ℂ :=
  listComb thetaListDivision (fullDivisionList a) cardinalNotch

theorem cardinalNotch_degree {a : ℂ} (hz : XiC a = 0) :
    cardinalNotch.natDegree ≤ (fullDivisionList a).length := by
  simp only [cardinalNotch, Polynomial.natDegree_X_add_C, fullDivisionList, List.length_replicate]
  exact xiZeroMult_pos_of_zero hz

theorem notchedDivisorSource_spec {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0) :
    ExpMomentSource (notchedDivisorSource a) ∧
      (∀ x, notchedDivisorSource a (-x) = notchedDivisorSource a x) ∧
      (∃ C, ∀ x, ‖notchedDivisorSource a x‖ ≤ C * thetaCuspFullSource x) ∧
      ∀ z, sourceTransform (notchedDivisorSource a) z * listDivisor (fullDivisionList a) z =
        XiC z * (z^2 + 1/4) := by
  obtain ⟨hs, he, hb, ht, _⟩ := listComb_spec (thetaDivisionList_full ha) cardinalNotch
    (cardinalNotch_degree hz)
  exact ⟨hs, he, hb, fun z => by simpa only [notchedDivisorSource, cardinalNotch_eval] using ht z⟩

theorem notchedDivisorSource_center_ne_zero {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0) :
    sourceTransform (notchedDivisorSource a) a ≠ 0 :=
  fullDivision_sourceTransform_ne_zero ha cardinalNotch (cardinalNotch_degree hz)
    (cardinalNotch_eval_ne_zero ha)

/-- A literal theta-relative source with cardinal transform on one unsigned zero pair. -/
def divisorCardinalSource (a : ℂ) (x : ℝ) : ℂ :=
  (sourceTransform (notchedDivisorSource a) a)⁻¹ * notchedDivisorSource a x

theorem divisorCardinalSource_regularity {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0) :
    ExpMomentSource (divisorCardinalSource a) ∧
      ExponentialFirstJet (divisorCardinalSource a) ∧
      (∃ C, LipschitzWith C (divisorCardinalSource a)) ∧
      (∀ x, divisorCardinalSource a (-x) = divisorCardinalSource a x) ∧
      ∃ C, ∀ x, ‖divisorCardinalSource a x‖ ≤ C * thetaCuspFullSource x := by
  obtain ⟨hs, he, ⟨M, hb⟩, _⟩ := notchedDivisorSource_spec ha hz
  obtain ⟨C, hC⟩ := exists_lipschitz_listComb (fullDivisionList a) cardinalNotch
  let c := (sourceTransform (notchedDivisorSource a) a)⁻¹
  refine ⟨hs.const_mul c,
    (exponentialFirstJet_listComb (thetaDivisionList_full ha) cardinalNotch).const_mul c,
    ⟨_, (lipschitzWith_smul c).comp hC⟩,
    fun x => by simp only [divisorCardinalSource, he x], ‖c‖ * M, fun x => ?_⟩
  change ‖c * notchedDivisorSource a x‖ ≤ _
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg c)

theorem divisorCardinalSource_transform {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0)
    {z : ℂ} (hzero : XiC z = 0) :
    sourceTransform (divisorCardinalSource a) z = if z = a ∨ z = -a then 1 else 0 := by
  have hn := notchedDivisorSource_center_ne_zero ha hz
  obtain ⟨_, he, _, hT⟩ := notchedDivisorSource_spec ha hz
  unfold divisorCardinalSource
  rw [sourceTransform_const_mul]
  split_ifs with h
  · rcases h with rfl | rfl
    · exact inv_mul_cancel₀ hn
    · rw [sourceTransform_neg_eq_of_even he]
      exact inv_mul_cancel₀ hn
  · have hp := fullDivisionList_divisor_ne_zero ha (fun h' => h (Or.inl h'))
      (fun h' => h (Or.inr h'))
    have ht := hT z
    rw [hzero, zero_mul] at ht
    rw [(mul_eq_zero.mp ht).resolve_right hp, mul_zero]

theorem divisorCardinalSource_poles {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0) :
    sourceTransform (divisorCardinalSource a) (I/2) = 0 ∧
      sourceTransform (divisorCardinalSource a) (-I/2) = 0 := by
  obtain ⟨_, he, _, hT⟩ := notchedDivisorSource_spec ha hz
  have hne : (I/2 : ℂ) ≠ a := by intro h; rw [← h] at ha; norm_num at ha
  have hneg : (I/2 : ℂ) ≠ -a := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have ht := hT (I/2)
  have hpoly : (I/2 : ℂ)^2 + 1/4 = 0 := by norm_num [div_pow]
  rw [hpoly, mul_zero] at ht
  have hzero := (mul_eq_zero.mp ht).resolve_right (fullDivisionList_divisor_ne_zero ha hne hneg)
  constructor
  · unfold divisorCardinalSource
    rw [sourceTransform_const_mul, hzero, mul_zero]
  · unfold divisorCardinalSource
    rw [sourceTransform_const_mul]
    rw [show (-I/2 : ℂ) = -(I/2) by ring, sourceTransform_neg_eq_of_even he, hzero, mul_zero]

end RHTower
