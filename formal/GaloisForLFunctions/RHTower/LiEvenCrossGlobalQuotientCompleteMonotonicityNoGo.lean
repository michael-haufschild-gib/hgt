import GaloisForLFunctions.RHTower.LiEvenCrossLocalBernsteinShapeNoGo

/-!
# Global real-ray complete monotonicity still does not orient the LI tower

The exact LI radial response has atoms `z * b / (z+b)^(2 : ℕ)`; after division by `z`, its
quotient atoms are `b / (z+b)^(2 : ℕ)`.  This module proves that the conjugation-symmetric packet
`7 × (1/2) + (3/4+i) + (3/4-i)` has a strictly completely monotone quotient response on the
entire positive real ray, at every derivative order, while its fourth completed-Abel endpoint
mode is strictly negative.

Hence global real-variable shape of the quotient response cannot orient the LI coefficient
tower.  A surviving argument must use complex analytic continuation or singularity-support
control capable of excluding off-axis squared nodes.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

def liLocalRadialQuotientAtom (b z : ℂ) : ℂ := b / (z + b) ^ (2 : ℕ)

theorem iteratedDeriv_liLocalRadialQuotientAtom (b : ℂ) (m : ℕ) (z : ℂ)
    (hz : z + b ≠ 0) :
    iteratedDeriv m (liLocalRadialQuotientAtom b) z =
      (-1 : ℂ) ^ m * ((m + 1).factorial : ℂ) * b / (z + b) ^ (m + 2) := by
  have hs : ContDiffAt ℂ m (fun w : ℂ => ((w + b) ^ (2 : ℕ))⁻¹) z :=
    ((contDiffAt_id.add contDiffAt_const).pow 2).inv (pow_ne_zero 2 hz)
  change iteratedDeriv m (fun w : ℂ => b * ((w + b) ^ (2 : ℕ))⁻¹) z = _
  rw [iteratedDeriv_const_mul b hs, iteratedDeriv_invSq_add_const b m z hz]
  ring

def liLocalRadialQuotientSignedJet (b : ℂ) (m : ℕ) (v : ℝ) : ℂ :=
  ((m + 1).factorial : ℂ) * b / ((v : ℂ) + b) ^ (m + 2)

theorem negOnePow_mul_iteratedDeriv_liLocalRadialQuotientAtom
    (b : ℂ) (m : ℕ) (v : ℝ) (hz : (v : ℂ) + b ≠ 0) :
    (-1 : ℂ) ^ m * iteratedDeriv m (liLocalRadialQuotientAtom b) (v : ℂ) =
      liLocalRadialQuotientSignedJet b m v := by
  rw [iteratedDeriv_liLocalRadialQuotientAtom b m (v : ℂ) hz,
    liLocalRadialQuotientSignedJet]
  have hsign : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    (-1 : ℂ) ^ m *
        ((-1 : ℂ) ^ m * ((m + 1).factorial : ℂ) * b /
          ((v : ℂ) + b) ^ (m + 2)) =
      ((-1 : ℂ) ^ m * (-1 : ℂ) ^ m) *
        (((m + 1).factorial : ℂ) * b / ((v : ℂ) + b) ^ (m + 2)) := by ring
    _ = ((m + 1).factorial : ℂ) * b / ((v : ℂ) + b) ^ (m + 2) := by
      rw [hsign, one_mul]

theorem liLocalRadialQuotientSignedJet_base_eq_ofReal (m : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    liLocalRadialQuotientSignedJet liLocalOnLineNode m v =
      ((((m + 1).factorial : ℝ) * (1 / 2) / (v + 1 / 2) ^ (m + 2) : ℝ) : ℂ) := by
  have hden : v + 1 / 2 ≠ 0 := by linarith
  simp only [liLocalRadialQuotientSignedJet, liLocalOnLineNode]
  norm_num [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow]

theorem liLocalRadialQuotientSignedJet_base_re (m : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    (liLocalRadialQuotientSignedJet liLocalOnLineNode m v).re =
      ((m + 1).factorial : ℝ) * (1 / 2) / (v + 1 / 2) ^ (m + 2) := by
  rw [liLocalRadialQuotientSignedJet_base_eq_ofReal m v hv]
  rfl

theorem add_half_le_norm_add_liLocalOffLineNode {v : ℝ} (hv : 0 ≤ v) :
    v + 1 / 2 ≤ ‖(v : ℂ) + liLocalOffLineNode‖ := by
  rw [Complex.norm_def]
  rw [Real.le_sqrt (by linarith)]
  simp [liLocalOffLineNode, Complex.normSq_apply]
  all_goals try exact Complex.normSq_nonneg _
  nlinarith

theorem add_half_le_norm_add_liLocalOffLineNodeConj {v : ℝ} (hv : 0 ≤ v) :
    v + 1 / 2 ≤ ‖(v : ℂ) + liLocalOffLineNodeConj‖ := by
  rw [Complex.norm_def]
  rw [Real.le_sqrt (by linarith)]
  simp [liLocalOffLineNodeConj, Complex.normSq_apply]
  all_goals try exact Complex.normSq_nonneg _
  nlinarith

theorem norm_liLocalRadialQuotientSignedJet_offPlus_le (m : ℕ) {v : ℝ}
    (hv : 0 ≤ v) :
    ‖liLocalRadialQuotientSignedJet liLocalOffLineNode m v‖ ≤
      ((m + 1).factorial : ℝ) * (5 / 4) / (v + 1 / 2) ^ (m + 2) := by
  have hden : (v + 1 / 2) ^ (m + 2) ≤
      ‖(v : ℂ) + liLocalOffLineNode‖ ^ (m + 2) :=
    pow_le_pow_left₀ (by linarith) (add_half_le_norm_add_liLocalOffLineNode hv) _
  rw [liLocalRadialQuotientSignedJet, norm_div, norm_mul, norm_pow,
    norm_liLocalOffLineNode]
  norm_num
  gcongr

theorem norm_liLocalRadialQuotientSignedJet_offMinus_le (m : ℕ) {v : ℝ}
    (hv : 0 ≤ v) :
    ‖liLocalRadialQuotientSignedJet liLocalOffLineNodeConj m v‖ ≤
      ((m + 1).factorial : ℝ) * (5 / 4) / (v + 1 / 2) ^ (m + 2) := by
  have hden : (v + 1 / 2) ^ (m + 2) ≤
      ‖(v : ℂ) + liLocalOffLineNodeConj‖ ^ (m + 2) :=
    pow_le_pow_left₀ (by linarith) (add_half_le_norm_add_liLocalOffLineNodeConj hv) _
  rw [liLocalRadialQuotientSignedJet, norm_div, norm_mul, norm_pow,
    norm_liLocalOffLineNodeConj]
  norm_num
  gcongr

theorem quotientSignedJetCounterexample_pos (m : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    0 < (7 * liLocalRadialQuotientSignedJet liLocalOnLineNode m v +
      liLocalRadialQuotientSignedJet liLocalOffLineNode m v +
      liLocalRadialQuotientSignedJet liLocalOffLineNodeConj m v).re := by
  let F : ℝ := ((m + 1).factorial : ℝ) / (v + 1 / 2) ^ (m + 2)
  have hF : 0 < F := by
    dsimp [F]
    positivity
  have hb : (liLocalRadialQuotientSignedJet liLocalOnLineNode m v).re = (1 / 2) * F := by
    rw [liLocalRadialQuotientSignedJet_base_re m v hv]
    dsimp [F]
    ring
  have hp : ‖liLocalRadialQuotientSignedJet liLocalOffLineNode m v‖ ≤ (5 / 4) * F := by
    have := norm_liLocalRadialQuotientSignedJet_offPlus_le m hv
    convert this using 1
    dsimp [F]
    ring
  have hm : ‖liLocalRadialQuotientSignedJet liLocalOffLineNodeConj m v‖ ≤ (5 / 4) * F := by
    have := norm_liLocalRadialQuotientSignedJet_offMinus_le m hv
    convert this using 1
    dsimp [F]
    ring
  have hpair : |(liLocalRadialQuotientSignedJet liLocalOffLineNode m v +
      liLocalRadialQuotientSignedJet liLocalOffLineNodeConj m v).re| ≤ 2 * ((5 / 4) * F) := by
    calc
      |(liLocalRadialQuotientSignedJet liLocalOffLineNode m v +
          liLocalRadialQuotientSignedJet liLocalOffLineNodeConj m v).re| ≤
          ‖liLocalRadialQuotientSignedJet liLocalOffLineNode m v +
            liLocalRadialQuotientSignedJet liLocalOffLineNodeConj m v‖ :=
        Complex.abs_re_le_norm _
      _ ≤ ‖liLocalRadialQuotientSignedJet liLocalOffLineNode m v‖ +
          ‖liLocalRadialQuotientSignedJet liLocalOffLineNodeConj m v‖ := norm_add_le _ _
      _ ≤ (5 / 4) * F + (5 / 4) * F := add_le_add hp hm
      _ = 2 * ((5 / 4) * F) := by ring
  have hpairlower : -2 * ((5 / 4) * F) ≤
      (liLocalRadialQuotientSignedJet liLocalOffLineNode m v +
        liLocalRadialQuotientSignedJet liLocalOffLineNodeConj m v).re := by
    linarith [neg_abs_le (liLocalRadialQuotientSignedJet liLocalOffLineNode m v +
      liLocalRadialQuotientSignedJet liLocalOffLineNodeConj m v).re]
  have hpairlower' : -2 * ((5 / 4) * F) ≤
      (liLocalRadialQuotientSignedJet liLocalOffLineNode m v).re +
        (liLocalRadialQuotientSignedJet liLocalOffLineNodeConj m v).re := by
    simpa only [Complex.add_re] using hpairlower
  simp only [Complex.add_re, Complex.mul_re]
  norm_num
  rw [hb]
  nlinarith

def liLocalQuotientComplexResponse (z : ℂ) : ℂ :=
  7 * liLocalRadialQuotientAtom liLocalOnLineNode z +
    liLocalRadialQuotientAtom liLocalOffLineNode z +
    liLocalRadialQuotientAtom liLocalOffLineNodeConj z

def liLocalQuotientResponse (v : ℝ) : ℝ := (liLocalQuotientComplexResponse v).re

theorem contDiffAt_liLocalRadialQuotientAtom (b z : ℂ) (hz : z + b ≠ 0) (n : ℕ∞) :
    ContDiffAt ℂ n (liLocalRadialQuotientAtom b) z := by
  exact contDiffAt_const.div ((contDiffAt_id.add contDiffAt_const).pow 2)
    (pow_ne_zero 2 hz)

theorem signed_iteratedDeriv_liLocalQuotientComplexResponse (m : ℕ) {v : ℝ}
    (hv : -(1 / 2) < v) :
    (-1 : ℂ) ^ m * iteratedDeriv m liLocalQuotientComplexResponse (v : ℂ) =
      7 * liLocalRadialQuotientSignedJet liLocalOnLineNode m v +
        liLocalRadialQuotientSignedJet liLocalOffLineNode m v +
        liLocalRadialQuotientSignedJet liLocalOffLineNodeConj m v := by
  have h0 := add_liLocalOnLineNode_ne_zero hv
  have hp := add_liLocalOffLineNode_ne_zero v
  have hm := add_liLocalOffLineNodeConj_ne_zero v
  have hc0 := contDiffAt_liLocalRadialQuotientAtom liLocalOnLineNode (v : ℂ) h0 m
  have hcp := contDiffAt_liLocalRadialQuotientAtom liLocalOffLineNode (v : ℂ) hp m
  have hcm := contDiffAt_liLocalRadialQuotientAtom liLocalOffLineNodeConj (v : ℂ) hm m
  have h7 : ContDiffAt ℂ m
      (fun z => 7 * liLocalRadialQuotientAtom liLocalOnLineNode z) (v : ℂ) :=
    contDiffAt_const.mul hc0
  change (-1 : ℂ) ^ m * iteratedDeriv m
      (fun z => (7 * liLocalRadialQuotientAtom liLocalOnLineNode z +
        liLocalRadialQuotientAtom liLocalOffLineNode z) +
        liLocalRadialQuotientAtom liLocalOffLineNodeConj z) (v : ℂ) = _
  have hsplit0 : iteratedDeriv m
      (fun z => 7 * liLocalRadialQuotientAtom liLocalOnLineNode z +
        liLocalRadialQuotientAtom liLocalOffLineNode z) (v : ℂ) =
      iteratedDeriv m (fun z => 7 * liLocalRadialQuotientAtom liLocalOnLineNode z) (v : ℂ) +
        iteratedDeriv m (liLocalRadialQuotientAtom liLocalOffLineNode) (v : ℂ) := by
    rw [show (fun z => 7 * liLocalRadialQuotientAtom liLocalOnLineNode z +
      liLocalRadialQuotientAtom liLocalOffLineNode z) =
      (fun z => 7 * liLocalRadialQuotientAtom liLocalOnLineNode z) +
        liLocalRadialQuotientAtom liLocalOffLineNode by rfl]
    exact iteratedDeriv_add h7 hcp
  have hsplit : iteratedDeriv m
      (fun z => (7 * liLocalRadialQuotientAtom liLocalOnLineNode z +
        liLocalRadialQuotientAtom liLocalOffLineNode z) +
        liLocalRadialQuotientAtom liLocalOffLineNodeConj z) (v : ℂ) =
      iteratedDeriv m
          (fun z => 7 * liLocalRadialQuotientAtom liLocalOnLineNode z +
            liLocalRadialQuotientAtom liLocalOffLineNode z) (v : ℂ) +
        iteratedDeriv m (liLocalRadialQuotientAtom liLocalOffLineNodeConj) (v : ℂ) := by
    rw [show (fun z => (7 * liLocalRadialQuotientAtom liLocalOnLineNode z +
      liLocalRadialQuotientAtom liLocalOffLineNode z) +
      liLocalRadialQuotientAtom liLocalOffLineNodeConj z) =
      (fun z => 7 * liLocalRadialQuotientAtom liLocalOnLineNode z +
        liLocalRadialQuotientAtom liLocalOffLineNode z) +
        liLocalRadialQuotientAtom liLocalOffLineNodeConj by rfl]
    exact iteratedDeriv_add (h7.add hcp) hcm
  rw [hsplit, hsplit0, iteratedDeriv_const_mul 7 hc0]
  calc
    (-1 : ℂ) ^ m *
        (7 * iteratedDeriv m (liLocalRadialQuotientAtom liLocalOnLineNode) (v : ℂ) +
          iteratedDeriv m (liLocalRadialQuotientAtom liLocalOffLineNode) (v : ℂ) +
          iteratedDeriv m (liLocalRadialQuotientAtom liLocalOffLineNodeConj) (v : ℂ)) =
      7 * ((-1 : ℂ) ^ m * iteratedDeriv m
        (liLocalRadialQuotientAtom liLocalOnLineNode) (v : ℂ)) +
        ((-1 : ℂ) ^ m * iteratedDeriv m
          (liLocalRadialQuotientAtom liLocalOffLineNode) (v : ℂ)) +
        ((-1 : ℂ) ^ m * iteratedDeriv m
          (liLocalRadialQuotientAtom liLocalOffLineNodeConj) (v : ℂ)) := by ring
    _ = _ := by
      rw [negOnePow_mul_iteratedDeriv_liLocalRadialQuotientAtom
          liLocalOnLineNode m v h0,
        negOnePow_mul_iteratedDeriv_liLocalRadialQuotientAtom
          liLocalOffLineNode m v hp,
        negOnePow_mul_iteratedDeriv_liLocalRadialQuotientAtom
          liLocalOffLineNodeConj m v hm]

theorem analyticAt_liLocalRadialQuotientAtom (b z : ℂ) (hz : z + b ≠ 0) :
    AnalyticAt ℂ (liLocalRadialQuotientAtom b) z := by
  exact analyticAt_const.div ((analyticAt_id.add analyticAt_const).pow 2)
    (pow_ne_zero 2 hz)

theorem analyticAt_liLocalQuotientComplexResponse_of_gt {v : ℝ} (hv : -(1 / 2) < v) :
    AnalyticAt ℂ liLocalQuotientComplexResponse (v : ℂ) := by
  have h0 := analyticAt_liLocalRadialQuotientAtom liLocalOnLineNode (v : ℂ)
    (add_liLocalOnLineNode_ne_zero hv)
  have hp := analyticAt_liLocalRadialQuotientAtom liLocalOffLineNode (v : ℂ)
    (add_liLocalOffLineNode_ne_zero v)
  have hm := analyticAt_liLocalRadialQuotientAtom liLocalOffLineNodeConj (v : ℂ)
    (add_liLocalOffLineNodeConj_ne_zero v)
  exact ((analyticAt_const.mul h0).add hp).add hm

theorem iteratedDeriv_liLocalQuotientResponse (n : ℕ) {v : ℝ} (hv : -(1 / 2) < v) :
    iteratedDeriv n liLocalQuotientResponse v =
      (iteratedDeriv n liLocalQuotientComplexResponse (v : ℂ)).re := by
  exact iteratedDeriv_re_comp_ofReal_of_analyticAt
    (T := -(1 / 2)) (fun t ht => analyticAt_liLocalQuotientComplexResponse_of_gt ht) n hv

theorem alternating_iteratedDeriv_liLocalQuotientResponse_pos (m : ℕ) {v : ℝ}
    (hv : 0 ≤ v) :
    0 < (-1 : ℝ) ^ m * iteratedDeriv m liLocalQuotientResponse v := by
  rw [iteratedDeriv_liLocalQuotientResponse m (by linarith)]
  have hcomplex := signed_iteratedDeriv_liLocalQuotientComplexResponse m
    (v := v) (by linarith)
  have hpos := quotientSignedJetCounterexample_pos m hv
  rw [← hcomplex] at hpos
  have hsigncast : (-1 : ℂ) ^ m = (((-1 : ℝ) ^ m : ℝ) : ℂ) := by
    calc
      (-1 : ℂ) ^ m = (((-1 : ℝ) : ℂ)) ^ m := by norm_num
      _ = (((-1 : ℝ) ^ m : ℝ) : ℂ) := (Complex.ofReal_pow _ _).symm
  have hsignre : ((-1 : ℂ) ^ m).re = (-1 : ℝ) ^ m := by rw [hsigncast]; rfl
  have hsignim : ((-1 : ℂ) ^ m).im = 0 := by rw [hsigncast]; rfl
  simpa only [Complex.mul_re, hsignre, hsignim, zero_mul, sub_zero] using hpos

def StrictCompletelyMonotoneOnPositiveRay (f : ℝ → ℝ) : Prop :=
  ∀ m : ℕ, ∀ v : ℝ, 0 ≤ v → 0 < (-1 : ℝ) ^ m * iteratedDeriv m f v

theorem strictCompletelyMonotoneOnPositiveRay_liLocalQuotientResponse :
    StrictCompletelyMonotoneOnPositiveRay liLocalQuotientResponse := by
  intro m v hv
  exact alternating_iteratedDeriv_liLocalQuotientResponse_pos m hv

/-- The same finite symmetric packet has global strict complete monotonicity and a negative
completed-Abel mode. -/
theorem liLocalQuotient_counterexample_and_negative_fourthMode :
    StrictCompletelyMonotoneOnPositiveRay liLocalQuotientResponse ∧
      (liLocalCompletedAbelEndpointMode 3).re < 0 :=
  ⟨strictCompletelyMonotoneOnPositiveRay_liLocalQuotientResponse,
    liLocalCompletedAbelEndpointMode_three_re_neg⟩

def GlobalQuotientCompleteMonotonicityForcesEndpointModes : Prop :=
  StrictCompletelyMonotoneOnPositiveRay liLocalQuotientResponse →
    ∀ n : ℕ, 0 ≤ (liLocalCompletedAbelEndpointMode n).re

/-- **Global quotient-shape no-go.** Strict complete monotonicity on the whole positive ray
does not imply endpoint adjacent-mode nonnegativity. -/
theorem not_globalQuotientCompleteMonotonicityForcesEndpointModes :
    ¬ GlobalQuotientCompleteMonotonicityForcesEndpointModes := by
  intro h
  have hnonneg := h strictCompletelyMonotoneOnPositiveRay_liLocalQuotientResponse 3
  linarith [liLocalCompletedAbelEndpointMode_three_re_neg]

end

end RHTower

