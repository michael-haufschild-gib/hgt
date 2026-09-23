import GaloisForLFunctions.RHTower.SuzukiCheckpointEventDynamics

/-!
# Strict-convex checkpoint event geometry does not control absolute source sign

The literal Suzuki checkpoint criterion is RH-equivalent.  This file isolates the
source-independent convex/event package preceding that criterion and gives a universal
countermodel on every nondegenerate event cell.  Positive curvature fixes drawdown from the
checkpoint, but leaves its additive level free.
-/

noncomputable section

open Filter Set

namespace RHTower

/-- Midpoint of the universal SCE countermodel cell. -/
def sceCounterMidpoint (a b : ℝ) : ℝ := (a + b) / 2

/-- Positive depth assigned to the universal SCE countermodel. -/
def sceCounterDepth (a b w : ℝ) : ℝ := w * (b - a) / 4

/-- Positive quadratic coefficient of the universal SCE countermodel. -/
def sceCounterCurvature (a b w : ℝ) : ℝ := 2 * w / (b - a)

/-- Strictly convex source potential with positive endpoints and a negative checkpoint. -/
def sceCounterPotential (a b w : ℝ) (t : ℝ) : ℝ :=
  sceCounterCurvature a b w * (t - sceCounterMidpoint a b) ^ (2 : ℕ) -
    sceCounterDepth a b w

/-- Positive strictly convex reservoir whose affine event reduction is `sceCounterPotential`. -/
def sceCounterReservoir (a b w : ℝ) (t : ℝ) : ℝ :=
  sceCounterPotential a b w t + w * (t - a)

/-- Literal first moment in the universal SCE countermodel. -/
def sceCounterMoment (a w : ℝ) : ℝ := w * a

/-- Restricted Legendre event conjugate of a reservoir. -/
def sceRestrictedEventConjugate (a b w : ℝ) (R : ℝ → ℝ) : ℝ :=
  sSup ((fun t => w * t - R t) '' Icc a b)

/-- Exact source-independent structure advertised by the strict-convex checkpoint route. -/
def SCEConvexEventAxioms
    (a b w : ℝ) (R F : ℝ → ℝ) (v q : ℝ) : Prop :=
  StrictConvexOn ℝ (Icc a b) R ∧
  StrictConvexOn ℝ (Icc a b) F ∧
  (∀ t, 0 < R t) ∧
  v ∈ Ioo a b ∧
  HasDerivAt R w v ∧
  (∀ t, F t = R t - w * t + q) ∧
  0 < F a ∧
  0 < F b ∧
  (∀ u ∈ Icc a b, F v ≤ F u ∧ (F u = F v → u = v)) ∧
  (∀ u, F u - F v = R u - R v - w * (u - v)) ∧
  F b = F a + (R b - R a) - w * (b - a)

/-- Proposed source-independent SCE inference: convex/event geometry forces conjugate domination. -/
def SCEConvexEventSignPrinciple : Prop :=
  ∀ a b w R F v q,
    a < b → 0 < w → SCEConvexEventAxioms a b w R F v q →
      sceRestrictedEventConjugate a b w R ≤ q

private def sceCounterPotentialDeriv (a b w : ℝ) (t : ℝ) : ℝ :=
  2 * sceCounterCurvature a b w * (t - sceCounterMidpoint a b)

private def sceCounterReservoirDeriv (a b w : ℝ) (t : ℝ) : ℝ :=
  sceCounterPotentialDeriv a b w t + w

theorem sceCounterDepth_pos {a b w : ℝ} (hab : a < b) (hw : 0 < w) :
    0 < sceCounterDepth a b w := by
  unfold sceCounterDepth
  positivity

theorem sceCounterCurvature_pos {a b w : ℝ} (hab : a < b) (hw : 0 < w) :
    0 < sceCounterCurvature a b w := by
  unfold sceCounterCurvature
  positivity

theorem sceCounterMidpoint_mem_Ioo {a b : ℝ} (hab : a < b) :
    sceCounterMidpoint a b ∈ Ioo a b := by
  unfold sceCounterMidpoint
  constructor <;> linarith

theorem hasDerivAt_sceCounterPotential (a b w t : ℝ) :
    HasDerivAt (sceCounterPotential a b w) (sceCounterPotentialDeriv a b w t) t := by
  have hbase := ((hasDerivAt_id t).sub_const (sceCounterMidpoint a b)).pow 2
  have h := (hbase.const_mul (sceCounterCurvature a b w)).sub_const
    (sceCounterDepth a b w)
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at h
  change HasDerivAt
    (fun u => sceCounterCurvature a b w * (u - sceCounterMidpoint a b) ^ (2 : ℕ) -
      sceCounterDepth a b w)
    (2 * sceCounterCurvature a b w * (t - sceCounterMidpoint a b)) t
  exact h.congr_deriv (by ring)

private theorem hasDerivAt_sceCounterPotentialDeriv (a b w t : ℝ) :
    HasDerivAt (sceCounterPotentialDeriv a b w)
      (2 * sceCounterCurvature a b w) t := by
  have h := ((hasDerivAt_id t).sub_const (sceCounterMidpoint a b)).const_mul
    (2 * sceCounterCurvature a b w)
  simp only [id_eq, mul_one] at h
  change HasDerivAt
    (fun u => 2 * sceCounterCurvature a b w * (u - sceCounterMidpoint a b))
    (2 * sceCounterCurvature a b w) t
  exact h

theorem hasDerivAt_sceCounterReservoir (a b w t : ℝ) :
    HasDerivAt (sceCounterReservoir a b w) (sceCounterReservoirDeriv a b w t) t := by
  have hlin : HasDerivAt (fun u : ℝ => w * (u - a)) w t := by
    have h := ((hasDerivAt_id t).sub_const a).const_mul w
    simpa only [id_eq, mul_one] using h
  have h := (hasDerivAt_sceCounterPotential a b w t).add hlin
  change HasDerivAt
    (sceCounterPotential a b w + fun u => w * (u - a))
    (sceCounterPotentialDeriv a b w t + w) t
  exact h

private theorem hasDerivAt_sceCounterReservoirDeriv (a b w t : ℝ) :
    HasDerivAt (sceCounterReservoirDeriv a b w)
      (2 * sceCounterCurvature a b w) t := by
  have h := (hasDerivAt_sceCounterPotentialDeriv a b w t).add_const w
  exact h

theorem iteratedDeriv_two_sceCounterPotential (a b w t : ℝ) :
    iteratedDeriv 2 (sceCounterPotential a b w) t = 2 * sceCounterCurvature a b w := by
  have hderiv : deriv (sceCounterPotential a b w) = sceCounterPotentialDeriv a b w := by
    funext u
    exact (hasDerivAt_sceCounterPotential a b w u).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv,
    (hasDerivAt_sceCounterPotentialDeriv a b w t).deriv]

theorem iteratedDeriv_two_sceCounterReservoir (a b w t : ℝ) :
    iteratedDeriv 2 (sceCounterReservoir a b w) t = 2 * sceCounterCurvature a b w := by
  have hderiv : deriv (sceCounterReservoir a b w) = sceCounterReservoirDeriv a b w := by
    funext u
    exact (hasDerivAt_sceCounterReservoir a b w u).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv,
    (hasDerivAt_sceCounterReservoirDeriv a b w t).deriv]

theorem strictConvexOn_sceCounterPotential {a b w : ℝ} (hab : a < b) (hw : 0 < w) :
    StrictConvexOn ℝ (Icc a b) (sceCounterPotential a b w) := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc a b)
  · intro t _
    exact (hasDerivAt_sceCounterPotential a b w t).continuousAt.continuousWithinAt
  · intro t _
    rw [← iteratedDeriv_eq_iterate, iteratedDeriv_two_sceCounterPotential]
    exact mul_pos (by norm_num) (sceCounterCurvature_pos hab hw)

theorem strictConvexOn_sceCounterReservoir {a b w : ℝ} (hab : a < b) (hw : 0 < w) :
    StrictConvexOn ℝ (Icc a b) (sceCounterReservoir a b w) := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc a b)
  · intro t _
    exact (hasDerivAt_sceCounterReservoir a b w t).continuousAt.continuousWithinAt
  · intro t _
    rw [← iteratedDeriv_eq_iterate, iteratedDeriv_two_sceCounterReservoir]
    exact mul_pos (by norm_num) (sceCounterCurvature_pos hab hw)

theorem sceCounterPotential_sub_midpoint (a b w u : ℝ) :
    sceCounterPotential a b w u -
        sceCounterPotential a b w (sceCounterMidpoint a b) =
      sceCounterCurvature a b w * (u - sceCounterMidpoint a b) ^ (2 : ℕ) := by
  simp [sceCounterPotential]

theorem sceCounterPotential_midpoint {a b w : ℝ} :
    sceCounterPotential a b w (sceCounterMidpoint a b) = -sceCounterDepth a b w := by
  simp [sceCounterPotential]

theorem sceCounterPotential_leftEndpoint {a b w : ℝ} (hab : a < b) :
    sceCounterPotential a b w a = sceCounterDepth a b w := by
  have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  unfold sceCounterPotential sceCounterCurvature sceCounterMidpoint sceCounterDepth
  field_simp [hne]
  ring

theorem sceCounterPotential_rightEndpoint {a b w : ℝ} (hab : a < b) :
    sceCounterPotential a b w b = sceCounterDepth a b w := by
  have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  unfold sceCounterPotential sceCounterCurvature sceCounterMidpoint sceCounterDepth
  field_simp [hne]
  ring

theorem sceCounterReservoir_stationary {a b w : ℝ} :
    HasDerivAt (sceCounterReservoir a b w) w (sceCounterMidpoint a b) := by
  convert hasDerivAt_sceCounterReservoir a b w (sceCounterMidpoint a b) using 1
  simp [sceCounterReservoirDeriv, sceCounterPotentialDeriv]

theorem sceCounterReservoir_pos {a b w t : ℝ} (hab : a < b) (hw : 0 < w) :
    0 < sceCounterReservoir a b w t := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hk : 0 < sceCounterCurvature a b w := sceCounterCurvature_pos hab hw
  have hfloor : 0 < w * (b - a) / 8 := by positivity
  have hsquare : 0 ≤ sceCounterCurvature a b w *
      (t - (a + (b - a) / 4)) ^ (2 : ℕ) := mul_nonneg hk.le (sq_nonneg _)
  have hid : sceCounterReservoir a b w t =
      sceCounterCurvature a b w * (t - (a + (b - a) / 4)) ^ (2 : ℕ) +
        w * (b - a) / 8 := by
    have hne : b - a ≠ 0 := ne_of_gt hgap
    unfold sceCounterReservoir sceCounterPotential sceCounterCurvature
      sceCounterMidpoint sceCounterDepth
    field_simp [hne]
    ring
  rw [hid]
  exact add_pos_of_nonneg_of_pos hsquare hfloor

theorem sceCounterPotential_uniqueMin {a b w u : ℝ} (hab : a < b) (hw : 0 < w) :
    sceCounterPotential a b w (sceCounterMidpoint a b) ≤ sceCounterPotential a b w u ∧
      (sceCounterPotential a b w u = sceCounterPotential a b w (sceCounterMidpoint a b) →
        u = sceCounterMidpoint a b) := by
  have hk : 0 < sceCounterCurvature a b w := sceCounterCurvature_pos hab hw
  have hdiff := sceCounterPotential_sub_midpoint a b w u
  constructor
  · have hnonneg : 0 ≤ sceCounterCurvature a b w *
        (u - sceCounterMidpoint a b) ^ (2 : ℕ) := mul_nonneg hk.le (sq_nonneg _)
    linarith
  · intro heq
    have hzero : sceCounterCurvature a b w *
        (u - sceCounterMidpoint a b) ^ (2 : ℕ) = 0 := by linarith
    have hsq : (u - sceCounterMidpoint a b) ^ (2 : ℕ) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hk)
    nlinarith

theorem sceCounter_affineEventIdentity (a b w t : ℝ) :
    sceCounterPotential a b w t =
      sceCounterReservoir a b w t - w * t + sceCounterMoment a w := by
  simp [sceCounterReservoir, sceCounterMoment]
  ring

theorem sceCounter_bregmanDrawdown (a b w u : ℝ) :
    sceCounterPotential a b w u -
        sceCounterPotential a b w (sceCounterMidpoint a b) =
      sceCounterReservoir a b w u -
        sceCounterReservoir a b w (sceCounterMidpoint a b) -
          w * (u - sceCounterMidpoint a b) := by
  simp [sceCounterReservoir]
  ring

theorem sceCounter_endpointRecurrence (a b w : ℝ) :
    sceCounterPotential a b w b =
      sceCounterPotential a b w a +
        (sceCounterReservoir a b w b - sceCounterReservoir a b w a) - w * (b - a) := by
  simp [sceCounterReservoir]

/-- **Exact checkpoint classification.** An affine event identity and a minimizing checkpoint
identify the restricted conjugate exactly; convexity is needed only to produce/identify that
checkpoint. -/
theorem sceRestrictedEventConjugate_eq_moment_sub_checkpoint
    {a b w v q : ℝ} {R F : ℝ → ℝ}
    (hv : v ∈ Icc a b)
    (haffine : ∀ t, F t = R t - w * t + q)
    (hmin : ∀ u ∈ Icc a b, F v ≤ F u) :
    sceRestrictedEventConjugate a b w R = q - F v := by
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨v, hv, ?_⟩
    have hid := haffine v
    dsimp
    linarith
  · intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    have hle := hmin u hu
    have hid := haffine u
    dsimp
    linarith

/-- Under the full SCE convex/event package, conjugate excess is exactly negative checkpoint
height. This is the strongest positive survivor of the no-go. -/
theorem sceConvexEventAxioms_conjugate_sub_moment
    {a b w v q : ℝ} {R F : ℝ → ℝ}
    (h : SCEConvexEventAxioms a b w R F v q) :
    sceRestrictedEventConjugate a b w R - q = -F v := by
  rcases h with ⟨_, _, _, hv, _, haffine, _, _, hmin, _, _⟩
  have hv' : v ∈ Icc a b := ⟨le_of_lt hv.1, le_of_lt hv.2⟩
  rw [sceRestrictedEventConjugate_eq_moment_sub_checkpoint hv' haffine
    (fun u hu => (hmin u hu).1)]
  ring

/-- The desired conjugate domination contains exactly the missing absolute checkpoint sign. -/
theorem sceConvexEventAxioms_conjugate_le_moment_iff
    {a b w v q : ℝ} {R F : ℝ → ℝ}
    (h : SCEConvexEventAxioms a b w R F v q) :
    sceRestrictedEventConjugate a b w R ≤ q ↔ 0 ≤ F v := by
  rw [← sub_nonpos]
  rw [sceConvexEventAxioms_conjugate_sub_moment h]
  exact neg_nonpos

theorem sceRestrictedEventConjugate_sceCounterReservoir
    {a b w : ℝ} (hab : a < b) (hw : 0 < w) :
    sceRestrictedEventConjugate a b w (sceCounterReservoir a b w) =
      sceCounterMoment a w + sceCounterDepth a b w := by
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨sceCounterMidpoint a b, ?_, ?_⟩
    · have hv := sceCounterMidpoint_mem_Ioo hab
      exact ⟨le_of_lt hv.1, le_of_lt hv.2⟩
    · have hid := sceCounter_affineEventIdentity a b w (sceCounterMidpoint a b)
      rw [sceCounterPotential_midpoint] at hid
      dsimp
      linarith
  · intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    have hmin := (sceCounterPotential_uniqueMin (u := u) hab hw).1
    have hid := sceCounter_affineEventIdentity a b w u
    rw [sceCounterPotential_midpoint] at hmin
    dsimp
    linarith

theorem sceCounterAxioms {a b w : ℝ} (hab : a < b) (hw : 0 < w) :
    SCEConvexEventAxioms a b w
      (sceCounterReservoir a b w) (sceCounterPotential a b w)
      (sceCounterMidpoint a b) (sceCounterMoment a w) := by
  refine ⟨strictConvexOn_sceCounterReservoir hab hw,
    strictConvexOn_sceCounterPotential hab hw, ?_, sceCounterMidpoint_mem_Ioo hab,
    sceCounterReservoir_stationary, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact sceCounterReservoir_pos hab hw
  · exact sceCounter_affineEventIdentity a b w
  · rw [sceCounterPotential_leftEndpoint hab]
    exact sceCounterDepth_pos hab hw
  · rw [sceCounterPotential_rightEndpoint hab]
    exact sceCounterDepth_pos hab hw
  · intro u _
    exact sceCounterPotential_uniqueMin hab hw
  · exact sceCounter_bregmanDrawdown a b w
  · exact sceCounter_endpointRecurrence a b w

/-- **Universal SCE countermodel.** Every nondegenerate cell and positive event slope carries
the complete strict-convex checkpoint package, yet its restricted conjugate strictly exceeds
the moment. -/
theorem exists_sceConvexEventCounterexample :
    ∀ a b w, a < b → 0 < w →
      ∃ R F v q,
        SCEConvexEventAxioms a b w R F v q ∧
          F v < 0 ∧
          q < sceRestrictedEventConjugate a b w R := by
  intro a b w hab hw
  refine ⟨sceCounterReservoir a b w, sceCounterPotential a b w,
    sceCounterMidpoint a b, sceCounterMoment a w, sceCounterAxioms hab hw, ?_, ?_⟩
  · rw [sceCounterPotential_midpoint]
    exact neg_lt_zero.mpr (sceCounterDepth_pos hab hw)
  rw [sceRestrictedEventConjugate_sceCounterReservoir hab hw]
  exact lt_add_of_pos_right _ (sceCounterDepth_pos hab hw)

/-- **SCE route kill.** Strict convexity, positive reservoir, unique stationary checkpoint,
positive source endpoints, exact affine event identity, Bregman drawdown, and endpoint recurrence
do not imply the RH-equivalent conjugate--moment inequality. -/
theorem not_sceConvexEventSignPrinciple : ¬ SCEConvexEventSignPrinciple := by
  intro h
  have hbad := h 0 1 1
    (sceCounterReservoir 0 1 1) (sceCounterPotential 0 1 1)
    (sceCounterMidpoint 0 1) (sceCounterMoment 0 1)
    (by norm_num) (by norm_num) (sceCounterAxioms (by norm_num) (by norm_num))
  have hexcess : sceCounterMoment 0 1 <
      sceRestrictedEventConjugate 0 1 1 (sceCounterReservoir 0 1 1) := by
    rw [sceRestrictedEventConjugate_sceCounterReservoir (by norm_num) (by norm_num)]
    exact lt_add_of_pos_right _ (sceCounterDepth_pos (by norm_num) (by norm_num))
  exact (not_lt_of_ge hbad) hexcess

end RHTower
