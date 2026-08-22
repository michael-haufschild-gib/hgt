import GaloisForLFunctions.HTGeometry.BanachIntervalIntegralAbsoluteContinuity
import Mathlib.Tactic

/-!
# Transient antipodal conformal-channel forcing

This module formalizes the analytic core of Okten--Turan, arXiv:2608.19244v1, equations
`(90)`--`(103)`.  A Bochner absolutely-continuous path is represented by its initial value and an
interval-integrable velocity.  A centred antipodal mismatch is any continuous-linear image whose
projection factor is contractive and whose antipodal-composition factor has controlled norm.

The capstone is unconditional in Lean: every hypothesis is explicit mathematical data from the
paper, with no axiom, placeholder, or unproved derivative interface.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Bochner absolutely-continuous path with initial value `x0` and velocity `v`. -/
def bochnerIntervalPath (x0 : E) (v : ℝ → E) (a t : ℝ) : E :=
  x0 + ∫ s in a..t, v s

/-- Continuous-linear maps commute with Bochner interval paths. -/
theorem bochnerIntervalPath_map {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℝ] F) {x0 : E} {v : ℝ → E} {a t : ℝ}
    (hv : IntervalIntegrable v volume a t) :
    bochnerIntervalPath (L x0) (fun s => L (v s)) a t =
      L (bochnerIntervalPath x0 v a t) := by
  rw [bochnerIntervalPath, bochnerIntervalPath, L.intervalIntegral_comp_comm hv, map_add]

/-- Equation `(92)`, in pointwise form.  Every excursion from the initial endpoint and back toward
the final endpoint costs at least twice its size, after paying the two endpoint norms. -/
theorem bochnerIntervalPath_endpoint_excursion
    {x0 : E} {v : ℝ → E} {a b t : ℝ}
    (hab : a ≤ b) (ht : t ∈ Icc a b)
    (hv : IntervalIntegrable v volume a b) :
    2 * ‖bochnerIntervalPath x0 v a t‖ ≤
      ‖bochnerIntervalPath x0 v a a‖ + ‖bochnerIntervalPath x0 v a b‖ +
        ∫ s in a..b, ‖v s‖ := by
  have ha : a ∈ uIcc a b := by simp [hab]
  have hb : b ∈ uIcc a b := by simp [hab]
  have ht' : t ∈ uIcc a b := by simpa [uIcc_of_le hab] using ht
  have hv_at : IntervalIntegrable v volume a t :=
    hv.mono_set (uIcc_subset_uIcc ha ht')
  have hv_tb : IntervalIntegrable v volume t b :=
    hv.mono_set (uIcc_subset_uIcc ht' hb)
  have hleftDiff : bochnerIntervalPath x0 v a t - bochnerIntervalPath x0 v a a =
      ∫ s in a..t, v s := by
    simp [bochnerIntervalPath]
  have hrightDiff : bochnerIntervalPath x0 v a b - bochnerIntervalPath x0 v a t =
      ∫ s in t..b, v s := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hv_at hv_tb
    simp only [bochnerIntervalPath]
    rw [← hsplit]
    abel
  have hleft : ‖bochnerIntervalPath x0 v a t‖ ≤ ‖bochnerIntervalPath x0 v a a‖ +
      ∫ s in a..t, ‖v s‖ := by
    calc
      ‖bochnerIntervalPath x0 v a t‖
          ≤ ‖bochnerIntervalPath x0 v a a‖ +
              ‖bochnerIntervalPath x0 v a a - bochnerIntervalPath x0 v a t‖ :=
            norm_le_norm_add_norm_sub _ _
      _ = ‖bochnerIntervalPath x0 v a a‖ +
              ‖bochnerIntervalPath x0 v a t - bochnerIntervalPath x0 v a a‖ := by
            rw [norm_sub_rev]
      _ = ‖bochnerIntervalPath x0 v a a‖ + ‖∫ s in a..t, v s‖ := by rw [hleftDiff]
      _ ≤ ‖bochnerIntervalPath x0 v a a‖ + ∫ s in a..t, ‖v s‖ :=
            add_le_add_right (intervalIntegral.norm_integral_le_integral_norm ht.1) _
  have hright : ‖bochnerIntervalPath x0 v a t‖ ≤ ‖bochnerIntervalPath x0 v a b‖ +
      ∫ s in t..b, ‖v s‖ := by
    calc
      ‖bochnerIntervalPath x0 v a t‖
          ≤ ‖bochnerIntervalPath x0 v a b‖ +
              ‖bochnerIntervalPath x0 v a b - bochnerIntervalPath x0 v a t‖ :=
            norm_le_norm_add_norm_sub _ _
      _ = ‖bochnerIntervalPath x0 v a b‖ + ‖∫ s in t..b, v s‖ := by rw [hrightDiff]
      _ ≤ ‖bochnerIntervalPath x0 v a b‖ + ∫ s in t..b, ‖v s‖ :=
            add_le_add_right (intervalIntegral.norm_integral_le_integral_norm ht.2) _
  have hsplitNorm := intervalIntegral.integral_add_adjacent_intervals hv_at.norm hv_tb.norm
  linarith

/-- Abstract defect lower bound at one mismatch excursion.  This is the dependency-closed analytic
form of equations `(94)`--`(101)` before maximizing over time. -/
theorem transientDefect_lower_bound_at
    {q0 : E} {qdot kdot delta rem : ℝ → E} {a b t C Lambda epsilon : ℝ}
    (hab : a ≤ b) (ht : t ∈ Icc a b)
    (hC : 0 ≤ C) (hLambda : 0 < Lambda)
    (hqdot : IntervalIntegrable qdot volume a b)
    (hkdot : IntervalIntegrable kdot volume a b)
    (hdeltaInt : IntervalIntegrable delta volume a b)
    (hrem : IntervalIntegrable rem volume a b)
    (hqdotBound : ∀ᵐ u ∂volume.restrict (Icc a b), ‖qdot u‖ ≤ Lambda * ‖kdot u‖)
    (hstart : ‖bochnerIntervalPath q0 qdot a a‖ ≤ epsilon)
    (hend : ‖bochnerIntervalPath q0 qdot a b‖ ≤ epsilon)
    (hdelta : ∀ᵐ u ∂volume.restrict (Icc a b), delta u = C • kdot u + rem u) :
    ∫ u in a..b, ‖delta u‖ ≥
      C * (2 / Lambda) * (‖bochnerIntervalPath q0 qdot a t‖ - epsilon) -
        ∫ u in a..b, ‖rem u‖ := by
  have hexc := bochnerIntervalPath_endpoint_excursion (x0 := q0) hab ht hqdot
  have hqIntegral : (∫ u in a..b, ‖qdot u‖) ≤
      Lambda * ∫ u in a..b, ‖kdot u‖ := by
    have hmono := intervalIntegral.integral_mono_ae_restrict hab hqdot.norm
      (hkdot.norm.const_mul Lambda) hqdotBound
    simpa only [intervalIntegral.integral_const_mul] using hmono
  have hspeed : (2 / Lambda) * (‖bochnerIntervalPath q0 qdot a t‖ - epsilon) ≤
      ∫ u in a..b, ‖kdot u‖ := by
    have hraw : 2 * (‖bochnerIntervalPath q0 qdot a t‖ - epsilon) ≤
        Lambda * ∫ u in a..b, ‖kdot u‖ := by
      linarith
    have hdiv : (2 * (‖bochnerIntervalPath q0 qdot a t‖ - epsilon)) / Lambda ≤
        ∫ u in a..b, ‖kdot u‖ := (div_le_iff₀ hLambda).2 (by
          simpa only [mul_comm] using hraw)
    convert hdiv using 1
    ring
  have hfluxPoint : ∀ᵐ u ∂volume.restrict (Icc a b),
      C * ‖kdot u‖ ≤ ‖delta u‖ + ‖rem u‖ := by
    filter_upwards [hdelta] with u hu
    calc
      C * ‖kdot u‖ = ‖C • kdot u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
      _ = ‖delta u - rem u‖ := by rw [hu]; simp
      _ ≤ ‖delta u‖ + ‖rem u‖ := norm_sub_le _ _
  have hfluxIntegral : C * (∫ u in a..b, ‖kdot u‖) ≤
      (∫ u in a..b, ‖delta u‖) + ∫ u in a..b, ‖rem u‖ := by
    have hmono := intervalIntegral.integral_mono_ae_restrict hab
      (hkdot.norm.const_mul C) (hdeltaInt.norm.add hrem.norm) hfluxPoint
    simpa only [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hdeltaInt.norm hrem.norm] using hmono
  have hscaled := mul_le_mul_of_nonneg_left hspeed hC
  linarith

/-- Maximum squared norm attained by a Bochner interval path.  This is `Mmax` for the centred
antipodal mismatch path. -/
def bochnerPathMaxSq (x0 : E) (v : ℝ → E) (a b : ℝ) : ℝ :=
  sSup ((fun t => ‖bochnerIntervalPath x0 v a t‖ ^ 2) '' Icc a b)

theorem continuousOn_bochnerIntervalPath
    {x0 : E} {v : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hv : IntervalIntegrable v volume a b) :
    ContinuousOn (bochnerIntervalPath x0 v a) (Icc a b) := by
  have hac :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_normed
      hv (c := a) (by simp [hab])
  change ContinuousOn ((fun _ : ℝ => x0) + fun t => ∫ s in a..t, v s) (Icc a b)
  simpa only [uIcc_of_le hab] using continuousOn_const.add hac.continuousOn

/-- The squared mismatch maximum is attained on every nonempty compact time interval. -/
theorem exists_bochnerPathMaxSq
    {x0 : E} {v : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hv : IntervalIntegrable v volume a b) :
    ∃ t ∈ Icc a b, ‖bochnerIntervalPath x0 v a t‖ ^ 2 = bochnerPathMaxSq x0 v a b := by
  have hcont : ContinuousOn (fun t => ‖bochnerIntervalPath x0 v a t‖ ^ 2) (Icc a b) :=
    (continuousOn_bochnerIntervalPath hab hv).norm.pow 2
  have hne : (Icc a b).Nonempty := nonempty_Icc.mpr hab
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  refine ⟨t, ht, ?_⟩
  apply le_antisymm
  · apply le_csSup (isCompact_Icc.bddAbove_image hcont)
    exact ⟨t, ht, rfl⟩
  · apply csSup_le (hne.image _)
    rintro y ⟨u, hu, rfl⟩
    exact hmax hu

/-- Centred antipodal mismatch map `P (1 - T)`: `T` composes with the induced antipode and `P`
removes the constant spatial mode. -/
def centeredAntipodalMismatchMap (P T : E →L[ℝ] E) : E →L[ℝ] E :=
  P.comp (1 - T)

/-- Equation `(95)`: a contractive centring projection and an antipodal-composition norm bound
give the distortion factor `1 + alpha`. -/
theorem norm_centeredAntipodalMismatchMap_le
    {P T : E →L[ℝ] E} {alpha : ℝ}
    (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (hT : ∀ x, ‖T x‖ ≤ alpha * ‖x‖) (x : E) :
    ‖centeredAntipodalMismatchMap P T x‖ ≤ (1 + alpha) * ‖x‖ := by
  calc
    ‖centeredAntipodalMismatchMap P T x‖ = ‖P (x - T x)‖ := by
      simp [centeredAntipodalMismatchMap]
    _ ≤ ‖x - T x‖ := hP _
    _ ≤ ‖x‖ + ‖T x‖ := norm_sub_le _ _
    _ ≤ ‖x‖ + alpha * ‖x‖ := add_le_add_right (hT x) _
    _ = (1 + alpha) * ‖x‖ := by ring

/-- Okten--Turan robust transient antipodal conformal-channel bound, equations `(100)`--`(101)`.
Here `C = cCFT/(24*pi)` and `alpha = Jmin^(-1/2)` in the paper. -/
theorem oktenTuran_transientAntipodalDefect_lower_bound
    {P T : E →L[ℝ] E} {alpha : ℝ} {kappa0 : E}
    {kdot delta rem : ℝ → E} {a b C epsilon : ℝ}
    (hab : a ≤ b) (halpha : 0 ≤ alpha) (hepsilon : 0 ≤ epsilon) (hC : 0 ≤ C)
    (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (hT : ∀ x, ‖T x‖ ≤ alpha * ‖x‖)
    (hkdot : IntervalIntegrable kdot volume a b)
    (hdeltaInt : IntervalIntegrable delta volume a b)
    (hrem : IntervalIntegrable rem volume a b)
    (hstart : ‖bochnerIntervalPath (centeredAntipodalMismatchMap P T kappa0)
        (fun u => centeredAntipodalMismatchMap P T (kdot u)) a a‖ ^ 2 ≤ epsilon ^ 2)
    (hend : ‖bochnerIntervalPath (centeredAntipodalMismatchMap P T kappa0)
        (fun u => centeredAntipodalMismatchMap P T (kdot u)) a b‖ ^ 2 ≤ epsilon ^ 2)
    (hdelta : ∀ᵐ u ∂volume.restrict (Icc a b), delta u = C • kdot u + rem u) :
    ∫ u in a..b, ‖delta u‖ ≥
      C * (2 / (1 + alpha)) *
          (Real.sqrt (bochnerPathMaxSq (centeredAntipodalMismatchMap P T kappa0)
            (fun u => centeredAntipodalMismatchMap P T (kdot u)) a b) - epsilon) -
        ∫ u in a..b, ‖rem u‖ := by
  let Q := centeredAntipodalMismatchMap P T
  have hqdot : IntervalIntegrable (fun u => Q (kdot u)) volume a b := by
    exact ⟨Q.integrable_comp hkdot.1, Q.integrable_comp hkdot.2⟩
  obtain ⟨t, ht, htmax⟩ := exists_bochnerPathMaxSq hab hqdot
  have hstartNorm : ‖bochnerIntervalPath (Q kappa0) (fun u => Q (kdot u)) a a‖ ≤ epsilon :=
    (sq_le_sq₀ (norm_nonneg _) hepsilon).mp hstart
  have hendNorm : ‖bochnerIntervalPath (Q kappa0) (fun u => Q (kdot u)) a b‖ ≤ epsilon :=
    (sq_le_sq₀ (norm_nonneg _) hepsilon).mp hend
  have hbound := transientDefect_lower_bound_at
    (q0 := Q kappa0) (qdot := fun u => Q (kdot u)) (kdot := kdot)
    (delta := delta) (rem := rem) (t := t) (C := C) (Lambda := 1 + alpha)
    (epsilon := epsilon) hab ht hC (by linarith) hqdot hkdot hdeltaInt hrem
    (Filter.Eventually.of_forall fun u => norm_centeredAntipodalMismatchMap_le hP hT (kdot u))
    hstartNorm hendNorm hdelta
  have hsqrt : Real.sqrt (bochnerPathMaxSq (Q kappa0) (fun u => Q (kdot u)) a b) =
      ‖bochnerIntervalPath (Q kappa0) (fun u => Q (kdot u)) a t‖ := by
    rw [← htmax, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simpa only [Q, hsqrt] using hbound

/-- Okten--Turan exact-restoration specialization, equations `(90)` and `(99)`. -/
theorem oktenTuran_transientAntipodalDefect_lower_bound_exact
    {P T : E →L[ℝ] E} {alpha : ℝ} {kappa0 : E}
    {kdot delta rem : ℝ → E} {a b C : ℝ}
    (hab : a ≤ b) (halpha : 0 ≤ alpha) (hC : 0 ≤ C)
    (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (hT : ∀ x, ‖T x‖ ≤ alpha * ‖x‖)
    (hkdot : IntervalIntegrable kdot volume a b)
    (hdeltaInt : IntervalIntegrable delta volume a b)
    (hrem : IntervalIntegrable rem volume a b)
    (hstart : bochnerIntervalPath (centeredAntipodalMismatchMap P T kappa0)
        (fun u => centeredAntipodalMismatchMap P T (kdot u)) a a = 0)
    (hend : bochnerIntervalPath (centeredAntipodalMismatchMap P T kappa0)
        (fun u => centeredAntipodalMismatchMap P T (kdot u)) a b = 0)
    (hdelta : ∀ᵐ u ∂volume.restrict (Icc a b), delta u = C • kdot u + rem u) :
    ∫ u in a..b, ‖delta u‖ ≥
      C * (2 / (1 + alpha)) *
          Real.sqrt (bochnerPathMaxSq (centeredAntipodalMismatchMap P T kappa0)
            (fun u => centeredAntipodalMismatchMap P T (kdot u)) a b) -
        ∫ u in a..b, ‖rem u‖ := by
  simpa [hstart, hend] using
    (oktenTuran_transientAntipodalDefect_lower_bound
      (P := P) (T := T) (alpha := alpha) (kappa0 := kappa0)
      (kdot := kdot) (delta := delta) (rem := rem) (a := a) (b := b)
      (C := C) (epsilon := 0) hab halpha (by positivity) hC hP hT hkdot hdeltaInt hrem
      (by simp [hstart]) (by simp [hend]) hdelta)

/-- Equation `(102)`: conformal forcing scale. -/
def conformalForcingScale (C alpha maxSq : ℝ) : ℝ :=
  C * (2 / (1 + alpha)) * Real.sqrt maxSq

/-- Equation `(104)`: dimensionless remainder fraction, defined only for use when the forcing
scale is positive. -/
def conformalRemainderRatio (remainderBudget forcingScale : ℝ) : ℝ :=
  remainderBudget / forcingScale

/-- Positivity threshold following equation `(101)`.  This is the paper's displayed threshold
with `C = cCFT / (24 * pi)`, `peak = sqrt Mmax`, and `alpha = Jmin^(-1/2)`. -/
theorem transientDefect_pos_of_peak_gt_threshold
    {integratedDefect C alpha peak epsilon remainderBudget : ℝ}
    (hC : 0 < C) (halpha : 0 ≤ alpha)
    (hbound : C * (2 / (1 + alpha)) * (peak - epsilon) - remainderBudget ≤
      integratedDefect)
    (hpeak : epsilon + (1 + alpha) / (2 * C) * remainderBudget < peak) :
    0 < integratedDefect := by
  have hden : 0 < 2 * C := by positivity
  have honepos : 0 < 1 + alpha := by linarith
  have hscale : remainderBudget < C * (2 / (1 + alpha)) * (peak - epsilon) := by
    have hraw : (1 + alpha) / (2 * C) * remainderBudget < peak - epsilon := by linarith
    have hraw' : (1 + alpha) * remainderBudget < (2 * C) * (peak - epsilon) := by
      have hrawDiv : ((1 + alpha) * remainderBudget) / (2 * C) < peak - epsilon := by
        convert hraw using 1
        ring
      have := (div_lt_iff₀ hden).mp hrawDiv
      nlinarith
    calc
      remainderBudget < (2 * C) * (peak - epsilon) / (1 + alpha) :=
        (lt_div_iff₀ honepos).2 (by nlinarith [hraw'])
      _ = C * (2 / (1 + alpha)) * (peak - epsilon) := by field_simp
  linarith

/-- Equation `(108)`: time- and area-normalized form of the exact integrated bound.  The
area-normalized scale is `sqrt Mmax / sqrt area`; substituting `alpha = Jmin^(-1/2)` gives the
displayed geometric formula. -/
theorem oktenTuran_timeAveraged_lower_bound
    {integratedDefect remainderBudget cCFT alpha maxSq duration area : ℝ}
    (halpha : 0 ≤ alpha) (hduration : 0 < duration) (harea : 0 < area)
    (hbound : cCFT / (24 * Real.pi) * (2 / (1 + alpha)) * Real.sqrt maxSq ≤
      integratedDefect + remainderBudget) :
    cCFT / (12 * Real.pi * duration * (1 + alpha)) *
        (Real.sqrt maxSq / Real.sqrt area) ≤
      (integratedDefect / duration + remainderBudget / duration) / Real.sqrt area := by
  have hsqrt : 0 < Real.sqrt area := Real.sqrt_pos.2 harea
  have hden : 0 < duration * Real.sqrt area := mul_pos hduration hsqrt
  have hone : 1 + alpha ≠ 0 := by linarith
  have hdiv := (div_le_div_iff_of_pos_right hden).2 hbound
  calc
    cCFT / (12 * Real.pi * duration * (1 + alpha)) *
          (Real.sqrt maxSq / Real.sqrt area) =
        (cCFT / (24 * Real.pi) * (2 / (1 + alpha)) * Real.sqrt maxSq) /
          (duration * Real.sqrt area) := by
      field_simp [Real.pi_ne_zero, hduration.ne', hsqrt.ne', hone]
      ring
    _ ≤ (integratedDefect + remainderBudget) / (duration * Real.sqrt area) := hdiv
    _ = (integratedDefect / duration + remainderBudget / duration) / Real.sqrt area := by
      field_simp [hduration.ne', hsqrt.ne']

/-- Equation `(103)` implies strict positivity when the remainder budget is smaller than the
conformal forcing scale. -/
theorem integratedDefect_pos_of_remainder_lt_forcing
    {integratedDefect forcingScale remainderBudget : ℝ}
    (hbound : integratedDefect ≥ forcingScale - remainderBudget)
    (hrem : remainderBudget < forcingScale) : 0 < integratedDefect := by
  linarith

end

end GaloisForLFunctions.HTGeometry
