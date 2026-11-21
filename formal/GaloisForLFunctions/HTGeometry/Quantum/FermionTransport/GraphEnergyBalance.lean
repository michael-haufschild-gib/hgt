import GaloisForLFunctions.HTGeometry.Quantum.FermionTransport.GraphDissipationOnset
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Free-energy balance for closed-box Fermi–Dirac transport

At positive time an empty or full component carries no current. Replacing
such components by a Gibbs profile preserves the currents and dissipation.
The logarithmic onset is integrable, giving the exact free-energy balance
from time zero even when occupations start on the boundary.
-/

open Set Filter MeasureTheory
open scoped BigOperators Topology Interval

namespace GaloisForLFunctions.HTGeometry.Quantum.FermiGraph

noncomputable section

variable {V : Type*} {G : WeightedGraph V} {E : V → ℝ}

private def boxOutwardCurrent (G : WeightedGraph V) (E f : V → ℝ) (v u : V) : ℝ :=
  G.w v u * (Real.exp (E v) * f v * (1 - f u) - Real.exp (E u) * f u * (1 - f v))

private def filledOccupation (E f : V → ℝ) (v : V) : Occupation :=
  if h : f v ∈ Ioo (0 : ℝ) 1 then ⟨f v, h⟩ else gibbsOccupation (E v) 0

private theorem boundary_is_endpoint {f : V → ℝ} (hf : ∀ v, f v ∈ Icc (0 : ℝ) 1)
    {v : V} (hv : f v ∉ Ioo (0 : ℝ) 1) : f v = 0 ∨ f v = 1 := by
  by_contra! he
  exact hv ⟨lt_of_le_of_ne (hf v).1 (Ne.symm he.1), lt_of_le_of_ne (hf v).2 he.2⟩

private theorem same_on_boundary_edge {f : V → ℝ} (hf : ∀ v, f v ∈ Icc (0 : ℝ) 1)
    (hno : ¬ HasActiveBoundaryEdge G f) {v u : V} (hw : 0 < G.w v u)
    (hv : f v ∉ Ioo (0 : ℝ) 1) : f u = f v := by
  rcases boundary_is_endpoint hf hv with h₀ | h₁
  · rw [h₀]
    exact le_antisymm (le_of_not_gt fun hu => hno ⟨v, u, hw, Or.inl ⟨h₀, hu⟩⟩) (hf u).1
  · rw [h₁]
    exact le_antisymm (hf u).2 (le_of_not_gt fun hu => hno ⟨v, u, hw, Or.inr ⟨h₁, hu⟩⟩)

private theorem boxOutwardCurrent_eq_zero_of_boundary {f : V → ℝ}
    (hf : ∀ v, f v ∈ Icc (0 : ℝ) 1) (hno : ¬ HasActiveBoundaryEdge G f) {v : V}
    (hv : f v ∉ Ioo (0 : ℝ) 1) (u : V) : boxOutwardCurrent G E f v u = 0 := by
  rcases (G.w_nonneg v u).eq_or_lt with hw | hw
  · simp only [boxOutwardCurrent, ← hw, zero_mul]
  · rw [boxOutwardCurrent, same_on_boundary_edge hf hno hw hv]
    rcases boundary_is_endpoint hf hv with h₀ | h₁
    · simp only [h₀, mul_zero, zero_mul, sub_self]
    · simp only [h₁, sub_self, mul_zero]

private theorem flux_filled_eq_boxOutwardCurrent {f : V → ℝ}
    (hf : ∀ v, f v ∈ Icc (0 : ℝ) 1) (hno : ¬ HasActiveBoundaryEdge G f) (v u : V) :
    flux G E (filledOccupation E f) v u = boxOutwardCurrent G E f v u := by
  rcases (G.w_nonneg v u).eq_or_lt with hw | hw
  · simp only [flux, boxOutwardCurrent, ← hw, zero_mul]
  · by_cases hv : f v ∈ Ioo (0 : ℝ) 1
    · have hwu : 0 < G.w u v := (G.w_symm v u) ▸ hw
      have hu : f u ∈ Ioo (0 : ℝ) 1 := by
        by_contra hu
        exact hu ((same_on_boundary_edge hf hno hwu hu) ▸ hv)
      rw [flux_eq_particle_hole]
      simp only [filledOccupation, dif_pos hv, dif_pos hu, boxOutwardCurrent]
    · have hu : f u ∉ Ioo (0 : ℝ) 1 := by
        rw [same_on_boundary_edge hf hno hw hv]
        exact hv
      have hμ (k : V) (hk : f k ∉ Ioo (0 : ℝ) 1) :
          chemicalPotential E (filledOccupation E f) k = 0 := by
        simpa only [chemicalPotential, filledOccupation, dif_neg hk] using chemicalPotential_gibbs E 0 k
      rw [boxOutwardCurrent_eq_zero_of_boundary hf hno hv, flux, hμ v hv, hμ u hu, sub_self, mul_zero]

variable [Fintype V]

private theorem clippedDrift_eq_neg_sum_boxOutwardCurrent {f : V → ℝ}
    (hf : ∀ v, f v ∈ Icc (0 : ℝ) 1) (v : V) :
    clippedDrift G E f v = -∑ u, boxOutwardCurrent G E f v u := by
  rw [clippedDrift_eq_of_box G E f hf, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun u _ => by unfold boxOutwardCurrent; ring

/-- Replacing every saturated component by a Gibbs profile leaves all
currents unchanged and realizes the closed-box dissipation in the interior. -/
theorem exists_interior_with_same_drift_and_dissipation {f : V → ℝ}
    (hf : ∀ v, f v ∈ Icc (0 : ℝ) 1) (hno : ¬ HasActiveBoundaryEdge G f) :
    ∃ p : V → Occupation, clippedDrift G E f = drift G E p ∧
      boxDissipation G E f = dissipation G E p := by
  let p := filledOccupation E f
  have hd : clippedDrift G E f = drift G E p := by
    funext v
    rw [clippedDrift_eq_neg_sum_boxOutwardCurrent hf v, drift]
    simp only [p, flux_filled_eq_boxOutwardCurrent hf hno]
  refine ⟨p, hd, ?_⟩
  have hprod (v : V) : (E v + Real.log (f v) - Real.log (1 - f v)) * clippedDrift G E f v =
      chemicalPotential E p v * drift G E p v := by
    by_cases hv : f v ∈ Ioo (0 : ℝ) 1
    · have hμ : chemicalPotential E p v = E v + Real.log (f v) - Real.log (1 - f v) := by
        simp only [p, chemicalPotential, filledOccupation, dif_pos hv]
        rw [Real.log_div hv.1.ne' (sub_pos.mpr hv.2).ne']
        ring
      rw [hd, hμ]
    · have hz : clippedDrift G E f v = 0 := by
        rw [clippedDrift_eq_neg_sum_boxOutwardCurrent hf v]
        simp only [boxOutwardCurrent_eq_zero_of_boundary hf hno hv, Finset.sum_const_zero, neg_zero]
      rw [← hd, hz, mul_zero, mul_zero]
  unfold boxDissipation
  simp_rw [hprod]
  rw [sum_chemicalPotential_mul_drift, neg_neg]

/-- Without an active boundary edge, dissipation is nonnegative. -/
theorem boxDissipation_nonneg_of_no_active_edge {f : V → ℝ}
    (hf : ∀ v, f v ∈ Icc (0 : ℝ) 1) (hno : ¬ HasActiveBoundaryEdge G f) :
    0 ≤ boxDissipation G E f := by
  obtain ⟨p, _, hD⟩ := exists_interior_with_same_drift_and_dissipation (E := E) hf hno
  rw [hD]
  exact dissipation_nonneg G E p

/-- For an inactive boundary, zero dissipation characterizes a stationary
field. Saturated components already have zero drift. -/
theorem boxDissipation_eq_zero_iff_drift_of_no_active_edge {f : V → ℝ}
    (hf : ∀ v, f v ∈ Icc (0 : ℝ) 1) (hno : ¬ HasActiveBoundaryEdge G f) :
    boxDissipation G E f = 0 ↔ ∀ v, clippedDrift G E f v = 0 := by
  obtain ⟨p, hd, hD⟩ := exists_interior_with_same_drift_and_dissipation (E := E) hf hno
  rw [hD, hd, dissipation_eq_zero_iff, ← drift_eq_zero_iff]

/-- Stationarity on the closed box requires an inactive boundary as
well as zero dissipation. An active boundary forces an inward current. -/
theorem clippedDrift_eq_zero_iff_inactive_and_zero_dissipation {f : V → ℝ}
    (hf : ∀ v, f v ∈ Icc (0 : ℝ) 1) :
    (∀ v, clippedDrift G E f v = 0) ↔ ¬ HasActiveBoundaryEdge G f ∧ boxDissipation G E f = 0 := by
  constructor
  · intro hd
    have hno : ¬ HasActiveBoundaryEdge G f := by
      intro ha
      have hp := (boundaryEntropyCoefficient_pos_iff G E f hf).mpr ha
      have hz (v : V) : boundaryEntropyRate G E f v = 0 := by
        simp only [boundaryEntropyRate, hd, neg_zero, ite_self]
      simp only [boundaryEntropyCoefficient, hz, Finset.sum_const_zero, lt_irrefl] at hp
    exact ⟨hno, (boxDissipation_eq_zero_iff_drift_of_no_active_edge hf hno).mpr hd⟩
  · rintro ⟨hno, hD⟩
    exact (boxDissipation_eq_zero_iff_drift_of_no_active_edge hf hno).mp hD

variable {x : ℝ → V → ℝ}

/-- At positive time every saturated vertex belongs to a saturated
component. A positive edge could otherwise propagate a particle or vacancy. -/
theorem IsBoxOccupationFlow.no_active_boundary_edge_pos (h : IsBoxOccupationFlow G E x)
    {t : ℝ} (ht : 0 < t) : ¬ HasActiveBoundaryEdge G (x t) := by
  rintro ⟨v, u, hw, hactive⟩
  have hw' : 0 < G.w u v := (G.w_symm v u) ▸ hw
  rcases hactive with ⟨hv, hu⟩ | ⟨hv, hu⟩
  · obtain ⟨k, hk, hpos⟩ := (h.pos_iff_initial_particle u ht).mp hu
    have hs := h.pos_of_path hpos (hk.trans (.single hw')) t ht
    exact hs.ne' hv
  · obtain ⟨k, hk, hpos⟩ := (h.vacancy_pos_iff_initial_vacancy u ht).mp (sub_pos.mpr hu)
    have hs := h.vacancy_pos_of_path hpos (hk.trans (.single hw')) t ht
    exact hs.ne' (by rw [hv, sub_self])

/-- Every forward solution has nonnegative dissipation at positive time. -/
theorem IsBoxOccupationFlow.boxDissipation_nonneg_pos (h : IsBoxOccupationFlow G E x)
    {t : ℝ} (ht : 0 < t) : 0 ≤ boxDissipation G E (x t) :=
  boxDissipation_nonneg_of_no_active_edge (h.in_box t ht.le) (h.no_active_boundary_edge_pos ht)

/-- Dissipation vanishes at a positive time exactly when every site has
zero velocity at that time. -/
theorem IsBoxOccupationFlow.boxDissipation_eq_zero_iff_drift_pos (h : IsBoxOccupationFlow G E x)
    {t : ℝ} (ht : 0 < t) : boxDissipation G E (x t) = 0 ↔ ∀ v, clippedDrift G E (x t) v = 0 :=
  boxDissipation_eq_zero_iff_drift_of_no_active_edge (h.in_box t ht.le) (h.no_active_boundary_edge_pos ht)

private theorem continuousOn_log_of_fixed_support {p : ℝ → ℝ}
    (hc : ContinuousOn p (Ioi 0)) (hn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ p t)
    (hsupport : ∀ s ∈ Ioi (0 : ℝ), ∀ t ∈ Ioi (0 : ℝ), 0 < p s ↔ 0 < p t) :
    ContinuousOn (fun t => Real.log (p t)) (Ioi 0) := by
  intro t ht
  by_cases hz : p t = 0
  · change Tendsto (fun s => Real.log (p s)) (𝓝[Ioi 0] t) (𝓝 (Real.log (p t)))
    rw [hz, Real.log_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hzero : p s = 0 := (le_of_not_gt fun hp =>
      (hsupport s hs t ht).mp hp |>.ne' hz).antisymm (hn s hs)
    rw [hzero, Real.log_zero]
  · exact (Real.continuousAt_log hz).tendsto.comp (hc t ht)

private theorem IsBoxOccupationFlow.continuousOn_coordinate (h : IsBoxOccupationFlow G E x) (v : V) :
    ContinuousOn (fun t => x t v) (Ici 0) :=
  fun t ht => (h.hasDerivAt_coordinate t ht v).continuousAt.continuousWithinAt

/-- Saturated components stay constant, so their logarithms cause
no discontinuity at positive times. -/
theorem IsBoxOccupationFlow.continuousOn_boxDissipation (h : IsBoxOccupationFlow G E x) :
    ContinuousOn (fun t => boxDissipation G E (x t)) (Ioi 0) := by
  have hx (v : V) : ContinuousOn (fun t => x t v) (Ioi 0) :=
    (h.continuousOn_coordinate v).mono fun _ ht => (mem_Ioi.mp ht).le
  unfold boxDissipation
  apply ContinuousOn.neg
  apply continuousOn_finsetSum
  intro v _
  have hp : ContinuousOn (fun t => Real.log (x t v)) (Ioi 0) :=
    continuousOn_log_of_fixed_support (hx v) (fun t ht => (h.in_box t (mem_Ioi.mp ht).le v).1)
      (fun _ hs _ ht => (h.pos_iff_initial_particle v hs).trans (h.pos_iff_initial_particle v ht).symm)
  have hq : ContinuousOn (fun t => Real.log (1 - x t v)) (Ioi 0) :=
    continuousOn_log_of_fixed_support (continuousOn_const.sub (hx v))
      (fun t ht => sub_nonneg.mpr (h.in_box t (mem_Ioi.mp ht).le v).2)
      (fun _ hs _ ht => (h.vacancy_pos_iff_initial_vacancy v hs).trans
        (h.vacancy_pos_iff_initial_vacancy v ht).symm)
  have hd : ContinuousOn (fun t => clippedDrift G E (x t) v) (Ioi 0) := by
    let P (t : ℝ) := ∑ u, (G.w v u * Real.exp (E u) * (x t u * (1 - x t v)) -
      G.w v u * Real.exp (E v) * (x t v * (1 - x t u)))
    have hP : ContinuousOn P (Ioi 0) := by
      unfold P
      apply continuousOn_finsetSum
      intro u _
      fun_prop
    exact hP.congr fun t ht => clippedDrift_eq_of_box G E (x t) (h.in_box t (mem_Ioi.mp ht).le) v
  exact ((continuousOn_const.add hp).sub hq).mul hd

/-- Free energy is continuous up to the initial state. -/
theorem IsBoxOccupationFlow.continuousOn_freeEnergy (h : IsBoxOccupationFlow G E x) :
    ContinuousOn (fun t => freeEnergy E (x t)) (Ici 0) := by
  unfold freeEnergy
  apply continuousOn_finsetSum
  intro v _
  exact (continuousOn_const.mul (h.continuousOn_coordinate v)).sub
    (Real.binEntropy_continuous.comp_continuousOn (h.continuousOn_coordinate v))

/-- The logarithmic singularity at the initial boundary is integrable. -/
theorem IsBoxOccupationFlow.intervalIntegrable_boxDissipation (h : IsBoxOccupationFlow G E x)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => boxDissipation G E (x t)) volume a b := by
  let C := boundaryEntropyCoefficient G E (x 0)
  let D (t : ℝ) := boxDissipation G E (x t)
  let R (t : ℝ) := if t = 0 then boundaryDissipationFinitePart G E (x 0) else D t - C * -Real.log t
  have hlog : ContinuousOn Real.log (Ioi (0 : ℝ)) := fun _ ht =>
    (Real.continuousAt_log (mem_Ioi.mp ht).ne').continuousWithinAt
  have hC : ContinuousOn (fun _ : ℝ => C) (Ioi 0) := continuousOn_const
  have hRpos : ContinuousOn R (Ioi 0) := by
    refine (h.continuousOn_boxDissipation.sub (hC.mul hlog.neg)).congr ?_
    intro t ht
    exact if_neg (mem_Ioi.mp ht).ne'
  have hR : ContinuousOn R (Ici 0) := by
    intro t ht
    rcases (show 0 ≤ t from ht).eq_or_lt with h₀ | hpos
    · subst t
      rw [← Ioi_insert, continuousWithinAt_insert_self]
      change Tendsto R (𝓝[>] 0) (𝓝 (R 0))
      simp only [R, if_pos rfl]
      refine h.tendsto_boxDissipation_finite_part.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (if_neg (mem_Ioi.mp hs).ne').symm
    · exact ((hRpos t hpos).continuousAt (Ioi_mem_nhds hpos)).continuousWithinAt
  have hRc : ContinuousOn R (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact hR.mono fun _ ht => ha.trans ht.1
  have hI : IntervalIntegrable (fun t => R t + C * -Real.log t) volume a b :=
    hRc.intervalIntegrable.add (intervalIntegral.intervalIntegrable_log'.neg.const_mul C)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hI ⊢
  refine hI.congr_fun (fun t ht => ?_) measurableSet_Ioc
  change R t + C * -Real.log t = D t
  have he : R t = D t - C * -Real.log t := if_neg (ha.trans_lt ht.1).ne'
  rw [he, sub_add_cancel]

/-- Finite-graph free-energy balance holds on every forward interval,
including an interval starting at a fully saturated field. -/
theorem IsBoxOccupationFlow.integral_boxDissipation_eq_freeEnergy_sub (h : IsBoxOccupationFlow G E x)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, boxDissipation G E (x t)) = freeEnergy E (x a) - freeEnergy E (x b) := by
  have hc : ContinuousOn (fun t => -freeEnergy E (x t)) (Icc a b) :=
    h.continuousOn_freeEnergy.neg.mono fun _ ht => ha.trans ht.1
  have hd (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun s => -freeEnergy E (x s)) (boxDissipation G E (x t)) t := by
    simpa only [neg_neg] using (h.hasDerivAt_freeEnergy_pos (ha.trans_lt ht.1)).fun_neg
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc hd
    (h.intervalIntegrable_boxDissipation ha hab)
  change (∫ t in a..b, boxDissipation G E (x t)) = -freeEnergy E (x b) - -freeEnergy E (x a) at hi
  rwa [neg_sub_neg] at hi

/-- Free energy is nonincreasing along the whole forward flow. -/
theorem IsBoxOccupationFlow.antitoneOn_freeEnergy (h : IsBoxOccupationFlow G E x) :
    AntitoneOn (fun t => freeEnergy E (x t)) (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) h.continuousOn_freeEnergy
  · rw [interior_Ici]
    exact fun _ ht => (h.hasDerivAt_freeEnergy_pos ht).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro t ht
    rw [(h.hasDerivAt_freeEnergy_pos ht).deriv]
    exact neg_nonpos.mpr (h.boxDissipation_nonneg_pos ht)

/-- Equality of endpoint energies forces the full occupation field
to be constant throughout the interval. -/
theorem IsBoxOccupationFlow.freeEnergy_eq_iff_eqOn (h : IsBoxOccupationFlow G E x)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    freeEnergy E (x b) = freeEnergy E (x a) ↔ EqOn x (fun _ => x a) (Icc a b) := by
  constructor
  · intro hF
    have hE : EqOn (fun t => freeEnergy E (x t)) (fun _ => freeEnergy E (x a)) (Icc a b) := by
      intro t ht
      have ht₀ := ha.trans ht.1
      have hl : freeEnergy E (x b) ≤ freeEnergy E (x t) :=
        h.antitoneOn_freeEnergy ht₀ (ha.trans hab) ht.2
      rw [hF] at hl
      exact (h.antitoneOn_freeEnergy ha ht₀ ht.1).antisymm hl
    have hd (t : ℝ) (ht : t ∈ Ioo a b) : ∀ v, clippedDrift G E (x t) v = 0 := by
      have he : (fun _ => freeEnergy E (x a)) =ᶠ[𝓝 t] fun s => freeEnergy E (x s) := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        exact (hE ⟨hs.1.le, hs.2.le⟩).symm
      have hc := (hasDerivAt_const t (freeEnergy E (x a))).congr_of_eventuallyEq he.symm
      have hp := ha.trans_lt ht.1
      have hz : -boxDissipation G E (x t) = 0 :=
        (h.hasDerivAt_freeEnergy_pos hp).deriv.symm.trans hc.deriv
      exact (h.boxDissipation_eq_zero_iff_drift_pos hp).mp (neg_eq_zero.mp hz)
    intro t ht
    change x t = x a
    rcases ht.1.eq_or_lt with he | hlt
    · rw [he]
    · funext v
      have hc : ContinuousOn (fun s => x s v) (Icc a t) :=
        (h.continuousOn_coordinate v).mono fun _ hs => ha.trans hs.1
      obtain ⟨s, hs, hmean⟩ := exists_hasDerivAt_eq_slope (fun r => x r v) (fun _ => 0) hlt hc
        (fun r hr => by
          have hh := h.hasDerivAt_coordinate r (ha.trans hr.1.le) v
          rwa [hd r ⟨hr.1, hr.2.trans_le ht.2⟩ v] at hh)
      exact sub_eq_zero.mp ((div_eq_zero_iff.mp hmean.symm).resolve_right (sub_pos.mpr hlt).ne')
  · intro he
    exact congrArg (freeEnergy E) (he ⟨hab, le_rfl⟩)

/-- A nonstationary initial field strictly loses free energy by every
positive time. A stationary initial field generates the constant flow. -/
theorem IsBoxOccupationFlow.freeEnergy_eq_initial_iff_drift_zero (h : IsBoxOccupationFlow G E x)
    {b : ℝ} (hb : 0 < b) :
    freeEnergy E (x b) = freeEnergy E (x 0) ↔ ∀ v, clippedDrift G E (x 0) v = 0 := by
  constructor
  · intro hF v
    have he := (h.freeEnergy_eq_iff_eqOn le_rfl hb.le).mp hF
    have hl : 0 < b / 2 := half_pos hb
    have hr : b / 2 < b := half_lt_self hb
    have hev : (fun t => x t v) =ᶠ[𝓝 (b / 2)] fun _ => x 0 v := by
      filter_upwards [Ioo_mem_nhds hl hr] with t ht
      exact congrFun (he ⟨ht.1.le, ht.2.le⟩) v
    have hc := (hasDerivAt_const (b / 2) (x 0 v)).congr_of_eventuallyEq hev
    have hd := h.hasDerivAt_coordinate (b / 2) hl.le v
    rw [show x (b / 2) = x 0 from he ⟨hl.le, hr.le⟩] at hd
    exact hd.deriv.symm.trans hc.deriv
  · intro hd
    have hc : IsBoxOccupationFlow G E (fun _ : ℝ => x 0) := by
      refine ⟨fun _ _ => h.in_box 0 le_rfl, fun t _ => ?_⟩
      have hz : clippedDrift G E (x 0) = 0 := funext hd
      change HasDerivAt (fun _ : ℝ => x 0) (clippedDrift G E (x 0)) t
      rw [hz]
      exact hasDerivAt_const t (x 0)
    exact congrArg (freeEnergy E) (h.eqOn hc rfl hb.le)

#print axioms exists_interior_with_same_drift_and_dissipation
#print axioms boxDissipation_nonneg_of_no_active_edge
#print axioms boxDissipation_eq_zero_iff_drift_of_no_active_edge
#print axioms clippedDrift_eq_zero_iff_inactive_and_zero_dissipation
#print axioms IsBoxOccupationFlow.no_active_boundary_edge_pos
#print axioms IsBoxOccupationFlow.boxDissipation_nonneg_pos
#print axioms IsBoxOccupationFlow.boxDissipation_eq_zero_iff_drift_pos
#print axioms IsBoxOccupationFlow.continuousOn_boxDissipation
#print axioms IsBoxOccupationFlow.continuousOn_freeEnergy
#print axioms IsBoxOccupationFlow.intervalIntegrable_boxDissipation
#print axioms IsBoxOccupationFlow.integral_boxDissipation_eq_freeEnergy_sub
#print axioms IsBoxOccupationFlow.antitoneOn_freeEnergy
#print axioms IsBoxOccupationFlow.freeEnergy_eq_iff_eqOn
#print axioms IsBoxOccupationFlow.freeEnergy_eq_initial_iff_drift_zero

end

end GaloisForLFunctions.HTGeometry.Quantum.FermiGraph
