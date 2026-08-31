import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedIntegrableCocycleDescent

/-!
# Lattice-carry transgression and invariant formation current

A compact finite-mass observer does not necessarily kill open affine drift.  It can retain the
drift as a lattice-valued section defect.  This module proves the exact classification law:

`mass * drift = lattice period * mean carry`.

Changing the phase section changes carry by an integrable coboundary without changing its mean.
The absolute carry traffic exceeds the oriented current by exactly twice the smaller of the two
counter-propagating currents.  Serial formation adds carries, and bounded phase remainder cannot
alter the asymptotic winding rate of an open lift.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Positive microscopic carry. -/
def carryPositivePart (k : Ω → ℝ) (x : Ω) : ℝ := max (k x) 0

/-- Negative microscopic carry, recorded with positive magnitude. -/
def carryNegativePart (k : Ω → ℝ) (x : Ω) : ℝ := max (-k x) 0

omit [MeasurableSpace Ω] in
theorem carry_eq_positivePart_sub_negativePart (k : Ω → ℝ) (x : Ω) :
    k x = carryPositivePart k x - carryNegativePart k x := by
  rcases le_total 0 (k x) with hk | hk
  · simp [carryPositivePart, carryNegativePart, hk, neg_nonpos.mpr hk]
  · have hkn : -k x ≥ 0 := neg_nonneg.mpr hk
    simp [carryPositivePart, carryNegativePart, hk, hkn]

omit [MeasurableSpace Ω] in
theorem abs_carry_eq_positivePart_add_negativePart (k : Ω → ℝ) (x : Ω) :
    |k x| = carryPositivePart k x + carryNegativePart k x := by
  rcases le_total 0 (k x) with hk | hk
  · simp [carryPositivePart, carryNegativePart, hk, neg_nonpos.mpr hk, abs_of_nonneg hk]
  · have hkn : -k x ≥ 0 := neg_nonneg.mpr hk
    simp [carryPositivePart, carryNegativePart, hk, hkn, abs_of_nonpos hk]

/-- **Invariant drift-current reconstruction.**  An integrable compensated lift over finite
invariant mass has drift equal to its lattice period times mean carry, with the total mass factor
retained for non-probability measures. -/
theorem compensatedLift_integral_current
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (L chi : ℝ) (u k : Ω → ℝ) (hu : Integrable u μ) (hk : Integrable k μ)
    (hlift : (fun x => u (T x) - u x + L * k x) =ᵐ[μ] fun _ => chi) :
    μ.real Set.univ * chi = L * ∫ x, k x ∂μ := by
  have hmap : Measure.map T μ = μ := hT.map_eq
  have hmeasmap : AEStronglyMeasurable u (Measure.map T μ) := by
    rw [hmap]
    exact hu.aestronglyMeasurable
  have huT : Integrable (fun x => u (T x)) μ :=
    (hT.integrable_comp hu.aestronglyMeasurable).mpr hu
  have hshift : ∫ x, u (T x) ∂μ = ∫ x, u x ∂μ := by
    calc
      ∫ x, u (T x) ∂μ = ∫ x, u x ∂Measure.map T μ := by
        simpa only [Function.comp_apply] using
          (integral_map hT.measurable.aemeasurable hmeasmap).symm
      _ = ∫ x, u x ∂μ := by rw [hmap]
  calc
    μ.real Set.univ * chi = ∫ _ : Ω, chi ∂μ := by rw [integral_const]; simp
    _ = ∫ x, (u (T x) - u x + L * k x) ∂μ :=
      (integral_congr_ae hlift).symm
    _ = (∫ x, u (T x) ∂μ) - (∫ x, u x ∂μ) + L * ∫ x, k x ∂μ := by
      calc
        ∫ x, (u (T x) - u x + L * k x) ∂μ =
            (∫ x, (u (T x) - u x) ∂μ) + ∫ x, L * k x ∂μ := by
          simpa using integral_add (huT.sub hu) (hk.const_mul L)
        _ = (∫ x, u (T x) ∂μ) - (∫ x, u x ∂μ) + L * ∫ x, k x ∂μ := by
          rw [integral_sub huT hu, integral_const_mul]
    _ = L * ∫ x, k x ∂μ := by rw [hshift]; ring

/-- Probability-normalized drift-current reconstruction. -/
theorem compensatedLift_probability_current
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (L chi : ℝ) (u k : Ω → ℝ) (hu : Integrable u μ) (hk : Integrable k μ)
    (hlift : (fun x => u (T x) - u x + L * k x) =ᵐ[μ] fun _ => chi) :
    chi = L * ∫ x, k x ∂μ := by
  simpa using compensatedLift_integral_current μ T hT L chi u k hu hk hlift

/-- With finite invariant probability mass and no lattice carry, an integrable exact lift is
neutral.  This is the zero-current chamber of compensated descent. -/
theorem compensatedLift_neutral_of_zero_carry
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (L chi : ℝ) (u k : Ω → ℝ) (hu : Integrable u μ) (hk : Integrable k μ)
    (hlift : (fun x => u (T x) - u x + L * k x) =ᵐ[μ] fun _ => chi)
    (hkzero : k =ᵐ[μ] 0) : chi = 0 := by
  have hcurrent := compensatedLift_probability_current μ T hT L chi u k hu hk hlift
  have hint : (∫ x, k x ∂μ) = 0 := by
    simpa using integral_congr_ae hkzero
  rw [hcurrent, hint, mul_zero]

omit [MeasurableSpace Ω] in
/-- Lattice gauge changes preserve the compensated lift equation pointwise. -/
theorem compensatedLift_gauge_covariant
    (T : Ω → Ω) (L chi : ℝ) (u k h : Ω → ℝ)
    (hlift : ∀ x, u (T x) - u x + L * k x = chi) (x : Ω) :
    (u (T x) + L * h (T x)) - (u x + L * h x) +
        L * (k x + h x - h (T x)) = chi := by
  rw [← hlift x]
  ring

/-- An integrable lattice gauge changes carry by a coboundary but preserves invariant current. -/
theorem carryGauge_integral_current_eq
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (k h : Ω → ℝ) (hk : Integrable k μ) (hh : Integrable h μ) :
    (∫ x, (k x + h x - h (T x)) ∂μ) = ∫ x, k x ∂μ := by
  have hhT : Integrable (fun x => h (T x)) μ :=
    (hT.integrable_comp hh.aestronglyMeasurable).mpr hh
  have hmap : Measure.map T μ = μ := hT.map_eq
  have hmeasmap : AEStronglyMeasurable h (Measure.map T μ) := by
    rw [hmap]
    exact hh.aestronglyMeasurable
  have hshift : ∫ x, h (T x) ∂μ = ∫ x, h x ∂μ := by
    calc
      ∫ x, h (T x) ∂μ = ∫ x, h x ∂Measure.map T μ := by
        simpa only [Function.comp_apply] using
          (integral_map hT.measurable.aemeasurable hmeasmap).symm
      _ = ∫ x, h x ∂μ := by rw [hmap]
  calc
    ∫ x, (k x + h x - h (T x)) ∂μ =
        (∫ x, (k x + h x) ∂μ) - ∫ x, h (T x) ∂μ := by
      simpa using integral_sub (hk.add hh) hhT
    _ = (∫ x, k x ∂μ) + (∫ x, h x ∂μ) - ∫ x, h (T x) ∂μ := by
      rw [integral_add hk hh]
    _ = ∫ x, k x ∂μ := by rw [hshift]; ring

/-- **Hahn traffic/counterflow identity.**  Absolute carry traffic exceeds oriented current
magnitude by exactly twice the smaller counter-propagating current. -/
theorem carryTraffic_sub_abs_current_eq_two_min
    (μ : Measure Ω) (k : Ω → ℝ) (hk : Integrable k μ) :
    (∫ x, |k x| ∂μ) - |∫ x, k x ∂μ| =
      2 * min (∫ x, carryPositivePart k x ∂μ)
        (∫ x, carryNegativePart k x ∂μ) := by
  have hp : Integrable (carryPositivePart k) μ := hk.pos_part
  have hn : Integrable (carryNegativePart k) μ := hk.neg_part
  have ha : Integrable (fun x => |k x|) μ := by simpa [Real.norm_eq_abs] using hk.norm
  let A : ℝ := ∫ x, carryPositivePart k x ∂μ
  let B : ℝ := ∫ x, carryNegativePart k x ∂μ
  have hA : 0 ≤ A := integral_nonneg fun x => le_max_right (k x) 0
  have hB : 0 ≤ B := integral_nonneg fun x => le_max_right (-k x) 0
  have hcurrent : (∫ x, k x ∂μ) = A - B := by
    calc
      ∫ x, k x ∂μ = ∫ x, (carryPositivePart k x - carryNegativePart k x) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x =>
          carry_eq_positivePart_sub_negativePart k x)
      _ = A - B := by rw [integral_sub hp hn]
  have htraffic : (∫ x, |k x| ∂μ) = A + B := by
    calc
      ∫ x, |k x| ∂μ = ∫ x, (carryPositivePart k x + carryNegativePart k x) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x =>
          abs_carry_eq_positivePart_add_negativePart k x)
      _ = A + B := by rw [integral_add hp hn]
  rw [hcurrent, htraffic]
  rcases le_total A B with hAB | hBA
  · rw [min_eq_left hAB, abs_of_nonpos (sub_nonpos.mpr hAB)]
    ring
  · rw [min_eq_right hBA, abs_of_nonneg (sub_nonneg.mpr hBA)]
    ring

/-- Drift reconstruction fused with phase-blind traffic: the lost orientation is exact
counterflow. -/
theorem compensatedLift_traffic_counterflow
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (L chi : ℝ) (hL : 0 < L) (u k : Ω → ℝ)
    (hu : Integrable u μ) (hk : Integrable k μ)
    (hlift : (fun x => u (T x) - u x + L * k x) =ᵐ[μ] fun _ => chi) :
    L * (∫ x, |k x| ∂μ) - |chi| =
      2 * L * min (∫ x, carryPositivePart k x ∂μ)
        (∫ x, carryNegativePart k x ∂μ) := by
  have hcurrent := compensatedLift_probability_current μ T hT L chi u k hu hk hlift
  have htraffic := carryTraffic_sub_abs_current_eq_two_min μ k hk
  rw [hcurrent, abs_mul, abs_of_pos hL]
  nlinarith

omit [MeasurableSpace Ω] in
/-- **Serial formation.**  Compensated lift drift and carry add exactly through every finite
observer history. -/
theorem compensatedLift_iterate
    (T : Ω → Ω) (L chi : ℝ) (u k : Ω → ℝ)
    (hlift : ∀ x, u (T x) - u x + L * k x = chi) :
    ∀ n x, u ((T^[n]) x) - u x +
        L * ∑ j ∈ Finset.range n, k ((T^[j]) x) = (n : ℝ) * chi := by
  intro n
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      have hstep := hlift ((T^[n]) x)
      have hprev := ih x
      rw [Function.iterate_succ_apply', Finset.sum_range_succ, Nat.cast_succ]
      linarith

/-- **Exact winding-rate prediction.**  A bounded compact-phase remainder cannot alter the
asymptotic velocity of an open lift; its winding rate is source velocity divided by lattice
period. -/
theorem tendsto_windingRate_of_bounded_remainder
    (L c : ℝ) (hL : 0 < L) (X K r : ℕ → ℝ)
    (hdecomp : ∀ n, X n = L * K n + r n)
    (hr0 : ∀ n, 0 ≤ r n) (hrL : ∀ n, r n ≤ L)
    (hX : Tendsto (fun n : ℕ => X n / (n : ℝ)) atTop (nhds c)) :
    Tendsto (fun n : ℕ => K n / (n : ℝ)) atTop (nhds (c / L)) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have hupper : Tendsto (fun n : ℕ => L / (n : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul L
  have hr : Tendsto (fun n : ℕ => r n / (n : ℝ)) atTop (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => ?_)
      (Filter.Eventually.of_forall fun n => ?_) hupper
    · exact div_nonneg (hr0 n) (Nat.cast_nonneg n)
    · exact div_le_div_of_nonneg_right (hrL n) (Nat.cast_nonneg n)
  have hquot : Tendsto (fun n : ℕ => (X n / (n : ℝ) - r n / (n : ℝ)) / L)
      atTop (nhds ((c - 0) / L)) := (hX.sub hr).div_const L
  convert hquot using 1
  · funext n
    rw [hdecomp n]
    by_cases hn : n = 0
    · subst n
      simp
    · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp [hL.ne', hnR]
      ring
  · simp

end

end GaloisForLFunctions.HTGeometry
