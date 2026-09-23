import Mathlib

/-!
# Determinant-one Nevanlinna boundary algebra

This module formalizes the algebraic source of the projective support label for an N-extremal
Nevanlinna family. A determinant-one real matrix has disjoint finite and infinite denominator
fibers, and the explicit one-point label recovers each fiber exactly. The usual resolvent Mobius
difference formula follows from the same determinant identity.
-/

namespace GaloisForLFunctions.HTGeometry

open OnePoint
open Filter
open scoped OnePoint Topology

noncomputable section

variable {X : Type*}

/-- The projective boundary is measured by its Borel sigma algebra. Mathlib intentionally does
not install a measurable-space instance on the general one-point construction, so this concrete
real instance is part of the Nevanlinna boundary data. -/
noncomputable instance instMeasurableSpaceOnePointReal : MeasurableSpace (OnePoint ℝ) :=
  borel (OnePoint ℝ)

instance instBorelSpaceOnePointReal : BorelSpace (OnePoint ℝ) := ⟨rfl⟩

/-- Pointwise real determinant-one Nevanlinna matrix data. Analyticity and the moment-problem
interpretation are deliberately separate from this algebraic layer. -/
structure NevanlinnaMatrixData (X : Type*) where
  a : X → ℝ
  b : X → ℝ
  c : X → ℝ
  d : X → ℝ
  det_one : ∀ x, a x * d x - b x * c x = 1

namespace NevanlinnaMatrixData

variable (W : NevanlinnaMatrixData X)

/-- Denominator-zero fiber for a finite projective parameter. -/
def finiteDenominatorFiber (tau : ℝ) : Set X := {x | W.c x * tau + W.d x = 0}

/-- Denominator-zero fiber for the projective parameter at infinity. -/
def infinityDenominatorFiber : Set X := {x | W.c x = 0}

/-- Explicit projective support label `[-D:C]` in the one-point model of `RP^(1 : ℕ)(R)`. -/
def projectiveLabel (x : X) : OnePoint ℝ :=
  if W.c x = 0 then ∞ else ((-W.d x / W.c x : ℝ) : OnePoint ℝ)

/-- The determinant identity forbids a common zero of the lower row. -/
theorem C_D_ne_zero (x : X) : ¬(W.c x = 0 ∧ W.d x = 0) := by
  rintro ⟨hC, hD⟩
  have h := W.det_one x
  rw [hC, hD] at h
  norm_num at h

/-- Distinct finite parameters have disjoint denominator fibers. -/
theorem finiteDenominatorFiber_disjoint {tau sigma : ℝ} (h : tau ≠ sigma) :
    Disjoint (W.finiteDenominatorFiber tau) (W.finiteDenominatorFiber sigma) := by
  rw [Set.disjoint_left]
  intro x hxt hxs
  change W.c x * tau + W.d x = 0 at hxt
  change W.c x * sigma + W.d x = 0 at hxs
  have hC : W.c x = 0 := by
    by_contra hC
    apply h
    apply mul_left_cancel₀ hC
    linarith
  have hD : W.d x = 0 := by simpa [hC] using hxt
  exact C_D_ne_zero W x ⟨hC, hD⟩

/-- Every finite denominator fiber is disjoint from the infinity fiber. -/
theorem finiteDenominatorFiber_disjoint_infinity (tau : ℝ) :
    Disjoint (W.finiteDenominatorFiber tau) W.infinityDenominatorFiber := by
  rw [Set.disjoint_left]
  intro x hxt hxinf
  change W.c x * tau + W.d x = 0 at hxt
  change W.c x = 0 at hxinf
  have hD : W.d x = 0 := by simpa [hxinf] using hxt
  exact C_D_ne_zero W x ⟨hxinf, hD⟩

/-- A finite label is recovered exactly by its denominator equation. -/
theorem projectiveLabel_eq_coe_iff (x : X) (tau : ℝ) :
    W.projectiveLabel x = (tau : OnePoint ℝ) ↔ W.c x * tau + W.d x = 0 := by
  unfold projectiveLabel
  by_cases hC : W.c x = 0
  · have hD : W.d x ≠ 0 := fun hD => C_D_ne_zero W x ⟨hC, hD⟩
    simp [hC, hD]
  · simp only [hC, if_false, OnePoint.coe_eq_coe]
    constructor
    · intro h
      field_simp at h
      linarith
    · intro h
      apply (div_eq_iff hC).2
      linarith

/-- The infinity label is recovered exactly by vanishing of `C`. -/
theorem projectiveLabel_eq_infty_iff (x : X) :
    W.projectiveLabel x = ∞ ↔ W.c x = 0 := by
  unfold projectiveLabel
  by_cases hC : W.c x = 0
  · simp [hC]
  · simp [hC, OnePoint.coe_ne_infty]

theorem projectiveLabel_eq_of_mem_finiteFiber {x : X} {tau : ℝ}
    (hx : x ∈ W.finiteDenominatorFiber tau) :
    W.projectiveLabel x = (tau : OnePoint ℝ) :=
  (W.projectiveLabel_eq_coe_iff x tau).2 hx

theorem projectiveLabel_eq_infty_of_mem_infinityFiber {x : X}
    (hx : x ∈ W.infinityDenominatorFiber) : W.projectiveLabel x = ∞ :=
  (W.projectiveLabel_eq_infty_iff x).2 hx

/-- If the lower row is continuous, the determinant-one projective label `[-D:C]` is continuous
into the one-point model of the real projective line. At a zero of `C`, determinant one forces
`D ≠ 0`, so `-D/C` escapes every compact real set and converges to infinity. -/
theorem continuous_projectiveLabel
    [TopologicalSpace X] (hc : Continuous W.c) (hd : Continuous W.d) :
    Continuous W.projectiveLabel := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hcx : W.c x = 0
  · have hdx : W.d x ≠ 0 := fun hdx => C_D_ne_zero W x ⟨hcx, hdx⟩
    change Tendsto W.projectiveLabel (nhds x) (nhds (W.projectiveLabel x))
    rw [show W.projectiveLabel x = ∞ from (W.projectiveLabel_eq_infty_iff x).2 hcx]
    rw [OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
    intro s hs
    rcases Metric.isBounded_iff_subset_closedBall 0 |>.1 hs.2.isBounded with ⟨r, hr⟩
    let R : ℝ := |r| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have hrR : r ≤ R := by dsimp [R]; linarith [le_abs_self r]
    have hsR : s ⊆ Metric.closedBall (0 : ℝ) R :=
      hr.trans (Metric.closedBall_subset_closedBall hrR)
    have hdpos : 0 < |W.d x| := abs_pos.mpr hdx
    let eps : ℝ := |W.d x| / (2 * (R + 1))
    have heps : 0 < eps := by dsimp [eps]; positivity
    have hdEv : ∀ᶠ y in nhds x, |W.d x| / 2 < |W.d y| := by
      exact (continuousAt_const : ContinuousAt (fun _ : X => |W.d x| / 2) x).eventually_lt
        hd.continuousAt.abs (by linarith)
    have hcEv : ∀ᶠ y in nhds x, |W.c y| < eps := by
      apply hc.continuousAt.abs.eventually_lt
        (continuousAt_const : ContinuousAt (fun _ : X => eps) x)
      simpa [hcx] using heps
    filter_upwards [hdEv, hcEv] with y hdy hcy
    by_cases hcy0 : W.c y = 0
    · simp [NevanlinnaMatrixData.projectiveLabel, hcy0]
    · have hcabs : 0 < |W.c y| := abs_pos.mpr hcy0
      have hratio : R < |-W.d y / W.c y| := by
        rw [abs_div, abs_neg]
        apply (lt_div_iff₀ hcabs).2
        have hmul : |W.c y| * (R + 1) < |W.d x| / 2 := by
          dsimp [eps] at hcy
          have hR1 : 0 < R + 1 := by linarith
          calc
            |W.c y| * (R + 1) <
                (|W.d x| / (2 * (R + 1))) * (R + 1) :=
              mul_lt_mul_of_pos_right hcy hR1
            _ = |W.d x| / 2 := by field_simp
        nlinarith
      have hnot : -W.d y / W.c y ∉ s := by
        intro hmem
        have hb := hsR hmem
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hb
        linarith
      simp [NevanlinnaMatrixData.projectiveLabel, hcy0, hnot]
  · have hratioCont : ContinuousAt (fun y => -W.d y / W.c y) x :=
      hd.continuousAt.neg.div hc.continuousAt hcx
    have hcoeCont : ContinuousAt (fun y => ((-W.d y / W.c y : ℝ) : OnePoint ℝ)) x := by
      simpa [Function.comp_def] using OnePoint.continuous_coe.continuousAt.comp hratioCont
    apply hcoeCont.congr_of_eventuallyEq
    filter_upwards [hc.continuousAt.eventually_ne hcx] with y hy
    simp [NevanlinnaMatrixData.projectiveLabel, hy]

/-- A probability measure carried by one finite denominator fiber has exactly that finite
projective label. This turns spectral support separation into the pushforward hypothesis used by
the abstract labeled-boundary simplex. -/
theorem map_projectiveLabel_eq_dirac_of_carried_finite
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure mu] (tau : ℝ)
    (hc : Continuous W.c) (hd : Continuous W.d)
    (hcarry : mu (W.finiteDenominatorFiber tau)ᶜ = 0) :
    MeasureTheory.Measure.map W.projectiveLabel mu =
      MeasureTheory.Measure.dirac (tau : OnePoint ℝ) := by
  have hmeas : Measurable W.projectiveLabel :=
    (W.continuous_projectiveLabel hc hd).measurable
  have hmem : ∀ᵐ x ∂mu, x ∈ W.finiteDenominatorFiber tau := by
    rw [MeasureTheory.ae_iff]
    exact hcarry
  have hae : W.projectiveLabel =ᵐ[mu] fun _ => (tau : OnePoint ℝ) := by
    filter_upwards [hmem] with x hx
    exact W.projectiveLabel_eq_of_mem_finiteFiber hx
  rw [MeasureTheory.Measure.map_congr hae, MeasureTheory.Measure.map_const]
  rw [MeasureTheory.measure_univ, one_smul]

/-- A probability measure carried by the infinite denominator fiber has the point-at-infinity
projective label. -/
theorem map_projectiveLabel_eq_dirac_of_carried_infinity
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure mu]
    (hc : Continuous W.c) (hd : Continuous W.d)
    (hcarry : mu W.infinityDenominatorFiberᶜ = 0) :
    MeasureTheory.Measure.map W.projectiveLabel mu =
      MeasureTheory.Measure.dirac (∞ : OnePoint ℝ) := by
  have hmeas : Measurable W.projectiveLabel :=
    (W.continuous_projectiveLabel hc hd).measurable
  have hmem : ∀ᵐ x ∂mu, x ∈ W.infinityDenominatorFiber := by
    rw [MeasureTheory.ae_iff]
    exact hcarry
  have hae : W.projectiveLabel =ᵐ[mu] fun _ => (∞ : OnePoint ℝ) := by
    filter_upwards [hmem] with x hx
    exact W.projectiveLabel_eq_infty_of_mem_infinityFiber hx
  rw [MeasureTheory.Measure.map_congr hae, MeasureTheory.Measure.map_const]
  rw [MeasureTheory.measure_univ, one_smul]

variable {W}

/-- Exact determinant-one Mobius difference formula on the regular denominator locus. -/
theorem mobius_difference (x : X) (tau : ℝ)
    (hC : W.c x ≠ 0) (hden : W.c x * tau + W.d x ≠ 0) :
    (W.a x * tau + W.b x) / (W.c x * tau + W.d x) =
      W.a x / W.c x + (-1 / W.c x ^ (2 : ℕ)) / (tau - (-W.d x / W.c x)) := by
  have hdet := W.det_one x
  have hden' : tau * W.c x + W.d x ≠ 0 := by simpa [mul_comm] using hden
  field_simp [hC, hden, hden']
  linear_combination -(W.c x * tau + W.d x) * hdet

end NevanlinnaMatrixData

end

end GaloisForLFunctions.HTGeometry
