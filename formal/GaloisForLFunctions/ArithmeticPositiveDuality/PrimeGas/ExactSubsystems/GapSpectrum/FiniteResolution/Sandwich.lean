import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.FiniteResolution.RowProbability
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.Continuum.Collision
import Mathlib.Probability.CDF

/-! # Collision control of the error in the positive gap cumulative -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open MeasureTheory Set Filter Topology

/-- Probability of identical labels at inverse temperature 1+h. -/
def collisionMass (h : Ioi (0:ℝ)) := (overlapCoefficient (excessDamping h) 0).re

theorem collisionMass_as_sum (h : Ioi (0:ℝ)) :
    collisionMass h = ∑' n, labelMass h n * labelMass h n := by
  classical
  let x := excessDamping h
  have hd : (fun q => h.val/2*gapFrequency q) ⁻¹' {0} = {q : ℕ+ × ℕ+ | q.1 = q.2} := by
    ext q
    change h.val/2*gapFrequency q = 0 ↔ q.1 = q.2
    rw [mul_eq_zero,or_iff_right (half_pos (show 0 < h.val from h.property)).ne',gapFrequency,mul_eq_zero,
      or_iff_right two_ne_zero,sub_eq_zero]
    exact ⟨label_of_energy_eq,congrArg energy⟩
  have hz := sampledGapLaw_zero (excessDamping_gt h) (half_pos (show 0 < h.val from h.property)).ne'
  unfold collisionMass
  rw [← hz]
  change ((Measure.map _ _) {0}).toReal = _
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _),hd]
  change (gibbsPairLaw x (excessDamping_gt h) : Measure (ℕ+ × ℕ+)).real _ = _
  rw [pair_event_rows]
  apply tsum_congr
  intro n
  apply congrArg (labelMass h n * ·)
  rw [tsum_eq_single n]
  · exact if_pos rfl
  · intro m hm
    exact if_neg hm

private theorem integralRowSummable (h : Ioi (0:ℝ)) :
    Summable (fun n : ℕ+ => labelMass h n * (n.val:ℝ)^(-h.val)) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (labelMass_pos h n).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) _ (labelMass_hasSum h).summable
  intro n
  apply mul_le_of_le_one_right (labelMass_pos h n).le
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast n.pos) (neg_nonpos.mpr h.property.le)

/-- Total continuum row factor before calibrating the two open half-lines. -/
def rowIntegralFactor (h : Ioi (0:ℝ)) :=
  (∑' n : ℕ+, labelMass h n*(n.val:ℝ)^(-h.val))/(h.val*labelPartition h)

private theorem partition_real (β : TraceTemperature) :
    (riemannZeta (β.val:ℂ)).re = ∑' n, thermalWeight β n := by
  rw [← thermalWeight_partition β,Complex.ofReal_re]

/-- The integral calibration is itself a quotient of two prime-gas partition functions. -/
theorem rowIntegralFactor_zeta (h : Ioi (0:ℝ)) :
    rowIntegralFactor h = (riemannZeta ((1+2*h.val:ℝ):ℂ)).re /
      (h.val*(riemannZeta ((1+h.val:ℝ):ℂ)).re^2) := by
  have hh : 0 < h.val := h.property
  let β : TraceTemperature := ⟨1+2*h.val,by linarith only [hh]⟩
  have hn (n : ℕ+) : labelMass h n*(n.val:ℝ)^(-h.val) =
      thermalWeight β n/labelPartition h := by
    rw [labelMass_eq,Real.rpow_def_of_pos (Nat.cast_pos.mpr n.pos)]
    rw [div_mul_eq_mul_div,thermalWeight,thermalWeight,← Real.exp_add]
    congr 2
    change -(1+h.val)*Real.log (n.val:ℝ)+Real.log (n.val:ℝ)*(-h.val) = -(1+2*h.val)*Real.log (n.val:ℝ)
    ring
  have hz : (riemannZeta ((1+h.val:ℝ):ℂ)).re = labelPartition h := partition_real (labelTemperature h)
  have hz' : (riemannZeta ((1+2*h.val:ℝ):ℂ)).re = ∑' n, thermalWeight β n := partition_real β
  rw [rowIntegralFactor,tsum_congr hn,tsum_div_const,hz,hz']
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The same diagonal probability controls the cumulative row error at every positive cutoff. -/
theorem positive_band_sandwich (h : Ioi (0:ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    let P := (criticalGapLaw h : Measure ℝ).real (Ioc 0 t)
    let A := rowIntegralFactor h*(1-Real.exp (-t))
    P ≤ A ∧ A ≤ P+collisionMass h := by
  let B := fun n : ℕ+ => labelMass h n*(positiveGapRow h.val (t/h.val) n / labelPartition h)
  let w := fun n : ℕ+ => labelMass h n*(n.val:ℝ)^(-h.val)
  let c := (1-Real.exp (-t))/(h.val*labelPartition h)
  have ht' := div_nonneg ht h.property.le
  have hh : h.val ≠ 0 := h.property.ne'
  have he : -h.val*(t/h.val) = -t := by field_simp
  have hB0 (n : ℕ+) : 0 ≤ B n := by
    apply mul_nonneg (labelMass_pos h n).le
    exact div_nonneg (Finset.sum_nonneg fun i _ => (Real.exp_pos _).le) (labelPartition_pos h).le
  have hrow (n : ℕ+) : B n ≤ w n*c ∧ w n*c ≤ B n+labelMass h n*labelMass h n := by
    have hs := positive_gap_row_estimate (show 0 < h.val from h.property) ht' n
    dsimp only at hs
    rw [he] at hs
    have H := mul_le_mul_of_nonneg_left (sub_nonneg.mp hs.1) (div_nonneg (labelMass_pos h n).le (labelPartition_pos h).le)
    have H' := mul_le_mul_of_nonneg_left (sub_le_iff_le_add.mp hs.2) (div_nonneg (labelMass_pos h n).le (labelPartition_pos h).le)
    have hp : Real.exp (-(1+h.val)*energy n)/labelPartition h = labelMass h n := (labelMass_eq h n).symm
    constructor
    · calc
        B n = (labelMass h n / labelPartition h)*positiveGapRow h.val (t/h.val) n := by dsimp [B]; ring
        _ ≤ _ := H
        _ = w n*c := by dsimp [w,c]; simp only [div_eq_mul_inv,mul_inv_rev]; ring
    · calc
        w n*c = (labelMass h n/labelPartition h)*((n.val:ℝ)^(-h.val)*(1-Real.exp (-t))/h.val) := by
          dsimp [w,c]; simp only [div_eq_mul_inv,mul_inv_rev]; ring
        _ ≤ _ := H'
        _ = B n + labelMass h n*labelMass h n := by
          rw [show (labelMass h n/labelPartition h)*(Real.exp (-(1+h.val)*energy n)+positiveGapRow h.val (t/h.val) n) =
            B n + labelMass h n*(Real.exp (-(1+h.val)*energy n)/labelPartition h) by dsimp [B]; ring,hp]
  have hw := (integralRowSummable h).mul_right c
  have hB := Summable.of_nonneg_of_le hB0 (fun n => (hrow n).1) hw
  have hdiag : Summable (fun n => labelMass h n*labelMass h n) := by
    apply Summable.of_nonneg_of_le (fun n => mul_self_nonneg _) _ (labelMass_hasSum h).summable
    intro n
    have hle := (labelMass_hasSum h).summable.le_tsum n (fun i _ => (labelMass_pos h i).le)
    exact mul_le_of_le_one_right (labelMass_pos h n).le (hle.trans_eq (labelMass_hasSum h).tsum_eq)
  have hP : (criticalGapLaw h : Measure ℝ).real (Ioc 0 t) = ∑' n, B n := by
    have hp := positive_band_probability h ht'
    rwa [show h.val*(t/h.val) = t by field_simp] at hp
  have hA : rowIntegralFactor h*(1-Real.exp (-t)) = ∑' n, w n*c := by
    rw [tsum_mul_right]
    dsimp [rowIntegralFactor,w,c]
    ring
  dsimp only
  rw [hP,hA,collisionMass_as_sum,← hB.tsum_add hdiag]
  exact ⟨hB.tsum_le_tsum (fun n => (hrow n).1) hw,hw.tsum_le_tsum (fun n => (hrow n).2) (hB.add hdiag)⟩

#print axioms collisionMass_as_sum
#print axioms rowIntegralFactor_zeta
#print axioms positive_band_sandwich

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
