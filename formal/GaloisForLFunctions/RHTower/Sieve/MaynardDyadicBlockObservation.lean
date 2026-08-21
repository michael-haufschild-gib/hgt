import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalObservationCone

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex
open GaloisForLFunctions.HTGeometry

/-- Radius whose observation endpoint covers every proportional adjacent window with physical
scale in `[x,2x]` and relative width at most `R`. -/
def maynardDyadicBlockObservationRadius (x N R : ℝ) : ℝ :=
  x * (N + 4 * R) / 2

private theorem arithmeticFunction_sum_apply_block
    {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (F : ι → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ u, F i) n = ∑ i ∈ u, F i n := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [ArithmeticFunction.zero_apply]
  | @insert a u ha ih => simp [ha, ih, ArithmeticFunction.add_apply]

/-- One observation cone fixed at the left endpoint of a dyadic physical block is coefficient-
exact for every proportional adjacent window throughout that block. -/
theorem complexCoeff_windowRelevant_mul_scaled_routeWeight_eq_dyadicBlockObserved
    (L X k : ℕ) (T t : ℝ) {x lambda N R W : ℝ}
    (hx : 0 < x) (hlambda : lambda ∈ Set.Icc x (2 * x))
    (hN : 0 < N) (hR : 0 < R) (hW : 0 < W) (hWR : W ≤ R)
    (n : ℕ) :
    complexCoeff (heathBrownWindowRelevantEligiblePacket
        L X k T t (lambda * N)) n *
        ((routeTSmoothWindowWeight (lambda * N) (lambda * W) (n : ℝ) : ℝ) : ℂ) =
      complexCoeff (heathBrownObservedEligiblePacket L X k T t
        (x * N) (maynardDyadicBlockObservationRadius x N R)) n *
        ((routeTSmoothWindowWeight (lambda * N) (lambda * W) (n : ℝ) : ℝ) : ℂ) := by
  classical
  have hlambdaPos : 0 < lambda := hx.trans_le hlambda.1
  have hwidth : 0 < lambda * W := mul_pos hlambdaPos hW
  have hbaseMono : x * N ≤ lambda * N :=
    mul_le_mul_of_nonneg_right hlambda.1 hN.le
  have hphysEnd :
      lambda * N + 2 * (lambda * W) ≤
        x * N + 2 * maynardDyadicBlockObservationRadius x N R := by
    have hbaseUpper : lambda * N ≤ (2 * x) * N :=
      mul_le_mul_of_nonneg_right hlambda.2 hN.le
    have hwidthMono : lambda * W ≤ lambda * R :=
      mul_le_mul_of_nonneg_left hWR hlambdaPos.le
    have hwidthUpper : lambda * R ≤ (2 * x) * R :=
      mul_le_mul_of_nonneg_right hlambda.2 hR.le
    rw [maynardDyadicBlockObservationRadius]
    nlinarith
  rw [complexCoeff_apply, complexCoeff_apply]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [heathBrownWindowRelevantEligiblePacket,
    heathBrownObservedEligiblePacket,
    arithmeticFunction_sum_apply_block,
    arithmeticFunction_sum_apply_block]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro box hbox
  let q := heathBrownBoxFactorExponent box.a box.b box.q
  by_cases hactual : IsHeathBrownBoxEligible L X k T t box ∧
      IsHeathBrownBoxWindowRelevant (lambda * N) X k box
  · have hblockWindow : IsHeathBrownBoxWindowRelevant (x * N) X k box :=
      ⟨hactual.2.1, hbaseMono.trans_lt hactual.2.2⟩
    by_cases hvisible : (groupedDyadicLower q : ℝ) <
        x * N + 2 * maynardDyadicBlockObservationRadius x N R
    · have hblock : IsHeathBrownBoxEligible L X k T t box ∧
          IsHeathBrownBoxObservedRelevant (x * N)
            (maynardDyadicBlockObservationRadius x N R) X k box :=
        ⟨hactual.1, hblockWindow, hvisible⟩
      simp [hactual, hblock]
    · have hblock : ¬ (IsHeathBrownBoxEligible L X k T t box ∧
          IsHeathBrownBoxObservedRelevant (x * N)
            (maynardDyadicBlockObservationRadius x N R) X k box) := by
        intro h
        exact hvisible h.2.2
      have hlower : x * N + 2 * maynardDyadicBlockObservationRadius x N R ≤
          (groupedDyadicLower q : ℝ) := le_of_not_gt hvisible
      by_cases hterm : heathBrownDyadicTermBox
          L X k box.m box.a box.b box.q n = 0
      · have hnotObserved : ¬ IsHeathBrownBoxObservedRelevant (x * N)
            (maynardDyadicBlockObservationRadius x N R) X k box := by
          intro hobs
          exact hblock ⟨hactual.1, hobs⟩
        simp [hactual, hnotObserved, hterm]
      · have hnlow := vanishesBelow_heathBrownDyadicTermBox
          L X k box.m box.a box.b box.q n
        have hnedge : heathBrownDyadicCoreLower
            (k - box.m) box.a box.b box.q ≤ n := by
          by_contra hnot
          exact hterm (hnlow (Nat.lt_of_not_ge hnot))
        have hnreal : lambda * N + 2 * (lambda * W) ≤ (n : ℝ) := by
          have hedge : x * N + 2 * maynardDyadicBlockObservationRadius x N R ≤
              (heathBrownDyadicCoreLower
                (k - box.m) box.a box.b box.q : ℝ) := by
            rw [← groupedDyadicLower_heathBrownBoxFactorExponent_eq_coreLower]
            exact hlower
          exact hphysEnd.trans (hedge.trans (by exact_mod_cast hnedge))
        have hplus := smoothWeight_eq_zero hwidth
          (show lambda * N + lambda * W + lambda * W ≤ (n : ℝ) by linarith)
        have hbase := smoothWeight_eq_zero hwidth
          (show lambda * N + lambda * W ≤ (n : ℝ) by linarith)
        have hzero : routeTSmoothWindowWeight
            (lambda * N) (lambda * W) (n : ℝ) = 0 := by
          rw [routeTSmoothWindowWeight, hplus, hbase, sub_self]
        simp [hactual, hzero]
  · by_cases hblock : IsHeathBrownBoxEligible L X k T t box ∧
        IsHeathBrownBoxObservedRelevant (x * N)
          (maynardDyadicBlockObservationRadius x N R) X k box
    · have hupper : (groupedDyadicUpper q : ℝ) ≤ lambda * N := by
        apply le_of_not_gt
        intro hu
        exact hactual ⟨hblock.1, hblock.2.1.1, hu⟩
      by_cases hterm : heathBrownDyadicTermBox
          L X k box.m box.a box.b box.q n = 0
      · have hnotWindow : ¬ IsHeathBrownBoxWindowRelevant
            (lambda * N) X k box := by
          intro hwin
          exact hactual ⟨hblock.1, hwin⟩
        simp [hnotWindow, hblock, hterm]
      · have hlocal := upperSupported_heathBrownDyadicTermBox
          L X k box.m box.a box.b box.q n hterm
        have hnupper : (n : ℝ) ≤ lambda * N := by
          have hncore : n ≤ heathBrownDyadicCoreUpper
              (k - box.m) box.a box.b box.q := (Finset.mem_Icc.mp hlocal).2
          have hcore : (heathBrownDyadicCoreUpper
              (k - box.m) box.a box.b box.q : ℝ) ≤ lambda * N := by
            rw [← groupedDyadicUpper_heathBrownBoxFactorExponent_eq_coreUpper]
            exact hupper
          exact (by exact_mod_cast hncore : (n : ℝ) ≤
            (heathBrownDyadicCoreUpper
              (k - box.m) box.a box.b box.q : ℝ)).trans hcore
        have hplus := smoothWeight_eq_one hwidth
          (show (n : ℝ) ≤ lambda * N + lambda * W by linarith)
        have hbase := smoothWeight_eq_one hwidth hnupper
        have hzero : routeTSmoothWindowWeight
            (lambda * N) (lambda * W) (n : ℝ) = 0 := by
          rw [routeTSmoothWindowWeight, hplus, hbase, sub_self]
        simp [hblock, hzero]
    · simp [hactual, hblock]

/-- A moving window-relevant packet is coefficient-exactly replaced by the fixed left-base
window-relevant packet throughout a dyadic physical block.  Boxes visible only at the left base
are supported below every later physical base and hence vanish against the adjacent-window weight. -/
theorem complexCoeff_windowRelevant_mul_scaled_routeWeight_eq_leftWindowRelevant
    (L X k : ℕ) (T t : ℝ) {x lambda N W : ℝ}
    (hx : 0 < x) (hlambda : lambda ∈ Set.Icc x (2 * x))
    (hN : 0 < N) (hW : 0 < W) (n : ℕ) :
    complexCoeff (heathBrownWindowRelevantEligiblePacket
        L X k T t (lambda * N)) n *
        ((routeTSmoothWindowWeight (lambda * N) (lambda * W) (n : ℝ) : ℝ) : ℂ) =
      complexCoeff (heathBrownWindowRelevantEligiblePacket
        L X k T t (x * N)) n *
        ((routeTSmoothWindowWeight (lambda * N) (lambda * W) (n : ℝ) : ℝ) : ℂ) := by
  classical
  have hlambdaPos : 0 < lambda := hx.trans_le hlambda.1
  have hwidth : 0 < lambda * W := mul_pos hlambdaPos hW
  have hbaseMono : x * N ≤ lambda * N :=
    mul_le_mul_of_nonneg_right hlambda.1 hN.le
  rw [complexCoeff_apply, complexCoeff_apply]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [heathBrownWindowRelevantEligiblePacket,
    heathBrownWindowRelevantEligiblePacket,
    arithmeticFunction_sum_apply_block,
    arithmeticFunction_sum_apply_block]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro box hbox
  let q := heathBrownBoxFactorExponent box.a box.b box.q
  by_cases hactual : IsHeathBrownBoxEligible L X k T t box ∧
      IsHeathBrownBoxWindowRelevant (lambda * N) X k box
  · have hfixed : IsHeathBrownBoxEligible L X k T t box ∧
        IsHeathBrownBoxWindowRelevant (x * N) X k box :=
      ⟨hactual.1, hactual.2.1, hbaseMono.trans_lt hactual.2.2⟩
    simp [hactual, hfixed]
  · by_cases hfixed : IsHeathBrownBoxEligible L X k T t box ∧
        IsHeathBrownBoxWindowRelevant (x * N) X k box
    · have hupper : (groupedDyadicUpper q : ℝ) ≤ lambda * N := by
        apply le_of_not_gt
        intro hu
        exact hactual ⟨hfixed.1, hfixed.2.1, hu⟩
      by_cases hterm : heathBrownDyadicTermBox
          L X k box.m box.a box.b box.q n = 0
      · have hnotWindow : ¬ IsHeathBrownBoxWindowRelevant
            (lambda * N) X k box := by
          intro hwin
          exact hactual ⟨hfixed.1, hwin⟩
        simp [hnotWindow, hfixed, hterm]
      · have hlocal := upperSupported_heathBrownDyadicTermBox
          L X k box.m box.a box.b box.q n hterm
        have hnupper : (n : ℝ) ≤ lambda * N := by
          have hncore : n ≤ heathBrownDyadicCoreUpper
              (k - box.m) box.a box.b box.q := (Finset.mem_Icc.mp hlocal).2
          have hcore : (heathBrownDyadicCoreUpper
              (k - box.m) box.a box.b box.q : ℝ) ≤ lambda * N := by
            rw [← groupedDyadicUpper_heathBrownBoxFactorExponent_eq_coreUpper]
            exact hupper
          exact (by exact_mod_cast hncore : (n : ℝ) ≤
            (heathBrownDyadicCoreUpper
              (k - box.m) box.a box.b box.q : ℝ)).trans hcore
        have hplus := smoothWeight_eq_one hwidth
          (show (n : ℝ) ≤ lambda * N + lambda * W by linarith)
        have hbase := smoothWeight_eq_one hwidth hnupper
        have hzero : routeTSmoothWindowWeight
            (lambda * N) (lambda * W) (n : ℝ) = 0 := by
          rw [routeTSmoothWindowWeight, hplus, hbase, sub_self]
        simp [hfixed, hzero]
    · simp [hactual, hfixed]

end RHTower.Sieve
