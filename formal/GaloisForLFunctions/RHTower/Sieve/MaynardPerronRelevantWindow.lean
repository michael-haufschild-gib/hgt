import GaloisForLFunctions.RHTower.Sieve.MaynardEligibleWindowPerron
import GaloisForLFunctions.RHTower.Sieve.MaynardPerronRelevantAggregate

/-!
# Perron-relevant Route-T window

The pointwise aggregate used for large-value selection must contain only boxes visible through the
Perron cutoff.  This module proves that recut coefficient-exactly under each smooth weight and
replaces the eligible aggregate by the eligible-and-relevant aggregate in the adjacent-window
identity.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

/-- Arithmetic packet containing exactly eligible boxes whose lower edge reaches the prefix. -/
def heathBrownPerronRelevantEligiblePacket
    (L X k : ℕ) (T0 t : ℝ) : ArithmeticFunction ℝ := by
  classical
  exact ∑ box : HeathBrownBoxChoice L X k,
    if IsHeathBrownBoxEligible L X k T0 t box ∧
        IsHeathBrownBoxPerronRelevant X k box then
      heathBrownDyadicTermBox L X k box.m box.a box.b box.q
    else 0

private theorem arithmeticFunction_sum_apply_relevant
    {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (F : ι → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ u, F i) n = ∑ i ∈ u, F i n := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [ArithmeticFunction.zero_apply]
  | @insert a u ha ih => simp [ha, ih, ArithmeticFunction.add_apply]

/-- Below the prefix cutoff, removing Perron-invisible boxes changes no coefficient. -/
theorem heathBrownEligiblePacket_apply_eq_perronRelevant
    (L X k : ℕ) (T0 t : ℝ) {n : ℕ} (hn : n ≤ X) :
    heathBrownEligiblePacket L X k T0 t n =
      heathBrownPerronRelevantEligiblePacket L X k T0 t n := by
  classical
  rw [heathBrownEligiblePacket, heathBrownPerronRelevantEligiblePacket,
    arithmeticFunction_sum_apply_relevant, arithmeticFunction_sum_apply_relevant]
  apply Finset.sum_congr rfl
  intro box _hbox
  by_cases helig : IsHeathBrownBoxEligible L X k T0 t box
  · by_cases hrel : IsHeathBrownBoxPerronRelevant X k box
    · simp [helig, hrel]
    · have hXlt : X < groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) :=
        Nat.lt_of_not_ge hrel
      rw [groupedDyadicLower_heathBrownBoxFactorExponent_eq_coreLower] at hXlt
      have hzero := vanishesBelow_heathBrownDyadicTermBox
        L X k box.m box.a box.b box.q n (hn.trans_lt hXlt)
      simp [helig, hrel, hzero]
  · simp [helig]

/-- L-series of the recut packet is exactly the recut pointwise aggregate. -/
theorem LSeries_heathBrownPerronRelevantEligiblePacket
    (L X k : ℕ) (T0 t : ℝ) (s : ℂ) :
    LSeries (complexCoeff (heathBrownPerronRelevantEligiblePacket L X k T0 t)) s =
      heathBrownPerronRelevantEligibleDyadicAggregate L X k T0 t s := by
  classical
  rw [heathBrownPerronRelevantEligiblePacket, complexCoeff_sum, LSeries_sum]
  · simp only [heathBrownPerronRelevantEligibleDyadicAggregate]
    apply Finset.sum_congr rfl
    intro box _hbox
    by_cases h : IsHeathBrownBoxEligible L X k T0 t box ∧
        IsHeathBrownBoxPerronRelevant X k box
    · simp [h, heathBrownBoxTerm]
      exact LSeries_heathBrownDyadicTermBox
        L X k box.m box.a box.b box.q s
    · simp only [h, if_false]
      have hzero : complexCoeff (0 : ArithmeticFunction ℝ) = 0 := by
        funext n
        simp [complexCoeff_apply]
      rw [hzero]
      exact congrFun LSeries_zero s
  · intro box _hbox
    by_cases h : IsHeathBrownBoxEligible L X k T0 t box ∧
        IsHeathBrownBoxPerronRelevant X k box
    · simp only [h]
      exact LSeriesSummable_complexCoeff_heathBrownDyadicTermBox
        L X k box.m box.a box.b box.q s
    · simp only [h, if_false]
      have hzero : complexCoeff (0 : ArithmeticFunction ℝ) = 0 := by
        funext n
        simp [complexCoeff_apply]
      rw [hzero]
      exact LSeriesSummable_zero

theorem LSeriesSummable_heathBrownPerronRelevantEligiblePacket
    (L X k : ℕ) (T0 t : ℝ) (s : ℂ) :
    LSeriesSummable
      (complexCoeff (heathBrownPerronRelevantEligiblePacket L X k T0 t)) s := by
  classical
  rw [heathBrownPerronRelevantEligiblePacket, complexCoeff_sum]
  apply LSeriesSummable.sum
  intro box _hbox
  by_cases h : IsHeathBrownBoxEligible L X k T0 t box ∧
      IsHeathBrownBoxPerronRelevant X k box
  · simp only [h]
    exact LSeriesSummable_complexCoeff_heathBrownDyadicTermBox
      L X k box.m box.a box.b box.q s
  · simp only [h, if_false]
    have hzero : complexCoeff (0 : ArithmeticFunction ℝ) = 0 := by
      funext n
      simp [complexCoeff_apply]
    rw [hzero]
    exact LSeriesSummable_zero

/-- Smoothed Perron identity for the recut packet. -/
theorem smul_tsum_heathBrownPerronRelevantEligiblePacket_smoothWeight_eq_integral
    (L X k : ℕ) (T0 t : ℝ) {N H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsigma : 1 < sigma) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
      complexCoeff (heathBrownPerronRelevantEligiblePacket L X k T0 t) n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∫ y : ℝ,
        heathBrownPerronRelevantEligibleDyadicAggregate L X k T0 t
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
  let F := heathBrownPerronRelevantEligiblePacket L X k T0 t
  have hF0 : complexCoeff F 0 = 0 := by
    classical
    have hpacket : F 0 = 0 := by
      dsimp only [F]
      rw [heathBrownPerronRelevantEligiblePacket,
        arithmeticFunction_sum_apply_relevant]
      apply Finset.sum_eq_zero
      intro box _hbox
      by_cases h : IsHeathBrownBoxEligible L X k T0 t box ∧
          IsHeathBrownBoxPerronRelevant X k box
      · simp only [h]
        by_contra hterm
        have hmem := upperSupported_heathBrownDyadicTermBox
          L X k box.m box.a box.b box.q 0 hterm
        simp at hmem
      · simp [h]
    simp [complexCoeff_apply, hpacket]
  have hsum : Summable fun n : ℕ => ‖complexCoeff F n‖ * (n : ℝ) ^ (-sigma) :=
    summable_norm_mul_rpow_of_LSeriesSummable (by linarith)
      (LSeriesSummable_heathBrownPerronRelevantEligiblePacket
        L X k T0 t (sigma : ℂ))
  have hperron := tsum_mul_smoothWeight_eq_integral_summable
    (a := complexCoeff F) hF0 hN hH hsigma hsum
  rw [hperron]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  congr 1
  rw [tsum_cpow_neg_eq_LSeries hF0]
  exact LSeries_heathBrownPerronRelevantEligiblePacket
    L X k T0 t ((sigma : ℂ) + (y : ℝ) * I)

/-- Every compactly supported smooth coefficient sum is unchanged by the Perron recut. -/
theorem tsum_heathBrownEligiblePacket_smoothWeight_eq_perronRelevant
    (L X k : ℕ) (T0 t : ℝ) {N H : ℝ}
    (hH : 0 < H) (hsupport : N + H ≤ X) :
    (∑' n : ℕ, complexCoeff (heathBrownEligiblePacket L X k T0 t) n *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∑' n : ℕ,
        complexCoeff (heathBrownPerronRelevantEligiblePacket L X k T0 t) n *
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ) := by
  apply tsum_congr
  intro n
  by_cases hn : n ≤ X
  · rw [complexCoeff_apply, complexCoeff_apply,
      heathBrownEligiblePacket_apply_eq_perronRelevant L X k T0 t hn]
  · have hXn : (X : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_not_ge hn
    have hge : N + H ≤ (n : ℝ) := hsupport.trans hXn
    rw [GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero hH hge]
    simp

/-- Mellin integral is unchanged after removing every box lying beyond the prefix support. -/
theorem integral_heathBrownEligibleDyadicAggregate_eq_perronRelevant
    (L X k : ℕ) (T0 t : ℝ) {N H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsupport : N + H ≤ X)
    (hsigma : 1 < sigma) :
    (∫ y : ℝ,
      heathBrownEligibleDyadicAggregate L X k T0 t
          ((sigma : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) =
      ∫ y : ℝ,
        heathBrownPerronRelevantEligibleDyadicAggregate L X k T0 t
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
  rw [← smul_tsum_heathBrownEligiblePacket_smoothWeight_eq_integral
      L X k T0 t hN hH hsigma,
    ← smul_tsum_heathBrownPerronRelevantEligiblePacket_smoothWeight_eq_integral
      L X k T0 t hN hH hsigma,
    tsum_heathBrownEligiblePacket_smoothWeight_eq_perronRelevant
      L X k T0 t hH hsupport]

/-- **Exact Perron-relevant adjacent-window formula.**  Large-value selection can now occur in the
same finite aggregate that actually contributes to the smooth prime window. -/
theorem tsum_vonMangoldt_smoothWindow_eq_integral_heathBrownPerronRelevantEligibleAggregate
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T0 t N H sigma : ℝ}
    (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N)
    (hN : 0 < N) (hH : 0 < H) (hsupport : N + 2 * H ≤ X)
    (hsigma : 1 < sigma) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
        (((GaloisForLFunctions.HTGeometry.smoothWeight
            (N + H) H (n : ℝ) : ℝ) : ℂ) -
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))) =
      (∫ y : ℝ,
        heathBrownPerronRelevantEligibleDyadicAggregate L X k T0 t
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I)) -
      ∫ y : ℝ,
        heathBrownPerronRelevantEligibleDyadicAggregate L X k T0 t
            ((sigma : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I) := by
  have hwindow :=
    tsum_vonMangoldt_smoothWindow_eq_integral_heathBrownEligibleDyadicAggregate
      L X k hXL hT0 hscale hN hH hsupport hsigma
  have hplusSupport : (N + H) + H ≤ (X : ℝ) := by linarith
  have hbaseSupport : N + H ≤ (X : ℝ) := by linarith
  have hplus := integral_heathBrownEligibleDyadicAggregate_eq_perronRelevant
    L X k T0 t (N := N + H) (H := H) (sigma := sigma)
      (by linarith) hH hplusSupport hsigma
  have hbase := integral_heathBrownEligibleDyadicAggregate_eq_perronRelevant
    L X k T0 t (N := N) (H := H) (sigma := sigma)
      hN hH hbaseSupport hsigma
  rw [hplus, hbase] at hwindow
  exact hwindow

end RHTower.Sieve
