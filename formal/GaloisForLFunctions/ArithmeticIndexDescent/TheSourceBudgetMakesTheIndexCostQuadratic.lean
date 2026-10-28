import GaloisForLFunctions.ArithmeticIndexDescent.TheCriticalRatePaysEveryNegativeSquare
import GaloisForLFunctions.RHTower.XiWardCriticalBudgetProbe
import GaloisForLFunctions.RHTower.Sieve.HarmonicCauchySchwarz

/-!
# A global arithmetic budget makes index cost quadratic

The actual strip-edge resolvent mass is at most 3/50. A right-hand packet
and its disjoint reflections spend twice the packet mass. The resulting
reciprocal-height budget, combined with weighted Cauchy--Schwarz, makes k
right copies cost at least 50k² - 3k/2 at the critical source rate.
This strengthens a forcing law; it supplies no upper bound on normal work.
-/

noncomputable section

open Filter Finset Set RHTower Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticElectrostatics
open GaloisForLFunctions.ArithmeticCorrespondencePositivity
open scoped Topology

namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- Every right-hand packet spends at most half the certified global reciprocal-height budget. -/
theorem rightPacket_inverseHeight_budget (s : Finset RightXiZeroCopy) :
    (∑ p ∈ s, 1 / (xiZeroHeight p.1 ^ 2 + 1)) ≤ (3 / 100 : ℝ) := by
  classical
  let m : XiZeroCopy → ℝ := xiBudgetMassAt (1 / 2)
  let e : RightXiZeroCopy × Bool → XiZeroCopy := fun pb => rightCopyVertex pb.1 pb.2
  have he : Function.Injective e := rightCopyVertex_injective
  have hm : Summable m := summable_xiBudgetMassAt xi_probe_half_ne_zero
  have hsum := hm.sum_le_tsum ((s ×ˢ (univ : Finset Bool)).image e)
    (fun q _ => xiBudgetMassAt_nonneg (by norm_num) q)
  rw [Finset.sum_image he.injOn, Finset.sum_product] at hsum
  have hmass (p : RightXiZeroCopy) (b : Bool) : m (e (p, b)) = m p.1 := by
    cases b <;> simp only [e, m, rightCopyVertex, Bool.false_eq_true, if_false, if_true,
      massAt_lineConj]
  have hdouble : (∑ p ∈ s, ∑ b ∈ (univ : Finset Bool), m (e (p, b))) =
      2 * ∑ p ∈ s, m p.1 := by
    simp [hmass, ← Finset.mul_sum]
  rw [hdouble] at hsum
  have htwo : 2 * (∑ p ∈ s, m p.1) ≤ (3 / 50 : ℝ) := hsum.trans tsum_massAt_half_le
  have hfloor (p : RightXiZeroCopy) : 1 / (xiZeroHeight p.1 ^ 2 + 1) ≤ m p.1 := by
    have h := xiBudgetMassAt_ge (c := 1 / 2) (by norm_num) p.1
    norm_num [xiSpectralPoint_re_eq] at h
    simpa only [m, xiZeroHeight, one_div] using h
  have hlow := Finset.sum_le_sum (fun p (_hp : p ∈ s) => hfloor p)
  linarith only [htwo, hlow]

/-- Index charge forced by the full strip-edge arithmetic resolvent budget. -/
def resolventIndexCharge (k : ℕ) : ℝ := 50 * (k : ℝ) ^ 2 - (3 / 2 : ℝ) * k

/-- Weighted Cauchy--Schwarz converts reciprocal mass control into a quadratic height cost. -/
theorem resolventIndexCharge_le_packetCharge (s : Finset RightXiZeroCopy) :
    resolventIndexCharge s.card ≤ rightPacketQuadraticCharge s := by
  have hcs := RHTower.Sieve.normSq_sum_le_weighted s
    (fun p : RightXiZeroCopy => xiZeroHeight p.1 ^ 2 + 1)
    (fun _ _ => by positivity) (fun _ => (1 : ℂ))
  have hcard : (s.card : ℝ) ^ 2 ≤
      (∑ p ∈ s, 1 / (xiZeroHeight p.1 ^ 2 + 1)) *
        ((∑ p ∈ s, xiZeroHeight p.1 ^ 2) + (s.card : ℝ)) := by
    simpa [Finset.sum_add_distrib] using hcs
  have hpaid := hcard.trans (mul_le_mul_of_nonneg_right (rightPacket_inverseHeight_budget s)
    (show 0 ≤ (∑ p ∈ s, xiZeroHeight p.1 ^ 2) + (s.card : ℝ) by positivity))
  unfold resolventIndexCharge rightPacketQuadraticCharge
  nlinarith only [hpaid]

/-- Each finite smooth Weil index forces its full quadratic resolvent charge in normal source work. -/
theorem eventually_lt_quadraticIncrement_of_lt_resolventIndexCharge
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) {b : ℝ}
    (hb : b < resolventIndexCharge
      (hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f))) :
    ∀ᶠ R : ℝ in atTop, b < quadraticWorkIncrement R := by
  obtain ⟨s, hcard⟩ := exists_rightCopy_packet_of_weilGram f hf hfc
  apply eventually_lt_quadraticIncrement_of_lt_packetCharge s
  rw [← hcard] at hb
  exact hb.trans_le (resolventIndexCharge_le_packetCharge s)

/-- The finite full-source moment pays the quadratic index charge. -/
theorem resolventIndexCharge_le_sourceMoment (hfin : offLineSupport.Finite)
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    resolventIndexCharge
      (hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f)) ≤
      quadraticPacketSourceMoment
        (offLineCopies_finite_of_offLineSupport_finite hfin).toFinset := by
  obtain ⟨s, hcard⟩ := exists_rightCopy_packet_of_weilGram f hf hfc
  rw [← hcard]
  exact (resolventIndexCharge_le_packetCharge s).trans (rightPacketCharge_le_sourceMoment hfin s)

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.rightPacket_inverseHeight_budget
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.resolventIndexCharge_le_packetCharge
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.eventually_lt_quadraticIncrement_of_lt_resolventIndexCharge
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.resolventIndexCharge_le_sourceMoment
