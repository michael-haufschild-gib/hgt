import GaloisForLFunctions.ArithmeticIndexDescent.TheCriticalRateClassifiesAllOffLineSupport

/-!
# Critical source work pays every negative square

Finite packets of right-hand zero copies retain their entire height-square
charge in the critically rescaled source increment. The actual Pontryagin
bound supplies such a packet for every finite smooth Weil negative index.
The certified arithmetic off-line height floor supplies the cost per negative square.
This is a source lower bound; no arithmetic upper budget is assumed.
-/

noncomputable section

open Filter Finset Set RHTower Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticElectrostatics
open GaloisForLFunctions.ArithmeticCorrespondencePositivity
open scoped Topology

namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- Height-square charge of a finite right-hand multiplicity packet. -/
def rightPacketQuadraticCharge (s : Finset RightXiZeroCopy) : ℝ :=
  (3 / 2 : ℝ) * ∑ p ∈ s, xiZeroHeight p.1 ^ 2

theorem rightPacket_quadratic_damping_tendsto (s : Finset RightXiZeroCopy) :
    Tendsto (fun R : ℝ => R ^ 2 * ∑ p ∈ s,
      (heightDamping (2 * R) (xiZeroHeight p.1) - heightDamping R (xiZeroHeight p.1)))
      atTop (𝓝 (rightPacketQuadraticCharge s)) := by
  simpa only [rightPacketQuadraticCharge, Finset.mul_sum] using
    tendsto_finsetSum s (fun p _ => heightDamping_quadraticGap_tendsto (xiZeroHeight p.1))

/-- The actual full pair sum pays a packet before either source limit is taken. -/
theorem rightPacket_quadratic_damping_le (s : Finset RightXiZeroCopy)
    {R : ℝ} (hR : 4 ≤ R) :
    R ^ 2 * (∑ p ∈ s,
      (heightDamping (2 * R) (xiZeroHeight p.1) - heightDamping R (xiZeroHeight p.1))) ≤
      quadraticWorkIncrement R :=
  mul_le_mul_of_nonneg_left
    (sum_damping_increment_le_sourceWork_increment s hR (by linarith only [hR]))
    (sq_nonneg R)

/-- Every amount below the packet's height-square charge is eventually visible in source work. -/
theorem eventually_lt_quadraticIncrement_of_lt_packetCharge (s : Finset RightXiZeroCopy)
    {b : ℝ} (hb : b < rightPacketQuadraticCharge s) :
    ∀ᶠ R : ℝ in atTop, b < quadraticWorkIncrement R := by
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    (rightPacket_quadratic_damping_tendsto s).eventually (lt_mem_nhds hb)] with R hR h
  exact h.trans_le (rightPacket_quadratic_damping_le s hR)

/-- The certified arithmetic height floor supplies a uniform charge for each right-hand copy. -/
theorem indexUnit_card_le_rightPacketCharge (s : Finset RightXiZeroCopy) :
    quadraticIndexUnit * (s.card : ℝ) ≤ rightPacketQuadraticCharge s := by
  have hp (p : RightXiZeroCopy) : xiOrderTwentyThreeOptimizedHeightSq ≤ xiZeroHeight p.1 ^ 2 := by
    have hoff : (p.1.1 : ℂ).re ≠ 1 / 2 :=
      (show 1 / 2 < (p.1.1 : ℂ).re from sub_pos.mp p.2).ne'
    exact orderTwentyThreeOptimizedHeightSq_le_im_sq_of_xiZeroCopy_offLine p.1 hoff
  have hsum : xiOrderTwentyThreeOptimizedHeightSq * (s.card : ℝ) ≤
      ∑ p ∈ s, xiZeroHeight p.1 ^ 2 := by
    calc
      _ = ∑ _p ∈ s, xiOrderTwentyThreeOptimizedHeightSq := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum fun p _ => hp p
  unfold quadraticIndexUnit rightPacketQuadraticCharge
  linarith only [hsum]

/-- The complete finite source moment pays every finite right-hand packet. -/
theorem rightPacketCharge_le_sourceMoment (hfin : offLineSupport.Finite)
    (s : Finset RightXiZeroCopy) :
    rightPacketQuadraticCharge s ≤ quadraticPacketSourceMoment
      (offLineCopies_finite_of_offLineSupport_finite hfin).toFinset := by
  by_contra! hlt
  let M := quadraticPacketSourceMoment
    (offLineCopies_finite_of_offLineSupport_finite hfin).toFinset
  have hb : (M + rightPacketQuadraticCharge s) / 2 < rightPacketQuadraticCharge s := by
    change M < rightPacketQuadraticCharge s at hlt
    linarith only [hlt]
  have hlow := ge_of_tendsto (quadraticWorkIncrement_tendsto_sourceMoment hfin)
    ((eventually_lt_quadraticIncrement_of_lt_packetCharge s hb).mono fun _ h => h.le)
  change (M + rightPacketQuadraticCharge s) / 2 ≤ M at hlow
  change M < rightPacketQuadraticCharge s at hlt
  linarith only [hlt, hlow]

/-- Every finite Weil negative index has an actual packet of right-hand Xi copies. -/
theorem exists_rightCopy_packet_of_weilGram {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    ∃ s : Finset RightXiZeroCopy,
      s.card = hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) := by
  classical
  let k := hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f)
  let R : Set ℂ := {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}
  have hk : (k : ℕ∞) ≤ R.encard := negIndex_weilGram_le_offLineCount f hf hfc
  obtain ⟨s, hs, hcard⟩ : ∃ s : Finset ℂ, (↑s : Set ℂ) ⊆ R ∧ s.card = k := by
    rcases R.finite_or_infinite with hR | hR
    · rw [hR.encard_eq_coe_toFinset_card] at hk
      obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (ENat.coe_le_coe.mp hk)
      exact ⟨s, fun ρ hρ => hR.mem_toFinset.mp (hs hρ), hcard⟩
    · exact hR.exists_subset_card_eq k
  let j : s → XiDivisorSupport := fun ρ =>
    xiDivisorZetaCarrierEquiv.symm ⟨ρ, (hs ρ.property).1⟩
  let p : s → RightXiZeroCopy := fun ρ =>
    ⟨firstZeroCopy (j ρ), sub_pos.mpr (hs ρ.property).2⟩
  have hp : Function.Injective p := by
    intro a b hab
    exact Subtype.ext (congrArg (fun q : RightXiZeroCopy => (q.1.1 : ℂ)) hab)
  refine ⟨s.attach.image p, ?_⟩
  rw [Finset.card_image_of_injective _ hp, Finset.card_attach]
  exact hcard

/-- Each negative square pays the certified arithmetic unit at the critical source rate. -/
theorem eventually_lt_quadraticIncrement_of_lt_negIndex {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) {b : ℝ}
    (hb : b < quadraticIndexUnit * (hermNegIndex
      (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) : ℝ)) :
    ∀ᶠ R : ℝ in atTop, b < quadraticWorkIncrement R := by
  obtain ⟨s, hcard⟩ := exists_rightCopy_packet_of_weilGram f hf hfc
  apply eventually_lt_quadraticIncrement_of_lt_packetCharge s
  apply hb.trans_le
  rw [← hcard]
  exact indexUnit_card_le_rightPacketCharge s

/-- The index charge is visible in finite Laurent-source readings, with damping chosen first. -/
theorem eventually_eventually_quadraticSourceWork_pays_negIndex {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) {b : ℝ}
    (hb : b < quadraticIndexUnit * (hermNegIndex
      (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) : ℝ)) :
    ∀ᶠ R : ℝ in atTop, ∀ᶠ N : ℕ in atTop,
      b < R ^ 2 * (xiTaperedSourceWork (2 * R) N - xiTaperedSourceWork R N) := by
  filter_upwards [eventually_lt_quadraticIncrement_of_lt_negIndex f hf hfc hb,
    eventually_ge_atTop (4 : ℝ)] with R h hR
  exact (quadraticTaperedSourceWork_tendsto hR).eventually (lt_mem_nhds h)

/-- On the finite stratum, the exact full-source moment pays every finite smooth Weil index. -/
theorem indexUnit_mul_negIndex_le_sourceMoment (hfin : offLineSupport.Finite)
    {ι : Type*} [Fintype ι] (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    quadraticIndexUnit * (hermNegIndex
      (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) : ℝ) ≤
      quadraticPacketSourceMoment
        (offLineCopies_finite_of_offLineSupport_finite hfin).toFinset := by
  obtain ⟨s, hcard⟩ := exists_rightCopy_packet_of_weilGram f hf hfc
  rw [← hcard]
  exact (indexUnit_card_le_rightPacketCharge s).trans (rightPacketCharge_le_sourceMoment hfin s)

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_rightCopy_packet_of_weilGram
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.eventually_lt_quadraticIncrement_of_lt_negIndex
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.eventually_eventually_quadraticSourceWork_pays_negIndex
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.indexUnit_mul_negIndex_le_sourceMoment
