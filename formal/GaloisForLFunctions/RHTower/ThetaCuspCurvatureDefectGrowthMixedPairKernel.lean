import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthMixedPairMoments
/-! The exact mixed-pair transfer derivative is absorbed by the deep-atom
Wronskian throughout q >= 3/2, d >= 8. No source positivity is assumed. -/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
noncomputable section

open Filter Set Topology

theorem hasDerivAt_mixedPairShiftValue (k : ℕ) (y : ℝ) :
    HasDerivAt (mixedPairShiftValue k) (mixedPairShiftJet k y) y := by
  unfold mixedPairShiftValue mixedPairShiftJet atomGapPolyEval atomGapPolyJet
  apply HasDerivAt.fun_sum
  intro j hj
  simpa only [mul_assoc] using (hasDerivAt_pow j y).const_mul (mixedPairShiftCoeff k j)

theorem hasDerivAt_mixedPairTransferCoeff (q : ℝ) (k : ℕ) (hk : k ≤ 9) :
    HasDerivAt (fun r => mixedPairTransferCoeff r k) (mixedPairShiftJet k (q-3/2)) q := by
  have h := (hasDerivAt_mixedPairShiftValue k (q-3/2)).comp q
    ((hasDerivAt_id q).sub_const (3/2))
  simp only [Function.comp_def,id_eq,mul_one] at h
  apply h.congr_of_eventuallyEq
  filter_upwards with r
  simpa only [show (3/2:ℝ)+(r-3/2)=r by ring] using
    mixedPairTransferCoeff_shift_eq (r-3/2) k hk

def mixedPairTransferNumeratorJet (q d : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 10, mixedPairShiftJet k (q-3/2)*(d-8)^k

theorem hasDerivAt_mixedPairTransferNumerator (q d : ℝ) :
    HasDerivAt (fun r => mixedPairTransferNumerator r d) (mixedPairTransferNumeratorJet q d) q := by
  have hs : HasDerivAt (fun r => ∑ k ∈ Finset.range 10, mixedPairTransferCoeff r k*(d-8)^k)
      (mixedPairTransferNumeratorJet q d) q := by
    apply HasDerivAt.fun_sum
    intro k hk
    exact (hasDerivAt_mixedPairTransferCoeff q k
      (by have := Finset.mem_range.mp hk; omega)).mul_const _
  apply hs.congr_of_eventuallyEq
  filter_upwards with r
  simpa only [show (8:ℝ)+(d-8)=d by ring] using mixedPairTransferNumerator_gap_expansion r (d-8)

theorem mixedPairTransferNumerator_gap_shift_expansion (y v : ℝ) :
    mixedPairTransferNumerator (3/2+y) (8+v)=
      ∑ k ∈ Finset.range 10, mixedPairShiftValue k y*v^k := by
  rw [mixedPairTransferNumerator_gap_expansion]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mixedPairTransferCoeff_shift_eq y k (by have := Finset.mem_range.mp hk; omega)]

def mixedPairTransferNextNumerator (q d : ℝ) : ℝ :=
  ((d-3)*mixedPairTransferNumerator q d-mixedPairTransferNumeratorJet q d)*dominantPairPolynomial q+
    mixedPairTransferNumerator q d*dominantPairPolynomialJet q

private theorem mixedPair_value_ten (y : ℝ) : mixedPairShiftValue 10 y=0 := by
  simp [mixedPairShiftValue,atomGapPolyEval,mixedPairShiftCoeff]

private theorem mixedPair_jet_ten (y : ℝ) : mixedPairShiftJet 10 y=0 := by
  simp [mixedPairShiftJet,atomGapPolyJet,mixedPairShiftCoeff]

private theorem atomGap_value_ten (y : ℝ) : atomGapShiftValue 10 y=0 := by
  simp [atomGapShiftValue,atomGapPolyEval,atomGapShiftCoeff]

private theorem atomGap_jet_ten (y : ℝ) : atomGapShiftJet 10 y=0 := by
  simp [atomGapShiftJet,atomGapPolyJet,atomGapShiftCoeff]

theorem mixedPairTransferNextNumerator_gap_expansion (y v : ℝ) :
    mixedPairTransferNextNumerator (3/2+y) (8+v)=
      ∑ k ∈ Finset.range 11, mixedPairNextShiftCoeff k y*v^k := by
  unfold mixedPairTransferNextNumerator
  rw [mixedPairTransferNumerator_gap_shift_expansion]
  unfold mixedPairTransferNumeratorJet mixedPairNextShiftCoeff
  rw [dominantPairPolynomial_gap_shift_eq,dominantPairPolynomialJet_gap_shift_eq]
  rw [show (3/2:ℝ)+y-3/2=y by ring,show (8:ℝ)+v-8=v by ring]
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.reduceSub,
    OfNat.zero_ne_ofNat,ite_false,ite_true,mixedPair_value_ten,mixedPair_jet_ten]
  ring

theorem atomPairTransferWronskian_next_expansion (y v : ℝ) :
    atomPairTransferWronskian (3/2+y) (8+v)=
      ∑ k ∈ Finset.range 11, atomGapNextShiftCoeff k y*v^k := by
  rw [atomPairTransferWronskian_gap_shift_expansion,
    atomTransferNumerator_gap_shift_expansion,dominantPairPolynomial_gap_shift_eq]
  unfold atomGapNextShiftCoeff
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.reduceSub,
    OfNat.zero_ne_ofNat,ite_false,ite_true]
  have hz : atomGapShiftWronskian 10 y=0 := by
    simp [atomGapShiftWronskian,atomGap_value_ten,atomGap_jet_ten]
  rw [hz]
  ring

theorem mixedPairTransferNextNumerator_absorption {q d : ℝ} (hq : 3/2 ≤ q) (hd : 8 ≤ d) :
    q*mixedPairTransferNextNumerator q d <
      256*polynomialMoment q 3 0*atomPairTransferWronskian q d := by
  let y := q-3/2
  let v := d-8
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have hqeq : q=3/2+y := by dsimp [y]; ring
  have hdeq : d=8+v := by dsimp [v]; ring
  have hs : 0 < ∑ k ∈ Finset.range 11, mixedPairShiftReserve k y*v^k := by
    apply Finset.sum_pos'
    · intro k hk
      exact mul_nonneg (mixedPairShiftReserve_pos y hy k
        (by have := Finset.mem_range.mp hk; omega)).le (pow_nonneg hv k)
    · exact ⟨0,by simp,by simpa using mixedPairShiftReserve_pos y hy 0 (by omega)⟩
  apply sub_pos.mp
  rw [hqeq,hdeq,atomPairTransferWronskian_next_expansion,mixedPairTransferNextNumerator_gap_expansion]
  have hm : polynomialMoment (3/2+y) 3 0=4*(3/2+y)+9/2 := by
    norm_num [polynomialMoment,Finset.sum_range_succ,Nat.choose,Nat.factorial]
  rw [hm]
  calc
    0 < ∑ k ∈ Finset.range 11, mixedPairShiftReserve k y*v^k := hs
    _ = _ := by
      unfold mixedPairShiftReserve
      simp only [sub_mul,mul_assoc,Finset.sum_sub_distrib,Finset.mul_sum]

end
end RHTower.ThetaCuspDefect
