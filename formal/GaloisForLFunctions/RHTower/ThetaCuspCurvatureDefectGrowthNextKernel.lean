import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthAtomGapCooling
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthNextKernelPolynomial
/-!
# Positive next transfer kernel on the cubic spectral support

The exact kernel for cooling relative to the dominant self-pair is
strictly positive for q >= 3/2 and t >= 9. Finite coefficient identities
and derivative uniqueness connect the source kernel to the positive
shifted certificate. This supplies the stable sign for every cubic and
higher convolution sector; their alternating absorption remains open.
-/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
open Filter Set Topology
noncomputable section

def shiftedTransferCoeff (q : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range 6,
    ((growthCoefficient q (i+2)*slopeNumerator q 3-q*growthCoefficientJet q (i+2)*growthNumerator q 3)*
        ((i+2).choose k:ℝ)*9^(i+2-k)+
      q*growthCoefficient q (i+2)*growthNumerator q 3*((i+3).choose k:ℝ)*9^(i+3-k))

theorem growthTransferKernel_nine_add_expansion (q v : ℝ) :
    growthTransferKernel q (9+v)=∑ k ∈ Finset.range 9, shiftedTransferCoeff q k*v^k := by
  unfold growthTransferKernel growthScore growthScoreJet shiftedTransferCoeff
  norm_num [Finset.sum_range_succ,Nat.choose]
  ring

theorem shiftedTransferCoeff_shift_0 (y : ℝ) :
    shiftedTransferCoeff (3/2+y) 0=pairKernelShiftValue 0 y := by
  unfold shiftedTransferCoeff growthNumerator slopeNumerator pairKernelShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [pairKernelShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedTransferCoeff_shift_1 (y : ℝ) :
    shiftedTransferCoeff (3/2+y) 1=pairKernelShiftValue 1 y := by
  unfold shiftedTransferCoeff growthNumerator slopeNumerator pairKernelShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [pairKernelShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedTransferCoeff_shift_2 (y : ℝ) :
    shiftedTransferCoeff (3/2+y) 2=pairKernelShiftValue 2 y := by
  unfold shiftedTransferCoeff growthNumerator slopeNumerator pairKernelShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [pairKernelShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedTransferCoeff_shift_3 (y : ℝ) :
    shiftedTransferCoeff (3/2+y) 3=pairKernelShiftValue 3 y := by
  unfold shiftedTransferCoeff growthNumerator slopeNumerator pairKernelShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [pairKernelShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedTransferCoeff_shift_4 (y : ℝ) :
    shiftedTransferCoeff (3/2+y) 4=pairKernelShiftValue 4 y := by
  unfold shiftedTransferCoeff growthNumerator slopeNumerator pairKernelShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [pairKernelShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedTransferCoeff_shift_5 (y : ℝ) :
    shiftedTransferCoeff (3/2+y) 5=pairKernelShiftValue 5 y := by
  unfold shiftedTransferCoeff growthNumerator slopeNumerator pairKernelShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [pairKernelShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedTransferCoeff_shift_6 (y : ℝ) :
    shiftedTransferCoeff (3/2+y) 6=pairKernelShiftValue 6 y := by
  unfold shiftedTransferCoeff growthNumerator slopeNumerator pairKernelShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [pairKernelShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedTransferCoeff_shift_7 (y : ℝ) :
    shiftedTransferCoeff (3/2+y) 7=pairKernelShiftValue 7 y := by
  unfold shiftedTransferCoeff growthNumerator slopeNumerator pairKernelShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [pairKernelShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedTransferCoeff_shift_8 (y : ℝ) :
    shiftedTransferCoeff (3/2+y) 8=pairKernelShiftValue 8 y := by
  unfold shiftedTransferCoeff growthNumerator slopeNumerator pairKernelShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [pairKernelShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedTransferCoeff_shift_eq (y : ℝ) (k : ℕ) (hk : k ≤ 8) :
    shiftedTransferCoeff (3/2+y) k=pairKernelShiftValue k y := by
  interval_cases k
  · exact shiftedTransferCoeff_shift_0 y
  · exact shiftedTransferCoeff_shift_1 y
  · exact shiftedTransferCoeff_shift_2 y
  · exact shiftedTransferCoeff_shift_3 y
  · exact shiftedTransferCoeff_shift_4 y
  · exact shiftedTransferCoeff_shift_5 y
  · exact shiftedTransferCoeff_shift_6 y
  · exact shiftedTransferCoeff_shift_7 y
  · exact shiftedTransferCoeff_shift_8 y

theorem hasDerivAt_pairKernelShiftValue (k : ℕ) (y : ℝ) :
    HasDerivAt (pairKernelShiftValue k) (pairKernelShiftJet k y) y := by
  unfold pairKernelShiftValue pairKernelShiftJet atomGapPolyEval atomGapPolyJet
  apply HasDerivAt.fun_sum
  intro j hj
  simpa only [mul_assoc] using (hasDerivAt_pow j y).const_mul (pairKernelShiftCoeff k j)

theorem hasDerivAt_shiftedTransferCoeff (q : ℝ) (k : ℕ) (hk : k ≤ 8) :
    HasDerivAt (fun r => shiftedTransferCoeff r k) (pairKernelShiftJet k (q-3/2)) q := by
  have h := (hasDerivAt_pairKernelShiftValue k (q-3/2)).comp q
    ((hasDerivAt_id q).sub_const (3/2))
  simp only [Function.comp_def,id_eq,mul_one] at h
  apply h.congr_of_eventuallyEq
  filter_upwards with r
  simpa only [show (3/2:ℝ)+(r-3/2)=r by ring] using
    shiftedTransferCoeff_shift_eq (r-3/2) k hk

theorem growthTransferKernel_shift_expansion (y v : ℝ) :
    growthTransferKernel (3/2+y) (9+v)=
      ∑ k ∈ Finset.range 9, pairKernelShiftValue k y*v^k := by
  rw [growthTransferKernel_nine_add_expansion]
  apply Finset.sum_congr rfl
  intro k hk
  rw [shiftedTransferCoeff_shift_eq y k (by have := Finset.mem_range.mp hk; omega)]

theorem growthTransferKernelJet_shift_expansion (y v : ℝ) :
    growthTransferKernelJet (3/2+y) (9+v)=
      ∑ k ∈ Finset.range 9, pairKernelShiftJet k y*v^k := by
  have hs : HasDerivAt (fun r => ∑ k ∈ Finset.range 9, shiftedTransferCoeff r k*v^k)
      (∑ k ∈ Finset.range 9, pairKernelShiftJet k ((3/2+y)-3/2)*v^k) (3/2+y) := by
    apply HasDerivAt.fun_sum
    intro k hk
    exact (hasDerivAt_shiftedTransferCoeff (3/2+y) k
      (by have := Finset.mem_range.mp hk; omega)).mul_const _
  have ha := hasDerivAt_growthTransferKernel (3/2+y) (9+v)
  have he : (fun r => growthTransferKernel r (9+v))=
      (fun r => ∑ k ∈ Finset.range 9, shiftedTransferCoeff r k*v^k) := by
    funext r
    exact growthTransferKernel_nine_add_expansion r v
  rw [he] at ha
  simpa only [show (3/2:ℝ)+y-3/2=y by ring] using ha.unique hs

def pairRelativeTransferKernel (q t : ℝ) : ℝ :=
  ((q*(t-6)-9)*growthTransferKernel q t-q*growthTransferKernelJet q t)*dominantPairPolynomial q+
    q*growthTransferKernel q t*dominantPairPolynomialJet q

theorem pairRelativeTransferKernel_shift_expansion (y v : ℝ) :
    pairRelativeTransferKernel (3/2+y) (9+v)=
      ∑ k ∈ Finset.range 10, pairRelativeShiftCoeff k y*v^k := by
  unfold pairRelativeTransferKernel
  rw [growthTransferKernel_shift_expansion,growthTransferKernelJet_shift_expansion,
    dominantPairPolynomial_gap_shift_eq,dominantPairPolynomialJet_gap_shift_eq]
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  unfold pairRelativeShiftCoeff
  norm_num only [Nat.reduceSub,OfNat.zero_ne_ofNat,ite_false,ite_true]
  rw [pairKernelShiftValue_nine,pairKernelShiftJet_nine]
  ring

theorem pairRelativeTransferKernel_shift_pos (y v : ℝ) (hy : 0 ≤ y) (hv : 0 ≤ v) :
    0 < pairRelativeTransferKernel (3/2+y) (9+v) := by
  rw [pairRelativeTransferKernel_shift_expansion]
  apply Finset.sum_pos'
  · intro k hk
    exact mul_nonneg (pairRelativeShiftCoeff_pos y hy k
      (by have := Finset.mem_range.mp hk; omega)).le (pow_nonneg hv k)
  · refine ⟨0,by simp,?_⟩
    simpa only [pow_zero,mul_one] using pairRelativeShiftCoeff_pos y hy 0 (by omega)

theorem pairRelativeTransferKernel_pos {q t : ℝ} (hq : 3/2 ≤ q) (ht : 9 ≤ t) :
    0 < pairRelativeTransferKernel q t := by
  have h := pairRelativeTransferKernel_shift_pos (q-3/2) (t-9) (by linarith) (by linarith)
  simpa only [show (3/2:ℝ)+(q-3/2)=q by ring,show (9:ℝ)+(t-9)=t by ring] using h

end
end RHTower.ThetaCuspDefect
