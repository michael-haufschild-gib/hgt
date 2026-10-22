import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthAtomPairCooling
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthAtomGapPolynomial
/-!
# Exact relative cooling of every deep atom and the complete deep tail

The ten positive coefficient Wronskians give a strictly positive atom
Wronskian for every q >= 3/2 and gap d >= 8. Exact exponential transport
then makes every literal n >= 3 atom transfer strictly decrease relative
to the dominant self-pair. Countable additivity gives the same strict
comparison for the complete deep tail. No sign of the complete signed
cumulant transfer or global source growth is assumed or concluded here.
-/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
noncomputable section

def shiftedAtomMomentCoeff (q : ℝ) (j k : ℕ) : ℝ :=
  (((j+1).choose k:ℝ)*(8:ℝ)^(j+1-k)+(j.choose k:ℝ)*8^(j-k))*q^(j+1)+
    (3/2)*∑ i ∈ Finset.range (j+1),
      (j.choose i:ℝ)*(i.factorial:ℝ)*((j-i+1).choose k:ℝ)*8^(j-i+1-k)*q^(j-i)

theorem polynomialMoment_eight_add_expansion (q v : ℝ) (j : ℕ) (hj : j ≤ 8) :
    polynomialMoment q (8+v) j =
      ∑ k ∈ Finset.range 10, shiftedAtomMomentCoeff q j k*v^k := by
  interval_cases j <;>
    norm_num [polynomialMoment,shiftedAtomMomentCoeff,Finset.sum_range_succ,
      Nat.choose,Nat.factorial] <;> ring

def shiftedAtomGrowthCoeff (q : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 6,
    growthCoefficient q (j+2)*q^(5-j)*shiftedAtomMomentCoeff q (j+2) k

def shiftedAtomSlopeCoeff (q : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 6,
    (growthCoefficientJet q (j+2)*q^(6-j)*shiftedAtomMomentCoeff q (j+2) k-
      growthCoefficient q (j+2)*q^(5-j)*shiftedAtomMomentCoeff q (j+3) k)

def shiftedAtomTransferCoeff (q : ℝ) (k : ℕ) : ℝ :=
  slopeNumerator q 3*shiftedAtomGrowthCoeff q k-
    growthNumerator q 3*shiftedAtomSlopeCoeff q k

theorem growthNumerator_eight_add_expansion (q v : ℝ) :
    growthNumerator q (8+v)=∑ k ∈ Finset.range 10, shiftedAtomGrowthCoeff q k*v^k := by
  unfold growthNumerator shiftedAtomGrowthCoeff
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [polynomialMoment_eight_add_expansion q v (j+2) (by have := Finset.mem_range.mp hj; omega)]
  simp only [Finset.mul_sum,mul_assoc]

theorem slopeNumerator_eight_add_expansion (q v : ℝ) :
    slopeNumerator q (8+v)=∑ k ∈ Finset.range 10, shiftedAtomSlopeCoeff q k*v^k := by
  unfold slopeNumerator shiftedAtomSlopeCoeff
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hj8 : j+3 ≤ 8 := by have := Finset.mem_range.mp hj; omega
  rw [polynomialMoment_eight_add_expansion q v (j+2) (by omega),
    polynomialMoment_eight_add_expansion q v (j+3) hj8]
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib,sub_mul,mul_assoc]

theorem atomTransferNumerator_eight_add_expansion (q v : ℝ) :
    atomTransferNumerator q (8+v)=∑ k ∈ Finset.range 10, shiftedAtomTransferCoeff q k*v^k := by
  unfold atomTransferNumerator shiftedAtomTransferCoeff
  rw [growthNumerator_eight_add_expansion,slopeNumerator_eight_add_expansion]
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib,sub_mul,mul_assoc]

theorem shiftedAtomTransferCoeff_shift_0 (y : ℝ) :
    shiftedAtomTransferCoeff (3/2+y) 0=atomGapShiftValue 0 y := by
  unfold shiftedAtomTransferCoeff shiftedAtomGrowthCoeff shiftedAtomSlopeCoeff
    slopeNumerator growthNumerator atomGapShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [atomGapShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment shiftedAtomMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedAtomTransferCoeff_shift_1 (y : ℝ) :
    shiftedAtomTransferCoeff (3/2+y) 1=atomGapShiftValue 1 y := by
  unfold shiftedAtomTransferCoeff shiftedAtomGrowthCoeff shiftedAtomSlopeCoeff
    slopeNumerator growthNumerator atomGapShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [atomGapShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment shiftedAtomMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedAtomTransferCoeff_shift_2 (y : ℝ) :
    shiftedAtomTransferCoeff (3/2+y) 2=atomGapShiftValue 2 y := by
  unfold shiftedAtomTransferCoeff shiftedAtomGrowthCoeff shiftedAtomSlopeCoeff
    slopeNumerator growthNumerator atomGapShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [atomGapShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment shiftedAtomMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedAtomTransferCoeff_shift_3 (y : ℝ) :
    shiftedAtomTransferCoeff (3/2+y) 3=atomGapShiftValue 3 y := by
  unfold shiftedAtomTransferCoeff shiftedAtomGrowthCoeff shiftedAtomSlopeCoeff
    slopeNumerator growthNumerator atomGapShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [atomGapShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment shiftedAtomMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedAtomTransferCoeff_shift_4 (y : ℝ) :
    shiftedAtomTransferCoeff (3/2+y) 4=atomGapShiftValue 4 y := by
  unfold shiftedAtomTransferCoeff shiftedAtomGrowthCoeff shiftedAtomSlopeCoeff
    slopeNumerator growthNumerator atomGapShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [atomGapShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment shiftedAtomMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedAtomTransferCoeff_shift_5 (y : ℝ) :
    shiftedAtomTransferCoeff (3/2+y) 5=atomGapShiftValue 5 y := by
  unfold shiftedAtomTransferCoeff shiftedAtomGrowthCoeff shiftedAtomSlopeCoeff
    slopeNumerator growthNumerator atomGapShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [atomGapShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment shiftedAtomMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedAtomTransferCoeff_shift_6 (y : ℝ) :
    shiftedAtomTransferCoeff (3/2+y) 6=atomGapShiftValue 6 y := by
  unfold shiftedAtomTransferCoeff shiftedAtomGrowthCoeff shiftedAtomSlopeCoeff
    slopeNumerator growthNumerator atomGapShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [atomGapShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment shiftedAtomMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedAtomTransferCoeff_shift_7 (y : ℝ) :
    shiftedAtomTransferCoeff (3/2+y) 7=atomGapShiftValue 7 y := by
  unfold shiftedAtomTransferCoeff shiftedAtomGrowthCoeff shiftedAtomSlopeCoeff
    slopeNumerator growthNumerator atomGapShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [atomGapShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment shiftedAtomMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedAtomTransferCoeff_shift_8 (y : ℝ) :
    shiftedAtomTransferCoeff (3/2+y) 8=atomGapShiftValue 8 y := by
  unfold shiftedAtomTransferCoeff shiftedAtomGrowthCoeff shiftedAtomSlopeCoeff
    slopeNumerator growthNumerator atomGapShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [atomGapShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment shiftedAtomMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedAtomTransferCoeff_shift_9 (y : ℝ) :
    shiftedAtomTransferCoeff (3/2+y) 9=atomGapShiftValue 9 y := by
  unfold shiftedAtomTransferCoeff shiftedAtomGrowthCoeff shiftedAtomSlopeCoeff
    slopeNumerator growthNumerator atomGapShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [atomGapShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold polynomialMoment shiftedAtomMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring_nf (config := {mode := .raw})

theorem shiftedAtomTransferCoeff_shift_eq (y : ℝ) (k : ℕ) (hk : k ≤ 9) :
    shiftedAtomTransferCoeff (3/2+y) k=atomGapShiftValue k y := by
  interval_cases k
  · exact shiftedAtomTransferCoeff_shift_0 y
  · exact shiftedAtomTransferCoeff_shift_1 y
  · exact shiftedAtomTransferCoeff_shift_2 y
  · exact shiftedAtomTransferCoeff_shift_3 y
  · exact shiftedAtomTransferCoeff_shift_4 y
  · exact shiftedAtomTransferCoeff_shift_5 y
  · exact shiftedAtomTransferCoeff_shift_6 y
  · exact shiftedAtomTransferCoeff_shift_7 y
  · exact shiftedAtomTransferCoeff_shift_8 y
  · exact shiftedAtomTransferCoeff_shift_9 y

theorem dominantPairPolynomial_gap_shift_eq (y : ℝ) :
    dominantPairPolynomial (3/2+y)=atomGapPolyEval atomGapPairCoeff y := by
  rw [dominantPairPolynomial_shift_eq]
  rfl

theorem dominantPairPolynomialJet_gap_shift_eq (y : ℝ) :
    dominantPairPolynomialJet (3/2+y)=atomGapPolyJet atomGapPairCoeff y := by
  unfold dominantPairPolynomialJet
  rw [show (3/2:ℝ)+y-3/2=y by ring]
  rfl

open Filter Set Topology

theorem hasDerivAt_atomGapShiftValue (k : ℕ) (y : ℝ) :
    HasDerivAt (atomGapShiftValue k) (atomGapShiftJet k y) y := by
  unfold atomGapShiftValue atomGapShiftJet atomGapPolyEval atomGapPolyJet
  apply HasDerivAt.fun_sum
  intro j hj
  simpa only [mul_assoc] using (hasDerivAt_pow j y).const_mul (atomGapShiftCoeff k j)

theorem hasDerivAt_shiftedAtomTransferCoeff (q : ℝ) (k : ℕ) (hk : k ≤ 9) :
    HasDerivAt (fun r => shiftedAtomTransferCoeff r k) (atomGapShiftJet k (q-3/2)) q := by
  have h := (hasDerivAt_atomGapShiftValue k (q-3/2)).comp q
    ((hasDerivAt_id q).sub_const (3/2))
  simp only [Function.comp_def,id_eq,mul_one] at h
  apply h.congr_of_eventuallyEq
  filter_upwards with r
  simpa only [show (3/2:ℝ)+(r-3/2)=r by ring] using
    shiftedAtomTransferCoeff_shift_eq (r-3/2) k hk

theorem atomTransferNumeratorJet_gap_expansion (q v : ℝ) :
    atomTransferNumeratorJet q (8+v)=
      ∑ k ∈ Finset.range 10, atomGapShiftJet k (q-3/2)*v^k := by
  have hs : HasDerivAt (fun r => ∑ k ∈ Finset.range 10, shiftedAtomTransferCoeff r k*v^k)
      (∑ k ∈ Finset.range 10, atomGapShiftJet k (q-3/2)*v^k) q := by
    apply HasDerivAt.fun_sum
    intro k hk
    exact (hasDerivAt_shiftedAtomTransferCoeff q k (by have := Finset.mem_range.mp hk; omega)).mul_const _
  have ha := hasDerivAt_atomTransferNumerator q (8+v)
  have he : (fun r => atomTransferNumerator r (8+v))=
      (fun r => ∑ k ∈ Finset.range 10, shiftedAtomTransferCoeff r k*v^k) := by
    funext r
    exact atomTransferNumerator_eight_add_expansion r v
  rw [he] at ha
  exact ha.unique hs

theorem atomTransferNumerator_gap_shift_expansion (y v : ℝ) :
    atomTransferNumerator (3/2+y) (8+v)=
      ∑ k ∈ Finset.range 10, atomGapShiftValue k y*v^k := by
  rw [atomTransferNumerator_eight_add_expansion]
  apply Finset.sum_congr rfl
  intro k hk
  rw [shiftedAtomTransferCoeff_shift_eq y k (by have := Finset.mem_range.mp hk; omega)]

theorem atomPairTransferWronskian_gap_shift_expansion (y v : ℝ) :
    atomPairTransferWronskian (3/2+y) (8+v)=
      (∑ k ∈ Finset.range 10, atomGapShiftWronskian k y*v^k)+
        (3/2+y)*dominantPairPolynomial (3/2+y)*v*atomTransferNumerator (3/2+y) (8+v) := by
  unfold atomPairTransferWronskian
  rw [atomTransferNumerator_gap_shift_expansion,atomTransferNumeratorJet_gap_expansion,
    dominantPairPolynomial_gap_shift_eq,dominantPairPolynomialJet_gap_shift_eq]
  rw [show (3/2:ℝ)+y-3/2=y by ring]
  unfold atomGapShiftWronskian
  simp only [sub_mul,add_mul,mul_add,mul_sub,Finset.mul_sum,Finset.sum_mul]
  simp only [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem atomTransferNumerator_gap_shift_pos (y v : ℝ) (hy : 0 ≤ y) (hv : 0 ≤ v) :
    0 < atomTransferNumerator (3/2+y) (8+v) := by
  rw [atomTransferNumerator_gap_shift_expansion]
  apply Finset.sum_pos'
  · intro k hk
    exact mul_nonneg (atomGapShiftValue_pos y hy k (by have := Finset.mem_range.mp hk; omega)).le
      (pow_nonneg hv k)
  · refine ⟨0, by simp, ?_⟩
    simpa only [pow_zero,mul_one] using atomGapShiftValue_pos y hy 0 (by omega)

theorem atomPairTransferWronskian_gap_shift_pos (y v : ℝ) (hy : 0 ≤ y) (hv : 0 ≤ v) :
    0 < atomPairTransferWronskian (3/2+y) (8+v) := by
  have hs : 0 < ∑ k ∈ Finset.range 10, atomGapShiftWronskian k y*v^k := by
    apply Finset.sum_pos'
    · intro k hk
      exact mul_nonneg (atomGapShiftWronskian_pos y hy k (by have := Finset.mem_range.mp hk; omega)).le
        (pow_nonneg hv k)
    · refine ⟨0, by simp, ?_⟩
      simpa only [pow_zero,mul_one] using atomGapShiftWronskian_pos y hy 0 (by omega)
  rw [atomPairTransferWronskian_gap_shift_expansion]
  apply add_pos_of_pos_of_nonneg hs
  have ha := atomTransferNumerator_gap_shift_pos y v hy hv
  have hp := dominantPairPolynomial_pos (q := 3/2+y) (by linarith)
  positivity

theorem atomPairTransferWronskian_pos {q d : ℝ} (hq : 3/2 ≤ q) (hd : 8 ≤ d) :
    0 < atomPairTransferWronskian q d := by
  have h := atomPairTransferWronskian_gap_shift_pos (q-3/2) (d-8) (by linarith) (by linarith)
  simpa only [show (3/2:ℝ)+(q-3/2)=q by ring,show (8:ℝ)+(d-8)=d by ring] using h

theorem atomPairPolynomialRatio_strictAntiOn {d : ℝ} (hd : 8 ≤ d) :
    StrictAntiOn (fun q => atomPairPolynomialRatio q d) (Ici (3/2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro q hq
    exact (hasDerivAt_atomPairPolynomialRatio hq d).continuousAt.continuousWithinAt
  · intro q hq
    have hq' : 3/2 < q := by simpa only [interior_Ici,mem_Ioi] using hq
    rw [(hasDerivAt_atomPairPolynomialRatio hq'.le d).deriv]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos _))
        (atomPairTransferWronskian_pos hq'.le hd))
      (pow_pos (dominantPairPolynomial_pos hq'.le) 2)

theorem atomTransfer_relative_eq {q : ℝ} (hq : 3/2 ≤ q) {n : ℕ} (hn : 2 ≤ n) :
    growthTransferFunctional q (atomMoment n q)/dominantPairTransfer q =
      ((thetaCuspLikelihoodGap n+1)*Real.exp (9-(3/2)*thetaCuspLikelihoodGap n)/16)*
        atomPairPolynomialRatio q (thetaCuspLikelihoodGap n) := by
  have hq0 : 0 < q := by linarith
  let d := thetaCuspLikelihoodGap n
  have ham : atomMoment n q=(fun j => Real.exp (-(3/2)*d)*Real.exp (-q*d)*(d+1)*bareMoment q d j) := by
    funext j
    exact atomMoment_eq_bare hn hq0 j
  have he : Real.exp (-(3/2)*d)*Real.exp (-q*d)=
      Real.exp (9-(3/2)*d)*Real.exp (-(d-6)*q)*(Real.exp (-(9/2))*Real.exp (-3*q))^2 := by
    rw [pow_two]
    simp only [← Real.exp_add]
    congr 1
    ring
  have hs : Real.exp (-(3/2)*d)*Real.exp (-q*d)*(d+1)=
      ((d+1)*Real.exp (9-(3/2)*d)/16)*Real.exp (-(d-6)*q)*dominantAtomScale q^2 := by
    rw [he]
    unfold dominantAtomScale
    ring
  rw [ham,growthTransferFunctional_smul,growthTransferFunctional_bare_atom hq0,
    dominantPairTransfer_eq hq0,hs]
  change ((d+1)*Real.exp (9-(3/2)*d)/16)*Real.exp (-(d-6)*q)*dominantAtomScale q^2*
    (atomTransferNumerator q d/q^8)/(dominantAtomScale q^2*dominantPairPolynomial q/q^9)=_
  unfold atomPairPolynomialRatio
  change _=((d+1)*Real.exp (9-(3/2)*d)/16)*
    (Real.exp (-(d-6)*q)*q*atomTransferNumerator q d/dominantPairPolynomial q)
  field_simp [hq0.ne',(dominantAtomScale_pos q).ne',(dominantPairPolynomial_pos hq).ne']

theorem atomTransfer_relative_strictAntiOn {n : ℕ} (hn : 3 ≤ n) :
    StrictAntiOn (fun q => growthTransferFunctional q (atomMoment n q)/dominantPairTransfer q)
      (Ici (3/2)) := by
  have hd : (8:ℝ) ≤ thetaCuspLikelihoodGap n := by
    have hnR : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    unfold thetaCuspLikelihoodGap
    nlinarith
  intro q hq r hr hqr
  dsimp only
  rw [atomTransfer_relative_eq hq (by omega),atomTransfer_relative_eq hr (by omega)]
  exact mul_lt_mul_of_pos_left (atomPairPolynomialRatio_strictAntiOn hd hq hr hqr)
    (by
      have hd1 : 0 < thetaCuspLikelihoodGap n+1 := by linarith
      exact div_pos (mul_pos hd1 (Real.exp_pos _)) (by norm_num))

theorem hasSum_atomTransfer_deep {q : ℝ} (hq : 0 < q) :
    HasSum (fun n : ℕ => growthTransferFunctional q (atomMoment (n+2) q))
      (growthTransferFunctional q (thetaCuspDeepTailMoment q)) := by
  have hs : HasSum (fun n : ℕ => growthTransferFunctional q (atomMoment (n+2) q))
      (growthTransferFunctional q (thetaCuspHigherLikelihoodSpectralMoment q)) := by
    unfold growthTransferFunctional
    exact hasSum_sum (fun j _ => ((hasSum_atomMoment hq (j+2)).mul_left _).add
      ((hasSum_atomMoment hq (j+3)).mul_left _))
  have hm : thetaCuspHigherLikelihoodSpectralMoment q=
      fun j => atomMoment 2 q j+thetaCuspDeepTailMoment q j := by
    funext j
    simpa only [atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
      thetaCuspHigherLikelihoodSpectralMoment_eq_second_add_deep hq j
  rw [hm,growthTransferFunctional_add,growthTransferFunctional_dominant_zero hq,zero_add] at hs
  exact hs

theorem hasSum_atomTransfer_relative_deep {q : ℝ} (hq : 0 < q) :
    HasSum (fun n : ℕ => growthTransferFunctional q (atomMoment (n+2) q)/dominantPairTransfer q)
      (growthTransferFunctional q (thetaCuspDeepTailMoment q)/dominantPairTransfer q) := by
  simpa only [div_eq_mul_inv] using (hasSum_atomTransfer_deep hq).mul_right (dominantPairTransfer q)⁻¹

theorem deepTransfer_relative_strictAntiOn :
    StrictAntiOn (fun q => growthTransferFunctional q (thetaCuspDeepTailMoment q)/dominantPairTransfer q)
      (Ici (3/2)) := by
  intro q hq r hr hqr
  have hq0 : 0 < q := by change 3/2 ≤ q at hq; linarith
  have hr0 : 0 < r := by change 3/2 ≤ r at hr; linarith
  refine hasSum_lt (i := 1) ?_ ?_ (hasSum_atomTransfer_relative_deep hr0)
    (hasSum_atomTransfer_relative_deep hq0)
  · intro n
    by_cases hn : n=0
    · subst n
      simp only [Nat.zero_add,growthTransferFunctional_dominant_zero hq0,
        growthTransferFunctional_dominant_zero hr0,zero_div,le_refl]
    · exact (atomTransfer_relative_strictAntiOn (n := n+2) (by omega) hq hr hqr).le
  · simpa only [Nat.reduceAdd] using atomTransfer_relative_strictAntiOn (n := 3) (by omega) hq hr hqr

end
end RHTower.ThetaCuspDefect
