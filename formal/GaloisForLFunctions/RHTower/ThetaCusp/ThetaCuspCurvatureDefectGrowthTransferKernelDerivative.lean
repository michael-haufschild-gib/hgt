import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthTransferFlow
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthTransferKernel
/-!
# Exact differential chain for the growth-transfer kernel

Second growth-coefficient derivatives and finite polynomial-moment
transport identify the q derivative of the full transfer kernel.
This supports the remaining stable-component versus dominant-pair
Wronskian comparison; no sign of that comparison is assumed here.
-/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
noncomputable section

def reducedGrowthCoefficientJetTwo (q : ℝ) : ℕ → ℝ
  | 2 => 0
  | 3 => 360
  | 4 => 150*(6-8*q-4*(q+3/2))
  | 5 => 45*(2*(3*q^2-(q+3/2))+4*(q+3/2)*(6*q-1)+6*(q+3/2)^2)
  | 6 => -21*(2*(q+3/2)^3+12*q*(q+3/2)^2+6*q^2*(q+3/2))
  | 7 => 2*(q+3/2)^4+16*q*(q+3/2)^3+12*q^2*(q+3/2)^2
  | _ => 0

def growthCoefficientJetTwo (q : ℝ) (j : ℕ) : ℝ :=
  (q+3)*reducedGrowthCoefficientJetTwo q j+2*reducedGrowthCoefficientJet q j

theorem hasDerivAt_reducedGrowthCoefficientJet (q : ℝ) (j : ℕ) (hj : j ≤ 7) :
    HasDerivAt (fun r => reducedGrowthCoefficientJet r j) (reducedGrowthCoefficientJetTwo q j) q := by
  have h := hasDerivAt_id q
  have ha := h.add_const (3/2:ℝ)
  have hq := h.pow 2
  interval_cases j
  · simpa [reducedGrowthCoefficientJet,reducedGrowthCoefficientJetTwo] using hasDerivAt_const q (0:ℝ)
  · simpa [reducedGrowthCoefficientJet,reducedGrowthCoefficientJetTwo] using hasDerivAt_const q (0:ℝ)
  · simpa [reducedGrowthCoefficientJet,reducedGrowthCoefficientJetTwo] using hasDerivAt_const q (0:ℝ)
  · exact (((h.const_mul 2).sub_const 6).const_mul 180).congr_deriv (by norm_num [reducedGrowthCoefficientJetTwo])
  · exact ((((ha.const_mul 3).sub (hq.const_mul 2)).add
      (ha.mul ((hasDerivAt_const q (3:ℝ)).sub (h.const_mul 4)))).const_mul 150).congr_deriv
      (by norm_num [reducedGrowthCoefficientJetTwo]; ring)
  · exact ((((ha.const_mul 2).mul ((hq.const_mul 3).sub ha)).add
      ((ha.pow 2).mul ((h.const_mul 6).sub_const 1))).const_mul 45).congr_deriv
      (by norm_num [reducedGrowthCoefficientJetTwo]; ring)
  · exact ((((h.const_mul 2).mul (ha.pow 3)).add
      (hq.mul ((ha.pow 2).const_mul 3))).const_mul (-21)).congr_deriv
      (by norm_num [reducedGrowthCoefficientJetTwo]; ring)
  · exact (((h.const_mul 2).mul (ha.pow 4)).add
      (hq.mul ((ha.pow 3).const_mul 4))).congr_deriv
      (by norm_num [reducedGrowthCoefficientJetTwo]; ring)

theorem hasDerivAt_growthCoefficientJet (q : ℝ) (j : ℕ) (hj : j ≤ 7) :
    HasDerivAt (fun r => growthCoefficientJet r j) (growthCoefficientJetTwo q j) q := by
  convert! ((((hasDerivAt_id q).add_const (3:ℝ)).mul
    (hasDerivAt_reducedGrowthCoefficientJet q j hj)).add
      (hasDerivAt_reducedGrowthCoefficient q j hj)) using 1
  · funext r
    exact growthCoefficientJet_factor r j hj
  · simp only [one_mul,id_eq,growthCoefficientJetTwo]
    ring

def polynomialMomentJet (q d : ℝ) (j : ℕ) : ℝ :=
  (d+1)*d^j*(j+1:ℕ)*q^j+(3/2)*d*∑ i ∈ Finset.range (j+1),
    (j.choose i:ℝ)*d^(j-i)*(i.factorial:ℝ)*(j-i:ℕ)*q^(j-i-1)

theorem hasDerivAt_polynomialMoment (q d : ℝ) (j : ℕ) :
    HasDerivAt (fun r => polynomialMoment r d j) (polynomialMomentJet q d j) q := by
  have hs : HasDerivAt (fun r : ℝ => ∑ i ∈ Finset.range (j+1),
      (j.choose i:ℝ)*d^(j-i)*(i.factorial:ℝ)*r^(j-i))
      (∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*d^(j-i)*(i.factorial:ℝ)*(j-i:ℕ)*q^(j-i-1)) q := by
    apply HasDerivAt.fun_sum
    intro i hi
    exact ((hasDerivAt_pow (j-i) q).const_mul ((j.choose i:ℝ)*d^(j-i)*(i.factorial:ℝ))).congr_deriv (by ring)
  exact (((hasDerivAt_pow (j+1) q).const_mul ((d+1)*d^j)).add
    (hs.const_mul ((3/2)*d))).congr_deriv
      (by unfold polynomialMomentJet; simp only [Nat.add_sub_cancel]; ring)

def growthNumeratorJet (q d : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6,
    (growthCoefficientJet q (j+2)*q^(5-j)*polynomialMoment q d (j+2)+
      growthCoefficient q (j+2)*((5-j:ℕ)*q^(5-j-1)*polynomialMoment q d (j+2)+
        q^(5-j)*polynomialMomentJet q d (j+2)))

def slopeNumeratorJet (q d : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6,
    ((growthCoefficientJetTwo q (j+2)*q^(6-j)*polynomialMoment q d (j+2)+
      growthCoefficientJet q (j+2)*((6-j:ℕ)*q^(6-j-1)*polynomialMoment q d (j+2)+
        q^(6-j)*polynomialMomentJet q d (j+2)))-
    (growthCoefficientJet q (j+2)*q^(5-j)*polynomialMoment q d (j+3)+
      growthCoefficient q (j+2)*((5-j:ℕ)*q^(5-j-1)*polynomialMoment q d (j+3)+
        q^(5-j)*polynomialMomentJet q d (j+3))))

theorem hasDerivAt_growthNumerator (q d : ℝ) :
    HasDerivAt (fun r => growthNumerator r d) (growthNumeratorJet q d) q := by
  unfold growthNumerator growthNumeratorJet
  apply HasDerivAt.fun_sum
  intro j hj
  have hj7 : j+2 ≤ 7 := by have := Finset.mem_range.mp hj; omega
  exact (((hasDerivAt_growthCoefficient q (j+2) hj7).mul (hasDerivAt_pow (5-j) q)).mul
    (hasDerivAt_polynomialMoment q d (j+2))).congr_deriv (by simp only [Pi.mul_apply]; ring)

theorem hasDerivAt_slopeNumerator (q d : ℝ) :
    HasDerivAt (fun r => slopeNumerator r d) (slopeNumeratorJet q d) q := by
  unfold slopeNumerator slopeNumeratorJet
  apply HasDerivAt.fun_sum
  intro j hj
  have hj7 : j+2 ≤ 7 := by have := Finset.mem_range.mp hj; omega
  exact ((((hasDerivAt_growthCoefficientJet q (j+2) hj7).mul (hasDerivAt_pow (6-j) q)).mul
    (hasDerivAt_polynomialMoment q d (j+2))).sub
    (((hasDerivAt_growthCoefficient q (j+2) hj7).mul (hasDerivAt_pow (5-j) q)).mul
      (hasDerivAt_polynomialMoment q d (j+3)))).congr_deriv (by simp only [Pi.mul_apply]; ring)

def growthScoreJetTwo (q t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6, growthCoefficientJetTwo q (j+2)*t^(j+2)

theorem hasDerivAt_growthScore (q t : ℝ) :
    HasDerivAt (fun r => growthScore r t) (growthScoreJet q t) q := by
  unfold growthScore growthScoreJet
  apply HasDerivAt.fun_sum
  intro j hj
  exact (hasDerivAt_growthCoefficient q (j+2) (by have := Finset.mem_range.mp hj; omega)).mul_const _

theorem hasDerivAt_growthScoreJet (q t : ℝ) :
    HasDerivAt (fun r => growthScoreJet r t) (growthScoreJetTwo q t) q := by
  unfold growthScoreJet growthScoreJetTwo
  apply HasDerivAt.fun_sum
  intro j hj
  exact (hasDerivAt_growthCoefficientJet q (j+2) (by have := Finset.mem_range.mp hj; omega)).mul_const _

def growthTransferKernelJet (q t : ℝ) : ℝ :=
  growthScoreJet q t*slopeNumerator q 3+growthScore q t*slopeNumeratorJet q 3+
    (t*growthScore q t*growthNumerator q 3+q*t*growthScoreJet q t*growthNumerator q 3+
      q*t*growthScore q t*growthNumeratorJet q 3)-
    (growthScoreJet q t*growthNumerator q 3+q*growthScoreJetTwo q t*growthNumerator q 3+
      q*growthScoreJet q t*growthNumeratorJet q 3)

theorem hasDerivAt_growthTransferKernel (q t : ℝ) :
    HasDerivAt (fun r => growthTransferKernel r t) (growthTransferKernelJet q t) q := by
  have h := hasDerivAt_id q
  have hs := hasDerivAt_growthScore q t
  have hs1 := hasDerivAt_growthScoreJet q t
  have hn := hasDerivAt_growthNumerator q 3
  have hn1 := hasDerivAt_slopeNumerator q 3
  exact (((hs.mul hn1).add ((((h.mul_const t).mul hs).mul hn))).sub
    ((h.mul hs1).mul hn)).congr_deriv
      (by unfold growthTransferKernelJet; simp only [Pi.mul_apply,id_eq]; ring)

end
end RHTower.ThetaCuspDefect
