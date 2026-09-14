import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalAngularProductBounds
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalForcingAngularPeriod

/-! Quantitative principal-subtracted products of the original squared source
and half-gradient forcing fields with both physical angular reader operations. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace RHTower.D4BMOriginalForcingProductBounds
open D4BMJointSource D4BMModularCore D4BMGlobalAngularResponse D4BMSquareCuspJets
open D4BMOriginalPrincipalMatching D4BMOriginalAngularReaderBounds D4BMAngularSeries
open GaloisForLFunctions.HTGeometry.ScalarTwoJet
noncomputable section
set_option autoImplicit false

private abbrev Point := Fin 2 → ℝ

/-- The two unchanged angular fields in the literal forcing, retaining its half-gradient normalization. -/
def sourceField (q : XiZeroCopy) (gradient : Bool) (z : Point) : ℂ :=
  if gradient then fullGradientEnergy q z/2 else fullSquarePotential q z

def sourceCoefficient (q : XiZeroCopy) (br gradient : Bool) (i : Fin 3) : ℂ :=
  if gradient then principalGradient q br i else principalAmplitude q i

def sourcePrincipal (q : XiZeroCopy) (br gradient : Bool) (z : Point) : ℂ :=
  ∑ i : Fin 3,sourceCoefficient q br gradient i*(z 1:ℂ)^(principalExponent q i)

def sourceRemainder (q : XiZeroCopy) (br gradient : Bool) (z : Point) : ℂ :=
  sourceField q gradient z-sourcePrincipal q br gradient z

private theorem principal_gradient (q : XiZeroCopy) (br : Bool) (z : Point) (hz : 0 < z 1) :
    (z 1:ℂ)^2*((coordDeriv 0 (principal (center q)) z)^2+
      (coordDeriv 1 (principal (center q)) z)^2)/2=
      ∑ i : Fin 3,principalGradient q br i*(z 1:ℂ)^(principalExponent q i) := by
  rw [principal_gradient_expansion q z hz]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  cases br <;> fin_cases i
  all_goals dsimp [principalGradient,principalExponent,physicalRate,principalAmplitude]
  all_goals ring

private theorem remainder_square (q : XiZeroCopy) (br : Bool) (z : Point) (hz : 0 < z 1) :
    sourceRemainder q br false z=(1/2:ℂ)*squareRemainder (center q) z := by
  have hp := principalSquare_expansion q z hz
  change (principal (center q) z)^2/2=∑ i : Fin 3,principalAmplitude q i*(z 1:ℂ)^(principalExponent q i) at hp
  change fullSquarePotential q z-(∑ i : Fin 3,principalAmplitude q i*(z 1:ℂ)^(principalExponent q i))=_
  rw [← hp]
  unfold fullSquarePotential squareRemainder
  ring

private theorem remainder_gradient (q : XiZeroCopy) (br : Bool) (z : Point) (hz : 0 < z 1) :
    sourceRemainder q br true z=(1/2:ℂ)*(z 1:ℂ)^2*
      (gradientProductRemainder (center q) 0 0 z+gradientProductRemainder (center q) 1 1 z) := by
  change fullGradientEnergy q z/2-(∑ i : Fin 3,principalGradient q br i*(z 1:ℂ)^(principalExponent q i))=_
  rw [← principal_gradient q br z hz]
  unfold fullGradientEnergy gradientProductRemainder
  ring

/-- Both fixed fields in the original forcing retain arbitrary complex cusp weights after their exact principal subtraction. -/
theorem source_remainder_weighted (q : XiZeroCopy) (br gradient : Bool) (w : ℂ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ z : Point,1 ≤ z 1 → ‖(z 1:ℂ)^w*sourceRemainder q br gradient z‖ ≤ C := by
  cases gradient
  · obtain ⟨C,hC,hc⟩ := squareRemainder_jet_weighted_bound (center q) w [] ⟨1,by norm_num⟩
    refine ⟨‖(1/2:ℂ)‖*C,by positivity,?_⟩
    intro z hz
    rw [remainder_square q br z (by linarith),mul_left_comm,norm_mul]
    exact mul_le_mul_of_nonneg_left (hc z hz) (norm_nonneg _)
  · obtain ⟨A,hA,ha⟩ := gradientProductRemainder_jet_weighted_bound (center q) (w+2) 0 0 [] ⟨1,by norm_num⟩
    obtain ⟨B,hB,hb⟩ := gradientProductRemainder_jet_weighted_bound (center q) (w+2) 1 1 [] ⟨1,by norm_num⟩
    refine ⟨‖(1/2:ℂ)‖*(A+B),by positivity,?_⟩
    intro z hz
    have hn : (z 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have he : (z 1:ℂ)^(w+2)=(z 1:ℂ)^w*(z 1:ℂ)^2 := by rw [Complex.cpow_add _ _ hn,Complex.cpow_two]
    rw [remainder_gradient q br z (by linarith)]
    rw [show (z 1:ℂ)^w*((1/2:ℂ)*(z 1:ℂ)^2*
      (gradientProductRemainder (center q) 0 0 z+gradientProductRemainder (center q) 1 1 z))=
      (1/2:ℂ)*((z 1:ℂ)^(w+2)*gradientProductRemainder (center q) 0 0 z+
        (z 1:ℂ)^(w+2)*gradientProductRemainder (center q) 1 1 z) by rw [he];ring,norm_mul]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (ha z hz) (hb z hz))) (norm_nonneg _)

private theorem exp_cpow (a : ℂ) (k : ℝ) :
    (Real.exp k:ℂ)^a=Complex.exp (a*(k:ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos k).ne'),
    ← Complex.ofReal_log (Real.exp_pos k).le,Real.log_exp]
  congr 1
  ring

private theorem source_remainder_decay (q : XiZeroCopy) (br gradient : Bool) (N : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ x k : ℝ,0 ≤ k →
      ‖sourceRemainder q br gradient ![x,Real.exp k]‖ ≤ C*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨C,hC,h⟩ := source_remainder_weighted q br gradient (N:ℂ)
  refine ⟨C,hC,?_⟩
  intro x k hk
  have hb := h ![x,Real.exp k] (Real.one_le_exp hk)
  simp only [Matrix.cons_val,exp_cpow] at hb
  have he : sourceRemainder q br gradient ![x,Real.exp k]=
      Complex.exp (-(N:ℂ)*(k:ℂ))*(Complex.exp ((N:ℂ)*(k:ℂ))*sourceRemainder q br gradient ![x,Real.exp k]) := by
    rw [← mul_assoc,← Complex.exp_add,neg_mul,neg_add_cancel,Complex.exp_zero,one_mul]
  rw [he,norm_mul,Complex.norm_exp]
  have hn : (-(N:ℂ)*(k:ℂ)).re=-(N:ℝ)*k := by simp
  rw [hn]
  exact (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)).trans_eq (mul_comm _ _)

/-- Original fixed angular forcing component paired with the actual reader operation, before any cutoff limit. -/
def fixedProduct (q : XiZeroCopy) (br gradient d : Bool) (x k : ℝ) : ℂ :=
  sourceField q gradient ![x,Real.exp k]*angularJet q d x k-
    sourcePrincipal q br gradient ![x,Real.exp k]*angularPrincipal q d k

private theorem fixed_product_decomposition (q : XiZeroCopy) (br gradient d : Bool) (x k : ℝ) :
    fixedProduct q br gradient d x k=sourceRemainder q br gradient ![x,Real.exp k]*angularJet q d x k+
      ∑ i : Fin 3,sourceCoefficient q br gradient i*
        (Complex.exp (principalExponent q i*(k:ℂ))*tailJet q d ![x,Real.exp k]) := by
  simp only [fixedProduct,sourceRemainder,sourcePrincipal,Matrix.cons_val,exp_cpow,angularJet_decomposition,Fin.sum_univ_three]
  ring

/-- All principal/tail cross terms in both literal forcing fields decay at every cusp order for either actual reader operation. -/
theorem fixed_product_decay (q : XiZeroCopy) (br gradient d : Bool) (N : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ x k : ℝ,0 ≤ k → ‖fixedProduct q br gradient d x k‖ ≤ C*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨A,hA,ha⟩ := source_remainder_decay q br gradient (N+1)
  obtain ⟨D,hD,hd⟩ := angularJet_bound q d
  have h (i : Fin 3) := principal_tail_bound q d (principalExponent q i) N
  choose B hB hb using h
  let C := A*D+∑ i : Fin 3,‖sourceCoefficient q br gradient i‖*B i
  have hC : 0 ≤ C := add_nonneg (mul_nonneg hA hD) (Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hB i)))
  refine ⟨C,hC,?_⟩
  intro x k hk
  have hsource : ‖sourceRemainder q br gradient ![x,Real.exp k]*angularJet q d x k‖ ≤
      A*D*Real.exp (-(N:ℝ)*k) := by
    rw [norm_mul]
    calc
      _ ≤ (A*Real.exp (-((N+1:ℕ):ℝ)*k))*(D*Real.exp k) := mul_le_mul (ha x k hk) (hd x k hk) (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [mul_mul_mul_comm,← Real.exp_add]
        congr 2
        push_cast
        ring
  have hsum : ‖∑ i : Fin 3,sourceCoefficient q br gradient i*
      (Complex.exp (principalExponent q i*(k:ℂ))*tailJet q d ![x,Real.exp k])‖ ≤
      (∑ i : Fin 3,‖sourceCoefficient q br gradient i‖*B i)*Real.exp (-(N:ℝ)*k) := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb i x k hk) (norm_nonneg _)
  rw [fixed_product_decomposition]
  exact ((norm_add_le _ _).trans (add_le_add hsource hsum)).trans_eq (by dsimp [C];ring)

end
end RHTower.D4BMOriginalForcingProductBounds
