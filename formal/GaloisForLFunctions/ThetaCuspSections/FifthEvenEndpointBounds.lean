import GaloisForLFunctions.ThetaCuspSections.FifthEvenOriginObstruction
import GaloisForLFunctions.ThetaCuspSections.FifthEvenInheritedLoadBoundary
import GaloisForLFunctions.RHTower.FiniteDegreeReciprocalPerturbation
import GaloisForLFunctions.HTGeometry.RealSchurPosDef

/-!
# Coupled fifth-section endpoint forms

Retained Schur coordinates control the complete scale-seven error. The origin
form remains exact; a bordered determinant identity isolates its two load coordinates.
-/

noncomputable section
open Matrix RHTower Polynomial RHTower.ThetaCuspGaussianLimit
namespace GaloisForLFunctions.ThetaCuspSections.EvenFiveEndpoint

/-- The normalized origin moments before division by three times the zeroth moment. -/
def mOrigin (X : ℝ) (k : ℕ) : ℝ := EvenFiveOrigin.originMomentPolynomial X k
abbrev loss : ℝ := EvenFiveBoundary.scaleSevenCompensationLoss
def retainedRatio : ℝ := 19/25000000000
/-- The retained two-atom moments at scale seven. -/
def mSeven (k : ℕ) : ℝ :=
  ((thetaPairRadialEvenPolynomial 49 k).eval 14+
    8*retainedRatio*(thetaPairRadialEvenPolynomial 196 k).eval 35+
    16*retainedRatio^2*(thetaPairRadialEvenPolynomial 784 k).eval 56)/121
def headDet (m : ℕ → ℝ) : ℝ := m 0*m 2-m 1^2
def adj (m : ℕ → ℝ) (a b c e : ℝ) : ℝ := m 2*a*c-m 1*(a*e+b*c)+m 0*b*e
/-- Head-cleared Schur entries after eliminating the first two Hankel coordinates. -/
def schur3 (m : ℕ → ℝ) (i j : ℕ) : ℝ :=
 headDet m*m (i+j+4)-adj m (m (i+2)) (m (i+3)) (m (j+2)) (m (j+3))
/-- The numerator of the retained form on the common load kernel. -/
def kernelNum (m : ℕ → ℝ) : ℝ :=
 176400*schur3 m 0 0-840*schur3 m 0 1+(840/1568)*schur3 m 0 2+
 schur3 m 1 1-(2/1568)*schur3 m 1 2+schur3 m 2 2/1568^2
def crossZero (m : ℕ → ℝ) : ℝ := -420*schur3 m 0 0+schur3 m 0 1-schur3 m 0 2/1568
def crossOne (m : ℕ → ℝ) : ℝ := -420*schur3 m 0 1+schur3 m 1 1-schur3 m 1 2/1568
/-- The two load-coordinate Schur form after eliminating the common kernel. -/
def schur2 (m : ℕ → ℝ) (i j : Fin 2) : ℝ :=
 let b := fun k : Fin 2 => if k=0 then crossZero m else -420*crossZero m+crossOne m
 let t := if i=0 then
   (if j=0 then schur3 m 0 0 else -420*schur3 m 0 0+schur3 m 0 1)
  else (if j=0 then -420*schur3 m 0 0+schur3 m 0 1
   else 176400*schur3 m 0 0-840*schur3 m 0 1+schur3 m 1 1)
 (t-b i*b j/kernelNum m)/headDet m
/-- The rational endpoint gap at the lower endpoint of the origin parameter interval. -/
def gap (i j : Fin 2) : ℝ :=
 schur2 (mOrigin (191/10)) i j/(3*mOrigin (191/10) 0)+schur2 mSeven i j/loss
private theorem radial_eight_coeff (a : ℝ) (k : ℕ) :
 radialCoeffs a 8 k = radialStepCoeff a (radialCoeffs a 7) k := rfl
private theorem radial_seven_zero_16 (a : ℝ) : radialCoeffs a 7 16=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_17 (a : ℝ) : radialCoeffs a 7 17=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_18 (a : ℝ) : radialCoeffs a 7 18=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_19 (a : ℝ) : radialCoeffs a 7 19=0 :=
 radialCoeffs_eq_zero a (by norm_num)

def kernelTail : Fin 3 → ℝ := ![-420,1,-1/1568]
/-- The tail lift orthogonal to the common load kernel. -/
def projectTail (m : ℕ → ℝ) (b : Fin 2 → ℝ) (i : Fin 3) : ℝ :=
  let t : Fin 3 → ℝ := ![b 0-420*b 1,b 1,0]
  let c := (b 0*crossZero m+b 1*(-420*crossZero m+crossOne m))/kernelNum m
  t i-c*kernelTail i
/-- Head elimination of a tail vector in the fifth Hankel section. -/
def liftTail (m : ℕ → ℝ) (t : Fin 3 → ℝ) (i : Fin 5) : ℝ :=
  let a := ∑ j : Fin 3, t j*m (j.val+2)
  let b := ∑ j : Fin 3, t j*m (j.val+3)
  if i.val=0 then -(m 2*a-m 1*b)/headDet m
  else if i.val=1 then (m 1*a-m 0*b)/headDet m
  else t ⟨i.val-2,by omega⟩
def loadColumn (i : Fin 2) : Fin 2 → ℝ :=
  if i.val=0 then ![1,0] else ![-gap 0 1/gap 0 0,1]
/-- Scale-seven Schur coordinates, with the last two columns adapted to the endpoint gap. -/
def sevenVector (i k : Fin 5) : ℝ :=
  if i.val=0 then (if k.val=0 then 1 else 0)
  else if i.val=1 then (if k.val=0 then -mSeven 1/mSeven 0 else if k.val=1 then 1 else 0)
  else if i.val=2 then liftTail mSeven kernelTail k
  else liftTail mSeven (projectTail mSeven (loadColumn ⟨i.val-3,by omega⟩)) k
/-- The three retained kernel pivots and the two endpoint-gap pivots. -/
def diag (i : Fin 5) : ℝ :=
  if i.val=0 then mSeven 0/loss
  else if i.val=1 then headDet mSeven/(mSeven 0*loss)
  else if i.val=2 then kernelNum mSeven/(headDet mSeven*loss)
  else if i.val=3 then gap 0 0
  else (gap 0 0*gap 1 1-gap 0 1^2)/gap 0 0
def sevenPolynomial (a X : ℝ) (i j : Fin 5) : ℝ :=
  ∑ u : Fin 5, ∑ v : Fin 5, sevenVector i u*sevenVector j v*
    (thetaPairRadialEvenPolynomial a (u.val+v.val)).eval X
def sevenTail (i j : Fin 5) : ℝ :=
  ∑ u : Fin 5, ∑ v : Fin 5, |sevenVector i u| * |sevenVector j v| *
    ((2*(u.val+v.val)).factorial:ℝ)/(10000000000000*(3/20:ℝ)^(2*(u.val+v.val)))
def sevenError (i j : Fin 5) : ℝ :=
  ((8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 i j|+
    16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 i j|)/121+sevenTail i j

local macro "norm_endpoint" : tactic =>
`(tactic| norm_num [sevenError, sevenTail, sevenPolynomial, sevenVector, loadColumn, liftTail, projectTail, kernelTail, diag, loss, EvenFiveBoundary.scaleSevenCompensationLoss, Fin.sum_univ_succ, Nat.factorial, gap,schur2,kernelNum,crossZero,crossOne,schur3,headDet,adj,mOrigin,EvenFiveOrigin.originMomentPolynomial,mSeven,retainedRatio,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,radialCoeffs_0_0,radialCoeffs_0_1,radialCoeffs_1_0,radialCoeffs_1_1,radialCoeffs_1_2,radialCoeffs_1_3,radialCoeffs_2_0,radialCoeffs_2_1,radialCoeffs_2_2,radialCoeffs_2_3,radialCoeffs_2_4,radialCoeffs_2_5,radialCoeffs_3_0,radialCoeffs_3_1,radialCoeffs_3_2,radialCoeffs_3_3,radialCoeffs_3_4,radialCoeffs_3_5,radialCoeffs_3_6,radialCoeffs_3_7,radialCoeffs_4_0,radialCoeffs_4_1,radialCoeffs_4_2,radialCoeffs_4_3,radialCoeffs_4_4,radialCoeffs_4_5,radialCoeffs_4_6,radialCoeffs_4_7,radialCoeffs_4_8,radialCoeffs_4_9,radialCoeffs_5_0,radialCoeffs_5_1,radialCoeffs_5_2,radialCoeffs_5_3,radialCoeffs_5_4,radialCoeffs_5_5,radialCoeffs_5_6,radialCoeffs_5_7,radialCoeffs_5_8,radialCoeffs_5_9,radialCoeffs_5_10,radialCoeffs_5_11,radialCoeffs_6_0,radialCoeffs_6_1,radialCoeffs_6_2,radialCoeffs_6_3,radialCoeffs_6_4,radialCoeffs_6_5,radialCoeffs_6_6,radialCoeffs_6_7,radialCoeffs_6_8,radialCoeffs_6_9,radialCoeffs_6_10,radialCoeffs_6_11,radialCoeffs_6_12,radialCoeffs_6_13,radialCoeffs_7_0,radialCoeffs_7_1,radialCoeffs_7_2,radialCoeffs_7_3,radialCoeffs_7_4,radialCoeffs_7_5,radialCoeffs_7_6,radialCoeffs_7_7,radialCoeffs_7_8,radialCoeffs_7_9,radialCoeffs_7_10,radialCoeffs_7_11,radialCoeffs_7_12,radialCoeffs_7_13,radialCoeffs_7_14,radialCoeffs_7_15,radial_eight_coeff,radial_seven_zero_16,radial_seven_zero_17,radial_seven_zero_18,radial_seven_zero_19,radialStepCoeff,radialInnerCoeff])

private theorem diagonal_positive_0 : 0 < diag 0 := by
  norm_endpoint

private theorem diagonal_positive_1 : 0 < diag 1 := by
  norm_endpoint

private theorem diagonal_positive_2 : 0 < diag 2 := by
  norm_endpoint

private theorem diagonal_positive_3 : 0 < diag 3 := by
  norm_endpoint

private theorem diagonal_positive_4 : 0 < diag 4 := by
  norm_endpoint

private theorem mixed_error_0_0 : (8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 0 0|/(121*loss) < diag 0/96 := by
  norm_endpoint

private theorem second_error_0_0 : 16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 0 0|/(121*loss) < diag 0/96 := by
  norm_endpoint

private theorem tail_error_0_0 : sevenTail 0 0/loss < diag 0/96 := by
  norm_endpoint

private theorem mixed_error_0_1 : ((8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 0 1|/(121*loss))^2 < diag 0*diag 1/96^2 := by
  norm_endpoint

private theorem second_error_0_1 : (16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 0 1|/(121*loss))^2 < diag 0*diag 1/96^2 := by
  norm_endpoint

private theorem tail_error_0_1 : (sevenTail 0 1/loss)^2 < diag 0*diag 1/96^2 := by
  norm_endpoint

private theorem mixed_error_0_2 : ((8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 0 2|/(121*loss))^2 < diag 0*diag 2/96^2 := by
  norm_endpoint

private theorem second_error_0_2 : (16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 0 2|/(121*loss))^2 < diag 0*diag 2/96^2 := by
  norm_endpoint

private theorem tail_error_0_2 : (sevenTail 0 2/loss)^2 < diag 0*diag 2/96^2 := by
  norm_endpoint

private theorem mixed_error_0_3 : ((8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 0 3|/(121*loss))^2 < diag 0*diag 3/96^2 := by
  norm_endpoint

private theorem second_error_0_3 : (16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 0 3|/(121*loss))^2 < diag 0*diag 3/96^2 := by
  norm_endpoint

private theorem tail_error_0_3 : (sevenTail 0 3/loss)^2 < diag 0*diag 3/96^2 := by
  norm_endpoint

private theorem mixed_error_0_4 : ((8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 0 4|/(121*loss))^2 < diag 0*diag 4/96^2 := by
  norm_endpoint

private theorem second_error_0_4 : (16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 0 4|/(121*loss))^2 < diag 0*diag 4/96^2 := by
  norm_endpoint

private theorem tail_error_0_4 : (sevenTail 0 4/loss)^2 < diag 0*diag 4/96^2 := by
  norm_endpoint

private theorem mixed_error_1_1 : (8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 1 1|/(121*loss) < diag 1/96 := by
  norm_endpoint

private theorem second_error_1_1 : 16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 1 1|/(121*loss) < diag 1/96 := by
  norm_endpoint

private theorem tail_error_1_1 : sevenTail 1 1/loss < diag 1/96 := by
  norm_endpoint

private theorem mixed_error_1_2 : ((8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 1 2|/(121*loss))^2 < diag 1*diag 2/96^2 := by
  norm_endpoint

private theorem second_error_1_2 : (16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 1 2|/(121*loss))^2 < diag 1*diag 2/96^2 := by
  norm_endpoint

private theorem tail_error_1_2 : (sevenTail 1 2/loss)^2 < diag 1*diag 2/96^2 := by
  norm_endpoint

private theorem mixed_error_1_3 : ((8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 1 3|/(121*loss))^2 < diag 1*diag 3/96^2 := by
  norm_endpoint

private theorem second_error_1_3 : (16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 1 3|/(121*loss))^2 < diag 1*diag 3/96^2 := by
  norm_endpoint

private theorem tail_error_1_3 : (sevenTail 1 3/loss)^2 < diag 1*diag 3/96^2 := by
  norm_endpoint

private theorem mixed_error_1_4 : ((8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 1 4|/(121*loss))^2 < diag 1*diag 4/96^2 := by
  norm_endpoint

private theorem second_error_1_4 : (16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 1 4|/(121*loss))^2 < diag 1*diag 4/96^2 := by
  norm_endpoint

private theorem tail_error_1_4 : (sevenTail 1 4/loss)^2 < diag 1*diag 4/96^2 := by
  norm_endpoint

private theorem mixed_error_2_2 : (8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 2 2|/(121*loss) < diag 2/96 := by
  norm_endpoint

private theorem second_error_2_2 : 16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 2 2|/(121*loss) < diag 2/96 := by
  norm_endpoint

private theorem tail_error_2_2 : sevenTail 2 2/loss < diag 2/96 := by
  norm_endpoint

private theorem mixed_error_2_3 : ((8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 2 3|/(121*loss))^2 < diag 2*diag 3/96^2 := by
  norm_endpoint

private theorem second_error_2_3 : (16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 2 3|/(121*loss))^2 < diag 2*diag 3/96^2 := by
  norm_endpoint

private theorem tail_error_2_3 : (sevenTail 2 3/loss)^2 < diag 2*diag 3/96^2 := by
  norm_endpoint

private theorem mixed_error_2_4 : ((8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 2 4|/(121*loss))^2 < diag 2*diag 4/96^2 := by
  norm_endpoint

private theorem second_error_2_4 : (16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 2 4|/(121*loss))^2 < diag 2*diag 4/96^2 := by
  norm_endpoint

private theorem tail_error_2_4 : (sevenTail 2 4/loss)^2 < diag 2*diag 4/96^2 := by
  norm_endpoint

private theorem mixed_error_3_3 : (8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 3 3|/(121*loss) < diag 3/96 := by
  norm_endpoint

private theorem second_error_3_3 : 16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 3 3|/(121*loss) < diag 3/96 := by
  norm_endpoint

private theorem tail_error_3_3 : sevenTail 3 3/loss < diag 3/96 := by
  norm_endpoint

private theorem mixed_error_3_4 : ((8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 3 4|/(121*loss))^2 < diag 3*diag 4/96^2 := by
  norm_endpoint

private theorem second_error_3_4 : (16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 3 4|/(121*loss))^2 < diag 3*diag 4/96^2 := by
  norm_endpoint

private theorem tail_error_3_4 : (sevenTail 3 4/loss)^2 < diag 3*diag 4/96^2 := by
  norm_endpoint

private theorem mixed_error_4_4 : (8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 4 4|/(121*loss) < diag 4/96 := by
  norm_endpoint

private theorem second_error_4_4 : 16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 4 4|/(121*loss) < diag 4/96 := by
  norm_endpoint

private theorem tail_error_4_4 : sevenTail 4 4/loss < diag 4/96 := by
  norm_endpoint

def kernelU (m : ℕ → ℝ) : ℝ := -420*m 2+m 3-m 4/1568
def kernelV (m : ℕ → ℝ) : ℝ := -420*m 3+m 4-m 5/1568
def kernelT (m : ℕ → ℝ) : ℝ :=
  176400*m 4-840*m 5+(1+840/1568)*m 6-2*m 7/1568+m 8/1568^2
/-- The Hankel determinant restricted to the three-dimensional common load kernel. -/
def kernelDet (m : ℕ → ℝ) : ℝ :=
  m 0*m 2*kernelT m+2*m 1*kernelU m*kernelV m-
    m 0*kernelV m^2-m 2*kernelU m^2-m 1^2*kernelT m
def kernelBorder (m : ℕ → ℝ) (i : Fin 2) : Fin 3 → ℝ :=
  let p : Fin 3 → ℝ := fun k =>
    if k.val=0 then m 2 else if k.val=1 then m 3 else -420*m 4+m 5-m 6/1568
  let q : Fin 3 → ℝ := fun k =>
    if k.val=0 then m 3 else if k.val=1 then m 4 else -420*m 5+m 6-m 7/1568
  if i.val=0 then p else fun k => q k-420*p k
def loadCorner (m : ℕ → ℝ) (i j : Fin 2) : ℝ :=
  if i.val=0 then (if j.val=0 then m 4 else m 5-420*m 4)
  else if j.val=0 then m 5-420*m 4 else m 6-840*m 5+176400*m 4
def kernelAdjPair (m : ℕ → ℝ) (p q : Fin 3 → ℝ) : ℝ :=
  (m 2*kernelT m-kernelV m^2)*p 0*q 0+
  (m 0*kernelT m-kernelU m^2)*p 1*q 1+
  (m 0*m 2-m 1^2)*p 2*q 2+
  (kernelU m*kernelV m-m 1*kernelT m)*(p 0*q 1+p 1*q 0)+
  (m 1*kernelV m-m 2*kernelU m)*(p 0*q 2+p 2*q 0)+
  (m 1*kernelU m-m 0*kernelV m)*(p 1*q 2+p 2*q 1)
private theorem kernelBorder_00 (m : ℕ → ℝ) : kernelBorder m 0 0 = m 2 := rfl
private theorem kernelBorder_01 (m : ℕ → ℝ) : kernelBorder m 0 1 = m 3 := rfl
private theorem kernelBorder_02 (m : ℕ → ℝ) : kernelBorder m 0 2 = -420*m 4+m 5-m 6/1568 := rfl
private theorem kernelBorder_10 (m : ℕ → ℝ) : kernelBorder m 1 0 = m 3-420*m 2 := rfl
private theorem kernelBorder_11 (m : ℕ → ℝ) : kernelBorder m 1 1 = m 4-420*m 3 := rfl
private theorem kernelBorder_12 (m : ℕ → ℝ) : kernelBorder m 1 2 =
    (-420*m 5+m 6-m 7/1568)-420*(-420*m 4+m 5-m 6/1568) := rfl
/-- The kernel-determinant multiple of the two-coordinate Schur form. -/
def originSchurNumerator (m : ℕ → ℝ) (i j : Fin 2) : ℝ :=
  kernelDet m*loadCorner m i j-kernelAdjPair m (kernelBorder m i) (kernelBorder m j)
/-- The retained Schur form after paying the complete five-coordinate error. -/
def paidSevenSchur : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  schur2 mSeven i j/loss-(5/32)*gap i j
/-- The exact origin gap multiplied by its positive normalization denominator. -/
def paidGapNumerator (X : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  originSchurNumerator (mOrigin X) i j+
    3*mOrigin X 0*kernelDet (mOrigin X)*paidSevenSchur i j

def kernelCrossEnergy (m : ℕ → ℝ) (p q : Fin 3 → ℝ) : ℝ :=
  let a := p 1*q 2-p 2*q 1
  let b := p 2*q 0-p 0*q 2
  let c := p 0*q 1-p 1*q 0
  m 0*a^2+m 2*b^2+kernelT m*c^2+
    2*m 1*a*b+2*kernelU m*a*c+2*kernelV m*b*c
def originReducedDet (m : ℕ → ℝ) : ℝ :=
  let p := kernelBorder m 0
  let q := kernelBorder m 1
  let a := m 4
  let b := m 5-420*m 4
  let c := m 6-840*m 5+176400*m 4
  kernelDet m*(a*c-b^2)-c*kernelAdjPair m p p-a*kernelAdjPair m q q+
    2*b*kernelAdjPair m p q+kernelCrossEnergy m p q
/-- The endpoint-gap determinant after factoring out the common-kernel determinant. -/
def paidGapReducedDet (X : ℝ) : ℝ :=
  let m := mOrigin X
  originReducedDet m+
    3*m 0*(originSchurNumerator m 0 0*paidSevenSchur 1 1+
      originSchurNumerator m 1 1*paidSevenSchur 0 0-
      2*originSchurNumerator m 0 1*paidSevenSchur 0 1)+
    9*m 0^2*kernelDet m*(paidSevenSchur 0 0*paidSevenSchur 1 1-paidSevenSchur 0 1^2)

private theorem paidSevenSchur_00 : paidSevenSchur 0 0 =
    (77823589288666326500231483525535147042963486152333881423850577248705827605229713493546434462554055194962335967989336172661693329287113591496067967465209:ℝ)/
      1755127208175132818879075093054200815146392631621110036464129779666968099532774608328840277670502015842846312782112419312505038149413190000000000 := by
  simp only [paidSevenSchur]
  norm_endpoint

private theorem paidSevenSchur_01 : paidSevenSchur 0 1 =
    (213634858032934921254755799410551877313697330561115055300195851565570358045178979771160212930399966024545162329858804781715588254934373409344237054121171677:ℝ)/
      14041017665401062551032600744433606521171141052968880291713038237335744796262196866630722221364016126742770502256899354500040305195305520000000000 := by
  simp only [paidSevenSchur]
  norm_endpoint

private theorem paidSevenSchur_11 : paidSevenSchur 1 1 =
    (6252277575739794174596338789602460218609276873477589919459839916656154203221402741336384649789533473691285534227998318787688891731167030613030733844902491683:ℝ)/
      864062625563142310832775430426683478225916372490392633336186968451430449000750576408044444391631761645708953985039960276925557242788032000000000 := by
  simp only [paidSevenSchur]
  norm_endpoint

theorem paid_seven_first_positive : 0 < paidSevenSchur 0 0 := by
  rw [paidSevenSchur_00]
  norm_num

theorem paid_seven_det_positive : 0 < paidSevenSchur 0 0*paidSevenSchur 1 1-paidSevenSchur 0 1^2 := by
  rw [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]
  norm_num

theorem adjugate_pair_identity (m : ℕ → ℝ) (p q : Fin 3 → ℝ) :
    kernelAdjPair m p p*kernelAdjPair m q q-kernelAdjPair m p q^2 =
      kernelDet m*kernelCrossEnergy m p q := by
  dsimp only [kernelAdjPair,kernelDet,kernelCrossEnergy]
  ring

theorem origin_numerator_det_factor (m : ℕ → ℝ) :
    originSchurNumerator m 0 0*originSchurNumerator m 1 1-
      originSchurNumerator m 0 1^2 = kernelDet m*originReducedDet m := by
  have h := adjugate_pair_identity m (kernelBorder m 0) (kernelBorder m 1)
  norm_num [originSchurNumerator,originReducedDet,loadCorner]
  linear_combination h

theorem paid_gap_det_factor (X : ℝ) :
    paidGapNumerator X 0 0*paidGapNumerator X 1 1-paidGapNumerator X 0 1^2 =
      kernelDet (mOrigin X)*paidGapReducedDet X := by
  have h := origin_numerator_det_factor (mOrigin X)
  dsimp only [paidGapNumerator,paidGapReducedDet]
  linear_combination h
theorem paid_gap_first_positive (z : ℝ) (hz : 0 ≤ z) (hzU : z ≤ 1) :
    0 < paidGapNumerator ((z+191)/10) 0 0 := by
  have hp (n : ℕ) : z^n ≤ 1 := by simpa using pow_le_pow_left₀ hz hzU n
  simp only [paidGapNumerator,originSchurNumerator,kernelAdjPair,
    kernelBorder_00,kernelBorder_01,kernelBorder_02]
  dsimp only [loadCorner,kernelDet,kernelU,kernelV,kernelT,paidSevenSchur]
  norm_endpoint
  ring_nf
  norm_num
  ring_nf
  linarith only [pow_nonneg hz 1, pow_nonneg hz 2, pow_nonneg hz 3, pow_nonneg hz 4, pow_nonneg hz 5, pow_nonneg hz 6, pow_nonneg hz 7, pow_nonneg hz 8, pow_nonneg hz 9, pow_nonneg hz 10, pow_nonneg hz 11, pow_nonneg hz 12, pow_nonneg hz 13, pow_nonneg hz 14, pow_nonneg hz 15, pow_nonneg hz 16, pow_nonneg hz 17, pow_nonneg hz 18, pow_nonneg hz 19, pow_nonneg hz 20, pow_nonneg hz 21, pow_nonneg hz 22, pow_nonneg hz 23, pow_nonneg hz 24, hp 1, hp 2, hp 3, hp 4, hp 5, hp 6, hp 7, hp 8, hp 9, hp 10, hp 11, hp 12, hp 13, hp 14, hp 15, hp 16, hp 17, hp 18, hp 19, hp 20, hp 21, hp 22, hp 23, hp 24]
private def constantTerm : ℝ := 2301013779120485576329895300099360359410079751145750678847690729588176220338615386162229918143092665014198556239287257800708955388874267998640715272548789600385465592570809926650020429609315163783/25126415811307591860701792807208715658000797833160948860208567035891992993982070247405881295750180380103585496893417848832000000000000000000000000000000000000000
private def negativeCoeff11 : ℝ := 295581012772371477157146938526272975021922284582949078375064390037129711324075487822059054268590952762091809720940815253121477019500875980568835635038945547944631480618824016230286273170839736437262286331465410391229911827230837/72003332040700391303227045952568669724758314643977600938066236991082666380271006850307182647347508960905735473136504371317554773370473352164395422201789312759778345572049616896000000000000000000000000000000000000000
private def negativeCoeff12 : ℝ := 393692845618962474747753356458928488473255302141440840575283778039257546898196597429123920838854432772598862693520089450660747240278341948115033190056646170322331250876495225985912922965211572452364502605557085102331357456766197/288013328162801565212908183810274678899033258575910403752264947964330665521084027401228730589390035843622941892546017485270219093481893408657581688807157251039113382288198467584000000000000000000000000000000000000000
private def negativeCoeff13 : ℝ := 581604937200331691485443229126114671722345639508298579541404924656795282467343599686436573987165753135115202955712159452906221734907240283474842127537267382106148192549415822710689220597843789098982857105155006787495317136371/36001666020350195651613522976284334862379157321988800469033118495541333190135503425153591323673754480452867736568252185658777386685236676082197711100894656379889172786024808448000000000000000000000000000000000000000
private def negativeCoeff14 : ℝ := 9434465779408259845968586181686350166633331184763249320270620882054884287136214776353785580379732115384107954128058423392136574039882602732525515159008810322224949584276246890175562821689992876224247681409667998575982321953/72003332040700391303227045952568669724758314643977600938066236991082666380271006850307182647347508960905735473136504371317554773370473352164395422201789312759778345572049616896000000000000000000000000000000000000000
private def negativeCoeff15 : ℝ := 30832039915233833618036573578285725655819889849463917381486488365697048419758773051095355808031160728284526170823904627910880356822058423754395810785347857001322648889598805457912396437343832315824679688731582227466762383/36001666020350195651613522976284334862379157321988800469033118495541333190135503425153591323673754480452867736568252185658777386685236676082197711100894656379889172786024808448000000000000000000000000000000000000000
private def negativeCoeff16 : ℝ := 2716628430250333449445762121257461614041512509792331477754484716060420255303988398466067971628420489606637083128153294902473181495517044570280251699613801718644399107397394443934982776168665460738229974820005677228539257/576026656325603130425816367620549357798066517151820807504529895928661331042168054802457461178780071687245883785092034970540438186963786817315163377614314502078226764576396935168000000000000000000000000000000000000000
private def negativeCoeff17 : ℝ := 19874107272762677607049304972514364663354494682507176073573946942003152412349559890992693476050299556544865663300921507184950546055336656041344393789017143735570665888641945596138229362734290882032119466665331410867/894451329698141506872385664007064220183333101167423614137468782497921321494049774537977424190652285228642676684925520140590742526341283877818576673314152953537619199652790272000000000000000000000000000000000000000
private def negativeCoeff18 : ℝ := 25933994208203870225736261419710603937511563260513657014222358120386247234389695376423831557775539595704327988973940111907261618603118479700650560541763762142197266592546042809230660514973887679355442392303445591531/288013328162801565212908183810274678899033258575910403752264947964330665521084027401228730589390035843622941892546017485270219093481893408657581688807157251039113382288198467584000000000000000000000000000000000000000
private def negativeCoeff19 : ℝ := 45261889552858991934340605801045220040255021023754769367545229104943204278329096134637316184863806802153536511755965394744189546585832556205196419628342807891779170256365070260401059269761069985013138490601782627/144006664081400782606454091905137339449516629287955201876132473982165332760542013700614365294695017921811470946273008742635109546740946704328790844403578625519556691144099233792000000000000000000000000000000000000000
private def negativeCoeff20 : ℝ := 15536630147572410541894506097592172078520350455229044127544563194743120746397392141350467185412768605291831702135288913979399311880984776495161115326398961094297737363709003466114959668852213767469955580864559/16457904466445803726451896217729981651373329061480594500129425597961752315490515851498784605108002048207025251002629570586869662484679623351861810788980414345092193273611341004800000000000000000000000000000000000000
private def negativeCoeff21 : ℝ := 12101346222861663923591231151874656029583494733790848154616122339099913686138855224145114853829975885472264407877049481803979156429713038154101022462354955089793844893307326737868786609/4975084429110557656870356435512745903001119012496665670432369002895588990606952016812898726964517930857694742289072727089090849347041554428165192758229267906560000000000000000000000000000000000
private def negativeCoeff22 : ℝ := 26604697978396585897193846634479198521273748501552843498711484544111094542739522910852570100059204388505331027379858074489588962816048768145645764551197631296488837851488574902333771/4975084429110557656870356435512745903001119012496665670432369002895588990606952016812898726964517930857694742289072727089090849347041554428165192758229267906560000000000000000000000000000000000
private def negativeCoeff23 : ℝ := 24744574840260484882254626673539132362585809579602176245780581182943839068437965373646501990871855504011262741305860163266003064855919394901435497838439129167467296766629803398787/2487542214555278828435178217756372951500559506248332835216184501447794495303476008406449363482258965428847371144536363544545424673520777214082596379114633953280000000000000000000000000000000000
private def negativeCoeff24 : ℝ := 13988068077856886046365025010728447141416582104292799493642488520361887588677918452003620943790483086982238705162652516189807533069294826411376183725909122298663634956385661017/904560805292828664885519351911408346000203456817575576442248909617379816473991275784163404902639623792308134961649586743471063517643918986939125956041685073920000000000000000000000000000000000
private def negativeCoeff25 : ℝ := 39274356555125260797646448009247978819787017404337633567833994918400441636702962918527403951232543757175319459117656245859046310552472799147454005136033221906870346951087481/1990033771644223062748142574205098361200447604998666268172947601158235596242780806725159490785807172343077896915629090835636339738816621771266077103291707162624000000000000000000000000000000000
private def negativeCoeff26 : ℝ := 320788377744904545007651046838197364922474025742045692828261339434573151757712105845220935949945328449260304381814443852191459723575398631279705053818146828062018050093/15920270173153784501985140593640786889603580839989330145383580809265884769942246453801275926286457378744623175325032726685090717910532974170128616826333657300992000000000000000000000000000000
private def negativeCoeff27 : ℝ := 179502749188710536609345259/11338401925370018158084096000000000000000000000000000
private def negativeCoeff28 : ℝ := 16309948892691243319389/1814144308059202905293455360000000000000000000000000
private def negativeCoeff29 : ℝ := 17034392650954221/5183269451597722586552729600000000000000000000000
private def negativeCoeff30 : ℝ := 337403577627/580526178578944929693905715200000000000000000000
private def negativeCoefficientSum : ℝ :=
  negativeCoeff11+
  negativeCoeff12+
  negativeCoeff13+
  negativeCoeff14+
  negativeCoeff15+
  negativeCoeff16+
  negativeCoeff17+
  negativeCoeff18+
  negativeCoeff19+
  negativeCoeff20+
  negativeCoeff21+
  negativeCoeff22+
  negativeCoeff23+
  negativeCoeff24+
  negativeCoeff25+
  negativeCoeff26+
  negativeCoeff27+
  negativeCoeff28+
  negativeCoeff29+
  negativeCoeff30

private def negativePolynomial (z : ℝ) : ℝ :=
  z^11*negativeCoeff11+
  z^12*negativeCoeff12+
  z^13*negativeCoeff13+
  z^14*negativeCoeff14+
  z^15*negativeCoeff15+
  z^16*negativeCoeff16+
  z^17*negativeCoeff17+
  z^18*negativeCoeff18+
  z^19*negativeCoeff19+
  z^20*negativeCoeff20+
  z^21*negativeCoeff21+
  z^22*negativeCoeff22+
  z^23*negativeCoeff23+
  z^24*negativeCoeff24+
  z^25*negativeCoeff25+
  z^26*negativeCoeff26+
  z^27*negativeCoeff27+
  z^28*negativeCoeff28+
  z^29*negativeCoeff29+
  z^30*negativeCoeff30

private def positiveCoeff1 : ℝ := 9167154069642398377790585433315846581262946560759751677272228774170522198098309813568889850134440696565567429892151428798811416628102768379421246877390193802486065428011481097121325266957670934201869214544621689724280607557876467235261610463/1307292058846960418421348238010603985096476542405517972179302477235268907477699639025382663169074978361563627842040644594749632853947735414487051044402022994580433010688000000000000000000000000000000000000000
private def positiveCoeff2 : ℝ := 324148833681130512668518672225062213216355814642682650997626246762701672662158636644797295396678530254126377165476279700786000405535852771642659780749086135771988213648843421167455844580230506992364789460200550964769414787481298729050720276257/1291001188575175219361020667660010304666812757800156902064452707903567864169131381985220202289583428631211834941239830408261214352229309788552673946771782400340276845477888000000000000000000000000000000000000000
private def positiveCoeff3 : ℝ := 6249367691528700116559483295112068681408198809591144752922695056876992011369523227465825952147658616641801726396286277891964916902780453682803233310321975479512752815255187640280174559470481931174664212007750667869109811221008040538482305632487/1099287512071761699285909098512498774423791063266833602107881480779888036340015371760415002249580289479476877452465715592634424020923257284952601865676172713889745733924421632000000000000000000000000000000000000000
private def positiveCoeff4 : ℝ := 54057984235514228027046183759502384150406438604484498759232782960169440000050910192248554621447972052447201900285766635737877893449433987749802036882073427770313061187834141909009670335494940060633602245754449565577564686356950620637408987511767/576026656325603130425816367620549357798066517151820807504529895928661331042168054802457461178780071687245883785092034970540438186963786817315163377614314502078226764576396935168000000000000000000000000000000000000000
private def positiveCoeff5 : ℝ := 44668292483623273185983759625813134813051288687154729200026342353917149919509011679647966173123487238392765058691563164735171603784731612979710564671913994286278558225955816821880426089828058049188953117453694245754876324957813431362554459121/36001666020350195651613522976284334862379157321988800469033118495541333190135503425153591323673754480452867736568252185658777386685236676082197711100894656379889172786024808448000000000000000000000000000000000000000
private def positiveCoeff6 : ℝ := 1000888680288140273300317163859399654053302508132719352336093498555613419065037566668658815990509690013390211076903581792823272318401204729649672602097114785229080435850861925253870735310985611902777437317635031885089044472563072355346902063/72003332040700391303227045952568669724758314643977600938066236991082666380271006850307182647347508960905735473136504371317554773370473352164395422201789312759778345572049616896000000000000000000000000000000000000000
private def positiveCoeff7 : ℝ := 686481126681960008368805128428479210913692593562823614842187212302064070371766272879529096560517555968261899855186877117865137186092816000418675977517075171010379510291746562190133063123469829385690653452684510458222518476216938510318163/5143095145764313664516217568040619266054165331712685781290445499363047598590786203593370189096250640064695390938321740808396769526462382297456815871556379482841310398003544064000000000000000000000000000000000000000
private def positiveCoeff8 : ℝ := 307376366888446297594218278404004557477104239157497528072326393567260066681560610079281153391451711459273713924135313069875891418376495451569702712721594789657244544162355175014183570309795707260994961717400665945703897033783572822690907/288013328162801565212908183810274678899033258575910403752264947964330665521084027401228730589390035843622941892546017485270219093481893408657581688807157251039113382288198467584000000000000000000000000000000000000000
private def positiveCoeff9 : ℝ := 479721694795822091110860838438245613326154254916072872346166912386178337267897874648097270277165104423470860960408492113645129194137726673651381258378751971176120570663267633637225991208896813875786933689275601756948696467397302494347/72003332040700391303227045952568669724758314643977600938066236991082666380271006850307182647347508960905735473136504371317554773370473352164395422201789312759778345572049616896000000000000000000000000000000000000000
private def positiveCoeff10 : ℝ := 3921853300547232261840593612700320928719480980814963810170819858911283756733643426227201002386483546960431195241612943828756642366289339664759181621719610570843305353599473573028594114764389799172601909601547414192948291264620615039/144006664081400782606454091905137339449516629287955201876132473982165332760542013700614365294695017921811470946273008742635109546740946704328790844403578625519556691144099233792000000000000000000000000000000000000000
private def positivePolynomial (z : ℝ) : ℝ :=
  z^1*positiveCoeff1+
  z^2*positiveCoeff2+
  z^3*positiveCoeff3+
  z^4*positiveCoeff4+
  z^5*positiveCoeff5+
  z^6*positiveCoeff6+
  z^7*positiveCoeff7+
  z^8*positiveCoeff8+
  z^9*positiveCoeff9+
  z^10*positiveCoeff10

/-- The shifted origin determinant separates into positive low powers and a bounded negative tail. -/
theorem paid_gap_decomposition (z : ℝ) :
    paidGapReducedDet ((z+191)/10)+negativePolynomial z = constantTerm+positivePolynomial z := by
  simp only [paidGapReducedDet,originReducedDet,kernelCrossEnergy,originSchurNumerator,kernelAdjPair,
    kernelBorder_00,kernelBorder_01,kernelBorder_02,kernelBorder_10,kernelBorder_11,kernelBorder_12]
  dsimp only [loadCorner,kernelDet,kernelU,kernelV,kernelT]
  norm_num [mOrigin,EvenFiveOrigin.originMomentPolynomial,paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11,negativePolynomial,positivePolynomial,constantTerm,negativeCoeff11,negativeCoeff12,negativeCoeff13,negativeCoeff14,negativeCoeff15,negativeCoeff16,negativeCoeff17,negativeCoeff18,negativeCoeff19,negativeCoeff20,negativeCoeff21,negativeCoeff22,negativeCoeff23,negativeCoeff24,negativeCoeff25,negativeCoeff26,negativeCoeff27,negativeCoeff28,negativeCoeff29,negativeCoeff30,positiveCoeff1,positiveCoeff2,positiveCoeff3,positiveCoeff4,positiveCoeff5,positiveCoeff6,positiveCoeff7,positiveCoeff8,positiveCoeff9,positiveCoeff10]
  ring_nf
private theorem negative_sum_lt_constant : negativeCoefficientSum < constantTerm := by
  norm_num [negativeCoefficientSum,constantTerm,negativeCoeff11,negativeCoeff12,negativeCoeff13,negativeCoeff14,negativeCoeff15,negativeCoeff16,negativeCoeff17,negativeCoeff18,negativeCoeff19,negativeCoeff20,negativeCoeff21,negativeCoeff22,negativeCoeff23,negativeCoeff24,negativeCoeff25,negativeCoeff26,negativeCoeff27,negativeCoeff28,negativeCoeff29,negativeCoeff30]

private theorem negativePolynomial_le (z : ℝ) (hz : 0 ≤ z) (hzU : z ≤ 1) :
    negativePolynomial z ≤ negativeCoefficientSum := by
  have hp (n : ℕ) : z^n ≤ 1 := by simpa using pow_le_pow_left₀ hz hzU n
  have h11 : z^11*negativeCoeff11 ≤ negativeCoeff11 := by
    have h := mul_le_mul_of_nonneg_right (hp 11)
      (show 0 ≤ negativeCoeff11 by dsimp only [negativeCoeff11]; positivity)
    simpa only [one_mul] using h
  have h12 : z^12*negativeCoeff12 ≤ negativeCoeff12 := by
    have h := mul_le_mul_of_nonneg_right (hp 12)
      (show 0 ≤ negativeCoeff12 by dsimp only [negativeCoeff12]; positivity)
    simpa only [one_mul] using h
  have h13 : z^13*negativeCoeff13 ≤ negativeCoeff13 := by
    have h := mul_le_mul_of_nonneg_right (hp 13)
      (show 0 ≤ negativeCoeff13 by dsimp only [negativeCoeff13]; positivity)
    simpa only [one_mul] using h
  have h14 : z^14*negativeCoeff14 ≤ negativeCoeff14 := by
    have h := mul_le_mul_of_nonneg_right (hp 14)
      (show 0 ≤ negativeCoeff14 by dsimp only [negativeCoeff14]; positivity)
    simpa only [one_mul] using h
  have h15 : z^15*negativeCoeff15 ≤ negativeCoeff15 := by
    have h := mul_le_mul_of_nonneg_right (hp 15)
      (show 0 ≤ negativeCoeff15 by dsimp only [negativeCoeff15]; positivity)
    simpa only [one_mul] using h
  have h16 : z^16*negativeCoeff16 ≤ negativeCoeff16 := by
    have h := mul_le_mul_of_nonneg_right (hp 16)
      (show 0 ≤ negativeCoeff16 by dsimp only [negativeCoeff16]; positivity)
    simpa only [one_mul] using h
  have h17 : z^17*negativeCoeff17 ≤ negativeCoeff17 := by
    have h := mul_le_mul_of_nonneg_right (hp 17)
      (show 0 ≤ negativeCoeff17 by dsimp only [negativeCoeff17]; positivity)
    simpa only [one_mul] using h
  have h18 : z^18*negativeCoeff18 ≤ negativeCoeff18 := by
    have h := mul_le_mul_of_nonneg_right (hp 18)
      (show 0 ≤ negativeCoeff18 by dsimp only [negativeCoeff18]; positivity)
    simpa only [one_mul] using h
  have h19 : z^19*negativeCoeff19 ≤ negativeCoeff19 := by
    have h := mul_le_mul_of_nonneg_right (hp 19)
      (show 0 ≤ negativeCoeff19 by dsimp only [negativeCoeff19]; positivity)
    simpa only [one_mul] using h
  have h20 : z^20*negativeCoeff20 ≤ negativeCoeff20 := by
    have h := mul_le_mul_of_nonneg_right (hp 20)
      (show 0 ≤ negativeCoeff20 by dsimp only [negativeCoeff20]; positivity)
    simpa only [one_mul] using h
  have h21 : z^21*negativeCoeff21 ≤ negativeCoeff21 := by
    have h := mul_le_mul_of_nonneg_right (hp 21)
      (show 0 ≤ negativeCoeff21 by dsimp only [negativeCoeff21]; positivity)
    simpa only [one_mul] using h
  have h22 : z^22*negativeCoeff22 ≤ negativeCoeff22 := by
    have h := mul_le_mul_of_nonneg_right (hp 22)
      (show 0 ≤ negativeCoeff22 by dsimp only [negativeCoeff22]; positivity)
    simpa only [one_mul] using h
  have h23 : z^23*negativeCoeff23 ≤ negativeCoeff23 := by
    have h := mul_le_mul_of_nonneg_right (hp 23)
      (show 0 ≤ negativeCoeff23 by dsimp only [negativeCoeff23]; positivity)
    simpa only [one_mul] using h
  have h24 : z^24*negativeCoeff24 ≤ negativeCoeff24 := by
    have h := mul_le_mul_of_nonneg_right (hp 24)
      (show 0 ≤ negativeCoeff24 by dsimp only [negativeCoeff24]; positivity)
    simpa only [one_mul] using h
  have h25 : z^25*negativeCoeff25 ≤ negativeCoeff25 := by
    have h := mul_le_mul_of_nonneg_right (hp 25)
      (show 0 ≤ negativeCoeff25 by dsimp only [negativeCoeff25]; positivity)
    simpa only [one_mul] using h
  have h26 : z^26*negativeCoeff26 ≤ negativeCoeff26 := by
    have h := mul_le_mul_of_nonneg_right (hp 26)
      (show 0 ≤ negativeCoeff26 by dsimp only [negativeCoeff26]; positivity)
    simpa only [one_mul] using h
  have h27 : z^27*negativeCoeff27 ≤ negativeCoeff27 := by
    have h := mul_le_mul_of_nonneg_right (hp 27)
      (show 0 ≤ negativeCoeff27 by dsimp only [negativeCoeff27]; positivity)
    simpa only [one_mul] using h
  have h28 : z^28*negativeCoeff28 ≤ negativeCoeff28 := by
    have h := mul_le_mul_of_nonneg_right (hp 28)
      (show 0 ≤ negativeCoeff28 by dsimp only [negativeCoeff28]; positivity)
    simpa only [one_mul] using h
  have h29 : z^29*negativeCoeff29 ≤ negativeCoeff29 := by
    have h := mul_le_mul_of_nonneg_right (hp 29)
      (show 0 ≤ negativeCoeff29 by dsimp only [negativeCoeff29]; positivity)
    simpa only [one_mul] using h
  have h30 : z^30*negativeCoeff30 ≤ negativeCoeff30 := by
    have h := mul_le_mul_of_nonneg_right (hp 30)
      (show 0 ≤ negativeCoeff30 by dsimp only [negativeCoeff30]; positivity)
    simpa only [one_mul] using h
  dsimp only [negativePolynomial,negativeCoefficientSum]
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h11 h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22) h23) h24) h25) h26) h27) h28) h29) h30)

private theorem positivePolynomial_nonneg (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ positivePolynomial z := by
  dsimp only [positivePolynomial,positiveCoeff1,positiveCoeff2,positiveCoeff3,
    positiveCoeff4,positiveCoeff5,positiveCoeff6,positiveCoeff7,positiveCoeff8,
    positiveCoeff9,positiveCoeff10]
  positivity

private theorem positive_remainder (z : ℝ) (hz : 0 ≤ z) :
    constantTerm ≤ paidGapReducedDet ((z+191)/10)+negativePolynomial z := by
  rw [paid_gap_decomposition]
  exact le_add_of_nonneg_right (positivePolynomial_nonneg z hz)

/-- The reduced origin determinant is positive throughout the certified parameter interval. -/
theorem paid_gap_reduced_det_positive (z : ℝ) (hz : 0 ≤ z) (hzU : z ≤ 1) :
    0 < paidGapReducedDet ((z+191)/10) := by
  have h : negativePolynomial z < paidGapReducedDet ((z+191)/10)+negativePolynomial z :=
    (negativePolynomial_le z hz hzU).trans_lt
      (negative_sum_lt_constant.trans_le (positive_remainder z hz))
  have h' : (0:ℝ)+negativePolynomial z <
      paidGapReducedDet ((z+191)/10)+negativePolynomial z := by
    simpa only [zero_add] using h
  exact (add_lt_add_iff_right (negativePolynomial z)).mp h'

/-- Every normalization pivot is strictly positive. -/
theorem diag_pos (i : Fin 5) : 0 < diag i := by
  fin_cases i
  · exact diagonal_positive_0
  · exact diagonal_positive_1
  · exact diagonal_positive_2
  · exact diagonal_positive_3
  · exact diagonal_positive_4

theorem loss_pos : 0 < loss := by
  norm_num [loss,EvenFiveBoundary.scaleSevenCompensationLoss]

private theorem sevenPolynomial_symm (a X : ℝ) (i j : Fin 5) :
    sevenPolynomial a X i j = sevenPolynomial a X j i := by
  unfold sevenPolynomial
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [Nat.add_comm v.val u.val]
  ring

private theorem sevenTail_symm (i j : Fin 5) : sevenTail i j = sevenTail j i := by
  unfold sevenTail
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [Nat.add_comm v.val u.val]
  ring

private theorem sevenError_symm (i j : Fin 5) : sevenError i j = sevenError j i := by
  simp only [sevenError,sevenPolynomial_symm _ _ i j,sevenTail_symm i j]

private theorem sevenError_split (i j : Fin 5) :
    sevenError i j/loss =
      (8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 i j|/(121*loss)+
      16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 i j|/(121*loss)+
      sevenTail i j/loss := by
  dsimp only [sevenError]
  ring

private theorem error_diagonal_strict (i : Fin 5) : sevenError i i/loss < diag i/32 := by
  have hm : (8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 i i|/(121*loss) < diag i/96 := by
    fin_cases i
    · exact mixed_error_0_0
    · exact mixed_error_1_1
    · exact mixed_error_2_2
    · exact mixed_error_3_3
    · exact mixed_error_4_4
  have hs : 16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 i i|/(121*loss) < diag i/96 := by
    fin_cases i
    · exact second_error_0_0
    · exact second_error_1_1
    · exact second_error_2_2
    · exact second_error_3_3
    · exact second_error_4_4
  have ht : sevenTail i i/loss < diag i/96 := by
    fin_cases i
    · exact tail_error_0_0
    · exact tail_error_1_1
    · exact tail_error_2_2
    · exact tail_error_3_3
    · exact tail_error_4_4
  rw [sevenError_split]
  linarith only [hm,hs,ht]

private theorem mixed_square_strict (i j : Fin 5) (hij : i < j) :
    ((8*((19/25000000000:ℝ)-(3/4000000000)))*|sevenPolynomial 196 35 i j|/(121*loss))^2 < diag i*diag j/96^2 := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · exact mixed_error_0_1
  · exact mixed_error_0_2
  · exact mixed_error_0_3
  · exact mixed_error_0_4
  · exact mixed_error_1_2
  · exact mixed_error_1_3
  · exact mixed_error_1_4
  · exact mixed_error_2_3
  · exact mixed_error_2_4
  · exact mixed_error_3_4

private theorem second_square_strict (i j : Fin 5) (hij : i < j) :
    (16*((19/25000000000:ℝ)^2-(3/4000000000:ℝ)^2)*|sevenPolynomial 784 56 i j|/(121*loss))^2 < diag i*diag j/96^2 := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · exact second_error_0_1
  · exact second_error_0_2
  · exact second_error_0_3
  · exact second_error_0_4
  · exact second_error_1_2
  · exact second_error_1_3
  · exact second_error_1_4
  · exact second_error_2_3
  · exact second_error_2_4
  · exact second_error_3_4

private theorem tail_square_strict (i j : Fin 5) (hij : i < j) :
    (sevenTail i j/loss)^2 < diag i*diag j/96^2 := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · exact tail_error_0_1
  · exact tail_error_0_2
  · exact tail_error_0_3
  · exact tail_error_0_4
  · exact tail_error_1_2
  · exact tail_error_1_3
  · exact tail_error_1_4
  · exact tail_error_2_3
  · exact tail_error_2_4
  · exact tail_error_3_4

private theorem component_lt_sqrt {a t d : ℝ} (ht : 0 < t) (ht2 : t^2=d)
    (ha : a^2 < d/96^2) : a < t/96 := by
  by_contra h
  have hd : 0 ≤ a-t/96 := sub_nonneg.mpr (le_of_not_gt h)
  have hs : 0 ≤ a+t/96 := by linarith only [hd,ht]
  have hp := mul_nonneg hd hs
  nlinarith only [hp,ha,ht2]

private theorem error_upper_strict (i j : Fin 5) (hij : i < j) :
    sevenError i j/loss < Real.sqrt (diag i)*Real.sqrt (diag j)/32 := by
  have ht : 0 < Real.sqrt (diag i)*Real.sqrt (diag j) :=
    mul_pos (Real.sqrt_pos.2 (diag_pos i)) (Real.sqrt_pos.2 (diag_pos j))
  have ht2 : (Real.sqrt (diag i)*Real.sqrt (diag j))^2 = diag i*diag j := by
    rw [mul_pow,Real.sq_sqrt (diag_pos i).le,Real.sq_sqrt (diag_pos j).le]
  have hm := component_lt_sqrt ht ht2 (mixed_square_strict i j hij)
  have hs := component_lt_sqrt ht ht2 (second_square_strict i j hij)
  have htail := component_lt_sqrt ht ht2 (tail_square_strict i j hij)
  rw [sevenError_split]
  linarith only [hm,hs,htail]

/-- The complete scale-seven error costs strictly less than one thirty-second per normalized entry. -/
theorem seven_error_strict (i j : Fin 5) :
    sevenError i j/loss < Real.sqrt (diag i)*Real.sqrt (diag j)/32 := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact error_upper_strict i j hij
  · have hroot : Real.sqrt (diag i)*Real.sqrt (diag i) = diag i := by
      nlinarith only [Real.sq_sqrt (diag_pos i).le]
    rw [hroot]
    exact error_diagonal_strict i
  · rw [sevenError_symm i j,mul_comm (Real.sqrt (diag i))]
    exact error_upper_strict j i hij

/-- The retained bilinear form in the unnormalized Schur coordinates. -/
def sevenRetainedRaw (i j : Fin 5) : ℝ :=
  (sevenPolynomial 49 14 i j+8*retainedRatio*sevenPolynomial 196 35 i j+
    16*retainedRatio^2*sevenPolynomial 784 56 i j)/121

/-- The load coordinates of a Schur basis vector. -/
def sevenLoad (i : Fin 5) : Fin 2 → ℝ :=
  if i.val<3 then 0 else loadColumn ⟨i.val-3,by omega⟩

/-- The positive retained load in the unnormalized Schur coordinates. -/
def sevenLoadRaw (i j : Fin 5) : ℝ :=
  ∑ a : Fin 2, ∑ b : Fin 2, sevenLoad i a*paidSevenSchur a b*sevenLoad j b


/-- The normalized Schur basis at scale seven. -/
def sevenBasis : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => sevenVector j i/Real.sqrt (diag j)

/-- The complete native matrix divided by its compensation loss in Schur coordinates. -/
def sevenSourceGram : Matrix (Fin 5) (Fin 5) ℝ :=
  (loss*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2)⁻¹ •
    (sevenBasisᴴ*nativeShiftedMatrix 5 0 EvenFiveBoundary.witnessCenter*sevenBasis)

/-- The retained two-atom matrix in normalized Schur coordinates. -/
def sevenModelGram : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => sevenRetainedRaw i j/(loss*(Real.sqrt (diag i)*Real.sqrt (diag j)))

private theorem sevenSourceGram_entry (i j : Fin 5) :
    sevenSourceGram i j =
      EvenFiveBoundary.scaleSevenEnergy (sevenVector i) (sevenVector j)
        EvenFiveBoundary.witnessCenter/
      (loss*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2*
        (Real.sqrt (diag i)*Real.sqrt (diag j))) := by
  simp only [sevenSourceGram,Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply,
    Matrix.conjTranspose_apply,sevenBasis,star_trivial,Finset.sum_mul,
    EvenFiveBoundary.scaleSevenEnergy,nativeShiftedMatrix,add_zero,Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem first_mass_pos : 0 < thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1 := by
  apply thetaCuspSourceTerm_pos_of_pos_of_nat_pos
  · unfold EvenFiveBoundary.witnessCenter
    apply div_pos
    · apply Real.log_pos
      exact (lt_div_iff₀ Real.pi_pos).mpr (by nlinarith only [Real.pi_lt_four])
    · norm_num
  · norm_num

private theorem normalized_error_strict {E R e f l t : ℝ}
    (hf : 0 < f) (hl : 0 < l) (ht : 0 < t)
    (hsource : |E-f^2*R| ≤ e*f^2) (he : e/l < t/32) :
    |E/(l*f^2*t)-R/(l*t)| < 1/32 := by
  have hd : 0 < l*f^2*t := mul_pos (mul_pos hl (sq_pos_of_pos hf)) ht
  have hid : E/(l*f^2*t)-R/(l*t) = (E-f^2*R)/(l*f^2*t) := by
    field_simp [hf.ne',hl.ne',ht.ne']
  rw [hid,abs_div,abs_of_pos hd]
  apply (div_lt_iff₀ hd).mpr
  have hem := mul_lt_mul_of_pos_right ((div_lt_iff₀ hl).mp he) (sq_pos_of_pos hf)
  calc
    |E-f^2*R| ≤ e*f^2 := hsource
    _ < (1/32)*(l*f^2*t) := by nlinarith only [hem]

/-- The full theta source differs from its retained model by strictly less than one thirty-second per entry. -/
theorem sevenSourceGram_error_strict (i j : Fin 5) :
    |(sevenSourceGram-sevenModelGram) i j| < 1/32 := by
  have hs := EvenFiveBoundary.scaleSeven_retained_bilinear_error (sevenVector i) (sevenVector j)
  change |EvenFiveBoundary.scaleSevenEnergy (sevenVector i) (sevenVector j)
      EvenFiveBoundary.witnessCenter-
    thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2*sevenRetainedRaw i j| ≤
      sevenError i j*thetaCuspSourceTerm EvenFiveBoundary.witnessCenter 1^2 at hs
  rw [Matrix.sub_apply,sevenSourceGram_entry]
  exact normalized_error_strict first_mass_pos loss_pos
    (mul_pos (Real.sqrt_pos.2 (diag_pos i)) (Real.sqrt_pos.2 (diag_pos j))) hs (seven_error_strict i j)

private theorem schur2_symm (m : ℕ → ℝ) (i j : Fin 2) : schur2 m i j = schur2 m j i := by
  fin_cases i <;> fin_cases j <;> norm_num [schur2] <;> ring

private theorem gap_symm (i j : Fin 2) : gap i j = gap j i := by
  exact congrArg₂ (fun a b => a/(3*mOrigin (191/10) 0)+b/loss)
    (schur2_symm _ i j) (schur2_symm _ i j)

/-- The error-paid retained load is symmetric. -/
theorem paidSevenSchur_hermitian : paidSevenSchur.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial]
  exact congrArg₂ (fun a b => a/loss-(5/32)*b)
    (schur2_symm _ j i) (gap_symm j i)

private theorem loadCorner_symm (m : ℕ → ℝ) (i j : Fin 2) :
    loadCorner m i j = loadCorner m j i := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem kernelAdjPair_symm (m : ℕ → ℝ) (p q : Fin 3 → ℝ) :
    kernelAdjPair m p q = kernelAdjPair m q p := by
  dsimp only [kernelAdjPair]
  ring

/-- The denominator-cleared origin gap is symmetric. -/
theorem paidGapNumerator_hermitian (X : ℝ) : (paidGapNumerator X).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial,paidGapNumerator,originSchurNumerator]
  rw [loadCorner_symm _ j i,kernelAdjPair_symm]
  have hv := congrFun (congrFun paidSevenSchur_hermitian i) j
  simp only [Matrix.conjTranspose_apply,star_trivial] at hv
  rw [hv]

end GaloisForLFunctions.ThetaCuspSections.EvenFiveEndpoint
