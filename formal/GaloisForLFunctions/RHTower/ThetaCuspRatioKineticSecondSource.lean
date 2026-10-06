import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSecondSourceParts
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

def completeKineticSourceCoeff1Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 1 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 1 1=kineticDriftCell h completeKineticSlope 1 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff1Row1Norm h).property,(kineticSourcePart4Coeff1Row1Norm h).property,(kineticSourcePart6Coeff1Row1Norm h).property,(kineticSourcePart8Coeff1Row1Norm h).property,(kineticSourcePart10Coeff1Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff1Row1Norm,kineticSourcePart4Coeff1Row1Norm,kineticSourcePart6Coeff1Row1Norm,kineticSourcePart8Coeff1Row1Norm,kineticSourcePart10Coeff1Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff1Row1RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 1 1).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff1Row1Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff1Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff1Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 1 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 1 2=kineticDriftCell h completeKineticSlope 1 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff1Row2Norm h).property,(kineticSourcePart4Coeff1Row2Norm h).property,(kineticSourcePart6Coeff1Row2Norm h).property,(kineticSourcePart8Coeff1Row2Norm h).property,(kineticSourcePart10Coeff1Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff1Row2Norm,kineticSourcePart4Coeff1Row2Norm,kineticSourcePart6Coeff1Row2Norm,kineticSourcePart8Coeff1Row2Norm,kineticSourcePart10Coeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff1Row2RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 1 2).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff1Row2Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff1Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff1Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 1 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 1 3=kineticDriftCell h completeKineticSlope 1 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff1Row3Norm h).property,(kineticSourcePart4Coeff1Row3Norm h).property,(kineticSourcePart6Coeff1Row3Norm h).property,(kineticSourcePart8Coeff1Row3Norm h).property,(kineticSourcePart10Coeff1Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff1Row3Norm,kineticSourcePart4Coeff1Row3Norm,kineticSourcePart6Coeff1Row3Norm,kineticSourcePart8Coeff1Row3Norm,kineticSourcePart10Coeff1Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff1Row3RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 1 3).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff1Row3Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff1Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff1Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 1 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 1 4=kineticDriftCell h completeKineticSlope 1 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff1Row4Norm h).property,(kineticSourcePart4Coeff1Row4Norm h).property,(kineticSourcePart6Coeff1Row4Norm h).property,(kineticSourcePart8Coeff1Row4Norm h).property,(kineticSourcePart10Coeff1Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff1Row4Norm,kineticSourcePart4Coeff1Row4Norm,kineticSourcePart6Coeff1Row4Norm,kineticSourcePart8Coeff1Row4Norm,kineticSourcePart10Coeff1Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff1Row4RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 1 4).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff1Row4Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff1Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff1Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 1 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 1 5=kineticDriftCell h completeKineticSlope 1 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff1Row5Norm h).property,(kineticSourcePart4Coeff1Row5Norm h).property,(kineticSourcePart6Coeff1Row5Norm h).property,(kineticSourcePart8Coeff1Row5Norm h).property,(kineticSourcePart10Coeff1Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff1Row5Norm,kineticSourcePart4Coeff1Row5Norm,kineticSourcePart6Coeff1Row5Norm,kineticSourcePart8Coeff1Row5Norm,kineticSourcePart10Coeff1Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff1Row5RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 1 5).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff1Row5Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff1Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff1Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 1 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 1 6=kineticDriftCell h completeKineticSlope 1 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff1Row6Norm h).property,(kineticSourcePart4Coeff1Row6Norm h).property,(kineticSourcePart6Coeff1Row6Norm h).property,(kineticSourcePart8Coeff1Row6Norm h).property,(kineticSourcePart10Coeff1Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff1Row6Norm,kineticSourcePart4Coeff1Row6Norm,kineticSourcePart6Coeff1Row6Norm,kineticSourcePart8Coeff1Row6Norm,kineticSourcePart10Coeff1Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff1Row6RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 1 6).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff1Row6Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff1Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff1Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 1 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 1 7=kineticDriftCell h completeKineticSlope 1 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff1Row7Norm h).property,(kineticSourcePart4Coeff1Row7Norm h).property,(kineticSourcePart6Coeff1Row7Norm h).property,(kineticSourcePart8Coeff1Row7Norm h).property,(kineticSourcePart10Coeff1Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff1Row7Norm,kineticSourcePart4Coeff1Row7Norm,kineticSourcePart6Coeff1Row7Norm,kineticSourcePart8Coeff1Row7Norm,kineticSourcePart10Coeff1Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff1Row7RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 1 7).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff1Row7Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff1Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff1Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 1 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 1 8=kineticDriftCell h completeKineticSlope 1 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff1Row8Norm h).property,(kineticSourcePart4Coeff1Row8Norm h).property,(kineticSourcePart6Coeff1Row8Norm h).property,(kineticSourcePart8Coeff1Row8Norm h).property,(kineticSourcePart10Coeff1Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff1Row8Norm,kineticSourcePart4Coeff1Row8Norm,kineticSourcePart6Coeff1Row8Norm,kineticSourcePart8Coeff1Row8Norm,kineticSourcePart10Coeff1Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff1Row8RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 1 8).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff1Row8Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff1Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff1Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 1 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 1 9=kineticDriftCell h completeKineticSlope 1 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff1Row9Norm h).property,(kineticSourcePart4Coeff1Row9Norm h).property,(kineticSourcePart6Coeff1Row9Norm h).property,(kineticSourcePart8Coeff1Row9Norm h).property,(kineticSourcePart10Coeff1Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff1Row9Norm,kineticSourcePart4Coeff1Row9Norm,kineticSourcePart6Coeff1Row9Norm,kineticSourcePart8Coeff1Row9Norm,kineticSourcePart10Coeff1Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff1Row9RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 1 9).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff1Row9Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff1Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff1Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 1 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 1 10=kineticDriftCell h completeKineticSlope 1 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff1Row10Norm h).property,(kineticSourcePart4Coeff1Row10Norm h).property,(kineticSourcePart6Coeff1Row10Norm h).property,(kineticSourcePart8Coeff1Row10Norm h).property,(kineticSourcePart10Coeff1Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff1Row10Norm,kineticSourcePart4Coeff1Row10Norm,kineticSourcePart6Coeff1Row10Norm,kineticSourcePart8Coeff1Row10Norm,kineticSourcePart10Coeff1Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff1Row10RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 1 10).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff1Row10Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff1Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def reducedKineticFullCoefficient1RealNorm (h v : ℝ) :
    {c : ℝ // reducedKineticCoefficient h v 1=c} := by
  have he := reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) 1
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have hr := congrArg Complex.re he
  change reducedKineticCoefficient h v 1=_ at hr
  simp only [Complex.add_re,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] at hr
  conv at hr =>
    rhs
    rw [(kineticSourceCoeff1Row1RealNorm h).property,(kineticSourceCoeff1Row2RealNorm h).property,(kineticSourceCoeff1Row3RealNorm h).property,(kineticSourceCoeff1Row4RealNorm h).property,(kineticSourceCoeff1Row5RealNorm h).property,(kineticSourceCoeff1Row6RealNorm h).property,(kineticSourceCoeff1Row7RealNorm h).property,(kineticSourceCoeff1Row8RealNorm h).property,(kineticSourceCoeff1Row9RealNorm h).property,(kineticSourceCoeff1Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff1Row1RealNorm,kineticSourceCoeff1Row2RealNorm,kineticSourceCoeff1Row3RealNorm,kineticSourceCoeff1Row4RealNorm,kineticSourceCoeff1Row5RealNorm,kineticSourceCoeff1Row6RealNorm,kineticSourceCoeff1Row7RealNorm,kineticSourceCoeff1Row8RealNorm,kineticSourceCoeff1Row9RealNorm,kineticSourceCoeff1Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,hr⟩

theorem reducedKineticControl_one (h v Z : ℝ) :
    reducedKineticControl h v Z 1=19*reducedKineticCoefficient h v 0+
      reducedKineticCoefficient h v 1*Z := by
  norm_num [reducedKineticControl,kineticControl,
    HTGeometry.EvenCompactBernstein.degreeElevationCoefficient,Finset.sum_range_succ,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
  ring

def reducedKineticDefectControl1Norm (h r : ℝ) :
    {c : ℝ // reducedKineticControl h (9-r*h^2) (1/3) 1=c} := by
  have he := reducedKineticControl_one h (9-r*h^2) (1/3)
  conv at he =>
    rhs
    rw [(reducedKineticFullCoefficient0RealNorm h (9-r*h^2)).property,
      (reducedKineticFullCoefficient1RealNorm h (9-r*h^2)).property]
    dsimp only [reducedKineticFullCoefficient0RealNorm,reducedKineticFullCoefficient1RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction
