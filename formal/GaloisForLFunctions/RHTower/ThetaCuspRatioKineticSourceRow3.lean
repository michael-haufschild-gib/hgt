import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceParts3
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def completeKineticSourceCoeff3Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 3 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 3 1=kineticDriftCell h completeKineticSlope 3 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff3Row1Norm h).property,(kineticSourcePart4Coeff3Row1Norm h).property,(kineticSourcePart6Coeff3Row1Norm h).property,(kineticSourcePart8Coeff3Row1Norm h).property,(kineticSourcePart10Coeff3Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff3Row1Norm,kineticSourcePart4Coeff3Row1Norm,kineticSourcePart6Coeff3Row1Norm,kineticSourcePart8Coeff3Row1Norm,kineticSourcePart10Coeff3Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff3Row1RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 3 1).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff3Row1Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff3Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff3Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 3 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 3 2=kineticDriftCell h completeKineticSlope 3 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff3Row2Norm h).property,(kineticSourcePart4Coeff3Row2Norm h).property,(kineticSourcePart6Coeff3Row2Norm h).property,(kineticSourcePart8Coeff3Row2Norm h).property,(kineticSourcePart10Coeff3Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff3Row2Norm,kineticSourcePart4Coeff3Row2Norm,kineticSourcePart6Coeff3Row2Norm,kineticSourcePart8Coeff3Row2Norm,kineticSourcePart10Coeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff3Row2RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 3 2).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff3Row2Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff3Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff3Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 3 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 3 3=kineticDriftCell h completeKineticSlope 3 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff3Row3Norm h).property,(kineticSourcePart4Coeff3Row3Norm h).property,(kineticSourcePart6Coeff3Row3Norm h).property,(kineticSourcePart8Coeff3Row3Norm h).property,(kineticSourcePart10Coeff3Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff3Row3Norm,kineticSourcePart4Coeff3Row3Norm,kineticSourcePart6Coeff3Row3Norm,kineticSourcePart8Coeff3Row3Norm,kineticSourcePart10Coeff3Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff3Row3RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 3 3).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff3Row3Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff3Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff3Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 3 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 3 4=kineticDriftCell h completeKineticSlope 3 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff3Row4Norm h).property,(kineticSourcePart4Coeff3Row4Norm h).property,(kineticSourcePart6Coeff3Row4Norm h).property,(kineticSourcePart8Coeff3Row4Norm h).property,(kineticSourcePart10Coeff3Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff3Row4Norm,kineticSourcePart4Coeff3Row4Norm,kineticSourcePart6Coeff3Row4Norm,kineticSourcePart8Coeff3Row4Norm,kineticSourcePart10Coeff3Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff3Row4RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 3 4).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff3Row4Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff3Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff3Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 3 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 3 5=kineticDriftCell h completeKineticSlope 3 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff3Row5Norm h).property,(kineticSourcePart4Coeff3Row5Norm h).property,(kineticSourcePart6Coeff3Row5Norm h).property,(kineticSourcePart8Coeff3Row5Norm h).property,(kineticSourcePart10Coeff3Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff3Row5Norm,kineticSourcePart4Coeff3Row5Norm,kineticSourcePart6Coeff3Row5Norm,kineticSourcePart8Coeff3Row5Norm,kineticSourcePart10Coeff3Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff3Row5RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 3 5).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff3Row5Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff3Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff3Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 3 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 3 6=kineticDriftCell h completeKineticSlope 3 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff3Row6Norm h).property,(kineticSourcePart4Coeff3Row6Norm h).property,(kineticSourcePart6Coeff3Row6Norm h).property,(kineticSourcePart8Coeff3Row6Norm h).property,(kineticSourcePart10Coeff3Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff3Row6Norm,kineticSourcePart4Coeff3Row6Norm,kineticSourcePart6Coeff3Row6Norm,kineticSourcePart8Coeff3Row6Norm,kineticSourcePart10Coeff3Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff3Row6RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 3 6).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff3Row6Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff3Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff3Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 3 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 3 7=kineticDriftCell h completeKineticSlope 3 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff3Row7Norm h).property,(kineticSourcePart4Coeff3Row7Norm h).property,(kineticSourcePart6Coeff3Row7Norm h).property,(kineticSourcePart8Coeff3Row7Norm h).property,(kineticSourcePart10Coeff3Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff3Row7Norm,kineticSourcePart4Coeff3Row7Norm,kineticSourcePart6Coeff3Row7Norm,kineticSourcePart8Coeff3Row7Norm,kineticSourcePart10Coeff3Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff3Row7RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 3 7).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff3Row7Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff3Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff3Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 3 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 3 8=kineticDriftCell h completeKineticSlope 3 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff3Row8Norm h).property,(kineticSourcePart4Coeff3Row8Norm h).property,(kineticSourcePart6Coeff3Row8Norm h).property,(kineticSourcePart8Coeff3Row8Norm h).property,(kineticSourcePart10Coeff3Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff3Row8Norm,kineticSourcePart4Coeff3Row8Norm,kineticSourcePart6Coeff3Row8Norm,kineticSourcePart8Coeff3Row8Norm,kineticSourcePart10Coeff3Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff3Row8RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 3 8).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff3Row8Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff3Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff3Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 3 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 3 9=kineticDriftCell h completeKineticSlope 3 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff3Row9Norm h).property,(kineticSourcePart4Coeff3Row9Norm h).property,(kineticSourcePart6Coeff3Row9Norm h).property,(kineticSourcePart8Coeff3Row9Norm h).property,(kineticSourcePart10Coeff3Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff3Row9Norm,kineticSourcePart4Coeff3Row9Norm,kineticSourcePart6Coeff3Row9Norm,kineticSourcePart8Coeff3Row9Norm,kineticSourcePart10Coeff3Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff3Row9RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 3 9).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff3Row9Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff3Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff3Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 3 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 3 10=kineticDriftCell h completeKineticSlope 3 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff3Row10Norm h).property,(kineticSourcePart4Coeff3Row10Norm h).property,(kineticSourcePart6Coeff3Row10Norm h).property,(kineticSourcePart8Coeff3Row10Norm h).property,(kineticSourcePart10Coeff3Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff3Row10Norm,kineticSourcePart4Coeff3Row10Norm,kineticSourcePart6Coeff3Row10Norm,kineticSourcePart8Coeff3Row10Norm,kineticSourcePart10Coeff3Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff3Row10RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 3 10).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff3Row10Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff3Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticSourceCoeff3Row1_zero (h : ℂ) :
    kineticDriftCell h completeKineticSlope 3 1=0 := by
  rw [(completeKineticSourceCoeff3Row1Norm h).property]
  norm_num [completeKineticSourceCoeff3Row1Norm,Nat.rawCast,Int.rawCast]

def reducedKineticFullCoefficient3RealNorm (h v : ℝ) :
    {c : ℝ // reducedKineticCoefficient h v 3=c} := by
  have he := reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) 3
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have hr := congrArg Complex.re he
  change reducedKineticCoefficient h v 3=_ at hr
  simp only [Complex.add_re,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] at hr
  conv at hr =>
    rhs
    rw [(kineticSourceCoeff3Row1RealNorm h).property,(kineticSourceCoeff3Row2RealNorm h).property,(kineticSourceCoeff3Row3RealNorm h).property,(kineticSourceCoeff3Row4RealNorm h).property,(kineticSourceCoeff3Row5RealNorm h).property,(kineticSourceCoeff3Row6RealNorm h).property,(kineticSourceCoeff3Row7RealNorm h).property,(kineticSourceCoeff3Row8RealNorm h).property,(kineticSourceCoeff3Row9RealNorm h).property,(kineticSourceCoeff3Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff3Row1RealNorm,kineticSourceCoeff3Row2RealNorm,kineticSourceCoeff3Row3RealNorm,kineticSourceCoeff3Row4RealNorm,kineticSourceCoeff3Row5RealNorm,kineticSourceCoeff3Row6RealNorm,kineticSourceCoeff3Row7RealNorm,kineticSourceCoeff3Row8RealNorm,kineticSourceCoeff3Row9RealNorm,kineticSourceCoeff3Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,hr⟩

theorem reducedKineticCoefficient3_zero_drift (h : ℝ) :
    reducedKineticCoefficient h 0 3=0 := by
  change ((reducedKineticDriftCoefficient (h:ℂ) 3).eval 0).re=0
  rw [←Polynomial.coeff_zero_eq_eval_zero,reducedKineticDriftCoefficient_coeff]
  change (kineticDriftCell (h:ℂ) completeKineticSlope 3 1).re=0
  rw [kineticSourceCoeff3Row1_zero]
  rfl

end
end HTGeometry.ThetaRatioKineticContraction

