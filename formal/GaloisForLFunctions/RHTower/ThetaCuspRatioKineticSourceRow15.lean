import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceParts15
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def completeKineticSourceCoeff15Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 15 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 15 1=kineticDriftCell h completeKineticSlope 15 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff15Row1Norm h).property,(kineticSourcePart4Coeff15Row1Norm h).property,(kineticSourcePart6Coeff15Row1Norm h).property,(kineticSourcePart8Coeff15Row1Norm h).property,(kineticSourcePart10Coeff15Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff15Row1Norm,kineticSourcePart4Coeff15Row1Norm,kineticSourcePart6Coeff15Row1Norm,kineticSourcePart8Coeff15Row1Norm,kineticSourcePart10Coeff15Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff15Row1RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 15 1).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff15Row1Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff15Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff15Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 15 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 15 2=kineticDriftCell h completeKineticSlope 15 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff15Row2Norm h).property,(kineticSourcePart4Coeff15Row2Norm h).property,(kineticSourcePart6Coeff15Row2Norm h).property,(kineticSourcePart8Coeff15Row2Norm h).property,(kineticSourcePart10Coeff15Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff15Row2Norm,kineticSourcePart4Coeff15Row2Norm,kineticSourcePart6Coeff15Row2Norm,kineticSourcePart8Coeff15Row2Norm,kineticSourcePart10Coeff15Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff15Row2RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 15 2).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff15Row2Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff15Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff15Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 15 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 15 3=kineticDriftCell h completeKineticSlope 15 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff15Row3Norm h).property,(kineticSourcePart4Coeff15Row3Norm h).property,(kineticSourcePart6Coeff15Row3Norm h).property,(kineticSourcePart8Coeff15Row3Norm h).property,(kineticSourcePart10Coeff15Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff15Row3Norm,kineticSourcePart4Coeff15Row3Norm,kineticSourcePart6Coeff15Row3Norm,kineticSourcePart8Coeff15Row3Norm,kineticSourcePart10Coeff15Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff15Row3RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 15 3).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff15Row3Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff15Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff15Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 15 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 15 4=kineticDriftCell h completeKineticSlope 15 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff15Row4Norm h).property,(kineticSourcePart4Coeff15Row4Norm h).property,(kineticSourcePart6Coeff15Row4Norm h).property,(kineticSourcePart8Coeff15Row4Norm h).property,(kineticSourcePart10Coeff15Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff15Row4Norm,kineticSourcePart4Coeff15Row4Norm,kineticSourcePart6Coeff15Row4Norm,kineticSourcePart8Coeff15Row4Norm,kineticSourcePart10Coeff15Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff15Row4RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 15 4).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff15Row4Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff15Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff15Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 15 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 15 5=kineticDriftCell h completeKineticSlope 15 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff15Row5Norm h).property,(kineticSourcePart4Coeff15Row5Norm h).property,(kineticSourcePart6Coeff15Row5Norm h).property,(kineticSourcePart8Coeff15Row5Norm h).property,(kineticSourcePart10Coeff15Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff15Row5Norm,kineticSourcePart4Coeff15Row5Norm,kineticSourcePart6Coeff15Row5Norm,kineticSourcePart8Coeff15Row5Norm,kineticSourcePart10Coeff15Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff15Row5RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 15 5).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff15Row5Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff15Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff15Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 15 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 15 6=kineticDriftCell h completeKineticSlope 15 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff15Row6Norm h).property,(kineticSourcePart4Coeff15Row6Norm h).property,(kineticSourcePart6Coeff15Row6Norm h).property,(kineticSourcePart8Coeff15Row6Norm h).property,(kineticSourcePart10Coeff15Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff15Row6Norm,kineticSourcePart4Coeff15Row6Norm,kineticSourcePart6Coeff15Row6Norm,kineticSourcePart8Coeff15Row6Norm,kineticSourcePart10Coeff15Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff15Row6RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 15 6).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff15Row6Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff15Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff15Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 15 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 15 7=kineticDriftCell h completeKineticSlope 15 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff15Row7Norm h).property,(kineticSourcePart4Coeff15Row7Norm h).property,(kineticSourcePart6Coeff15Row7Norm h).property,(kineticSourcePart8Coeff15Row7Norm h).property,(kineticSourcePart10Coeff15Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff15Row7Norm,kineticSourcePart4Coeff15Row7Norm,kineticSourcePart6Coeff15Row7Norm,kineticSourcePart8Coeff15Row7Norm,kineticSourcePart10Coeff15Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff15Row7RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 15 7).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff15Row7Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff15Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff15Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 15 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 15 8=kineticDriftCell h completeKineticSlope 15 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff15Row8Norm h).property,(kineticSourcePart4Coeff15Row8Norm h).property,(kineticSourcePart6Coeff15Row8Norm h).property,(kineticSourcePart8Coeff15Row8Norm h).property,(kineticSourcePart10Coeff15Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff15Row8Norm,kineticSourcePart4Coeff15Row8Norm,kineticSourcePart6Coeff15Row8Norm,kineticSourcePart8Coeff15Row8Norm,kineticSourcePart10Coeff15Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff15Row8RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 15 8).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff15Row8Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff15Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff15Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 15 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 15 9=kineticDriftCell h completeKineticSlope 15 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff15Row9Norm h).property,(kineticSourcePart4Coeff15Row9Norm h).property,(kineticSourcePart6Coeff15Row9Norm h).property,(kineticSourcePart8Coeff15Row9Norm h).property,(kineticSourcePart10Coeff15Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff15Row9Norm,kineticSourcePart4Coeff15Row9Norm,kineticSourcePart6Coeff15Row9Norm,kineticSourcePart8Coeff15Row9Norm,kineticSourcePart10Coeff15Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff15Row9RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 15 9).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff15Row9Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff15Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff15Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 15 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 15 10=kineticDriftCell h completeKineticSlope 15 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff15Row10Norm h).property,(kineticSourcePart4Coeff15Row10Norm h).property,(kineticSourcePart6Coeff15Row10Norm h).property,(kineticSourcePart8Coeff15Row10Norm h).property,(kineticSourcePart10Coeff15Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff15Row10Norm,kineticSourcePart4Coeff15Row10Norm,kineticSourcePart6Coeff15Row10Norm,kineticSourcePart8Coeff15Row10Norm,kineticSourcePart10Coeff15Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff15Row10RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 15 10).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff15Row10Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff15Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticSourceCoeff15Row1_zero (h : ℂ) :
    kineticDriftCell h completeKineticSlope 15 1=0 := by
  rw [(completeKineticSourceCoeff15Row1Norm h).property]
  norm_num [completeKineticSourceCoeff15Row1Norm,Nat.rawCast,Int.rawCast]

def reducedKineticFullCoefficient15RealNorm (h v : ℝ) :
    {c : ℝ // reducedKineticCoefficient h v 15=c} := by
  have he := reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) 15
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have hr := congrArg Complex.re he
  change reducedKineticCoefficient h v 15=_ at hr
  simp only [Complex.add_re,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] at hr
  conv at hr =>
    rhs
    rw [(kineticSourceCoeff15Row1RealNorm h).property,(kineticSourceCoeff15Row2RealNorm h).property,(kineticSourceCoeff15Row3RealNorm h).property,(kineticSourceCoeff15Row4RealNorm h).property,(kineticSourceCoeff15Row5RealNorm h).property,(kineticSourceCoeff15Row6RealNorm h).property,(kineticSourceCoeff15Row7RealNorm h).property,(kineticSourceCoeff15Row8RealNorm h).property,(kineticSourceCoeff15Row9RealNorm h).property,(kineticSourceCoeff15Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff15Row1RealNorm,kineticSourceCoeff15Row2RealNorm,kineticSourceCoeff15Row3RealNorm,kineticSourceCoeff15Row4RealNorm,kineticSourceCoeff15Row5RealNorm,kineticSourceCoeff15Row6RealNorm,kineticSourceCoeff15Row7RealNorm,kineticSourceCoeff15Row8RealNorm,kineticSourceCoeff15Row9RealNorm,kineticSourceCoeff15Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,hr⟩

theorem reducedKineticCoefficient15_zero_drift (h : ℝ) :
    reducedKineticCoefficient h 0 15=0 := by
  change ((reducedKineticDriftCoefficient (h:ℂ) 15).eval 0).re=0
  rw [←Polynomial.coeff_zero_eq_eval_zero,reducedKineticDriftCoefficient_coeff]
  change (kineticDriftCell (h:ℂ) completeKineticSlope 15 1).re=0
  rw [kineticSourceCoeff15Row1_zero]
  rfl

end
end HTGeometry.ThetaRatioKineticContraction

