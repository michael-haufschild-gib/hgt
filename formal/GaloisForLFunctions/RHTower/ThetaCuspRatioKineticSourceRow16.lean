import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceParts16
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def completeKineticSourceCoeff16Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 16 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 16 1=kineticDriftCell h completeKineticSlope 16 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff16Row1Norm h).property,(kineticSourcePart4Coeff16Row1Norm h).property,(kineticSourcePart6Coeff16Row1Norm h).property,(kineticSourcePart8Coeff16Row1Norm h).property,(kineticSourcePart10Coeff16Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff16Row1Norm,kineticSourcePart4Coeff16Row1Norm,kineticSourcePart6Coeff16Row1Norm,kineticSourcePart8Coeff16Row1Norm,kineticSourcePart10Coeff16Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff16Row1RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 16 1).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff16Row1Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff16Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff16Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 16 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 16 2=kineticDriftCell h completeKineticSlope 16 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff16Row2Norm h).property,(kineticSourcePart4Coeff16Row2Norm h).property,(kineticSourcePart6Coeff16Row2Norm h).property,(kineticSourcePart8Coeff16Row2Norm h).property,(kineticSourcePart10Coeff16Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff16Row2Norm,kineticSourcePart4Coeff16Row2Norm,kineticSourcePart6Coeff16Row2Norm,kineticSourcePart8Coeff16Row2Norm,kineticSourcePart10Coeff16Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff16Row2RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 16 2).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff16Row2Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff16Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff16Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 16 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 16 3=kineticDriftCell h completeKineticSlope 16 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff16Row3Norm h).property,(kineticSourcePart4Coeff16Row3Norm h).property,(kineticSourcePart6Coeff16Row3Norm h).property,(kineticSourcePart8Coeff16Row3Norm h).property,(kineticSourcePart10Coeff16Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff16Row3Norm,kineticSourcePart4Coeff16Row3Norm,kineticSourcePart6Coeff16Row3Norm,kineticSourcePart8Coeff16Row3Norm,kineticSourcePart10Coeff16Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff16Row3RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 16 3).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff16Row3Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff16Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff16Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 16 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 16 4=kineticDriftCell h completeKineticSlope 16 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff16Row4Norm h).property,(kineticSourcePart4Coeff16Row4Norm h).property,(kineticSourcePart6Coeff16Row4Norm h).property,(kineticSourcePart8Coeff16Row4Norm h).property,(kineticSourcePart10Coeff16Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff16Row4Norm,kineticSourcePart4Coeff16Row4Norm,kineticSourcePart6Coeff16Row4Norm,kineticSourcePart8Coeff16Row4Norm,kineticSourcePart10Coeff16Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff16Row4RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 16 4).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff16Row4Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff16Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff16Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 16 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 16 5=kineticDriftCell h completeKineticSlope 16 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff16Row5Norm h).property,(kineticSourcePart4Coeff16Row5Norm h).property,(kineticSourcePart6Coeff16Row5Norm h).property,(kineticSourcePart8Coeff16Row5Norm h).property,(kineticSourcePart10Coeff16Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff16Row5Norm,kineticSourcePart4Coeff16Row5Norm,kineticSourcePart6Coeff16Row5Norm,kineticSourcePart8Coeff16Row5Norm,kineticSourcePart10Coeff16Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff16Row5RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 16 5).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff16Row5Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff16Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff16Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 16 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 16 6=kineticDriftCell h completeKineticSlope 16 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff16Row6Norm h).property,(kineticSourcePart4Coeff16Row6Norm h).property,(kineticSourcePart6Coeff16Row6Norm h).property,(kineticSourcePart8Coeff16Row6Norm h).property,(kineticSourcePart10Coeff16Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff16Row6Norm,kineticSourcePart4Coeff16Row6Norm,kineticSourcePart6Coeff16Row6Norm,kineticSourcePart8Coeff16Row6Norm,kineticSourcePart10Coeff16Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff16Row6RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 16 6).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff16Row6Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff16Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff16Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 16 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 16 7=kineticDriftCell h completeKineticSlope 16 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff16Row7Norm h).property,(kineticSourcePart4Coeff16Row7Norm h).property,(kineticSourcePart6Coeff16Row7Norm h).property,(kineticSourcePart8Coeff16Row7Norm h).property,(kineticSourcePart10Coeff16Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff16Row7Norm,kineticSourcePart4Coeff16Row7Norm,kineticSourcePart6Coeff16Row7Norm,kineticSourcePart8Coeff16Row7Norm,kineticSourcePart10Coeff16Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff16Row7RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 16 7).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff16Row7Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff16Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff16Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 16 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 16 8=kineticDriftCell h completeKineticSlope 16 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff16Row8Norm h).property,(kineticSourcePart4Coeff16Row8Norm h).property,(kineticSourcePart6Coeff16Row8Norm h).property,(kineticSourcePart8Coeff16Row8Norm h).property,(kineticSourcePart10Coeff16Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff16Row8Norm,kineticSourcePart4Coeff16Row8Norm,kineticSourcePart6Coeff16Row8Norm,kineticSourcePart8Coeff16Row8Norm,kineticSourcePart10Coeff16Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff16Row8RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 16 8).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff16Row8Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff16Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff16Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 16 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 16 9=kineticDriftCell h completeKineticSlope 16 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff16Row9Norm h).property,(kineticSourcePart4Coeff16Row9Norm h).property,(kineticSourcePart6Coeff16Row9Norm h).property,(kineticSourcePart8Coeff16Row9Norm h).property,(kineticSourcePart10Coeff16Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff16Row9Norm,kineticSourcePart4Coeff16Row9Norm,kineticSourcePart6Coeff16Row9Norm,kineticSourcePart8Coeff16Row9Norm,kineticSourcePart10Coeff16Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff16Row9RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 16 9).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff16Row9Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff16Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff16Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 16 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 16 10=kineticDriftCell h completeKineticSlope 16 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff16Row10Norm h).property,(kineticSourcePart4Coeff16Row10Norm h).property,(kineticSourcePart6Coeff16Row10Norm h).property,(kineticSourcePart8Coeff16Row10Norm h).property,(kineticSourcePart10Coeff16Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff16Row10Norm,kineticSourcePart4Coeff16Row10Norm,kineticSourcePart6Coeff16Row10Norm,kineticSourcePart8Coeff16Row10Norm,kineticSourcePart10Coeff16Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff16Row10RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 16 10).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff16Row10Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff16Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticSourceCoeff16Row1_zero (h : ℂ) :
    kineticDriftCell h completeKineticSlope 16 1=0 := by
  rw [(completeKineticSourceCoeff16Row1Norm h).property]
  norm_num [completeKineticSourceCoeff16Row1Norm,Nat.rawCast,Int.rawCast]

def reducedKineticFullCoefficient16RealNorm (h v : ℝ) :
    {c : ℝ // reducedKineticCoefficient h v 16=c} := by
  have he := reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) 16
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have hr := congrArg Complex.re he
  change reducedKineticCoefficient h v 16=_ at hr
  simp only [Complex.add_re,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] at hr
  conv at hr =>
    rhs
    rw [(kineticSourceCoeff16Row1RealNorm h).property,(kineticSourceCoeff16Row2RealNorm h).property,(kineticSourceCoeff16Row3RealNorm h).property,(kineticSourceCoeff16Row4RealNorm h).property,(kineticSourceCoeff16Row5RealNorm h).property,(kineticSourceCoeff16Row6RealNorm h).property,(kineticSourceCoeff16Row7RealNorm h).property,(kineticSourceCoeff16Row8RealNorm h).property,(kineticSourceCoeff16Row9RealNorm h).property,(kineticSourceCoeff16Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff16Row1RealNorm,kineticSourceCoeff16Row2RealNorm,kineticSourceCoeff16Row3RealNorm,kineticSourceCoeff16Row4RealNorm,kineticSourceCoeff16Row5RealNorm,kineticSourceCoeff16Row6RealNorm,kineticSourceCoeff16Row7RealNorm,kineticSourceCoeff16Row8RealNorm,kineticSourceCoeff16Row9RealNorm,kineticSourceCoeff16Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,hr⟩

theorem reducedKineticCoefficient16_zero_drift (h : ℝ) :
    reducedKineticCoefficient h 0 16=0 := by
  change ((reducedKineticDriftCoefficient (h:ℂ) 16).eval 0).re=0
  rw [←Polynomial.coeff_zero_eq_eval_zero,reducedKineticDriftCoefficient_coeff]
  change (kineticDriftCell (h:ℂ) completeKineticSlope 16 1).re=0
  rw [kineticSourceCoeff16Row1_zero]
  rfl

end
end HTGeometry.ThetaRatioKineticContraction

