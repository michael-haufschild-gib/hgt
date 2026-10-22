import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceParts7
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def completeKineticSourceCoeff7Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 7 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 7 1=kineticDriftCell h completeKineticSlope 7 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff7Row1Norm h).property,(kineticSourcePart4Coeff7Row1Norm h).property,(kineticSourcePart6Coeff7Row1Norm h).property,(kineticSourcePart8Coeff7Row1Norm h).property,(kineticSourcePart10Coeff7Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff7Row1Norm,kineticSourcePart4Coeff7Row1Norm,kineticSourcePart6Coeff7Row1Norm,kineticSourcePart8Coeff7Row1Norm,kineticSourcePart10Coeff7Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff7Row1RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 7 1).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff7Row1Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff7Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff7Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 7 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 7 2=kineticDriftCell h completeKineticSlope 7 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff7Row2Norm h).property,(kineticSourcePart4Coeff7Row2Norm h).property,(kineticSourcePart6Coeff7Row2Norm h).property,(kineticSourcePart8Coeff7Row2Norm h).property,(kineticSourcePart10Coeff7Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff7Row2Norm,kineticSourcePart4Coeff7Row2Norm,kineticSourcePart6Coeff7Row2Norm,kineticSourcePart8Coeff7Row2Norm,kineticSourcePart10Coeff7Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff7Row2RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 7 2).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff7Row2Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff7Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff7Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 7 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 7 3=kineticDriftCell h completeKineticSlope 7 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff7Row3Norm h).property,(kineticSourcePart4Coeff7Row3Norm h).property,(kineticSourcePart6Coeff7Row3Norm h).property,(kineticSourcePart8Coeff7Row3Norm h).property,(kineticSourcePart10Coeff7Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff7Row3Norm,kineticSourcePart4Coeff7Row3Norm,kineticSourcePart6Coeff7Row3Norm,kineticSourcePart8Coeff7Row3Norm,kineticSourcePart10Coeff7Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff7Row3RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 7 3).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff7Row3Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff7Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff7Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 7 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 7 4=kineticDriftCell h completeKineticSlope 7 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff7Row4Norm h).property,(kineticSourcePart4Coeff7Row4Norm h).property,(kineticSourcePart6Coeff7Row4Norm h).property,(kineticSourcePart8Coeff7Row4Norm h).property,(kineticSourcePart10Coeff7Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff7Row4Norm,kineticSourcePart4Coeff7Row4Norm,kineticSourcePart6Coeff7Row4Norm,kineticSourcePart8Coeff7Row4Norm,kineticSourcePart10Coeff7Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff7Row4RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 7 4).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff7Row4Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff7Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff7Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 7 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 7 5=kineticDriftCell h completeKineticSlope 7 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff7Row5Norm h).property,(kineticSourcePart4Coeff7Row5Norm h).property,(kineticSourcePart6Coeff7Row5Norm h).property,(kineticSourcePart8Coeff7Row5Norm h).property,(kineticSourcePart10Coeff7Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff7Row5Norm,kineticSourcePart4Coeff7Row5Norm,kineticSourcePart6Coeff7Row5Norm,kineticSourcePart8Coeff7Row5Norm,kineticSourcePart10Coeff7Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff7Row5RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 7 5).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff7Row5Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff7Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff7Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 7 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 7 6=kineticDriftCell h completeKineticSlope 7 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff7Row6Norm h).property,(kineticSourcePart4Coeff7Row6Norm h).property,(kineticSourcePart6Coeff7Row6Norm h).property,(kineticSourcePart8Coeff7Row6Norm h).property,(kineticSourcePart10Coeff7Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff7Row6Norm,kineticSourcePart4Coeff7Row6Norm,kineticSourcePart6Coeff7Row6Norm,kineticSourcePart8Coeff7Row6Norm,kineticSourcePart10Coeff7Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff7Row6RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 7 6).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff7Row6Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff7Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff7Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 7 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 7 7=kineticDriftCell h completeKineticSlope 7 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff7Row7Norm h).property,(kineticSourcePart4Coeff7Row7Norm h).property,(kineticSourcePart6Coeff7Row7Norm h).property,(kineticSourcePart8Coeff7Row7Norm h).property,(kineticSourcePart10Coeff7Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff7Row7Norm,kineticSourcePart4Coeff7Row7Norm,kineticSourcePart6Coeff7Row7Norm,kineticSourcePart8Coeff7Row7Norm,kineticSourcePart10Coeff7Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff7Row7RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 7 7).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff7Row7Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff7Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff7Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 7 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 7 8=kineticDriftCell h completeKineticSlope 7 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff7Row8Norm h).property,(kineticSourcePart4Coeff7Row8Norm h).property,(kineticSourcePart6Coeff7Row8Norm h).property,(kineticSourcePart8Coeff7Row8Norm h).property,(kineticSourcePart10Coeff7Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff7Row8Norm,kineticSourcePart4Coeff7Row8Norm,kineticSourcePart6Coeff7Row8Norm,kineticSourcePart8Coeff7Row8Norm,kineticSourcePart10Coeff7Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff7Row8RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 7 8).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff7Row8Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff7Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff7Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 7 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 7 9=kineticDriftCell h completeKineticSlope 7 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff7Row9Norm h).property,(kineticSourcePart4Coeff7Row9Norm h).property,(kineticSourcePart6Coeff7Row9Norm h).property,(kineticSourcePart8Coeff7Row9Norm h).property,(kineticSourcePart10Coeff7Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff7Row9Norm,kineticSourcePart4Coeff7Row9Norm,kineticSourcePart6Coeff7Row9Norm,kineticSourcePart8Coeff7Row9Norm,kineticSourcePart10Coeff7Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff7Row9RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 7 9).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff7Row9Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff7Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff7Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 7 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 7 10=kineticDriftCell h completeKineticSlope 7 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff7Row10Norm h).property,(kineticSourcePart4Coeff7Row10Norm h).property,(kineticSourcePart6Coeff7Row10Norm h).property,(kineticSourcePart8Coeff7Row10Norm h).property,(kineticSourcePart10Coeff7Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff7Row10Norm,kineticSourcePart4Coeff7Row10Norm,kineticSourcePart6Coeff7Row10Norm,kineticSourcePart8Coeff7Row10Norm,kineticSourcePart10Coeff7Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff7Row10RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 7 10).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff7Row10Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff7Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticSourceCoeff7Row1_zero (h : ℂ) :
    kineticDriftCell h completeKineticSlope 7 1=0 := by
  rw [(completeKineticSourceCoeff7Row1Norm h).property]
  norm_num [completeKineticSourceCoeff7Row1Norm,Nat.rawCast,Int.rawCast]

def reducedKineticFullCoefficient7RealNorm (h v : ℝ) :
    {c : ℝ // reducedKineticCoefficient h v 7=c} := by
  have he := reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) 7
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have hr := congrArg Complex.re he
  change reducedKineticCoefficient h v 7=_ at hr
  simp only [Complex.add_re,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] at hr
  conv at hr =>
    rhs
    rw [(kineticSourceCoeff7Row1RealNorm h).property,(kineticSourceCoeff7Row2RealNorm h).property,(kineticSourceCoeff7Row3RealNorm h).property,(kineticSourceCoeff7Row4RealNorm h).property,(kineticSourceCoeff7Row5RealNorm h).property,(kineticSourceCoeff7Row6RealNorm h).property,(kineticSourceCoeff7Row7RealNorm h).property,(kineticSourceCoeff7Row8RealNorm h).property,(kineticSourceCoeff7Row9RealNorm h).property,(kineticSourceCoeff7Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff7Row1RealNorm,kineticSourceCoeff7Row2RealNorm,kineticSourceCoeff7Row3RealNorm,kineticSourceCoeff7Row4RealNorm,kineticSourceCoeff7Row5RealNorm,kineticSourceCoeff7Row6RealNorm,kineticSourceCoeff7Row7RealNorm,kineticSourceCoeff7Row8RealNorm,kineticSourceCoeff7Row9RealNorm,kineticSourceCoeff7Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,hr⟩

theorem reducedKineticCoefficient7_zero_drift (h : ℝ) :
    reducedKineticCoefficient h 0 7=0 := by
  change ((reducedKineticDriftCoefficient (h:ℂ) 7).eval 0).re=0
  rw [←Polynomial.coeff_zero_eq_eval_zero,reducedKineticDriftCoefficient_coeff]
  change (kineticDriftCell (h:ℂ) completeKineticSlope 7 1).re=0
  rw [kineticSourceCoeff7Row1_zero]
  rfl

end
end HTGeometry.ThetaRatioKineticContraction

