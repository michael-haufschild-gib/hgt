import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceParts5
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def completeKineticSourceCoeff5Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 5 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 5 1=kineticDriftCell h completeKineticSlope 5 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff5Row1Norm h).property,(kineticSourcePart4Coeff5Row1Norm h).property,(kineticSourcePart6Coeff5Row1Norm h).property,(kineticSourcePart8Coeff5Row1Norm h).property,(kineticSourcePart10Coeff5Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff5Row1Norm,kineticSourcePart4Coeff5Row1Norm,kineticSourcePart6Coeff5Row1Norm,kineticSourcePart8Coeff5Row1Norm,kineticSourcePart10Coeff5Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff5Row1RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 5 1).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff5Row1Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff5Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff5Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 5 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 5 2=kineticDriftCell h completeKineticSlope 5 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff5Row2Norm h).property,(kineticSourcePart4Coeff5Row2Norm h).property,(kineticSourcePart6Coeff5Row2Norm h).property,(kineticSourcePart8Coeff5Row2Norm h).property,(kineticSourcePart10Coeff5Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff5Row2Norm,kineticSourcePart4Coeff5Row2Norm,kineticSourcePart6Coeff5Row2Norm,kineticSourcePart8Coeff5Row2Norm,kineticSourcePart10Coeff5Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff5Row2RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 5 2).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff5Row2Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff5Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff5Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 5 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 5 3=kineticDriftCell h completeKineticSlope 5 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff5Row3Norm h).property,(kineticSourcePart4Coeff5Row3Norm h).property,(kineticSourcePart6Coeff5Row3Norm h).property,(kineticSourcePart8Coeff5Row3Norm h).property,(kineticSourcePart10Coeff5Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff5Row3Norm,kineticSourcePart4Coeff5Row3Norm,kineticSourcePart6Coeff5Row3Norm,kineticSourcePart8Coeff5Row3Norm,kineticSourcePart10Coeff5Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff5Row3RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 5 3).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff5Row3Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff5Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff5Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 5 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 5 4=kineticDriftCell h completeKineticSlope 5 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff5Row4Norm h).property,(kineticSourcePart4Coeff5Row4Norm h).property,(kineticSourcePart6Coeff5Row4Norm h).property,(kineticSourcePart8Coeff5Row4Norm h).property,(kineticSourcePart10Coeff5Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff5Row4Norm,kineticSourcePart4Coeff5Row4Norm,kineticSourcePart6Coeff5Row4Norm,kineticSourcePart8Coeff5Row4Norm,kineticSourcePart10Coeff5Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff5Row4RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 5 4).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff5Row4Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff5Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff5Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 5 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 5 5=kineticDriftCell h completeKineticSlope 5 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff5Row5Norm h).property,(kineticSourcePart4Coeff5Row5Norm h).property,(kineticSourcePart6Coeff5Row5Norm h).property,(kineticSourcePart8Coeff5Row5Norm h).property,(kineticSourcePart10Coeff5Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff5Row5Norm,kineticSourcePart4Coeff5Row5Norm,kineticSourcePart6Coeff5Row5Norm,kineticSourcePart8Coeff5Row5Norm,kineticSourcePart10Coeff5Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff5Row5RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 5 5).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff5Row5Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff5Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff5Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 5 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 5 6=kineticDriftCell h completeKineticSlope 5 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff5Row6Norm h).property,(kineticSourcePart4Coeff5Row6Norm h).property,(kineticSourcePart6Coeff5Row6Norm h).property,(kineticSourcePart8Coeff5Row6Norm h).property,(kineticSourcePart10Coeff5Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff5Row6Norm,kineticSourcePart4Coeff5Row6Norm,kineticSourcePart6Coeff5Row6Norm,kineticSourcePart8Coeff5Row6Norm,kineticSourcePart10Coeff5Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff5Row6RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 5 6).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff5Row6Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff5Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff5Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 5 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 5 7=kineticDriftCell h completeKineticSlope 5 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff5Row7Norm h).property,(kineticSourcePart4Coeff5Row7Norm h).property,(kineticSourcePart6Coeff5Row7Norm h).property,(kineticSourcePart8Coeff5Row7Norm h).property,(kineticSourcePart10Coeff5Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff5Row7Norm,kineticSourcePart4Coeff5Row7Norm,kineticSourcePart6Coeff5Row7Norm,kineticSourcePart8Coeff5Row7Norm,kineticSourcePart10Coeff5Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff5Row7RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 5 7).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff5Row7Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff5Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff5Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 5 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 5 8=kineticDriftCell h completeKineticSlope 5 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff5Row8Norm h).property,(kineticSourcePart4Coeff5Row8Norm h).property,(kineticSourcePart6Coeff5Row8Norm h).property,(kineticSourcePart8Coeff5Row8Norm h).property,(kineticSourcePart10Coeff5Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff5Row8Norm,kineticSourcePart4Coeff5Row8Norm,kineticSourcePart6Coeff5Row8Norm,kineticSourcePart8Coeff5Row8Norm,kineticSourcePart10Coeff5Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff5Row8RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 5 8).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff5Row8Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff5Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff5Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 5 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 5 9=kineticDriftCell h completeKineticSlope 5 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff5Row9Norm h).property,(kineticSourcePart4Coeff5Row9Norm h).property,(kineticSourcePart6Coeff5Row9Norm h).property,(kineticSourcePart8Coeff5Row9Norm h).property,(kineticSourcePart10Coeff5Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff5Row9Norm,kineticSourcePart4Coeff5Row9Norm,kineticSourcePart6Coeff5Row9Norm,kineticSourcePart8Coeff5Row9Norm,kineticSourcePart10Coeff5Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff5Row9RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 5 9).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff5Row9Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff5Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff5Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 5 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 5 10=kineticDriftCell h completeKineticSlope 5 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff5Row10Norm h).property,(kineticSourcePart4Coeff5Row10Norm h).property,(kineticSourcePart6Coeff5Row10Norm h).property,(kineticSourcePart8Coeff5Row10Norm h).property,(kineticSourcePart10Coeff5Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff5Row10Norm,kineticSourcePart4Coeff5Row10Norm,kineticSourcePart6Coeff5Row10Norm,kineticSourcePart8Coeff5Row10Norm,kineticSourcePart10Coeff5Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff5Row10RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 5 10).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff5Row10Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff5Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticSourceCoeff5Row1_zero (h : ℂ) :
    kineticDriftCell h completeKineticSlope 5 1=0 := by
  rw [(completeKineticSourceCoeff5Row1Norm h).property]
  norm_num [completeKineticSourceCoeff5Row1Norm,Nat.rawCast,Int.rawCast]

def reducedKineticFullCoefficient5RealNorm (h v : ℝ) :
    {c : ℝ // reducedKineticCoefficient h v 5=c} := by
  have he := reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) 5
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have hr := congrArg Complex.re he
  change reducedKineticCoefficient h v 5=_ at hr
  simp only [Complex.add_re,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] at hr
  conv at hr =>
    rhs
    rw [(kineticSourceCoeff5Row1RealNorm h).property,(kineticSourceCoeff5Row2RealNorm h).property,(kineticSourceCoeff5Row3RealNorm h).property,(kineticSourceCoeff5Row4RealNorm h).property,(kineticSourceCoeff5Row5RealNorm h).property,(kineticSourceCoeff5Row6RealNorm h).property,(kineticSourceCoeff5Row7RealNorm h).property,(kineticSourceCoeff5Row8RealNorm h).property,(kineticSourceCoeff5Row9RealNorm h).property,(kineticSourceCoeff5Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff5Row1RealNorm,kineticSourceCoeff5Row2RealNorm,kineticSourceCoeff5Row3RealNorm,kineticSourceCoeff5Row4RealNorm,kineticSourceCoeff5Row5RealNorm,kineticSourceCoeff5Row6RealNorm,kineticSourceCoeff5Row7RealNorm,kineticSourceCoeff5Row8RealNorm,kineticSourceCoeff5Row9RealNorm,kineticSourceCoeff5Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,hr⟩

theorem reducedKineticCoefficient5_zero_drift (h : ℝ) :
    reducedKineticCoefficient h 0 5=0 := by
  change ((reducedKineticDriftCoefficient (h:ℂ) 5).eval 0).re=0
  rw [←Polynomial.coeff_zero_eq_eval_zero,reducedKineticDriftCoefficient_coeff]
  change (kineticDriftCell (h:ℂ) completeKineticSlope 5 1).re=0
  rw [kineticSourceCoeff5Row1_zero]
  rfl

end
end HTGeometry.ThetaRatioKineticContraction

