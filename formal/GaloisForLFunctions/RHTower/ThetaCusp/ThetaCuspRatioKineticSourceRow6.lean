import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceParts6
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def completeKineticSourceCoeff6Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 6 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 6 1=kineticDriftCell h completeKineticSlope 6 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff6Row1Norm h).property,(kineticSourcePart4Coeff6Row1Norm h).property,(kineticSourcePart6Coeff6Row1Norm h).property,(kineticSourcePart8Coeff6Row1Norm h).property,(kineticSourcePart10Coeff6Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff6Row1Norm,kineticSourcePart4Coeff6Row1Norm,kineticSourcePart6Coeff6Row1Norm,kineticSourcePart8Coeff6Row1Norm,kineticSourcePart10Coeff6Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff6Row1RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 6 1).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff6Row1Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff6Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff6Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 6 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 6 2=kineticDriftCell h completeKineticSlope 6 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff6Row2Norm h).property,(kineticSourcePart4Coeff6Row2Norm h).property,(kineticSourcePart6Coeff6Row2Norm h).property,(kineticSourcePart8Coeff6Row2Norm h).property,(kineticSourcePart10Coeff6Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff6Row2Norm,kineticSourcePart4Coeff6Row2Norm,kineticSourcePart6Coeff6Row2Norm,kineticSourcePart8Coeff6Row2Norm,kineticSourcePart10Coeff6Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff6Row2RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 6 2).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff6Row2Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff6Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff6Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 6 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 6 3=kineticDriftCell h completeKineticSlope 6 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff6Row3Norm h).property,(kineticSourcePart4Coeff6Row3Norm h).property,(kineticSourcePart6Coeff6Row3Norm h).property,(kineticSourcePart8Coeff6Row3Norm h).property,(kineticSourcePart10Coeff6Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff6Row3Norm,kineticSourcePart4Coeff6Row3Norm,kineticSourcePart6Coeff6Row3Norm,kineticSourcePart8Coeff6Row3Norm,kineticSourcePart10Coeff6Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff6Row3RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 6 3).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff6Row3Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff6Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff6Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 6 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 6 4=kineticDriftCell h completeKineticSlope 6 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff6Row4Norm h).property,(kineticSourcePart4Coeff6Row4Norm h).property,(kineticSourcePart6Coeff6Row4Norm h).property,(kineticSourcePart8Coeff6Row4Norm h).property,(kineticSourcePart10Coeff6Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff6Row4Norm,kineticSourcePart4Coeff6Row4Norm,kineticSourcePart6Coeff6Row4Norm,kineticSourcePart8Coeff6Row4Norm,kineticSourcePart10Coeff6Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff6Row4RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 6 4).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff6Row4Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff6Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff6Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 6 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 6 5=kineticDriftCell h completeKineticSlope 6 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff6Row5Norm h).property,(kineticSourcePart4Coeff6Row5Norm h).property,(kineticSourcePart6Coeff6Row5Norm h).property,(kineticSourcePart8Coeff6Row5Norm h).property,(kineticSourcePart10Coeff6Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff6Row5Norm,kineticSourcePart4Coeff6Row5Norm,kineticSourcePart6Coeff6Row5Norm,kineticSourcePart8Coeff6Row5Norm,kineticSourcePart10Coeff6Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff6Row5RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 6 5).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff6Row5Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff6Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff6Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 6 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 6 6=kineticDriftCell h completeKineticSlope 6 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff6Row6Norm h).property,(kineticSourcePart4Coeff6Row6Norm h).property,(kineticSourcePart6Coeff6Row6Norm h).property,(kineticSourcePart8Coeff6Row6Norm h).property,(kineticSourcePart10Coeff6Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff6Row6Norm,kineticSourcePart4Coeff6Row6Norm,kineticSourcePart6Coeff6Row6Norm,kineticSourcePart8Coeff6Row6Norm,kineticSourcePart10Coeff6Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff6Row6RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 6 6).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff6Row6Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff6Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff6Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 6 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 6 7=kineticDriftCell h completeKineticSlope 6 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff6Row7Norm h).property,(kineticSourcePart4Coeff6Row7Norm h).property,(kineticSourcePart6Coeff6Row7Norm h).property,(kineticSourcePart8Coeff6Row7Norm h).property,(kineticSourcePart10Coeff6Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff6Row7Norm,kineticSourcePart4Coeff6Row7Norm,kineticSourcePart6Coeff6Row7Norm,kineticSourcePart8Coeff6Row7Norm,kineticSourcePart10Coeff6Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff6Row7RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 6 7).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff6Row7Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff6Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff6Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 6 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 6 8=kineticDriftCell h completeKineticSlope 6 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff6Row8Norm h).property,(kineticSourcePart4Coeff6Row8Norm h).property,(kineticSourcePart6Coeff6Row8Norm h).property,(kineticSourcePart8Coeff6Row8Norm h).property,(kineticSourcePart10Coeff6Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff6Row8Norm,kineticSourcePart4Coeff6Row8Norm,kineticSourcePart6Coeff6Row8Norm,kineticSourcePart8Coeff6Row8Norm,kineticSourcePart10Coeff6Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff6Row8RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 6 8).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff6Row8Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff6Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff6Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 6 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 6 9=kineticDriftCell h completeKineticSlope 6 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff6Row9Norm h).property,(kineticSourcePart4Coeff6Row9Norm h).property,(kineticSourcePart6Coeff6Row9Norm h).property,(kineticSourcePart8Coeff6Row9Norm h).property,(kineticSourcePart10Coeff6Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff6Row9Norm,kineticSourcePart4Coeff6Row9Norm,kineticSourcePart6Coeff6Row9Norm,kineticSourcePart8Coeff6Row9Norm,kineticSourcePart10Coeff6Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff6Row9RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 6 9).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff6Row9Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff6Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff6Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 6 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 6 10=kineticDriftCell h completeKineticSlope 6 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff6Row10Norm h).property,(kineticSourcePart4Coeff6Row10Norm h).property,(kineticSourcePart6Coeff6Row10Norm h).property,(kineticSourcePart8Coeff6Row10Norm h).property,(kineticSourcePart10Coeff6Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff6Row10Norm,kineticSourcePart4Coeff6Row10Norm,kineticSourcePart6Coeff6Row10Norm,kineticSourcePart8Coeff6Row10Norm,kineticSourcePart10Coeff6Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff6Row10RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 6 10).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff6Row10Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff6Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticSourceCoeff6Row1_zero (h : ℂ) :
    kineticDriftCell h completeKineticSlope 6 1=0 := by
  rw [(completeKineticSourceCoeff6Row1Norm h).property]
  norm_num [completeKineticSourceCoeff6Row1Norm,Nat.rawCast,Int.rawCast]

def reducedKineticFullCoefficient6RealNorm (h v : ℝ) :
    {c : ℝ // reducedKineticCoefficient h v 6=c} := by
  have he := reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) 6
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have hr := congrArg Complex.re he
  change reducedKineticCoefficient h v 6=_ at hr
  simp only [Complex.add_re,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] at hr
  conv at hr =>
    rhs
    rw [(kineticSourceCoeff6Row1RealNorm h).property,(kineticSourceCoeff6Row2RealNorm h).property,(kineticSourceCoeff6Row3RealNorm h).property,(kineticSourceCoeff6Row4RealNorm h).property,(kineticSourceCoeff6Row5RealNorm h).property,(kineticSourceCoeff6Row6RealNorm h).property,(kineticSourceCoeff6Row7RealNorm h).property,(kineticSourceCoeff6Row8RealNorm h).property,(kineticSourceCoeff6Row9RealNorm h).property,(kineticSourceCoeff6Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff6Row1RealNorm,kineticSourceCoeff6Row2RealNorm,kineticSourceCoeff6Row3RealNorm,kineticSourceCoeff6Row4RealNorm,kineticSourceCoeff6Row5RealNorm,kineticSourceCoeff6Row6RealNorm,kineticSourceCoeff6Row7RealNorm,kineticSourceCoeff6Row8RealNorm,kineticSourceCoeff6Row9RealNorm,kineticSourceCoeff6Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,hr⟩

theorem reducedKineticCoefficient6_zero_drift (h : ℝ) :
    reducedKineticCoefficient h 0 6=0 := by
  change ((reducedKineticDriftCoefficient (h:ℂ) 6).eval 0).re=0
  rw [←Polynomial.coeff_zero_eq_eval_zero,reducedKineticDriftCoefficient_coeff]
  change (kineticDriftCell (h:ℂ) completeKineticSlope 6 1).re=0
  rw [kineticSourceCoeff6Row1_zero]
  rfl

end
end HTGeometry.ThetaRatioKineticContraction

