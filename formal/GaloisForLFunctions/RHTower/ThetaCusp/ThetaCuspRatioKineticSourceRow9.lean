import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceParts9
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def completeKineticSourceCoeff9Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 9 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 9 1=kineticDriftCell h completeKineticSlope 9 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff9Row1Norm h).property,(kineticSourcePart4Coeff9Row1Norm h).property,(kineticSourcePart6Coeff9Row1Norm h).property,(kineticSourcePart8Coeff9Row1Norm h).property,(kineticSourcePart10Coeff9Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff9Row1Norm,kineticSourcePart4Coeff9Row1Norm,kineticSourcePart6Coeff9Row1Norm,kineticSourcePart8Coeff9Row1Norm,kineticSourcePart10Coeff9Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff9Row1RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 9 1).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff9Row1Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff9Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff9Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 9 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 9 2=kineticDriftCell h completeKineticSlope 9 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff9Row2Norm h).property,(kineticSourcePart4Coeff9Row2Norm h).property,(kineticSourcePart6Coeff9Row2Norm h).property,(kineticSourcePart8Coeff9Row2Norm h).property,(kineticSourcePart10Coeff9Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff9Row2Norm,kineticSourcePart4Coeff9Row2Norm,kineticSourcePart6Coeff9Row2Norm,kineticSourcePart8Coeff9Row2Norm,kineticSourcePart10Coeff9Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff9Row2RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 9 2).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff9Row2Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff9Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff9Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 9 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 9 3=kineticDriftCell h completeKineticSlope 9 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff9Row3Norm h).property,(kineticSourcePart4Coeff9Row3Norm h).property,(kineticSourcePart6Coeff9Row3Norm h).property,(kineticSourcePart8Coeff9Row3Norm h).property,(kineticSourcePart10Coeff9Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff9Row3Norm,kineticSourcePart4Coeff9Row3Norm,kineticSourcePart6Coeff9Row3Norm,kineticSourcePart8Coeff9Row3Norm,kineticSourcePart10Coeff9Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff9Row3RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 9 3).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff9Row3Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff9Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff9Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 9 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 9 4=kineticDriftCell h completeKineticSlope 9 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff9Row4Norm h).property,(kineticSourcePart4Coeff9Row4Norm h).property,(kineticSourcePart6Coeff9Row4Norm h).property,(kineticSourcePart8Coeff9Row4Norm h).property,(kineticSourcePart10Coeff9Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff9Row4Norm,kineticSourcePart4Coeff9Row4Norm,kineticSourcePart6Coeff9Row4Norm,kineticSourcePart8Coeff9Row4Norm,kineticSourcePart10Coeff9Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff9Row4RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 9 4).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff9Row4Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff9Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff9Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 9 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 9 5=kineticDriftCell h completeKineticSlope 9 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff9Row5Norm h).property,(kineticSourcePart4Coeff9Row5Norm h).property,(kineticSourcePart6Coeff9Row5Norm h).property,(kineticSourcePart8Coeff9Row5Norm h).property,(kineticSourcePart10Coeff9Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff9Row5Norm,kineticSourcePart4Coeff9Row5Norm,kineticSourcePart6Coeff9Row5Norm,kineticSourcePart8Coeff9Row5Norm,kineticSourcePart10Coeff9Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff9Row5RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 9 5).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff9Row5Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff9Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff9Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 9 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 9 6=kineticDriftCell h completeKineticSlope 9 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff9Row6Norm h).property,(kineticSourcePart4Coeff9Row6Norm h).property,(kineticSourcePart6Coeff9Row6Norm h).property,(kineticSourcePart8Coeff9Row6Norm h).property,(kineticSourcePart10Coeff9Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff9Row6Norm,kineticSourcePart4Coeff9Row6Norm,kineticSourcePart6Coeff9Row6Norm,kineticSourcePart8Coeff9Row6Norm,kineticSourcePart10Coeff9Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff9Row6RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 9 6).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff9Row6Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff9Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff9Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 9 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 9 7=kineticDriftCell h completeKineticSlope 9 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff9Row7Norm h).property,(kineticSourcePart4Coeff9Row7Norm h).property,(kineticSourcePart6Coeff9Row7Norm h).property,(kineticSourcePart8Coeff9Row7Norm h).property,(kineticSourcePart10Coeff9Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff9Row7Norm,kineticSourcePart4Coeff9Row7Norm,kineticSourcePart6Coeff9Row7Norm,kineticSourcePart8Coeff9Row7Norm,kineticSourcePart10Coeff9Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff9Row7RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 9 7).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff9Row7Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff9Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff9Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 9 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 9 8=kineticDriftCell h completeKineticSlope 9 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff9Row8Norm h).property,(kineticSourcePart4Coeff9Row8Norm h).property,(kineticSourcePart6Coeff9Row8Norm h).property,(kineticSourcePart8Coeff9Row8Norm h).property,(kineticSourcePart10Coeff9Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff9Row8Norm,kineticSourcePart4Coeff9Row8Norm,kineticSourcePart6Coeff9Row8Norm,kineticSourcePart8Coeff9Row8Norm,kineticSourcePart10Coeff9Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff9Row8RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 9 8).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff9Row8Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff9Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff9Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 9 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 9 9=kineticDriftCell h completeKineticSlope 9 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff9Row9Norm h).property,(kineticSourcePart4Coeff9Row9Norm h).property,(kineticSourcePart6Coeff9Row9Norm h).property,(kineticSourcePart8Coeff9Row9Norm h).property,(kineticSourcePart10Coeff9Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff9Row9Norm,kineticSourcePart4Coeff9Row9Norm,kineticSourcePart6Coeff9Row9Norm,kineticSourcePart8Coeff9Row9Norm,kineticSourcePart10Coeff9Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff9Row9RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 9 9).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff9Row9Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff9Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff9Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 9 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 9 10=kineticDriftCell h completeKineticSlope 9 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff9Row10Norm h).property,(kineticSourcePart4Coeff9Row10Norm h).property,(kineticSourcePart6Coeff9Row10Norm h).property,(kineticSourcePart8Coeff9Row10Norm h).property,(kineticSourcePart10Coeff9Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff9Row10Norm,kineticSourcePart4Coeff9Row10Norm,kineticSourcePart6Coeff9Row10Norm,kineticSourcePart8Coeff9Row10Norm,kineticSourcePart10Coeff9Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff9Row10RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 9 10).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff9Row10Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff9Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticSourceCoeff9Row1_zero (h : ℂ) :
    kineticDriftCell h completeKineticSlope 9 1=0 := by
  rw [(completeKineticSourceCoeff9Row1Norm h).property]
  norm_num [completeKineticSourceCoeff9Row1Norm,Nat.rawCast,Int.rawCast]

def reducedKineticFullCoefficient9RealNorm (h v : ℝ) :
    {c : ℝ // reducedKineticCoefficient h v 9=c} := by
  have he := reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) 9
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have hr := congrArg Complex.re he
  change reducedKineticCoefficient h v 9=_ at hr
  simp only [Complex.add_re,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] at hr
  conv at hr =>
    rhs
    rw [(kineticSourceCoeff9Row1RealNorm h).property,(kineticSourceCoeff9Row2RealNorm h).property,(kineticSourceCoeff9Row3RealNorm h).property,(kineticSourceCoeff9Row4RealNorm h).property,(kineticSourceCoeff9Row5RealNorm h).property,(kineticSourceCoeff9Row6RealNorm h).property,(kineticSourceCoeff9Row7RealNorm h).property,(kineticSourceCoeff9Row8RealNorm h).property,(kineticSourceCoeff9Row9RealNorm h).property,(kineticSourceCoeff9Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff9Row1RealNorm,kineticSourceCoeff9Row2RealNorm,kineticSourceCoeff9Row3RealNorm,kineticSourceCoeff9Row4RealNorm,kineticSourceCoeff9Row5RealNorm,kineticSourceCoeff9Row6RealNorm,kineticSourceCoeff9Row7RealNorm,kineticSourceCoeff9Row8RealNorm,kineticSourceCoeff9Row9RealNorm,kineticSourceCoeff9Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,hr⟩

theorem reducedKineticCoefficient9_zero_drift (h : ℝ) :
    reducedKineticCoefficient h 0 9=0 := by
  change ((reducedKineticDriftCoefficient (h:ℂ) 9).eval 0).re=0
  rw [←Polynomial.coeff_zero_eq_eval_zero,reducedKineticDriftCoefficient_coeff]
  change (kineticDriftCell (h:ℂ) completeKineticSlope 9 1).re=0
  rw [kineticSourceCoeff9Row1_zero]
  rfl

end
end HTGeometry.ThetaRatioKineticContraction

