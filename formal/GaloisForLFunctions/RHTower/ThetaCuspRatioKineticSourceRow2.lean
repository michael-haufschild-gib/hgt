import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceParts2
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def completeKineticSourceCoeff2Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 2 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 2 1=kineticDriftCell h completeKineticSlope 2 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff2Row1Norm h).property,(kineticSourcePart4Coeff2Row1Norm h).property,(kineticSourcePart6Coeff2Row1Norm h).property,(kineticSourcePart8Coeff2Row1Norm h).property,(kineticSourcePart10Coeff2Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff2Row1Norm,kineticSourcePart4Coeff2Row1Norm,kineticSourcePart6Coeff2Row1Norm,kineticSourcePart8Coeff2Row1Norm,kineticSourcePart10Coeff2Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff2Row1RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 2 1).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff2Row1Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff2Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff2Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 2 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 2 2=kineticDriftCell h completeKineticSlope 2 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff2Row2Norm h).property,(kineticSourcePart4Coeff2Row2Norm h).property,(kineticSourcePart6Coeff2Row2Norm h).property,(kineticSourcePart8Coeff2Row2Norm h).property,(kineticSourcePart10Coeff2Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff2Row2Norm,kineticSourcePart4Coeff2Row2Norm,kineticSourcePart6Coeff2Row2Norm,kineticSourcePart8Coeff2Row2Norm,kineticSourcePart10Coeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff2Row2RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 2 2).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff2Row2Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff2Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff2Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 2 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 2 3=kineticDriftCell h completeKineticSlope 2 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff2Row3Norm h).property,(kineticSourcePart4Coeff2Row3Norm h).property,(kineticSourcePart6Coeff2Row3Norm h).property,(kineticSourcePart8Coeff2Row3Norm h).property,(kineticSourcePart10Coeff2Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff2Row3Norm,kineticSourcePart4Coeff2Row3Norm,kineticSourcePart6Coeff2Row3Norm,kineticSourcePart8Coeff2Row3Norm,kineticSourcePart10Coeff2Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff2Row3RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 2 3).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff2Row3Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff2Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff2Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 2 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 2 4=kineticDriftCell h completeKineticSlope 2 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff2Row4Norm h).property,(kineticSourcePart4Coeff2Row4Norm h).property,(kineticSourcePart6Coeff2Row4Norm h).property,(kineticSourcePart8Coeff2Row4Norm h).property,(kineticSourcePart10Coeff2Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff2Row4Norm,kineticSourcePart4Coeff2Row4Norm,kineticSourcePart6Coeff2Row4Norm,kineticSourcePart8Coeff2Row4Norm,kineticSourcePart10Coeff2Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff2Row4RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 2 4).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff2Row4Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff2Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff2Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 2 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 2 5=kineticDriftCell h completeKineticSlope 2 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff2Row5Norm h).property,(kineticSourcePart4Coeff2Row5Norm h).property,(kineticSourcePart6Coeff2Row5Norm h).property,(kineticSourcePart8Coeff2Row5Norm h).property,(kineticSourcePart10Coeff2Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff2Row5Norm,kineticSourcePart4Coeff2Row5Norm,kineticSourcePart6Coeff2Row5Norm,kineticSourcePart8Coeff2Row5Norm,kineticSourcePart10Coeff2Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff2Row5RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 2 5).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff2Row5Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff2Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff2Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 2 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 2 6=kineticDriftCell h completeKineticSlope 2 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff2Row6Norm h).property,(kineticSourcePart4Coeff2Row6Norm h).property,(kineticSourcePart6Coeff2Row6Norm h).property,(kineticSourcePart8Coeff2Row6Norm h).property,(kineticSourcePart10Coeff2Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff2Row6Norm,kineticSourcePart4Coeff2Row6Norm,kineticSourcePart6Coeff2Row6Norm,kineticSourcePart8Coeff2Row6Norm,kineticSourcePart10Coeff2Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff2Row6RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 2 6).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff2Row6Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff2Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff2Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 2 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 2 7=kineticDriftCell h completeKineticSlope 2 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff2Row7Norm h).property,(kineticSourcePart4Coeff2Row7Norm h).property,(kineticSourcePart6Coeff2Row7Norm h).property,(kineticSourcePart8Coeff2Row7Norm h).property,(kineticSourcePart10Coeff2Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff2Row7Norm,kineticSourcePart4Coeff2Row7Norm,kineticSourcePart6Coeff2Row7Norm,kineticSourcePart8Coeff2Row7Norm,kineticSourcePart10Coeff2Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff2Row7RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 2 7).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff2Row7Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff2Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff2Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 2 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 2 8=kineticDriftCell h completeKineticSlope 2 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff2Row8Norm h).property,(kineticSourcePart4Coeff2Row8Norm h).property,(kineticSourcePart6Coeff2Row8Norm h).property,(kineticSourcePart8Coeff2Row8Norm h).property,(kineticSourcePart10Coeff2Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff2Row8Norm,kineticSourcePart4Coeff2Row8Norm,kineticSourcePart6Coeff2Row8Norm,kineticSourcePart8Coeff2Row8Norm,kineticSourcePart10Coeff2Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff2Row8RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 2 8).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff2Row8Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff2Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff2Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 2 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 2 9=kineticDriftCell h completeKineticSlope 2 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff2Row9Norm h).property,(kineticSourcePart4Coeff2Row9Norm h).property,(kineticSourcePart6Coeff2Row9Norm h).property,(kineticSourcePart8Coeff2Row9Norm h).property,(kineticSourcePart10Coeff2Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff2Row9Norm,kineticSourcePart4Coeff2Row9Norm,kineticSourcePart6Coeff2Row9Norm,kineticSourcePart8Coeff2Row9Norm,kineticSourcePart10Coeff2Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff2Row9RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 2 9).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff2Row9Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff2Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff2Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 2 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 2 10=kineticDriftCell h completeKineticSlope 2 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff2Row10Norm h).property,(kineticSourcePart4Coeff2Row10Norm h).property,(kineticSourcePart6Coeff2Row10Norm h).property,(kineticSourcePart8Coeff2Row10Norm h).property,(kineticSourcePart10Coeff2Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff2Row10Norm,kineticSourcePart4Coeff2Row10Norm,kineticSourcePart6Coeff2Row10Norm,kineticSourcePart8Coeff2Row10Norm,kineticSourcePart10Coeff2Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff2Row10RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 2 10).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff2Row10Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff2Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticSourceCoeff2Row1_zero (h : ℂ) :
    kineticDriftCell h completeKineticSlope 2 1=0 := by
  rw [(completeKineticSourceCoeff2Row1Norm h).property]
  norm_num [completeKineticSourceCoeff2Row1Norm,Nat.rawCast,Int.rawCast]

def reducedKineticFullCoefficient2RealNorm (h v : ℝ) :
    {c : ℝ // reducedKineticCoefficient h v 2=c} := by
  have he := reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) 2
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have hr := congrArg Complex.re he
  change reducedKineticCoefficient h v 2=_ at hr
  simp only [Complex.add_re,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] at hr
  conv at hr =>
    rhs
    rw [(kineticSourceCoeff2Row1RealNorm h).property,(kineticSourceCoeff2Row2RealNorm h).property,(kineticSourceCoeff2Row3RealNorm h).property,(kineticSourceCoeff2Row4RealNorm h).property,(kineticSourceCoeff2Row5RealNorm h).property,(kineticSourceCoeff2Row6RealNorm h).property,(kineticSourceCoeff2Row7RealNorm h).property,(kineticSourceCoeff2Row8RealNorm h).property,(kineticSourceCoeff2Row9RealNorm h).property,(kineticSourceCoeff2Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff2Row1RealNorm,kineticSourceCoeff2Row2RealNorm,kineticSourceCoeff2Row3RealNorm,kineticSourceCoeff2Row4RealNorm,kineticSourceCoeff2Row5RealNorm,kineticSourceCoeff2Row6RealNorm,kineticSourceCoeff2Row7RealNorm,kineticSourceCoeff2Row8RealNorm,kineticSourceCoeff2Row9RealNorm,kineticSourceCoeff2Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,hr⟩

theorem reducedKineticCoefficient2_zero_drift (h : ℝ) :
    reducedKineticCoefficient h 0 2=0 := by
  change ((reducedKineticDriftCoefficient (h:ℂ) 2).eval 0).re=0
  rw [←Polynomial.coeff_zero_eq_eval_zero,reducedKineticDriftCoefficient_coeff]
  change (kineticDriftCell (h:ℂ) completeKineticSlope 2 1).re=0
  rw [kineticSourceCoeff2Row1_zero]
  rfl

end
end HTGeometry.ThetaRatioKineticContraction
