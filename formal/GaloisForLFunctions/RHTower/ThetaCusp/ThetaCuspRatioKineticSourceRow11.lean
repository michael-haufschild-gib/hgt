import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceParts11
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def completeKineticSourceCoeff11Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 11 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 11 1=kineticDriftCell h completeKineticSlope 11 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff11Row1Norm h).property,(kineticSourcePart4Coeff11Row1Norm h).property,(kineticSourcePart6Coeff11Row1Norm h).property,(kineticSourcePart8Coeff11Row1Norm h).property,(kineticSourcePart10Coeff11Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff11Row1Norm,kineticSourcePart4Coeff11Row1Norm,kineticSourcePart6Coeff11Row1Norm,kineticSourcePart8Coeff11Row1Norm,kineticSourcePart10Coeff11Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff11Row1RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 11 1).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff11Row1Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff11Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff11Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 11 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 11 2=kineticDriftCell h completeKineticSlope 11 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff11Row2Norm h).property,(kineticSourcePart4Coeff11Row2Norm h).property,(kineticSourcePart6Coeff11Row2Norm h).property,(kineticSourcePart8Coeff11Row2Norm h).property,(kineticSourcePart10Coeff11Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff11Row2Norm,kineticSourcePart4Coeff11Row2Norm,kineticSourcePart6Coeff11Row2Norm,kineticSourcePart8Coeff11Row2Norm,kineticSourcePart10Coeff11Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff11Row2RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 11 2).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff11Row2Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff11Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff11Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 11 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 11 3=kineticDriftCell h completeKineticSlope 11 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff11Row3Norm h).property,(kineticSourcePart4Coeff11Row3Norm h).property,(kineticSourcePart6Coeff11Row3Norm h).property,(kineticSourcePart8Coeff11Row3Norm h).property,(kineticSourcePart10Coeff11Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff11Row3Norm,kineticSourcePart4Coeff11Row3Norm,kineticSourcePart6Coeff11Row3Norm,kineticSourcePart8Coeff11Row3Norm,kineticSourcePart10Coeff11Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff11Row3RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 11 3).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff11Row3Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff11Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff11Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 11 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 11 4=kineticDriftCell h completeKineticSlope 11 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff11Row4Norm h).property,(kineticSourcePart4Coeff11Row4Norm h).property,(kineticSourcePart6Coeff11Row4Norm h).property,(kineticSourcePart8Coeff11Row4Norm h).property,(kineticSourcePart10Coeff11Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff11Row4Norm,kineticSourcePart4Coeff11Row4Norm,kineticSourcePart6Coeff11Row4Norm,kineticSourcePart8Coeff11Row4Norm,kineticSourcePart10Coeff11Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff11Row4RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 11 4).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff11Row4Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff11Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff11Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 11 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 11 5=kineticDriftCell h completeKineticSlope 11 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff11Row5Norm h).property,(kineticSourcePart4Coeff11Row5Norm h).property,(kineticSourcePart6Coeff11Row5Norm h).property,(kineticSourcePart8Coeff11Row5Norm h).property,(kineticSourcePart10Coeff11Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff11Row5Norm,kineticSourcePart4Coeff11Row5Norm,kineticSourcePart6Coeff11Row5Norm,kineticSourcePart8Coeff11Row5Norm,kineticSourcePart10Coeff11Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff11Row5RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 11 5).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff11Row5Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff11Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff11Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 11 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 11 6=kineticDriftCell h completeKineticSlope 11 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff11Row6Norm h).property,(kineticSourcePart4Coeff11Row6Norm h).property,(kineticSourcePart6Coeff11Row6Norm h).property,(kineticSourcePart8Coeff11Row6Norm h).property,(kineticSourcePart10Coeff11Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff11Row6Norm,kineticSourcePart4Coeff11Row6Norm,kineticSourcePart6Coeff11Row6Norm,kineticSourcePart8Coeff11Row6Norm,kineticSourcePart10Coeff11Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff11Row6RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 11 6).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff11Row6Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff11Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff11Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 11 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 11 7=kineticDriftCell h completeKineticSlope 11 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff11Row7Norm h).property,(kineticSourcePart4Coeff11Row7Norm h).property,(kineticSourcePart6Coeff11Row7Norm h).property,(kineticSourcePart8Coeff11Row7Norm h).property,(kineticSourcePart10Coeff11Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff11Row7Norm,kineticSourcePart4Coeff11Row7Norm,kineticSourcePart6Coeff11Row7Norm,kineticSourcePart8Coeff11Row7Norm,kineticSourcePart10Coeff11Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff11Row7RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 11 7).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff11Row7Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff11Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff11Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 11 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 11 8=kineticDriftCell h completeKineticSlope 11 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff11Row8Norm h).property,(kineticSourcePart4Coeff11Row8Norm h).property,(kineticSourcePart6Coeff11Row8Norm h).property,(kineticSourcePart8Coeff11Row8Norm h).property,(kineticSourcePart10Coeff11Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff11Row8Norm,kineticSourcePart4Coeff11Row8Norm,kineticSourcePart6Coeff11Row8Norm,kineticSourcePart8Coeff11Row8Norm,kineticSourcePart10Coeff11Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff11Row8RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 11 8).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff11Row8Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff11Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff11Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 11 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 11 9=kineticDriftCell h completeKineticSlope 11 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff11Row9Norm h).property,(kineticSourcePart4Coeff11Row9Norm h).property,(kineticSourcePart6Coeff11Row9Norm h).property,(kineticSourcePart8Coeff11Row9Norm h).property,(kineticSourcePart10Coeff11Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff11Row9Norm,kineticSourcePart4Coeff11Row9Norm,kineticSourcePart6Coeff11Row9Norm,kineticSourcePart8Coeff11Row9Norm,kineticSourcePart10Coeff11Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff11Row9RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 11 9).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff11Row9Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff11Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff11Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 11 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 11 10=kineticDriftCell h completeKineticSlope 11 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff11Row10Norm h).property,(kineticSourcePart4Coeff11Row10Norm h).property,(kineticSourcePart6Coeff11Row10Norm h).property,(kineticSourcePart8Coeff11Row10Norm h).property,(kineticSourcePart10Coeff11Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff11Row10Norm,kineticSourcePart4Coeff11Row10Norm,kineticSourcePart6Coeff11Row10Norm,kineticSourcePart8Coeff11Row10Norm,kineticSourcePart10Coeff11Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff11Row10RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 11 10).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff11Row10Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff11Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticSourceCoeff11Row1_zero (h : ℂ) :
    kineticDriftCell h completeKineticSlope 11 1=0 := by
  rw [(completeKineticSourceCoeff11Row1Norm h).property]
  norm_num [completeKineticSourceCoeff11Row1Norm,Nat.rawCast,Int.rawCast]

def reducedKineticFullCoefficient11RealNorm (h v : ℝ) :
    {c : ℝ // reducedKineticCoefficient h v 11=c} := by
  have he := reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) 11
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have hr := congrArg Complex.re he
  change reducedKineticCoefficient h v 11=_ at hr
  simp only [Complex.add_re,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] at hr
  conv at hr =>
    rhs
    rw [(kineticSourceCoeff11Row1RealNorm h).property,(kineticSourceCoeff11Row2RealNorm h).property,(kineticSourceCoeff11Row3RealNorm h).property,(kineticSourceCoeff11Row4RealNorm h).property,(kineticSourceCoeff11Row5RealNorm h).property,(kineticSourceCoeff11Row6RealNorm h).property,(kineticSourceCoeff11Row7RealNorm h).property,(kineticSourceCoeff11Row8RealNorm h).property,(kineticSourceCoeff11Row9RealNorm h).property,(kineticSourceCoeff11Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff11Row1RealNorm,kineticSourceCoeff11Row2RealNorm,kineticSourceCoeff11Row3RealNorm,kineticSourceCoeff11Row4RealNorm,kineticSourceCoeff11Row5RealNorm,kineticSourceCoeff11Row6RealNorm,kineticSourceCoeff11Row7RealNorm,kineticSourceCoeff11Row8RealNorm,kineticSourceCoeff11Row9RealNorm,kineticSourceCoeff11Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,hr⟩

theorem reducedKineticCoefficient11_zero_drift (h : ℝ) :
    reducedKineticCoefficient h 0 11=0 := by
  change ((reducedKineticDriftCoefficient (h:ℂ) 11).eval 0).re=0
  rw [←Polynomial.coeff_zero_eq_eval_zero,reducedKineticDriftCoefficient_coeff]
  change (kineticDriftCell (h:ℂ) completeKineticSlope 11 1).re=0
  rw [kineticSourceCoeff11Row1_zero]
  rfl

end
end HTGeometry.ThetaRatioKineticContraction

