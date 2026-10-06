import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceParts17
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def completeKineticSourceCoeff17Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 17 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 17 1=kineticDriftCell h completeKineticSlope 17 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff17Row1Norm h).property,(kineticSourcePart4Coeff17Row1Norm h).property,(kineticSourcePart6Coeff17Row1Norm h).property,(kineticSourcePart8Coeff17Row1Norm h).property,(kineticSourcePart10Coeff17Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff17Row1Norm,kineticSourcePart4Coeff17Row1Norm,kineticSourcePart6Coeff17Row1Norm,kineticSourcePart8Coeff17Row1Norm,kineticSourcePart10Coeff17Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff17Row1RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 17 1).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff17Row1Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff17Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff17Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 17 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 17 2=kineticDriftCell h completeKineticSlope 17 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff17Row2Norm h).property,(kineticSourcePart4Coeff17Row2Norm h).property,(kineticSourcePart6Coeff17Row2Norm h).property,(kineticSourcePart8Coeff17Row2Norm h).property,(kineticSourcePart10Coeff17Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff17Row2Norm,kineticSourcePart4Coeff17Row2Norm,kineticSourcePart6Coeff17Row2Norm,kineticSourcePart8Coeff17Row2Norm,kineticSourcePart10Coeff17Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff17Row2RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 17 2).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff17Row2Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff17Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff17Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 17 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 17 3=kineticDriftCell h completeKineticSlope 17 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff17Row3Norm h).property,(kineticSourcePart4Coeff17Row3Norm h).property,(kineticSourcePart6Coeff17Row3Norm h).property,(kineticSourcePart8Coeff17Row3Norm h).property,(kineticSourcePart10Coeff17Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff17Row3Norm,kineticSourcePart4Coeff17Row3Norm,kineticSourcePart6Coeff17Row3Norm,kineticSourcePart8Coeff17Row3Norm,kineticSourcePart10Coeff17Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff17Row3RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 17 3).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff17Row3Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff17Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff17Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 17 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 17 4=kineticDriftCell h completeKineticSlope 17 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff17Row4Norm h).property,(kineticSourcePart4Coeff17Row4Norm h).property,(kineticSourcePart6Coeff17Row4Norm h).property,(kineticSourcePart8Coeff17Row4Norm h).property,(kineticSourcePart10Coeff17Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff17Row4Norm,kineticSourcePart4Coeff17Row4Norm,kineticSourcePart6Coeff17Row4Norm,kineticSourcePart8Coeff17Row4Norm,kineticSourcePart10Coeff17Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff17Row4RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 17 4).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff17Row4Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff17Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff17Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 17 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 17 5=kineticDriftCell h completeKineticSlope 17 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff17Row5Norm h).property,(kineticSourcePart4Coeff17Row5Norm h).property,(kineticSourcePart6Coeff17Row5Norm h).property,(kineticSourcePart8Coeff17Row5Norm h).property,(kineticSourcePart10Coeff17Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff17Row5Norm,kineticSourcePart4Coeff17Row5Norm,kineticSourcePart6Coeff17Row5Norm,kineticSourcePart8Coeff17Row5Norm,kineticSourcePart10Coeff17Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff17Row5RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 17 5).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff17Row5Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff17Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff17Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 17 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 17 6=kineticDriftCell h completeKineticSlope 17 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff17Row6Norm h).property,(kineticSourcePart4Coeff17Row6Norm h).property,(kineticSourcePart6Coeff17Row6Norm h).property,(kineticSourcePart8Coeff17Row6Norm h).property,(kineticSourcePart10Coeff17Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff17Row6Norm,kineticSourcePart4Coeff17Row6Norm,kineticSourcePart6Coeff17Row6Norm,kineticSourcePart8Coeff17Row6Norm,kineticSourcePart10Coeff17Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff17Row6RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 17 6).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff17Row6Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff17Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff17Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 17 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 17 7=kineticDriftCell h completeKineticSlope 17 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff17Row7Norm h).property,(kineticSourcePart4Coeff17Row7Norm h).property,(kineticSourcePart6Coeff17Row7Norm h).property,(kineticSourcePart8Coeff17Row7Norm h).property,(kineticSourcePart10Coeff17Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff17Row7Norm,kineticSourcePart4Coeff17Row7Norm,kineticSourcePart6Coeff17Row7Norm,kineticSourcePart8Coeff17Row7Norm,kineticSourcePart10Coeff17Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff17Row7RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 17 7).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff17Row7Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff17Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff17Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 17 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 17 8=kineticDriftCell h completeKineticSlope 17 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff17Row8Norm h).property,(kineticSourcePart4Coeff17Row8Norm h).property,(kineticSourcePart6Coeff17Row8Norm h).property,(kineticSourcePart8Coeff17Row8Norm h).property,(kineticSourcePart10Coeff17Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff17Row8Norm,kineticSourcePart4Coeff17Row8Norm,kineticSourcePart6Coeff17Row8Norm,kineticSourcePart8Coeff17Row8Norm,kineticSourcePart10Coeff17Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff17Row8RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 17 8).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff17Row8Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff17Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff17Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 17 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 17 9=kineticDriftCell h completeKineticSlope 17 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff17Row9Norm h).property,(kineticSourcePart4Coeff17Row9Norm h).property,(kineticSourcePart6Coeff17Row9Norm h).property,(kineticSourcePart8Coeff17Row9Norm h).property,(kineticSourcePart10Coeff17Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff17Row9Norm,kineticSourcePart4Coeff17Row9Norm,kineticSourcePart6Coeff17Row9Norm,kineticSourcePart8Coeff17Row9Norm,kineticSourcePart10Coeff17Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff17Row9RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 17 9).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff17Row9Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff17Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff17Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 17 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 17 10=kineticDriftCell h completeKineticSlope 17 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff17Row10Norm h).property,(kineticSourcePart4Coeff17Row10Norm h).property,(kineticSourcePart6Coeff17Row10Norm h).property,(kineticSourcePart8Coeff17Row10Norm h).property,(kineticSourcePart10Coeff17Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff17Row10Norm,kineticSourcePart4Coeff17Row10Norm,kineticSourcePart6Coeff17Row10Norm,kineticSourcePart8Coeff17Row10Norm,kineticSourcePart10Coeff17Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff17Row10RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 17 10).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff17Row10Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff17Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticSourceCoeff17Row1_zero (h : ℂ) :
    kineticDriftCell h completeKineticSlope 17 1=0 := by
  rw [(completeKineticSourceCoeff17Row1Norm h).property]
  norm_num [completeKineticSourceCoeff17Row1Norm,Nat.rawCast,Int.rawCast]

def reducedKineticFullCoefficient17RealNorm (h v : ℝ) :
    {c : ℝ // reducedKineticCoefficient h v 17=c} := by
  have he := reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) 17
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have hr := congrArg Complex.re he
  change reducedKineticCoefficient h v 17=_ at hr
  simp only [Complex.add_re,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] at hr
  conv at hr =>
    rhs
    rw [(kineticSourceCoeff17Row1RealNorm h).property,(kineticSourceCoeff17Row2RealNorm h).property,(kineticSourceCoeff17Row3RealNorm h).property,(kineticSourceCoeff17Row4RealNorm h).property,(kineticSourceCoeff17Row5RealNorm h).property,(kineticSourceCoeff17Row6RealNorm h).property,(kineticSourceCoeff17Row7RealNorm h).property,(kineticSourceCoeff17Row8RealNorm h).property,(kineticSourceCoeff17Row9RealNorm h).property,(kineticSourceCoeff17Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff17Row1RealNorm,kineticSourceCoeff17Row2RealNorm,kineticSourceCoeff17Row3RealNorm,kineticSourceCoeff17Row4RealNorm,kineticSourceCoeff17Row5RealNorm,kineticSourceCoeff17Row6RealNorm,kineticSourceCoeff17Row7RealNorm,kineticSourceCoeff17Row8RealNorm,kineticSourceCoeff17Row9RealNorm,kineticSourceCoeff17Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,hr⟩

theorem reducedKineticCoefficient17_zero_drift (h : ℝ) :
    reducedKineticCoefficient h 0 17=0 := by
  change ((reducedKineticDriftCoefficient (h:ℂ) 17).eval 0).re=0
  rw [←Polynomial.coeff_zero_eq_eval_zero,reducedKineticDriftCoefficient_coeff]
  change (kineticDriftCell (h:ℂ) completeKineticSlope 17 1).re=0
  rw [kineticSourceCoeff17Row1_zero]
  rfl

end
end HTGeometry.ThetaRatioKineticContraction

