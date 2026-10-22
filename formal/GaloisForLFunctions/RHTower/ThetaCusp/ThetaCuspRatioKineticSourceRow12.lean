import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceParts12
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def completeKineticSourceCoeff12Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 12 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 12 1=kineticDriftCell h completeKineticSlope 12 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff12Row1Norm h).property,(kineticSourcePart4Coeff12Row1Norm h).property,(kineticSourcePart6Coeff12Row1Norm h).property,(kineticSourcePart8Coeff12Row1Norm h).property,(kineticSourcePart10Coeff12Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff12Row1Norm,kineticSourcePart4Coeff12Row1Norm,kineticSourcePart6Coeff12Row1Norm,kineticSourcePart8Coeff12Row1Norm,kineticSourcePart10Coeff12Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff12Row1RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 12 1).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff12Row1Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff12Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff12Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 12 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 12 2=kineticDriftCell h completeKineticSlope 12 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff12Row2Norm h).property,(kineticSourcePart4Coeff12Row2Norm h).property,(kineticSourcePart6Coeff12Row2Norm h).property,(kineticSourcePart8Coeff12Row2Norm h).property,(kineticSourcePart10Coeff12Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff12Row2Norm,kineticSourcePart4Coeff12Row2Norm,kineticSourcePart6Coeff12Row2Norm,kineticSourcePart8Coeff12Row2Norm,kineticSourcePart10Coeff12Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff12Row2RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 12 2).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff12Row2Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff12Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff12Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 12 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 12 3=kineticDriftCell h completeKineticSlope 12 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff12Row3Norm h).property,(kineticSourcePart4Coeff12Row3Norm h).property,(kineticSourcePart6Coeff12Row3Norm h).property,(kineticSourcePart8Coeff12Row3Norm h).property,(kineticSourcePart10Coeff12Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff12Row3Norm,kineticSourcePart4Coeff12Row3Norm,kineticSourcePart6Coeff12Row3Norm,kineticSourcePart8Coeff12Row3Norm,kineticSourcePart10Coeff12Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff12Row3RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 12 3).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff12Row3Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff12Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff12Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 12 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 12 4=kineticDriftCell h completeKineticSlope 12 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff12Row4Norm h).property,(kineticSourcePart4Coeff12Row4Norm h).property,(kineticSourcePart6Coeff12Row4Norm h).property,(kineticSourcePart8Coeff12Row4Norm h).property,(kineticSourcePart10Coeff12Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff12Row4Norm,kineticSourcePart4Coeff12Row4Norm,kineticSourcePart6Coeff12Row4Norm,kineticSourcePart8Coeff12Row4Norm,kineticSourcePart10Coeff12Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff12Row4RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 12 4).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff12Row4Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff12Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff12Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 12 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 12 5=kineticDriftCell h completeKineticSlope 12 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff12Row5Norm h).property,(kineticSourcePart4Coeff12Row5Norm h).property,(kineticSourcePart6Coeff12Row5Norm h).property,(kineticSourcePart8Coeff12Row5Norm h).property,(kineticSourcePart10Coeff12Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff12Row5Norm,kineticSourcePart4Coeff12Row5Norm,kineticSourcePart6Coeff12Row5Norm,kineticSourcePart8Coeff12Row5Norm,kineticSourcePart10Coeff12Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff12Row5RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 12 5).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff12Row5Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff12Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff12Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 12 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 12 6=kineticDriftCell h completeKineticSlope 12 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff12Row6Norm h).property,(kineticSourcePart4Coeff12Row6Norm h).property,(kineticSourcePart6Coeff12Row6Norm h).property,(kineticSourcePart8Coeff12Row6Norm h).property,(kineticSourcePart10Coeff12Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff12Row6Norm,kineticSourcePart4Coeff12Row6Norm,kineticSourcePart6Coeff12Row6Norm,kineticSourcePart8Coeff12Row6Norm,kineticSourcePart10Coeff12Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff12Row6RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 12 6).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff12Row6Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff12Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff12Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 12 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 12 7=kineticDriftCell h completeKineticSlope 12 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff12Row7Norm h).property,(kineticSourcePart4Coeff12Row7Norm h).property,(kineticSourcePart6Coeff12Row7Norm h).property,(kineticSourcePart8Coeff12Row7Norm h).property,(kineticSourcePart10Coeff12Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff12Row7Norm,kineticSourcePart4Coeff12Row7Norm,kineticSourcePart6Coeff12Row7Norm,kineticSourcePart8Coeff12Row7Norm,kineticSourcePart10Coeff12Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff12Row7RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 12 7).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff12Row7Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff12Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff12Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 12 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 12 8=kineticDriftCell h completeKineticSlope 12 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff12Row8Norm h).property,(kineticSourcePart4Coeff12Row8Norm h).property,(kineticSourcePart6Coeff12Row8Norm h).property,(kineticSourcePart8Coeff12Row8Norm h).property,(kineticSourcePart10Coeff12Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff12Row8Norm,kineticSourcePart4Coeff12Row8Norm,kineticSourcePart6Coeff12Row8Norm,kineticSourcePart8Coeff12Row8Norm,kineticSourcePart10Coeff12Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff12Row8RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 12 8).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff12Row8Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff12Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff12Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 12 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 12 9=kineticDriftCell h completeKineticSlope 12 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff12Row9Norm h).property,(kineticSourcePart4Coeff12Row9Norm h).property,(kineticSourcePart6Coeff12Row9Norm h).property,(kineticSourcePart8Coeff12Row9Norm h).property,(kineticSourcePart10Coeff12Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff12Row9Norm,kineticSourcePart4Coeff12Row9Norm,kineticSourcePart6Coeff12Row9Norm,kineticSourcePart8Coeff12Row9Norm,kineticSourcePart10Coeff12Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff12Row9RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 12 9).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff12Row9Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff12Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff12Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 12 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 12 10=kineticDriftCell h completeKineticSlope 12 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff12Row10Norm h).property,(kineticSourcePart4Coeff12Row10Norm h).property,(kineticSourcePart6Coeff12Row10Norm h).property,(kineticSourcePart8Coeff12Row10Norm h).property,(kineticSourcePart10Coeff12Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff12Row10Norm,kineticSourcePart4Coeff12Row10Norm,kineticSourcePart6Coeff12Row10Norm,kineticSourcePart8Coeff12Row10Norm,kineticSourcePart10Coeff12Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff12Row10RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 12 10).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff12Row10Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff12Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticSourceCoeff12Row1_zero (h : ℂ) :
    kineticDriftCell h completeKineticSlope 12 1=0 := by
  rw [(completeKineticSourceCoeff12Row1Norm h).property]
  norm_num [completeKineticSourceCoeff12Row1Norm,Nat.rawCast,Int.rawCast]

def reducedKineticFullCoefficient12RealNorm (h v : ℝ) :
    {c : ℝ // reducedKineticCoefficient h v 12=c} := by
  have he := reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) 12
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have hr := congrArg Complex.re he
  change reducedKineticCoefficient h v 12=_ at hr
  simp only [Complex.add_re,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] at hr
  conv at hr =>
    rhs
    rw [(kineticSourceCoeff12Row1RealNorm h).property,(kineticSourceCoeff12Row2RealNorm h).property,(kineticSourceCoeff12Row3RealNorm h).property,(kineticSourceCoeff12Row4RealNorm h).property,(kineticSourceCoeff12Row5RealNorm h).property,(kineticSourceCoeff12Row6RealNorm h).property,(kineticSourceCoeff12Row7RealNorm h).property,(kineticSourceCoeff12Row8RealNorm h).property,(kineticSourceCoeff12Row9RealNorm h).property,(kineticSourceCoeff12Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff12Row1RealNorm,kineticSourceCoeff12Row2RealNorm,kineticSourceCoeff12Row3RealNorm,kineticSourceCoeff12Row4RealNorm,kineticSourceCoeff12Row5RealNorm,kineticSourceCoeff12Row6RealNorm,kineticSourceCoeff12Row7RealNorm,kineticSourceCoeff12Row8RealNorm,kineticSourceCoeff12Row9RealNorm,kineticSourceCoeff12Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,hr⟩

theorem reducedKineticCoefficient12_zero_drift (h : ℝ) :
    reducedKineticCoefficient h 0 12=0 := by
  change ((reducedKineticDriftCoefficient (h:ℂ) 12).eval 0).re=0
  rw [←Polynomial.coeff_zero_eq_eval_zero,reducedKineticDriftCoefficient_coeff]
  change (kineticDriftCell (h:ℂ) completeKineticSlope 12 1).re=0
  rw [kineticSourceCoeff12Row1_zero]
  rfl

end
end HTGeometry.ThetaRatioKineticContraction

