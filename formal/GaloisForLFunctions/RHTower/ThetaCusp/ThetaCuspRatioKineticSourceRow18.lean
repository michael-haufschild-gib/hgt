import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceParts18
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def completeKineticSourceCoeff18Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 18 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 18 1=kineticDriftCell h completeKineticSlope 18 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff18Row1Norm h).property,(kineticSourcePart4Coeff18Row1Norm h).property,(kineticSourcePart6Coeff18Row1Norm h).property,(kineticSourcePart8Coeff18Row1Norm h).property,(kineticSourcePart10Coeff18Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff18Row1Norm,kineticSourcePart4Coeff18Row1Norm,kineticSourcePart6Coeff18Row1Norm,kineticSourcePart8Coeff18Row1Norm,kineticSourcePart10Coeff18Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff18Row1RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 18 1).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff18Row1Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff18Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff18Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 18 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 18 2=kineticDriftCell h completeKineticSlope 18 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff18Row2Norm h).property,(kineticSourcePart4Coeff18Row2Norm h).property,(kineticSourcePart6Coeff18Row2Norm h).property,(kineticSourcePart8Coeff18Row2Norm h).property,(kineticSourcePart10Coeff18Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff18Row2Norm,kineticSourcePart4Coeff18Row2Norm,kineticSourcePart6Coeff18Row2Norm,kineticSourcePart8Coeff18Row2Norm,kineticSourcePart10Coeff18Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff18Row2RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 18 2).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff18Row2Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff18Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff18Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 18 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 18 3=kineticDriftCell h completeKineticSlope 18 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff18Row3Norm h).property,(kineticSourcePart4Coeff18Row3Norm h).property,(kineticSourcePart6Coeff18Row3Norm h).property,(kineticSourcePart8Coeff18Row3Norm h).property,(kineticSourcePart10Coeff18Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff18Row3Norm,kineticSourcePart4Coeff18Row3Norm,kineticSourcePart6Coeff18Row3Norm,kineticSourcePart8Coeff18Row3Norm,kineticSourcePart10Coeff18Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff18Row3RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 18 3).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff18Row3Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff18Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff18Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 18 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 18 4=kineticDriftCell h completeKineticSlope 18 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff18Row4Norm h).property,(kineticSourcePart4Coeff18Row4Norm h).property,(kineticSourcePart6Coeff18Row4Norm h).property,(kineticSourcePart8Coeff18Row4Norm h).property,(kineticSourcePart10Coeff18Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff18Row4Norm,kineticSourcePart4Coeff18Row4Norm,kineticSourcePart6Coeff18Row4Norm,kineticSourcePart8Coeff18Row4Norm,kineticSourcePart10Coeff18Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff18Row4RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 18 4).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff18Row4Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff18Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff18Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 18 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 18 5=kineticDriftCell h completeKineticSlope 18 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff18Row5Norm h).property,(kineticSourcePart4Coeff18Row5Norm h).property,(kineticSourcePart6Coeff18Row5Norm h).property,(kineticSourcePart8Coeff18Row5Norm h).property,(kineticSourcePart10Coeff18Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff18Row5Norm,kineticSourcePart4Coeff18Row5Norm,kineticSourcePart6Coeff18Row5Norm,kineticSourcePart8Coeff18Row5Norm,kineticSourcePart10Coeff18Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff18Row5RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 18 5).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff18Row5Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff18Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff18Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 18 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 18 6=kineticDriftCell h completeKineticSlope 18 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff18Row6Norm h).property,(kineticSourcePart4Coeff18Row6Norm h).property,(kineticSourcePart6Coeff18Row6Norm h).property,(kineticSourcePart8Coeff18Row6Norm h).property,(kineticSourcePart10Coeff18Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff18Row6Norm,kineticSourcePart4Coeff18Row6Norm,kineticSourcePart6Coeff18Row6Norm,kineticSourcePart8Coeff18Row6Norm,kineticSourcePart10Coeff18Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff18Row6RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 18 6).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff18Row6Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff18Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff18Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 18 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 18 7=kineticDriftCell h completeKineticSlope 18 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff18Row7Norm h).property,(kineticSourcePart4Coeff18Row7Norm h).property,(kineticSourcePart6Coeff18Row7Norm h).property,(kineticSourcePart8Coeff18Row7Norm h).property,(kineticSourcePart10Coeff18Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff18Row7Norm,kineticSourcePart4Coeff18Row7Norm,kineticSourcePart6Coeff18Row7Norm,kineticSourcePart8Coeff18Row7Norm,kineticSourcePart10Coeff18Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff18Row7RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 18 7).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff18Row7Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff18Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff18Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 18 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 18 8=kineticDriftCell h completeKineticSlope 18 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff18Row8Norm h).property,(kineticSourcePart4Coeff18Row8Norm h).property,(kineticSourcePart6Coeff18Row8Norm h).property,(kineticSourcePart8Coeff18Row8Norm h).property,(kineticSourcePart10Coeff18Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff18Row8Norm,kineticSourcePart4Coeff18Row8Norm,kineticSourcePart6Coeff18Row8Norm,kineticSourcePart8Coeff18Row8Norm,kineticSourcePart10Coeff18Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff18Row8RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 18 8).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff18Row8Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff18Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff18Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 18 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 18 9=kineticDriftCell h completeKineticSlope 18 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff18Row9Norm h).property,(kineticSourcePart4Coeff18Row9Norm h).property,(kineticSourcePart6Coeff18Row9Norm h).property,(kineticSourcePart8Coeff18Row9Norm h).property,(kineticSourcePart10Coeff18Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff18Row9Norm,kineticSourcePart4Coeff18Row9Norm,kineticSourcePart6Coeff18Row9Norm,kineticSourcePart8Coeff18Row9Norm,kineticSourcePart10Coeff18Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff18Row9RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 18 9).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff18Row9Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff18Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff18Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 18 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 18 10=kineticDriftCell h completeKineticSlope 18 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff18Row10Norm h).property,(kineticSourcePart4Coeff18Row10Norm h).property,(kineticSourcePart6Coeff18Row10Norm h).property,(kineticSourcePart8Coeff18Row10Norm h).property,(kineticSourcePart10Coeff18Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff18Row10Norm,kineticSourcePart4Coeff18Row10Norm,kineticSourcePart6Coeff18Row10Norm,kineticSourcePart8Coeff18Row10Norm,kineticSourcePart10Coeff18Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff18Row10RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 18 10).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff18Row10Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff18Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticSourceCoeff18Row1_zero (h : ℂ) :
    kineticDriftCell h completeKineticSlope 18 1=0 := by
  rw [(completeKineticSourceCoeff18Row1Norm h).property]
  norm_num [completeKineticSourceCoeff18Row1Norm,Nat.rawCast,Int.rawCast]

def reducedKineticFullCoefficient18RealNorm (h v : ℝ) :
    {c : ℝ // reducedKineticCoefficient h v 18=c} := by
  have he := reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) 18
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have hr := congrArg Complex.re he
  change reducedKineticCoefficient h v 18=_ at hr
  simp only [Complex.add_re,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] at hr
  conv at hr =>
    rhs
    rw [(kineticSourceCoeff18Row1RealNorm h).property,(kineticSourceCoeff18Row2RealNorm h).property,(kineticSourceCoeff18Row3RealNorm h).property,(kineticSourceCoeff18Row4RealNorm h).property,(kineticSourceCoeff18Row5RealNorm h).property,(kineticSourceCoeff18Row6RealNorm h).property,(kineticSourceCoeff18Row7RealNorm h).property,(kineticSourceCoeff18Row8RealNorm h).property,(kineticSourceCoeff18Row9RealNorm h).property,(kineticSourceCoeff18Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff18Row1RealNorm,kineticSourceCoeff18Row2RealNorm,kineticSourceCoeff18Row3RealNorm,kineticSourceCoeff18Row4RealNorm,kineticSourceCoeff18Row5RealNorm,kineticSourceCoeff18Row6RealNorm,kineticSourceCoeff18Row7RealNorm,kineticSourceCoeff18Row8RealNorm,kineticSourceCoeff18Row9RealNorm,kineticSourceCoeff18Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,hr⟩

theorem reducedKineticCoefficient18_zero_drift (h : ℝ) :
    reducedKineticCoefficient h 0 18=0 := by
  change ((reducedKineticDriftCoefficient (h:ℂ) 18).eval 0).re=0
  rw [←Polynomial.coeff_zero_eq_eval_zero,reducedKineticDriftCoefficient_coeff]
  change (kineticDriftCell (h:ℂ) completeKineticSlope 18 1).re=0
  rw [kineticSourceCoeff18Row1_zero]
  rfl

end
end HTGeometry.ThetaRatioKineticContraction

