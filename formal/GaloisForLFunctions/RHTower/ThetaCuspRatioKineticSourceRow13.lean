import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceParts13
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def completeKineticSourceCoeff13Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 13 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 13 1=kineticDriftCell h completeKineticSlope 13 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff13Row1Norm h).property,(kineticSourcePart4Coeff13Row1Norm h).property,(kineticSourcePart6Coeff13Row1Norm h).property,(kineticSourcePart8Coeff13Row1Norm h).property,(kineticSourcePart10Coeff13Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff13Row1Norm,kineticSourcePart4Coeff13Row1Norm,kineticSourcePart6Coeff13Row1Norm,kineticSourcePart8Coeff13Row1Norm,kineticSourcePart10Coeff13Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff13Row1RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 13 1).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff13Row1Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff13Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff13Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 13 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 13 2=kineticDriftCell h completeKineticSlope 13 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff13Row2Norm h).property,(kineticSourcePart4Coeff13Row2Norm h).property,(kineticSourcePart6Coeff13Row2Norm h).property,(kineticSourcePart8Coeff13Row2Norm h).property,(kineticSourcePart10Coeff13Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff13Row2Norm,kineticSourcePart4Coeff13Row2Norm,kineticSourcePart6Coeff13Row2Norm,kineticSourcePart8Coeff13Row2Norm,kineticSourcePart10Coeff13Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff13Row2RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 13 2).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff13Row2Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff13Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff13Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 13 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 13 3=kineticDriftCell h completeKineticSlope 13 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff13Row3Norm h).property,(kineticSourcePart4Coeff13Row3Norm h).property,(kineticSourcePart6Coeff13Row3Norm h).property,(kineticSourcePart8Coeff13Row3Norm h).property,(kineticSourcePart10Coeff13Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff13Row3Norm,kineticSourcePart4Coeff13Row3Norm,kineticSourcePart6Coeff13Row3Norm,kineticSourcePart8Coeff13Row3Norm,kineticSourcePart10Coeff13Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff13Row3RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 13 3).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff13Row3Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff13Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff13Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 13 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 13 4=kineticDriftCell h completeKineticSlope 13 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff13Row4Norm h).property,(kineticSourcePart4Coeff13Row4Norm h).property,(kineticSourcePart6Coeff13Row4Norm h).property,(kineticSourcePart8Coeff13Row4Norm h).property,(kineticSourcePart10Coeff13Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff13Row4Norm,kineticSourcePart4Coeff13Row4Norm,kineticSourcePart6Coeff13Row4Norm,kineticSourcePart8Coeff13Row4Norm,kineticSourcePart10Coeff13Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff13Row4RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 13 4).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff13Row4Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff13Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff13Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 13 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 13 5=kineticDriftCell h completeKineticSlope 13 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff13Row5Norm h).property,(kineticSourcePart4Coeff13Row5Norm h).property,(kineticSourcePart6Coeff13Row5Norm h).property,(kineticSourcePart8Coeff13Row5Norm h).property,(kineticSourcePart10Coeff13Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff13Row5Norm,kineticSourcePart4Coeff13Row5Norm,kineticSourcePart6Coeff13Row5Norm,kineticSourcePart8Coeff13Row5Norm,kineticSourcePart10Coeff13Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff13Row5RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 13 5).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff13Row5Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff13Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff13Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 13 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 13 6=kineticDriftCell h completeKineticSlope 13 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff13Row6Norm h).property,(kineticSourcePart4Coeff13Row6Norm h).property,(kineticSourcePart6Coeff13Row6Norm h).property,(kineticSourcePart8Coeff13Row6Norm h).property,(kineticSourcePart10Coeff13Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff13Row6Norm,kineticSourcePart4Coeff13Row6Norm,kineticSourcePart6Coeff13Row6Norm,kineticSourcePart8Coeff13Row6Norm,kineticSourcePart10Coeff13Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff13Row6RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 13 6).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff13Row6Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff13Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff13Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 13 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 13 7=kineticDriftCell h completeKineticSlope 13 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff13Row7Norm h).property,(kineticSourcePart4Coeff13Row7Norm h).property,(kineticSourcePart6Coeff13Row7Norm h).property,(kineticSourcePart8Coeff13Row7Norm h).property,(kineticSourcePart10Coeff13Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff13Row7Norm,kineticSourcePart4Coeff13Row7Norm,kineticSourcePart6Coeff13Row7Norm,kineticSourcePart8Coeff13Row7Norm,kineticSourcePart10Coeff13Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff13Row7RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 13 7).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff13Row7Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff13Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff13Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 13 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 13 8=kineticDriftCell h completeKineticSlope 13 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff13Row8Norm h).property,(kineticSourcePart4Coeff13Row8Norm h).property,(kineticSourcePart6Coeff13Row8Norm h).property,(kineticSourcePart8Coeff13Row8Norm h).property,(kineticSourcePart10Coeff13Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff13Row8Norm,kineticSourcePart4Coeff13Row8Norm,kineticSourcePart6Coeff13Row8Norm,kineticSourcePart8Coeff13Row8Norm,kineticSourcePart10Coeff13Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff13Row8RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 13 8).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff13Row8Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff13Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff13Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 13 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 13 9=kineticDriftCell h completeKineticSlope 13 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff13Row9Norm h).property,(kineticSourcePart4Coeff13Row9Norm h).property,(kineticSourcePart6Coeff13Row9Norm h).property,(kineticSourcePart8Coeff13Row9Norm h).property,(kineticSourcePart10Coeff13Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff13Row9Norm,kineticSourcePart4Coeff13Row9Norm,kineticSourcePart6Coeff13Row9Norm,kineticSourcePart8Coeff13Row9Norm,kineticSourcePart10Coeff13Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff13Row9RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 13 9).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff13Row9Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff13Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff13Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 13 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 13 10=kineticDriftCell h completeKineticSlope 13 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff13Row10Norm h).property,(kineticSourcePart4Coeff13Row10Norm h).property,(kineticSourcePart6Coeff13Row10Norm h).property,(kineticSourcePart8Coeff13Row10Norm h).property,(kineticSourcePart10Coeff13Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff13Row10Norm,kineticSourcePart4Coeff13Row10Norm,kineticSourcePart6Coeff13Row10Norm,kineticSourcePart8Coeff13Row10Norm,kineticSourcePart10Coeff13Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff13Row10RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 13 10).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff13Row10Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff13Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticSourceCoeff13Row1_zero (h : ℂ) :
    kineticDriftCell h completeKineticSlope 13 1=0 := by
  rw [(completeKineticSourceCoeff13Row1Norm h).property]
  norm_num [completeKineticSourceCoeff13Row1Norm,Nat.rawCast,Int.rawCast]

def reducedKineticFullCoefficient13RealNorm (h v : ℝ) :
    {c : ℝ // reducedKineticCoefficient h v 13=c} := by
  have he := reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) 13
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have hr := congrArg Complex.re he
  change reducedKineticCoefficient h v 13=_ at hr
  simp only [Complex.add_re,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] at hr
  conv at hr =>
    rhs
    rw [(kineticSourceCoeff13Row1RealNorm h).property,(kineticSourceCoeff13Row2RealNorm h).property,(kineticSourceCoeff13Row3RealNorm h).property,(kineticSourceCoeff13Row4RealNorm h).property,(kineticSourceCoeff13Row5RealNorm h).property,(kineticSourceCoeff13Row6RealNorm h).property,(kineticSourceCoeff13Row7RealNorm h).property,(kineticSourceCoeff13Row8RealNorm h).property,(kineticSourceCoeff13Row9RealNorm h).property,(kineticSourceCoeff13Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff13Row1RealNorm,kineticSourceCoeff13Row2RealNorm,kineticSourceCoeff13Row3RealNorm,kineticSourceCoeff13Row4RealNorm,kineticSourceCoeff13Row5RealNorm,kineticSourceCoeff13Row6RealNorm,kineticSourceCoeff13Row7RealNorm,kineticSourceCoeff13Row8RealNorm,kineticSourceCoeff13Row9RealNorm,kineticSourceCoeff13Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,hr⟩

theorem reducedKineticCoefficient13_zero_drift (h : ℝ) :
    reducedKineticCoefficient h 0 13=0 := by
  change ((reducedKineticDriftCoefficient (h:ℂ) 13).eval 0).re=0
  rw [←Polynomial.coeff_zero_eq_eval_zero,reducedKineticDriftCoefficient_coeff]
  change (kineticDriftCell (h:ℂ) completeKineticSlope 13 1).re=0
  rw [kineticSourceCoeff13Row1_zero]
  rfl

end
end HTGeometry.ThetaRatioKineticContraction

