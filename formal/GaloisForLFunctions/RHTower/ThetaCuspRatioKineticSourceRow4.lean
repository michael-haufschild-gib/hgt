import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSourceParts4
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def completeKineticSourceCoeff4Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 4 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 4 1=kineticDriftCell h completeKineticSlope 4 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff4Row1Norm h).property,(kineticSourcePart4Coeff4Row1Norm h).property,(kineticSourcePart6Coeff4Row1Norm h).property,(kineticSourcePart8Coeff4Row1Norm h).property,(kineticSourcePart10Coeff4Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff4Row1Norm,kineticSourcePart4Coeff4Row1Norm,kineticSourcePart6Coeff4Row1Norm,kineticSourcePart8Coeff4Row1Norm,kineticSourcePart10Coeff4Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff4Row1RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 4 1).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff4Row1Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff4Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff4Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 4 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 4 2=kineticDriftCell h completeKineticSlope 4 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff4Row2Norm h).property,(kineticSourcePart4Coeff4Row2Norm h).property,(kineticSourcePart6Coeff4Row2Norm h).property,(kineticSourcePart8Coeff4Row2Norm h).property,(kineticSourcePart10Coeff4Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff4Row2Norm,kineticSourcePart4Coeff4Row2Norm,kineticSourcePart6Coeff4Row2Norm,kineticSourcePart8Coeff4Row2Norm,kineticSourcePart10Coeff4Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff4Row2RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 4 2).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff4Row2Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff4Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff4Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 4 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 4 3=kineticDriftCell h completeKineticSlope 4 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff4Row3Norm h).property,(kineticSourcePart4Coeff4Row3Norm h).property,(kineticSourcePart6Coeff4Row3Norm h).property,(kineticSourcePart8Coeff4Row3Norm h).property,(kineticSourcePart10Coeff4Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff4Row3Norm,kineticSourcePart4Coeff4Row3Norm,kineticSourcePart6Coeff4Row3Norm,kineticSourcePart8Coeff4Row3Norm,kineticSourcePart10Coeff4Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff4Row3RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 4 3).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff4Row3Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff4Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff4Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 4 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 4 4=kineticDriftCell h completeKineticSlope 4 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff4Row4Norm h).property,(kineticSourcePart4Coeff4Row4Norm h).property,(kineticSourcePart6Coeff4Row4Norm h).property,(kineticSourcePart8Coeff4Row4Norm h).property,(kineticSourcePart10Coeff4Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff4Row4Norm,kineticSourcePart4Coeff4Row4Norm,kineticSourcePart6Coeff4Row4Norm,kineticSourcePart8Coeff4Row4Norm,kineticSourcePart10Coeff4Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff4Row4RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 4 4).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff4Row4Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff4Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff4Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 4 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 4 5=kineticDriftCell h completeKineticSlope 4 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff4Row5Norm h).property,(kineticSourcePart4Coeff4Row5Norm h).property,(kineticSourcePart6Coeff4Row5Norm h).property,(kineticSourcePart8Coeff4Row5Norm h).property,(kineticSourcePart10Coeff4Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff4Row5Norm,kineticSourcePart4Coeff4Row5Norm,kineticSourcePart6Coeff4Row5Norm,kineticSourcePart8Coeff4Row5Norm,kineticSourcePart10Coeff4Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff4Row5RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 4 5).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff4Row5Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff4Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff4Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 4 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 4 6=kineticDriftCell h completeKineticSlope 4 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff4Row6Norm h).property,(kineticSourcePart4Coeff4Row6Norm h).property,(kineticSourcePart6Coeff4Row6Norm h).property,(kineticSourcePart8Coeff4Row6Norm h).property,(kineticSourcePart10Coeff4Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff4Row6Norm,kineticSourcePart4Coeff4Row6Norm,kineticSourcePart6Coeff4Row6Norm,kineticSourcePart8Coeff4Row6Norm,kineticSourcePart10Coeff4Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff4Row6RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 4 6).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff4Row6Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff4Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff4Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 4 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 4 7=kineticDriftCell h completeKineticSlope 4 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff4Row7Norm h).property,(kineticSourcePart4Coeff4Row7Norm h).property,(kineticSourcePart6Coeff4Row7Norm h).property,(kineticSourcePart8Coeff4Row7Norm h).property,(kineticSourcePart10Coeff4Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff4Row7Norm,kineticSourcePart4Coeff4Row7Norm,kineticSourcePart6Coeff4Row7Norm,kineticSourcePart8Coeff4Row7Norm,kineticSourcePart10Coeff4Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff4Row7RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 4 7).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff4Row7Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff4Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff4Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 4 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 4 8=kineticDriftCell h completeKineticSlope 4 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff4Row8Norm h).property,(kineticSourcePart4Coeff4Row8Norm h).property,(kineticSourcePart6Coeff4Row8Norm h).property,(kineticSourcePart8Coeff4Row8Norm h).property,(kineticSourcePart10Coeff4Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff4Row8Norm,kineticSourcePart4Coeff4Row8Norm,kineticSourcePart6Coeff4Row8Norm,kineticSourcePart8Coeff4Row8Norm,kineticSourcePart10Coeff4Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff4Row8RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 4 8).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff4Row8Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff4Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff4Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 4 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 4 9=kineticDriftCell h completeKineticSlope 4 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff4Row9Norm h).property,(kineticSourcePart4Coeff4Row9Norm h).property,(kineticSourcePart6Coeff4Row9Norm h).property,(kineticSourcePart8Coeff4Row9Norm h).property,(kineticSourcePart10Coeff4Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff4Row9Norm,kineticSourcePart4Coeff4Row9Norm,kineticSourcePart6Coeff4Row9Norm,kineticSourcePart8Coeff4Row9Norm,kineticSourcePart10Coeff4Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff4Row9RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 4 9).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff4Row9Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff4Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff4Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 4 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 4 10=kineticDriftCell h completeKineticSlope 4 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff4Row10Norm h).property,(kineticSourcePart4Coeff4Row10Norm h).property,(kineticSourcePart6Coeff4Row10Norm h).property,(kineticSourcePart8Coeff4Row10Norm h).property,(kineticSourcePart10Coeff4Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff4Row10Norm,kineticSourcePart4Coeff4Row10Norm,kineticSourcePart6Coeff4Row10Norm,kineticSourcePart8Coeff4Row10Norm,kineticSourcePart10Coeff4Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff4Row10RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 4 10).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff4Row10Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff4Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticSourceCoeff4Row1_zero (h : ℂ) :
    kineticDriftCell h completeKineticSlope 4 1=0 := by
  rw [(completeKineticSourceCoeff4Row1Norm h).property]
  norm_num [completeKineticSourceCoeff4Row1Norm,Nat.rawCast,Int.rawCast]

def reducedKineticFullCoefficient4RealNorm (h v : ℝ) :
    {c : ℝ // reducedKineticCoefficient h v 4=c} := by
  have he := reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) 4
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have hr := congrArg Complex.re he
  change reducedKineticCoefficient h v 4=_ at hr
  simp only [Complex.add_re,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] at hr
  conv at hr =>
    rhs
    rw [(kineticSourceCoeff4Row1RealNorm h).property,(kineticSourceCoeff4Row2RealNorm h).property,(kineticSourceCoeff4Row3RealNorm h).property,(kineticSourceCoeff4Row4RealNorm h).property,(kineticSourceCoeff4Row5RealNorm h).property,(kineticSourceCoeff4Row6RealNorm h).property,(kineticSourceCoeff4Row7RealNorm h).property,(kineticSourceCoeff4Row8RealNorm h).property,(kineticSourceCoeff4Row9RealNorm h).property,(kineticSourceCoeff4Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff4Row1RealNorm,kineticSourceCoeff4Row2RealNorm,kineticSourceCoeff4Row3RealNorm,kineticSourceCoeff4Row4RealNorm,kineticSourceCoeff4Row5RealNorm,kineticSourceCoeff4Row6RealNorm,kineticSourceCoeff4Row7RealNorm,kineticSourceCoeff4Row8RealNorm,kineticSourceCoeff4Row9RealNorm,kineticSourceCoeff4Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,hr⟩

theorem reducedKineticCoefficient4_zero_drift (h : ℝ) :
    reducedKineticCoefficient h 0 4=0 := by
  change ((reducedKineticDriftCoefficient (h:ℂ) 4).eval 0).re=0
  rw [←Polynomial.coeff_zero_eq_eval_zero,reducedKineticDriftCoefficient_coeff]
  change (kineticDriftCell (h:ℂ) completeKineticSlope 4 1).re=0
  rw [kineticSourceCoeff4Row1_zero]
  rfl

end
end HTGeometry.ThetaRatioKineticContraction

