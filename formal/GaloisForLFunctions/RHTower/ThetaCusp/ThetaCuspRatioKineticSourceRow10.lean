import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceParts10
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def completeKineticSourceCoeff10Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 10 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 10 1=kineticDriftCell h completeKineticSlope 10 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff10Row1Norm h).property,(kineticSourcePart4Coeff10Row1Norm h).property,(kineticSourcePart6Coeff10Row1Norm h).property,(kineticSourcePart8Coeff10Row1Norm h).property,(kineticSourcePart10Coeff10Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff10Row1Norm,kineticSourcePart4Coeff10Row1Norm,kineticSourcePart6Coeff10Row1Norm,kineticSourcePart8Coeff10Row1Norm,kineticSourcePart10Coeff10Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff10Row1RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 10 1).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff10Row1Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff10Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff10Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 10 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 10 2=kineticDriftCell h completeKineticSlope 10 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff10Row2Norm h).property,(kineticSourcePart4Coeff10Row2Norm h).property,(kineticSourcePart6Coeff10Row2Norm h).property,(kineticSourcePart8Coeff10Row2Norm h).property,(kineticSourcePart10Coeff10Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff10Row2Norm,kineticSourcePart4Coeff10Row2Norm,kineticSourcePart6Coeff10Row2Norm,kineticSourcePart8Coeff10Row2Norm,kineticSourcePart10Coeff10Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff10Row2RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 10 2).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff10Row2Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff10Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff10Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 10 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 10 3=kineticDriftCell h completeKineticSlope 10 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff10Row3Norm h).property,(kineticSourcePart4Coeff10Row3Norm h).property,(kineticSourcePart6Coeff10Row3Norm h).property,(kineticSourcePart8Coeff10Row3Norm h).property,(kineticSourcePart10Coeff10Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff10Row3Norm,kineticSourcePart4Coeff10Row3Norm,kineticSourcePart6Coeff10Row3Norm,kineticSourcePart8Coeff10Row3Norm,kineticSourcePart10Coeff10Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff10Row3RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 10 3).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff10Row3Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff10Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff10Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 10 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 10 4=kineticDriftCell h completeKineticSlope 10 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff10Row4Norm h).property,(kineticSourcePart4Coeff10Row4Norm h).property,(kineticSourcePart6Coeff10Row4Norm h).property,(kineticSourcePart8Coeff10Row4Norm h).property,(kineticSourcePart10Coeff10Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff10Row4Norm,kineticSourcePart4Coeff10Row4Norm,kineticSourcePart6Coeff10Row4Norm,kineticSourcePart8Coeff10Row4Norm,kineticSourcePart10Coeff10Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff10Row4RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 10 4).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff10Row4Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff10Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff10Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 10 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 10 5=kineticDriftCell h completeKineticSlope 10 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff10Row5Norm h).property,(kineticSourcePart4Coeff10Row5Norm h).property,(kineticSourcePart6Coeff10Row5Norm h).property,(kineticSourcePart8Coeff10Row5Norm h).property,(kineticSourcePart10Coeff10Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff10Row5Norm,kineticSourcePart4Coeff10Row5Norm,kineticSourcePart6Coeff10Row5Norm,kineticSourcePart8Coeff10Row5Norm,kineticSourcePart10Coeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff10Row5RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 10 5).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff10Row5Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff10Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff10Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 10 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 10 6=kineticDriftCell h completeKineticSlope 10 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff10Row6Norm h).property,(kineticSourcePart4Coeff10Row6Norm h).property,(kineticSourcePart6Coeff10Row6Norm h).property,(kineticSourcePart8Coeff10Row6Norm h).property,(kineticSourcePart10Coeff10Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff10Row6Norm,kineticSourcePart4Coeff10Row6Norm,kineticSourcePart6Coeff10Row6Norm,kineticSourcePart8Coeff10Row6Norm,kineticSourcePart10Coeff10Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff10Row6RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 10 6).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff10Row6Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff10Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff10Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 10 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 10 7=kineticDriftCell h completeKineticSlope 10 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff10Row7Norm h).property,(kineticSourcePart4Coeff10Row7Norm h).property,(kineticSourcePart6Coeff10Row7Norm h).property,(kineticSourcePart8Coeff10Row7Norm h).property,(kineticSourcePart10Coeff10Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff10Row7Norm,kineticSourcePart4Coeff10Row7Norm,kineticSourcePart6Coeff10Row7Norm,kineticSourcePart8Coeff10Row7Norm,kineticSourcePart10Coeff10Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff10Row7RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 10 7).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff10Row7Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff10Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff10Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 10 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 10 8=kineticDriftCell h completeKineticSlope 10 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff10Row8Norm h).property,(kineticSourcePart4Coeff10Row8Norm h).property,(kineticSourcePart6Coeff10Row8Norm h).property,(kineticSourcePart8Coeff10Row8Norm h).property,(kineticSourcePart10Coeff10Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff10Row8Norm,kineticSourcePart4Coeff10Row8Norm,kineticSourcePart6Coeff10Row8Norm,kineticSourcePart8Coeff10Row8Norm,kineticSourcePart10Coeff10Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff10Row8RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 10 8).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff10Row8Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff10Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff10Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 10 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 10 9=kineticDriftCell h completeKineticSlope 10 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff10Row9Norm h).property,(kineticSourcePart4Coeff10Row9Norm h).property,(kineticSourcePart6Coeff10Row9Norm h).property,(kineticSourcePart8Coeff10Row9Norm h).property,(kineticSourcePart10Coeff10Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff10Row9Norm,kineticSourcePart4Coeff10Row9Norm,kineticSourcePart6Coeff10Row9Norm,kineticSourcePart8Coeff10Row9Norm,kineticSourcePart10Coeff10Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff10Row9RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 10 9).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff10Row9Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff10Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff10Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 10 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 10 10=kineticDriftCell h completeKineticSlope 10 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff10Row10Norm h).property,(kineticSourcePart4Coeff10Row10Norm h).property,(kineticSourcePart6Coeff10Row10Norm h).property,(kineticSourcePart8Coeff10Row10Norm h).property,(kineticSourcePart10Coeff10Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff10Row10Norm,kineticSourcePart4Coeff10Row10Norm,kineticSourcePart6Coeff10Row10Norm,kineticSourcePart8Coeff10Row10Norm,kineticSourcePart10Coeff10Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff10Row10RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 10 10).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff10Row10Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff10Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticSourceCoeff10Row1_zero (h : ℂ) :
    kineticDriftCell h completeKineticSlope 10 1=0 := by
  rw [(completeKineticSourceCoeff10Row1Norm h).property]
  norm_num [completeKineticSourceCoeff10Row1Norm,Nat.rawCast,Int.rawCast]

def reducedKineticFullCoefficient10RealNorm (h v : ℝ) :
    {c : ℝ // reducedKineticCoefficient h v 10=c} := by
  have he := reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) 10
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have hr := congrArg Complex.re he
  change reducedKineticCoefficient h v 10=_ at hr
  simp only [Complex.add_re,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] at hr
  conv at hr =>
    rhs
    rw [(kineticSourceCoeff10Row1RealNorm h).property,(kineticSourceCoeff10Row2RealNorm h).property,(kineticSourceCoeff10Row3RealNorm h).property,(kineticSourceCoeff10Row4RealNorm h).property,(kineticSourceCoeff10Row5RealNorm h).property,(kineticSourceCoeff10Row6RealNorm h).property,(kineticSourceCoeff10Row7RealNorm h).property,(kineticSourceCoeff10Row8RealNorm h).property,(kineticSourceCoeff10Row9RealNorm h).property,(kineticSourceCoeff10Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff10Row1RealNorm,kineticSourceCoeff10Row2RealNorm,kineticSourceCoeff10Row3RealNorm,kineticSourceCoeff10Row4RealNorm,kineticSourceCoeff10Row5RealNorm,kineticSourceCoeff10Row6RealNorm,kineticSourceCoeff10Row7RealNorm,kineticSourceCoeff10Row8RealNorm,kineticSourceCoeff10Row9RealNorm,kineticSourceCoeff10Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,hr⟩

theorem reducedKineticCoefficient10_zero_drift (h : ℝ) :
    reducedKineticCoefficient h 0 10=0 := by
  change ((reducedKineticDriftCoefficient (h:ℂ) 10).eval 0).re=0
  rw [←Polynomial.coeff_zero_eq_eval_zero,reducedKineticDriftCoefficient_coeff]
  change (kineticDriftCell (h:ℂ) completeKineticSlope 10 1).re=0
  rw [kineticSourceCoeff10Row1_zero]
  rfl

end
end HTGeometry.ThetaRatioKineticContraction

