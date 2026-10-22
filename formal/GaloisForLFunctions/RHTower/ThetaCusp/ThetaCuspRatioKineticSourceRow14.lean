import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSourceParts14
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

def completeKineticSourceCoeff14Row1Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 14 1=c} := by
  have he : kineticDriftCell h completeKineticSlope 14 1=kineticDriftCell h completeKineticSlope 14 1 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff14Row1Norm h).property,(kineticSourcePart4Coeff14Row1Norm h).property,(kineticSourcePart6Coeff14Row1Norm h).property,(kineticSourcePart8Coeff14Row1Norm h).property,(kineticSourcePart10Coeff14Row1Norm h).property]
    dsimp only [kineticSourcePart2Coeff14Row1Norm,kineticSourcePart4Coeff14Row1Norm,kineticSourcePart6Coeff14Row1Norm,kineticSourcePart8Coeff14Row1Norm,kineticSourcePart10Coeff14Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff14Row1RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 14 1).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff14Row1Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff14Row1Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff14Row2Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 14 2=c} := by
  have he : kineticDriftCell h completeKineticSlope 14 2=kineticDriftCell h completeKineticSlope 14 2 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff14Row2Norm h).property,(kineticSourcePart4Coeff14Row2Norm h).property,(kineticSourcePart6Coeff14Row2Norm h).property,(kineticSourcePart8Coeff14Row2Norm h).property,(kineticSourcePart10Coeff14Row2Norm h).property]
    dsimp only [kineticSourcePart2Coeff14Row2Norm,kineticSourcePart4Coeff14Row2Norm,kineticSourcePart6Coeff14Row2Norm,kineticSourcePart8Coeff14Row2Norm,kineticSourcePart10Coeff14Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff14Row2RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 14 2).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff14Row2Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff14Row2Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff14Row3Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 14 3=c} := by
  have he : kineticDriftCell h completeKineticSlope 14 3=kineticDriftCell h completeKineticSlope 14 3 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff14Row3Norm h).property,(kineticSourcePart4Coeff14Row3Norm h).property,(kineticSourcePart6Coeff14Row3Norm h).property,(kineticSourcePart8Coeff14Row3Norm h).property,(kineticSourcePart10Coeff14Row3Norm h).property]
    dsimp only [kineticSourcePart2Coeff14Row3Norm,kineticSourcePart4Coeff14Row3Norm,kineticSourcePart6Coeff14Row3Norm,kineticSourcePart8Coeff14Row3Norm,kineticSourcePart10Coeff14Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff14Row3RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 14 3).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff14Row3Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff14Row3Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff14Row4Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 14 4=c} := by
  have he : kineticDriftCell h completeKineticSlope 14 4=kineticDriftCell h completeKineticSlope 14 4 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff14Row4Norm h).property,(kineticSourcePart4Coeff14Row4Norm h).property,(kineticSourcePart6Coeff14Row4Norm h).property,(kineticSourcePart8Coeff14Row4Norm h).property,(kineticSourcePart10Coeff14Row4Norm h).property]
    dsimp only [kineticSourcePart2Coeff14Row4Norm,kineticSourcePart4Coeff14Row4Norm,kineticSourcePart6Coeff14Row4Norm,kineticSourcePart8Coeff14Row4Norm,kineticSourcePart10Coeff14Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff14Row4RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 14 4).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff14Row4Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff14Row4Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff14Row5Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 14 5=c} := by
  have he : kineticDriftCell h completeKineticSlope 14 5=kineticDriftCell h completeKineticSlope 14 5 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff14Row5Norm h).property,(kineticSourcePart4Coeff14Row5Norm h).property,(kineticSourcePart6Coeff14Row5Norm h).property,(kineticSourcePart8Coeff14Row5Norm h).property,(kineticSourcePart10Coeff14Row5Norm h).property]
    dsimp only [kineticSourcePart2Coeff14Row5Norm,kineticSourcePart4Coeff14Row5Norm,kineticSourcePart6Coeff14Row5Norm,kineticSourcePart8Coeff14Row5Norm,kineticSourcePart10Coeff14Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff14Row5RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 14 5).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff14Row5Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff14Row5Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff14Row6Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 14 6=c} := by
  have he : kineticDriftCell h completeKineticSlope 14 6=kineticDriftCell h completeKineticSlope 14 6 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff14Row6Norm h).property,(kineticSourcePart4Coeff14Row6Norm h).property,(kineticSourcePart6Coeff14Row6Norm h).property,(kineticSourcePart8Coeff14Row6Norm h).property,(kineticSourcePart10Coeff14Row6Norm h).property]
    dsimp only [kineticSourcePart2Coeff14Row6Norm,kineticSourcePart4Coeff14Row6Norm,kineticSourcePart6Coeff14Row6Norm,kineticSourcePart8Coeff14Row6Norm,kineticSourcePart10Coeff14Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff14Row6RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 14 6).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff14Row6Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff14Row6Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff14Row7Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 14 7=c} := by
  have he : kineticDriftCell h completeKineticSlope 14 7=kineticDriftCell h completeKineticSlope 14 7 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff14Row7Norm h).property,(kineticSourcePart4Coeff14Row7Norm h).property,(kineticSourcePart6Coeff14Row7Norm h).property,(kineticSourcePart8Coeff14Row7Norm h).property,(kineticSourcePart10Coeff14Row7Norm h).property]
    dsimp only [kineticSourcePart2Coeff14Row7Norm,kineticSourcePart4Coeff14Row7Norm,kineticSourcePart6Coeff14Row7Norm,kineticSourcePart8Coeff14Row7Norm,kineticSourcePart10Coeff14Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff14Row7RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 14 7).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff14Row7Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff14Row7Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff14Row8Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 14 8=c} := by
  have he : kineticDriftCell h completeKineticSlope 14 8=kineticDriftCell h completeKineticSlope 14 8 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff14Row8Norm h).property,(kineticSourcePart4Coeff14Row8Norm h).property,(kineticSourcePart6Coeff14Row8Norm h).property,(kineticSourcePart8Coeff14Row8Norm h).property,(kineticSourcePart10Coeff14Row8Norm h).property]
    dsimp only [kineticSourcePart2Coeff14Row8Norm,kineticSourcePart4Coeff14Row8Norm,kineticSourcePart6Coeff14Row8Norm,kineticSourcePart8Coeff14Row8Norm,kineticSourcePart10Coeff14Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff14Row8RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 14 8).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff14Row8Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff14Row8Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff14Row9Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 14 9=c} := by
  have he : kineticDriftCell h completeKineticSlope 14 9=kineticDriftCell h completeKineticSlope 14 9 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff14Row9Norm h).property,(kineticSourcePart4Coeff14Row9Norm h).property,(kineticSourcePart6Coeff14Row9Norm h).property,(kineticSourcePart8Coeff14Row9Norm h).property,(kineticSourcePart10Coeff14Row9Norm h).property]
    dsimp only [kineticSourcePart2Coeff14Row9Norm,kineticSourcePart4Coeff14Row9Norm,kineticSourcePart6Coeff14Row9Norm,kineticSourcePart8Coeff14Row9Norm,kineticSourcePart10Coeff14Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff14Row9RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 14 9).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff14Row9Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff14Row9Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def completeKineticSourceCoeff14Row10Norm (h : ℂ) : {c : ℂ // kineticDriftCell h completeKineticSlope 14 10=c} := by
  have he : kineticDriftCell h completeKineticSlope 14 10=kineticDriftCell h completeKineticSlope 14 10 := rfl
  conv at he =>
    rhs
    rw [completeKineticSlope_cofactors]
    simp only [kineticDriftCell_add]
    rw [(kineticSourcePart2Coeff14Row10Norm h).property,(kineticSourcePart4Coeff14Row10Norm h).property,(kineticSourcePart6Coeff14Row10Norm h).property,(kineticSourcePart8Coeff14Row10Norm h).property,(kineticSourcePart10Coeff14Row10Norm h).property]
    dsimp only [kineticSourcePart2Coeff14Row10Norm,kineticSourcePart4Coeff14Row10Norm,kineticSourcePart6Coeff14Row10Norm,kineticSourcePart8Coeff14Row10Norm,kineticSourcePart10Coeff14Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,Polynomial.coeff_X]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def kineticSourceCoeff14Row10RealNorm (h : ℝ) :
    {c : ℝ // (kineticDriftCell (h:ℂ) completeKineticSlope 14 10).re=c} := by
  have he := congrArg Complex.re (completeKineticSourceCoeff14Row10Norm (h:ℂ)).property
  conv at he =>
    rhs
    dsimp only [completeKineticSourceCoeff14Row10Norm]
    norm_num [Nat.rawCast,Int.rawCast,←Complex.ofReal_pow,Complex.add_re,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

theorem kineticSourceCoeff14Row1_zero (h : ℂ) :
    kineticDriftCell h completeKineticSlope 14 1=0 := by
  rw [(completeKineticSourceCoeff14Row1Norm h).property]
  norm_num [completeKineticSourceCoeff14Row1Norm,Nat.rawCast,Int.rawCast]

def reducedKineticFullCoefficient14RealNorm (h v : ℝ) :
    {c : ℝ // reducedKineticCoefficient h v 14=c} := by
  have he := reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) 14
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at he
  have hr := congrArg Complex.re he
  change reducedKineticCoefficient h v 14=_ at hr
  simp only [Complex.add_re,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] at hr
  conv at hr =>
    rhs
    rw [(kineticSourceCoeff14Row1RealNorm h).property,(kineticSourceCoeff14Row2RealNorm h).property,(kineticSourceCoeff14Row3RealNorm h).property,(kineticSourceCoeff14Row4RealNorm h).property,(kineticSourceCoeff14Row5RealNorm h).property,(kineticSourceCoeff14Row6RealNorm h).property,(kineticSourceCoeff14Row7RealNorm h).property,(kineticSourceCoeff14Row8RealNorm h).property,(kineticSourceCoeff14Row9RealNorm h).property,(kineticSourceCoeff14Row10RealNorm h).property]
    dsimp only [kineticSourceCoeff14Row1RealNorm,kineticSourceCoeff14Row2RealNorm,kineticSourceCoeff14Row3RealNorm,kineticSourceCoeff14Row4RealNorm,kineticSourceCoeff14Row5RealNorm,kineticSourceCoeff14Row6RealNorm,kineticSourceCoeff14Row7RealNorm,kineticSourceCoeff14Row8RealNorm,kineticSourceCoeff14Row9RealNorm,kineticSourceCoeff14Row10RealNorm]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,hr⟩

theorem reducedKineticCoefficient14_zero_drift (h : ℝ) :
    reducedKineticCoefficient h 0 14=0 := by
  change ((reducedKineticDriftCoefficient (h:ℂ) 14).eval 0).re=0
  rw [←Polynomial.coeff_zero_eq_eval_zero,reducedKineticDriftCoefficient_coeff]
  change (kineticDriftCell (h:ℂ) completeKineticSlope 14 1).re=0
  rw [kineticSourceCoeff14Row1_zero]
  rfl

end
end HTGeometry.ThetaRatioKineticContraction

