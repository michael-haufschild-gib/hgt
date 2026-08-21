/-
# Chen--Gupta--Li Class-I weight factorization

Separates each exact shifted-tail coefficient into common oscillatory
Möbius-character data and real `n^{-Re rho} exp(-n/Y)` weight. This bridges
the heterogeneous witness to finite Abel summation.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiClassIAbelDeweighting

open Complex

noncomputable section

namespace RHTower

def cglShiftedTailDyadicOscillatoryTerm (X N q : ℕ)
    (χ : DirichletCharacter ℂ (q + 1)) (s : CGLRightHalfPlanePoint) (j : Fin N) : ℂ :=
  (zeroDetectionMobiusCoefficient X (cglCharacterDyadicIndex N j) : ℂ) *
    χ (cglCharacterDyadicIndex N j) *
      cglCharacterDyadicPhase N (-s.1.im) j

def cglShiftedTailDyadicRealWeight (N : ℕ)
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) (j : Fin N) : ℝ :=
  (cglCharacterDyadicIndex N j : ℝ) ^ (-s.1.re) *
    Real.exp (-((cglCharacterDyadicIndex N j : ℝ) * x.1))

theorem cglShiftedTailDyadicCoefficient_factor
    (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) (j : Fin N) :
    (cglShiftedTailDyadicCoefficients X N s x) j *
      χ (cglCharacterDyadicIndex N j) * cglCharacterDyadicPhase N (-s.1.im) j =
      cglShiftedTailDyadicOscillatoryTerm X N q χ s j *
        (cglShiftedTailDyadicRealWeight N s x j : ℂ) := by
  have hpos : 0 < (cglCharacterDyadicIndex N j : ℝ) := by
    unfold cglCharacterDyadicIndex
    positivity
  have hnonneg : 0 ≤ (cglCharacterDyadicIndex N j : ℝ) := hpos.le
  simp only [cglShiftedTailDyadicCoefficients]
  unfold cglShiftedTailDyadicOscillatoryTerm cglShiftedTailDyadicRealWeight
  push_cast
  have hpow : (cglCharacterDyadicIndex N j : ℂ) ^ (-((s.1.re : ℝ) : ℂ)) =
      (((cglCharacterDyadicIndex N j : ℝ) ^ (-s.1.re) : ℝ) : ℂ) := by
    rw [← show ((-s.1.re : ℝ) : ℂ) = -((s.1.re : ℝ) : ℂ) by norm_cast]
    exact (Complex.ofReal_cpow hnonneg (-s.1.re)).symm
  rw [hpow]
  ring

theorem cglShiftedTailDyadicScaledPolynomial_factor
    (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    cglShiftedTailDyadicScaledPolynomial X N q χ s x =
      (cglShiftedTailDyadicCoefficientScale X N s x : ℂ) *
        ∑ j : Fin N, cglShiftedTailDyadicOscillatoryTerm X N q χ s j *
          (cglShiftedTailDyadicRealWeight N s x j : ℂ) := by
  rw [cglShiftedTailDyadicScaledPolynomial_eq_scale_mul]
  congr 1
  unfold cglCharacterDyadicPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  simpa [cglShiftedTailDyadicRow] using
    cglShiftedTailDyadicCoefficient_factor X N q χ s x j

end RHTower
