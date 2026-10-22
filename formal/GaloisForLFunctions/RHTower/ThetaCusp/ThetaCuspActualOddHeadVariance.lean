import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspGlobalOddCompensation
import GaloisForLFunctions.HTGeometry.SixPointSignedHankel
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchurMovingMinimizerVariance

/-!
# The actual corrected odd head and its moving-minimizer reserve

The zero-mass correction already used to prove the sixth mixed rank makes the
literal weighted odd three-by-three head positive at every positive center.
The next column uses the actual eighth, tenth, and twelfth reflection jets.
For any terminal entry, the fixed-vector source energy is exactly the local
Schur current plus a nonnegative moving-minimizer square.  The terminal entry
and its integrated sign are deliberately not replaced by a positivity premise.
-/

namespace RHTower
noncomputable section
open Matrix GaloisForLFunctions.HTGeometry

private theorem hankelThreeMatrix_posDef {p0 p2 p4 p6 p8 : ℝ}
    (h0 : 0 < p0) (h2 : 0 < p0*p4-p2^(2 : ℕ))
    (h3 : 0 < HilbertMetric.signedEvenHankelThreeDet p0 p2 p4 p6 p8) :
    (!![p0,p2,p4; p2,p4,p6; p4,p6,p8] : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro v hv
    have hcoords : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hv
      funext i
      fin_cases i <;> simp [hn.1, hn.2.1, hn.2.2]
    have h := hankelThreeQuadratic_pos h0 h2 h3 hcoords
    have heq : star v ⬝ᵥ
        (!![p0,p2,p4; p2,p4,p6; p4,p6,p8] : Matrix (Fin 3) (Fin 3) ℝ).mulVec v =
        hankelThreeQuadratic p0 p2 p4 p6 p8 (v 0) (v 1) (v 2) := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hankelThreeQuadratic]
      ring
    rwa [heq]

/-- The literal weighted odd head with its lawful zero-mass tenth-entry correction. -/
def thetaCuspCorrectedOddHeadMatrix (a C r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let w := r*Real.sinh (a*r)
  let x := r/2
  !![w*(-thetaCuspNativeReflectionJet 2 x), w*thetaCuspNativeReflectionJet 4 x,
      w*(-thetaCuspNativeReflectionJet 6 x);
     w*thetaCuspNativeReflectionJet 4 x, w*(-thetaCuspNativeReflectionJet 6 x),
      w*thetaCuspNativeReflectionJet 8 x;
     w*(-thetaCuspNativeReflectionJet 6 x), w*thetaCuspNativeReflectionJet 8 x,
      thetaCuspCenterCorrectedOddLastEntry a C r]

/-- The source-selected correction makes the entire local odd head strict. -/
theorem thetaCuspCorrectedOddHeadMatrix_posDef {a C r : ℝ}
    (ha : 0 < a) (hC0 : 1000000000 ≤ C) (hC1 : C ≤ 3000000000)
    (hr : 0 < r) : (thetaCuspCorrectedOddHeadMatrix a C r).PosDef := by
  let w := r*Real.sinh (a*r)
  let x := r/2
  have hw : 0 < w := mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha hr))
  have hh := thetaCuspNativeOddHankelThree_head_pos x
  have h0 : 0 < w*(-thetaCuspNativeReflectionJet 2 x) := mul_pos hw hh.1
  have h2 : 0 <
      (w*(-thetaCuspNativeReflectionJet 2 x))*(w*(-thetaCuspNativeReflectionJet 6 x))-
        (w*thetaCuspNativeReflectionJet 4 x)^(2 : ℕ) := by
    calc
      _ = w^(2 : ℕ)*((-thetaCuspNativeReflectionJet 2 x)*
          (-thetaCuspNativeReflectionJet 6 x)-
          (thetaCuspNativeReflectionJet 4 x)^(2 : ℕ)) := by ring
      _ > 0 := mul_pos (sq_pos_of_pos hw) hh.2
  have h3 : 0 < HilbertMetric.signedEvenHankelThreeDet
      (w*(-thetaCuspNativeReflectionJet 2 x))
      (w*thetaCuspNativeReflectionJet 4 x)
      (w*(-thetaCuspNativeReflectionJet 6 x))
      (w*thetaCuspNativeReflectionJet 8 x)
      (thetaCuspCenterCorrectedOddLastEntry a C r) :=
    thetaCuspCenterCorrectedOddDet_pos_global ha hC0 hC1 hr
  exact hankelThreeMatrix_posDef h0 h2 h3

/-- The literal weighted cross-column for the fourteenth-jet successor. -/
def thetaCuspCorrectedOddCross (a r : ℝ) : Fin 3 → ℝ :=
  let w := r*Real.sinh (a*r)
  let x := r/2
  ![w*thetaCuspNativeReflectionJet 8 x,
    w*(-thetaCuspNativeReflectionJet 10 x),
    w*thetaCuspNativeReflectionJet 12 x]

/-- The fixed-vector source energy retains the exact positive local variance. -/
theorem thetaCuspActualOddFourSource_eq_localSchur_add_variance
    {a C r : ℝ} (ha : 0 < a)
    (hC0 : 1000000000 ≤ C) (hC1 : C ≤ 3000000000) (hr : 0 < r)
    (d : ℝ) (v : Fin 3 → ℝ) :
    let A := thetaCuspCorrectedOddHeadMatrix a C r
    let b := thetaCuspCorrectedOddCross a r
    let u := A⁻¹.mulVec b
    d - 2*(v ⬝ᵥ b) + v ⬝ᵥ (A.mulVec v) =
      (d-(u ⬝ᵥ b)) + (v-u) ⬝ᵥ (A.mulVec (v-u)) := by
  dsimp
  have hA := thetaCuspCorrectedOddHeadMatrix_posDef ha hC0 hC1 hr
  have h := schurMovingMinimizer_inverse
    (thetaCuspCorrectedOddHeadMatrix a C r) (thetaCuspCorrectedOddCross a r) v hA
  linarith only [h]

/-- The variance term in the actual source decomposition is nonnegative. -/
theorem thetaCuspActualOddFourSource_variance_nonneg
    {a C r : ℝ} (ha : 0 < a)
    (hC0 : 1000000000 ≤ C) (hC1 : C ≤ 3000000000) (hr : 0 < r)
    (v : Fin 3 → ℝ) :
    let A := thetaCuspCorrectedOddHeadMatrix a C r
    let u := A⁻¹.mulVec (thetaCuspCorrectedOddCross a r)
    0 ≤ (v-u) ⬝ᵥ (A.mulVec (v-u)) := by
  dsimp
  have hA := thetaCuspCorrectedOddHeadMatrix_posDef ha hC0 hC1 hr
  simpa using hA.posSemidef.dotProduct_mulVec_nonneg
    (v-(thetaCuspCorrectedOddHeadMatrix a C r)⁻¹.mulVec
      (thetaCuspCorrectedOddCross a r))

end
end RHTower
