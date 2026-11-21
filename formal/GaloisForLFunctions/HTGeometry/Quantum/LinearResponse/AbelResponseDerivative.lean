import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelPerturbationBounds
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelForwardProbeGeneric
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelWidthScaling
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Differentiating along a Hermitian line

The uniform quadratic remainder yields the derivative of each
measured entry at every point of a real affine Hermitian family.
-/

open Filter Matrix Set MeasureTheory
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] {H T : Matrix ι ι ℂ}

omit [Fintype ι] in
/-- A real parameter preserves Hermiticity along the affine family. -/
theorem abelAffineHamiltonian_isHermitian (hH : H.IsHermitian) (hT : T.IsHermitian)
    (t : ℝ) : (H + (t : ℂ) • T).IsHermitian := by
  show (H + (t : ℂ) • T)ᴴ = H + (t : ℂ) • T
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal, show Hᴴ = H from hH, show Tᴴ = T from hT]

private theorem norm_entry_sq_le_hsSqRe (X : Matrix ι ι ℂ) (i j : ι) :
    ‖X i j‖ ^ 2 ≤ hsSqRe X := by
  rw [hsSqRe_eq_sum]
  calc
    _ ≤ ∑ k, ‖X k j‖ ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg ‖X k j‖) (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum
      (fun l _ => Finset.sum_nonneg (fun k _ => sq_nonneg ‖X k l‖)) (Finset.mem_univ j)

variable [DecidableEq ι]

/-- The first variation is the actual derivative along every real
affine Hermitian line, including eigenvalue collisions. -/
theorem hasDerivAt_abelResponse_affine_entry (hH : H.IsHermitian) (hT : T.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) (s : ℝ) (i j : ι) :
    HasDerivAt (fun t : ℝ =>
      hamiltonianDampedGapResponse (abelAffineHamiltonian_isHermitian hH hT t) 0 ε X i j)
      (abelResponseVariation (abelAffineHamiltonian_isHermitian hH hT s) ε T X i j) s := by
  let hS := abelAffineHamiltonian_isHermitian hH hT s
  let R := fun t : ℝ => hamiltonianDampedGapResponse
    (abelAffineHamiltonian_isHermitian hH hT t) 0 ε X
  let V := abelResponseVariation hS ε T X
  let b := 4 * hsSqRe T / (ε : ℝ) ^ 2
  let c := b * √(hsSqRe X)
  have hb : 0 ≤ b :=
    div_nonneg (mul_nonneg (by positivity) (hsSqRe_nonneg T)) (sq_nonneg (ε : ℝ))
  have hc : 0 ≤ c := mul_nonneg hb (Real.sqrt_nonneg _)
  change HasDerivAt (fun t => R t i j) (V i j) s
  apply HasDerivAt.of_isLittleO
  refine Asymptotics.IsBigO.trans_isLittleO
    (Asymptotics.IsBigO.of_bound c (.of_forall fun t => ?_))
    (Asymptotics.isLittleO_pow_sub_sub s (m := 2) (Nat.lt_succ_self 1))
  let hK := abelAffineHamiltonian_isHermitian hH hT t
  let d := ((t - s : ℝ) : ℂ)
  have hdiff : (H + (t : ℂ) • T) - (H + (s : ℂ) • T) = d • T := by
    rw [show d = (t : ℂ) - (s : ℂ) from Complex.ofReal_sub t s, sub_smul]
    abel
  have hv : abelResponseVariation hS ε (d • T) X = d • V := by
    calc
      _ = abelResponseVariationLinear hS ε X (d • T) := rfl
      _ = d • abelResponseVariationLinear hS ε X T :=
        (abelResponseVariationLinear hS ε X).map_smul d T
      _ = _ := rfl
  have hsq := hsSqRe_abelResponse_sub_variation_le hS hK ε X
  change hsSqRe (R t - R s -
    abelResponseVariation hS ε ((H + (t : ℂ) • T) - (H + (s : ℂ) • T)) X) ≤ _ at hsq
  rw [hdiff, hv, hsSqRe_complex_smul, show ‖d‖ = ‖t - s‖ from Complex.norm_real _] at hsq
  let E := R t - R s - d • V
  have hentry : ‖E i j‖ ^ 2 ≤ (c * ‖t - s‖ ^ 2) ^ 2 :=
    (norm_entry_sq_le_hsSqRe E i j).trans (hsq.trans (le_of_eq (by
      dsimp only [c, b]
      rw [mul_pow, mul_pow, Real.sq_sqrt (hsSqRe_nonneg X)]
      simp only [div_eq_mul_inv]
      ring)))
  have hnorm : ‖E i j‖ ≤ c * ‖t - s‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (sq_nonneg _))).mp hentry
  change ‖R t i j - R s i j - (t - s) • V i j‖ ≤ c * ‖‖t - s‖ ^ 2‖
  rw [Real.norm_of_nonneg (sq_nonneg ‖t - s‖)]
  exact hnorm

/-- For almost every coupling vector, the only Hermitian directions
invisible to both first variations are scalar energy shifts. -/
theorem ae_abelForwardVariations_eq_zero_iff_scalarDirection {d N : ℕ} (o : Fin d)
    (ε : Ioi (0 : ℝ)) (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ a, (P a).IsHermitian) :
    ∀ᵐ θ : Fin N → ℝ ∂volume,
      ∀ (S : Matrix (Fin d) (Fin d) ℂ), S.IsHermitian →
        let hH := isHermitian_spectralEnsembleMatrix hP θ
        (abelResponseVariation hH ε S (abelDiagonalProbe d) = 0 ∧
          abelResponseVariation hH ε S (abelSumProbe d) = 0) ↔
          ∃ r : ℝ, S = (r : ℂ) • 1 := by
  filter_upwards [ae_abelForwardReadings_eq_iff_scalarDifference o ε P hP] with θ hθ
  intro S hS
  let H := spectralEnsembleMatrix P θ
  let hH := isHermitian_spectralEnsembleMatrix hP θ
  let hK : (H - S).IsHermitian := hH.sub hS
  have hD := abelResponseVariation_sub_eq_zero_iff hH hK ε (abelDiagonalProbe d)
  have hJ := abelResponseVariation_sub_eq_zero_iff hH hK ε (abelSumProbe d)
  have hs := (hθ (H - S) hK).trans (hermitian_scalarDifference_iff_real o hH hK)
  rw [show spectralEnsembleMatrix P θ - (H - S) = S from sub_sub_cancel H S] at hD hJ hs
  exact (and_congr hD hJ).trans hs

#print axioms hasDerivAt_abelResponse_affine_entry
#print axioms ae_abelForwardVariations_eq_zero_iff_scalarDirection

end

end GaloisForLFunctions.HTGeometry
