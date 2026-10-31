import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentTriangularMultiplication
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Continuous unipotent coefficient operations

Finite convolution and the principal-unit inverse recursion make every
matrix coefficient continuous in the free stream. This gives continuity
of the actual group product and of its finite triangular corrections.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
noncomputable section
variable {R X : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [TopologicalSpace X]

private theorem continuous_coeff_product (f g : X → PowerSeries R)
    (hf : ∀ n, Continuous fun x => PowerSeries.coeff n (f x))
    (hg : ∀ n, Continuous fun x => PowerSeries.coeff n (g x)) (N : ℕ) :
    Continuous fun x => PowerSeries.coeff N (f x * g x) := by
  have he : (fun x => PowerSeries.coeff N (f x * g x)) =
      (fun x => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal N,
        PowerSeries.coeff p.1 (f x) * PowerSeries.coeff p.2 (g x)) := by
    funext x
    rw [PowerSeries.coeff_mul]
  rw [he]
  exact continuous_finsetSum _ fun p _ => (hf p.1).mul (hg p.2)

/-- Every coefficient of the principal-unit inverse depends continuously on its input coefficients. -/
theorem continuous_coeff_invOfUnit_one (f : X → PowerSeries R)
    (hf : ∀ n, Continuous fun x => PowerSeries.coeff n (f x)) (N : ℕ) :
    Continuous fun x => PowerSeries.coeff N (PowerSeries.invOfUnit (f x) 1) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    have he : (fun x => PowerSeries.coeff N (PowerSeries.invOfUnit (f x) 1)) =
        (fun x => if N = 0 then (1 : R) else -(1 : R) *
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal N, if p.2 < N then
            PowerSeries.coeff p.1 (f x) * PowerSeries.coeff p.2 (PowerSeries.invOfUnit (f x) 1)
            else 0) := by
      funext x
      rw [PowerSeries.coeff_invOfUnit, inv_one, Units.val_one]
    rw [he]
    split_ifs with hN
    · exact continuous_const
    · apply Continuous.mul continuous_const
      apply continuous_finsetSum
      intro p hp
      by_cases hl : p.2 < N
      · simp only [if_pos hl]
        exact (hf p.1).mul (ih p.2 hl)
      · simp only [if_neg hl]
        exact continuous_const

private theorem continuous_streamUpperLeft_coeff (N : ℕ) :
    Continuous fun x : ℕ → R => PowerSeries.coeff N (streamUpperLeft R x) := by
  cases N with
  | zero =>
    simp only [streamUpperLeft, PowerSeries.coeff_mk]
    exact continuous_const
  | succ n =>
    simpa only [streamUpperLeft, PowerSeries.coeff_mk] using continuous_apply (3 * n + 2)

private theorem continuous_streamUpperRight_coeff (N : ℕ) :
    Continuous fun x : ℕ → R => PowerSeries.coeff N (streamUpperRight R x) := by
  simpa only [streamUpperRight, PowerSeries.coeff_mk] using continuous_apply (3 * N)

private theorem continuous_streamLowerLeft_coeff (N : ℕ) :
    Continuous fun x : ℕ → R => PowerSeries.coeff N (streamLowerLeft R x) := by
  cases N with
  | zero =>
    simp only [streamLowerLeft, PowerSeries.coeff_mk]
    exact continuous_const
  | succ n =>
    simpa only [streamLowerLeft, PowerSeries.coeff_mk] using continuous_apply (3 * n + 1)

/-- All four decoded matrix entries have continuous coefficients in the free stream. -/
theorem continuous_unipotentDecoded_coeff (i j : Fin 2) (N : ℕ) :
    Continuous fun x : ℕ → R =>
      PowerSeries.coeff N (((unipotentCoefficientStreamEquiv R).symm x).1 i j) := by
  fin_cases i <;> fin_cases j
  · exact continuous_streamUpperLeft_coeff N
  · exact continuous_streamUpperRight_coeff N
  · exact continuous_streamLowerLeft_coeff N
  · have hbc (n : ℕ) : Continuous fun x : ℕ → R =>
        PowerSeries.coeff n (1 + streamUpperRight R x * streamLowerLeft R x) := by
      have hc : Continuous (fun _ : ℕ → R => PowerSeries.coeff n (1 : PowerSeries R)) := continuous_const
      have hp := continuous_coeff_product (streamUpperRight R) (streamLowerLeft R)
        continuous_streamUpperRight_coeff continuous_streamLowerLeft_coeff n
      convert hc.add hp using 1
      funext x
      exact map_add (PowerSeries.coeff n) 1 (streamUpperRight R x * streamLowerLeft R x)
    change Continuous fun x : ℕ → R =>
      PowerSeries.coeff N (PowerSeries.invOfUnit (streamUpperLeft R x) 1 *
        (1 + streamUpperRight R x * streamLowerLeft R x))
    exact continuous_coeff_product _ _
      (continuous_coeff_invOfUnit_one (streamUpperLeft R) continuous_streamUpperLeft_coeff) hbc N

private theorem continuous_stream_of_coefficients (f : X → unipotentCoefficientGroup R)
    (hf : ∀ i j n, Continuous fun x => PowerSeries.coeff n ((f x).1 i j)) :
    Continuous fun x => unipotentCoefficientStreamEquiv R (f x) := by
  apply continuous_pi
  intro N
  change Continuous fun x =>
    unipotentCoordinatesToStream R (unipotentCoefficientToCoordinates R (f x)) N
  unfold unipotentCoordinatesToStream
  split_ifs <;> exact hf _ _ _

/-- Actual group multiplication expressed in the unrestricted coefficient streams. -/
def unipotentStreamProduct (p : (ℕ → R) × (ℕ → R)) : ℕ → R :=
  unipotentCoefficientStreamEquiv R
    ((unipotentCoefficientStreamEquiv R).symm p.1 * (unipotentCoefficientStreamEquiv R).symm p.2)

/-- Actual unipotent multiplication is continuous for the coefficient-stream topology. -/
theorem continuous_unipotentStreamProduct : Continuous (unipotentStreamProduct (R := R)) := by
  apply continuous_stream_of_coefficients
  intro i j N
  have he : (fun p : (ℕ → R) × (ℕ → R) => PowerSeries.coeff N
      (((unipotentCoefficientStreamEquiv R).symm p.1 *
        (unipotentCoefficientStreamEquiv R).symm p.2).1 i j)) =
      (fun p => PowerSeries.coeff N
        (((unipotentCoefficientStreamEquiv R).symm p.1).1 i 0 *
          ((unipotentCoefficientStreamEquiv R).symm p.2).1 0 j) +
        PowerSeries.coeff N
          (((unipotentCoefficientStreamEquiv R).symm p.1).1 i 1 *
            ((unipotentCoefficientStreamEquiv R).symm p.2).1 1 j)) := by
    funext p
    change PowerSeries.coeff N
      ((((unipotentCoefficientStreamEquiv R).symm p.1).1 *
        ((unipotentCoefficientStreamEquiv R).symm p.2).1) i j) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add]
  rw [he]
  apply Continuous.add
  · exact continuous_coeff_product _ _
      (fun n => (continuous_unipotentDecoded_coeff i 0 n).comp continuous_fst)
      (fun n => (continuous_unipotentDecoded_coeff 0 j n).comp continuous_snd) N
  · exact continuous_coeff_product _ _
      (fun n => (continuous_unipotentDecoded_coeff i 1 n).comp continuous_fst)
      (fun n => (continuous_unipotentDecoded_coeff 1 j n).comp continuous_snd) N

private theorem continuous_prefixCompletion_stream (N : ℕ) :
    Continuous fun x : Fin N → R => unipotentCoefficientStreamEquiv R (unipotentPrefixCompletion x) := by
  apply continuous_pi
  intro k
  simp only [unipotentPrefixCompletion, Equiv.apply_symm_apply]
  by_cases hk : k < N
  · simp only [dif_pos hk]
    exact continuous_apply (⟨k, hk⟩ : Fin N)
  · simp only [dif_neg hk]
    exact continuous_const

/-- Actual group inversion expressed in the unrestricted coefficient stream. -/
def unipotentStreamInverse (x : ℕ → R) : ℕ → R :=
  unipotentCoefficientStreamEquiv R (((unipotentCoefficientStreamEquiv R).symm x)⁻¹)

/-- Inversion is continuous because the determinant-one inverse is the matrix adjugate. -/
theorem continuous_unipotentStreamInverse : Continuous (unipotentStreamInverse (R := R)) := by
  apply continuous_stream_of_coefficients
  intro i j N
  change Continuous fun x : ℕ → R => PowerSeries.coeff N
    ((((unipotentCoefficientStreamEquiv R).symm x).1)⁻¹ i j)
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  · exact continuous_unipotentDecoded_coeff 1 1 N
  · change Continuous fun x : ℕ → R =>
      PowerSeries.coeff N (-(((unipotentCoefficientStreamEquiv R).symm x).1 0 1))
    convert (continuous_unipotentDecoded_coeff (R := R) 0 1 N).neg using 1
    funext x
    exact map_neg (PowerSeries.coeff N) (((unipotentCoefficientStreamEquiv R).symm x).1 0 1)
  · change Continuous fun x : ℕ → R =>
      PowerSeries.coeff N (-(((unipotentCoefficientStreamEquiv R).symm x).1 1 0))
    convert (continuous_unipotentDecoded_coeff (R := R) 1 0 N).neg using 1
    funext x
    exact map_neg (PowerSeries.coeff N) (((unipotentCoefficientStreamEquiv R).symm x).1 1 0)
  · exact continuous_unipotentDecoded_coeff 0 0 N

/-- The finite strict-prefix correction is continuous in both prefixes. -/
theorem continuous_unipotentTriangularCorrection (N : ℕ) :
    Continuous fun p : (Fin N → R) × (Fin N → R) => unipotentTriangularCorrection N p.1 p.2 := by
  have hf : Continuous fun p : (Fin N → R) × (Fin N → R) =>
      unipotentCoefficientStreamEquiv R (unipotentPrefixCompletion p.1) :=
    (continuous_prefixCompletion_stream (R := R) N).comp continuous_fst
  have hg : Continuous fun p : (Fin N → R) × (Fin N → R) =>
      unipotentCoefficientStreamEquiv R (unipotentPrefixCompletion p.2) :=
    (continuous_prefixCompletion_stream (R := R) N).comp continuous_snd
  have hp : Continuous fun p : (Fin N → R) × (Fin N → R) =>
      unipotentCoefficientStreamEquiv R (unipotentPrefixCompletion p.1 * unipotentPrefixCompletion p.2) := by
    have hc : Continuous fun p : (Fin N → R) × (Fin N → R) =>
        unipotentStreamProduct
          (unipotentCoefficientStreamEquiv R (unipotentPrefixCompletion p.1),
            unipotentCoefficientStreamEquiv R (unipotentPrefixCompletion p.2)) :=
      continuous_unipotentStreamProduct.comp (hf.prodMk hg)
    simpa only [unipotentStreamProduct, Equiv.symm_apply_apply] using hc
  change Continuous fun p : (Fin N → R) × (Fin N → R) =>
    unipotentCoefficientStreamEquiv R (unipotentPrefixCompletion p.1 * unipotentPrefixCompletion p.2) N -
      unipotentCoefficientStreamEquiv R (unipotentPrefixCompletion p.1) N -
        unipotentCoefficientStreamEquiv R (unipotentPrefixCompletion p.2) N
  exact (((continuous_apply N).comp hp).sub ((continuous_apply N).comp hf)).sub
    ((continuous_apply N).comp hg)

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.continuous_unipotentStreamProduct
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.continuous_unipotentStreamInverse
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.continuous_unipotentTriangularCorrection
