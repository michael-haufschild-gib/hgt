import GaloisForLFunctions.RHTower.MobiusCoprimeHarmonicUniform
import Mathlib.Algebra.BigOperators.Module
/-!
# Uniform Abel cancellation in a moving Möbius--Gamma row

The harmonic Möbius prefixes are uniformly bounded. Abel summation turns this
into a cutoff- and row-uniform estimate for the literal additive Gamma--Hankel
row at boundary exponent one. The full two-index covariance still needs
collective cancellation among moving rows.
-/


open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace RHTower

private theorem abs_weighted_sum_le_twice_bound
    (a w : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hpartial : ∀ k : ℕ, |∑ i ∈ Finset.range k, a i| ≤ C)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_mono : ∀ i, w i ≤ w (i + 1))
    (N : ℕ) :
    |∑ i ∈ Finset.range N, w i * a i| ≤ 2 * C * w (N - 1) := by
  by_cases hN : N = 0
  · subst N
    simpa using mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)
      (hw_nonneg 0)
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let A : ℕ → ℝ := fun k => ∑ i ∈ Finset.range k, a i
  let d : ℕ → ℝ := fun i => w (i + 1) - w i
  have hd : ∀ i, 0 ≤ d i := fun i => sub_nonneg.mpr (hw_mono i)
  have htel : (∑ i ∈ Finset.range (N - 1), d i) = w (N - 1) - w 0 := by
    simpa [d] using (Finset.sum_range_sub w (N - 1))
  have habel : (∑ i ∈ Finset.range N, w i * a i) =
      w (N - 1) * A N - ∑ i ∈ Finset.range (N - 1), d i * A (i + 1) := by
    simpa only [smul_eq_mul, A, d] using (Finset.sum_range_by_parts w a N)
  have hfirst : |w (N - 1) * A N| ≤ w (N - 1) * C := by
    rw [abs_mul, abs_of_nonneg (hw_nonneg _)]
    exact mul_le_mul_of_nonneg_left (by simpa [A] using hpartial N)
      (hw_nonneg _)
  have hsecond :
      |∑ i ∈ Finset.range (N - 1), d i * A (i + 1)| ≤
        ∑ i ∈ Finset.range (N - 1), d i * C := by
    calc
      |∑ i ∈ Finset.range (N - 1), d i * A (i + 1)| ≤
          ∑ i ∈ Finset.range (N - 1), |d i * A (i + 1)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (N - 1), d i * C := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_nonneg (hd i)]
        exact mul_le_mul_of_nonneg_left (by simpa [A] using hpartial (i + 1)) (hd i)
  rw [habel]
  calc
    |w (N - 1) * A N - ∑ i ∈ Finset.range (N - 1), d i * A (i + 1)| ≤
        |w (N - 1) * A N| +
          |∑ i ∈ Finset.range (N - 1), d i * A (i + 1)| := abs_sub _ _
    _ ≤ w (N - 1) * C +
          ∑ i ∈ Finset.range (N - 1), d i * C := by
      exact add_le_add hfirst hsecond
    _ = C * (2 * w (N - 1) - w 0) := by
      rw [← Finset.sum_mul, htel]
      ring
    _ ≤ 2 * C * w (N - 1) := by
      nlinarith [mul_nonneg hC (hw_nonneg 0)]

private theorem abs_mobiusHarmonic_range_le_two (k : ℕ) :
    |∑ i ∈ Finset.range k, shiftedMobiusRealCoefficient i / ((i + 1 : ℕ) : ℝ)| ≤ 2 := by
  have hsum : ∀ j : ℕ,
      (∑ i ∈ Finset.range j,
        shiftedMobiusRealCoefficient i / ((i + 1 : ℕ) : ℝ)) =
      coprimeMobiusHarmonic 1 j := by
    intro j
    induction j with
    | zero => simp [coprimeMobiusHarmonic]
    | succ j ih =>
      rw [Finset.sum_range_succ, ih]
      unfold coprimeMobiusHarmonic
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1)]
      simp [shiftedMobiusRealCoefficient]
  rw [hsum]
  by_cases hk : k = 0
  · subst k
    simp [coprimeMobiusHarmonic]
  · exact abs_coprimeMobiusHarmonic_le_two 1 k (Nat.one_le_iff_ne_zero.mpr hk)

/-- Literal fixed-row Gamma--Hankel Möbius cross sum. -/
noncomputable def mobiusGammaHankelMovingRow (m N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N,
    shiftedMobiusRealCoefficient i / (((m + i + 2 : ℕ) : ℝ))

/-- A whole additive row cancels uniformly in its moving origin and cutoff. -/
theorem abs_mobiusGammaHankelMovingRow_le (m N : ℕ) :
    |mobiusGammaHankelMovingRow m N| ≤
      4 * (N : ℝ) / ((m + N + 1 : ℕ) : ℝ) := by
  let a : ℕ → ℝ := fun i =>
    shiftedMobiusRealCoefficient i / ((i + 1 : ℕ) : ℝ)
  let w : ℕ → ℝ := fun i =>
    (((i + 1 : ℕ) : ℝ)) / ((m + i + 2 : ℕ) : ℝ)
  have hw_nonneg : ∀ i, 0 ≤ w i := by
    intro i
    dsimp [w]
    positivity
  have hw_mono : ∀ i, w i ≤ w (i + 1) := by
    intro i
    dsimp [w]
    simp only [show i + 1 + 1 = i + 2 by omega,
      show m + (i + 1) + 2 = m + i + 3 by omega]
    have h1 : (0 : ℝ) < ((m + i + 2 : ℕ) : ℝ) := by positivity
    have h2 : (0 : ℝ) < ((m + i + 3 : ℕ) : ℝ) := by positivity
    rw [div_le_div_iff₀ h1 h2]
    push_cast
    nlinarith
  have hrow : mobiusGammaHankelMovingRow m N =
      ∑ i ∈ Finset.range N, w i * a i := by
    unfold mobiusGammaHankelMovingRow
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [w, a]
    have h1 : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    field_simp
  rw [hrow]
  have hab := abs_weighted_sum_le_twice_bound a w 2 (by norm_num)
    (fun k => abs_mobiusHarmonic_range_le_two k) hw_nonneg hw_mono N
  by_cases hN : N = 0
  · subst N
    simp at hab ⊢
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hlast : w (N - 1) = (N : ℝ) / ((m + N + 1 : ℕ) : ℝ) := by
      dsimp [w]
      simp only [show N - 1 + 1 = N by omega,
        show m + (N - 1) + 2 = m + N + 1 by omega]
    rw [hlast] at hab
    calc
      |∑ i ∈ Finset.range N, w i * a i| ≤
          2 * 2 * ((N : ℝ) / ((m + N + 1 : ℕ) : ℝ)) := hab
      _ = 4 * (N : ℝ) / ((m + N + 1 : ℕ) : ℝ) := by ring

/-- The bounded rows are exactly the rows of the literal boundary
Möbius--Gamma--Hankel quadratic form, with no change of coefficients. -/
theorem finiteMobiusGammaHankelEnergy_one_eq_movingRowSum (N : ℕ) :
    finiteMobiusGammaHankelEnergy N 1 =
      ∑ m ∈ Finset.range N,
        shiftedMobiusRealCoefficient m * mobiusGammaHankelMovingRow m N := by
  unfold finiteMobiusGammaHankelEnergy finiteGammaHankelEnergy
    mobiusGammaHankelMovingRow
  simp only [Real.Gamma_one, Real.rpow_one, one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  ring

end RHTower
