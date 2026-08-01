import GaloisForLFunctions.HTGeometry.PrimeDirichletPositiveDefinite

/-!
# Cauchy law for positive-definite kernel packets

A positive-definite translation kernel controls correlations between any two finite packets, not
only correlations with one distinguished anchor.  The mixed packet correlation squared is at most
the product of the two coherent Gram energies.  The result is proved directly from finite kernel
positivity, so it applies without a Hilbert-space realization or a representing measure.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators ComplexConjugate

noncomputable section

/-- Coherent energy of a finite real packet for a translation kernel. -/
def realKernelPacketEnergy (K : ℝ → ℝ) {N : ℕ}
    (t b : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, b i * K (t j - t i) * b j

/-- Mixed correlation of two finite real packets for a translation kernel. -/
def realKernelPacketCross (K : ℝ → ℝ) {N M : ℕ}
    (s a : Fin N → ℝ) (t b : Fin M → ℝ) : ℝ :=
  ∑ i, ∑ j, a i * K (t j - s i) * b j

/-- Every finite packet has nonnegative coherent energy under a positive-definite kernel. -/
theorem realKernelPacketEnergy_nonneg_of_positiveDefinite
    (K : ℝ → ℝ)
    (hPD : PositiveDefiniteOnReal (fun y => (K y : ℂ)))
    {N : ℕ} (t b : Fin N → ℝ) :
    0 ≤ realKernelPacketEnergy K t b := by
  obtain ⟨r, hr, hq⟩ := hPD N t (fun i => (b i : ℂ))
  have hre := congrArg Complex.re hq
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero] at hre
  simpa [realKernelPacketEnergy] using hre.ge.trans_eq hr.symm

/-- **Universal two-packet Cauchy law.**  For an even real positive-definite translation kernel,
the square of every mixed finite-packet correlation is bounded by the product of the two coherent
packet energies. -/
theorem realKernelPacketCross_sq_le_energy_mul_energy_of_positiveDefinite
    (K : ℝ → ℝ)
    (hPD : PositiveDefiniteOnReal (fun y => (K y : ℂ)))
    (hEven : ∀ y, K (-y) = K y)
    {N M : ℕ} (s a : Fin N → ℝ) (t b : Fin M → ℝ) :
    realKernelPacketCross K s a t b ^ 2 ≤
      realKernelPacketEnergy K s a * realKernelPacketEnergy K t b := by
  let A := realKernelPacketEnergy K s a
  let B := realKernelPacketEnergy K t b
  let C := realKernelPacketCross K s a t b
  have hA : 0 ≤ A := realKernelPacketEnergy_nonneg_of_positiveDefinite K hPD s a
  have hB : 0 ≤ B := realKernelPacketEnergy_nonneg_of_positiveDefinite K hPD t b
  have hquad : ∀ z : ℝ, 0 ≤ A * z ^ 2 + 2 * C * z + B := by
    intro z
    let T : Fin (N + M) → ℝ := Fin.append s t
    let D : Fin (N + M) → ℂ :=
      Fin.append (fun i => ((z * a i : ℝ) : ℂ)) (fun j => (b j : ℂ))
    obtain ⟨r, hr, hq⟩ := hPD (N + M) T D
    have hre := congrArg Complex.re hq
    have hform :
        (∑ i, ∑ j, star (D i) * (K (T j - T i) : ℂ) * D j) =
          ((A * z ^ 2 + 2 * C * z + B : ℝ) : ℂ) := by
      simp only [Fin.sum_univ_add, T, D, Fin.append_left, Fin.append_right,
        Complex.star_def, Complex.conj_ofReal]
      dsimp only [A, B, C, realKernelPacketEnergy, realKernelPacketCross]
      rw [show (∑ i : Fin N, ∑ j : Fin N,
            ((z * a i : ℝ) : ℂ) * (K (s j - s i) : ℂ) * ((z * a j : ℝ) : ℂ)) =
          (((∑ i : Fin N, ∑ j : Fin N, a i * K (s j - s i) * a j) * z ^ 2 : ℝ) : ℂ) by
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring]
      rw [show (∑ i : Fin N, ∑ j : Fin M,
            ((z * a i : ℝ) : ℂ) * (K (t j - s i) : ℂ) * (b j : ℂ)) =
          (((∑ i : Fin N, ∑ j : Fin M, a i * K (t j - s i) * b j) * z : ℝ) : ℂ) by
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring]
      rw [show (∑ i : Fin M, ∑ j : Fin N,
            (b i : ℂ) * (K (s j - t i) : ℂ) * ((z * a j : ℝ) : ℂ)) =
          (((∑ i : Fin N, ∑ j : Fin M, a i * K (t j - s i) * b j) * z : ℝ) : ℂ) by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [show s i - t j = -(t j - s i) by ring, hEven]
        push_cast
        ring]
      push_cast
      ring
    rw [hform] at hre
    simp only [Complex.ofReal_re] at hre
    nlinarith
  by_cases hA0 : A = 0
  · have hC0 : C = 0 := by
      by_contra hC
      have hneg := hquad (-B / (2 * C) - 1)
      rw [hA0, zero_mul, zero_add] at hneg
      have hnegEq : 2 * C * (-B / (2 * C) - 1) + B = -2 * C := by
        field_simp [hC]
        ring
      rw [hnegEq] at hneg
      have hpos := hquad (-B / (2 * C) + 1)
      rw [hA0, zero_mul, zero_add] at hpos
      have hposEq : 2 * C * (-B / (2 * C) + 1) + B = 2 * C := by
        field_simp [hC]
        ring
      rw [hposEq] at hpos
      exact hC (le_antisymm (by linarith) (by linarith))
    simpa [hA0, hC0]
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have h := hquad (-C / A)
    field_simp [hA0] at h
    nlinarith

end

end GaloisForLFunctions.HTGeometry
