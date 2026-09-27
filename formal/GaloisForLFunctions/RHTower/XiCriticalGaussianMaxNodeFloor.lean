import GaloisForLFunctions.RHTower.XiCriticalGaussianEnergyFloor

/-!
# An independent critical reserve with the largest selected node as heat rate

Distinct actual critical nodes contribute simultaneously to the positive real
channel. Summing those contributions before using interpolation removes an
extra dimension factor from the previous floor. Its heat rate is the largest
selected squared node, rather than one plus the sum of all squared nodes.
-/

open scoped Real BigOperators
open Complex GaloisForLFunctions.HTGeometry
noncomputable section

namespace RHTower

/-- Actual critical nodes provide a coefficient-uniform floor with an explicit positive
Vandermonde constant and the exact largest selected squared height as decay rate. -/
theorem exists_xiGaussianRealChannel_maxNode_floor (n : ℕ) :
    ∃ (γ : Fin (n + 1) → ℝ) (q : Fin (n + 1) → XiZeroCopy)
      (iMax : Fin (n + 1)) (c : ℝ),
      0 < c ∧ Function.Injective (fun i => (γ i : ℂ) ^ 2) ∧
      (∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      (∀ i, γ i ^ 2 ≤ γ iMax ^ 2) ∧
      c = ‖(Matrix.vandermonde (fun i => (γ i : ℂ) ^ 2)).det‖ ^ 2 /
        (((n + 1 : ℕ) : ℝ) ^ 2 * polynomialSamplingCap (fun i => (γ i : ℂ) ^ 2) ^ 2) ∧
      ∀ (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}),
        c * Real.exp (-(γ iMax ^ 2 * (t : ℝ))) *
          (∑ j ∈ Finset.range (n + 1), a j ^ 2) ≤
            xiGaussianRealChannelEnergy
              (∑ j ∈ Finset.range (n + 1), Polynomial.C (a j) * Polynomial.X ^ j) t := by
  classical
  let N := n + 1
  obtain ⟨γ, q, hinj, hq, _⟩ := exists_xiCriticalGaussian_nodes N
  obtain ⟨iMax, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin N))
    (fun i => γ i ^ 2) ⟨⟨0, by dsimp only [N]; omega⟩, Finset.mem_univ _⟩
  let z : Fin N → ℂ := fun i => (γ i : ℂ) ^ 2
  let C := polynomialSamplingCap z
  let A : ℝ := (N : ℝ) ^ 2 * C ^ 2
  let D : ℝ := ‖(Matrix.vandermonde z).det‖ ^ 2
  let L : ℝ := γ iMax ^ 2
  have hN : (0 : ℝ) < N := by dsimp only [N]; positivity
  have hC : 0 < C := by
    unfold C polynomialSamplingCap
    exact mul_pos (by positivity)
      (pow_pos (pow_pos (lt_of_lt_of_le zero_lt_one (one_le_phaseFrequencyScale z)) _) _)
  have hA : 0 < A := mul_pos (pow_pos hN _) (pow_pos hC _)
  have hD : 0 < D := pow_pos
    (norm_pos_iff.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)) _
  have hqinj : Function.Injective q := by
    intro i j hij
    apply hinj
    change (γ i : ℂ) ^ 2 = (γ j : ℂ) ^ 2
    rw [← (hq i).2, ← (hq j).2, hij]
  refine ⟨γ, q, iMax, D / A, div_pos hD hA, hinj, hq,
    fun i => hmax i (Finset.mem_univ i), rfl, ?_⟩
  intro a t
  let Q : Polynomial ℝ := ∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j
  let v : Fin N → ℂ := fun j => (a j : ℂ)
  let J := xiGaussianRealChannelEnergy Q t
  let f : XiZeroCopy → ℝ := fun p =>
    (‖xiPolynomialGaussianHeatTerm Q t p‖ + (xiPolynomialGaussianHeatTerm Q t p).re) / 2
  have heval (i : Fin N) : ‖polynomialSample v (z i)‖ ^ 2 = (Q.eval (γ i ^ 2)) ^ 2 := by
    have he : evalRealPolynomial Q (z i) = polynomialSample v (z i) := by
      rw [evalRealPolynomial_rangeSum, ← Fin.sum_univ_eq_sum_range]
      rfl
    rw [← he]
    simp only [z, ← Complex.ofReal_pow, evalRealPolynomial_ofReal,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsum : (∑ i : Fin N, f (q i)) ≤ J := by
    have h := (summable_xiGaussianRealChannel_atom Q t).sum_le_tsum
      (Finset.univ.image q) (fun p _ => xiGaussianRealChannel_atom_nonneg Q t p)
    change (∑ p ∈ Finset.univ.image q, f p) ≤ J at h
    rw [Finset.sum_image (fun i _ j _ hij => hqinj hij)] at h
    exact h
  have hheat : Real.exp (-(L * (t : ℝ))) *
      (∑ i : Fin N, ‖polynomialSample v (z i)‖ ^ 2) ≤ J := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum (fun i _ => ?_)).trans hsum
    change _ ≤ (‖xiPolynomialGaussianHeatTerm Q t (q i)‖ +
      (xiPolynomialGaussianHeatTerm Q t (q i)).re) / 2
    rw [xiGaussianRealChannel_atom_at_real Q t (γ i) ⟨q i, (hq i).2⟩, heval]
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (hmax i (Finset.mem_univ i)) t.property.le
    change _ ≤ γ iMax ^ 2 * (t : ℝ) at h
    dsimp only [L]
    nlinarith only [h]
  have hsamp : D * (∑ j ∈ Finset.range N, a j ^ 2) ≤
      A * ∑ i : Fin N, ‖polynomialSample v (z i)‖ ^ 2 := by
    have h := polynomialSample_energy_bound z v
    have hcoeff : (∑ j : Fin N, ‖v j‖ ^ 2) = ∑ j ∈ Finset.range N, a j ^ 2 := by
      simp only [v, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact Fin.sum_univ_eq_sum_range (fun j => a j ^ 2) N
    rwa [hcoeff] at h
  have hsampleFloor : D / A * (∑ j ∈ Finset.range N, a j ^ 2) ≤
      ∑ i : Fin N, ‖polynomialSample v (z i)‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hA]
    simpa only [mul_comm] using hsamp
  calc
    _ = Real.exp (-(L * (t : ℝ))) * (D / A * ∑ j ∈ Finset.range N, a j ^ 2) := by ring
    _ ≤ Real.exp (-(L * (t : ℝ))) * ∑ i : Fin N, ‖polynomialSample v (z i)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hsampleFloor (Real.exp_pos _).le
    _ ≤ J := hheat

end RHTower
