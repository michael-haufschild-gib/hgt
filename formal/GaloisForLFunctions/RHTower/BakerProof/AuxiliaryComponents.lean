import GaloisForLFunctions.RHTower.BakerProof.AuxiliaryZeroEstimate

/-!
# Shifted component functions in Baker's extrapolation

The matrix rows are values of a family of algebraic coefficient-functions indexed by multiindices.
Their derivatives obey the triangular shift law that drives Baker extrapolation: a derivative of the
component at `ν` is a logarithmic linear combination of components at `ν + multi`.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerProof

noncomputable def Relation.auxiliaryComponent (R : Relation) (c : ℤ)
    (pivot : Fin R.n) (ν : R.NonPivot pivot → ℕ) {L : ℕ}
    (η : R.Column L → 𝓞 R.CoefficientField) (z : ℂ) : ℂ :=
  ∑ m, (∏ i : R.NonPivot pivot,
      R.coeffEmbedding (R.scaledDirection c pivot m i) ^ ν i) *
    R.integralCoeffEmbedding (η m) * Complex.exp (R.frequency m * z)

theorem Relation.iteratedDeriv_auxiliaryComponent (R : Relation) (c : ℤ)
    (pivot : Fin R.n) (ν : R.NonPivot pivot → ℕ) {L : ℕ}
    (η : R.Column L → 𝓞 R.CoefficientField) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (R.auxiliaryComponent c pivot ν η) z =
      ∑ m, (∏ i : R.NonPivot pivot,
          R.coeffEmbedding (R.scaledDirection c pivot m i) ^ ν i) *
        R.integralCoeffEmbedding (η m) * R.frequency m ^ k *
          Complex.exp (R.frequency m * z) := by
  unfold Relation.auxiliaryComponent
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [iteratedDeriv_const_mul_field]
    rw [congrFun (iteratedDeriv_cexp_const_mul k (R.frequency m)) z]
    ring
  · intro m hm
    fun_prop

theorem Relation.auxiliaryComponent_eq_zero_of_kernel (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L S T : ℕ} (η : R.Column L → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0)
    (sample : Fin S) (ν : R.NonPivot pivot → ℕ) (hν : ∀ i, ν i < T) :
    R.auxiliaryComponent c pivot ν η (sample : ℕ) = 0 := by
  let row : R.Row pivot S T := ⟨sample, fun i => ⟨ν i, hν i⟩⟩
  have hrow := R.auxiliary_kernel_row_eq c hint pivot η hker row
  simpa [Relation.auxiliaryComponent, row] using hrow

/-- **Baker's triangular shift law.**  After multiplication by the scaled pivot coefficient,
the `k`-th derivative of component `ν` is the multinomial logarithmic combination of the shifted
components `ν + multi`, with `|multi| = k`. -/
theorem Relation.scaled_iteratedDeriv_auxiliaryComponent (R : Relation) (c : ℤ)
    (pivot : Fin R.n) (ν : R.NonPivot pivot → ℕ) {L : ℕ}
    (η : R.Column L → 𝓞 R.CoefficientField) (k : ℕ) (z : ℂ) :
    R.coeffEmbedding (R.scaledCoeff c pivot) ^ k *
        iteratedDeriv k (R.auxiliaryComponent c pivot ν η) z =
      ∑ multi ∈ Finset.piAntidiag (Finset.univ : Finset (R.NonPivot pivot)) k,
        (Nat.multinomial Finset.univ multi : ℂ) *
          (∏ i : R.NonPivot pivot,
            ((Real.log (R.p (i : Fin R.n)) : ℝ) : ℂ) ^ multi i) *
            R.auxiliaryComponent c pivot (fun i => ν i + multi i) η z := by
  let a : ℂ := R.coeffEmbedding (R.scaledCoeff c pivot)
  let D : R.Column L → R.NonPivot pivot → ℂ := fun m i =>
    R.coeffEmbedding (R.scaledDirection c pivot m i)
  let logp : R.NonPivot pivot → ℂ := fun i => ((Real.log (R.p i) : ℝ) : ℂ)
  rw [R.iteratedDeriv_auxiliaryComponent]
  rw [Finset.mul_sum]
  calc
    ∑ m, a ^ k * ((∏ i, D m i ^ ν i) * R.integralCoeffEmbedding (η m) *
        R.frequency m ^ k * Complex.exp (R.frequency m * z)) =
        ∑ m, (∏ i, D m i ^ ν i) * R.integralCoeffEmbedding (η m) *
          (∑ i : R.NonPivot pivot, D m i * logp i) ^ k *
          Complex.exp (R.frequency m * z) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [← R.scaled_frequency_eq c pivot m]
      simp only [a]
      ring
    _ = ∑ m, (∏ i, D m i ^ ν i) * R.integralCoeffEmbedding (η m) *
          (∑ multi ∈ Finset.piAntidiag (Finset.univ : Finset (R.NonPivot pivot)) k,
            (Nat.multinomial Finset.univ multi : ℂ) *
              ∏ i, (D m i * logp i) ^ multi i) *
          Complex.exp (R.frequency m * z) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_pow_eq_sum_piAntidiag]
    _ = ∑ multi ∈ Finset.piAntidiag (Finset.univ : Finset (R.NonPivot pivot)) k,
          (Nat.multinomial Finset.univ multi : ℂ) * (∏ i, logp i ^ multi i) *
            (∑ m, (∏ i, D m i ^ (ν i + multi i)) *
              R.integralCoeffEmbedding (η m) * Complex.exp (R.frequency m * z)) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro multi hmulti
      apply Finset.sum_congr rfl
      intro m hm
      simp_rw [mul_pow, pow_add]
      simp_rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      rfl

/-- Kernel vanishing of the shifted components propagates to derivatives: if every coordinate of
`ν` remains inside the row box after adding derivative order `k`, then the `k`-th derivative of
component `ν` vanishes at every selected sample. -/
theorem Relation.auxiliaryComponent_iteratedDeriv_eq_zero_of_kernel
    (R : Relation) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L S T : ℕ} (η : R.Column L → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0)
    (sample : Fin S) (ν : R.NonPivot pivot → ℕ) (k : ℕ)
    (hνk : ∀ i, ν i + k < T) :
    iteratedDeriv k (R.auxiliaryComponent c pivot ν η) (sample : ℕ) = 0 := by
  have ha : R.coeffEmbedding (R.scaledCoeff c pivot) ≠ 0 := by
    simp only [R.coeffEmbedding_scaledCoeff]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hc) (R.coeff_ne_zero pivot)
  apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero k ha)
  rw [R.scaled_iteratedDeriv_auxiliaryComponent]
  apply Finset.sum_eq_zero
  intro multi hmulti
  have hsum : ∑ i, multi i = k := (Finset.mem_piAntidiag.mp hmulti).1
  rw [R.auxiliaryComponent_eq_zero_of_kernel c hint pivot η hker sample
    (fun i => ν i + multi i)]
  · ring
  · intro i
    apply lt_of_le_of_lt _ (hνk i)
    apply Nat.add_le_add_left
    rw [← hsum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

end GaloisForLFunctions.RHTower.BakerProof
