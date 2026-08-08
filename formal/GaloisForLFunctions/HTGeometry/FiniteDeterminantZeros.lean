/-
# Zeros of the regularized determinant of a finite matrix

`det₂(1 + zM)` vanishes exactly where `1 + zM` is singular, that is exactly at the reciprocals
`z = −1/λ` of the eigenvalues of `M`, and it vanishes there to the order given by the number of
Schur diagonal entries equal to `λ` — the algebraic multiplicity.

The factorization is explicit: grouping the Schur product `∏ᵢ (1 + z tᵢ)e^{−z tᵢ}` according to
whether `tᵢ = −1/z₀`, each grouped factor is `−(z − z₀)/z₀` and the rest is nonzero at `z₀`.

Main results:
* `finiteDet2_eq_zero_iff_det` — the determinant is the only source of zeros.
* `finiteDet2_eq_zero_iff_exists_eigenvector` — the zeros are the reciprocal eigenvalues.
* `finiteDet2_factor` — the explicit order of vanishing.
-/
import GaloisForLFunctions.HTGeometry.FiniteRegularizedDeterminant

namespace GaloisForLFunctions.HTGeometry

open Matrix Finset

variable {m : Type*} [Fintype m] [DecidableEq m] {M U T : Matrix m m ℂ}

theorem finiteDet2_eq_zero_iff_det (M : Matrix m m ℂ) (z : ℂ) :
    finiteDet2 M z = 0 ↔ (1 + z • M).det = 0 := by
  rw [finiteDet2, mul_eq_zero]
  simp [Complex.exp_ne_zero]

/-- The zeros of the regularized determinant are exactly the reciprocals of the eigenvalues. -/
theorem finiteDet2_eq_zero_iff_exists_eigenvector (M : Matrix m m ℂ) {z : ℂ} (hz : z ≠ 0) :
    finiteDet2 M z = 0 ↔ ∃ v : m → ℂ, v ≠ 0 ∧ M *ᵥ v = (-z⁻¹) • v := by
  rw [finiteDet2_eq_zero_iff_det]
  constructor
  · intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    refine ⟨v, hv0, ?_⟩
    have hsm : ((1 : Matrix m m ℂ) + z • M) *ᵥ v = v + z • (M *ᵥ v) := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec, smul_mulVec]
    rw [hsm] at hv
    have hzv : z • (M *ᵥ v) = -v := by
      have h2 : v + z • (M *ᵥ v) = 0 := hv
      linear_combination (norm := module) h2
    have hMv : M *ᵥ v = z⁻¹ • (-v) := by
      rw [← hzv, smul_smul, inv_mul_cancel₀ hz, one_smul]
    rw [hMv, smul_neg, ← neg_smul]
  · rintro ⟨v, hv0, hv⟩
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, ?_⟩
    rw [Matrix.add_mulVec, Matrix.one_mulVec, smul_mulVec, hv, smul_smul]
    rw [mul_neg, mul_inv_cancel₀ hz]
    simp

/-- **The order of vanishing of the regularized determinant.**  At `z₀ ≠ 0` the determinant factors
as `(z − z₀)^d` times an entire function that is nonzero at `z₀`, where `d` is the number of Schur
diagonal entries equal to `−1/z₀`. -/
theorem finiteDet2_factor [LinearOrder m] (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hT : T.BlockTriangular id) (hMT : Uᴴ * M * U = T) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ G z₀ ≠ 0 ∧
      ∀ z, finiteDet2 M z
        = (z - z₀) ^ ({i | T i i = -z₀⁻¹} : Finset m).card * G z := by
  classical
  set S : Finset m := {i | T i i = -z₀⁻¹} with hSdef
  refine ⟨fun z => (-z₀⁻¹) ^ S.card * (∏ i ∈ S, Complex.exp (-(z * T i i)))
      * ∏ i ∈ Sᶜ, ((1 + z * T i i) * Complex.exp (-(z * T i i))), ?_, ?_, ?_⟩
  · have hexp : ∀ c : ℂ, Differentiable ℂ fun z : ℂ => Complex.exp (-(z * c)) := fun c =>
      Complex.differentiable_exp.comp ((differentiable_id.mul_const c).neg)
    have hprod : ∀ (s : Finset m) (f : m → ℂ → ℂ), (∀ i ∈ s, Differentiable ℂ (f i)) →
        Differentiable ℂ fun z => ∏ i ∈ s, f i z := by
      intro s f hf
      have hfun : (fun z => ∏ i ∈ s, f i z) = ∏ i ∈ s, f i := by
        funext z; simp [Finset.prod_apply]
      rw [hfun]
      exact Differentiable.finsetProd (f := f) hf
    refine Differentiable.mul (Differentiable.mul (differentiable_const _) ?_) ?_
    · exact hprod _ _ fun i _ => hexp (T i i)
    · exact hprod _ _ fun i _ =>
        Differentiable.mul ((differentiable_const 1).add (differentiable_id.mul_const _))
          (hexp (T i i))
  · refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr (inv_ne_zero hz₀))) ?_) ?_
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => Complex.exp_ne_zero _
    · refine Finset.prod_ne_zero_iff.mpr fun i hi => mul_ne_zero ?_ (Complex.exp_ne_zero _)
      intro hzero
      have hti : T i i = -z₀⁻¹ := by
        have : z₀ * T i i = -1 := by
          have := hzero
          linear_combination this
        field_simp
        linear_combination this
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hti⟩)
        (Finset.mem_compl.mp hi)
  · intro z
    rw [finiteDet2_eq_prod hU1 hU2 hT hMT z,
      ← Finset.prod_mul_prod_compl S fun i => (1 + z * T i i) * Complex.exp (-(z * T i i))]
    have hS : ∀ i ∈ S, (1 + z * T i i) * Complex.exp (-(z * T i i))
        = (-z₀⁻¹) * (z - z₀) * Complex.exp (-(z * T i i)) := by
      intro i hi
      have hti : T i i = -z₀⁻¹ := (Finset.mem_filter.mp hi).2
      rw [hti]
      congr 1
      linear_combination -(inv_mul_cancel₀ hz₀)
    rw [Finset.prod_congr rfl hS, Finset.prod_mul_distrib, Finset.prod_const, mul_pow]
    ring

end GaloisForLFunctions.HTGeometry
