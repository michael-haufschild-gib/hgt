import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Divisibility from an integral rational basis

An explicit rational basis of a number field whose vectors are algebraic
integers need not be an integral basis.  Its discriminant nevertheless equals
the absolute field discriminant times the square of an integer index.  This
module packages the exact divisibility consequence needed by explicit
ramification calculations.
-/

namespace NumberField

noncomputable section

/-- The absolute field discriminant divides the discriminant of every
`ℚ`-basis consisting of algebraic integers. -/
theorem discr_dvd_of_integral_basis_discr
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ K) (hint : ∀ i, IsIntegral ℤ (b i))
    {d : ℤ} (hdiscr : Algebra.discr ℚ b = (d : ℚ)) :
    discr K ∣ d := by
  classical
  let b0 := integralBasis K
  let e : ι ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 K) := b.indexEquiv b0
  let b' : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ K := b.reindex e
  let P : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 K))
      (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ := b0.toMatrix b'
  have hPint : ∀ i j, IsIntegral ℤ (P i j) := by
    intro i j
    let x : 𝓞 K := ⟨b' j, by
      dsimp [b']
      rw [Module.Basis.reindex_apply]
      exact hint (e.symm j)⟩
    have hx : algebraMap (𝓞 K) K x = b' j := rfl
    have hrepr := integralBasis_repr_apply K x i
    change IsIntegral ℤ (b0.repr (b' j) i)
    rw [← hx, hrepr]
    exact isIntegral_algebraMap
  have hdet : IsIntegral ℤ P.det := IsIntegral.det hPint
  obtain ⟨z : ℤ, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdet
  have hb' : Algebra.discr ℚ b' = (d : ℚ) := by
    calc
      Algebra.discr ℚ b' = Algebra.discr ℚ (b.reindex e) := rfl
      _ = Algebra.discr ℚ b := by
        rw [Module.Basis.coe_reindex, Algebra.discr_reindex]
      _ = (d : ℚ) := hdiscr
  have hchange : Algebra.discr ℚ b' = P.det ^ (2 : ℕ) * Algebra.discr ℚ b0 := by
    rw [← b0.toMatrix_map_vecMul b']
    exact Algebra.discr_of_matrix_vecMul b0 P
  have hq : (d : ℚ) = (z : ℚ) ^ (2 : ℕ) * (discr K : ℚ) := by
    rw [← hb', hchange, ← hz, coe_discr]
    rfl
  have hzint : d = z ^ (2 : ℕ) * discr K := by
    exact_mod_cast hq
  refine ⟨z ^ (2 : ℕ), ?_⟩
  rw [mul_comm]
  exact hzint

end

end NumberField
