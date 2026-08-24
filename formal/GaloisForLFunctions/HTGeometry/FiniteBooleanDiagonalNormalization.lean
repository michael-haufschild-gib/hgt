import GaloisForLFunctions.HTGeometry.BooleanSoninFullHistory

/-!
# Finite Boolean diagonal normalization

On the uniform Boolean cube of dimension `n`, equality of two independent packets has mass
`2⁻ⁿ`.  Multiplication by `2ⁿ` turns its expectation into the exact diagonal coupling.  The
identity is reporter-valued, is compatible with adjoining an ignored Boolean coordinate, and
forces every scalar normalization from its total mass.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Uniform point mass on the Boolean cube of dimension `n`. -/
def finiteBooleanCubeWeight (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

/-- Expectation of a reporter of two independent uniform Boolean packets. -/
def finiteBooleanIndependentExpectation (n : ℕ)
    (F : (Fin n → Bool) → (Fin n → Bool) → ℝ) : ℝ :=
  finiteBooleanCubeWeight n ^ 2 * ∑ u, ∑ v, F u v

/-- Diagonal coupling expectation of a two-packet reporter. -/
def finiteBooleanDiagonalExpectation (n : ℕ)
    (F : (Fin n → Bool) → (Fin n → Bool) → ℝ) : ℝ :=
  finiteBooleanCubeWeight n * ∑ u, F u u

/-- Equality-cylinder kernel on a finite Boolean cube. -/
def finiteBooleanDiagonalKernel {n : ℕ} (u v : Fin n → Bool) : ℝ :=
  if u = v then 1 else 0

/-- Summing an equality-cylinder reporter removes the redundant second packet. -/
theorem sum_finiteBooleanDiagonalKernel_mul
    (n : ℕ) (F : (Fin n → Bool) → (Fin n → Bool) → ℝ) :
    (∑ u, ∑ v, finiteBooleanDiagonalKernel u v * F u v) = ∑ u, F u u := by
  classical
  apply Finset.sum_congr rfl
  intro u hu
  simp [finiteBooleanDiagonalKernel]

/-- **Exact Boolean entropy normalization.**  `2ⁿ` times the independent equality-cylinder
expectation is the diagonal coupling for every reporter. -/
theorem finiteBooleanDiagonalExpectation_eq_normalized
    (n : ℕ) (F : (Fin n → Bool) → (Fin n → Bool) → ℝ) :
    (2 : ℝ) ^ n * finiteBooleanIndependentExpectation n
      (fun u v => finiteBooleanDiagonalKernel u v * F u v) =
        finiteBooleanDiagonalExpectation n F := by
  rw [finiteBooleanIndependentExpectation, finiteBooleanDiagonalExpectation,
    sum_finiteBooleanDiagonalKernel_mul, finiteBooleanCubeWeight]
  have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- Equality of two independent uniform `n`-bit packets has mass exactly `2⁻ⁿ`. -/
theorem finiteBooleanDiagonalMass (n : ℕ) :
    finiteBooleanIndependentExpectation n finiteBooleanDiagonalKernel =
      ((2 : ℝ) ^ n)⁻¹ := by
  have hnorm := finiteBooleanDiagonalExpectation_eq_normalized n (fun _ _ => 1)
  simp only [mul_one] at hnorm
  have hdiag : finiteBooleanDiagonalExpectation n (fun _ _ => 1) = 1 := by
    rw [finiteBooleanDiagonalExpectation, finiteBooleanCubeWeight]
    simp
  rw [hdiag] at hnorm
  have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    finiteBooleanIndependentExpectation n finiteBooleanDiagonalKernel =
        ((2 : ℝ) ^ n)⁻¹ *
          ((2 : ℝ) ^ n * finiteBooleanIndependentExpectation n finiteBooleanDiagonalKernel) := by
            field_simp
    _ = ((2 : ℝ) ^ n)⁻¹ := by rw [hnorm]; ring

/-- Adjoining one ignored Boolean coordinate does not change the normalized diagonal reporter. -/
theorem finiteBooleanDiagonalExpectation_lift_succ
    (n : ℕ) (F : (Fin n → Bool) → (Fin n → Bool) → ℝ) :
    finiteBooleanDiagonalExpectation (n + 1)
      (fun u v => F (fun i => u i.castSucc) (fun i => v i.castSucc)) =
      finiteBooleanDiagonalExpectation n F := by
  rw [finiteBooleanDiagonalExpectation, finiteBooleanDiagonalExpectation,
    finiteBooleanCubeWeight, finiteBooleanCubeWeight]
  rw [← Fintype.sum_equiv (HTGeometry.snocBoolEquiv n)
    (fun p => F p.1 p.1)
    (fun u => F (fun i => u i.castSucc) (fun i => u i.castSucc))]
  · rw [Fintype.sum_prod_type_right]
    simp only [Fintype.sum_bool]
    have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    ring
  · intro p
    simp [HTGeometry.snocBoolEquiv]

/-- **Scalar normalization is forced by total mass.**  Any scalarized diagonal with finite mass
limit `M` has normalized coefficient `cₓ / 2ⁿˣ → M`. -/
theorem finiteBoolean_scalar_normalization_forced
    {α : Type*} {l : Filter α} (n : α → ℕ) (c : α → ℝ) (M : ℝ)
    (h : Tendsto (fun x => c x *
      finiteBooleanIndependentExpectation (n x) finiteBooleanDiagonalKernel) l (nhds M)) :
    Tendsto (fun x => c x / (2 : ℝ) ^ n x) l (nhds M) := by
  refine h.congr' (Eventually.of_forall fun x => ?_)
  rw [finiteBooleanDiagonalMass]
  simp [div_eq_mul_inv]

end

end GaloisForLFunctions.HTGeometry
