import GaloisForLFunctions.HTGeometry.HorizonConormalJacobianKernel

/-!
# Proportional conormals from a one-dimensional kernel

Two low tangent pairs whose conormal vectors lie in the same one-dimensional kernel are
proportional:

```text
exists_smul_of_finrank_ker_eq_one     a nonzero vector spans a one-dimensional kernel
tangent_smul_of_conormal_smul
    ** proportional conormal vectors ⟹ proportional tangent pairs **
```

Together with `horizonObservationJacobian_mulVec_conormal` and corank one of the reduced
observation Jacobian, this is the step that lets two singular points of the reduced fibre be
compared: their conormal vectors both lie in the kernel of the Jacobian, which is a line.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Matrix

set_option maxHeartbeats 2000000

/-- In a one-dimensional kernel, a nonzero vector spans. -/
theorem exists_smul_of_finrank_ker_eq_one {E ι : Type*} [Field E] [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι E) (hker : Module.finrank E (LinearMap.ker P.mulVecLin) = 1)
    {v w : ι → E} (hv : P.mulVec v = 0) (hw : P.mulVec w = 0) (hvne : v ≠ 0) :
    ∃ c : E, w = c • v := by
  have hvmem : v ∈ LinearMap.ker P.mulVecLin := by
    simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hv
  have hwmem : w ∈ LinearMap.ker P.mulVecLin := by
    simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hw
  have hvne' : (⟨v, hvmem⟩ : LinearMap.ker P.mulVecLin) ≠ 0 := by
    intro h
    exact hvne (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hvne').mp hker ⟨w, hwmem⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

/-- Proportional conormal vectors come from proportional tangent pairs. -/
theorem tangent_smul_of_conormal_smul {E : Type*} [Field E] {m n : ℕ} {U V U' V' : E[X]} {c : E}
    (hU : U.degree < (m : ℕ)) (hV : V.degree < (n : ℕ))
    (hU' : U'.degree < (m : ℕ)) (hV' : V'.degree < (n : ℕ))
    (h : horizonConormalVector U' V' m n = c • horizonConormalVector U V m n) :
    U' = Polynomial.C c * U ∧ V' = Polynomial.C c * V := by
  classical
  constructor
  · refine Polynomial.ext fun i => ?_
    rw [Polynomial.coeff_C_mul]
    by_cases hi : i < m
    · have hidx : (⟨m - 1 - i, by omega⟩ : Fin m) = ⟨m - 1 - i, by omega⟩ := rfl
      have := congrFun h (Sum.inl (⟨m - 1 - i, by omega⟩ : Fin m))
      show U'.coeff i = c * U.coeff i
      simpa [horizonConormalVector, show m - 1 - (m - 1 - i) = i by omega] using this
    · rw [Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hU' (by exact_mod_cast (by omega : m ≤ i))),
        Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hU (by exact_mod_cast (by omega : m ≤ i))), mul_zero]
  · refine Polynomial.ext fun i => ?_
    rw [Polynomial.coeff_C_mul]
    by_cases hi : i < n
    · have := congrFun h (Sum.inr (⟨n - 1 - i, by omega⟩ : Fin n))
      show V'.coeff i = c * V.coeff i
      have h2 : -V'.coeff i = c * -V.coeff i := by
        simpa [horizonConormalVector, show n - 1 - (n - 1 - i) = i by omega] using this
      linear_combination -h2
    · rw [Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hV' (by exact_mod_cast (by omega : n ≤ i))),
        Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hV (by exact_mod_cast (by omega : n ≤ i))), mul_zero]

end GaloisForLFunctions.HTGeometry
