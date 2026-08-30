import GaloisForLFunctions.HTGeometry.RittScalingSliceTransport
import GaloisForLFunctions.HTGeometry.HyperexponentialPrimitive

/-!
# The eigen-inhomogeneous slice, and both descents read off an adjunction

The second descent of Ritt's `n = 2` case has a different shape from the first: after eliminating
the generator `s = τ / d τ` one is left with

`ν · Φ(a) = a + β`

for `a` in a simple transcendental extension of the coefficient field, with the substitution acting
on the generator by a pure scaling.  The same coprime slicing applies — the denominator is again an
eigenvector with scalar `q ^ deg Q` — but the relation is now read off at the coefficient of
`X ^ deg Q` rather than one above it, because the inhomogeneity is a constant instead of a multiple
of the generator.

Together with the coprime monic representation of a member of a simple transcendental extension,
both descents become statements about membership in `E⟮t⟯`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

/-- **The eigen-inhomogeneous coprime descent.** -/
theorem exists_eigen_shift_solution_of_scaling_cross (Φ : K →+* K) {q ν β : K} (hq : q ≠ 0)
    {P Q : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hcross : C ν * twistComp Φ (C q * X) P * Q
      = twistComp Φ (C q * X) Q * (P + C β * Q)) :
    ∃ a : K, ν * Φ a = a + β := by
  classical
  have hTdeg : (C q * X : K[X]).natDegree = 1 := natDegree_scaleSubst hq
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  set e : ℕ := Q.natDegree with he
  have hcopQ : IsCoprime Q (P + C β * Q) := by
    have h := hcop.symm.add_mul_left_right (C β)
    have heq : P + Q * C β = P + C β * Q := by ring
    rwa [heq] at h
  have hdvd : Q ∣ twistComp Φ (C q * X) Q := by
    refine hcopQ.dvd_of_dvd_mul_right ?_
    exact ⟨C ν * twistComp Φ (C q * X) P, by rw [← hcross]; ring⟩
  obtain ⟨d, hd0, hd⟩ :=
    eq_C_mul_of_dvd_of_natDegree_eq (twistComp_ne_zero Φ hTdeg hQ0) hdvd
      (natDegree_twistComp Φ hTdeg Q)
  have hde : d = q ^ e := by
    have hj := coeff_eigen_of_twistComp_scale Φ hd e
    rw [hQ.coeff_natDegree, map_one, one_mul, mul_one] at hj
    exact hj.symm
  have hnum : C ν * twistComp Φ (C q * X) P = C (q ^ e) * (P + C β * Q) := by
    refine mul_right_cancel₀ hQ0 ?_
    rw [hcross, hd, hde]
    ring
  have hcoeff := congrArg (fun p : K[X] => p.coeff e) hnum
  simp only [coeff_C_mul, coeff_twistComp_scale, coeff_add] at hcoeff
  rw [hQ.coeff_natDegree] at hcoeff
  refine ⟨P.coeff e, ?_⟩
  have hqe : (q : K) ^ e ≠ 0 := pow_ne_zero _ hq
  refine mul_left_cancel₀ hqe ?_
  linear_combination hcoeff

section Ambient

variable {E L : Type*} [Field E] [Field L] [Algebra E L]

/-- The inhomogeneous descent, for a member of a simple transcendental extension. -/
theorem exists_shift_solution_of_mem_adjoin (σ : L →+* L) (φ : E →+* E)
    (hcomp : ∀ a : E, σ (algebraMap E L a) = algebraMap E L (φ a))
    {t : L} (ht : Transcendental E t) {μ β : E} (hμ : μ ≠ 0)
    (hσt : σ t = algebraMap E L μ * t)
    {W : L} (hW : W ∈ IntermediateField.adjoin E ({t} : Set L))
    (hrel : σ W = W + algebraMap E L β * t) :
    ∃ a : E, φ a * μ = a + β := by
  obtain ⟨A, B, hB, hcop, hAB⟩ := exists_coprime_monic_repr ht hW
  have hinj : Function.Injective (aeval t : E[X] →ₐ[E] L) :=
    transcendental_iff_injective.mp ht
  have hBt : aeval t B ≠ 0 := fun h => hB.ne_zero (hinj (by simpa using h))
  have hWeq : W = aeval t A / aeval t B := by
    field_simp
    exact hAB
  rw [hWeq] at hrel
  exact exists_shift_solution_of_transcendental σ φ hcomp ht hμ hσt hB hcop hrel

/-- The eigen-inhomogeneous descent, for a member of a simple transcendental extension. -/
theorem exists_eigen_shift_solution_of_mem_adjoin (σ : L →+* L) (φ : E →+* E)
    (hcomp : ∀ a : E, σ (algebraMap E L a) = algebraMap E L (φ a))
    {t : L} (ht : Transcendental E t) {μ ν β : E} (hμ : μ ≠ 0)
    (hσt : σ t = algebraMap E L μ * t)
    {W : L} (hW : W ∈ IntermediateField.adjoin E ({t} : Set L))
    (hrel : algebraMap E L ν * σ W = W + algebraMap E L β) :
    ∃ a : E, ν * φ a = a + β := by
  obtain ⟨A, B, hB, hcop, hAB⟩ := exists_coprime_monic_repr ht hW
  have hinj : Function.Injective (aeval t : E[X] →ₐ[E] L) :=
    transcendental_iff_injective.mp ht
  have hBt : aeval t B ≠ 0 := fun h => hB.ne_zero (hinj (by simpa using h))
  have htw : aeval t (twistComp φ (C μ * X) B) ≠ 0 := fun h =>
    (twistComp_ne_zero φ (natDegree_scaleSubst hμ) hB.ne_zero) (hinj (by simpa using h))
  have hWeq : W = aeval t A / aeval t B := by
    field_simp
    exact hAB
  refine exists_eigen_shift_solution_of_scaling_cross φ hμ hB hcop (hinj ?_)
  have hσA := aeval_twistComp_scale σ φ hcomp hσt A
  have hσB := aeval_twistComp_scale σ φ hcomp hσt B
  rw [hWeq, map_div₀, ← hσA, ← hσB] at hrel
  rw [map_mul, map_mul, map_mul, map_add, map_mul, aeval_C, aeval_C]
  rw [div_add' _ _ _ hBt, ← mul_div_assoc, div_eq_div_iff htw hBt] at hrel
  linear_combination hrel

end Ambient

end GaloisForLFunctions.HTGeometry
