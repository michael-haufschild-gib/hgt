import GaloisForLFunctions.HTGeometry.FibreSemicontinuity

/-!
# Points where the module has no torsion have the generic fibre dimension

```text
not_dvd_of_smul_injective          a point with no torsion contributes no cyclic summand
finrank_fibre_eq_of_smul_injective ** two such points have the same fibre dimension **
```

If the linear factor of a point divides one of the elementary divisors, the corresponding cyclic
summand contains a nonzero element killed by that factor, so the module has torsion there.  With no
torsion at either point, the fibre dimension of `finrank_fibre_eq` reduces to the free rank at both,
and the two agree.

This is the form in which flatness of a one-parameter family is used: torsion-freeness at two points
of the base line makes the fibres over them equidimensional.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise
open Module Polynomial

variable {K : Type*} [Field K]

/-- A point where the module has no torsion contributes no torsion summand. -/
theorem not_dvd_of_smul_injective {V : Type*} [AddCommGroup V] [Module K[X] V] [Module K V]
    [IsScalarTower K K[X] V] {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → K[X]}
    {e : ι → ℕ}
    (eqv : V ≃ₗ[K[X]] (Fin n →₀ K[X]) × (∀ i, K[X] ⧸ (Ideal.span {p i ^ e i})))
    {lam : K} (hlam : ∀ v : V, (X - C lam : K[X]) • v = 0 → v = 0) (hp : ∀ i, p i ≠ 0) (i : ι) :
    ¬ ((X - C lam : K[X]) ∣ p i ^ e i) := by
  intro hdvd
  obtain ⟨q, hq⟩ := hdvd
  have hpow : p i ^ e i ≠ 0 := pow_ne_zero _ (hp i)
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, mul_zero] at hq
    exact hpow hq
  -- `q` is a nonzero element of the cyclic summand killed by the linear factor
  have hqmem : (Ideal.Quotient.mk (Ideal.span {p i ^ e i}) q) ≠ 0 := by
    intro h
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    have hcancel : (1 : K[X]) = (X - C lam) * c := by
      have hqq : q * 1 = q * ((X - C lam) * c) := by
        rw [mul_one]
        nth_rewrite 1 [hc]
        rw [hq]
        ring
      exact mul_left_cancel₀ hq0 hqq
    have hdeg := congrArg Polynomial.natDegree hcancel
    rw [Polynomial.natDegree_one, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero lam) ?_,
      Polynomial.natDegree_X_sub_C] at hdeg
    · omega
    · intro hc0
      rw [hc0, mul_zero] at hcancel
      exact one_ne_zero hcancel
  set w : ∀ j, K[X] ⧸ (Ideal.span {p j ^ e j}) :=
    Pi.single (M := fun j => K[X] ⧸ (Ideal.span {p j ^ e j})) i
      (Ideal.Quotient.mk (Ideal.span {p i ^ e i}) q) with hw
  set v : V := eqv.symm (0, w) with hv
  have hkill : (X - C lam : K[X]) • v = 0 := by
    rw [hv, ← map_smul]
    have hsm : (X - C lam : K[X]) • ((0 : Fin n →₀ K[X]), w) = 0 := by
      refine Prod.ext (by simp) ?_
      funext j
      simp only [Prod.smul_snd, Pi.smul_apply, Prod.snd_zero, Pi.zero_apply]
      by_cases hj : j = i
      · subst hj
        rw [hw, Pi.single_eq_same]
        have hmk : (X - C lam : K[X]) • (Ideal.Quotient.mk (Ideal.span {p j ^ e j}) q)
            = Ideal.Quotient.mk (Ideal.span {p j ^ e j}) ((X - C lam) * q) := rfl
        rw [hmk, ← hq, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_span_singleton_self _
      · rw [hw, Pi.single_eq_of_ne hj, smul_zero]
    rw [hsm, map_zero]
  have hvne : v ≠ 0 := by
    rw [hv]
    intro h
    have h0 := congrArg eqv h
    rw [LinearEquiv.apply_symm_apply, map_zero] at h0
    have hcomp := congrArg (fun z => (Prod.snd z) i) h0
    simp only [hw, Pi.single_eq_same, Prod.snd_zero, Pi.zero_apply] at hcomp
    exact hqmem hcomp
  exact hvne (hlam v hkill)

/-- **Two points with no torsion have the same fibre dimension.** -/
theorem finrank_fibre_eq_of_smul_injective {V : Type*} [AddCommGroup V] [Module K[X] V]
    [Module K V] [IsScalarTower K K[X] V] [Module.Finite K[X] V] {lam mu : K}
    (hlam : ∀ v : V, (X - C lam : K[X]) • v = 0 → v = 0)
    (hmu : ∀ v : V, (X - C mu : K[X]) • v = 0 → v = 0) :
    finrank K (V ⧸ (Ideal.span {(X - C lam : K[X])} • (⊤ : Submodule K[X] V)))
      = finrank K (V ⧸ (Ideal.span {(X - C mu : K[X])} • (⊤ : Submodule K[X] V))) := by
  classical
  obtain ⟨n, ι, hι, p, hp, e, ⟨eqv0⟩⟩ := Module.equiv_free_prod_directSum K[X] V
  haveI := hι
  haveI : DecidableEq ι := Classical.decEq ι
  have eqv : V ≃ₗ[K[X]] (Fin n →₀ K[X]) × (∀ i, K[X] ⧸ (Ideal.span {p i ^ e i})) :=
    eqv0.trans ((LinearEquiv.refl K[X] (Fin n →₀ K[X])).prodCongr
      (DirectSum.linearEquivFunOnFintype K[X] ι (fun i => K[X] ⧸ (Ideal.span {p i ^ e i}))))
  have hpne : ∀ i, p i ≠ 0 := fun i => (hp i).ne_zero
  rw [finrank_fibre_eq eqv lam, finrank_fibre_eq eqv mu]
  congr 1
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
  · intro i _
    rw [if_neg (not_dvd_of_smul_injective eqv hmu hpne i)]
  · intro i _
    rw [if_neg (not_dvd_of_smul_injective eqv hlam hpne i)]

end GaloisForLFunctions.HTGeometry
