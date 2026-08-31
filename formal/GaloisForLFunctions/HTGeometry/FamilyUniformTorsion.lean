import GaloisForLFunctions.HTGeometry.FamilyGradedFibre

/-!
# One annihilator for all the torsion of a family

```text
torsionIdeal                          the elements a nonzero scalar polynomial pushes into the ideal
exists_uniform_torsion_annihilator    ** a single nonzero scalar polynomial annihilates all of it **
saturated_of_eval_ne_zero             ** so away from its roots the family is saturated **
```

The family ring is noetherian, so the torsion ideal is finitely generated; the product of the
annihilators of a finite generating set annihilates every torsion element, in every degree at once.
That uniformity is what a degeneration argument needs: the exceptional points of the base line are
the roots of one polynomial, not a set depending on the degree.

Saturation away from those roots is Bézout: the linear factor of the point is coprime to the
annihilator, so a combination of the two returns the element itself.
-/

namespace GaloisForLFunctions.HTGeometry
open MvPolynomial Polynomial

universe u
variable {K : Type u} [Field K] {N : ℕ}

/-- The elements of the family ring that a nonzero scalar polynomial pushes into an ideal. -/
noncomputable def torsionIdeal (A : Ideal (Polynomial (MvPolynomial (Fin N) K))) :
    Ideal (Polynomial (MvPolynomial (Fin N) K)) where
  carrier := {F | ∃ p : Polynomial K, p ≠ 0 ∧
    (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) p * F ∈ A}
  add_mem' := by
    rintro F G ⟨p, hp, hpF⟩ ⟨q, hq, hqG⟩
    refine ⟨p * q, mul_ne_zero hp hq, ?_⟩
    have hexp : (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) (p * q)
        * (F + G)
        = (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) q
            * ((algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) p * F)
          + (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) p
            * ((algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) q * G) := by
      rw [map_mul]
      ring
    rw [hexp]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpF) (Ideal.mul_mem_left _ _ hqG)
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  smul_mem' := by
    rintro c F ⟨p, hp, hpF⟩
    refine ⟨p, hp, ?_⟩
    have hexp : (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) p * (c • F)
        = c * ((algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) p * F) := by
      rw [smul_eq_mul]
      ring
    rw [hexp]
    exact Ideal.mul_mem_left _ _ hpF

/-- **A single scalar polynomial annihilates all the torsion.**  The family ring is noetherian, so
the ideal of torsion elements is finitely generated and the product of the annihilators of its
generators works for every element at once. -/
theorem exists_uniform_torsion_annihilator
    (A : Ideal (Polynomial (MvPolynomial (Fin N) K))) :
    ∃ q : Polynomial K, q ≠ 0 ∧ ∀ (F : Polynomial (MvPolynomial (Fin N) K)) (p : Polynomial K),
      p ≠ 0 → (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) p * F ∈ A →
        (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) q * F ∈ A := by
  classical
  obtain ⟨s, hs⟩ := (isNoetherian_def.mp inferInstance) (torsionIdeal A)
  have hmem : ∀ i : ↥(s : Finset (Polynomial (MvPolynomial (Fin N) K))),
      (i : Polynomial (MvPolynomial (Fin N) K)) ∈ torsionIdeal A := by
    intro i
    rw [← hs]
    exact Ideal.subset_span i.2
  choose p hp0 hpA using fun i => hmem i
  refine ⟨∏ i : ↥(s : Finset (Polynomial (MvPolynomial (Fin N) K))), p i, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => hp0 i
  · intro F r hr hrF
    have hFT : F ∈ torsionIdeal A := ⟨r, hr, hrF⟩
    rw [← hs, Submodule.mem_span_finset] at hFT
    obtain ⟨c, -, hc⟩ := hFT
    rw [← hc, Finset.mul_sum]
    refine Ideal.sum_mem _ fun i hi => ?_
    have hiA : (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K)))
        (∏ j : ↥(s : Finset (Polynomial (MvPolynomial (Fin N) K))), p j) * i ∈ A := by
      have hsplit : (∏ j : ↥(s : Finset (Polynomial (MvPolynomial (Fin N) K))), p j)
          = p ⟨i, hi⟩ * ∏ j ∈ Finset.univ.erase (⟨i, hi⟩ :
              ↥(s : Finset (Polynomial (MvPolynomial (Fin N) K)))), p j :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
      rw [hsplit, map_mul]
      have hassoc : (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K)))
            (p ⟨i, hi⟩)
          * (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K)))
            (∏ j ∈ Finset.univ.erase (⟨i, hi⟩ :
              ↥(s : Finset (Polynomial (MvPolynomial (Fin N) K)))), p j) * i
          = (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K)))
            (∏ j ∈ Finset.univ.erase (⟨i, hi⟩ :
              ↥(s : Finset (Polynomial (MvPolynomial (Fin N) K)))), p j)
            * ((algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K)))
              (p ⟨i, hi⟩) * i) := by ring
      rw [hassoc]
      exact Ideal.mul_mem_left _ _ (hpA ⟨i, hi⟩)
    have hcomm : (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K)))
        (∏ j : ↥(s : Finset (Polynomial (MvPolynomial (Fin N) K))), p j) * (c i • i)
        = c i * ((algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K)))
          (∏ j : ↥(s : Finset (Polynomial (MvPolynomial (Fin N) K))), p j) * i) := by
      rw [smul_eq_mul]
      ring
    rw [hcomm]
    exact Ideal.mul_mem_left _ _ hiA

/-- **Away from the roots of the annihilator the family is saturated.** -/
theorem saturated_of_eval_ne_zero {A : Ideal (Polynomial (MvPolynomial (Fin N) K))}
    {q : Polynomial K} (hq : ∀ (F : Polynomial (MvPolynomial (Fin N) K)) (p : Polynomial K),
      p ≠ 0 → (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) p * F ∈ A →
        (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) q * F ∈ A)
    {lam : K} (hlam : q.eval lam ≠ 0) (F : Polynomial (MvPolynomial (Fin N) K))
    (hF : (Polynomial.X - Polynomial.C (MvPolynomial.C lam)) * F ∈ A) : F ∈ A := by
  have hmapX : (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K)))
      (Polynomial.X - Polynomial.C lam)
      = Polynomial.X - Polynomial.C (MvPolynomial.C lam) := by
    show Polynomial.map (MvPolynomial.C : K →+* MvPolynomial (Fin N) K)
      (Polynomial.X - Polynomial.C lam) = _
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hne : (Polynomial.X - Polynomial.C lam : Polynomial K) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero lam
  have hqF := hq F (Polynomial.X - Polynomial.C lam) hne (by rw [hmapX]; exact hF)
  have hcop : IsCoprime (Polynomial.X - Polynomial.C lam : Polynomial K) q := by
    have hirr : Irreducible (Polynomial.X - Polynomial.C lam : Polynomial K) :=
      Polynomial.irreducible_X_sub_C lam
    rw [hirr.coprime_iff_not_dvd]
    intro hdvd
    exact hlam (Polynomial.dvd_iff_isRoot.mp hdvd)
  obtain ⟨a, b, hab⟩ := hcop
  have hone : F = (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) a
      * ((Polynomial.X - Polynomial.C (MvPolynomial.C lam)) * F)
      + (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) b
        * ((algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) q * F) := by
    have hsum := congrArg (algebraMap (Polynomial K)
      (Polynomial (MvPolynomial (Fin N) K))) hab
    rw [map_add, map_mul, map_mul, map_one, hmapX] at hsum
    calc F = 1 * F := (one_mul F).symm
      _ = ((algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) a
            * (Polynomial.X - Polynomial.C (MvPolynomial.C lam))
          + (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) b
            * (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K))) q) * F := by
            rw [hsum]
      _ = _ := by ring
  rw [hone]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hF) (Ideal.mul_mem_left _ _ hqF)

end GaloisForLFunctions.HTGeometry
