import GaloisForLFunctions.HTGeometry.FamilyNonzeroFibres
import GaloisForLFunctions.HTGeometry.DegreePartMonotone

/-!
# The weight rescaling is a graded automorphism

```text
coeff_familyWeightScale             the rescaling multiplies each coefficient by a nonzero scalar
weightScaleEquiv                    ** hence it is an automorphism of the polynomial ring **
homogeneousComponent_familyWeightScale
                                    ** and it commutes with taking homogeneous components **
isHomogIdeal_map_weightScaleEquiv   so it carries homogeneous ideals to homogeneous ideals
finrank_quotDegreePart_map_weightScaleEquiv
                                    ** and preserves the Hilbert function **
```

The rescaling `x i ↦ lam ^ (w i) * x i` acts on the monomial basis diagonally with nonzero entries,
so on each graded piece it is a diagonal linear isomorphism.  That is all that is needed: the fibre
of the flat family over a nonzero point is the *rescaled* ideal, not the ideal itself, and this file
is what says the rescaling is invisible to the Hilbert function — so the fibre bound of the family
may be read as a statement about the original ideal, with the linear form deformed.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Module

universe u
variable {σ : Type*} {K : Type u} [Field K]

theorem familyWeightScale_X (w : σ → ℤ) (lam : K) (i : σ) :
    familyWeightScale (K := K) w lam (X i) = MvPolynomial.C (lam ^ (w i)) * X i := by
  rw [familyWeightScale, MvPolynomial.aeval_X]

/-- **The rescaling multiplies each coefficient by a nonzero scalar.** -/
theorem coeff_familyWeightScale (w : σ → ℤ) {lam : K} (hlam : lam ≠ 0)
    (f : MvPolynomial σ K) (α : σ →₀ ℕ) :
    MvPolynomial.coeff α (familyWeightScale (K := K) w lam f)
      = lam ^ (Finsupp.weight w α) * MvPolynomial.coeff α f := by
  classical
  rw [familyWeightScale_eq_sum]
  simp only [familyWeightScale_monomial w hlam, MvPolynomial.C_mul_monomial]
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' f.support α]
  by_cases hα : α ∈ f.support
  · rw [if_pos hα]
  · rw [if_neg hα, MvPolynomial.notMem_support_iff.mp hα, mul_zero]

theorem familyWeightScale_comp (w : σ → ℤ) {lam : K} (hlam : lam ≠ 0) :
    (familyWeightScale (K := K) w lam).comp (familyWeightScale (K := K) w lam⁻¹)
      = AlgHom.id K (MvPolynomial σ K) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, familyWeightScale_X, map_mul, familyWeightScale_X,
    MvPolynomial.algHom_C, AlgHom.id_apply]
  simp only [MvPolynomial.algebraMap_eq]
  rw [← map_mul, ← mul_zpow, inv_mul_cancel₀ hlam, one_zpow, map_one, one_mul]

/-- **The rescaling is an automorphism of the polynomial ring.** -/
noncomputable def weightScaleEquiv (w : σ → ℤ) {lam : K} (hlam : lam ≠ 0) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom (familyWeightScale w lam) (familyWeightScale w lam⁻¹)
    (familyWeightScale_comp w hlam)
    (by
      have h := familyWeightScale_comp (K := K) w (inv_ne_zero hlam)
      rwa [inv_inv] at h)

@[simp]
theorem weightScaleEquiv_apply (w : σ → ℤ) {lam : K} (hlam : lam ≠ 0) (f : MvPolynomial σ K) :
    weightScaleEquiv w hlam f = familyWeightScale w lam f := rfl

/-- **The rescaling commutes with taking homogeneous components.** -/
theorem homogeneousComponent_familyWeightScale (w : σ → ℤ) {lam : K} (hlam : lam ≠ 0) (e : ℕ)
    (f : MvPolynomial σ K) :
    MvPolynomial.homogeneousComponent e (familyWeightScale (K := K) w lam f)
      = familyWeightScale (K := K) w lam (MvPolynomial.homogeneousComponent e f) := by
  classical
  ext α
  rw [MvPolynomial.coeff_homogeneousComponent, coeff_familyWeightScale w hlam,
    coeff_familyWeightScale w hlam, MvPolynomial.coeff_homogeneousComponent]
  by_cases hα : Finsupp.degree α = e
  · rw [if_pos hα, if_pos hα]
  · rw [if_neg hα, if_neg hα, mul_zero]

theorem isHomogeneous_familyWeightScale (w : σ → ℤ) {lam : K} (hlam : lam ≠ 0) {e : ℕ}
    {f : MvPolynomial σ K} (hf : f.IsHomogeneous e) :
    (familyWeightScale (K := K) w lam f).IsHomogeneous e := by
  intro α hα
  refine hf ?_
  intro h0
  rw [coeff_familyWeightScale w hlam, h0, mul_zero] at hα
  exact hα rfl

/-- The rescaling on one graded piece. -/
noncomputable def weightScaleDegreeMap (w : σ → ℤ) {lam : K} (hlam : lam ≠ 0) (e : ℕ) :
    homogeneousSubmodule σ K e →ₗ[K] homogeneousSubmodule σ K e where
  toFun x := ⟨familyWeightScale w lam (x : MvPolynomial σ K),
    isHomogeneous_familyWeightScale w hlam (MvPolynomial.mem_homogeneousSubmodule e _ |>.mp x.2)⟩
  map_add' x y := by
    refine Subtype.ext ?_
    show familyWeightScale w lam ((x : MvPolynomial σ K) + y) = _
    rw [map_add]
    rfl
  map_smul' c x := by
    refine Subtype.ext ?_
    show familyWeightScale w lam (c • (x : MvPolynomial σ K)) = _
    rw [map_smul]
    rfl

@[simp]
theorem weightScaleDegreeMap_coe (w : σ → ℤ) {lam : K} (hlam : lam ≠ 0) (e : ℕ)
    (x : homogeneousSubmodule σ K e) :
    ((weightScaleDegreeMap w hlam e x : homogeneousSubmodule σ K e) : MvPolynomial σ K)
      = familyWeightScale w lam (x : MvPolynomial σ K) := rfl

/-- **The rescaling is an isomorphism of each graded piece.** -/
noncomputable def weightScaleDegreeEquiv (w : σ → ℤ) {lam : K} (hlam : lam ≠ 0) (e : ℕ) :
    homogeneousSubmodule σ K e ≃ₗ[K] homogeneousSubmodule σ K e :=
  LinearEquiv.ofLinear (weightScaleDegreeMap w hlam e)
    (weightScaleDegreeMap w (inv_ne_zero hlam) e)
    (by
      refine LinearMap.ext fun x => Subtype.ext ?_
      rw [LinearMap.comp_apply, weightScaleDegreeMap_coe, weightScaleDegreeMap_coe]
      have := congrArg (fun g : MvPolynomial σ K →ₐ[K] MvPolynomial σ K => g (x : MvPolynomial σ K))
        (familyWeightScale_comp (K := K) w hlam)
      simpa using this)
    (by
      refine LinearMap.ext fun x => Subtype.ext ?_
      rw [LinearMap.comp_apply, weightScaleDegreeMap_coe, weightScaleDegreeMap_coe]
      have h := familyWeightScale_comp (K := K) w (inv_ne_zero hlam)
      rw [inv_inv] at h
      have := congrArg (fun g : MvPolynomial σ K →ₐ[K] MvPolynomial σ K => g (x : MvPolynomial σ K)) h
      simpa using this)

@[simp]
theorem weightScaleDegreeEquiv_coe (w : σ → ℤ) {lam : K} (hlam : lam ≠ 0) (e : ℕ)
    (x : homogeneousSubmodule σ K e) :
    ((weightScaleDegreeEquiv w hlam e x : homogeneousSubmodule σ K e) : MvPolynomial σ K)
      = familyWeightScale w lam (x : MvPolynomial σ K) := rfl

theorem mem_map_weightScaleEquiv_iff (w : σ → ℤ) {lam : K} (hlam : lam ≠ 0)
    (I : Ideal (MvPolynomial σ K)) (x : MvPolynomial σ K) :
    familyWeightScale w lam x ∈ Ideal.map (weightScaleEquiv w hlam : MvPolynomial σ K →+* MvPolynomial σ K) I
      ↔ x ∈ I := by
  constructor
  · intro h
    have h2 := Ideal.mem_map_of_mem
      ((weightScaleEquiv w hlam).symm : MvPolynomial σ K →+* MvPolynomial σ K) h
    rw [Ideal.map_map] at h2
    have hid : ((weightScaleEquiv w hlam).symm : MvPolynomial σ K →+* MvPolynomial σ K).comp
        ((weightScaleEquiv w hlam) : MvPolynomial σ K →+* MvPolynomial σ K)
        = RingHom.id _ := by
      refine RingHom.ext fun y => ?_
      exact (weightScaleEquiv w hlam).symm_apply_apply y
    rw [hid, Ideal.map_id] at h2
    have hxx : ((weightScaleEquiv w hlam).symm : MvPolynomial σ K →+* MvPolynomial σ K)
        (familyWeightScale w lam x) = x := (weightScaleEquiv w hlam).symm_apply_apply x
    rwa [hxx] at h2
  · intro h
    exact Ideal.mem_map_of_mem _ h

/-- **The rescaling carries homogeneous ideals to homogeneous ideals.** -/
theorem isHomogIdeal_map_weightScaleEquiv (w : σ → ℤ) {lam : K} (hlam : lam ≠ 0)
    {I : Ideal (MvPolynomial σ K)} (hI : IsHomogIdeal I) :
    IsHomogIdeal (Ideal.map (weightScaleEquiv w hlam : MvPolynomial σ K →+* MvPolynomial σ K) I) := by
  intro e f hf
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
    (weightScaleEquiv w hlam).surjective).mp hf
  show MvPolynomial.homogeneousComponent e (familyWeightScale w lam y) ∈ _
  rw [homogeneousComponent_familyWeightScale w hlam]
  exact (mem_map_weightScaleEquiv_iff w hlam I _).mpr (hI e y hy)

theorem map_degreePart_weightScaleEquiv (w : σ → ℤ) {lam : K} (hlam : lam ≠ 0)
    (I : Ideal (MvPolynomial σ K)) (e : ℕ) :
    Submodule.map (weightScaleDegreeEquiv w hlam e : homogeneousSubmodule σ K e →ₗ[K] _)
        (degreePart (I.restrictScalars K) e)
      = degreePart ((Ideal.map (weightScaleEquiv w hlam : MvPolynomial σ K →+* MvPolynomial σ K)
          I).restrictScalars K) e := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show ((weightScaleDegreeEquiv w hlam e y : homogeneousSubmodule σ K e) : MvPolynomial σ K) ∈ _
    rw [weightScaleDegreeEquiv_coe]
    exact (mem_map_weightScaleEquiv_iff w hlam I _).mpr hy
  · intro hx
    refine ⟨(weightScaleDegreeEquiv w hlam e).symm x, ?_, by simp⟩
    have hxe : ((weightScaleDegreeEquiv w hlam e)
        ((weightScaleDegreeEquiv w hlam e).symm x) : homogeneousSubmodule σ K e) = x := by
      simp
    have hmem : familyWeightScale w lam
        (((weightScaleDegreeEquiv w hlam e).symm x : homogeneousSubmodule σ K e)
          : MvPolynomial σ K)
        ∈ Ideal.map (weightScaleEquiv w hlam : MvPolynomial σ K →+* MvPolynomial σ K) I := by
      rw [← weightScaleDegreeEquiv_coe w hlam e, hxe]
      exact hx
    exact (mem_map_weightScaleEquiv_iff w hlam I _).mp hmem

/-- **The rescaling preserves the Hilbert function.** -/
theorem finrank_quotDegreePart_map_weightScaleEquiv (w : σ → ℤ) {lam : K} (hlam : lam ≠ 0)
    (I : Ideal (MvPolynomial σ K)) (e : ℕ) :
    finrank K (quotDegreePart ((Ideal.map (weightScaleEquiv w hlam : MvPolynomial σ K →+* MvPolynomial σ K)
        I).restrictScalars K) e)
      = finrank K (quotDegreePart (I.restrictScalars K) e) :=
  (Submodule.Quotient.equiv _ _ (weightScaleDegreeEquiv w hlam e)
    (map_degreePart_weightScaleEquiv w hlam I e)).finrank_eq.symm

end GaloisForLFunctions.HTGeometry
