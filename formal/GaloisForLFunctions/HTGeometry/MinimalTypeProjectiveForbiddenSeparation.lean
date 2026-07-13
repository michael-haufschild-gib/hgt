import GaloisForLFunctions.HTGeometry.MinimalTypeProjectiveSeparation

namespace GaloisForLFunctions.HTGeometry

open Complex
open scoped BigOperators

noncomputable section

/-- Product imposing target-target projective separation and avoidance of a finite frozen affine
parameter packet. -/
def projectiveForbiddenSeparationProduct
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (C D : ℂ → ℂ) (shift : ι → ℂ) (forbidden : κ → ℂ) (z : ℂ) : ℂ :=
  projectiveSeparationProduct C D shift z *
    ∏ x : ι × κ,
      (D (z + shift x.1) + forbidden x.2 * C (z + shift x.1))

/-- The frozen-avoidance product is entire. -/
theorem projectiveForbiddenSeparationProduct_differentiable
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D)
    (shift : ι → ℂ) (forbidden : κ → ℂ) :
    Differentiable ℂ (projectiveForbiddenSeparationProduct C D shift forbidden) := by
  unfold projectiveForbiddenSeparationProduct
  apply Differentiable.mul (projectiveSeparationProduct_differentiable hC hD shift)
  rw [show (fun z => ∏ x : ι × κ,
      (D (z + shift x.1) + forbidden x.2 * C (z + shift x.1))) =
      ∏ x : ι × κ, (fun z =>
        D (z + shift x.1) + forbidden x.2 * C (z + shift x.1)) by
    funext z
    simp only [Finset.prod_apply]]
  exact Differentiable.finsetProd fun x (_hx : x ∈ (Finset.univ : Finset (ι × κ))) =>
    (hD.comp (differentiable_id.add_const (shift x.1))).add
      ((differentiable_const (c := forbidden x.2)).mul
        (hC.comp (differentiable_id.add_const (shift x.1))))

/-- Every finite forbidden affine packet leaves a nonzero entire separation product. -/
theorem projectiveForbiddenSeparationProduct_ne_zero
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (shift : ι → ℂ) (hshift : Function.Injective shift) (forbidden : κ → ℂ) :
    projectiveForbiddenSeparationProduct C D shift forbidden ≠ 0 := by
  unfold projectiveForbiddenSeparationProduct
  apply differentiable_mul_ne_zero
    (projectiveSeparationProduct_differentiable hCmin.1 hD shift)
  · rw [show (fun z => ∏ x : ι × κ,
        (D (z + shift x.1) + forbidden x.2 * C (z + shift x.1))) =
        ∏ x : ι × κ, (fun z =>
          D (z + shift x.1) + forbidden x.2 * C (z + shift x.1)) by
      funext z
      simp only [Finset.prod_apply]]
    exact Differentiable.finsetProd fun x (_hx : x ∈ (Finset.univ : Finset (ι × κ))) =>
      (hD.comp (differentiable_id.add_const (shift x.1))).add
        ((differentiable_const (c := forbidden x.2)).mul
          (hCmin.1.comp (differentiable_id.add_const (shift x.1))))
  · exact projectiveSeparationProduct_ne_zero
      hCmin hD hnoCommon hCp hCc shift hshift
  · apply differentiable_finset_prod_ne_zero Finset.univ
    · intro x hx
      exact (hD.comp (differentiable_id.add_const (shift x.1))).add
        ((differentiable_const (c := forbidden x.2)).mul
          (hCmin.1.comp (differentiable_id.add_const (shift x.1))))
    · intro x hx hzero
      have hDp : D p ≠ 0 := by
        intro h
        exact hnoCommon p ⟨hCp, h⟩
      have hvalue := congrFun hzero (p - shift x.1)
      apply hDp
      simpa [hCp] using hvalue

/-- A regular affine quotient avoids `t` whenever the corresponding homogeneous linear factor is
nonzero. -/
theorem quotient_ne_forbidden_of_linearFactor_ne_zero
    {C D : ℂ → ℂ} {z t : ℂ} (hC : C z ≠ 0)
    (hfactor : D z + t * C z ≠ 0) :
    -D z / C z ≠ t := by
  intro heq
  apply hfactor
  have hcross := (div_eq_iff hC).mp heq
  calc
    D z + t * C z = D z + -D z := by rw [← hcross]
    _ = 0 := add_neg_cancel _

/-- **Arbitrarily high frozen-safe projective row.** A finite injective target-shift packet admits
arbitrarily high regular rows whose affine parameters are pairwise distinct and avoid every member
of an arbitrary finite frozen packet. -/
theorem exists_upper_quotientSeparated_avoidingFinite_shift_row
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (shift : ι → ℂ) (hshift : Function.Injective shift)
    (forbidden : κ → ℂ) (H : ℝ) :
    ∃ z : ℂ, H < z.im ∧
      (∀ i, C (z + shift i) ≠ 0) ∧
      (∀ i j, i ≠ j →
        -D (z + shift i) / C (z + shift i) ≠
          -D (z + shift j) / C (z + shift j)) ∧
      (∀ i k, -D (z + shift i) / C (z + shift i) ≠ forbidden k) := by
  have hdiff := projectiveForbiddenSeparationProduct_differentiable
    hCmin.1 hD shift forbidden
  have hne := projectiveForbiddenSeparationProduct_ne_zero
    hCmin hD hnoCommon hCp hCc shift hshift forbidden
  obtain ⟨z, hzH, hz⟩ := exists_upper_ne_zero_of_differentiable_ne_zero hdiff hne H
  change projectiveSeparationProduct C D shift z *
    (∏ x : ι × κ,
      (D (z + shift x.1) + forbidden x.2 * C (z + shift x.1))) ≠ 0 at hz
  have hsep : projectiveSeparationProduct C D shift z ≠ 0 := by
    intro hzero
    exact hz (by rw [hzero, zero_mul])
  have hforbid : (∏ x : ι × κ,
      (D (z + shift x.1) + forbidden x.2 * C (z + shift x.1))) ≠ 0 := by
    intro hzero
    exact hz (by rw [hzero, mul_zero])
  change
    (∏ i, C (z + shift i)) *
      (∏ x : {x : ι × ι // x.1 ≠ x.2},
        projectiveShiftCollision C D (shift x.1.1) (shift x.1.2) z) ≠ 0 at hsep
  have hregularProduct : (∏ i, C (z + shift i)) ≠ 0 := by
    intro hzero
    exact hsep (by rw [hzero, zero_mul])
  have hcollisionProduct :
      (∏ x : {x : ι × ι // x.1 ≠ x.2},
        projectiveShiftCollision C D (shift x.1.1) (shift x.1.2) z) ≠ 0 := by
    intro hzero
    exact hsep (by rw [hzero, mul_zero])
  have hregular : ∀ i, C (z + shift i) ≠ 0 := fun i =>
    (Finset.prod_ne_zero_iff.mp hregularProduct) i (Finset.mem_univ i)
  refine ⟨z, hzH, hregular, ?_, ?_⟩
  · intro i j hij
    let x : {x : ι × ι // x.1 ≠ x.2} := ⟨(i, j), hij⟩
    exact quotient_ne_of_projectiveShiftCollision_ne_zero
      (hregular i) (hregular j)
      ((Finset.prod_ne_zero_iff.mp hcollisionProduct) x (Finset.mem_univ x))
  · intro i k
    apply quotient_ne_forbidden_of_linearFactor_ne_zero (hregular i)
    exact (Finset.prod_ne_zero_iff.mp hforbid) (i, k) (Finset.mem_univ (i, k))

end
end GaloisForLFunctions.HTGeometry
