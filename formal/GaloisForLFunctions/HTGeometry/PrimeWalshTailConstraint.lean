import GaloisForLFunctions.HTGeometry.PrimeOrientationTailCluster

/-!
# Prime-Walsh reconstruction on finite orientation constraints

Walsh characters supply every nonlinear observation of a finite Boolean orientation chamber.
This file proves Fourier-Walsh inversion directly, then shows that restriction of the complete
Walsh palette to any finite constraint is onto its full function space.  Its exact rank is therefore
the number of allowed patterns, not merely the dimension of their coordinate span.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The signed Walsh character indexed by a finite coordinate subset. -/
def orientationWalshCharacter {I : Type*} (B : Finset I) (x : I → Bool) : ℂ :=
  ∏ i ∈ B, primeDirichletSign (x i)

/-- The Walsh character kernel factors into one-coordinate kernels. -/
theorem sum_orientationWalshCharacter_mul {I : Type*} [Fintype I]
    (x y : I → Bool) :
    (∑ B : Finset I, orientationWalshCharacter B x * orientationWalshCharacter B y) =
      ∏ i : I, (1 + primeDirichletSign (x i) * primeDirichletSign (y i)) := by
  classical
  calc
    _ = ∑ B ∈ Finset.univ.powerset,
        ∏ i ∈ B, (primeDirichletSign (x i) * primeDirichletSign (y i)) := by
      rw [show (Finset.univ : Finset (Finset I)) = Finset.univ.powerset by ext B; simp]
      simp only [orientationWalshCharacter, Finset.prod_mul_distrib]
    _ = ∏ i ∈ (Finset.univ : Finset I),
        ((primeDirichletSign (x i) * primeDirichletSign (y i)) + 1) := by
      rw [Finset.prod_add]
      simp
    _ = _ := by simp [add_comm]

/-- Orthogonality of the complete finite Walsh character family. -/
theorem sum_orientationWalshCharacter_mul_eq {I : Type*} [Fintype I]
    (x y : I → Bool) :
    (∑ B : Finset I, orientationWalshCharacter B x * orientationWalshCharacter B y) =
      if x = y then (2 : ℂ) ^ Fintype.card I else 0 := by
  rw [sum_orientationWalshCharacter_mul]
  by_cases hxy : x = y
  · subst y
    rw [if_pos rfl]
    have hfactor : ∀ i, (1 + primeDirichletSign (x i) * primeDirichletSign (x i)) =
        (2 : ℂ) := by
      intro i
      cases x i <;> norm_num [primeDirichletSign]
    simp_rw [hfactor]
    simp
  · have hne : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
    obtain ⟨i, hi⟩ := hne
    rw [if_neg hxy]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hxi : x i <;> cases hyi : y i <;> simp_all [primeDirichletSign]

/-- The inverse Walsh-transform coefficient of a function on a finite orientation cube. -/
def inverseWalshCoefficient {I : Type*} [Fintype I]
    (f : (I → Bool) → ℂ) (B : Finset I) : ℂ :=
  by
    classical
    letI : Fintype (I → Bool) := Fintype.ofFinite _
    exact ((2 : ℂ) ^ Fintype.card I)⁻¹ *
      ∑ x : I → Bool, f x * orientationWalshCharacter B x

/-- Every complex function on a finite Boolean cube is its finite Walsh expansion. -/
theorem orientationWalsh_inversion {I : Type*} [Fintype I]
    (f : (I → Bool) → ℂ) (y : I → Bool) :
    ∑ B : Finset I, inverseWalshCoefficient f B * orientationWalshCharacter B y = f y := by
  classical
  letI : Fintype (I → Bool) := Fintype.ofFinite _
  rw [show (∑ B : Finset I, inverseWalshCoefficient f B * orientationWalshCharacter B y) =
      ((2 : ℂ) ^ Fintype.card I)⁻¹ *
        ∑ x : I → Bool, f x *
          (∑ B : Finset I, orientationWalshCharacter B x * orientationWalshCharacter B y) by
    simp only [inverseWalshCoefficient]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B _
    ring]
  simp_rw [sum_orientationWalshCharacter_mul_eq]
  have htwo : (2 : ℂ) ^ Fintype.card I ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Finset.sum_eq_single y]
  · rw [if_pos rfl]
    field_simp
  · intro x _ hxy
    simp [hxy]
  · simp

/-- The finite Walsh linear functional attached to a coefficient vector. -/
def orientationWalshLinearForm {I : Type*} [Fintype I]
    (c : Finset I → ℂ) (x : I → Bool) : ℂ :=
  ∑ B : Finset I, c B * orientationWalshCharacter B x

/-- A Walsh combination vanishes modulo finite prime support exactly when it vanishes on the
complete compact tail constraint. -/
theorem orientationWalsh_tailRelation_iff_vanishes_tailCluster
    {I : Type*} [Fintype I] (θ : ℕ → (I → Bool)) (c : Finset I → ℂ) :
    {n | orientationWalshLinearForm c (θ n) ≠ 0}.Finite ↔
      ∀ x ∈ primeOrientationTailClusterSet θ, orientationWalshLinearForm c x = 0 := by
  classical
  let f : (↥(Finset.univ : Finset I) → Bool) → ℂ := fun b =>
    orientationWalshLinearForm c (fun i => b ⟨i, Finset.mem_univ i⟩)
  have h := finiteObservable_eventuallyEq_iff_eq_tailCluster θ Finset.univ f (fun _ => 0)
  simpa [f, orientationWalshLinearForm, orientationWalshCharacter,
    orientationRestriction] using h

/-- Restrict a Walsh coefficient vector to complex functions on a finite pattern constraint. -/
def orientationWalshRestrictionLinearMap {I : Type*} [Fintype I]
    (R : Set (I → Bool)) :
    (Finset I → ℂ) →ₗ[ℂ] (R → ℂ) where
  toFun := fun c x =>
    ∑ B : Finset I, c B * orientationWalshCharacter B x.1
  map_add' := by
    intro c d
    funext x
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro a c
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]

/-- Walsh observations restrict onto every complex function on an arbitrary finite constraint. -/
theorem orientationWalshRestrictionLinearMap_surjective
    {I : Type*} [Fintype I] (R : Set (I → Bool)) :
    Function.Surjective (orientationWalshRestrictionLinearMap R) := by
  classical
  letI : Fintype (I → Bool) := Fintype.ofFinite _
  intro f
  let F : (I → Bool) → ℂ := fun x => if hx : x ∈ R then f ⟨x, hx⟩ else 0
  refine ⟨inverseWalshCoefficient F, ?_⟩
  funext x
  change (∑ B : Finset I,
    inverseWalshCoefficient F B * orientationWalshCharacter B x.1) = f x
  rw [orientationWalsh_inversion]
  simp [F, x.2]

/-- **Finite Prime-Walsh rank law.**  The restriction rank of the complete Walsh palette is exactly
the number of allowed Boolean patterns. -/
theorem orientationWalshRestrictionLinearMap_finrank
    {I : Type*} [Fintype I] (R : Set (I → Bool)) :
    Module.finrank ℂ (orientationWalshRestrictionLinearMap R).range = Fintype.card R := by
  classical
  letI : Fintype R := Fintype.ofFinite _
  rw [LinearMap.range_eq_top.mpr (orientationWalshRestrictionLinearMap_surjective R)]
  simp

end

end GaloisForLFunctions.HTGeometry
