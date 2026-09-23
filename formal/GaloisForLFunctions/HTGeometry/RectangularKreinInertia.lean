import GaloisForLFunctions.HTGeometry.KreinLangerInertia

/-!
# Rectangular factored Krein inertia

The existing exact-inertia theorem uses equally many positive and negative feature vectors.  A
relative orientation defect naturally has different positive and negative ranks.  This file proves
the rectangular form: if the combined feature evaluation is surjective, the positive and negative
inertias are exactly the two feature counts.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix GaloisForLFunctions
open scoped BigOperators ComplexOrder

noncomputable section

/-- Rescaling each vector of a finite independent family by a nonzero scalar preserves
independence. -/
theorem linearIndependent_smul_nonzero
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V]
    (v : ι → V) (c : ι → ℂ) (hv : LinearIndependent ℂ v)
    (hc : ∀ i, c i ≠ 0) :
    LinearIndependent ℂ (fun i => c i • v i) := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro d hd i
  have hscaled : ∑ j, (d j * c j) • v j = 0 := by
    simpa [mul_smul] using hd
  have hi := hv (fun j => d j * c j) hscaled i
  exact (mul_eq_zero.mp hi).resolve_right (hc i)

/-- A Hermitian feature form with independently sized positive and negative packets. -/
def rectangularKreinForm {N kp kn : ℕ}
    (w : Fin kp → (Fin N → ℂ)) (u : Fin kn → (Fin N → ℂ)) :
    Matrix (Fin N) (Fin N) ℂ :=
  (∑ i, Matrix.of (fun p q => w i p * star (w i q))) -
    (∑ i, Matrix.of (fun p q => u i p * star (u i q)))

/-- Evaluation against a finite feature packet. -/
def rectangularFeatureEval {N k : ℕ} (v : Fin k → (Fin N → ℂ)) :
    (Fin N → ℂ) →ₗ[ℂ] (Fin k → ℂ) :=
  LinearMap.pi fun i =>
    { toFun := fun x => star (v i) ⬝ᵥ x
      map_add' := fun x y => dotProduct_add _ x y
      map_smul' := fun c x => dotProduct_smul c _ x }

@[simp]
theorem rectangularFeatureEval_apply {N k : ℕ} (v : Fin k → (Fin N → ℂ))
    (x : Fin N → ℂ) (i : Fin k) :
    rectangularFeatureEval v x i = star (v i) ⬝ᵥ x := rfl

/-- Swapping the positive and negative packets negates the form. -/
theorem rectangularKreinForm_swap {N kp kn : ℕ}
    (w : Fin kp → (Fin N → ℂ)) (u : Fin kn → (Fin N → ℂ)) :
    rectangularKreinForm u w = -rectangularKreinForm w u := by
  simp only [rectangularKreinForm]
  abel

/-- Orthogonality to the positive packet and nonvanishing against the negative packet gives a
strictly negative direction. -/
theorem rectangular_neg_def_of_orthogonal {N kp kn : ℕ}
    (w : Fin kp → (Fin N → ℂ)) (u : Fin kn → (Fin N → ℂ))
    (x : Fin N → ℂ)
    (hw : ∀ i, star (w i) ⬝ᵥ x = 0)
    (hu : ∃ i, star (u i) ⬝ᵥ x ≠ 0) :
    (star x ⬝ᵥ (rectangularKreinForm w u).mulVec x).re < 0 := by
  rw [rectangularKreinForm, Matrix.sub_mulVec, dotProduct_sub,
    Matrix.sum_mulVec, Matrix.sum_mulVec, dotProduct_sum, dotProduct_sum]
  simp_rw [rankOne_quadForm]
  rw [show (∑ i, ((‖star (w i) ⬝ᵥ x‖ ^ (2 : ℕ) : ℝ) : ℂ)) = 0 from
    Finset.sum_eq_zero (fun i _ => by rw [hw i]; simp)]
  rw [zero_sub, ← Complex.ofReal_sum]
  obtain ⟨i0, hi0⟩ := hu
  have hpos : 0 < ∑ i, ‖star (u i) ⬝ᵥ x‖ ^ (2 : ℕ) :=
    Finset.sum_pos' (fun i _ => sq_nonneg _)
      ⟨i0, Finset.mem_univ _, sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hi0)⟩
  simp only [Complex.neg_re, Complex.ofReal_re]
  linarith

/-- A surjective combined feature evaluation produces a negative-definite subspace whose dimension
is the number of negative features. -/
theorem exists_rectangular_neg_def_subspace {N kp kn : ℕ}
    (w : Fin kp → (Fin N → ℂ)) (u : Fin kn → (Fin N → ℂ))
    (hT : Function.Surjective
      ((rectangularFeatureEval w).prod (rectangularFeatureEval u))) :
    ∃ W : Submodule ℂ (Fin N → ℂ), Module.finrank ℂ W = kn ∧
      ∀ y ∈ W, y ≠ 0 →
        (star y ⬝ᵥ (rectangularKreinForm w u).mulVec y).re < 0 := by
  choose x hx using fun m : Fin kn => hT (0, Pi.single m 1)
  have hΦx : ∀ m, rectangularFeatureEval w (x m) = 0 := fun m =>
    (Prod.mk.injEq _ _ _ _).mp (hx m) |>.1
  have hΨx : ∀ m, rectangularFeatureEval u (x m) = Pi.single m 1 := fun m =>
    (Prod.mk.injEq _ _ _ _).mp (hx m) |>.2
  let S : (Fin kn → ℂ) →ₗ[ℂ] (Fin N → ℂ) := Fintype.linearCombination ℂ x
  have hΨS : (rectangularFeatureEval u).comp S = LinearMap.id := by
    apply LinearMap.ext
    intro c
    simp only [LinearMap.comp_apply, LinearMap.id_apply, S,
      Fintype.linearCombination_apply, map_sum, map_smul, hΨx]
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hΦS : (rectangularFeatureEval w).comp S = 0 := by
    apply LinearMap.ext
    intro c
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, S,
      Fintype.linearCombination_apply, map_sum, map_smul, hΦx, smul_zero,
      Finset.sum_const_zero]
  have hSinj : Function.Injective S :=
    LinearMap.injective_of_comp_eq_id S (rectangularFeatureEval u) hΨS
  refine ⟨LinearMap.range S, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hSinj, Module.finrank_fin_fun]
  · intro y hy hy0
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hy
    have hwy : ∀ i, star (w i) ⬝ᵥ (S c) = 0 := by
      intro i
      have hzero : rectangularFeatureEval w (S c) = 0 := by
        rw [← LinearMap.comp_apply, hΦS, LinearMap.zero_apply]
      rw [← rectangularFeatureEval_apply]
      rw [hzero]
      rfl
    have hcne : c ≠ 0 := fun hc => hy0 (by rw [hc, map_zero])
    have huy : ∃ i, star (u i) ⬝ᵥ (S c) ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hcne
      refine ⟨i, ?_⟩
      have heval : rectangularFeatureEval u (S c) = c := by
        rw [← LinearMap.comp_apply, hΨS, LinearMap.id_apply]
      rw [← rectangularFeatureEval_apply, heval]
      simpa using hi
    exact rectangular_neg_def_of_orthogonal w u (S c) hwy huy

/-- The negative inertia of a rectangular factored form is exactly the negative feature count when
the combined evaluation is surjective. -/
theorem rectangular_exact_neg_inertia {N kp kn : ℕ}
    (w : Fin kp → (Fin N → ℂ)) (u : Fin kn → (Fin N → ℂ))
    (hT : Function.Surjective
      ((rectangularFeatureEval w).prod (rectangularFeatureEval u))) :
    (∀ W : Submodule ℂ (Fin N → ℂ),
        (∀ y ∈ W, y ≠ 0 →
          (star y ⬝ᵥ (rectangularKreinForm w u).mulVec y).re < 0) →
        Module.finrank ℂ W ≤ kn) ∧
      (∃ W : Submodule ℂ (Fin N → ℂ), Module.finrank ℂ W = kn ∧
        ∀ y ∈ W, y ≠ 0 →
          (star y ⬝ᵥ (rectangularKreinForm w u).mulVec y).re < 0) := by
  refine ⟨?_, exists_rectangular_neg_def_subspace w u hT⟩
  intro W hW
  refine neg_inertia_le_of_posSemidef (rectangularKreinForm w u) u ?_ W hW
  rw [rectangularKreinForm, sub_add_cancel]
  exact Matrix.posSemidef_sum Finset.univ (fun i _ => outer_posSemidef _)

/-- Surjectivity of the ordered evaluation is symmetric under swapping the packets. -/
theorem rectangular_eval_surjective_swap {N kp kn : ℕ}
    (w : Fin kp → (Fin N → ℂ)) (u : Fin kn → (Fin N → ℂ))
    (hT : Function.Surjective
      ((rectangularFeatureEval w).prod (rectangularFeatureEval u))) :
    Function.Surjective
      ((rectangularFeatureEval u).prod (rectangularFeatureEval w)) := by
  rintro ⟨a, b⟩
  obtain ⟨x, hx⟩ := hT (b, a)
  refine ⟨x, Prod.ext ?_ ?_⟩
  · exact congrArg Prod.snd hx
  · exact congrArg Prod.fst hx

/-- The positive inertia of a rectangular factored form is exactly the positive feature count when
the combined evaluation is surjective. -/
theorem rectangular_exact_pos_inertia {N kp kn : ℕ}
    (w : Fin kp → (Fin N → ℂ)) (u : Fin kn → (Fin N → ℂ))
    (hT : Function.Surjective
      ((rectangularFeatureEval w).prod (rectangularFeatureEval u))) :
    (∀ W : Submodule ℂ (Fin N → ℂ),
        (∀ y ∈ W, y ≠ 0 →
          0 < (star y ⬝ᵥ (rectangularKreinForm w u).mulVec y).re) →
        Module.finrank ℂ W ≤ kp) ∧
      (∃ W : Submodule ℂ (Fin N → ℂ), Module.finrank ℂ W = kp ∧
        ∀ y ∈ W, y ≠ 0 →
          0 < (star y ⬝ᵥ (rectangularKreinForm w u).mulVec y).re) := by
  have hneg := rectangular_exact_neg_inertia u w
    (rectangular_eval_surjective_swap w u hT)
  rw [rectangularKreinForm_swap] at hneg
  constructor
  · intro W hW
    apply hneg.1 W
    intro y hy hy0
    have hp := hW y hy hy0
    have hquad :
        (star y ⬝ᵥ (-rectangularKreinForm w u).mulVec y).re =
          -(star y ⬝ᵥ (rectangularKreinForm w u).mulVec y).re := by
      rw [neg_mulVec, dotProduct_neg, Complex.neg_re]
    rw [hquad]
    exact neg_lt_zero.mpr hp
  · obtain ⟨W, hWdim, hW⟩ := hneg.2
    refine ⟨W, hWdim, ?_⟩
    intro y hy hy0
    have hn := hW y hy hy0
    have hquad :
        (star y ⬝ᵥ (-rectangularKreinForm w u).mulVec y).re =
          -(star y ⬝ᵥ (rectangularKreinForm w u).mulVec y).re := by
      rw [neg_mulVec, dotProduct_neg, Complex.neg_re]
    rw [hquad] at hn
    linarith [hn]

/-- Combined feature independence gives the surjectivity required by the exact rectangular inertia
theorems. -/
theorem rectangular_eval_surjective_of_linearIndependent {N kp kn : ℕ}
    (w : Fin kp → (Fin N → ℂ)) (u : Fin kn → (Fin N → ℂ))
    (hV : LinearIndependent ℂ (Sum.elim w u)) :
    Function.Surjective
      ((rectangularFeatureEval w).prod (rectangularFeatureEval u)) := by
  have heval : Function.Surjective
      (fun x : Fin N → ℂ =>
        (fun j => star (Sum.elim w u j) ⬝ᵥ x : (Fin kp ⊕ Fin kn) → ℂ)) :=
    eval_surjective_rect (Sum.elim w u) hV
  intro y
  let target : (Fin kp ⊕ Fin kn) → ℂ := Sum.elim y.1 y.2
  obtain ⟨x, hx⟩ := heval target
  refine ⟨x, Prod.ext ?_ ?_⟩
  · funext i
    have hi := congrFun hx (Sum.inl i)
    simpa [target, rectangularFeatureEval] using hi
  · funext i
    have hi := congrFun hx (Sum.inr i)
    simpa [target, rectangularFeatureEval] using hi

end

end GaloisForLFunctions.HTGeometry
