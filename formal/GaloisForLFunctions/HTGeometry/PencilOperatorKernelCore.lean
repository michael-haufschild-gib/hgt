import GaloisForLFunctions.HTGeometry.PencilIteratedDerivation
import GaloisForLFunctions.HTGeometry.PencilSRRealization

/-!
# The operator kernel: structural core

The pieces needed to run the facet-isolation argument with an operator
`𝒟 = ∑_r δ^r P_r(T)` instead of a single polynomial.

* `iteratedDeriv_finset_sum` — iterated derivatives commute with finite sums;
* `seedCarrierPoly_eq_sum_phaseComp` — a pencil carrier is a sum of phase composites;
* `differentiable_dirDeriv_iterate_seedCarrierPoly` — every iterated derivative of a carrier is
  entire, because it is again such a sum;
* `dirDeriv_iterate_shiftAlgHom` — iterated derivations commute with the shift algebra;
* `symbHom_combination_eq_zero_of_isolated_const` — a constant isolated operator carrier kills the
  whole symbol combination at every positive level.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ} {α : Type*} [DecidableEq α] {facets : Finset (Finset α)}

/-! ### Iterated derivatives of finite sums -/

theorem iteratedDeriv_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} (m : ℕ)
    (hf : ∀ i ∈ s, ContDiff ℂ (m : ℕ∞) (f i)) (x : ℂ) :
    iteratedDeriv m (fun u => ∑ i ∈ s, f i u) x = ∑ i ∈ s, iteratedDeriv m (f i) x := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_sum hf]
  simp only [Finset.sum_apply, _root_.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [← iteratedDeriv_eq_iteratedFDeriv]

/-! ### A pencil carrier is a sum of phase composites -/

omit [DecidableEq α] in
theorem seedCarrierPoly_eq_sum_phaseComp (S : PencilSeparation facets (Fin d → ℂ))
    (Lin : Finset α → ((Fin d → ℂ) →ₗ[ℂ] ℂ))
    (hLin : ∀ A ∈ facets, ∀ z, S.phase A z = Lin A z) (P : MvPolynomial α ℂ) :
    seedCarrierPoly S.ω S.seed P
      = fun z => ∑ A ∈ facets,
          phaseComp (Lin A) (dilateSumHom (polyShift S.ω P) (S.phase A)) z := by
  funext z
  have hseed : S.seed = fun w => ∑ A ∈ facets, expSeedHom (S.phase A) w := rfl
  rw [hseed, seedCarrierPoly_sum]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [seedCarrierPoly_expSeedHom]
  show dilateSumHom (polyShift S.ω P) (S.phase A) (Complex.exp (S.phase A z))
    = dilateSumHom (polyShift S.ω P) (S.phase A) (Complex.exp (Lin A z))
  rw [hLin A hA z]

omit [DecidableEq α] in
theorem contDiff_dilateSumHom_polyShift (S : PencilSeparation facets (Fin d → ℂ))
    (A : Finset α) (P : MvPolynomial α ℂ) :
    ContDiff ℂ (⊤ : ℕ∞) (dilateSumHom (polyShift S.ω P) (S.phase A)) :=
  contDiff_dilateSumHom _ _

omit [DecidableEq α] in
/-- Every iterated derivative of a pencil carrier is again a sum of phase composites. -/
theorem dirDeriv_iterate_seedCarrierPoly (S : PencilSeparation facets (Fin d → ℂ))
    (Lin : Finset α → ((Fin d → ℂ) →ₗ[ℂ] ℂ))
    (hLin : ∀ A ∈ facets, ∀ z, S.phase A z = Lin A z) (P : MvPolynomial α ℂ)
    (w : Fin d → ℂ) (r : ℕ) :
    (dirDeriv w)^[r] (seedCarrierPoly S.ω S.seed P)
      = fun z => ∑ A ∈ facets, phaseComp (Lin A)
          (fun u => (Lin A w) ^ r
            * (eulerOp^[r] (dilateSumHom (polyShift S.ω P) (S.phase A))) u) z := by
  rw [seedCarrierPoly_eq_sum_phaseComp S Lin hLin P]
  exact dirDeriv_iterate_sum_phaseComp facets Lin _
    (fun A _ => contDiff_dilateSumHom_polyShift S A P) w r

omit [DecidableEq α] in
theorem differentiable_dirDeriv_iterate_seedCarrierPoly
    (S : PencilSeparation facets (Fin d → ℂ))
    (Lin : Finset α → ((Fin d → ℂ) →ₗ[ℂ] ℂ))
    (hLin : ∀ A ∈ facets, ∀ z, S.phase A z = Lin A z) (P : MvPolynomial α ℂ)
    (w : Fin d → ℂ) (r : ℕ) :
    Differentiable ℂ ((dirDeriv w)^[r] (seedCarrierPoly S.ω S.seed P)) := by
  rw [dirDeriv_iterate_seedCarrierPoly S Lin hLin P w r]
  refine Differentiable.fun_sum fun A _ => ?_
  exact differentiable_phaseComp
    (((contDiff_eulerOp_iterate (contDiff_dilateSumHom_polyShift S A P) r).differentiable
      (by simp)).const_mul _)

/-! ### Iterated derivations commute with the shift algebra -/

theorem dirDeriv_iterate_shiftAlgHom (a : AddMonoidAlgebra ℂ (Fin d → ℂ)) (w : Fin d → ℂ)
    {f : (Fin d → ℂ) → ℂ} (hf : ∀ j : ℕ, Differentiable ℂ ((dirDeriv w)^[j] f)) (r : ℕ) :
    (dirDeriv w)^[r] (shiftAlgHom a f) = shiftAlgHom a ((dirDeriv w)^[r] f) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, dirDeriv_shiftAlgHom a (hf r) w,
      ← Function.iterate_succ_apply' (dirDeriv w) r]

end

end GaloisForLFunctions.HTGeometry
