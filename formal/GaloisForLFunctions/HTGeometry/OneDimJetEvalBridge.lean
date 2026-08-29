import GaloisForLFunctions.HTGeometry.BoundedRandomEntireSeries
import GaloisForLFunctions.HTGeometry.MultivariateJetCompositionLaw

/-!
# One-dimensional mixed jets are ordinary iterated derivatives

In one coordinate a multi-index is a single order, and the canonical mixed-partial observation of
the one-variable embedding of an entire function is its iterated derivative at the point.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem finsupp_fin_one_eq_single (a : Fin 1 →₀ ℕ) : a = Finsupp.single 0 (a 0) := by
  refine Finsupp.ext fun i => ?_
  fin_cases i
  simp

theorem wordMultiplicity_const_zero (m : ℕ) :
    wordMultiplicity (fun _ : Fin m => (0 : Fin 1)) = Finsupp.single 0 m := by
  classical
  refine Finsupp.ext fun i => ?_
  fin_cases i
  rw [wordMultiplicity]
  simp

/-- **One-dimensional jet bridge.**  The canonical multi-index jet observation of the
one-coordinate embedding of an entire function is its iterated derivative. -/
theorem multiIndexJetEvalCLM_oneDim (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (x : Fin 1 → ℂ) (a : Fin 1 →₀ ℕ) :
    multiIndexJetEvalCLM x a (oneDimMultivariateEntireOfDifferentiable g hg)
      = iteratedDeriv (a 0) g (x 0) := by
  classical
  set m : ℕ := a 0 with hm
  have hmul : wordMultiplicity (multiIndexWord a)
      = wordMultiplicity (fun _ : Fin m => (0 : Fin 1)) := by
    rw [wordMultiplicity_multiIndexWord, wordMultiplicity_const_zero, hm,
      ← finsupp_fin_one_eq_single]
  rw [multiIndexJetEvalCLM_apply,
    orderedPartialJetEvalCLM_congr_of_wordMultiplicity_eq x hmul,
    orderedPartialJetEvalCLM_eq_iteratedFDeriv]
  have hcd : ContDiff ℂ (m : WithTop ℕ∞) g := hg.contDiff.of_le (by exact_mod_cast le_top)
  have hfun : ((oneDimMultivariateEntireOfDifferentiable g hg).1 : (Fin 1 → ℂ) → ℂ)
      = g ∘ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0) := rfl
  have hdir : (fun j : Fin m => coordinateJetDirection ((fun _ : Fin m => (0 : Fin 1)) j))
      = fun _ : Fin m => (Pi.single (0 : Fin 1) (1 : ℂ)) := rfl
  rw [hdir, hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ hcd _ le_rfl,
    iteratedDeriv_eq_iteratedFDeriv]
  simp

end

end GaloisForLFunctions.HTGeometry
