import GaloisForLFunctions.HTGeometry.FiniteObservableKoopmanBoundary

/-!
# Realizations of the derivative-invariant observable interface

The trivial and full observable spaces are derivative invariant, and invariance is preserved by
intersections, sums and infima.  The interesting finite-dimensional realization is the line spanned
by an eigenfunction of the derivative: if `deriv f = c • f` then `span {f}` is derivative invariant
and one-dimensional.

The exponential is such an eigenfunction, so the finite-dictionary classification applies to it:
the exponential is differentially algebraic, and no hypertranscendental clock is a scalar multiple
of it.
-/

open Module

namespace HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ## Lattice realizations -/

theorem derivInvariantObservableSpace_bot :
    DerivInvariantObservableSpace (⊥ : Submodule ℂ (ℂ → ℂ)) := by
  intro g hg
  rw [Submodule.mem_bot] at hg
  subst hg
  have h0 : deriv (0 : ℂ → ℂ) = 0 := by
    funext x
    exact deriv_const x 0
  rw [h0]
  exact Submodule.zero_mem _

theorem derivInvariantObservableSpace_top :
    DerivInvariantObservableSpace (⊤ : Submodule ℂ (ℂ → ℂ)) := fun _ _ => Submodule.mem_top

theorem DerivInvariantObservableSpace.inf {V W : Submodule ℂ (ℂ → ℂ)}
    (hV : DerivInvariantObservableSpace V) (hW : DerivInvariantObservableSpace W) :
    DerivInvariantObservableSpace (V ⊓ W) := fun g hg => ⟨hV g hg.1, hW g hg.2⟩

theorem DerivInvariantObservableSpace.iInf {ι : Type*} {V : ι → Submodule ℂ (ℂ → ℂ)}
    (hV : ∀ i, DerivInvariantObservableSpace (V i)) :
    DerivInvariantObservableSpace (⨅ i, V i) := by
  intro g hg
  rw [Submodule.mem_iInf] at hg ⊢
  exact fun i => hV i g (hg i)

/-! ## The eigenfunction line -/

/-- **Derivative eigenfunctions span invariant lines.** -/
theorem derivInvariantObservableSpace_span_singleton {f : ℂ → ℂ} {c : ℂ}
    (hf : Differentiable ℂ f) (hderiv : deriv f = c • f) :
    DerivInvariantObservableSpace (Submodule.span ℂ {f}) := by
  intro g hg
  rw [Submodule.mem_span_singleton] at hg ⊢
  obtain ⟨a, ha⟩ := hg
  refine ⟨a * c, ?_⟩
  have hsmul : deriv (a • f) = a • deriv f := by
    funext x
    exact deriv_const_smul a (hf x)
  rw [← ha, hsmul, hderiv, smul_smul]

instance finiteDimensional_span_singleton (f : ℂ → ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ ({f} : Set (ℂ → ℂ))) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_singleton f)

/-- The exponential clock spans a derivative-invariant line. -/
theorem derivInvariantObservableSpace_span_exp :
    DerivInvariantObservableSpace (Submodule.span ℂ {Complex.exp}) :=
  derivInvariantObservableSpace_span_singleton (c := 1) Complex.differentiable_exp
    (by rw [Complex.deriv_exp, one_smul])

/-! ## Consequences with no interface premise -/

/-- **The exponential clock is differentially algebraic.** -/
theorem differentiallyAlgebraic_complex_exp : DifferentiallyAlgebraic Complex.exp :=
  differentiallyAlgebraic_of_mem_derivInvariantObservableSpace
    (Submodule.span ℂ {Complex.exp})
    (Submodule.mem_span_singleton_self Complex.exp)
    derivInvariantObservableSpace_span_exp

/-- No hypertranscendental clock is a scalar multiple of the exponential. -/
theorem not_mem_span_exp_of_hypertranscendental {f : ℂ → ℂ} (hf : Hypertranscendental f) :
    f ∉ Submodule.span ℂ ({Complex.exp} : Set (ℂ → ℂ)) :=
  not_mem_derivInvariantObservableSpace_of_hypertranscendental
    (Submodule.span ℂ {Complex.exp}) hf derivInvariantObservableSpace_span_exp

/-- **Eigenfunction classification.**  Every derivative eigenfunction is differentially
algebraic. -/
theorem differentiallyAlgebraic_of_deriv_eq_smul {f : ℂ → ℂ} {c : ℂ}
    (hf : Differentiable ℂ f) (hderiv : deriv f = c • f) :
    DifferentiallyAlgebraic f :=
  differentiallyAlgebraic_of_mem_derivInvariantObservableSpace
    (Submodule.span ℂ {f}) (Submodule.mem_span_singleton_self f)
    (derivInvariantObservableSpace_span_singleton hf hderiv)

end

end HTGeometry
