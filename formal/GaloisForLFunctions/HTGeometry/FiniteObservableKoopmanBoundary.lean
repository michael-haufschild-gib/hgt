import GaloisForLFunctions.HTGeometry.FiniteGibbsDifferentialBoundary

/-!
# Finite observable-model boundary for hypertranscendental clocks

Machine-learned Koopman and latent linear models seek a finite-dimensional dictionary of
observables that is invariant, exactly or approximately, under an observable operator.  For the
clock variable of a complex function the infinitesimal observable operator is differentiation.
This file records the exact-realization boundary.

If a finite-dimensional space `V` contains `f` and is closed under differentiation, every jet
`f^(n)` lies in `V`.  Finite dimension then forces a nontrivial constant linear relation among the
jets.  Equivalently, `f` has a nonzero constant-coefficient differential annihilator and is
differentially algebraic.  Hence no hypertranscendental function belongs to such a finite exact
observable model.

The positive form is stronger than the no-go: the jet-observable tower of a hypertranscendental
clock escapes *every* finite-dimensional observable space.  This is a statement about the rank of
what a clock reveals under repeated observation, not a claim about an external temporal evolution.
It also makes the approximation boundary precise: finite learned dictionaries may approximate the
clock, but exact closure must fail at some derivative observable.

ML/operator-theory provenance: S. L. Brunton, B. W. Brunton, J. L. Proctor, and J. N. Kutz,
*Koopman Invariant Subspaces and Finite Linear Representations of Nonlinear Dynamical Systems for
Control*, PLOS ONE 11 (2016), e0150171, DOI 10.1371/journal.pone.0150171; B. Lusch, J. N. Kutz,
and S. L. Brunton, *Deep learning for universal linear embeddings of nonlinear dynamics*, Nature
Communications 9 (2018), 4950, DOI 10.1038/s41467-018-07210-0.  Those works motivate finite exact
or learned invariant observable subspaces; the formal conclusions below are ordinary finite-rank
linear algebra applied to the derivative-observable tower.
-/

namespace HTGeometry

noncomputable section

open GaloisForLFunctions Module

/-- A space of clock observables closed under infinitesimal clock readout. -/
def DerivInvariantObservableSpace (V : Submodule ℂ (ℂ → ℂ)) : Prop :=
  ∀ g : ℂ → ℂ, g ∈ V → deriv g ∈ V

/-- Membership propagates to every derivative observable in an invariant model space. -/
theorem iteratedDeriv_mem_of_mem_derivInvariantObservableSpace
    {V : Submodule ℂ (ℂ → ℂ)}
    (hV : DerivInvariantObservableSpace V)
    {f : ℂ → ℂ} (hf : f ∈ V) (n : ℕ) :
    iteratedDeriv n f ∈ V := by
  induction n with
  | zero => simpa [iteratedDeriv_zero] using hf
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact hV _ ih

private theorem not_linearIndependent_iteratedDeriv_of_forall_mem_finiteDimensional
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    (f : ℂ → ℂ) (hmem : ∀ n, iteratedDeriv n f ∈ V) :
    ¬ LinearIndependent ℂ (fun n : ℕ => iteratedDeriv n f) := by
  intro hli
  let jets : ℕ → V := fun n => ⟨iteratedDeriv n f, hmem n⟩
  have hjets : LinearIndependent ℂ jets := by
    apply LinearIndependent.of_comp V.subtype
    simpa only [Function.comp_apply, jets] using! hli
  have hfinite : LinearIndependent ℂ
      (fun i : Fin (finrank ℂ V + 1) => jets i) :=
    hjets.comp (fun i : Fin (finrank ℂ V + 1) => (i : ℕ)) Fin.val_injective
  have hbound := hfinite.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hbound
  omega

/-- A finite derivative-invariant observable model forces a nonzero constant-coefficient law. -/
theorem exists_nonzero_constantCoeff_annihilator_of_mem_derivInvariantObservableSpace
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    {f : ℂ → ℂ} (hf : f ∈ V)
    (hV : DerivInvariantObservableSpace V) :
    ∃ L : Polynomial ℂ, L ≠ 0 ∧ constantCoeffDifferentialOperator L f = 0 := by
  have hnotli : ¬ LinearIndependent ℂ (fun n : ℕ => iteratedDeriv n f) :=
    not_linearIndependent_iteratedDeriv_of_forall_mem_finiteDimensional V f
      (iteratedDeriv_mem_of_mem_derivInvariantObservableSpace hV hf)
  have hnot : ¬ ConstantCoefficientDifferentiallyTranscendental f := by
    rw [constantCoefficientDifferentiallyTranscendental_iff_linearIndependent_iteratedDeriv]
    exact hnotli
  unfold ConstantCoefficientDifferentiallyTranscendental at hnot
  push Not at hnot
  obtain ⟨L, hzero, hL⟩ := hnot
  exact ⟨L, hL, hzero⟩

/-- Positive classification: every finite exact observable closure is differentially algebraic. -/
theorem differentiallyAlgebraic_of_mem_derivInvariantObservableSpace
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    {f : ℂ → ℂ} (hf : f ∈ V)
    (hV : DerivInvariantObservableSpace V) :
    DifferentiallyAlgebraic f := by
  obtain ⟨L, hL, hzero⟩ :=
    exists_nonzero_constantCoeff_annihilator_of_mem_derivInvariantObservableSpace V hf hV
  exact differentiallyAlgebraic_of_constantCoeffDifferentialOperator_eq_zero hL hzero

/-- A hypertranscendental clock cannot belong to any finite exact invariant observable model. -/
theorem not_mem_derivInvariantObservableSpace_of_hypertranscendental
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    {f : ℂ → ℂ} (hf : Hypertranscendental f)
    (hV : DerivInvariantObservableSpace V) :
    f ∉ V := by
  intro hmem
  have hcc := hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental hf
  rw [constantCoefficientDifferentiallyTranscendental_iff_linearIndependent_iteratedDeriv] at hcc
  exact not_linearIndependent_iteratedDeriv_of_forall_mem_finiteDimensional V f
    (iteratedDeriv_mem_of_mem_derivInvariantObservableSpace hV hmem) hcc

/-- **Exact finite-dictionary jet-capacity law.**  A finite-dimensional observable space can
contain at most its dimension many derivative observables from a constant-coefficient
differentially transcendental source, at arbitrary distinct derivative orders. -/
theorem iteratedDeriv_mem_finset_card_le_finrank_of_constantCoefficientDifferentiallyTranscendental
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    {f : ℂ → ℂ} (hf : ConstantCoefficientDifferentiallyTranscendental f)
    (s : Finset ℕ) (hmem : ∀ n ∈ s, iteratedDeriv n f ∈ V) :
    s.card ≤ finrank ℂ V := by
  let jets : s → V := fun n => ⟨iteratedDeriv n f, hmem n n.2⟩
  have hjets : LinearIndependent ℂ jets := by
    apply LinearIndependent.of_comp V.subtype
    exact
      ((constantCoefficientDifferentiallyTranscendental_iff_linearIndependent_iteratedDeriv f).mp
        hf).comp (fun n : s => (n : ℕ)) Subtype.coe_injective
  simpa only [Fintype.card_coe] using hjets.fintype_card_le_finrank

/-- Quantitative positive escape: some derivative among the first `finrank V + 1` observables
already lies outside every fixed finite-dimensional dictionary. -/
theorem exists_iteratedDeriv_not_mem_le_finrank_of_constantCoefficientDifferentiallyTranscendental
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    {f : ℂ → ℂ} (hf : ConstantCoefficientDifferentiallyTranscendental f) :
    ∃ n ≤ finrank ℂ V, iteratedDeriv n f ∉ V := by
  by_contra hescape
  push Not at hescape
  have hcard :=
    iteratedDeriv_mem_finset_card_le_finrank_of_constantCoefficientDifferentiallyTranscendental
      V hf (Finset.range (finrank ℂ V + 1))
        (fun n hn => hescape n (by have := Finset.mem_range.mp hn; omega))
  simp only [Finset.card_range] at hcard
  omega

/-- Positive escape theorem: the derivative-observable tower leaves every finite model space. -/
theorem exists_iteratedDeriv_not_mem_finiteDimensional_of_hypertranscendental
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    {f : ℂ → ℂ} (hf : Hypertranscendental f) :
    ∃ n : ℕ, iteratedDeriv n f ∉ V := by
  obtain ⟨n, _, hn⟩ :=
    exists_iteratedDeriv_not_mem_le_finrank_of_constantCoefficientDifferentiallyTranscendental
      V (hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental hf)
  exact ⟨n, hn⟩

end

end HTGeometry
