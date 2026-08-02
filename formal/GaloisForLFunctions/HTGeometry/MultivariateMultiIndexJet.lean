import GaloisForLFunctions.HTGeometry.MultivariatePolynomialJetCoefficient

/-!
# Canonical multivariate jets indexed by multi-indices

Mixed partials are intrinsically indexed by finitely supported coordinate multiplicities, whereas
the Frechet-jet API evaluates an ordered finite word of directions.  This file chooses one
canonical word for each multi-index and proves that its multiplicity is exactly the prescribed
index.  It then packages the corresponding continuous jet observation and the finite polynomial
packet-surjectivity theorem without introducing duplicate variables for permutations of a word.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Slots of a coordinate multi-index: coordinate `i` contributes exactly `a i` slots. -/
abbrev MultiIndexSlot {d : ℕ} (a : Fin d →₀ ℕ) := Σ i, Fin (a i)

/-- A canonical ordered coordinate word representing a multi-index. -/
def multiIndexWord {d : ℕ} (a : Fin d →₀ ℕ) :
    Fin (Fintype.card (MultiIndexSlot a)) → Fin d :=
  fun j ↦ ((Fintype.equivFin (MultiIndexSlot a)).symm j).1

/-- The canonical word contains every coordinate with exactly its prescribed multiplicity. -/
theorem wordMultiplicity_multiIndexWord {d : ℕ} (a : Fin d →₀ ℕ) :
    wordMultiplicity (multiIndexWord a) = a := by
  classical
  ext i
  simp only [wordMultiplicity, multiIndexWord]
  change (Finsupp.applyAddHom i) (∑ c : Fin (Fintype.card (MultiIndexSlot a)),
    Finsupp.single (((Fintype.equivFin (MultiIndexSlot a)).symm c).1) 1) = a i
  rw [map_sum]
  calc
    ∑ c : Fin (Fintype.card (MultiIndexSlot a)),
        (Finsupp.applyAddHom i)
          (Finsupp.single (((Fintype.equivFin (MultiIndexSlot a)).symm c).1) 1) =
      ∑ s : MultiIndexSlot a, (Finsupp.single s.1 1) i := by
        simpa using ((Fintype.equivFin (MultiIndexSlot a)).symm.sum_comp
          (fun s : MultiIndexSlot a ↦ (Finsupp.single s.1 1) i))
    _ = a i := by
      rw [Fintype.sum_sigma]
      simp [Finsupp.single_apply]

/-- The continuous mixed-partial observation indexed by a coordinate multi-index. -/
def multiIndexJetEvalCLM {d : ℕ} (x : Fin d → ℂ) (a : Fin d →₀ ℕ) :
    MultivariateEntire d →L[ℂ] ℂ :=
  orderedPartialJetEvalCLM x (multiIndexWord a)

@[simp]
theorem multiIndexJetEvalCLM_apply {d : ℕ}
    (x : Fin d → ℂ) (a : Fin d →₀ ℕ) (f : MultivariateEntire d) :
    multiIndexJetEvalCLM x a f =
      orderedPartialJetEvalCLM x (multiIndexWord a) f :=
  rfl

/-- A polynomial mixed partial is its centered coefficient times the exact multi-index
factorial. -/
theorem multiIndexJetEvalCLM_mvPolynomial_eq_centered_coeff {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (x : Fin d → ℂ) (a : Fin d →₀ ℕ) :
    multiIndexJetEvalCLM x a (mvPolynomialMultivariateEntire P) =
      MvPolynomial.coeff a (mvPolynomialBaseTranslation x P) * multiIndexFactorial a := by
  rw [multiIndexJetEvalCLM, orderedPartialJetEvalCLM_mvPolynomial_eq_centered_coeff,
    wordMultiplicity_multiIndexWord]

/-- **Arbitrary finite multi-index jet packet surjectivity.** At finitely many distinct points,
every mixed partial below a prescribed total order is realized by one multivariable polynomial. -/
theorem exists_mvPolynomial_multiIndexJetEvalCLM_eq_arbitrary
    {d : ℕ} {I : Type*} [Finite I]
    (w : I → Fin d → ℂ) (hw : Function.Injective w)
    (m : I → ℕ) (jet : I → (Fin d →₀ ℕ) → ℂ) :
    ∃ P : MvPolynomial (Fin d) ℂ,
      ∀ i (a : Fin d →₀ ℕ),
        Finsupp.degree a < m i →
          multiIndexJetEvalCLM (w i) a (mvPolynomialMultivariateEntire P) = jet i a := by
  obtain ⟨P, hP⟩ := exists_mvPolynomial_orderedPartialJetEvalCLM_eq_arbitrary w hw m jet
  refine ⟨P, fun i a ha ↦ ?_⟩
  simpa [multiIndexJetEvalCLM, wordMultiplicity_multiIndexWord] using
    hP i (Fintype.card (MultiIndexSlot a)) (multiIndexWord a)
      (by simpa [wordMultiplicity_multiIndexWord] using ha)

/-- Local uniform convergence of line-entire sources is convergence in the compact-open
`MultivariateEntire` topology. -/
theorem tendsto_multivariateEntire_of_locallyUniform
    {T : Type*} {l : Filter T} {d : ℕ}
    {F : T → MultivariateEntire d} {f : MultivariateEntire d}
    (h : TendstoLocallyUniformly (fun t => (F t).1) f.1 l) :
    Filter.Tendsto F l (nhds f) := by
  rw [tendsto_subtype_rng]
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr h

/-- Consequently every fixed mixed jet converges under local uniform convergence. This is the
Cauchy-estimate bridge used for all derivative orders of a damped Poincare complement. -/
theorem tendsto_multiIndexJetEvalCLM_of_locallyUniform
    {T : Type*} {l : Filter T} {d : ℕ}
    {F : T → MultivariateEntire d} {f : MultivariateEntire d}
    (h : TendstoLocallyUniformly (fun t => (F t).1) f.1 l)
    (x : Fin d → ℂ) (a : Fin d →₀ ℕ) :
    Filter.Tendsto (fun t => multiIndexJetEvalCLM x a (F t)) l
      (nhds (multiIndexJetEvalCLM x a f)) := by
  have heval : Filter.Tendsto (fun g : MultivariateEntire d =>
      multiIndexJetEvalCLM x a g) (nhds f)
      (nhds (multiIndexJetEvalCLM x a f)) :=
    (multiIndexJetEvalCLM x a).continuous.continuousAt
  exact heval.comp (tendsto_multivariateEntire_of_locallyUniform h)

end

end GaloisForLFunctions.HTGeometry
