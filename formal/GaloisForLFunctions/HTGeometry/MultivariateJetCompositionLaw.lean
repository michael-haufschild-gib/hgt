import GaloisForLFunctions.HTGeometry.MultivariateEntirePartialDeriv
import GaloisForLFunctions.HTGeometry.MultivariateMultiIndexJet

/-!
# The jet composition law

An ordered mixed jet depends only on the multiplicity of its word, because two words with the same
multiplicity differ by a permutation of the slots and the iterated Frechet derivative is symmetric.
Stripping slots one at a time therefore identifies the iterated directional derivative of a source
with the shift of its multi-index jets: `∂^γ ∘ ∂^β = ∂^{β+γ}`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ}

/-- The multiplicity of a coordinate in a word counts its slots. -/
theorem wordMultiplicity_apply {n : ℕ} (word : Fin n → Fin d) (i : Fin d) :
    wordMultiplicity word i = Fintype.card {j : Fin n // word j = i} := by
  classical
  rw [wordMultiplicity, Finsupp.finsetSum_apply, Fintype.card_subtype]
  simp [Finsupp.single_apply, eq_comm]

/-- The canonical word of a multi-index of a given length has that total degree. -/
theorem degree_wordMultiplicity {n : ℕ} (word : Fin n → Fin d) :
    Finsupp.degree (wordMultiplicity word) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [wordMultiplicity_succ, map_add, ih, Finsupp.degree_single]

/-- Two words with the same multiplicity differ by a permutation of the slots. -/
theorem exists_perm_comp_of_wordMultiplicity_eq {n : ℕ} {w w' : Fin n → Fin d}
    (hw : wordMultiplicity w = wordMultiplicity w') :
    ∃ σ : Equiv.Perm (Fin n), w' ∘ σ = w := by
  classical
  have hcard : ∀ i : Fin d,
      Fintype.card {j : Fin n // w j = i} = Fintype.card {j : Fin n // w' j = i} := by
    intro i
    rw [← wordMultiplicity_apply, ← wordMultiplicity_apply, hw]
  let e : ∀ i : Fin d, {j : Fin n // w j = i} ≃ {j : Fin n // w' j = i} := fun i =>
    Fintype.equivOfCardEq (hcard i)
  refine ⟨((Equiv.sigmaFiberEquiv w).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv w'))), ?_⟩
  funext j
  exact (e (w j) ⟨j, rfl⟩).2

/-- Permuting the slots of a word does not change the ordered mixed jet. -/
theorem orderedPartialJetEvalCLM_comp_perm {n : ℕ} (x : Fin d → ℂ) (word : Fin n → Fin d)
    (σ : Equiv.Perm (Fin n)) (g : MultivariateEntire d) :
    orderedPartialJetEvalCLM x (word ∘ σ) g = orderedPartialJetEvalCLM x word g := by
  rw [orderedPartialJetEvalCLM_eq_iteratedFDeriv, orderedPartialJetEvalCLM_eq_iteratedFDeriv]
  simpa [Function.comp_def] using
    ((MultivariateEntire.contDiff g).contDiffAt.iteratedFDeriv_comp_perm
      (fun j => coordinateJetDirection (word j)) σ)

/-- **An ordered mixed jet depends only on the multiplicity of its word.** -/
theorem orderedPartialJetEvalCLM_congr_of_wordMultiplicity_eq {n m : ℕ} (x : Fin d → ℂ)
    {w : Fin n → Fin d} {w' : Fin m → Fin d} (hw : wordMultiplicity w = wordMultiplicity w')
    (g : MultivariateEntire d) :
    orderedPartialJetEvalCLM x w g = orderedPartialJetEvalCLM x w' g := by
  have hnm : n = m := by
    have h1 := degree_wordMultiplicity w
    have h2 := degree_wordMultiplicity w'
    rw [hw, h2] at h1
    exact h1.symm
  subst hnm
  obtain ⟨σ, hσ⟩ := exists_perm_comp_of_wordMultiplicity_eq hw
  rw [← hσ, orderedPartialJetEvalCLM_comp_perm]

/-- Iterated coordinate differentiation of a source along a word. -/
def wordPartialDerivEntire : {n : ℕ} → (Fin n → Fin d) → MultivariateEntire d →
    MultivariateEntire d
  | 0, _, g => g
  | (n + 1), word, g =>
      wordPartialDerivEntire (Fin.init word)
        (partialDerivEntire (coordinateJetDirection (word (Fin.last n))) g)

/-- The ordered mixed jet is the value of the iterated directional derivative. -/
theorem orderedPartialJetEvalCLM_eq_wordPartialDerivEntire :
    ∀ {n : ℕ} (x : Fin d → ℂ) (word : Fin n → Fin d) (g : MultivariateEntire d),
      orderedPartialJetEvalCLM x word g = (wordPartialDerivEntire word g).1 x
  | 0, x, word, g => by
      rw [orderedPartialJetEvalCLM_eq_iteratedFDeriv, iteratedFDeriv_zero_apply]
      rfl
  | (n + 1), x, word, g => by
      rw [orderedPartialJetEvalCLM_succ_right, wordPartialDerivEntire]
      exact orderedPartialJetEvalCLM_eq_wordPartialDerivEntire x (Fin.init word) _

/-- Appending one coordinate slot shifts the multi-index jet by that coordinate. -/
theorem multiIndexJetEvalCLM_partialDerivEntire (x : Fin d → ℂ) (γ : Fin d →₀ ℕ) (i : Fin d)
    (g : MultivariateEntire d) :
    multiIndexJetEvalCLM x γ (partialDerivEntire (coordinateJetDirection i) g) =
      multiIndexJetEvalCLM x (γ + Finsupp.single i 1) g := by
  have hmul : wordMultiplicity (Fin.snoc (multiIndexWord γ) i) =
      wordMultiplicity (multiIndexWord (γ + Finsupp.single i 1)) := by
    rw [wordMultiplicity_succ, Fin.init_snoc, Fin.snoc_last, wordMultiplicity_multiIndexWord,
      wordMultiplicity_multiIndexWord]
  rw [multiIndexJetEvalCLM_apply, multiIndexJetEvalCLM_apply,
    ← orderedPartialJetEvalCLM_congr_of_wordMultiplicity_eq x hmul g,
    orderedPartialJetEvalCLM_succ_right, Fin.init_snoc, Fin.snoc_last]

/-- **The jet composition law along a word.** -/
theorem multiIndexJetEvalCLM_wordPartialDerivEntire :
    ∀ {n : ℕ} (x : Fin d → ℂ) (γ : Fin d →₀ ℕ) (word : Fin n → Fin d) (g : MultivariateEntire d),
      multiIndexJetEvalCLM x γ (wordPartialDerivEntire word g) =
        multiIndexJetEvalCLM x (γ + wordMultiplicity word) g
  | 0, x, γ, word, g => by
      rw [wordPartialDerivEntire, wordMultiplicity_zero, add_zero]
  | (n + 1), x, γ, word, g => by
      rw [wordPartialDerivEntire,
        multiIndexJetEvalCLM_wordPartialDerivEntire x γ (Fin.init word) _,
        multiIndexJetEvalCLM_partialDerivEntire, wordMultiplicity_succ]
      rw [add_assoc]

/-- Iterated coordinate differentiation of a source along a multi-index. -/
def multiPartialDerivEntire (β : Fin d →₀ ℕ) (g : MultivariateEntire d) : MultivariateEntire d :=
  wordPartialDerivEntire (multiIndexWord β) g

/-- **`∂^γ ∘ ∂^β = ∂^{β+γ}` for the continuous multi-index jet observations.** -/
theorem multiIndexJetEvalCLM_multiPartialDerivEntire (x : Fin d → ℂ) (γ β : Fin d →₀ ℕ)
    (g : MultivariateEntire d) :
    multiIndexJetEvalCLM x γ (multiPartialDerivEntire β g) =
      multiIndexJetEvalCLM x (γ + β) g := by
  rw [multiPartialDerivEntire, multiIndexJetEvalCLM_wordPartialDerivEntire,
    wordMultiplicity_multiIndexWord]

/-- The zeroth multi-index jet is evaluation. -/
@[simp] theorem multiIndexJetEvalCLM_zero (x : Fin d → ℂ) (g : MultivariateEntire d) :
    multiIndexJetEvalCLM x 0 g = g.1 x := by
  have hmul : wordMultiplicity (multiIndexWord (0 : Fin d →₀ ℕ)) =
      wordMultiplicity (Fin.elim0 : Fin 0 → Fin d) := by
    rw [wordMultiplicity_multiIndexWord, wordMultiplicity_zero]
  rw [multiIndexJetEvalCLM_apply,
    orderedPartialJetEvalCLM_congr_of_wordMultiplicity_eq x hmul g,
    orderedPartialJetEvalCLM_eq_iteratedFDeriv, iteratedFDeriv_zero_apply]

end

end GaloisForLFunctions.HTGeometry
