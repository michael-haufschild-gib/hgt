import GaloisForLFunctions.HTGeometry.ChainShellMaximalProjectivity
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import GaloisForLFunctions.RHTower.UnitaryEulerFactorRigidity

/-!
# How many source energies can a finite set of detunings cover?

A model energy and an echo frequency determine a source energy by addition.
Over the rationals the affine dimension of all such sums is at most the sum
of the two affine dimensions. A projectively independent spectrum turns
this dimension bound into a bound on the number of covered energy levels.
-/

open scoped BigOperators Classical
open Module Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Rational directions of a two-term energy sum come from its two summands. -/
private theorem vectorSpan_energySum_le {A B I : Type*}
    (f : A → ℝ) (g : B → ℝ) (a : I → A) (b : I → B) :
    vectorSpan ℚ (range fun i => f (a i) + g (b i)) ≤
      vectorSpan ℚ (range f) ⊔ vectorSpan ℚ (range g) := by
  rw [vectorSpan_def]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
  apply Submodule.mem_sup.mpr
  refine ⟨f (a i) - f (a j), vsub_mem_vectorSpan ℚ ⟨_, rfl⟩ ⟨_, rfl⟩,
    g (b i) - g (b j), vsub_mem_vectorSpan ℚ ⟨_, rfl⟩ ⟨_, rfl⟩, ?_⟩
  change _ = (_ + _) - (_ + _)
  ring

/-- The rational affine dimension of any family of detuning matches is
bounded solely in terms of the number of model levels and selected detunings. -/
theorem energySum_affineDimension_bound {A B I : Type*}
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A → ℝ) (g : B → ℝ) (a : I → A) (b : I → B) :
    finrank ℚ (vectorSpan ℚ (range fun i => f (a i) + g (b i))) + 2 ≤
      Fintype.card A + Fintype.card B := by
  have h := (Submodule.finrank_mono (vectorSpan_energySum_le f g a b)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  have hf := finrank_vectorSpan_range_add_one_le ℚ f
  have hg := finrank_vectorSpan_range_add_one_le ℚ g
  omega

/-- Among a maximally projective source's energies, k model levels and q
selected detunings together cover at most k+q−1 distinct labels. -/
theorem maximallyProjective_detuningCoverage {I A B : Type*}
    [Fintype I] [DecidableEq I] [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (E : I → ℝ) (hE : MaximallyProjectiveEnergy E) (F : A → ℝ) (v : B → ℝ) :
    Fintype.card {i : I // ∃ a b, E i = F a + v b} + 1 ≤
      Fintype.card A + Fintype.card B := by
  classical
  let S := {i : I // ∃ a b, E i = F a + v b}
  change Fintype.card S + 1 ≤ _
  cases isEmpty_or_nonempty S with
  | inl h =>
    letI := h
    have ha := Fintype.card_pos (α := A)
    simp only [Fintype.card_eq_zero]
    omega
  | inr h =>
    letI := h
    let s : S := Classical.choice h
    have hAI : AffineIndependent ℚ E :=
      (affineIndependent_iff_linearIndependent_vsub ℚ E s.val).mpr
        (linearIndependent_rat_projectiveFrequency E hE s.val)
    have hsub : AffineIndependent ℚ (fun i : S => E i.val) :=
      hAI.subtype _
    choose a b hab using fun i : S => i.property
    have hfun : (fun i : S => E i.val) = fun i => F (a i) + v (b i) := funext hab
    have hc := hsub.finrank_vectorSpan_add_one
    rw [hfun] at hc
    have hr := energySum_affineDimension_bound F v a b
    omega

/-- Unnormalized trace weight carried by selected echo frequencies. The
squared eigenbasis overlaps are the spectral weights in the trace expansion. -/
def selectedEchoWeight {I A B : Type*} [Fintype I] [DecidableEq I]
    (E : I → ℝ) (V : Matrix.unitaryGroup I ℂ) (g : I → A) (F : A → ℝ) (v : B → ℝ) : ℝ :=
  ∑ i, ∑ j, if ∃ b, E i = F (g j) + v b then Complex.normSq ((V : Matrix I I ℂ) i j) else 0

/-- Basis optimization cannot assign more than one unit of trace weight to
each covered source energy. -/
theorem selectedEchoWeight_le_covered {I A B : Type*}
    [Fintype I] [DecidableEq I] (E : I → ℝ) (V : Matrix.unitaryGroup I ℂ)
    (g : I → A) (F : A → ℝ) (v : B → ℝ) :
    selectedEchoWeight E V g F v ≤ (Fintype.card {i : I // ∃ a b, E i = F a + v b} : ℝ) := by
  classical
  let covered (i : I) := ∃ a b, E i = F a + v b
  calc
    _ ≤ ∑ i, if covered i then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h : covered i
      · rw [if_pos h, ← RHTower.sum_normSq_row_of_mem_unitary V.2 i]
        apply Finset.sum_le_sum
        intro j _
        split
        · exact le_rfl
        · exact Complex.normSq_nonneg _
      · have hno (j : I) : ¬ ∃ b, E i = F (g j) + v b :=
          fun ⟨b, hb⟩ => h ⟨g j,b,hb⟩
        simp only [if_neg h, if_neg (hno _), Finset.sum_const_zero, le_refl]
    _ = _ := by rw [Finset.sum_boole, Fintype.card_subtype]; rfl

/-- For the commuting model retaining one representative per sector, every
nonrepresentative level contributes its own distinct nonzero echo frequency.
The zero-frequency atom consists exactly of the representatives. -/
theorem representativeEcho_detuning_eq_iff {I A : Type*}
    [Fintype I] [DecidableEq I] (E : I → ℝ) (hE : MaximallyProjectiveEnergy E)
    (g : I → A) (rep : A → I) (i j : I) :
    E i - E (rep (g i)) = E j - E (rep (g j)) ↔
      i = j ∨ (i = rep (g i) ∧ j = rep (g j)) := by
  constructor
  · intro he
    by_cases hi : i = rep (g i)
    · have hz : E j - E (rep (g j)) = 0 := he.symm.trans (sub_eq_zero.mpr (congrArg E hi))
      exact Or.inr ⟨hi, hE.injective (sub_eq_zero.mp hz)⟩
    · have hj : j ≠ rep (g j) := by
        intro h
        exact hi (hE.injective (sub_eq_zero.mp (he.trans (sub_eq_zero.mpr (congrArg E h)))))
      have h := maximallyProjectiveEnergy_orientedGap_injective E hE
        (a₁ := ⟨(i, rep (g i)), hi⟩) (a₂ := ⟨(j, rep (g j)), hj⟩) he
      exact Or.inl (congrArg (fun p => p.val.1) h)
  · rintro (rfl | ⟨hi,hj⟩)
    · rfl
    · rw [sub_eq_zero.mpr (congrArg E hi), sub_eq_zero.mpr (congrArg E hj)]

/-- One conull set of nearest-neighbour qubit chains works for all comparison
spectra and frequency sets chosen after observing the source Hamiltonian. -/
theorem chainShell_detuningCoverage_ae (n : ℕ) :
    ∀ᵐ θ ∂(shellProbability (Fin (Fintype.card (ChainLabel (n+3))))),
      ∀ k q : ℕ, ∀ (F : Fin (k+1) → ℝ) (v : Fin (q+1) → ℝ),
        Fintype.card {i // ∃ a b,
          (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (n+3)) θ).eigenvalues i =
            F a + v b} ≤ k + q + 1 := by
  filter_upwards [maximallyProjectiveEnergy_chainShell_ae n] with θ hθ
  intro k q F v
  have h := maximallyProjective_detuningCoverage _ hθ F v
  simp only [Fintype.card_fin] at h
  omega

/-- All choices of model eigenbasis, energy labels, and selected echo
frequencies share the same almost-sure trace-mass bound on the local chain. -/
theorem chainShell_selectedEchoWeight_ae (n : ℕ) :
    ∀ᵐ θ ∂(shellProbability (Fin (Fintype.card (ChainLabel (n+3))))),
      ∀ k q : ℕ, ∀ (V : Matrix.unitaryGroup (Fin (2^(n+3))) ℂ)
        (g : Fin (2^(n+3)) → Fin (k+1)) (F : Fin (k+1) → ℝ) (v : Fin (q+1) → ℝ),
        selectedEchoWeight
          (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (n+3)) θ).eigenvalues
          V g F v ≤ ((k + q + 1 : ℕ) : ℝ) := by
  filter_upwards [chainShell_detuningCoverage_ae n] with θ hθ
  intro k q V g F v
  exact (selectedEchoWeight_le_covered _ V g F v).trans (by exact_mod_cast hθ k q F v)

#print axioms chainShell_selectedEchoWeight_ae

end
end GaloisForLFunctions.HTGeometry
