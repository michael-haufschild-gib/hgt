import GaloisForLFunctions.RHTower.FZZCigarPunctureTwoChannelBarePencilNoGo

/-!
# FZZ puncture finite-dimensional bare-pencil no-go

Hardy's theorem supplies a real Xi zero above every height.  This file packages those choices into
a strictly increasing sequence of positive real `XiC` zeros and hence into injective zero packets
of every finite size.

For a fixed `N`-dimensional interior endomorphism, modes at distinct bare-pencil energies are
eigenvectors at distinct eigenvalues and therefore linearly independent.  Xi-completeness would
produce `N+1` such vectors in `ℂ^N`.  This contradiction is independent of selfadjointness,
normality, coupling rank, and even the detailed dark equation.

`[NEW] [ALL-FINITE-DIMENSION NO-GO] [POSITIVE SURVIVOR] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Canonical choice sequence of successively higher positive Hardy zeros. -/
noncomputable def hardyXiPositiveZeroSequence : ℕ → ℝ
  | 0 => Classical.choose (exists_Xi_zero_gt 0)
  | n + 1 => Classical.choose (exists_Xi_zero_gt (hardyXiPositiveZeroSequence n))

/-- First chosen Hardy zero is positive. -/
theorem hardyXiPositiveZeroSequence_zero_pos :
    0 < hardyXiPositiveZeroSequence 0 := by
  exact (Classical.choose_spec (exists_Xi_zero_gt 0)).1

/-- Every chosen Hardy zero lies strictly below its successor. -/
theorem hardyXiPositiveZeroSequence_lt_succ (n : ℕ) :
    hardyXiPositiveZeroSequence n < hardyXiPositiveZeroSequence (n + 1) := by
  exact (Classical.choose_spec
    (exists_Xi_zero_gt (hardyXiPositiveZeroSequence n))).1

/-- The chosen Hardy zero sequence is strictly increasing. -/
theorem hardyXiPositiveZeroSequence_strictMono :
    StrictMono hardyXiPositiveZeroSequence :=
  strictMono_nat_of_lt_succ hardyXiPositiveZeroSequence_lt_succ

/-- Every chosen Hardy zero is positive. -/
theorem hardyXiPositiveZeroSequence_pos (n : ℕ) :
    0 < hardyXiPositiveZeroSequence n := by
  rcases n with _ | n
  · exact hardyXiPositiveZeroSequence_zero_pos
  · exact lt_trans hardyXiPositiveZeroSequence_zero_pos
      (hardyXiPositiveZeroSequence_strictMono (Nat.zero_lt_succ n))

/-- Every chosen point is a zero of the real Hardy detector. -/
theorem Xi_hardyXiPositiveZeroSequence_eq_zero (n : ℕ) :
    Xi (hardyXiPositiveZeroSequence n) = 0 := by
  rcases n with _ | n
  · exact (Classical.choose_spec (exists_Xi_zero_gt 0)).2
  · exact (Classical.choose_spec
      (exists_Xi_zero_gt (hardyXiPositiveZeroSequence n))).2

/-- Every chosen point is a positive real zero of centered completed `XiC`. -/
theorem XiC_hardyXiPositiveZeroSequence_eq_zero (n : ℕ) :
    XiC (hardyXiPositiveZeroSequence n : ℂ) = 0 := by
  rw [XiC_ofReal, Xi_hardyXiPositiveZeroSequence_eq_zero]
  norm_num

/-- Unconditional injective packets of positive real `XiC` zeros of every finite size. -/
theorem exists_injective_positive_real_XiC_zero_packet (n : ℕ) :
    ∃ E : Fin n → ℝ,
      (∀ i, 0 < E i) ∧ Function.Injective E ∧
        ∀ i, XiC (E i : ℂ) = 0 := by
  refine ⟨fun i => hardyXiPositiveZeroSequence (i : ℕ), ?_, ?_, ?_⟩
  · exact fun i => hardyXiPositiveZeroSequence_pos (i : ℕ)
  · intro i j hij
    exact Fin.ext (hardyXiPositiveZeroSequence_strictMono.injective hij)
  · exact fun i => XiC_hardyXiPositiveZeroSequence_eq_zero (i : ℕ)

/-- Nonzero eigenvector of a fixed finite interior pencil lying in a fixed coupling kernel. -/
def FZZPunctureFiniteBareDarkEigenmode
    {N Q : ℕ} (A : Module.End ℂ (Fin N → ℂ))
    (K : (Fin N → ℂ) →ₗ[ℂ] (Fin Q → ℂ)) (E : ℝ) : Prop :=
  ∃ x : Fin N → ℂ, A.HasEigenvector (E : ℂ) x ∧ K x = 0

/-- Proposed completeness of one fixed finite bare pencil for every positive real `XiC` zero. -/
def FZZPunctureFiniteBarePencilXiComplete
    {N Q : ℕ} (A : Module.End ℂ (Fin N → ℂ))
    (K : (Fin N → ℂ) →ₗ[ℂ] (Fin Q → ℂ)) : Prop :=
  ∀ E : ℝ, 0 < E → XiC (E : ℂ) = 0 →
    FZZPunctureFiniteBareDarkEigenmode A K E

/-- No fixed finite-dimensional bare FZZ pencil can be Xi-complete. -/
theorem not_fzzPunctureFiniteBarePencilXiComplete
    {N Q : ℕ} (A : Module.End ℂ (Fin N → ℂ))
    (K : (Fin N → ℂ) →ₗ[ℂ] (Fin Q → ℂ)) :
    ¬ FZZPunctureFiniteBarePencilXiComplete A K := by
  intro hcomplete
  let E : Fin (N + 1) → ℝ := fun i => hardyXiPositiveZeroSequence (i : ℕ)
  have hmodes : ∀ i : Fin (N + 1),
      ∃ x : Fin N → ℂ, A.HasEigenvector (E i : ℂ) x ∧ K x = 0 := by
    intro i
    exact hcomplete (E i)
      (hardyXiPositiveZeroSequence_pos (i : ℕ))
      (XiC_hardyXiPositiveZeroSequence_eq_zero (i : ℕ))
  let v : Fin (N + 1) → (Fin N → ℂ) := fun i => Classical.choose (hmodes i)
  have hv : ∀ i : Fin (N + 1), A.HasEigenvector (E i : ℂ) (v i) := by
    intro i
    exact (Classical.choose_spec (hmodes i)).1
  have hE : Function.Injective (fun i : Fin (N + 1) => (E i : ℂ)) := by
    intro i j hij
    apply Fin.ext
    apply hardyXiPositiveZeroSequence_strictMono.injective
    exact Complex.ofReal_injective hij
  have hLI : LinearIndependent ℂ v :=
    A.eigenvectors_linearIndependent' (fun i : Fin (N + 1) => (E i : ℂ)) hE v hv
  have hcard := hLI.fintype_card_le_finrank
  simp at hcard

end

end RHTower
