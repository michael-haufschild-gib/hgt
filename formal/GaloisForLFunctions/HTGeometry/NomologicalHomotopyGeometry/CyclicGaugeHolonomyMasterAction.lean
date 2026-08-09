import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.CyclicActionNoether

set_option maxHeartbeats 200000

/-!
# Cyclic gauge holonomy and master action

Time-dependent formal gauge generators are integrated coefficientwise by an explicit Picard
recursion.  Existence and uniqueness are proved for the complete formal series, so every finite
filtration quotient sees the same compatible solution.  The remaining sections prove conjugation
covariance of the square-zero law and deformation differential, stabilizer-valued endpoints of
closed law paths, cyclic action covariance, and the Hamiltonian master equation.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.CyclicGaugeHolonomyMasterAction

open CyclicAInfinityLaw.QGeometry

variable {C : Type*} [AddCommGroup C] [Module ℝ C]

abbrev End := Module.End ℝ C

section PicardIntegration

/-- `n`th coefficient of the noncommutative product of two formal operator series. -/
def convolution (A B : ℕ → End (C := C)) (n : ℕ) : End (C := C) :=
  ∑ i ∈ Finset.range (n + 1), (A i).comp (B (n - i))

/-- Finite recursive approximation containing coefficients through order `n`. -/
noncomputable def picardApprox (ξ : ℕ → End (C := C)) : ℕ → ℕ → End (C := C)
  | 0 => Function.update (fun _ => 0) 0 LinearMap.id
  | n + 1 =>
      let previous := picardApprox ξ n
      Function.update previous (n + 1)
        ((n + 1 : ℝ)⁻¹ •
          ∑ i ∈ Finset.range (n + 1), (ξ i).comp (previous (n - i)))

/-- Coefficientwise Picard solution of `F' = ξF`, `F(0)=1`. -/
noncomputable def picardSolution (ξ : ℕ → End (C := C)) (n : ℕ) : End (C := C) :=
  picardApprox ξ n n

/-- Once constructed, a lower Picard coefficient is unchanged at every later stage. -/
theorem picardApprox_stable (ξ : ℕ → End (C := C)) {k n : ℕ} (hkn : k ≤ n) :
    picardApprox ξ n k = picardSolution ξ k := by
  induction n with
  | zero =>
      have hk : k = 0 := Nat.eq_zero_of_le_zero hkn
      subst k
      rfl
  | succ n ih =>
      by_cases hk : k = n + 1
      · subst k
        rfl
      · have hle : k ≤ n := Nat.lt_succ_iff.mp (lt_of_le_of_ne hkn hk)
        simpa [picardApprox, hk] using ih hle

@[simp]
theorem picardSolution_zero (ξ : ℕ → End (C := C)) :
    picardSolution ξ 0 = LinearMap.id := by
  simp [picardSolution, picardApprox]

/-- Coefficient recurrence equivalent to the formal gauge ODE. -/
theorem picardSolution_succ (ξ : ℕ → End (C := C)) (n : ℕ) :
    picardSolution ξ (n + 1) =
      (n + 1 : ℝ)⁻¹ • convolution ξ (picardSolution ξ) n := by
  rw [picardSolution, picardApprox]
  simp only [Function.update_self, convolution]
  apply congrArg
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  apply picardApprox_stable
  exact Nat.sub_le n i

/-- Formal coefficientwise solution predicate for a time-dependent gauge generator. -/
structure SolvesGaugeODE (ξ F : ℕ → End (C := C)) : Prop where
  initial : F 0 = LinearMap.id
  recurrence : ∀ n,
    F (n + 1) = (n + 1 : ℝ)⁻¹ • convolution ξ F n

/-- Picard coefficients solve the formal gauge ODE. -/
theorem picardSolution_solves (ξ : ℕ → End (C := C)) :
    SolvesGaugeODE ξ (picardSolution ξ) :=
  ⟨picardSolution_zero ξ, picardSolution_succ ξ⟩

/-- Coefficientwise uniqueness of the Picard solution. -/
theorem gaugeODE_unique (ξ F G : ℕ → End (C := C))
    (hF : SolvesGaugeODE ξ F) (hG : SolvesGaugeODE ξ G) : F = G := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => rw [hF.initial, hG.initial]
      | succ n =>
          rw [hF.recurrence, hG.recurrence]
          apply congrArg
          unfold convolution
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          exact ih (n - i) (Nat.lt_succ_of_le (Nat.sub_le n i))

/-- Every filtration-continuous formal generator has one coefficientwise Picard solution. -/
theorem gaugeODE_existsUnique (ξ : ℕ → End (C := C)) :
    ∃! F, SolvesGaugeODE ξ F :=
  ⟨picardSolution ξ, picardSolution_solves ξ,
    fun G hG => gaugeODE_unique ξ G (picardSolution ξ) hG (picardSolution_solves ξ)⟩

end PicardIntegration

section GaugeCovariance

/-- Conjugation by a structured formal coordinate change. -/
def conjugate (F : C ≃ₗ[ℝ] C) (D : End (C := C)) : End (C := C) :=
  (F.toLinearMap.comp D).comp F.symm.toLinearMap

/-- Conjugation preserves composition. -/
theorem conjugate_comp (F : C ≃ₗ[ℝ] C) (D E : End (C := C)) :
    conjugate F (D.comp E) = (conjugate F D).comp (conjugate F E) := by
  apply LinearMap.ext
  intro x
  simp [conjugate, LinearMap.comp_apply]

/-- Gauge conjugation preserves and reflects the square-zero law equation. -/
theorem conjugate_square_zero_iff (F : C ≃ₗ[ℝ] C) (Q : End (C := C)) :
    square (conjugate F Q) = 0 ↔ square Q = 0 := by
  rw [square, square, ← conjugate_comp]
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun h (F x)
    simpa [conjugate, LinearMap.comp_apply] using hx
  · intro h
    rw [h]
    apply LinearMap.ext
    intro x
    simp [conjugate]

/-- Adjoint transport intertwines the even gauge-anchor differential. -/
theorem conjugate_dEven (F : C ≃ₗ[ℝ] C) (Q D : End (C := C)) :
    conjugate F (dEven Q D) = dEven (conjugate F Q) (conjugate F D) := by
  apply LinearMap.ext
  intro x
  simp [conjugate, dEven, LinearMap.comp_apply]

/-- Adjoint transport intertwines the odd deformation differential. -/
theorem conjugate_dOdd (F : C ≃ₗ[ℝ] C) (Q D : End (C := C)) :
    conjugate F (dOdd Q D) = dOdd (conjugate F Q) (conjugate F D) := by
  apply LinearMap.ext
  intro x
  simp [conjugate, dOdd, LinearMap.comp_apply]

/-- Structured stabilizer of a cyclic law. -/
def stabilizer (Q : End (C := C)) : Set (C ≃ₗ[ℝ] C) :=
  {F | conjugate F Q = Q}

/-- Endpoint of a lifted closed law-orbit path lies in the structured stabilizer. -/
theorem closed_law_endpoint_mem_stabilizer
    (Q : End (C := C)) (F₁ : C ≃ₗ[ℝ] C)
    (hclosed : conjugate F₁ Q = Q) :
    F₁ ∈ stabilizer Q :=
  hclosed

/-- A stabilizer path projects to a closed law-orbit path. -/
structure StabilizerPath (Q : End (C := C)) where
  gauge : ℝ → C ≃ₗ[ℝ] C
  start : gauge 0 = LinearEquiv.refl ℝ C
  endpoint_stabilizes : gauge 1 ∈ stabilizer Q

/-- The projected endpoint of every stabilizer path is the original law. -/
theorem stabilizerPath_closes {Q : End (C := C)} (P : StabilizerPath Q) :
    conjugate (P.gauge 1) Q = Q :=
  P.endpoint_stabilizes

end GaugeCovariance

section MasterAction

variable {L M : Type*} [AddCommGroup L] [Module ℝ L]
  [AddCommGroup M] [Module ℝ M]

open CyclicActionNoether

/-- Cyclic coordinate changes pull back every finite-arity source-derived action exactly. -/
theorem actionTerm_natural
    {A : CyclicOperations (k := ℝ) (L := L)}
    {B : CyclicOperations (k := ℝ) (L := M)}
    (F : CyclicOperationsEquiv A B) (n : PositiveNat) (α : L) :
    actionTerm B n (F.map α) = actionTerm A n α := by
  rw [actionTerm, actionTerm, F.ell_natural, F.pairing_natural]

/-- Gauge covariance of the complete action at every finite arity quotient. -/
theorem actionPartial_natural
    {A : CyclicOperations (k := ℝ) (L := L)}
    {B : CyclicOperations (k := ℝ) (L := M)}
    (F : CyclicOperationsEquiv A B) (N : ℕ) (α : L) :
    actionPartial B N (F.map α) = actionPartial A N α := by
  rw [actionPartial, actionPartial]
  apply Finset.sum_congr rfl
  intro i _
  exact actionTerm_natural F ⟨i.1 + 1, Nat.succ_pos i.1⟩ α

/-- Hamiltonian realization of cyclic coderivations. -/
structure HamiltonianCorrespondence (H : Type*)
    [AddCommGroup H] [Module ℝ H] where
  hamiltonian : End (C := C) →ₗ[ℝ] H
  injective : Function.Injective hamiltonian
  poisson : H →ₗ[ℝ] H →ₗ[ℝ] H
  bracket_compat : ∀ D E,
    poisson (hamiltonian D) (hamiltonian E) = hamiltonian (oddBracket D E)

namespace HamiltonianCorrespondence

variable {H : Type*} [AddCommGroup H] [Module ℝ H]
variable (A : HamiltonianCorrespondence (C := C) H)

/-- Odd self-supercommutator is twice the composition square. -/
theorem oddBracket_self_eq_two_smul_square (Q : End (C := C)) :
    oddBracket Q Q = (2 : ℝ) • square Q := by
  apply LinearMap.ext
  intro x
  simp [oddBracket, square, LinearMap.comp_apply, two_smul]

/-- Classical master equation is equivalent to the source law equation. -/
theorem masterEquation_iff_square_zero (Q : End (C := C)) :
    A.poisson (A.hamiltonian Q) (A.hamiltonian Q) = 0 ↔ square Q = 0 := by
  rw [A.bracket_compat, oddBracket_self_eq_two_smul_square, map_smul]
  constructor
  · intro h
    have htwo : (2 : ℝ) • A.hamiltonian (square Q) = 0 := h
    have hz : A.hamiltonian (square Q) = 0 := by
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    exact A.injective (hz.trans (map_zero A.hamiltonian).symm)
  · intro h
    rw [h, map_zero, smul_zero]

end HamiltonianCorrespondence

end MasterAction

end HTGeometry.NomologicalHomotopyGeometry.CyclicGaugeHolonomyMasterAction
