import GaloisForLFunctions.HTGeometry.LocalObserverTimeGapBirthLaw

/-!
# A nontrivial Hermitian observer-time packet

The connected packet filtration is not only a vanishing theorem.  This file
exhibits a two-level Hermitian family with two independently switchable
controls whose joint two-control spectral packet is a nonzero analytic germ.

Both controls multiply the same off-diagonal Hermitian interaction.  The
selected eigenvalue branch through zero obeys

`w^(2 : ℕ) - w - (z₀ + z₁)^(2 : ℕ) = 0`.

If its two-control Möbius packet vanished, restriction to the diagonal
coupling ray would force that branch to vanish on a neighbourhood of zero,
and hence would force every sufficiently small coupling to be zero.  This is
impossible.  Thus a genuinely joint observer-time layer already occurs in the
smallest nontrivial Hermitian system.
-/

open Filter Topology
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

open FiniteLocalInteractionFamily

/-- Uncoupled two-level spectrum. -/
def twoControlSharpEnergy : Fin 2 → ℂ := ![0, 1]

/-- Each independently switchable channel carries the Pauli-X interaction. -/
def twoControlSharpInteraction (_ : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- Two-control Hermitian matrix family. -/
noncomputable def twoControlSharpMatrix (z : Fin 2 → ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  affineMatrixFamily
    (Matrix.diagonal twoControlSharpEnergy)
    twoControlSharpInteraction z

theorem twoControlSharpEnergy_injective :
    Function.Injective twoControlSharpEnergy := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [twoControlSharpEnergy] at hij ⊢

@[simp]
theorem twoControlSharpMatrix_zero :
    twoControlSharpMatrix 0 =
      Matrix.diagonal twoControlSharpEnergy := by
  simp [twoControlSharpMatrix, affineMatrixFamily]

theorem twoControlSharpMatrix_analyticAt :
    AnalyticAt ℂ twoControlSharpMatrix 0 := by
  exact affineMatrixFamily_analyticAt
    (Matrix.diagonal twoControlSharpEnergy)
    twoControlSharpInteraction 0

/-- Real controls give a Hermitian Hamiltonian. -/
theorem twoControlSharpMatrix_isHermitian_real
    (z : Fin 2 → ℝ) :
    (twoControlSharpMatrix (fun e => (z e : ℂ))).IsHermitian := by
  unfold twoControlSharpMatrix affineMatrixFamily
  apply Matrix.IsHermitian.add
  · rw [Matrix.isHermitian_diagonal_iff]
    intro i
    fin_cases i <;>
      simp [twoControlSharpEnergy, isSelfAdjoint_iff]
  · apply Finset.sum_induction
      (fun e : Fin 2 =>
        (z e : ℂ) • twoControlSharpInteraction e)
      (fun M => M.IsHermitian)
      (fun M N hM hN => hM.add hN)
      Matrix.isHermitian_zero
    intro e he
    apply Matrix.IsHermitian.smul
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [twoControlSharpInteraction]
    · rw [isSelfAdjoint_iff]
      simp

/-- Exact characteristic equation of the family. -/
theorem twoControlSharp_relation
    (z : Fin 2 → ℂ) (w : ℂ) :
    matrixCharpolyRelation (twoControlSharpMatrix z, w) =
      w ^ (2 : ℕ) - w - (z 0 + z 1) ^ (2 : ℕ) := by
  simp [matrixCharpolyRelation, twoControlSharpMatrix,
    affineMatrixFamily, twoControlSharpInteraction,
    twoControlSharpEnergy, Matrix.det_fin_two]
  ring

/-- Canonical local eigenvalue branch through the uncoupled energy zero. -/
noncomputable def twoControlSharpMatrixBranch :
    Matrix (Fin 2) (Fin 2) ℂ → ℂ :=
  Classical.choose
    (simpleDiagonalMatrix_eigenvalueBranch
      twoControlSharpEnergy twoControlSharpEnergy_injective 0)

theorem twoControlSharpMatrixBranch_spec :
    AnalyticAt ℂ twoControlSharpMatrixBranch
        (Matrix.diagonal twoControlSharpEnergy) ∧
      twoControlSharpMatrixBranch
          (Matrix.diagonal twoControlSharpEnergy) = 0 ∧
      ∀ᶠ H in 𝓝 (Matrix.diagonal twoControlSharpEnergy),
        matrixCharpolyRelation
          (H, twoControlSharpMatrixBranch H) = 0 := by
  simpa [twoControlSharpMatrixBranch, twoControlSharpEnergy] using
    Classical.choose_spec
      (simpleDiagonalMatrix_eigenvalueBranch
        twoControlSharpEnergy twoControlSharpEnergy_injective 0)

/-- Selected eigenvalue as a function of the two controls. -/
noncomputable def twoControlSharpBranch (z : Fin 2 → ℂ) : ℂ :=
  twoControlSharpMatrixBranch (twoControlSharpMatrix z)

theorem twoControlSharpBranch_analyticAt :
    AnalyticAt ℂ twoControlSharpBranch 0 := by
  exact twoControlSharpMatrixBranch_spec.1.fun_comp_of_eq
    twoControlSharpMatrix_analyticAt twoControlSharpMatrix_zero

@[simp]
theorem twoControlSharpBranch_zero :
    twoControlSharpBranch 0 = 0 := by
  rw [twoControlSharpBranch, twoControlSharpMatrix_zero]
  exact twoControlSharpMatrixBranch_spec.2.1

/-- The selected analytic branch satisfies the exact quadratic relation near
the uncoupled point. -/
theorem twoControlSharpBranch_relation :
    ∀ᶠ z : Fin 2 → ℂ in 𝓝 0,
      twoControlSharpBranch z ^ (2 : ℕ) -
        twoControlSharpBranch z -
        (z 0 + z 1) ^ (2 : ℕ) = 0 := by
  have ht := twoControlSharpMatrix_analyticAt.continuousAt
  change Tendsto twoControlSharpMatrix (𝓝 0)
    (𝓝 (twoControlSharpMatrix 0)) at ht
  rw [twoControlSharpMatrix_zero] at ht
  filter_upwards
    [ht.eventually twoControlSharpMatrixBranch_spec.2.2] with z hz
  rw [twoControlSharp_relation] at hz
  exact hz

def twoControlSharpBothRay (t : ℂ) : Fin 2 → ℂ := ![t, t]
def twoControlSharpLeftRay (t : ℂ) : Fin 2 → ℂ := ![t, 0]
def twoControlSharpRightRay (t : ℂ) : Fin 2 → ℂ := ![0, t]

theorem twoControlSharpBothRay_tendsto :
    Tendsto twoControlSharpBothRay (𝓝 0) (𝓝 0) := by
  apply tendsto_pi_nhds.2
  intro i
  fin_cases i <;>
    simpa [twoControlSharpBothRay] using!
      (tendsto_id : Tendsto (fun t : ℂ => t) (𝓝 0) (𝓝 0))

theorem twoControlSharpLeftRay_tendsto :
    Tendsto twoControlSharpLeftRay (𝓝 0) (𝓝 0) := by
  apply tendsto_pi_nhds.2
  intro i
  fin_cases i
  · simpa [twoControlSharpLeftRay] using!
      (tendsto_id : Tendsto (fun t : ℂ => t) (𝓝 0) (𝓝 0))
  · simp [twoControlSharpLeftRay]

theorem twoControlSharpRightRay_tendsto :
    Tendsto twoControlSharpRightRay (𝓝 0) (𝓝 0) := by
  apply tendsto_pi_nhds.2
  intro i
  fin_cases i
  · simp [twoControlSharpRightRay]
  · simpa [twoControlSharpRightRay] using!
      (tendsto_id : Tendsto (fun t : ℂ => t) (𝓝 0) (𝓝 0))

@[simp]
theorem twoControlSharpMatrix_left_eq_right (t : ℂ) :
    twoControlSharpMatrix (twoControlSharpLeftRay t) =
      twoControlSharpMatrix (twoControlSharpRightRay t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoControlSharpMatrix, affineMatrixFamily,
      twoControlSharpInteraction, twoControlSharpEnergy,
      twoControlSharpLeftRay, twoControlSharpRightRay]

/-- **Nontrivial two-control sharpness witness.**  The joint spectral packet
of this explicit two-level Hermitian family is not the zero analytic germ.
Thus the second connected layer of the observer-time birth filtration can be
physically active and cannot in general be deleted. -/
theorem twoControlSharp_packetResponse_ne_zero :
    ¬spectralPacketResponse twoControlSharpBranch
        ({0, 1} : Finset (Fin 2)) =ᶠ[𝓝 0]
      (fun _ : Fin 2 → ℂ => 0) := by
  intro hzero
  have hmobius := hzero.comp_tendsto twoControlSharpBothRay_tendsto
  have hrootBoth :=
    twoControlSharpBothRay_tendsto.eventually
      twoControlSharpBranch_relation
  have hrootLeft :=
    twoControlSharpLeftRay_tendsto.eventually
      twoControlSharpBranch_relation
  have hsame : ∀ t : ℂ,
      twoControlSharpBranch (twoControlSharpLeftRay t) =
        twoControlSharpBranch (twoControlSharpRightRay t) := by
    intro t
    unfold twoControlSharpBranch
    rw [twoControlSharpMatrix_left_eq_right]
  have hforced : ∀ᶠ t : ℂ in 𝓝 0, t = 0 := by
    filter_upwards [hmobius, hrootBoth, hrootLeft] with t hm hb hl
    change spectralPacketResponse twoControlSharpBranch
      ({0, 1} : Finset (Fin 2)) (twoControlSharpBothRay t) = 0 at hm
    have hadd :
        twoControlSharpBranch (twoControlSharpBothRay t) =
          2 * twoControlSharpBranch (twoControlSharpLeftRay t) := by
      unfold spectralPacketResponse at hm
      rw [show ({0, 1} : Finset (Fin 2)) =
          insert 0 {1} by ext i; fin_cases i <;> simp] at hm
      rw [finsetMobiusResponse_insert (by simp)] at hm
      rw [show ({1} : Finset (Fin 2)) =
          insert 1 ∅ by ext i; fin_cases i <;> simp] at hm
      rw [finsetMobiusResponse_insert (by simp)] at hm
      rw [finsetMobiusResponse_insert (by simp)] at hm
      simp only [finsetMobiusResponse, Finset.powerset_empty,
        Finset.sum_singleton, Finset.card_empty, pow_zero, one_mul,
        Finset.sdiff_empty] at hm
      have hfull :
          restrictInteractionPacket
              (insert (0 : Fin 2) (insert (1 : Fin 2) ∅))
              (twoControlSharpBothRay t) =
            twoControlSharpBothRay t := by
        funext i
        fin_cases i <;>
          simp [restrictInteractionPacket, twoControlSharpBothRay]
      have hleft :
          restrictInteractionPacket
              (insert (0 : Fin 2) ∅)
              (twoControlSharpBothRay t) =
            twoControlSharpLeftRay t := by
        funext i
        fin_cases i <;>
          simp [restrictInteractionPacket, twoControlSharpBothRay,
            twoControlSharpLeftRay]
      have hright :
          restrictInteractionPacket
              (insert (1 : Fin 2) ∅)
              (twoControlSharpBothRay t) =
            twoControlSharpRightRay t := by
        funext i
        fin_cases i <;>
          simp [restrictInteractionPacket, twoControlSharpBothRay,
            twoControlSharpRightRay]
      have hempty :
          restrictInteractionPacket (∅ : Finset (Fin 2))
              (twoControlSharpBothRay t) = 0 := by
        funext i
        simp [restrictInteractionPacket]
      rw [hfull, hleft, hright, hempty,
        twoControlSharpBranch_zero] at hm
      calc
        twoControlSharpBranch (twoControlSharpBothRay t) =
            twoControlSharpBranch (twoControlSharpLeftRay t) +
              twoControlSharpBranch (twoControlSharpRightRay t) := by
          linear_combination hm
        _ = 2 * twoControlSharpBranch (twoControlSharpLeftRay t) := by
          rw [← hsame t]
          ring
    have hb' :
        twoControlSharpBranch (twoControlSharpBothRay t) ^ (2 : ℕ) -
          twoControlSharpBranch (twoControlSharpBothRay t) -
          (2 * t) ^ (2 : ℕ) = 0 := by
      convert hb using 1
      · simp [twoControlSharpBothRay]
        ring
    have hl' :
        twoControlSharpBranch (twoControlSharpLeftRay t) ^ (2 : ℕ) -
          twoControlSharpBranch (twoControlSharpLeftRay t) -
          t ^ (2 : ℕ) = 0 := by
      simpa [twoControlSharpLeftRay] using hl
    rw [hadd] at hb'
    have ha :
        twoControlSharpBranch (twoControlSharpLeftRay t) = 0 := by
      linear_combination (1 / 2 : ℂ) * hb' - 2 * hl'
    have hz : t ^ (2 : ℕ) = 0 := by
      rw [ha] at hl'
      simpa using hl'.symm
    exact sq_eq_zero_iff.mp hz
  rw [Metric.eventually_nhds_iff] at hforced
  obtain ⟨ε, hε, hball⟩ := hforced
  let t : ℂ := (ε / 2 : ℝ)
  have htball : t ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [t]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have htzero := hball htball
  have htne : t ≠ 0 := by
    intro ht
    have hreal : ε / 2 = 0 := by
      change ((ε / 2 : ℝ) : ℂ) = 0 at ht
      exact_mod_cast ht
    linarith
  exact htne htzero

end GaloisForLFunctions.HTGeometry
