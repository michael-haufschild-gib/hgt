import GaloisForLFunctions.HTGeometry.TwoControlHermitianObserverTimeSharpness

/-!
# A nonredundant two-control Hermitian observer-time packet

The first two-control witness uses parallel copies of one transverse
interaction and attains the cardinality lower bound.  This file removes the
possible control-redundancy objection: one control is transverse and the
other is a diagonal level shift.  These Hermitian matrices are linearly
independent, yet their joint Möbius spectral packet is still a nonzero germ.

The exact characteristic relation is

`w^(2 : ℕ) - (1 + z₁) w + z₁ - z₀^(2 : ℕ) = 0`.

The diagonal-only branch is exactly `z₁` near zero.  If the joint packet
vanished, the full branch on `(t,t)` would equal the transverse-only branch
plus `t`; the two characteristic equations would then force every small
`t` to vanish, a contradiction.
-/

open Filter Topology
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

open FiniteLocalInteractionFamily

/-- Linearly independent transverse and diagonal Hermitian controls. -/
def twoControlIndependentInteraction :
    Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; 1, 0], !![1, 0; 0, 0]]

noncomputable def twoControlIndependentMatrix (z : Fin 2 → ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  affineMatrixFamily
    (Matrix.diagonal twoControlSharpEnergy)
    twoControlIndependentInteraction z

@[simp]
theorem twoControlIndependentMatrix_zero :
    twoControlIndependentMatrix 0 =
      Matrix.diagonal twoControlSharpEnergy := by
  simp [twoControlIndependentMatrix, affineMatrixFamily]

theorem twoControlIndependentMatrix_analyticAt :
    AnalyticAt ℂ twoControlIndependentMatrix 0 := by
  exact affineMatrixFamily_analyticAt
    (Matrix.diagonal twoControlSharpEnergy)
    twoControlIndependentInteraction 0

theorem twoControlIndependentMatrix_isHermitian_real
    (z : Fin 2 → ℝ) :
    (twoControlIndependentMatrix (fun e => (z e : ℂ))).IsHermitian := by
  unfold twoControlIndependentMatrix affineMatrixFamily
  apply Matrix.IsHermitian.add
  · rw [Matrix.isHermitian_diagonal_iff]
    intro i
    fin_cases i <;>
      simp [twoControlSharpEnergy, isSelfAdjoint_iff]
  · apply Finset.sum_induction
      (fun e : Fin 2 =>
        (z e : ℂ) • twoControlIndependentInteraction e)
      (fun M => M.IsHermitian)
      (fun M N hM hN => hM.add hN)
      Matrix.isHermitian_zero
    intro e he
    apply Matrix.IsHermitian.smul
    · ext i j
      fin_cases e <;> fin_cases i <;> fin_cases j <;>
        simp [twoControlIndependentInteraction]
    · rw [isSelfAdjoint_iff]
      simp

theorem twoControlIndependent_relation
    (z : Fin 2 → ℂ) (w : ℂ) :
    matrixCharpolyRelation (twoControlIndependentMatrix z, w) =
      w ^ (2 : ℕ) - (1 + z 1) * w + z 1 - (z 0) ^ (2 : ℕ) := by
  simp [matrixCharpolyRelation, twoControlIndependentMatrix,
    affineMatrixFamily, twoControlIndependentInteraction,
    twoControlSharpEnergy, Matrix.det_fin_two]
  ring

/-- Eigenvalue branch through zero for the nonredundant family. -/
noncomputable def twoControlIndependentBranch (z : Fin 2 → ℂ) : ℂ :=
  twoControlSharpMatrixBranch (twoControlIndependentMatrix z)

theorem twoControlIndependentBranch_analyticAt :
    AnalyticAt ℂ twoControlIndependentBranch 0 := by
  exact twoControlSharpMatrixBranch_spec.1.fun_comp_of_eq
    twoControlIndependentMatrix_analyticAt
    twoControlIndependentMatrix_zero

@[simp]
theorem twoControlIndependentBranch_zero :
    twoControlIndependentBranch 0 = 0 := by
  rw [twoControlIndependentBranch, twoControlIndependentMatrix_zero]
  exact twoControlSharpMatrixBranch_spec.2.1

theorem twoControlIndependentBranch_relation :
    ∀ᶠ z : Fin 2 → ℂ in 𝓝 0,
      twoControlIndependentBranch z ^ (2 : ℕ) -
        (1 + z 1) * twoControlIndependentBranch z +
        z 1 - (z 0) ^ (2 : ℕ) = 0 := by
  have ht := twoControlIndependentMatrix_analyticAt.continuousAt
  change Tendsto twoControlIndependentMatrix (𝓝 0)
    (𝓝 (twoControlIndependentMatrix 0)) at ht
  rw [twoControlIndependentMatrix_zero] at ht
  filter_upwards
    [ht.eventually twoControlSharpMatrixBranch_spec.2.2] with z hz
  rw [twoControlIndependent_relation] at hz
  exact hz

/-- With only the diagonal control active, the selected branch is exactly
that diagonal control near zero. -/
theorem twoControlIndependentRightBranch_eq :
    ∀ᶠ t : ℂ in 𝓝 0,
      twoControlIndependentBranch (twoControlSharpRightRay t) = t := by
  have hroot :=
    twoControlSharpRightRay_tendsto.eventually
      twoControlIndependentBranch_relation
  have hcont :
      Tendsto
        (fun t : ℂ =>
          twoControlIndependentBranch (twoControlSharpRightRay t))
        (𝓝 0) (𝓝 0) := by
    have hbranch :=
      twoControlIndependentBranch_analyticAt.continuousAt
    simpa [Function.comp_def] using
      hbranch.tendsto.comp twoControlSharpRightRay_tendsto
  have hopen : IsOpen ({1}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
  have hmem : (0 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hne : ∀ᶠ t : ℂ in 𝓝 0,
      twoControlIndependentBranch (twoControlSharpRightRay t) ≠ 1 :=
    hcont.eventually (hopen.mem_nhds hmem)
  filter_upwards [hroot, hne] with t ht hnot
  have hfactor :
      (twoControlIndependentBranch (twoControlSharpRightRay t) - t) *
        (twoControlIndependentBranch (twoControlSharpRightRay t) - 1) = 0 := by
    calc
      _ = twoControlIndependentBranch (twoControlSharpRightRay t) ^ (2 : ℕ) -
          (1 + t) *
            twoControlIndependentBranch (twoControlSharpRightRay t) +
          t := by ring
      _ = 0 := by
        simpa [twoControlSharpRightRay] using ht
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hfactor).resolve_right (sub_ne_zero.mpr hnot))

/-- **Nonredundant two-control witness.**  A transverse coupling and a
linearly independent diagonal level control have a nonzero joint spectral
packet.  Irreducible observer-time layers therefore persist after removing
the parallel-control artifact. -/
theorem twoControlIndependent_packetResponse_ne_zero :
    ¬spectralPacketResponse twoControlIndependentBranch
        ({0, 1} : Finset (Fin 2)) =ᶠ[𝓝 0]
      (fun _ : Fin 2 → ℂ => 0) := by
  intro hzero
  have hmobius := hzero.comp_tendsto twoControlSharpBothRay_tendsto
  have hrootBoth :=
    twoControlSharpBothRay_tendsto.eventually
      twoControlIndependentBranch_relation
  have hrootLeft :=
    twoControlSharpLeftRay_tendsto.eventually
      twoControlIndependentBranch_relation
  have hright := twoControlIndependentRightBranch_eq
  have hforced : ∀ᶠ t : ℂ in 𝓝 0, t = 0 := by
    filter_upwards [hmobius, hrootBoth, hrootLeft, hright]
      with t hm hb hl hr
    change spectralPacketResponse twoControlIndependentBranch
      ({0, 1} : Finset (Fin 2)) (twoControlSharpBothRay t) = 0 at hm
    have hadd :
        twoControlIndependentBranch (twoControlSharpBothRay t) =
          twoControlIndependentBranch (twoControlSharpLeftRay t) + t := by
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
      have hright' :
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
      rw [hfull, hleft, hright', hempty,
        twoControlIndependentBranch_zero, hr] at hm
      linear_combination hm
    have hb' :
        twoControlIndependentBranch (twoControlSharpBothRay t) ^ (2 : ℕ) -
          (1 + t) *
            twoControlIndependentBranch (twoControlSharpBothRay t) +
          t - t ^ (2 : ℕ) = 0 := by
      simpa [twoControlSharpBothRay] using hb
    have hl' :
        twoControlIndependentBranch (twoControlSharpLeftRay t) ^ (2 : ℕ) -
          twoControlIndependentBranch (twoControlSharpLeftRay t) -
          t ^ (2 : ℕ) = 0 := by
      simpa [twoControlSharpLeftRay] using hl
    rw [hadd] at hb'
    have hproduct :
        twoControlIndependentBranch (twoControlSharpLeftRay t) * t = 0 := by
      linear_combination hb' - hl'
    rcases mul_eq_zero.mp hproduct with ha | ht
    · have hz : t ^ (2 : ℕ) = 0 := by
        rw [ha] at hl'
        simpa using hl'.symm
      exact sq_eq_zero_iff.mp hz
    · exact ht
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
