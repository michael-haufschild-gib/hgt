import GaloisForLFunctions.HTGeometry.InteractionPacketHolonomyLaw
import GaloisForLFunctions.HTGeometry.TwoControlHermitianObserverTimeSharpness

/-!
# Three-control Hermitian cycle holonomy

This file proves that irreducible observer-time sectors are not confined to
two controls.  Three linearly independent Hermitian edge controls around a
qutrit cycle carry a nonzero joint spectral packet.

Every proper edge packet is a forest.  Flipping one edge sign is therefore a
spectral gauge transformation on every proper packet.  The closed cycle is
different: its characteristic equation contains the gauge-invariant
holonomy `z₀ z₁ z₂`.  Boolean packet projection cancels every proper forest
while retaining that closed-cycle obstruction.
-/

open Filter Topology
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

open FiniteLocalInteractionFamily

def threeControlCycleEnergy : Fin 3 → ℂ := ![0, 1, 2]

def threeControlCycleInteraction :
    Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![
    !![0, 1, 0; 1, 0, 0; 0, 0, 0],
    !![0, 0, 0; 0, 0, 1; 0, 1, 0],
    !![0, 0, 1; 0, 0, 0; 1, 0, 0]
  ]

noncomputable def threeControlCycleMatrix (z : Fin 3 → ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  affineMatrixFamily
    (Matrix.diagonal threeControlCycleEnergy)
    threeControlCycleInteraction z

theorem threeControlCycleEnergy_injective :
    Function.Injective threeControlCycleEnergy := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [threeControlCycleEnergy] at hij ⊢

@[simp]
theorem threeControlCycleMatrix_zero :
    threeControlCycleMatrix 0 =
      Matrix.diagonal threeControlCycleEnergy := by
  simp [threeControlCycleMatrix, affineMatrixFamily]

theorem threeControlCycleMatrix_analyticAt :
    AnalyticAt ℂ threeControlCycleMatrix 0 := by
  exact affineMatrixFamily_analyticAt
    (Matrix.diagonal threeControlCycleEnergy)
    threeControlCycleInteraction 0

theorem threeControlCycleMatrix_isHermitian_real
    (z : Fin 3 → ℝ) :
    (threeControlCycleMatrix (fun e => (z e : ℂ))).IsHermitian := by
  unfold threeControlCycleMatrix affineMatrixFamily
  apply Matrix.IsHermitian.add
  · rw [Matrix.isHermitian_diagonal_iff]
    intro i
    fin_cases i <;>
      simp [threeControlCycleEnergy, isSelfAdjoint_iff]
  · apply Finset.sum_induction
      (fun e : Fin 3 =>
        (z e : ℂ) • threeControlCycleInteraction e)
      (fun M => M.IsHermitian)
      (fun M N hM hN => hM.add hN)
      Matrix.isHermitian_zero
    intro e he
    apply Matrix.IsHermitian.smul
    · ext i j
      fin_cases e <;> fin_cases i <;> fin_cases j <;>
        simp [threeControlCycleInteraction]
    · rw [isSelfAdjoint_iff]
      simp

/-- Exact characteristic equation.  Its only term sensitive to one edge
sign is the closed-cycle holonomy `2 z₀ z₁ z₂`. -/
theorem threeControlCycle_relation
    (z : Fin 3 → ℂ) (w : ℂ) :
    matrixCharpolyRelation (threeControlCycleMatrix z, w) =
      w * ((w - 1) * (w - 2) - (z 1) ^ 2) -
        (z 0) ^ 2 * (w - 2) -
        (z 2) ^ 2 * (w - 1) -
        2 * z 0 * z 1 * z 2 := by
  simp [matrixCharpolyRelation, threeControlCycleMatrix,
    affineMatrixFamily, threeControlCycleInteraction,
    threeControlCycleEnergy, Matrix.det_fin_three, Fin.sum_univ_three]
  ring

noncomputable def threeControlCycleMatrixBranch :
    Matrix (Fin 3) (Fin 3) ℂ → ℂ :=
  Classical.choose
    (simpleDiagonalMatrix_eigenvalueBranch
      threeControlCycleEnergy threeControlCycleEnergy_injective 0)

theorem threeControlCycleMatrixBranch_spec :
    AnalyticAt ℂ threeControlCycleMatrixBranch
        (Matrix.diagonal threeControlCycleEnergy) ∧
      threeControlCycleMatrixBranch
          (Matrix.diagonal threeControlCycleEnergy) = 0 ∧
      ∀ᶠ H in 𝓝 (Matrix.diagonal threeControlCycleEnergy),
        matrixCharpolyRelation
          (H, threeControlCycleMatrixBranch H) = 0 := by
  simpa [threeControlCycleMatrixBranch, threeControlCycleEnergy] using
    Classical.choose_spec
      (simpleDiagonalMatrix_eigenvalueBranch
        threeControlCycleEnergy threeControlCycleEnergy_injective 0)

noncomputable def threeControlCycleBranch (z : Fin 3 → ℂ) : ℂ :=
  threeControlCycleMatrixBranch (threeControlCycleMatrix z)

theorem threeControlCycleBranch_analyticAt :
    AnalyticAt ℂ threeControlCycleBranch 0 := by
  exact threeControlCycleMatrixBranch_spec.1.fun_comp_of_eq
    threeControlCycleMatrix_analyticAt threeControlCycleMatrix_zero

@[simp]
theorem threeControlCycleBranch_zero :
    threeControlCycleBranch 0 = 0 := by
  rw [threeControlCycleBranch, threeControlCycleMatrix_zero]
  exact threeControlCycleMatrixBranch_spec.2.1

theorem threeControlCycleBranch_relation :
    ∀ᶠ z : Fin 3 → ℂ in 𝓝 0,
      threeControlCycleBranch z *
          ((threeControlCycleBranch z - 1) *
              (threeControlCycleBranch z - 2) -
            (z 1) ^ 2) -
        (z 0) ^ 2 * (threeControlCycleBranch z - 2) -
        (z 2) ^ 2 * (threeControlCycleBranch z - 1) -
        2 * z 0 * z 1 * z 2 = 0 := by
  have ht := threeControlCycleMatrix_analyticAt.continuousAt
  change Tendsto threeControlCycleMatrix (𝓝 0)
    (𝓝 (threeControlCycleMatrix 0)) at ht
  rw [threeControlCycleMatrix_zero] at ht
  filter_upwards
    [ht.eventually threeControlCycleMatrixBranch_spec.2.2] with z hz
  rw [threeControlCycle_relation] at hz
  exact hz

def threeControlCyclePositiveRay (t : ℂ) : Fin 3 → ℂ := ![t, t, t]
def threeControlCycleNegativeRay (t : ℂ) : Fin 3 → ℂ := ![-t, t, t]

def threeControlCyclePositiveActiveRay
    (active : Finset (Fin 3)) (t : ℂ) : Fin 3 → ℂ :=
  restrictInteractionPacket active (threeControlCyclePositiveRay t)

def threeControlCycleNegativeActiveRay
    (active : Finset (Fin 3)) (t : ℂ) : Fin 3 → ℂ :=
  restrictInteractionPacket active (threeControlCycleNegativeRay t)

theorem threeControlCyclePositiveRay_tendsto :
    Tendsto threeControlCyclePositiveRay (𝓝 0) (𝓝 0) := by
  apply tendsto_pi_nhds.2
  intro i
  fin_cases i <;>
    simpa [threeControlCyclePositiveRay] using!
      (tendsto_id : Tendsto (fun t : ℂ => t) (𝓝 0) (𝓝 0))

theorem threeControlCycleNegativeRay_tendsto :
    Tendsto threeControlCycleNegativeRay (𝓝 0) (𝓝 0) := by
  have h : ContinuousAt threeControlCycleNegativeRay 0 := by
    unfold threeControlCycleNegativeRay
    fun_prop
  change Tendsto threeControlCycleNegativeRay (𝓝 0)
    (𝓝 (threeControlCycleNegativeRay 0)) at h
  have hz : threeControlCycleNegativeRay 0 = 0 := by
    funext i
    fin_cases i <;> simp [threeControlCycleNegativeRay]
  simpa [hz] using h

theorem threeControlCyclePositiveActiveRay_tendsto
    (active : Finset (Fin 3)) :
    Tendsto (threeControlCyclePositiveActiveRay active) (𝓝 0) (𝓝 0) := by
  have hrestrict :=
    (restrictInteractionPacket_analyticAt active).continuousAt
  have hzero :
      restrictInteractionPacket active (0 : Fin 3 → ℂ) = 0 := by
    funext i
    simp [restrictInteractionPacket]
  change Tendsto (restrictInteractionPacket active) (𝓝 0)
    (𝓝 (restrictInteractionPacket active 0)) at hrestrict
  rw [hzero] at hrestrict
  exact hrestrict.comp threeControlCyclePositiveRay_tendsto

theorem threeControlCycleNegativeActiveRay_tendsto
    (active : Finset (Fin 3)) :
    Tendsto (threeControlCycleNegativeActiveRay active) (𝓝 0) (𝓝 0) := by
  have hrestrict :=
    (restrictInteractionPacket_analyticAt active).continuousAt
  have hzero :
      restrictInteractionPacket active (0 : Fin 3 → ℂ) = 0 := by
    funext i
    simp [restrictInteractionPacket]
  change Tendsto (restrictInteractionPacket active) (𝓝 0)
    (𝓝 (restrictInteractionPacket active 0)) at hrestrict
  rw [hzero] at hrestrict
  exact hrestrict.comp threeControlCycleNegativeRay_tendsto

theorem threeControlCycle_active_product_eq_zero
    (active : Finset (Fin 3))
    (hproper : active ≠ Finset.univ) (t : ℂ) :
    threeControlCyclePositiveActiveRay active t 0 *
        threeControlCyclePositiveActiveRay active t 1 *
        threeControlCyclePositiveActiveRay active t 2 = 0 := by
  have hmiss :
      (0 : Fin 3) ∉ active ∨
        (1 : Fin 3) ∉ active ∨
        (2 : Fin 3) ∉ active := by
    by_contra h
    push Not at h
    apply hproper
    ext i
    fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  rcases hmiss with h0 | h1 | h2
  · simp [threeControlCyclePositiveActiveRay,
      restrictInteractionPacket, h0]
  · simp [threeControlCyclePositiveActiveRay,
      restrictInteractionPacket, h1]
  · simp [threeControlCyclePositiveActiveRay,
      restrictInteractionPacket, h2]

theorem threeControlCycle_active_squares
    (active : Finset (Fin 3)) (t : ℂ) (i : Fin 3) :
    (threeControlCycleNegativeActiveRay active t i) ^ 2 =
      (threeControlCyclePositiveActiveRay active t i) ^ 2 := by
  fin_cases i <;>
    simp [threeControlCycleNegativeActiveRay,
      threeControlCyclePositiveActiveRay,
      threeControlCycleNegativeRay,
      threeControlCyclePositiveRay,
      restrictInteractionPacket]

theorem threeControlCycle_active_negative_product_eq_zero
    (active : Finset (Fin 3))
    (hproper : active ≠ Finset.univ) (t : ℂ) :
    threeControlCycleNegativeActiveRay active t 0 *
        threeControlCycleNegativeActiveRay active t 1 *
        threeControlCycleNegativeActiveRay active t 2 = 0 := by
  have hpos :=
    threeControlCycle_active_product_eq_zero active hproper t
  by_cases h0 : (0 : Fin 3) ∈ active
  · simpa [threeControlCycleNegativeActiveRay,
      threeControlCyclePositiveActiveRay,
      threeControlCycleNegativeRay,
      threeControlCyclePositiveRay,
      restrictInteractionPacket, h0] using congrArg Neg.neg hpos
  · simp [threeControlCycleNegativeActiveRay,
      restrictInteractionPacket, h0]

/-- Every proper cycle packet is a forest, so flipping one edge sign is a
spectral gauge transformation. -/
theorem threeControlCycleBranch_properActive_sign_germ
    (active : Finset (Fin 3))
    (hproper : active ≠ Finset.univ) :
    (fun t =>
      threeControlCycleBranch
        (threeControlCyclePositiveActiveRay active t)) =ᶠ[𝓝 0]
    (fun t =>
      threeControlCycleBranch
        (threeControlCycleNegativeActiveRay active t)) := by
  let H : ℂ → Matrix (Fin 3) (Fin 3) ℂ :=
    fun t =>
      threeControlCycleMatrix
        (threeControlCyclePositiveActiveRay active t)
  have hH :
      Tendsto H (𝓝 0)
        (𝓝 (Matrix.diagonal threeControlCycleEnergy)) := by
    have hmatrix := threeControlCycleMatrix_analyticAt.continuousAt
    change Tendsto threeControlCycleMatrix (𝓝 0)
      (𝓝 (threeControlCycleMatrix 0)) at hmatrix
    rw [threeControlCycleMatrix_zero] at hmatrix
    exact hmatrix.comp
      (threeControlCyclePositiveActiveRay_tendsto active)
  have hpos :
      Tendsto
        (fun t =>
          threeControlCycleBranch
            (threeControlCyclePositiveActiveRay active t))
        (𝓝 0) (𝓝 0) := by
    have hbranch := threeControlCycleBranch_analyticAt.continuousAt
    change Tendsto threeControlCycleBranch (𝓝 0)
      (𝓝 (threeControlCycleBranch 0)) at hbranch
    rw [threeControlCycleBranch_zero] at hbranch
    exact hbranch.comp
      (threeControlCyclePositiveActiveRay_tendsto active)
  have hneg :
      Tendsto
        (fun t =>
          threeControlCycleBranch
            (threeControlCycleNegativeActiveRay active t))
        (𝓝 0) (𝓝 0) := by
    have hbranch := threeControlCycleBranch_analyticAt.continuousAt
    change Tendsto threeControlCycleBranch (𝓝 0)
      (𝓝 (threeControlCycleBranch 0)) at hbranch
    rw [threeControlCycleBranch_zero] at hbranch
    exact hbranch.comp
      (threeControlCycleNegativeActiveRay_tendsto active)
  have hposRoot :
      ∀ᶠ t : ℂ in 𝓝 0,
        matrixCharpolyRelation
          (H t,
            threeControlCycleBranch
              (threeControlCyclePositiveActiveRay active t)) = 0 := by
    have hroot :=
      (threeControlCyclePositiveActiveRay_tendsto active).eventually
        threeControlCycleBranch_relation
    filter_upwards [hroot] with t ht
    rw [threeControlCycle_relation]
    exact ht
  have hnegRoot :
      ∀ᶠ t : ℂ in 𝓝 0,
        matrixCharpolyRelation
          (H t,
            threeControlCycleBranch
              (threeControlCycleNegativeActiveRay active t)) = 0 := by
    have hroot :=
      (threeControlCycleNegativeActiveRay_tendsto active).eventually
        threeControlCycleBranch_relation
    filter_upwards [hroot] with t ht
    rw [threeControlCycle_relation]
    have hposProduct :
        2 * threeControlCyclePositiveActiveRay active t 0 *
            threeControlCyclePositiveActiveRay active t 1 *
            threeControlCyclePositiveActiveRay active t 2 = 0 := by
      calc
        _ = 2 *
            (threeControlCyclePositiveActiveRay active t 0 *
              threeControlCyclePositiveActiveRay active t 1 *
              threeControlCyclePositiveActiveRay active t 2) := by ring
        _ = 0 := by
          rw [threeControlCycle_active_product_eq_zero
            active hproper t, mul_zero]
    have hnegProduct :
        2 * threeControlCycleNegativeActiveRay active t 0 *
            threeControlCycleNegativeActiveRay active t 1 *
            threeControlCycleNegativeActiveRay active t 2 = 0 := by
      calc
        _ = 2 *
            (threeControlCycleNegativeActiveRay active t 0 *
              threeControlCycleNegativeActiveRay active t 1 *
              threeControlCycleNegativeActiveRay active t 2) := by ring
        _ = 0 := by
          rw [threeControlCycle_active_negative_product_eq_zero
            active hproper t, mul_zero]
    rw [hposProduct]
    rw [threeControlCycle_active_squares active t 0,
      threeControlCycle_active_squares active t 1,
      threeControlCycle_active_squares active t 2, hnegProduct] at ht
    simpa using ht
  exact simpleDiagonalMatrix_root_germs_unique
    threeControlCycleEnergy threeControlCycleEnergy_injective 0
    hH hpos hneg hposRoot hnegRoot

/-- The full cycle branch detects its edge-sign holonomy. -/
theorem threeControlCycleBranch_full_sign_germ_ne :
    ¬(fun t =>
        threeControlCycleBranch (threeControlCyclePositiveRay t)) =ᶠ[𝓝 0]
      (fun t =>
        threeControlCycleBranch (threeControlCycleNegativeRay t)) := by
  intro hbranch
  have hpositiveRoot :=
    threeControlCyclePositiveRay_tendsto.eventually
      threeControlCycleBranch_relation
  have hnegativeRoot :=
    threeControlCycleNegativeRay_tendsto.eventually
      threeControlCycleBranch_relation
  have hforced : ∀ᶠ t : ℂ in 𝓝 0, t = 0 := by
    filter_upwards [hbranch, hpositiveRoot, hnegativeRoot]
      with t hsign hpos hneg
    rw [hsign] at hpos
    have hp0 : threeControlCyclePositiveRay t 0 = t := rfl
    have hp1 : threeControlCyclePositiveRay t 1 = t := rfl
    have hp2 : threeControlCyclePositiveRay t 2 = t := rfl
    have hn0 : threeControlCycleNegativeRay t 0 = -t := rfl
    have hn1 : threeControlCycleNegativeRay t 1 = t := rfl
    have hn2 : threeControlCycleNegativeRay t 2 = t := rfl
    have hfour : (4 : ℂ) * t ^ 3 = 0 := by
      simp only [hp0, hp1, hp2] at hpos
      simp only [hn0, hn1, hn2, neg_sq] at hneg
      linear_combination hneg - hpos
    have ht3 : t ^ 3 = 0 :=
      (mul_eq_zero.mp hfour).resolve_left (by norm_num)
    have hmul : t * t * t = 0 := by
      simpa [pow_succ] using ht3
    rcases mul_eq_zero.mp hmul with htt | ht
    · exact (mul_eq_zero.mp htt).elim id id
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

/-- **Three-control Hermitian holonomy witness.** Three linearly independent
edge controls around a qutrit cycle carry a nonzero joint spectral packet.
Every proper subpacket is sign-gauge trivial, while the closed cycle detects
the gauge-invariant product of all three edge signs. -/
theorem threeControlCycle_packetResponse_ne_zero :
    ¬spectralPacketResponse threeControlCycleBranch
        (Finset.univ : Finset (Fin 3)) =ᶠ[𝓝 0]
      (fun _ : Fin 3 → ℂ => 0) := by
  apply spectralPacketResponse_univ_germ_ne_zero_of_holonomy
    threeControlCycleBranch
    threeControlCyclePositiveRay
    threeControlCycleNegativeRay
    threeControlCyclePositiveRay_tendsto
    threeControlCycleNegativeRay_tendsto
  · intro active hactive
    simpa [threeControlCyclePositiveActiveRay,
      threeControlCycleNegativeActiveRay] using
      threeControlCycleBranch_properActive_sign_germ active hactive
  · exact threeControlCycleBranch_full_sign_germ_ne

end GaloisForLFunctions.HTGeometry
