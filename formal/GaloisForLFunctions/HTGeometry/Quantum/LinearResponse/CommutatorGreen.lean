import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Topology.Instances.Matrix

/-!
# Green function of a Hamiltonian commutator

The energy basis makes the commutator diagonal on matrix entries, with
eigenvalues given by Bohr frequencies. The inverse for a nonresonant
shift divides each entry by its shifted frequency. At resonance the
pole coefficient keeps exactly the entries at the resonant frequency.
-/

open Matrix Filter Set
open scoped Matrix Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}

/-- Coordinates in the orthonormal energy eigenbasis. -/
def hamiltonianEnergyCoordinates (hH : H.IsHermitian) : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hH.eigenvectorUnitary).symm

private theorem energyCoordinates_ext (hH : H.IsHermitian) {X Y : Matrix ι ι ℂ}
    (h : ∀ i j, hamiltonianEnergyCoordinates hH X i j = hamiltonianEnergyCoordinates hH Y i j) :
    X = Y :=
  (hamiltonianEnergyCoordinates hH).injective (Matrix.ext h)

/-- The energy difference of an ordered transition. -/
def hamiltonianGap (hH : H.IsHermitian) (i j : ι) : ℝ :=
  hH.eigenvalues i - hH.eigenvalues j

private theorem energyCoordinates_hamiltonian (hH : H.IsHermitian) :
    hamiltonianEnergyCoordinates hH H = diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
  apply (hamiltonianEnergyCoordinates hH).symm.injective
  change (hamiltonianEnergyCoordinates hH).symm (hamiltonianEnergyCoordinates hH H) = _
  rw [StarAlgEquiv.symm_apply_apply]
  exact hH.spectral_theorem

theorem energyCoordinates_commutator_apply (hH : H.IsHermitian) (X : Matrix ι ι ℂ) (i j : ι) :
    hamiltonianEnergyCoordinates hH (H * X - X * H) i j =
      (hamiltonianGap hH i j : ℂ) * hamiltonianEnergyCoordinates hH X i j := by
  rw [map_sub, map_mul, map_mul, energyCoordinates_hamiltonian, Matrix.sub_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, hamiltonianGap, Complex.ofReal_sub]
  ring

/-- Green response to a forcing matrix for the shifted Hamiltonian
commutator, with each scalar inverse totalized at its own pole. -/
def hamiltonianCommutatorGreen (hH : H.IsHermitian) (z : ℂ) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (hamiltonianEnergyCoordinates hH).symm (Matrix.of fun i j =>
    ((hamiltonianGap hH i j : ℂ) - z)⁻¹ * hamiltonianEnergyCoordinates hH X i j)

theorem energyCoordinates_commutatorGreen_apply
    (hH : H.IsHermitian) (z : ℂ) (X : Matrix ι ι ℂ) (i j : ι) :
    hamiltonianEnergyCoordinates hH (hamiltonianCommutatorGreen hH z X) i j =
      ((hamiltonianGap hH i j : ℂ) - z)⁻¹ * hamiltonianEnergyCoordinates hH X i j := by
  simp only [hamiltonianCommutatorGreen, StarAlgEquiv.apply_symm_apply, Matrix.of_apply]

private theorem energyCoordinates_shiftedCommutator_apply
    (hH : H.IsHermitian) (z : ℂ) (Y : Matrix ι ι ℂ) (i j : ι) :
    hamiltonianEnergyCoordinates hH (H * Y - Y * H - z • Y) i j =
      ((hamiltonianGap hH i j : ℂ) - z) * hamiltonianEnergyCoordinates hH Y i j := by
  rw [map_sub, Matrix.sub_apply, energyCoordinates_commutator_apply, map_smul,
    Matrix.smul_apply, smul_eq_mul, sub_mul]

/-- Away from the Bohr spectrum, the Green response is the unique
solution of the shifted commutator equation. -/
theorem shiftedCommutator_eq_iff
    (hH : H.IsHermitian) (z : ℂ) (hz : ∀ i j, (hamiltonianGap hH i j : ℂ) ≠ z)
    (X Y : Matrix ι ι ℂ) :
    H * Y - Y * H - z • Y = X ↔ Y = hamiltonianCommutatorGreen hH z X := by
  constructor
  · intro he
    apply energyCoordinates_ext hH
    intro i j
    have h := congrArg (fun Z => hamiltonianEnergyCoordinates hH Z i j) he
    rw [energyCoordinates_shiftedCommutator_apply] at h
    rw [energyCoordinates_commutatorGreen_apply, ← h,
      inv_mul_cancel_left₀ (sub_ne_zero.mpr (hz i j))]
  · rintro rfl
    apply energyCoordinates_ext hH
    intro i j
    rw [energyCoordinates_shiftedCommutator_apply, energyCoordinates_commutatorGreen_apply,
      mul_inv_cancel_left₀ (sub_ne_zero.mpr (hz i j))]

/-- Every nonreal shift lies in the resolvent set, with no restriction on
eigenvalue multiplicities. -/
theorem shiftedCommutator_eq_iff_of_nonreal
    (hH : H.IsHermitian) (z : {z : ℂ // z.im ≠ 0}) (X Y : Matrix ι ι ℂ) :
    H * Y - Y * H - (z : ℂ) • Y = X ↔ Y = hamiltonianCommutatorGreen hH z X := by
  refine shiftedCommutator_eq_iff hH z (fun i j he => z.2 ?_) X Y
  exact (congrArg Complex.im he).symm.trans (Complex.ofReal_im _)

/-- The part of a forcing matrix supported at a specified Bohr frequency. -/
def hamiltonianGapComponent (hH : H.IsHermitian) (μ : ℝ) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (hamiltonianEnergyCoordinates hH).symm (Matrix.of fun i j =>
    if hamiltonianGap hH i j = μ then hamiltonianEnergyCoordinates hH X i j else 0)

theorem energyCoordinates_gapComponent_apply
    (hH : H.IsHermitian) (μ : ℝ) (X : Matrix ι ι ℂ) (i j : ι) :
    hamiltonianEnergyCoordinates hH (hamiltonianGapComponent hH μ X) i j =
      if hamiltonianGap hH i j = μ then hamiltonianEnergyCoordinates hH X i j else 0 := by
  simp only [hamiltonianGapComponent, StarAlgEquiv.apply_symm_apply, Matrix.of_apply]

/-- The selected frequency component is a projection onto the
corresponding commutator eigenspace. -/
theorem hamiltonianGapComponent_eq_self_iff
    (hH : H.IsHermitian) (μ : ℝ) (X : Matrix ι ι ℂ) :
    hamiltonianGapComponent hH μ X = X ↔ H * X - X * H = (μ : ℂ) • X := by
  constructor
  · intro hx
    apply energyCoordinates_ext hH
    intro i j
    rw [energyCoordinates_commutator_apply, map_smul, Matrix.smul_apply, smul_eq_mul]
    by_cases hg : hamiltonianGap hH i j = μ
    · rw [hg]
    · have hc := congrArg (fun Z => hamiltonianEnergyCoordinates hH Z i j) hx
      rw [energyCoordinates_gapComponent_apply, if_neg hg] at hc
      rw [← hc, mul_zero, mul_zero]
  · intro hx
    apply energyCoordinates_ext hH
    intro i j
    rw [energyCoordinates_gapComponent_apply]
    by_cases hg : hamiltonianGap hH i j = μ
    · rw [if_pos hg]
    · rw [if_neg hg]
      have hc := congrArg (fun Z => hamiltonianEnergyCoordinates hH Z i j) hx
      rw [energyCoordinates_commutator_apply, map_smul, Matrix.smul_apply, smul_eq_mul] at hc
      have hm : ((hamiltonianGap hH i j : ℂ) - (μ : ℂ)) *
          hamiltonianEnergyCoordinates hH X i j = 0 := by rw [sub_mul, hc, sub_self]
      exact ((mul_eq_zero.mp hm).resolve_left
        (sub_ne_zero.mpr fun he => hg (Complex.ofReal_injective he))).symm

theorem hamiltonianGapComponent_idempotent
    (hH : H.IsHermitian) (μ : ℝ) (X : Matrix ι ι ℂ) :
    hamiltonianGapComponent hH μ (hamiltonianGapComponent hH μ X) =
      hamiltonianGapComponent hH μ X := by
  apply energyCoordinates_ext hH
  intro i j
  simp only [energyCoordinates_gapComponent_apply]
  split_ifs <;> rfl

theorem hamiltonianGapComponent_zero_eq_self_iff
    (hH : H.IsHermitian) (X : Matrix ι ι ℂ) :
    hamiltonianGapComponent hH 0 X = X ↔ H * X = X * H := by
  rw [hamiltonianGapComponent_eq_self_iff]
  simp only [Complex.ofReal_zero, zero_smul, sub_eq_zero]

/-- Remove every term at one resonant frequency. -/
def hamiltonianCommutatorGreenRegularPart
    (hH : H.IsHermitian) (μ : ℝ) (z : ℂ) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (hamiltonianEnergyCoordinates hH).symm (Matrix.of fun i j =>
    if hamiltonianGap hH i j = μ then 0
    else ((hamiltonianGap hH i j : ℂ) - z)⁻¹ * hamiltonianEnergyCoordinates hH X i j)

/-- Exact separation of the pole from the other Bohr frequencies. -/
theorem hamiltonianCommutatorGreen_eq_pole_add_regular
    (hH : H.IsHermitian) (μ : ℝ) (z : ℂ) (X : Matrix ι ι ℂ) :
    hamiltonianCommutatorGreen hH z X =
      ((μ : ℂ) - z)⁻¹ • hamiltonianGapComponent hH μ X +
        hamiltonianCommutatorGreenRegularPart hH μ z X := by
  apply energyCoordinates_ext hH
  intro i j
  rw [energyCoordinates_commutatorGreen_apply, map_add, map_smul, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, energyCoordinates_gapComponent_apply,
    hamiltonianCommutatorGreenRegularPart, StarAlgEquiv.apply_symm_apply, Matrix.of_apply]
  by_cases hg : hamiltonianGap hH i j = μ
  · rw [if_pos hg, if_pos hg, hg, add_zero]
  · rw [if_neg hg, if_neg hg, mul_zero, zero_add]

theorem continuousAt_hamiltonianCommutatorGreenRegularPart
    (hH : H.IsHermitian) (μ : ℝ) (X : Matrix ι ι ℂ) :
    ContinuousAt (fun z => hamiltonianCommutatorGreenRegularPart hH μ z X) (μ : ℂ) := by
  let M (z : ℂ) : Matrix ι ι ℂ := Matrix.of fun i j =>
    if hamiltonianGap hH i j = μ then 0
    else ((hamiltonianGap hH i j : ℂ) - z)⁻¹ * hamiltonianEnergyCoordinates hH X i j
  have hm : ContinuousAt M (μ : ℂ) := by
    change ContinuousAt (fun z => fun i j => M z i j) (μ : ℂ)
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    by_cases hg : hamiltonianGap hH i j = μ
    · simpa only [M, Matrix.of_apply, if_pos hg] using
        (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℂ)) (μ : ℂ))
    · have hf : ContinuousAt (fun z : ℂ => (hamiltonianGap hH i j : ℂ) - z) (μ : ℂ) :=
        continuousAt_const.sub continuousAt_id
      have hn : (hamiltonianGap hH i j : ℂ) - (μ : ℂ) ≠ 0 :=
        sub_ne_zero.mpr fun he => hg (Complex.ofReal_injective he)
      have ht : ContinuousAt (fun z : ℂ => ((hamiltonianGap hH i j : ℂ) - z)⁻¹ *
          hamiltonianEnergyCoordinates hH X i j) (μ : ℂ) :=
        (hf.inv₀ hn).mul continuousAt_const
      simpa only [M, Matrix.of_apply, if_neg hg] using ht
  let U : Matrix ι ι ℂ := hH.eigenvectorUnitary
  change ContinuousAt (fun z => U * M z * star U) (μ : ℂ)
  exact (continuousAt_const.mul hm).mul continuousAt_const

/-- The residue recovers the corresponding component even for a
degenerate energy level or a repeated nonzero Bohr frequency. -/
theorem tendsto_hamiltonianCommutatorGreen_pole
    (hH : H.IsHermitian) (μ : ℝ) (X : Matrix ι ι ℂ) :
    Tendsto (fun z => ((μ : ℂ) - z) • hamiltonianCommutatorGreen hH z X)
      (𝓝[≠] (μ : ℂ)) (𝓝 (hamiltonianGapComponent hH μ X)) := by
  have hd : ContinuousAt (fun z : ℂ => (μ : ℂ) - z) (μ : ℂ) :=
    continuousAt_const.sub continuousAt_id
  have hz : Tendsto (fun z : ℂ => (μ : ℂ) - z) (𝓝[≠] (μ : ℂ)) (𝓝 0) := by
    simpa only [ContinuousWithinAt, sub_self] using
      hd.continuousWithinAt (s := ({(μ : ℂ)}ᶜ : Set ℂ))
  have hr := (continuousAt_hamiltonianCommutatorGreenRegularPart hH μ X).continuousWithinAt
    (s := ({(μ : ℂ)}ᶜ : Set ℂ))
  have hl : Tendsto (fun z => hamiltonianGapComponent hH μ X +
      ((μ : ℂ) - z) • hamiltonianCommutatorGreenRegularPart hH μ z X)
      (𝓝[≠] (μ : ℂ)) (𝓝 (hamiltonianGapComponent hH μ X)) := by
    simpa only [zero_smul, add_zero] using tendsto_const_nhds.add (hz.smul hr)
  apply hl.congr'
  have hne : ∀ᶠ z in 𝓝[≠] (μ : ℂ), z ≠ (μ : ℂ) := self_mem_nhdsWithin
  filter_upwards [hne] with z hn
  rw [hamiltonianCommutatorGreen_eq_pole_add_regular hH μ z, smul_add, smul_smul,
    mul_inv_cancel₀ (sub_ne_zero.mpr (Ne.symm hn)), one_smul]

/-- A commutator source has zero residue at frequency zero. The
unscaled Green response then extends continuously and recovers the
source operator with its commuting component removed. -/
theorem continuousAt_commutatorGreen_commutator_zero (hH : H.IsHermitian) (X : Matrix ι ι ℂ) :
    ContinuousAt (fun z => hamiltonianCommutatorGreen hH z (H * X - X * H)) 0 ∧
      hamiltonianCommutatorGreen hH 0 (H * X - X * H) = X - hamiltonianGapComponent hH 0 X := by
  have hzero : hamiltonianGapComponent hH 0 (H * X - X * H) = 0 := by
    apply energyCoordinates_ext hH
    intro i j
    rw [energyCoordinates_gapComponent_apply, energyCoordinates_commutator_apply, map_zero,
      Matrix.zero_apply]
    split_ifs with hg
    · simp only [hg, Complex.ofReal_zero, zero_mul]
    · rfl
  have hregular : (fun z => hamiltonianCommutatorGreen hH z (H * X - X * H)) =
      fun z => hamiltonianCommutatorGreenRegularPart hH 0 z (H * X - X * H) := by
    funext z
    rw [hamiltonianCommutatorGreen_eq_pole_add_regular hH 0 z, hzero, smul_zero, zero_add]
  constructor
  · rw [hregular]
    simpa only [Complex.ofReal_zero] using
      continuousAt_hamiltonianCommutatorGreenRegularPart hH 0 (H * X - X * H)
  · apply energyCoordinates_ext hH
    intro i j
    rw [energyCoordinates_commutatorGreen_apply, energyCoordinates_commutator_apply, map_sub,
      Matrix.sub_apply, energyCoordinates_gapComponent_apply, sub_zero]
    by_cases hg : hamiltonianGap hH i j = 0
    · rw [if_pos hg, hg, Complex.ofReal_zero, zero_mul, mul_zero, sub_self]
    · rw [if_neg hg, sub_zero, inv_mul_cancel_left₀ (fun he => hg (Complex.ofReal_eq_zero.mp he))]

#print axioms shiftedCommutator_eq_iff_of_nonreal
#print axioms hamiltonianGapComponent_zero_eq_self_iff
#print axioms tendsto_hamiltonianCommutatorGreen_pole
#print axioms continuousAt_commutatorGreen_commutator_zero

end

end GaloisForLFunctions.HTGeometry
