import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.GrowingTheWeilWindowAddsAnOrthogonalKernel
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilKernelDivergesAtContact

/-!
# The evaluation kernels have a Hamiltonian density

De Branges' ordering theorem writes the reproducing kernels of a chain as
`K_a(z, w) = ∫₀^a ⟨H(t) Y(t, w), Y(t, z)⟩ dt`. This module proves the part of that representation which does not
need the ordering theorem, in the frame of finitely many evaluation points.

For points `z_i` and coefficients `α_i`, the Gram function `G(a) = ‖Σ_i α_i E_a(z_i)‖²` of the Riesz vectors is the
quadratic form of the kernel matrix (`evalGram_eq_kernel`). Its increase is the squared norm of the orthogonal
increment (`evalGram_sub_eq`), so it is monotone. Hence `G′` exists almost everywhere and

  `0 ≤ ∫_a^b G′ ≤ G(b) − G(a)`   (`integral_evalDensity_mem`).

The gap measures growth not recovered by the ordinary derivative. Monotonicity alone does not remove it or
identify a Hamiltonian; the exact endpoint estimates supply that additional information. Finite-contact
divergence is a separate issue: when RH fails, some diagonal kernel tends to infinity there
(`riemannHypothesis_or_evalGram_tends_to_top`). Local absolute continuity does not rule out that divergence.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower CanonicalSystemOfTheWindowTower CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
open Zeta23

/-- The real apertures strictly below contact. -/
def precontactSet : Set ℝ := {a | 0 < a ∧ (a : EReal) < WindowVisibilityLaw.onsetAperture zetaZeroConfig}

/-- A real aperture below contact as a pre-contact aperture. -/
def toPrecontact {a : ℝ} (h : a ∈ precontactSet) : PrecontactAperture := ⟨⟨a, h.1⟩, h.2⟩

variable {ι : Type*} [Fintype ι]

/-- The combined Riesz vector `Σ_i α_i E_a(z_i)`. -/
def evalCombination (α z : ι → ℂ) (a : PrecontactAperture) : WeilHilbertBeforeContact a :=
  ∑ i, α i • evalVector a (z i)

/-- The Gram function `a ↦ ‖Σ_i α_i E_a(z_i)‖²` below contact, extended by zero. -/
def evalGram (α z : ι → ℂ) (a : ℝ) : ℝ :=
  open Classical in
  if h : a ∈ precontactSet then ‖evalCombination α z (toPrecontact h)‖ ^ 2 else 0

/-- The combined increment of the Riesz vectors. -/
def combinationIncrement (α z : ι → ℂ) {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) :
    WeilHilbertBeforeContact b := ∑ i, α i • evalVectorIncrement hab (z i)

theorem evalCombination_eq (α z : ι → ℂ) {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) :
    evalCombination α z b = combinationIncrement α z hab + inclusion hab (evalCombination α z a) := by
  unfold evalCombination combinationIncrement
  rw [map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← smul_add]
  congr 1
  unfold evalVectorIncrement
  exact (sub_add_cancel _ _).symm

theorem inner_combinationIncrement_inclusion (α z : ι → ℂ) {a b : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (u : WeilHilbertBeforeContact a) :
    inner ℂ (combinationIncrement α z hab) (inclusion hab u) = 0 := by
  unfold combinationIncrement
  rw [sum_inner]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [inner_smul_left, inner_evalVectorIncrement_inclusion, mul_zero]

/-- **The increase of the Gram function is the squared norm of the orthogonal increment.** -/
theorem norm_evalCombination_sq (α z : ι → ℂ) {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) :
    ‖evalCombination α z b‖ ^ 2 =
      ‖evalCombination α z a‖ ^ 2 + ‖combinationIncrement α z hab‖ ^ 2 := by
  rw [evalCombination_eq α z hab, @norm_add_sq ℂ, inner_combinationIncrement_inclusion,
    (inclusion hab).norm_map]
  simp
  ring

/-- The Gram function is the quadratic form of the kernel matrix. -/
theorem evalGram_eq_kernel (α z : ι → ℂ) (a : PrecontactAperture) :
    ((‖evalCombination α z a‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, (starRingEnd ℂ) (α i) * α j * kernel a (z j) (z i) := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (evalCombination α z a)
  have e : ((‖evalCombination α z a‖ ^ 2 : ℝ) : ℂ) = ((‖evalCombination α z a‖ : ℂ)) ^ 2 := by
    push_cast
    rfl
  rw [e]
  have h' : inner ℂ (evalCombination α z a) (evalCombination α z a) =
      ((‖evalCombination α z a‖ : ℂ)) ^ 2 := by
    simpa using h
  rw [← h']
  unfold evalCombination
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_evalVector]
  have : eval a (z i) (evalVector a (z j)) = kernel a (z j) (z i) := rfl
  rw [this]
  ring

theorem monotoneOn_evalGram (α z : ι → ℂ) : MonotoneOn (evalGram α z) precontactSet := by
  intro a ha b hb hab
  unfold evalGram
  rw [dif_pos ha, dif_pos hb]
  have h := norm_evalCombination_sq α z (a := toPrecontact ha) (b := toPrecontact hb) hab
  rw [h]
  exact le_add_of_nonneg_right (by positivity)

/-- The density `G′` of the Gram function: the Hamiltonian form along the evaluation orbit. -/
def evalDensity (α z : ι → ℂ) : ℝ → ℝ := deriv (evalGram α z)

/-- **The density has finite mass, dominated by the kernel gain.** On every interval below contact, `G′` is
integrable with `0 ≤ ∫_a^b G′ ≤ G(b) − G(a)`; the difference is the singular part of the chain on `[a, b]`. -/
theorem integral_evalDensity_mem (α z : ι → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hs : Icc a b ⊆ precontactSet) :
    IntervalIntegrable (evalDensity α z) volume a b ∧
      0 ≤ ∫ x in a..b, evalDensity α z x ∧
        ∫ x in a..b, evalDensity α z x ≤ evalGram α z b - evalGram α z a := by
  have hmono : MonotoneOn (evalGram α z) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact (monotoneOn_evalGram α z).mono hs
  have hmem := hmono.intervalIntegral_deriv_mem_uIcc
  have hge : evalGram α z a ≤ evalGram α z b :=
    monotoneOn_evalGram α z (hs ⟨le_rfl, hab⟩) (hs ⟨hab, le_rfl⟩) hab
  rw [uIcc_of_le (sub_nonneg.mpr hge)] at hmem
  exact ⟨hmono.intervalIntegrable_deriv, hmem.1, hmem.2⟩

/-- Either RH holds, or some diagonal kernel diverges at finite contact. -/
theorem riemannHypothesis_or_evalGram_tends_to_top :
    RiemannHypothesis ∨ ∃ z : ℂ, ∀ C : ℝ, ∃ b₀ : PrecontactAperture, ∀ b : PrecontactAperture,
      b₀.1.1 ≤ b.1.1 → C < ‖evalCombination (fun _ : Unit => (1 : ℂ)) (fun _ => z) b‖ ^ 2 := by
  rcases riemannHypothesis_or_kernel_tends_to_top_at_contact with hRH | ⟨a, -, -, z, hz⟩
  · exact Or.inl hRH
  · refine Or.inr ⟨z, fun C => ?_⟩
    obtain ⟨b₀, hb₀⟩ := hz C
    refine ⟨b₀, fun b hb => ?_⟩
    have e : evalCombination (fun _ : Unit => (1 : ℂ)) (fun _ => z) b = evalVector b z := by
      simp [evalCombination]
    rw [e]
    exact hb₀ b hb

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
