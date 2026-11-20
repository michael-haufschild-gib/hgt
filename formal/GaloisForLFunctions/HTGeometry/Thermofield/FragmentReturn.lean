import GaloisForLFunctions.HTGeometry.Thermofield.FragmentCoherence
import GaloisForLFunctions.HTGeometry.Thermofield.ThermalReturnPlateau
import GaloisForLFunctions.HTGeometry.ReplicaOperatorCovarianceCrowdingLaw

/-!
# Thermal return of a restricted fragment

The fragment partial trace from the branch-overlap construction of Kanno
and Soda (arXiv:2611.26368, Section 7.3) removes phase pairs across hidden
labels. Time averaging then removes pairs of different energies. The difference
from the full thermofield plateau is exactly the lost equal-energy pair mass.
-/

open scoped BigOperators Interval Topology
open Filter Matrix

namespace GaloisForLFunctions.HTGeometry.Thermofield

open _root_.HTGeometry

noncomputable section

variable {α ν : Type*} [Fintype α] [DecidableEq α] [DecidableEq ν]

/-- Weight of a Gibbs pair still available after tracing out the hidden record. -/
def retainedPairMass (lost : α → ν) (β : ℝ) (E : α → ℝ) (a b : α) : ℝ :=
  if lost a = lost b then finiteGibbsStateWeight β E a * finiteGibbsStateWeight β E b else 0

/-- Hilbert--Schmidt overlap of the accessible fragment with its initial state. -/
def fragmentReturn (lost : α → ν) (β : ℝ) (E : α → ℝ) (t : ℝ) : ℂ :=
  (fragmentState lost β E t * fragmentState lost β E 0).trace

theorem fragmentReturn_eq (lost : α → ν) (β : ℝ) (E : α → ℝ) (t : ℝ) :
    fragmentReturn lost β E t =
      ∑ a, ∑ b, (retainedPairMass lost β E a b : ℂ) *
        Complex.exp ((t * (E a - E b) : ℝ) * Complex.I) := by
  simp only [fragmentReturn, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : lost a = lost b
  · simp only [fragmentState_apply, h, h.symm, if_true, Complex.ofReal_zero,
      mul_zero, zero_mul, Complex.exp_zero, one_mul, retainedPairMass]
    rw [finiteKMSWightmanWeight_symm β E b a, mul_assoc, ← Complex.ofReal_mul,
      ← pow_two, finiteKMSWightmanWeight_sq, mul_comm]
    congr 2
    push_cast
    ring
  · simp only [fragmentState_apply, if_neg h, if_neg (Ne.symm h), retainedPairMass,
      zero_mul, Complex.ofReal_zero]

/-- Symmetric-time mean of the actual fragment overlap. -/
def fragmentReturnMean (lost : α → ν) (β : ℝ) (E : α → ℝ) (T : ℝ) : ℂ :=
  (2 * T : ℂ)⁻¹ * ∫ t : ℝ in -T..T, fragmentReturn lost β E t

theorem fragmentReturnMean_eq (lost : α → ν) (β : ℝ) (E : α → ℝ) (T : ℝ) :
    fragmentReturnMean lost β E T =
      ∑ a, ∑ b, (retainedPairMass lost β E a b : ℂ) *
        symmetricPhaseAverage T (E a - E b) := by
  unfold fragmentReturnMean
  simp_rw [fragmentReturn_eq]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [intervalIntegral.integral_const_mul, symmetricPhaseAverage]
      ring
    · intro b _
      exact (by fun_prop : Continuous (fun t : ℝ => (retainedPairMass lost β E a b : ℂ) *
        Complex.exp ((t * (E a - E b) : ℝ) * Complex.I))).intervalIntegrable (-T) T
  · intro a _
    exact (by fun_prop : Continuous (fun t : ℝ =>
      ∑ b, (retainedPairMass lost β E a b : ℂ) *
        Complex.exp ((t * (E a - E b) : ℝ) * Complex.I))).intervalIntegrable (-T) T

/-- The long-time accessible return keeps pairs of equal energy in the same hidden sector. -/
def fragmentReturnPlateau (lost : α → ν) (β : ℝ) (E : α → ℝ) : ℝ :=
  ∑ a, ∑ b, if E a = E b then retainedPairMass lost β E a b else 0

theorem fragmentReturnMean_tendsto (lost : α → ν) (β : ℝ) (E : α → ℝ) :
    Tendsto (fragmentReturnMean lost β E) atTop (𝓝 (fragmentReturnPlateau lost β E : ℂ)) := by
  simp only [show fragmentReturnMean lost β E = (fun T =>
    ∑ a, ∑ b, (retainedPairMass lost β E a b : ℂ) *
      symmetricPhaseAverage T (E a - E b)) from funext (fragmentReturnMean_eq lost β E),
    fragmentReturnPlateau, Complex.ofReal_sum]
  apply tendsto_finsetSum
  intro a _
  apply tendsto_finsetSum
  intro b _
  have h := (symmetricPhaseAverage_tendsto_resonanceIndicator (E a - E b)).const_mul
    (retainedPairMass lost β E a b : ℂ)
  by_cases he : E a = E b
  · simpa only [he, sub_self, if_true, mul_one] using h
  · simpa only [sub_ne_zero.mpr he, if_false, mul_zero, Complex.ofReal_zero, he] using h

variable [Nonempty α]

/-- The ordinary Gibbs purity is a lower bound on the fragment return plateau. -/
theorem purity_le_fragmentReturnPlateau (lost : α → ν) (β : ℝ) (E : α → ℝ) :
    finiteGibbsPurity β E ≤ fragmentReturnPlateau lost β E := by
  apply Finset.sum_le_sum
  intro a _
  have h := Finset.single_le_sum
    (f := fun b => if E a = E b then retainedPairMass lost β E a b else 0)
    (fun b _ => by unfold retainedPairMass; split <;> try split <;> positivity)
    (Finset.mem_univ a)
  simpa only [retainedPairMass, if_true, pow_two] using h

/-- The inaccessible record deletes exactly the equal-energy pairs it separates. -/
theorem returnPlateau_eq_fragment_add_lost (lost : α → ν) (β : ℝ) (E : α → ℝ) :
    returnPlateau β E = fragmentReturnPlateau lost β E +
      ∑ a, ∑ b, if E a = E b ∧ lost a ≠ lost b then
        finiteGibbsStateWeight β E a * finiteGibbsStateWeight β E b else 0 := by
  rw [returnPlateau, fidelityReplicaCollisionMass_one_eq_spectralRows,
    fragmentReturnPlateau, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hE : E a = E b <;> by_cases hl : lost a = lost b <;>
    simp [retainedPairMass, hE, hl]

/-- The full plateau survives the partial trace precisely when the hidden
label is constant on every equal-energy class. -/
theorem fragmentReturnPlateau_eq_full_iff (lost : α → ν) (β : ℝ) (E : α → ℝ) :
    fragmentReturnPlateau lost β E = returnPlateau β E ↔
      ∀ a b, E a = E b → lost a = lost b := by
  rw [returnPlateau_eq_fragment_add_lost]
  let F : α → α → ℝ := fun a b => if E a = E b ∧ lost a ≠ lost b then
    finiteGibbsStateWeight β E a * finiteGibbsStateWeight β E b else 0
  change _ = _ + (∑ a, ∑ b, F a b) ↔ _
  have hnonneg (a b : α) : 0 ≤ F a b := by unfold F; split <;> positivity
  constructor
  · intro h a b hE
    have hz : (∑ a, ∑ b, F a b) = 0 := by linarith only [h]
    have ha := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => Finset.sum_nonneg fun b _ => hnonneg a b)).mp hz a (Finset.mem_univ a)
    have hb := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hnonneg a b)).mp ha b
      (Finset.mem_univ b)
    by_contra hne
    have hpos : 0 < F a b := by
      rw [show F a b = _ from if_pos ⟨hE, hne⟩]
      exact mul_pos (finiteGibbsStateWeight_pos β E a) (finiteGibbsStateWeight_pos β E b)
    exact hpos.ne' hb
  · intro h
    suffices (∑ a, ∑ b, F a b) = 0 by rw [this, add_zero]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    exact if_neg fun h' => h'.2 (h a b h'.1)

#print axioms fragmentReturn_eq
#print axioms fragmentReturnMean_eq
#print axioms fragmentReturnMean_tendsto
#print axioms purity_le_fragmentReturnPlateau
#print axioms returnPlateau_eq_fragment_add_lost
#print axioms fragmentReturnPlateau_eq_full_iff

end

end GaloisForLFunctions.HTGeometry.Thermofield
