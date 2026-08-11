import GaloisForLFunctions.RHTower.MobiusBoundaryOppositeSignTransport

/-!
# Route E opposite-parity Metropolis rejection law

This module formalizes the exact finite theorem from
`route-e-opposite-parity-metropolis-rejection-law.md`.  A datum packages a finite weighted
opposite-parity Markov kernel.  Its Metropolis conductance is the minimum of each directed edge
mass and its reversal.  The total rejected mass is exactly one half of the edge-law total
variation and bounds the signed current.

No reversibility, support-overlap, analytic, or asymptotic premise is used.
-/

namespace RHTower

open scoped BigOperators

/-- Finite weighted row-stochastic kernel whose supported transitions reverse sign. -/
structure RouteEOppositeParityKernel (ι : Type*) [Fintype ι] where
  sign : ι → ℝ
  weight : ι → ℝ
  transition : ι → ι → ℝ
  sign_abs_one : ∀ i, |sign i| = 1
  weight_nonneg : ∀ i, 0 ≤ weight i
  transition_nonneg : ∀ i j, 0 ≤ transition i j
  row_stochastic : ∀ i, ∑ j, transition i j = 1
  parity_reversing : ∀ i j, transition i j ≠ 0 → sign i + sign j = 0

namespace RouteEOppositeParityKernel

variable {ι : Type*} [Fintype ι]

/-- Directed physical edge mass `Q(i,j)=w(i)P(i,j)`. -/
def edgeMass (K : RouteEOppositeParityKernel ι) (i j : ι) : ℝ :=
  K.weight i * K.transition i j

/-- Symmetric accepted Metropolis conductance. -/
def acceptedConductance (K : RouteEOppositeParityKernel ι) (i j : ι) : ℝ :=
  min (K.edgeMass i j) (K.edgeMass j i)

/-- Unused physical mass at one vertex. -/
def rejectedAt (K : RouteEOppositeParityKernel ι) (i : ι) : ℝ :=
  K.weight i - ∑ j, K.acceptedConductance i j

/-- Total Metropolis rejection. -/
def totalRejection (K : RouteEOppositeParityKernel ι) : ℝ :=
  ∑ i, K.rejectedAt i

/-- Signed physical current. -/
def signedCurrent (K : RouteEOppositeParityKernel ι) : ℝ :=
  ∑ i, K.sign i * K.weight i

/-- Total physical mass of the row law. -/
def totalWeight (K : RouteEOppositeParityKernel ι) : ℝ :=
  ∑ i, K.weight i

theorem edgeMass_nonneg (K : RouteEOppositeParityKernel ι) (i j : ι) :
    0 ≤ K.edgeMass i j :=
  mul_nonneg (K.weight_nonneg i) (K.transition_nonneg i j)

theorem sum_edgeMass (K : RouteEOppositeParityKernel ι) (i : ι) :
    ∑ j, K.edgeMass i j = K.weight i := by
  simp [edgeMass, ← Finset.mul_sum, K.row_stochastic]

theorem sum_sum_edgeMass (K : RouteEOppositeParityKernel ι) :
    ∑ i, ∑ j, K.edgeMass i j = K.totalWeight := by
  simp [totalWeight, K.sum_edgeMass]

theorem totalWeight_nonneg (K : RouteEOppositeParityKernel ι) :
    0 ≤ K.totalWeight :=
  Finset.sum_nonneg fun i _hi => K.weight_nonneg i

theorem acceptedConductance_nonneg (K : RouteEOppositeParityKernel ι) (i j : ι) :
    0 ≤ K.acceptedConductance i j :=
  le_min (K.edgeMass_nonneg i j) (K.edgeMass_nonneg j i)

theorem acceptedConductance_symm (K : RouteEOppositeParityKernel ι) (i j : ι) :
    K.acceptedConductance i j = K.acceptedConductance j i := by
  simp only [acceptedConductance, min_comm]

theorem acceptedConductance_le_edgeMass
    (K : RouteEOppositeParityKernel ι) (i j : ι) :
    K.acceptedConductance i j ≤ K.edgeMass i j :=
  min_le_left _ _

theorem sum_acceptedConductance_le_weight
    (K : RouteEOppositeParityKernel ι) (i : ι) :
    ∑ j, K.acceptedConductance i j ≤ K.weight i := by
  calc
    ∑ j, K.acceptedConductance i j ≤ ∑ j, K.edgeMass i j :=
      Finset.sum_le_sum fun j _hj => K.acceptedConductance_le_edgeMass i j
    _ = K.weight i := K.sum_edgeMass i

theorem rejectedAt_nonneg (K : RouteEOppositeParityKernel ι) (i : ι) :
    0 ≤ K.rejectedAt i :=
  sub_nonneg.mpr (K.sum_acceptedConductance_le_weight i)

private theorem acceptedConductance_flip
    (K : RouteEOppositeParityKernel ι) (i j : ι)
    (hij : K.acceptedConductance i j ≠ 0) :
    K.sign i + K.sign j = 0 := by
  apply K.parity_reversing i j
  intro hP
  have hQ : K.edgeMass i j = 0 := by simp [edgeMass, hP]
  have hnonneg := K.edgeMass_nonneg j i
  apply hij
  simp [acceptedConductance, hQ, min_eq_left hnonneg]

private theorem abs_sub_eq_add_sub_two_min {a b : ℝ} :
    |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]
    ring

/-- Exact rejection identity: unused mass is half the total variation between the directed edge
law and its reversal. -/
theorem totalRejection_eq_half_edgeVariation (K : RouteEOppositeParityKernel ι) :
    K.totalRejection =
      (1 / 2 : ℝ) * ∑ i, ∑ j, |K.edgeMass i j - K.edgeMass j i| := by
  classical
  have hreverse : (∑ i, ∑ j, K.edgeMass j i) = ∑ i, K.weight i := by
    calc
      (∑ i, ∑ j, K.edgeMass j i) = ∑ j, ∑ i, K.edgeMass j i := Finset.sum_comm
      _ = ∑ j, K.weight j := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact K.sum_edgeMass j
  have hforward : (∑ i, ∑ j, K.edgeMass i j) = ∑ i, K.weight i := by
    apply Finset.sum_congr rfl
    intro i _hi
    exact K.sum_edgeMass i
  have hvariation :
      (∑ i, ∑ j, |K.edgeMass i j - K.edgeMass j i|) =
        2 * (∑ i, K.weight i - ∑ i, ∑ j, K.acceptedConductance i j) := by
    simp_rw [abs_sub_eq_add_sub_two_min]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      acceptedConductance]
    rw [hforward, hreverse]
    simp_rw [← Finset.mul_sum]
    ring
  rw [hvariation]
  simp only [totalRejection, rejectedAt, Finset.sum_sub_distrib]
  ring

/-- The exact accepted-conductance consumer: total rejection bounds signed current. -/
theorem abs_signedCurrent_le_totalRejection (K : RouteEOppositeParityKernel ι) :
    |K.signedCurrent| ≤ K.totalRejection := by
  classical
  simpa [signedCurrent, totalRejection, rejectedAt] using
    abs_sum_sign_weight_le_unusedConductance
      K.sign K.weight K.acceptedConductance K.sign_abs_one
      K.acceptedConductance_symm K.acceptedConductance_flip
      K.sum_acceptedConductance_le_weight

/-- Paper capstone: exact rejection identity together with the signed-current bound. -/
theorem rejection_identity_and_current_bound (K : RouteEOppositeParityKernel ι) :
    K.totalRejection =
        (1 / 2 : ℝ) * ∑ i, ∑ j, |K.edgeMass i j - K.edgeMass j i| ∧
      |K.signedCurrent| ≤ K.totalRejection :=
  ⟨K.totalRejection_eq_half_edgeVariation, K.abs_signedCurrent_le_totalRejection⟩

private theorem abs_sub_le_exp_defect_mul_left
    {a b η : ℝ} (hη : 0 ≤ η)
    (hab : a ≤ Real.exp η * b) (hba : b ≤ Real.exp η * a) :
    |a - b| ≤ (Real.exp η - 1) * a := by
  have hexp : 1 ≤ Real.exp η := Real.one_le_exp hη
  rcases le_total a b with hab' | hba'
  · rw [abs_of_nonpos (sub_nonpos.mpr hab')]
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hba')]
    calc
      a - b ≤ (Real.exp η - 1) * b := by linarith
      _ ≤ (Real.exp η - 1) * a :=
        mul_le_mul_of_nonneg_left hba' (sub_nonneg.mpr hexp)

/-- Sharp multiplicative Radon--Nikodym gate.  If every directed edge mass is within a factor
`exp η` of its reverse (in both orientations), then Metropolis rejection is at most
`(exp η - 1) / 2` of total mass. -/
theorem two_mul_totalRejection_le_exp_defect_mul_totalWeight
    (K : RouteEOppositeParityKernel ι) (η : ℝ) (hη : 0 ≤ η)
    (hbalance : ∀ i j, K.edgeMass i j ≤ Real.exp η * K.edgeMass j i) :
    2 * K.totalRejection ≤ (Real.exp η - 1) * K.totalWeight := by
  classical
  rw [K.totalRejection_eq_half_edgeVariation, ← K.sum_sum_edgeMass]
  have hvariation :
      (∑ i, ∑ j, |K.edgeMass i j - K.edgeMass j i|) ≤
        (Real.exp η - 1) * ∑ i, ∑ j, K.edgeMass i j := by
    calc
      (∑ i, ∑ j, |K.edgeMass i j - K.edgeMass j i|) ≤
          ∑ i, ∑ j, (Real.exp η - 1) * K.edgeMass i j := by
        exact Finset.sum_le_sum fun i _hi => Finset.sum_le_sum fun j _hj =>
          abs_sub_le_exp_defect_mul_left
            hη (hbalance i j) (hbalance j i)
      _ = (Real.exp η - 1) * ∑ i, ∑ j, K.edgeMass i j := by
        simp_rw [Finset.mul_sum]
  convert hvariation using 1
  ring

/-- Normalized sharp rate in the exact paper form. -/
theorem totalRejection_div_totalWeight_le_half_exp_defect
    (K : RouteEOppositeParityKernel ι) (η : ℝ) (hη : 0 ≤ η)
    (hweight : 0 < K.totalWeight)
    (hbalance : ∀ i j, K.edgeMass i j ≤ Real.exp η * K.edgeMass j i) :
    K.totalRejection / K.totalWeight ≤ (Real.exp η - 1) / 2 := by
  apply (div_le_iff₀ hweight).2
  have h := K.two_mul_totalRejection_le_exp_defect_mul_totalWeight η hη hbalance
  nlinarith [K.totalWeight_nonneg]

/-- If no directed edge has its reversal in support, the Metropolis conductance vanishes. -/
theorem acceptedConductance_eq_zero_of_reverse_disjoint
    (K : RouteEOppositeParityKernel ι)
    (hdisjoint : ∀ i j, K.edgeMass i j = 0 ∨ K.edgeMass j i = 0)
    (i j : ι) :
    K.acceptedConductance i j = 0 := by
  rcases hdisjoint i j with hij | hji
  · simp [acceptedConductance, hij, K.edgeMass_nonneg j i]
  · simp [acceptedConductance, hji, K.edgeMass_nonneg i j]

/-- Hostile sharpness law: disjoint forward/reverse support rejects all physical mass. -/
theorem totalRejection_eq_totalWeight_of_reverse_disjoint
    (K : RouteEOppositeParityKernel ι)
    (hdisjoint : ∀ i j, K.edgeMass i j = 0 ∨ K.edgeMass j i = 0) :
    K.totalRejection = K.totalWeight := by
  classical
  simp [totalRejection, rejectedAt, totalWeight,
    K.acceptedConductance_eq_zero_of_reverse_disjoint hdisjoint]

end RouteEOppositeParityKernel

end RHTower
