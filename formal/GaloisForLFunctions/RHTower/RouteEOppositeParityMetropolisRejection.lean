import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import GaloisForLFunctions.RHTower.MobiusBoundaryOppositeSignTransport

/-!
# Route E opposite-parity Metropolis rejection law

This module formalizes the exact finite theorem from
`route-e-opposite-parity-metropolis-rejection-law.md`.  A datum packages a finite weighted
opposite-parity Markov kernel.  Its Metropolis conductance is the minimum of each directed edge
mass and its reversal.  The total rejected mass is exactly one half of the edge-law total
variation and bounds the signed current.  Reversal absolute continuity additionally turns the
pair dissipation into twice the forward edge relative entropy, giving the sharp Pinsker rate.
The final statements instantiate the exact Gibbs likelihood-ratio oscillation.

No reversibility, analytic, or asymptotic premise is used.  Support absolute continuity appears
only where finite relative entropy requires it.
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

private lemma routeEPairEntropy_sq_le
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 * (a - b) ^ (2 : ℕ) ≤ (a + b) * ((a - b) * Real.log (a / b)) := by
  wlog hab : b ≤ a generalizing a b
  · have hswap := this b a hb ha (le_of_not_ge hab)
    have hlog : Real.log (b / a) = -Real.log (a / b) := by
      rw [Real.log_div hb.ne' ha.ne', Real.log_div ha.ne' hb.ne']
      ring
    rw [hlog] at hswap
    convert hswap using 1 <;> ring
  · have hdiff : 0 ≤ a - b := sub_nonneg.mpr hab
    have hx : 0 ≤ (a - b) / b := div_nonneg hdiff hb.le
    have hlog := Real.le_log_one_add_of_nonneg hx
    have hone : 1 + (a - b) / b = a / b := by
      field_simp [hb.ne']
      ring
    have hleft : 2 * ((a - b) / b) / ((a - b) / b + 2) =
        2 * (a - b) / (a + b) := by
      field_simp [ha.ne', hb.ne', (add_pos ha hb).ne']
      ring
    rw [hone, hleft] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hdiff
    have hadd : 0 ≤ a + b := (add_pos ha hb).le
    have hmul' := mul_le_mul_of_nonneg_left hmul hadd
    calc
      2 * (a - b) ^ (2 : ℕ) =
          (a + b) * ((a - b) * (2 * (a - b) / (a + b))) := by
            field_simp [(add_pos ha hb).ne']
      _ ≤ (a + b) * ((a - b) * Real.log (a / b)) := hmul'

private lemma routeEPairEntropy_sq_le_of_zero_iff
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : a = 0 ↔ b = 0) :
    2 * (a - b) ^ (2 : ℕ) ≤ (a + b) * ((a - b) * Real.log (a / b)) := by
  by_cases ha0 : a = 0
  · rw [ha0, hz.mp ha0]
    norm_num
  · have hb0 : b ≠ 0 := fun h ↦ ha0 (hz.mpr h)
    exact routeEPairEntropy_sq_le a b (lt_of_le_of_ne ha (Ne.symm ha0))
      (lt_of_le_of_ne hb (Ne.symm hb0))

private lemma routeEPairEntropy_nonneg_of_zero_iff
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : a = 0 ↔ b = 0) :
    0 ≤ (a - b) * Real.log (a / b) := by
  by_cases ha0 : a = 0
  · rw [ha0, hz.mp ha0]
    norm_num
  · have hb0 : b ≠ 0 := fun h ↦ ha0 (hz.mpr h)
    have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have h := routeEPairEntropy_sq_le a b ha' hb'
    have hprod : 0 ≤ (a + b) * ((a - b) * Real.log (a / b)) :=
      (mul_nonneg (by positivity) (sq_nonneg _)).trans h
    exact (mul_nonneg_iff_of_pos_left (add_pos ha' hb')).mp hprod

/-- Finite edge law is absolutely continuous with respect to reversal. -/
def ReverseAbsolutelyContinuous (K : RouteEOppositeParityKernel ι) : Prop :=
  ∀ i j, K.edgeMass j i = 0 → K.edgeMass i j = 0

/-- Forward relative entropy of normalized edge law against its reversal. -/
noncomputable def edgeRelativeEntropy (K : RouteEOppositeParityKernel ι) : ℝ :=
  (∑ i, ∑ j, K.edgeMass i j * Real.log (K.edgeMass i j / K.edgeMass j i)) /
    K.totalWeight

/-- Normalized directed edge law. -/
noncomputable def normalizedEdgeMass (K : RouteEOppositeParityKernel ι) (i j : ι) : ℝ :=
  K.edgeMass i j / K.totalWeight

/-- Total unnormalized edge-law variation against reversal. -/
def edgeVariationMass (K : RouteEOppositeParityKernel ι) : ℝ :=
  ∑ i, ∑ j, |K.edgeMass i j - K.edgeMass j i|

private lemma log_reverse_div
    (a b : ℝ) (hz : a = 0 ↔ b = 0) :
    Real.log (b / a) = -Real.log (a / b) := by
  by_cases ha : a = 0
  · rw [ha, hz.mp ha]
    norm_num
  · have hb : b ≠ 0 := fun h ↦ ha (hz.mpr h)
    rw [Real.log_div hb ha, Real.log_div ha hb]
    ring

private theorem pairEntropy_sum_eq_two_mul_forward
    (K : RouteEOppositeParityKernel ι) (hac : K.ReverseAbsolutelyContinuous) :
    (∑ i, ∑ j,
        (K.edgeMass i j - K.edgeMass j i) *
          Real.log (K.edgeMass i j / K.edgeMass j i)) =
      2 * ∑ i, ∑ j,
        K.edgeMass i j * Real.log (K.edgeMass i j / K.edgeMass j i) := by
  classical
  have hzero : ∀ i j, K.edgeMass i j = 0 ↔ K.edgeMass j i = 0 :=
    fun i j ↦ ⟨hac j i, hac i j⟩
  have hreverse :
      (∑ i, ∑ j,
          K.edgeMass j i * Real.log (K.edgeMass i j / K.edgeMass j i)) =
        -(∑ i, ∑ j,
          K.edgeMass i j * Real.log (K.edgeMass i j / K.edgeMass j i)) := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [log_reverse_div (K.edgeMass i j) (K.edgeMass j i) (hzero i j)]
    ring
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [hreverse]
  ring

/-- The finite formula is literally KL divergence of normalized edge law from its reversal. -/
theorem edgeRelativeEntropy_eq_normalizedEdgeLawSum
    (K : RouteEOppositeParityKernel ι) (hweight : 0 < K.totalWeight) :
    K.edgeRelativeEntropy =
      ∑ i, ∑ j, K.normalizedEdgeMass i j *
        Real.log (K.normalizedEdgeMass i j / K.normalizedEdgeMass j i) := by
  classical
  have hratio : ∀ i j,
      K.normalizedEdgeMass i j / K.normalizedEdgeMass j i =
        K.edgeMass i j / K.edgeMass j i := by
    intro i j
    simp only [normalizedEdgeMass]
    field_simp [hweight.ne']
  simp_rw [hratio, normalizedEdgeMass, div_mul_eq_mul_div, ← Finset.sum_div]
  rfl

private theorem edgeVariationMass_sq_le
    (K : RouteEOppositeParityKernel ι) (hac : K.ReverseAbsolutelyContinuous) :
    K.edgeVariationMass ^ (2 : ℕ) ≤
      2 * K.totalWeight *
        (∑ i, ∑ j,
          K.edgeMass i j * Real.log (K.edgeMass i j / K.edgeMass j i)) := by
  classical
  have hzero : ∀ i j, K.edgeMass i j = 0 ↔ K.edgeMass j i = 0 :=
    fun i j ↦ ⟨hac j i, hac i j⟩
  let pairEntropy : ι × ι → ℝ := fun e ↦
    (K.edgeMass e.1 e.2 - K.edgeMass e.2 e.1) *
      Real.log (K.edgeMass e.1 e.2 / K.edgeMass e.2 e.1)
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset (ι × ι))
    (r := fun e ↦ |K.edgeMass e.1 e.2 - K.edgeMass e.2 e.1|)
    (f := fun e ↦ K.edgeMass e.1 e.2 + K.edgeMass e.2 e.1)
    (g := fun e ↦ pairEntropy e / 2)
    (fun e _ ↦ add_nonneg (K.edgeMass_nonneg _ _) (K.edgeMass_nonneg _ _))
    (fun e _ ↦ div_nonneg
      (routeEPairEntropy_nonneg_of_zero_iff _ _
        (K.edgeMass_nonneg _ _) (K.edgeMass_nonneg _ _) (hzero _ _)) (by norm_num))
    (fun e _ ↦ by
      have hp := routeEPairEntropy_sq_le_of_zero_iff
        (K.edgeMass e.1 e.2) (K.edgeMass e.2 e.1)
        (K.edgeMass_nonneg _ _) (K.edgeMass_nonneg _ _) (hzero _ _)
      dsimp [pairEntropy]
      rw [sq_abs]
      nlinarith)
  have hfirst :
      (∑ e : ι × ι, (K.edgeMass e.1 e.2 + K.edgeMass e.2 e.1)) =
        2 * K.totalWeight := by
    rw [Fintype.sum_prod_type]
    simp_rw [Finset.sum_add_distrib]
    rw [K.sum_sum_edgeMass]
    have hreverse : (∑ i, ∑ j, K.edgeMass j i) = K.totalWeight := by
      rw [Finset.sum_comm]
      exact K.sum_sum_edgeMass
    rw [hreverse]
    ring
  have hsecond :
      (∑ e : ι × ι, pairEntropy e / 2) =
        (∑ i, ∑ j,
          K.edgeMass i j * Real.log (K.edgeMass i j / K.edgeMass j i)) := by
    rw [Fintype.sum_prod_type]
    dsimp [pairEntropy]
    simp_rw [← Finset.sum_div]
    rw [K.pairEntropy_sum_eq_two_mul_forward hac]
    ring
  rw [Fintype.sum_prod_type] at hcs
  change K.edgeVariationMass ^ (2 : ℕ) ≤ _ at hcs
  rw [hfirst, hsecond] at hcs
  simpa [mul_assoc] using hcs

/-- Pinsker rate specialized to reversal: rejection fraction is controlled by edge entropy. -/
theorem totalRejection_div_totalWeight_le_sqrt_half_edgeRelativeEntropy
    (K : RouteEOppositeParityKernel ι)
    (hac : K.ReverseAbsolutelyContinuous) (hweight : 0 < K.totalWeight) :
    K.totalRejection / K.totalWeight ≤ Real.sqrt (K.edgeRelativeEntropy / 2) := by
  have hsq := K.edgeVariationMass_sq_le hac
  have hreject : K.totalRejection = (1 / 2 : ℝ) * K.edgeVariationMass := by
    simpa [edgeVariationMass] using K.totalRejection_eq_half_edgeVariation
  have hentropy : 0 ≤ K.edgeRelativeEntropy := by
    have hforward : 0 ≤
        (∑ i, ∑ j,
          K.edgeMass i j * Real.log (K.edgeMass i j / K.edgeMass j i)) := by
      have hpair := K.pairEntropy_sum_eq_two_mul_forward hac
      have hpair_nonneg : 0 ≤
          (∑ i, ∑ j,
            (K.edgeMass i j - K.edgeMass j i) *
              Real.log (K.edgeMass i j / K.edgeMass j i)) := by
        apply Finset.sum_nonneg
        intro i _hi
        apply Finset.sum_nonneg
        intro j _hj
        exact routeEPairEntropy_nonneg_of_zero_iff _ _
          (K.edgeMass_nonneg _ _) (K.edgeMass_nonneg _ _)
          ⟨hac j i, hac i j⟩
      nlinarith
    exact div_nonneg hforward hweight.le
  have hreject_nonneg : 0 ≤ K.totalRejection := by
    apply Finset.sum_nonneg
    intro i _hi
    exact K.rejectedAt_nonneg i
  apply (Real.le_sqrt (div_nonneg hreject_nonneg hweight.le)
    (div_nonneg hentropy (by norm_num))).2
  rw [hreject]
  dsimp [edgeRelativeEntropy] at *
  field_simp [hweight.ne'] at *
  nlinarith

/-- Literal logarithmic detailed balance implies the paper's exponential rejection rate. -/
theorem totalRejection_div_totalWeight_le_half_exp_defect_of_log_ratio
    (K : RouteEOppositeParityKernel ι) (η : ℝ) (hη : 0 ≤ η)
    (hweight : 0 < K.totalWeight) (hac : K.ReverseAbsolutelyContinuous)
    (hlog : ∀ i j, K.edgeMass i j ≠ 0 →
      |Real.log (K.edgeMass i j / K.edgeMass j i)| ≤ η) :
    K.totalRejection / K.totalWeight ≤ (Real.exp η - 1) / 2 := by
  apply K.totalRejection_div_totalWeight_le_half_exp_defect η hη hweight
  intro i j
  by_cases ha0 : K.edgeMass i j = 0
  · rw [ha0]
    exact mul_nonneg (Real.exp_pos η).le (K.edgeMass_nonneg j i)
  · have hb0 : K.edgeMass j i ≠ 0 := fun h ↦ ha0 (hac i j h)
    have ha : 0 < K.edgeMass i j :=
      lt_of_le_of_ne (K.edgeMass_nonneg i j) (Ne.symm ha0)
    have hb : 0 < K.edgeMass j i :=
      lt_of_le_of_ne (K.edgeMass_nonneg j i) (Ne.symm hb0)
    have hlogle : Real.log (K.edgeMass i j / K.edgeMass j i) ≤ η :=
      (le_abs_self _).trans (hlog i j ha0)
    have hratio : K.edgeMass i j / K.edgeMass j i ≤ Real.exp η := by
      have hexp := Real.exp_le_exp.mpr hlogle
      rw [Real.exp_log (div_pos ha hb)] at hexp
      exact hexp
    calc
      K.edgeMass i j = (K.edgeMass i j / K.edgeMass j i) * K.edgeMass j i := by
        field_simp [hb0]
      _ ≤ Real.exp η * K.edgeMass j i :=
        mul_le_mul_of_nonneg_right hratio hb.le

end RouteEOppositeParityKernel

/-- One-site Gibbs weight used by the opposite-parity likelihood-ratio instantiation. -/
noncomputable def routeEGibbsLikelihoodWeight (X energy : ℝ) : ℝ :=
  Real.exp (-energy / X)

/-- Exact Gibbs likelihood-ratio oscillation, with no asymptotic remainder. -/
theorem abs_log_routeEGibbsLikelihoodWeight_div
    (X m n : ℝ) (hX : 0 < X) :
    |Real.log (routeEGibbsLikelihoodWeight X m / routeEGibbsLikelihoodWeight X n)| =
      |m - n| / X := by
  simp only [routeEGibbsLikelihoodWeight,
    Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _), Real.log_exp]
  have hrewrite : -m / X - -n / X = -(m - n) / X := by ring
  rw [hrewrite, abs_div, abs_neg, abs_of_pos hX]

/-- A finite energy aperture gives the exact pairwise Gibbs logarithmic defect. -/
theorem abs_log_routeEGibbsLikelihoodWeight_div_le
    (X H m n : ℝ) (hX : 0 < X) (hspan : |m - n| ≤ H) :
    |Real.log (routeEGibbsLikelihoodWeight X m / routeEGibbsLikelihoodWeight X n)| ≤
      H / X := by
  rw [abs_log_routeEGibbsLikelihoodWeight_div X m n hX]
  exact div_le_div_of_nonneg_right hspan hX.le

end RHTower
