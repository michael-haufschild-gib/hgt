import GaloisForLFunctions.HTGeometry.PrimeTorsionOrbitAvoidance
import GaloisForLFunctions.RHTower.FiniteGridChoiRayCap

/-!
# Complete prime-torsion polygons avoiding arbitrary circuit rays

The finite-grid moment law, arbitrary-ray cap reduction, and exact prime
orbit incidence count are combined here.  Under one explicit growing-replica
budget, every nonidentity point of one prime-order Choi polygon is farther
than `epsilon` from every normalized target in an arbitrary finite
dictionary.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Exact cardinal form of complete prime-torsion avoidance for arbitrary
normalized target rays. -/
theorem exists_primeTorsion_complete_circuitRay_avoidance
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p d : ℕ) [Fact p.Prime]
    (target : Y → EuclideanSpace ℂ (Fin d × Fin d)) (epsilon : ℝ)
    (hsmall : (p - 1) *
        (finiteGridChoiTargetCaptureSet p d target epsilon).card < p ^ d) :
    ∃ q : Fin d → ZMod p,
      ∀ a : ZMod p, a ≠ 0 → ∀ y : Y,
        epsilon < pureStateTraceDistance
          (finiteGridChoiVector p d fun i => a * q i) (target y) := by
  let bad := finiteGridChoiTargetCaptureSet p d target epsilon
  obtain ⟨q, hq⟩ :=
    exists_primeTorsion_complete_avoidance p d bad (by simpa [bad] using hsmall)
  refine ⟨q, ?_⟩
  intro a ha y
  by_contra hclose
  have hcapture : pureStateTraceDistance
      (finiteGridChoiVector p d fun i => a * q i) (target y) ≤ epsilon :=
    not_lt.mp hclose
  apply hq a ha
  exact Finset.mem_biUnion.mpr
    ⟨y, Finset.mem_univ y, by
      simpa [finiteGridChoiRayCaptureSet] using hcapture⟩

/-- **Complete circuit-ray polygon law.** Let `p` be prime and let `2n<p`.
For any finite dictionary of normalized states in the full Choi Hilbert
space, the displayed replica budget produces one order-`p` diagonal-unitary
Choi polygon whose every nonidentity point avoids every target by strict
trace distance `epsilon`.  Targets need not be diagonal or lie on the grid. -/
theorem exists_primeTorsion_complete_circuitRay_avoidance_of_replicaBudget
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p d : ℕ) [Fact p.Prime] (hd : 0 < d)
    (target : Y → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ y, ‖target y‖ = 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon < 1 / 2)
    (n : ℕ) (hreplica : 2 * n < p)
    (hbudget :
      (((p - 1) * Fintype.card Y : ℕ) : ℝ) * (n.factorial : ℝ) *
          ((d : ℝ)⁻¹) ^ n <
        (Real.sqrt (1 - 4 * epsilon ^ (2 : ℕ))) ^ (2 * n)) :
    ∃ q : Fin d → ZMod p,
      ∀ a : ZMod p, a ≠ 0 → ∀ y : Y,
        epsilon < pureStateTraceDistance
          (finiteGridChoiVector p d fun i => a * q i) (target y) := by
  let threshold := Real.sqrt (1 - 4 * epsilon ^ (2 : ℕ))
  have hsumSq :
      ∑ i : Fin d, finiteGridChoiWeight d i ^ (2 : ℕ) = (d : ℝ)⁻¹ :=
    finiteGridChoiWeight_sq_sum hd
  have hprod : 0 < (1 / 2 - epsilon) * (1 / 2 + epsilon) :=
    mul_pos (sub_pos.mpr hepsilonHalf) (by linarith)
  have hrad : 0 < 1 - 4 * epsilon ^ (2 : ℕ) := by
    nlinarith
  have hthreshold : 0 < threshold := Real.sqrt_pos.2 hrad
  have hcap := finiteGridCoherenceCap_card_mul_pow_le_factorial
    p (finiteGridChoiWeight_nonneg d) n hreplica threshold hthreshold.le
  rw [hsumSq] at hcap
  have hbadCard := finiteGridChoiTargetCaptureSet_card_le
    (M := p) (d := d) hd target htarget hepsilon hepsilonHalf.le
  let A : ℝ := (((p - 1) * Fintype.card Y : ℕ) : ℝ)
  let B : ℝ :=
    ((finiteGridCoherenceCap p (finiteGridChoiWeight d) threshold).card : ℝ)
  let P : ℝ := (p : ℝ) ^ d
  let F : ℝ := (n.factorial : ℝ) * ((d : ℝ)⁻¹) ^ n
  let T : ℝ := threshold ^ (2 * n)
  have hA : 0 ≤ A := by positivity
  have hP : 0 < P := by
    exact pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  have hT : 0 < T := pow_pos hthreshold _
  have hcap' : B * T ≤ P * F := by
    simpa [B, T, P, F, Fintype.card_fin, mul_assoc] using hcap
  have hbudget' : A * F < T := by
    simpa [A, F, T, threshold, mul_assoc] using hbudget
  have hAB : A * B < P := by
    have hABT : (A * B) * T < P * T := calc
      (A * B) * T = A * (B * T) := by ring
      _ ≤ A * (P * F) := mul_le_mul_of_nonneg_left hcap' hA
      _ = P * (A * F) := by ring
      _ < P * T := mul_lt_mul_of_pos_left hbudget' hP
    nlinarith
  have hcapSmall : (p - 1) * Fintype.card Y *
      (finiteGridCoherenceCap p (finiteGridChoiWeight d) threshold).card <
        p ^ d := by
    have hcast :
        (((p - 1) * Fintype.card Y *
          (finiteGridCoherenceCap p
            (finiteGridChoiWeight d) threshold).card : ℕ) : ℝ) <
          ((p ^ d : ℕ) : ℝ) := by
      push_cast
      simpa [A, B, P, mul_assoc] using hAB
    exact_mod_cast hcast
  have hsmall : (p - 1) *
      (finiteGridChoiTargetCaptureSet p d target epsilon).card < p ^ d :=
    lt_of_le_of_lt (Nat.mul_le_mul_left (p - 1) hbadCard)
      (by simpa [threshold, mul_assoc] using hcapSmall)
  exact exists_primeTorsion_complete_circuitRay_avoidance
    p d target epsilon hsmall

end RHTower
