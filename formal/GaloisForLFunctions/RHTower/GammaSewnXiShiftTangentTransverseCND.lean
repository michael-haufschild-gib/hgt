import GaloisForLFunctions.RHTower.GammaSewnXiShiftTangentHilbertKernel

/-!
# Source tangent transverse conditional negativity

The normalized prime-source tangent features already carry an exact off-diagonal sign law.
For every finite real coefficient packet on the transverse hyperplane `∑ i, c i = 0`, its
squared-distance quadratic form is exactly minus twice the all-depth squared resultant.  Thus
arbitrary coefficient interference has a coefficient-faithful sign at every finite depth, and
that sign survives the source-defined infinite-depth completion.

No Xi zero location or target data enters this construction.  This module does not identify the
source tangent distance kernel with the full completed prime–Gamma response kernel; that separate
coefficientwise intertwining theorem remains the next weld.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem hasSum_finset_sum_real
    {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ) (a : ι → ℝ)
    (h : ∀ i ∈ s, HasSum (f i) (a i)) :
    HasSum (fun e => ∑ i ∈ s, f i e) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hiSum := h i (Finset.mem_insert_self i s)
      have hsSum := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      simpa [Finset.sum_insert hi] using hiSum.add hsSum

/-- All-depth coefficient resultant of the normalized source tangent packet. -/
def gammaSewnXiShiftEndpointUnitTangentPacketResultant
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) (e : ℕ) : ℝ :=
  ∑ i, c i * gammaSewnXiShiftEndpointUnitTangentFeature (p i) e

/-- Squared-distance quadratic form of the all-depth source tangent packet. -/
def gammaSewnXiShiftEndpointUnitTangentPacketDistanceEnergy
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j *
    gammaSewnXiShiftEndpointUnitTangentDistanceSq (p i) (p j)

/-- Finite-depth negative square prefix. -/
def gammaSewnXiShiftEndpointUnitTangentPacketDepthPrefix
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) (D : ℕ) : ℝ :=
  -2 * ∑ e ∈ Finset.range D,
    gammaSewnXiShiftEndpointUnitTangentPacketResultant p c e ^ 2

/-- Arbitrary coefficient interference remains square-summable after the source-defined
all-depth completion. -/
theorem hasSum_gammaSewnXiShiftEndpointUnitTangentPacketResultant_sq
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) :
    HasSum
      (fun e => gammaSewnXiShiftEndpointUnitTangentPacketResultant p c e ^ 2)
      (∑ i, ∑ j, c i * c j *
        gammaSewnXiShiftEndpointUnitTangentKernel (p i) (p j)) := by
  classical
  have hpairs : ∀ i : Fin N, HasSum
      (fun e => ∑ j, c i * c j *
        (gammaSewnXiShiftEndpointUnitTangentFeature (p i) e *
          gammaSewnXiShiftEndpointUnitTangentFeature (p j) e))
      (∑ j, c i * c j *
        gammaSewnXiShiftEndpointUnitTangentKernel (p i) (p j)) := by
    intro i
    apply hasSum_finset_sum_real Finset.univ
    intro j _
    simpa only using
      (hasSum_gammaSewnXiShiftEndpointUnitTangentFeature_mul (p i) (p j)).mul_left
        (c i * c j)
  have hall : HasSum
      (fun e => ∑ i, ∑ j, c i * c j *
        (gammaSewnXiShiftEndpointUnitTangentFeature (p i) e *
          gammaSewnXiShiftEndpointUnitTangentFeature (p j) e))
      (∑ i, ∑ j, c i * c j *
        gammaSewnXiShiftEndpointUnitTangentKernel (p i) (p j)) := by
    apply hasSum_finset_sum_real Finset.univ
    intro i _
    exact hpairs i
  apply hall.congr_fun
  intro e
  unfold gammaSewnXiShiftEndpointUnitTangentPacketResultant
  rw [sq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact source-only off-diagonal factorization. On every transverse coefficient line, the
complete squared-distance response is minus twice the all-depth resultant energy. -/
theorem gammaSewnXiShiftEndpointUnitTangentPacketDistanceEnergy_eq_negative_tsum
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ)
    (hc : ∑ i, c i = 0) :
    gammaSewnXiShiftEndpointUnitTangentPacketDistanceEnergy p c =
      -2 * ∑' e : ℕ,
        gammaSewnXiShiftEndpointUnitTangentPacketResultant p c e ^ 2 := by
  have hsum :=
    (hasSum_gammaSewnXiShiftEndpointUnitTangentPacketResultant_sq p c).tsum_eq
  unfold gammaSewnXiShiftEndpointUnitTangentPacketDistanceEnergy
  simp_rw [gammaSewnXiShiftEndpointUnitTangentDistanceSq_eq]
  rw [hsum]
  calc
    (∑ i, ∑ j, c i * c j *
        (2 * (1 - gammaSewnXiShiftEndpointUnitTangentKernel (p i) (p j)))) =
        2 * (∑ i, c i) ^ 2 -
          2 * ∑ i, ∑ j, c i * c j *
            gammaSewnXiShiftEndpointUnitTangentKernel (p i) (p j) := by
      have hproduct :
          (∑ i, ∑ j, c i * c j) = (∑ i, c i) ^ 2 := by
        rw [sq, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      have hconst :
          (∑ i, ∑ j, c i * c j * 2) = 2 * (∑ i, c i) ^ 2 := by
        calc
          (∑ i, ∑ j, c i * c j * 2) =
              (∑ i, ∑ j, c i * c j) * 2 := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
          _ = 2 * (∑ i, c i) ^ 2 := by rw [hproduct]; ring
      have hkernel :
          (∑ i, ∑ j, c i * c j *
              (2 * gammaSewnXiShiftEndpointUnitTangentKernel (p i) (p j))) =
            2 * ∑ i, ∑ j, c i * c j *
              gammaSewnXiShiftEndpointUnitTangentKernel (p i) (p j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      simp_rw [mul_sub, mul_one]
      simp_rw [Finset.sum_sub_distrib]
      rw [hconst, hkernel]
    _ = -2 * ∑ i, ∑ j, c i * c j *
          gammaSewnXiShiftEndpointUnitTangentKernel (p i) (p j) := by
      rw [hc]
      ring

/-- Signed cancellation survives infinite-depth completion for arbitrary real coefficients. -/
theorem gammaSewnXiShiftEndpointUnitTangentPacketDistanceEnergy_nonpos
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ)
    (hc : ∑ i, c i = 0) :
    gammaSewnXiShiftEndpointUnitTangentPacketDistanceEnergy p c ≤ 0 := by
  rw [gammaSewnXiShiftEndpointUnitTangentPacketDistanceEnergy_eq_negative_tsum p c hc]
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
    (tsum_nonneg fun e => sq_nonneg _)

/-- Every finite-depth approximation already has the same nonpositive orientation. -/
theorem gammaSewnXiShiftEndpointUnitTangentPacketDepthPrefix_nonpos
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ) (D : ℕ) :
    gammaSewnXiShiftEndpointUnitTangentPacketDepthPrefix p c D ≤ 0 := by
  unfold gammaSewnXiShiftEndpointUnitTangentPacketDepthPrefix
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
    (Finset.sum_nonneg fun e _ => sq_nonneg _)

/-- Index stability through completion: finite depth prefixes converge to the exact transverse
distance energy, while retaining their sign at every stage. -/
theorem tendsto_gammaSewnXiShiftEndpointUnitTangentPacketDepthPrefix
    {N : ℕ} (p : Fin N → Nat.Primes) (c : Fin N → ℝ)
    (hc : ∑ i, c i = 0) :
    Tendsto
      (gammaSewnXiShiftEndpointUnitTangentPacketDepthPrefix p c)
      atTop
      (nhds (gammaSewnXiShiftEndpointUnitTangentPacketDistanceEnergy p c)) := by
  have h :=
    (hasSum_gammaSewnXiShiftEndpointUnitTangentPacketResultant_sq p c).tendsto_sum_nat
  have hscaled :
      Tendsto
        (fun D => (-2 : ℝ) * ∑ e ∈ Finset.range D,
          gammaSewnXiShiftEndpointUnitTangentPacketResultant p c e ^ 2)
        atTop
        (nhds ((-2 : ℝ) * ∑ i, ∑ j, c i * c j *
          gammaSewnXiShiftEndpointUnitTangentKernel (p i) (p j))) :=
    tendsto_const_nhds.mul h
  have hsum :=
    (hasSum_gammaSewnXiShiftEndpointUnitTangentPacketResultant_sq p c).tsum_eq
  rw [← hsum] at hscaled
  rw [gammaSewnXiShiftEndpointUnitTangentPacketDistanceEnergy_eq_negative_tsum p c hc]
  change Tendsto
    (fun D => (-2 : ℝ) * ∑ e ∈ Finset.range D,
      gammaSewnXiShiftEndpointUnitTangentPacketResultant p c e ^ 2)
    atTop
    (nhds ((-2 : ℝ) * ∑' e : ℕ,
      gammaSewnXiShiftEndpointUnitTangentPacketResultant p c e ^ 2))
  exact hscaled

end

end RHTower
