import GaloisForLFunctions.RHTower.FiniteComplexPacketEnergyPerturbation
import GaloisForLFunctions.RHTower.AtomicBernsteinPacketRpowGrowth

/-!
# Atomic Bernstein maximal-packet transfer

An absolutely summable atomic Bernstein packet splits exactly into a finite coordinate packet and
its complementary subtype.  If the complement has a uniformly smaller affine amplitude, its `l1`
norm is exponentially smaller and the finite packet's sharp half-order square-energy limit
survives unchanged in the complete atomic packet.
-/

open Complex Filter Topology
open scoped BigOperators Real

namespace RHTower

noncomputable section

/-- Bernstein packet carried by the complement of a finite index set. -/
def atomicBernsteinComplementPacket {I : Type*}
    (D : Finset I) (c u : I → ℂ) : ℕ → ℕ → ℂ :=
  atomicBernsteinPacket
    (fun j : {j : I // j ∉ D} => c j)
    (fun j : {j : I // j ∉ D} => u j)

/-- Collapsing equal coordinates and aggregating weights preserves every finite Bernstein row. -/
theorem finiteBernsteinCoordinatePacket_image_eq
    {I : Type*} (D : Finset I) (c u : I → ℂ) (n k : ℕ) :
    finiteBernsteinCoordinatePacket (D.image u)
        (finiteExponentialFiberCoefficient D c u) n k =
      ∑ j ∈ D, c j * bernsteinAffineRowCoefficient (u j) n k := by
  classical
  rw [finiteBernsteinCoordinatePacket]
  calc
    (∑ x ∈ D.image u,
        finiteExponentialFiberCoefficient D c u x *
          bernsteinAffineRowCoefficient x n k) =
      ∑ x ∈ D.image u, ∑ j ∈ D with u j = x,
        c j * bernsteinAffineRowCoefficient (u j) n k := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [finiteExponentialFiberCoefficient, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    _ = ∑ j ∈ D, c j * bernsteinAffineRowCoefficient (u j) n k :=
      Finset.sum_fiberwise_of_maps_to
        (fun j hj => Finset.mem_image_of_mem u hj)
        (fun j => c j * bernsteinAffineRowCoefficient (u j) n k)

/-- Exact split of an absolutely summable atomic packet into a finite part and its complement. -/
theorem atomicBernsteinPacket_eq_finiteCoordinate_add_complement
    {I : Type*} (D : Finset I) (c u : I → ℂ) (hc : Summable c)
    {B : ℝ} (hamp : ∀ j : I, ‖u j‖ + ‖1 - u j‖ ≤ B)
    {n k : ℕ} (hk : k ≤ n) :
    atomicBernsteinPacket c u n k =
      finiteBernsteinCoordinatePacket (D.image u)
          (finiteExponentialFiberCoefficient D c u) n k +
        atomicBernsteinComplementPacket D c u n k := by
  have hsumm := summable_atomicBernsteinCoefficientTerm hc hamp hk
  have hsplit := hsumm.sum_add_tsum_subtype_compl D
  rw [atomicBernsteinPacket, atomicBernsteinCoefficient,
    atomicBernsteinComplementPacket, atomicBernsteinPacket,
    atomicBernsteinCoefficient]
  rw [finiteBernsteinCoordinatePacket_image_eq]
  simpa only [atomicBernsteinCoefficientTerm, bernsteinAffineRowCoefficient,
    mul_assoc] using hsplit.symm

/-- A finite-coordinate packet is the same atomic packet indexed by the finite subtype. -/
theorem atomicBernsteinPacket_subtype_mem_eq_finiteCoordinatePacket
    {I : Type*} (D : Finset I) (c u : I → ℂ) :
    atomicBernsteinPacket
        (fun j : {j : I // j ∈ D} => c j)
        (fun j : {j : I // j ∈ D} => u j) =
      finiteBernsteinCoordinatePacket (D.image u)
        (finiteExponentialFiberCoefficient D c u) := by
  classical
  funext n k
  rw [finiteBernsteinCoordinatePacket_image_eq, atomicBernsteinPacket,
    atomicBernsteinCoefficient, tsum_fintype]
  rw [Finset.sum_subtype D (fun _ => Iff.rfl)
    (fun j => c j * bernsteinAffineRowCoefficient (u j) n k)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [atomicBernsteinCoefficientTerm, bernsteinAffineRowCoefficient]
  ring

/-- `l1` bound for a finite aggregated coordinate packet. -/
theorem finitePacketL1_finiteBernsteinCoordinatePacket_le
    {I : Type*} (D : Finset I) (c u : I → ℂ) (hc : Summable c)
    {B : ℝ} (hamp : ∀ j ∈ D, ‖u j‖ + ‖1 - u j‖ ≤ B) (n : ℕ) :
    finitePacketL1
        (finiteBernsteinCoordinatePacket (D.image u)
          (finiteExponentialFiberCoefficient D c u)) n ≤
      atomicWeightL1 (fun j : {j : I // j ∈ D} => c j) * B ^ n := by
  have hcD : Summable (fun j : {j : I // j ∈ D} => c j) := hc.subtype _
  have hDamp : ∀ j : {j : I // j ∈ D},
      ‖u j‖ + ‖1 - u j‖ ≤ B := fun j => hamp j j.2
  have h := finitePacketL1_atomicBernsteinPacket_le hcD hDamp n
  rw [atomicBernsteinPacket_subtype_mem_eq_finiteCoordinatePacket D c u] at h
  exact h

/-- `l1` bound for the complement of a finite atomic packet. -/
theorem finitePacketL1_atomicBernsteinComplementPacket_le
    {I : Type*} (D : Finset I) (c u : I → ℂ) (hc : Summable c)
    {beta : ℝ} (hamp : ∀ j ∉ D, ‖u j‖ + ‖1 - u j‖ ≤ beta) (n : ℕ) :
    finitePacketL1 (atomicBernsteinComplementPacket D c u) n ≤
      atomicWeightL1 (fun j : {j : I // j ∉ D} => c j) * beta ^ n := by
  exact finitePacketL1_atomicBernsteinPacket_le (hc.subtype _)
    (fun j => hamp j j.2) n

/-- Square energy of an absolutely summable atomic Bernstein packet. -/
def atomicBernsteinPacketSquareEnergy {I : Type*}
    (c u : I → ℂ) (n : ℕ) : ℝ :=
  finiteComplexPacketSquareEnergy (atomicBernsteinPacket c u n) (n + 1)

/-- A uniformly submaximal atomic complement does not change the leading finite packet's sharp
half-order energy limit. -/
theorem tendsto_atomicBernsteinPacketSquareEnergy_of_finiteCoordinatePacket
    {I : Type*} (D : Finset I) (c u : I → ℂ) (hc : Summable c)
    {B beta L : ℝ} (hB : 0 < B) (hbeta0 : 0 ≤ beta) (hbeta : beta < B)
    (hDamp : ∀ j ∈ D, ‖u j‖ + ‖1 - u j‖ ≤ B)
    (hsub : ∀ j ∉ D, ‖u j‖ + ‖1 - u j‖ ≤ beta)
    (hlead : Tendsto
      (fun n : ℕ => Real.sqrt n *
        finiteBernsteinCoordinatePacketEnergy (D.image u)
          (finiteExponentialFiberCoefficient D c u) n / (B ^ (2 : ℕ)) ^ n)
      atTop (nhds L)) :
    Tendsto
      (fun n : ℕ => Real.sqrt n * atomicBernsteinPacketSquareEnergy c u n /
        (B ^ (2 : ℕ)) ^ n)
      atTop (nhds L) := by
  let a : ℕ → ℕ → ℂ := fun n =>
    finiteBernsteinCoordinatePacket (D.image u)
      (finiteExponentialFiberCoefficient D c u) n
  let r : ℕ → ℕ → ℂ := fun n => atomicBernsteinComplementPacket D c u n
  let A : ℝ := atomicWeightL1 (fun j : {j : I // j ∈ D} => c j)
  let R : ℝ := atomicWeightL1 (fun j : {j : I // j ∉ D} => c j)
  have hA : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  have ha (n : ℕ) : ∑ k ∈ Finset.range (n + 1), ‖a n k‖ ≤ A * B ^ n := by
    exact finitePacketL1_finiteBernsteinCoordinatePacket_le D c u hc hDamp n
  have hr (n : ℕ) : ∑ k ∈ Finset.range (n + 1), ‖r n k‖ ≤ R * beta ^ n := by
    exact finitePacketL1_atomicBernsteinComplementPacket_le D c u hc hsub n
  have hlead' : Tendsto
      (fun n : ℕ => Real.sqrt n * finiteComplexPacketSquareEnergy (a n) (n + 1) /
        (B ^ (2 : ℕ)) ^ n) atTop (nhds L) := by
    simpa only [a, finiteComplexPacketSquareEnergy,
      finiteBernsteinCoordinatePacketEnergy] using hlead
  have htransfer :=
    tendsto_finiteComplexPacketSquareEnergy_add_of_exponentiallySmaller_l1
      a r hA hB hbeta0 hbeta ha hr hlead'
  apply htransfer.congr'
  filter_upwards with n
  congr 2
  rw [atomicBernsteinPacketSquareEnergy]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hglobal : ∀ j : I, ‖u j‖ + ‖1 - u j‖ ≤ B := by
    intro j
    by_cases hj : j ∈ D
    · exact (hDamp j hj).trans (by linarith)
    · exact (hsub j hj).trans hbeta.le
  rw [atomicBernsteinPacket_eq_finiteCoordinate_add_complement
    (B := B) D c u hc hglobal hkn]

end

end RHTower
