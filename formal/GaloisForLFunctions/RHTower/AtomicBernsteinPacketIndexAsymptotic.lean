import GaloisForLFunctions.RHTower.FiniteComplexPacketWeightedPerturbation
import GaloisForLFunctions.RHTower.FiniteBernsteinPacketIndexAsymptotic
import GaloisForLFunctions.RHTower.AtomicBernsteinMaximalPacketAsymptotic

/-!
# Full atomic Bernstein index asymptotics

The exact finite-coordinate decomposition and the summable complementary packet transfer the
index test law to the entire atomic source.
-/

open Filter Topology
open scoped BigOperators Real unitInterval

namespace RHTower

noncomputable section

def atomicBernsteinPacketIndexEnergy {ι : Type*} (c u : ι → ℂ) (g : I → ℝ) (n : ℕ) : ℝ :=
  ∑ k : Fin (n + 1), g (bernstein.z k) * ‖atomicBernsteinPacket c u n k‖ ^ 2

/-- The finite dominant index law survives the full, absolutely summable atomic complement. -/
theorem tendsto_atomicBernsteinPacketIndexEnergy_of_finiteCoordinatePacket
    {ι : Type*} (D : Finset ι) (c u : ι → ℂ) (hc : Summable c)
    {B beta L M : ℝ} (hB : 0 < B) (hbeta0 : 0 ≤ beta) (hbeta : beta < B)
    (hmain : ∀ q ∈ D, ‖u q‖ + ‖1 - u q‖ ≤ B)
    (htail : ∀ q ∉ D, ‖u q‖ + ‖1 - u q‖ ≤ beta)
    {g : I → ℝ} (hM : 0 ≤ M) (hg : ∀ x, |g x| ≤ M)
    (hlead : Tendsto (fun n : ℕ => Real.sqrt n / (B ^ 2) ^ n *
      finiteBernsteinCoordinatePacketIndexEnergy (D.image u)
        (finiteExponentialFiberCoefficient D c u) g n) atTop (nhds L)) :
    Tendsto (fun n : ℕ => Real.sqrt n / (B ^ 2) ^ n *
      atomicBernsteinPacketIndexEnergy c u g n) atTop (nhds L) := by
  classical
  have hall : ∀ q, ‖u q‖ + ‖1 - u q‖ ≤ B := by
    intro q
    by_cases hq : q ∈ D
    · exact hmain q hq
    · exact (htail q hq).trans hbeta.le
  have hA : 0 ≤ atomicWeightL1 (fun q : {q : ι // q ∈ D} => c q) :=
    tsum_nonneg fun _ => norm_nonneg _
  have ha : ∀ n : ℕ, (∑ k : Fin (n + 1),
      ‖finiteBernsteinCoordinatePacket (D.image u)
        (finiteExponentialFiberCoefficient D c u) n k‖) ≤
      atomicWeightL1 (fun q : {q : ι // q ∈ D} => c q) * B ^ n := by
    intro n
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      ‖finiteBernsteinCoordinatePacket (D.image u)
        (finiteExponentialFiberCoefficient D c u) n k‖) (n + 1)]
    exact finitePacketL1_finiteBernsteinCoordinatePacket_le D c u hc hmain n
  have hr : ∀ n : ℕ, (∑ k : Fin (n + 1), ‖atomicBernsteinComplementPacket D c u n k‖) ≤
      atomicWeightL1 (fun q : {q : ι // q ∉ D} => c q) * beta ^ n := by
    intro n
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => ‖atomicBernsteinComplementPacket D c u n k‖)
      (n + 1)]
    exact finitePacketL1_atomicBernsteinComplementPacket_le D c u hc htail n
  have h := tendsto_finiteWeightedComplexEnergy_add_of_exponentiallySmaller_l1
    (fun n => (Finset.univ : Finset (Fin (n + 1))))
    (fun n k => finiteBernsteinCoordinatePacket (D.image u)
      (finiteExponentialFiberCoefficient D c u) n k)
    (fun n k => atomicBernsteinComplementPacket D c u n k)
    (fun _ k => g (bernstein.z k)) hA hM hB hbeta0 hbeta
    (fun n k _ => hg (bernstein.z k)) ha hr hlead
  convert h using 1
  ext n
  apply congrArg (fun z : ℝ => Real.sqrt n / (B ^ 2) ^ n * z)
  apply Finset.sum_congr rfl
  intro k hk
  rw [atomicBernsteinPacket_eq_finiteCoordinate_add_complement D c u hc hall k.is_le]

end
end RHTower
