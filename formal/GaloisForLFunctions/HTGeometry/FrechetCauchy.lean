import GaloisForLFunctions.HTGeometry.FrechetTelescoping

/-!
# The partial sums along a halving basis are Cauchy

The telescoping bound says consecutive partial sums differ by an element of a late member of the
basis; since the basis presents the neighbourhood filter of the origin, that is exactly the Cauchy
condition.

* `halvingBasis_mono` : the basis is monotone.
* `cauchySeq_of_halvingBasis` : **the partial sums are Cauchy.**
-/

namespace GaloisForLFunctions

open Filter Set Pointwise Topology Uniformity

variable {E : Type*} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]

/-- A halving basis is monotone. -/
theorem halvingBasis_mono {C : ℕ → Set E} (hzero : ∀ n, (0 : E) ∈ C n)
    (hhalf : ∀ n, C (n + 1) + C (n + 1) ⊆ C n) {n j : ℕ} (hnj : n ≤ j) : C j ⊆ C n := by
  induction j, hnj using Nat.le_induction with
  | base => exact fun x hx => hx
  | succ k _ ih => exact (halvingBasis_antitone hzero hhalf k).trans ih

/-- **The partial sums of a series subordinate to a halving basis are Cauchy.** -/
theorem cauchySeq_of_halvingBasis {C : ℕ → Set E}
    (hbasis : (𝓝 (0 : E)).HasBasis (fun _ : ℕ => True) C)
    (hzero : ∀ n, (0 : E) ∈ C n) (hhalf : ∀ n, C (n + 1) + C (n + 1) ⊆ C n)
    (hsymm : ∀ n, -C n = C n)
    (a : ℕ → E) (m : ℕ) (ha : ∀ i, a i ∈ C (m + 1 + i)) :
    CauchySeq (fun q => ∑ i ∈ Finset.range q, a i) := by
  have huni : (𝓤 E).HasBasis (fun _ : ℕ => True)
      (fun n => (fun p : E × E => p.2 - p.1) ⁻¹' C n) := by
    rw [uniformity_eq_comap_nhds_zero]
    exact hbasis.comap _
  rw [huni.cauchySeq_iff]
  intro n _
  refine ⟨n, fun p hp q hq => ?_⟩
  show (∑ i ∈ Finset.range q, a i) - (∑ i ∈ Finset.range p, a i) ∈ C n
  rcases le_total p q with hpq | hqp
  · exact halvingBasis_mono hzero hhalf (by omega)
      (halvingBasis_sum_sub_mem hzero hhalf a m ha p q hpq)
  · have h := halvingBasis_mono hzero hhalf (n := n) (by omega)
      (halvingBasis_sum_sub_mem hzero hhalf a m ha q p hqp)
    have hneg : (∑ i ∈ Finset.range q, a i) - (∑ i ∈ Finset.range p, a i)
        = -((∑ i ∈ Finset.range p, a i) - (∑ i ∈ Finset.range q, a i)) := by abel
    rw [hneg, ← hsymm n]
    exact Set.neg_mem_neg.2 h

end GaloisForLFunctions
