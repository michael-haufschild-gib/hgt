import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticSmallJetCorrection
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Antitone-neighborhood Cauchy criterion

A rapidly shrinking symmetric neighborhood basis in a complete uniform additive group replaces
numerical norm estimates.  If the `n`th increment lies in the symmetric part of the
`(n+1)`st basis neighborhood, then every tail lies in the `n`th neighborhood and the sequence is
Cauchy.
-/

open Filter Set Topology
open scoped Pointwise Uniformity

namespace RHTower

noncomputable section

/--
Rapidly shrinking symmetric increments produce a Cauchy sequence.
-/
theorem cauchySeq_of_antitone_add_basis_increments
    {E : Type*} [UniformSpace E] [AddCommGroup E]
    [IsUniformAddGroup E]
    (u : ℕ → Set E)
    (hu : (𝓝 (0 : E)).HasAntitoneBasis u)
    (hadd : ∀ n, u (n + 1) + u (n + 1) ⊆ u n)
    (F : ℕ → E)
    (hstep :
      ∀ n,
        F (n + 1) - F n ∈
          u (n + 1) ∩ -(u (n + 1))) :
    CauchySeq F := by
  let v : ℕ → Set E :=
    fun n => u n ∩ -(u n)
  have hvzero :
      ∀ n, (0 : E) ∈ v n := by
    intro n
    exact
      mem_of_mem_nhds
        (inter_mem (hu.mem n)
          (neg_mem_nhds_zero E (hu.mem n)))
  have hvadd :
      ∀ n, v (n + 1) + v (n + 1) ⊆ v n := by
    intro n z hz
    rw [Set.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    refine ⟨?_, ?_⟩
    · exact
        hadd n
          ((Set.mem_add).2
            ⟨x, hx.1, y, hy.1, rfl⟩)
    · have hnx :
          -x ∈ u (n + 1) := by
        simpa using hx.2
      have hny :
          -y ∈ u (n + 1) := by
        simpa using hy.2
      have hneg :
          -(x + y) ∈ u n := by
        have :=
          hadd n
            ((Set.mem_add).2
              ⟨-x, hnx, -y, hny, rfl⟩)
        simpa [add_comm] using this
      simpa using hneg
  have htail :
      ∀ d m : ℕ,
        F (m + d) - F m ∈ v m := by
    intro d
    induction d with
    | zero =>
        intro m
        simpa using hvzero m
    | succ d ih =>
        intro m
        have hinc :
            F (m + 1) - F m ∈ v (m + 1) :=
          hstep m
        have hrest :
            F ((m + 1) + d) - F (m + 1) ∈
              v (m + 1) :=
          ih (m + 1)
        have hsum :
            (F (m + 1) - F m) +
                (F ((m + 1) + d) - F (m + 1)) ∈
              v m :=
          hvadd m
            ((Set.mem_add).2
              ⟨F (m + 1) - F m, hinc,
                F ((m + 1) + d) - F (m + 1),
                hrest, rfl⟩)
        have hidx :
            m + (d + 1) = (m + 1) + d := by
          omega
        rw [hidx]
        convert hsum using 1
        abel
  have hUniformBasis :
      (𝓤 E).HasAntitoneBasis
        (fun n =>
          {p : E × E | p.2 - p.1 ∈ u n}) := by
    rw [uniformity_eq_comap_nhds_zero E]
    exact hu.comap fun p : E × E => p.2 - p.1
  rw [hUniformBasis.toHasBasis.cauchySeq_iff]
  intro i hi
  refine ⟨i, ?_⟩
  intro m him n hin
  change F n - F m ∈ u i
  by_cases hmn : m ≤ n
  · have ht := htail (n - m) m
    have hidx : m + (n - m) = n :=
      Nat.add_sub_of_le hmn
    rw [hidx] at ht
    exact hu.antitone him ht.1
  · have hnm : n ≤ m :=
      le_of_not_ge hmn
    have ht := htail (m - n) n
    have hidx : n + (m - n) = m :=
      Nat.add_sub_of_le hnm
    rw [hidx] at ht
    have hneg :
        F n - F m ∈ u n := by
      have :
          -(F m - F n) ∈ u n := by
        simpa using ht.2
      simpa using this
    exact hu.antitone hin hneg

end

end RHTower
