import GaloisForLFunctions.HTGeometry.QuasiAbelianGaussianLatticeDecay

/-!
# Periodization along a lattice

The damping multiplier of Abe's construction has to be invariant under the lower lattice, and the
only elementary source of such a function is the periodization of a decaying one: summing over the
lattice makes the result invariant by reindexing, and the sum converges because the summand decays
along the lattice directions.

This file isolates the reindexing step, which is where invariance actually comes from and which is
purely formal.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The periodization of a function along a lattice embedding. -/
def latticePeriodizationFun {d k : ℕ} (emb : (Fin k → ℤ) →+ (Fin d → ℂ))
    (f : MultivariateEntire d) (x : Fin d → ℂ) : ℂ :=
  ∑' n : Fin k → ℤ, f.1 (x + emb n)

/-- **The periodization is invariant under the lattice.**  Translating the argument by a lattice
vector translates the summation index, and the sum is unconditional. -/
theorem latticePeriodizationFun_add_emb {d k : ℕ} (emb : (Fin k → ℤ) →+ (Fin d → ℂ))
    (f : MultivariateEntire d) (x : Fin d → ℂ) (p : Fin k → ℤ) :
    latticePeriodizationFun emb f (x + emb p) = latticePeriodizationFun emb f x := by
  rw [latticePeriodizationFun, latticePeriodizationFun]
  have hshift : ∀ n : Fin k → ℤ, f.1 (x + emb p + emb n) = f.1 (x + emb (p + n)) := by
    intro n
    congr 1
    rw [map_add]
    ring
  calc (∑' n : Fin k → ℤ, f.1 (x + emb p + emb n))
      = ∑' n : Fin k → ℤ, f.1 (x + emb (p + n)) := by simp only [hshift]
    _ = ∑' n : Fin k → ℤ, f.1 (x + emb n) :=
        (Equiv.addLeft p).tsum_eq (fun n => f.1 (x + emb n))

/-- The periodization of a nonnegative-decaying summand is invariant in the strong sense needed by
the automorphic-form closure: it agrees at every pair of points differing by a lattice vector. -/
theorem latticePeriodizationFun_invariant {d k : ℕ} (emb : (Fin k → ℤ) →+ (Fin d → ℂ))
    (f : MultivariateEntire d) {ΓH : AddSubgroup (Fin d → ℂ)}
    (hrange : ∀ η ∈ ΓH, ∃ p : Fin k → ℤ, η = emb p) :
    ∀ η ∈ ΓH, ∀ x, latticePeriodizationFun emb f (x + η) = latticePeriodizationFun emb f x := by
  intro η hη x
  obtain ⟨p, hp⟩ := hrange η hη
  rw [hp]
  exact latticePeriodizationFun_add_emb emb f x p

end

end GaloisForLFunctions.HTGeometry
