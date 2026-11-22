import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Finset.Max

/-!
# Finite covers of measurement profiles

For finitely many compact readouts with positive tolerances, finitely many
reference integer labels suffice to compare every single-label profile.
No continuity of the readouts as functions of the integer label is needed.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks

open scoped Classical
variable {I F : Type*} {K : F → Type*} [∀ j, PseudoMetricSpace (K j)]

/-- Each comparison measures the same profile on the two selected copies. -/
structure Readout (I F : Type*) (K : F → Type*) where
  left : F → I
  right : F → I
  value : (j : F) → ℕ+ → K j
  radius : F → {r : ℝ // 0 < r}

namespace Readout

variable (R : Readout I F K)

def near (a b : ℕ+) : Prop := ∀ j, dist (R.value j a) (R.value j b) < (R.radius j).val

def Passes (x : I → ℕ+) : Prop :=
  ∀ j, dist (R.value j (x (R.left j))) (R.value j (x (R.right j))) < (R.radius j).val

theorem near_refl (m : ℕ+) : R.near m m := fun j => by simpa only [dist_self] using (R.radius j).property

theorem near_symm {m n : ℕ+} (h : R.near m n) : R.near n m := fun j => by rw [dist_comm]; exact h j

/-- Centers are profiles of actual positive integers. -/
theorem exists_centers [Fintype F] [∀ j, CompactSpace (K j)] :
    ∃ S : Finset ℕ+, ∀ n : ℕ+, ∃ m ∈ S, R.near n m := by
  have hd : ∃ d : ℝ, 0 < d ∧ ∀ j, d ≤ (R.radius j).val := by
    cases isEmpty_or_nonempty F with
    | inl he => exact ⟨1,zero_lt_one,fun j => (he.false j).elim⟩
    | inr hn =>
      obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ (fun j => (R.radius j).val) Finset.univ_nonempty
      exact ⟨_,(R.radius j).property,fun i => hj i (Finset.mem_univ _)⟩
  obtain ⟨d,hd,hle⟩ := hd
  let profile (n : ℕ+) (j : F) := R.value j n
  have ht : TotallyBounded (Set.range profile) := isCompact_univ.totallyBounded.subset (Set.subset_univ _)
  obtain ⟨T,hsub,hfin,hcov⟩ := Metric.finite_approx_of_totallyBounded ht d hd
  letI : Fintype T := hfin.fintype
  let center (y : T) : ℕ+ := (hsub y.property).choose
  have hcenter (y : T) : profile (center y) = y.val := (hsub y.property).choose_spec
  refine ⟨Finset.univ.image center,fun n => ?_⟩
  obtain ⟨y,hy,hdist⟩ := Set.mem_iUnion₂.mp (hcov (Set.mem_range_self n))
  let a : T := ⟨y,hy⟩
  refine ⟨center a,Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩,fun j => ?_⟩
  have hab : dist (profile n) (profile (center a)) < d := by rw [hcenter]; exact hdist
  exact ((dist_le_pi_dist (profile n) (profile (center a)) j).trans_lt hab).trans_le (hle j)

#print axioms exists_centers

end Readout
end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks
