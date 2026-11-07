import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheExtremalFakePrimeMeasure
import GaloisForLFunctions.HTGeometry.ConicCaratheodory

/-!
# The extremal fake prime measure is sparse

An extremal fake prime measure of level `K` for a target `S` lives a priori on one period, `lcm(2, …, K)` residues, about `e^K` of them. Only `K` numbers
matter to the program: the `K − 1` moments and the mass on `S`. By Carathéodory's theorem in the cone of moment vectors, the same moments and the same
mass are attained by a measure with **at most `K` atoms**.

So the fake prime measure closest to the true one, at level `K`, is a sum of at most `K` point masses. Each atom sits where an optimal stencil is tight,
by complementary slackness (`IsFakePrimeMeasure.hasSum_slack`).
-/

open Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The moment vector of the residue `j + 1`: its sawteeth at the letters `2, …, K` and its indicator on the target. -/
def momentVector (K : ℕ) (S : Finset ℕ) (j : ℕ) : (Fin (K - 1) → ℝ) × ℝ :=
  (fun i => ((((j + 1) % ((i : ℕ) + 2)) : ℕ) : ℝ), if j + 1 ∈ S then 1 else 0)

/-- The mass on a target inside one period, as a sum over the period. -/
private lemma targetMass_eq_sum_range {S : Finset ℕ} {L : ℕ} (hS : ∀ r ∈ S, 1 ≤ r ∧ r < L) (w : ℕ → ℝ) :
    targetMass w S = ∑ j ∈ range (L - 1), w j * (if j + 1 ∈ S then 1 else 0) := by
  classical
  have hinj : Set.InjOn (fun r : ℕ => r - 1) (S : Set ℕ) := by
    intro a ha b hb hab
    have h1 := (hS a ha).1
    have h2 := (hS b hb).1
    simp only at hab
    omega
  have hsub : S.image (fun r => r - 1) ⊆ range (L - 1) := by
    intro j hj
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hj
    have := hS r hr
    exact mem_range.mpr (by omega)
  rw [← sum_subset hsub (fun j _ hj => by
    have hj' : j + 1 ∉ S := fun h => hj (mem_image.mpr ⟨j + 1, h, by simp⟩)
    simp [hj'])]
  rw [targetMass, ← sum_image (f := w) hinj]
  refine sum_congr rfl fun j hj => ?_
  obtain ⟨r, hr, rfl⟩ := mem_image.mp hj
  have e : r - 1 + 1 = r := by have := (hS r hr).1; omega
  simp [e, hr]

/-- **The extremal fake prime measure has at most `K` atoms.** For an alphabet `[2, K]` and a finite target inside one period there is an extremal fake prime
measure supported on at most `K` residues of one period. -/
theorem exists_sparse_extremal_of_target {K : ℕ} {S : Finset ℕ} (hK : 2 ≤ K)
    (hS : ∀ r ∈ S, 1 ≤ r ∧ r < lcmUpTo K) :
    ∃ u : ℕ → ℝ, IsFakePrimeMeasure K u ∧ (∀ j, lcmUpTo K ≤ j + 1 → u j = 0) ∧
      (∀ v : ℕ → ℝ, IsFakePrimeMeasure K v → targetMass v S ≤ targetMass u S) ∧
      ((range (lcmUpTo K - 1)).filter fun j => u j ≠ 0).card ≤ K := by
  classical
  obtain ⟨u, hu, hoff, hmax, -, -⟩ := exists_extremal_of_target hK hS
  obtain ⟨L, hL⟩ : ∃ L, L = lcmUpTo K := ⟨_, rfl⟩
  rw [← hL] at hoff hS ⊢
  obtain ⟨F, hF⟩ : ∃ F, F = (range (L - 1)).filter fun j => 0 < u j := ⟨_, rfl⟩
  obtain ⟨G, c, hGF, hcpos, -, hcard, hsum⟩ := HTGeometry.exists_pos_combination_card_le_finrank
    (momentVector K S) F u (fun j hj => by rw [hF] at hj; exact (mem_filter.mp hj).2)
  have hfin : Module.finrank ℝ ((Fin (K - 1) → ℝ) × ℝ) = K := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]
    omega
  rw [hfin] at hcard
  have hGr : G ⊆ range (L - 1) := fun j hj => (mem_filter.mp (hF ▸ hGF hj)).1
  -- The two sides agree coordinatewise.
  have hfst : ∀ i : Fin (K - 1), ∑ j ∈ F, u j * ((((j + 1) % ((i : ℕ) + 2)) : ℕ) : ℝ) =
      ∑ j ∈ G, c j * ((((j + 1) % ((i : ℕ) + 2)) : ℕ) : ℝ) := by
    intro i
    have h := congrArg (fun z : (Fin (K - 1) → ℝ) × ℝ => z.1 i) hsum
    simpa [Prod.fst_sum, Finset.sum_apply, momentVector, smul_eq_mul] using h
  have hsnd : ∑ j ∈ F, u j * (if j + 1 ∈ S then 1 else 0) = ∑ j ∈ G, c j * (if j + 1 ∈ S then 1 else 0) := by
    have h := congrArg (fun z : (Fin (K - 1) → ℝ) × ℝ => z.2) hsum
    simpa [Prod.snd_sum, momentVector, smul_eq_mul] using h
  -- Sums of `u` over the period are sums over `F`.
  have hrangeF : ∀ g : ℕ → ℝ, ∑ j ∈ range (L - 1), u j * g j = ∑ j ∈ F, u j * g j := by
    intro g
    rw [hF, sum_filter]
    refine sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rfl
    · have : u j = 0 := le_antisymm (not_lt.mp h) (hu.nonneg j)
      rw [this, zero_mul]
  -- The sparse measure.
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ℝ, v = fun j => if j ∈ G then c j else 0 := ⟨_, rfl⟩
  have hrangeG : ∀ g : ℕ → ℝ, ∑ j ∈ range (L - 1), v j * g j = ∑ j ∈ G, c j * g j := by
    intro g
    have h1 : ∑ j ∈ range (L - 1), v j * g j = ∑ j ∈ range (L - 1), if j ∈ G then c j * g j else 0 := by
      refine sum_congr rfl fun j _ => ?_
      rw [hv]
      simp only
      split_ifs <;> simp
    rw [h1, sum_ite_mem, inter_eq_right.mpr hGr]
  have hv0 : ∀ j, 0 ≤ v j := by
    intro j
    rw [hv]
    simp only
    split_ifs with h
    · exact (hcpos j h).le
    · exact le_rfl
  have hvoff : ∀ j, L ≤ j + 1 → v j = 0 := by
    intro j hj
    rw [hv]
    simp only
    rw [if_neg]
    intro hjG
    have := mem_range.mp (hGr hjG)
    omega
  have hvfin : ∀ g : ℕ → ℝ, HasSum (fun j => v j * g j) (∑ j ∈ range (L - 1), v j * g j) := by
    intro g
    refine hasSum_sum_of_ne_finset_zero fun j hj => ?_
    rw [hvoff j (by have := mem_range.not.mp hj; omega), zero_mul]
  have hufin : ∀ g : ℕ → ℝ, HasSum (fun j => u j * g j) (∑ j ∈ range (L - 1), u j * g j) := by
    intro g
    refine hasSum_sum_of_ne_finset_zero fun j hj => ?_
    rw [hoff j (by have := mem_range.not.mp hj; omega), zero_mul]
  have hfake : IsFakePrimeMeasure K v := by
    refine ⟨hv0, fun k hk => ?_⟩
    obtain ⟨hk1, hkK⟩ := mem_Icc.mp hk
    rcases eq_or_lt_of_le hk1 with h1 | h2
    · subst h1
      simp [Nat.mod_one]
    · have hi : k - 2 < K - 1 := by omega
      have hkk : k - 2 + 2 = k := by omega
      have h := hfst ⟨k - 2, hi⟩
      simp only [hkk] at h
      have hval : ∑ j ∈ range (L - 1), v j * (((j + 1) % k : ℕ) : ℝ) = Real.log k := by
        rw [hrangeG, ← h, ← hrangeF]
        exact (hufin _).unique (hu.moment k hk)
      rw [← hval]
      exact hvfin _
  refine ⟨v, hfake, hvoff, fun w hw => ?_, ?_⟩
  · have hmass : targetMass v S = targetMass u S := by
      rw [targetMass_eq_sum_range hS, targetMass_eq_sum_range hS, hrangeG, hrangeF, hsnd]
    rw [hmass]
    exact hmax w hw
  · refine (card_le_card fun j hj => ?_).trans hcard
    obtain ⟨-, hj2⟩ := mem_filter.mp hj
    by_contra hjG
    rw [hv] at hj2
    simp only [if_neg hjG] at hj2
    exact hj2 rfl

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
