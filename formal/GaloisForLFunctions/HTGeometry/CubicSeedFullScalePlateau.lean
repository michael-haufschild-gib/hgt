/-
# The full-scale cubic-phase plateau law

The three clauses of the cubic-phase capstone at one fixed seed: the seed is prepared by one gate
per multilinear monomial of degree at most three, so its exact circuit size is the monomial count;
the long-time shell density of the easy directions is at most `2^{-r/2} + 96/(κ²D)`; and almost
every Hamiltonian of the nearest-neighbour shell returns the evolved seed arbitrarily close to the
seed after every time.

Main results:
* `card_monLe` — **`(3)`**: the number of gates is the number of monomials of degree at most `m`.
* `ae_exists_late_cubicSeed_recurrence` — the later recurrence of a cubic seed.
* `exists_fixed_cubicSeed_plateau_and_recurrence` — the two dynamical clauses at one seed.
-/
import GaloisForLFunctions.HTGeometry.CubicFixedSeedSelection
import GaloisForLFunctions.HTGeometry.ChainShellMaximalProjectivity

open Finset MeasureTheory Matrix Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- **`(3)`.**  The multilinear monomials of degree at most `m` are counted by the partial sum of
binomial coefficients; at `m = 3` this is `1 + n + C(n,2) + C(n,3)`, a cubic in `n`. -/
theorem card_monLe (ι : Type*) [Fintype ι] [DecidableEq ι] (m : ℕ) :
    Fintype.card (MonLe ι m) = ∑ j ∈ Finset.range (m + 1), (Fintype.card ι).choose j := by
  classical
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter fun S : Finset ι => S.card ≤ m)
      = (Finset.range (m + 1)).biUnion
        (fun j => Finset.powersetCard j (Finset.univ : Finset ι)) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ, Nat.lt_succ_iff]
    constructor
    · intro h
      exact ⟨S.card, h, rfl⟩
    · rintro ⟨j, hj, hcard⟩
      omega
  rw [hset]
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_powersetCard, Finset.card_univ]
  · intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun S hi hj => hij ?_
    rw [Finset.mem_powersetCard] at hi hj
    rw [← hi.2, hj.2]

/-- **The later recurrence of a cubic seed.**  For almost every Hamiltonian of the shell the evolved
cubic seed returns arbitrarily close to the seed after every time. -/
theorem ae_exists_late_cubicSeed_recurrence (k : ℕ) (c : MonLe (Fin (k + 3)) 3 → ZMod 8)
    {ρ : ℝ} (hρ : 0 < ρ) (A : ℝ) :
    ∀ᵐ θ ∂(shellProbability (Fin (Fintype.card (ChainLabel (k + 3))))),
      ∃ s : ℝ, A < s ∧ 1 - ρ ≤ ‖finiteComplexInner
        (unitaryEvolution (spectralEnsembleMatrix (chainPauliFin (k + 3)) θ) s *ᵥ
          cubicSeed (k + 3) c) (cubicSeed (k + 3) c)‖ :=
  ae_exists_late_seed_recurrence_chainShell k (cubicSeed (k + 3) c)
    (finiteComplexInner_cubicSeed (k + 3) c) ⟨0, Nat.two_pow_pos (k + 3)⟩ hρ A

/-- **The two dynamical clauses at one fixed cubic seed.**  One seed can be fixed in advance whose
evolution under the nearest-neighbour shell is hard for the dictionary at every sufficiently late
time with shell density at most `2^{-r/2} + 96/(κ²D)`, and which almost surely returns arbitrarily
close to itself after every time. -/
theorem exists_fixed_cubicSeed_plateau_and_recurrence (k : ℕ) :
    ∃ c₀ : MonLe (Fin (k + 3)) 3 → ZMod 8,
      (∀ {C : Type} [Fintype C] [Nonempty C]
        (Z : C → (Fin (2 ^ (k + 3)) → ℂ)), (∀ κ, finiteComplexInner (Z κ) (Z κ) = 1) →
        ∀ {a : ℝ}, 0 < a → ∀ {r : ℕ}, 1 ≤ r → ∀ {kap : ℝ}, 0 < kap →
        16 * ((2 + kap) / (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)) / a ^ 2
            ≤ 1 / (2 * r) →
        ∀ {M : ℝ}, 1 < M → ∀ {s : ℕ}, (Fintype.card C : ℝ) ≤ M ^ (s + 1) →
        ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2 →
        (atTop.limsup fun t : ℝ => (sphereLaw (Fintype.card (ChainLabel (k + 3))))
            {x | ∃ κ : C, a ≤ finitePureStateFidelity
              (unitaryEvolution (spectralEnsembleMatrix (chainPauliFin (k + 3)) (sphereCoeff x))
                (2 * Real.pi * t) *ᵥ cubicSeed (k + 3) c₀) (Z κ)})
          ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2)))
            + ENNReal.ofReal (96 /
                (kap ^ 2 * (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ))))
      ∧ (∀ {ρ : ℝ}, 0 < ρ → ∀ A : ℝ,
        ∀ᵐ θ ∂(shellProbability (Fin (Fintype.card (ChainLabel (k + 3))))),
          ∃ s : ℝ, A < s ∧ 1 - ρ ≤ ‖finiteComplexInner
            (unitaryEvolution (spectralEnsembleMatrix (chainPauliFin (k + 3)) θ) s *ᵥ
              cubicSeed (k + 3) c₀) (cubicSeed (k + 3) c₀)‖) := by
  obtain ⟨c₀, hplateau⟩ := exists_fixed_cubicSeed_limsup_le k
  exact ⟨c₀, hplateau, fun hρ A => ae_exists_late_cubicSeed_recurrence k c₀ hρ A⟩

end GaloisForLFunctions.HTGeometry

end
