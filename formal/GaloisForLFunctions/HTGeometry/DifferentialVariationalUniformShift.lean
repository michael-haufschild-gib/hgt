import GaloisForLFunctions.HTGeometry.DifferentialVariationalAdaptedLattice

/-!
# Eventual confinement upgrades to uniform confinement

The block estimate unrolls the off-diagonal term as `wₙ = Σ_j σ^{n-1-j}(B(u_j))` and needs the rate
bound at *every* exponent `n-1-j`, not merely at large ones.  The slow sets only give the bound
eventually.

`exists_uniform_shift_of_eventually_carrier_le` closes that gap: the finitely many early indices each
admit some uniformizer confinement (every lattice sits inside some dilation of every other), and
their supremum is a single additive constant `γ` that makes the bound

```text
(σⁿ · P).carrier ≤ (π^{-(⌊n/c⌋ + γ)} L).carrier
```

hold for **all** `n`.  Since a constant is invisible to the rate, nothing is lost: the conclusion of
the block estimate is a statement about `⌊n/c⌋` for arbitrary `c`, and `γ` only shifts it.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- **Eventual confinement upgrades to a uniform confinement with an additive constant.**  The
finitely many early indices are absorbed into one constant, so a rate bound valid eventually becomes
one valid at every index. -/
theorem exists_uniform_shift_of_eventually_carrier_le (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L P : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (c : ℕ)
    (h : ∀ᶠ n : ℕ in Filter.atTop,
      ((σ ^ n).latticeBuildingAction b P).carrier ≤
        (DiffOp.leftScaleCompletedPseudoDiffOpLattice
          (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-((n / c : ℕ) : ℤ)))
          L).carrier) :
    ∃ γ : ℕ, ∀ n : ℕ,
      ((σ ^ n).latticeBuildingAction b P).carrier ≤
        (DiffOp.leftScaleCompletedPseudoDiffOpLattice
          (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
            (-(((n / c : ℕ) + γ : ℕ) : ℤ))) L).carrier := by
  classical
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 h
  have hearly : ∀ n : ℕ, ∃ k : ℕ,
      ((σ ^ n).latticeBuildingAction b P).carrier ≤
        (DiffOp.leftScaleCompletedPseudoDiffOpLattice
          (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(k : ℤ))) L).carrier :=
    fun n => DiffOp.exists_nat_carrier_le_leftScale_uniformizer L
      ((σ ^ n).latticeBuildingAction b P)
  choose kf hkf using hearly
  refine ⟨(Finset.range M).sup kf, fun n => ?_⟩
  rcases le_or_gt M n with hn | hn
  · refine le_trans (hM n hn) ?_
    refine DiffOp.leftScale_uniformizer_zpow_carrier_antitone L ?_
    exact neg_le_neg (by exact_mod_cast Nat.le_add_right (n / c) ((Finset.range M).sup kf))
  · refine le_trans (hkf n) ?_
    refine DiffOp.leftScale_uniformizer_zpow_carrier_antitone L ?_
    have hle : kf n ≤ (Finset.range M).sup kf :=
      Finset.le_sup (Finset.mem_range.2 hn)
    have hnat : kf n ≤ n / c + (Finset.range M).sup kf :=
      le_trans hle (Nat.le_add_left _ _)
    exact neg_le_neg (by exact_mod_cast hnat)

end

end GaloisForLFunctions.HTGeometry
