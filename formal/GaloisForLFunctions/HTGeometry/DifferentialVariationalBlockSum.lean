import GaloisForLFunctions.HTGeometry.DifferentialVariationalUniformShift

/-!
# The unrolled off-diagonal block stays in one dilation

This is the arithmetic heart of the block estimate.  Unrolling the component recursion writes the
`W`-part of the orbit as `σⁿ(w₀) + Σ_{j<n} σ^{n-1-j}(a_j)`, and the whole point is that the sum of
`n` terms is **no worse than a single term**.

Two facts make that work.

* `vecBuildingAction_smul_mem_leftScale_of_slow` — a single term.  If `a_j` sits in the dilation
  `π^{-m}` of a subspace on which the action is slow at rate `1/c` with additive constant `γ`, then
  `σ^p(a_j)` sits in `π^{-(m + ⌊p/c⌋ + γ)}`.  The dilation factor commutes past the action because
  the uniformizer is fixed by every differential coefficient automorphism.
* `variationalBlockSum_mem` — the collection.  With `m = ⌊j/c⌋ + δ` and `p = n-1-j`, superadditivity
  of floor division, `⌊j/c⌋ + ⌊(n-1-j)/c⌋ ≤ ⌊n/c⌋`, makes **every** summand land in the single
  submodule `π^{-(⌊n/c⌋ + δ + γ)} L₀`; a submodule is closed under addition, so the sum lands there
  too.

No cancellation or non-archimedean estimate is needed at this step — the shared target submodule
does the work, which is exactly why the accumulated off-diagonal term costs nothing in rate.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- One term of the unrolled off-diagonal block stays in a single dilation.  The two rate costs —
the dilation carrying the source and the slow bound on the transported subspace — add to the shared
rate because floor division is superadditive in its numerator. -/
theorem vecBuildingAction_smul_mem_leftScale_of_slow (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L₀ : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (T : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (c γ : ℕ)
    (hslow : ∀ p : ℕ, ∀ y ∈ T, (σ ^ p).vecBuildingAction b y ∈
      (DiffOp.leftScaleCompletedPseudoDiffOpLattice
        (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(((p / c : ℕ) + γ : ℕ) : ℤ)))
        L₀).carrier)
    (p m : ℕ) {z : Fin r → DiffOp.CompletedPseudoDiffOp K}
    (hz : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (m : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • z ∈ T) :
    (σ ^ p).vecBuildingAction b z ∈
      (DiffOp.leftScaleCompletedPseudoDiffOpLattice
        (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
          (-((m + (p / c : ℕ) + γ : ℕ) : ℤ))) L₀).carrier := by
  have hstep := hslow p _ hz
  have hsm := DiffOp.smul_mem_leftScale
    (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(m : ℤ))) _ hstep
  rw [DiffOp.leftScaleCompletedPseudoDiffOpLattice_mul, ← zpow_add] at hsm
  have hval : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(m : ℤ)) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) •
      ((σ ^ p).vecBuildingAction b
        (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (m : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • z)) =
      (σ ^ p).vecBuildingAction b z := by
    rw [(σ ^ p).vecBuildingAction_smul b,
      (σ ^ p).mapCompletedPseudoRingEquiv_uniformizer_zpow (m : ℤ), smul_smul,
      ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_smul]
  rw [hval] at hsm
  refine DiffOp.leftScale_uniformizer_zpow_carrier_antitone L₀ ?_ hsm
  have hnat : m + (p / c) + γ = m + ((p / c) + γ) := by omega
  exact le_of_eq (by rw [hnat]; push_cast; ring)

/-- The unrolled off-diagonal block, as a finite sum of transported terms. -/
def variationalBlockSum (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (a : ℕ → Fin r → DiffOp.CompletedPseudoDiffOp K) (n : ℕ) :
    Fin r → DiffOp.CompletedPseudoDiffOp K :=
  ∑ j ∈ Finset.range n, (σ ^ (n - 1 - j)).vecBuildingAction b (a j)

/-- **The block sum stays in one dilation.**  Every summand lies in the same submodule, so the whole
sum does — this is where the block estimate avoids any loss proportional to the number of terms. -/
theorem variationalBlockSum_mem (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L₀ : DiffOp.CompletedPseudoDiffOpLattice K (Fin r))
    (T : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (c γ δ : ℕ)
    (hslow : ∀ p : ℕ, ∀ y ∈ T, (σ ^ p).vecBuildingAction b y ∈
      (DiffOp.leftScaleCompletedPseudoDiffOpLattice
        (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(((p / c : ℕ) + γ : ℕ) : ℤ)))
        L₀).carrier)
    (a : ℕ → Fin r → DiffOp.CompletedPseudoDiffOp K)
    (ha : ∀ j : ℕ, ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
      (((j / c : ℕ) + δ : ℕ) : ℤ) : (DiffOp.CompletedPseudoDiffOp K)ˣ) :
      DiffOp.CompletedPseudoDiffOp K) • a j ∈ T)
    (n : ℕ) :
    variationalBlockSum σ b a n ∈
      (DiffOp.leftScaleCompletedPseudoDiffOpLattice
        (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^
          (-(((n / c : ℕ) + δ + γ : ℕ) : ℤ))) L₀).carrier := by
  classical
  refine Submodule.sum_mem _ fun j hj => ?_
  have hjn : j < n := Finset.mem_range.1 hj
  have hterm := vecBuildingAction_smul_mem_leftScale_of_slow σ b L₀ T c γ hslow
    (n - 1 - j) ((j / c : ℕ) + δ) (ha j)
  refine DiffOp.leftScale_uniformizer_zpow_carrier_antitone L₀ ?_ hterm
  have hdiv : (j / c) + ((n - 1 - j) / c) ≤ n / c := by
    have hsum : j + (n - 1 - j) ≤ n := by omega
    calc (j / c) + ((n - 1 - j) / c) ≤ (j + (n - 1 - j)) / c := Nat.add_div_le_add_div j _ c
      _ ≤ n / c := Nat.div_le_div_right hsum
  have hnat : (j / c) + δ + ((n - 1 - j) / c) + γ ≤ (n / c) + δ + γ := by omega
  exact neg_le_neg (by exact_mod_cast hnat)

end

end GaloisForLFunctions.HTGeometry
