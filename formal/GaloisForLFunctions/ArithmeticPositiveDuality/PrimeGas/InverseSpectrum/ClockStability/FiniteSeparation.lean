import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.OccupationGaps

/-! # Separation by finite blocks of continuous observations

If every pair above an error threshold is eventually separated, compactness
gives a common finite window with a whole run of separated observations.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

private def separatedBlocks {X : Type*} (d : ℕ → X → ℝ) (start k N : ℕ) : Set X :=
  ⋃ m : Fin (N+1), ⋂ j : Fin (k+1), {x | occupationWeight N < d (start+m.val+j.val) x}

private theorem mem_separatedBlocks {X : Type*} {d : ℕ → X → ℝ} {start k N : ℕ} {x : X} :
    x ∈ separatedBlocks d start k N ↔
      ∃ m : Fin (N+1), ∀ j : Fin (k+1), occupationWeight N < d (start+m.val+j.val) x := by
  simp only [separatedBlocks,mem_iUnion,mem_iInter,mem_setOf_eq]

/-- Uniform separation by a block after any prescribed starting index. -/
theorem compact_block_separation {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (E : X → ℝ) (hE : Continuous E) (d : ℕ → X → ℝ) (hd : ∀ n, Continuous (d n))
    (hsep : ∀ x, 0 < E x → ∀ᶠ n in atTop, 0 < d n x) {ε : ℝ} (hε : 0 < ε) (start k : ℕ) :
    ∃ N, ∀ x, ε ≤ E x → ∃ m ≤ N, ∀ j ≤ k, occupationWeight N < d (start+m+j) x := by
  let U := separatedBlocks d start k
  have hopen (N : ℕ) : IsOpen (U N) :=
    isOpen_iUnion fun m => isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (hd _)
  have hmono : Monotone U := by
    intro i N hi x hx
    obtain ⟨m,hm⟩ := mem_separatedBlocks.mp hx
    apply mem_separatedBlocks.mpr
    exact ⟨⟨m.val,m.isLt.trans_le (Nat.succ_le_succ hi)⟩,
      fun j => (occupationWeight_antitone hi).trans_lt (hm j)⟩
  have hcover : {x | ε ≤ E x} ⊆ ⋃ N, U N := by
    intro x hx
    obtain ⟨m,hm⟩ := eventually_atTop.mp (hsep x (hε.trans_le hx))
    have hj (j : Fin (k+1)) : ∀ᶠ N in atTop, occupationWeight N < d (start+m+j.val) x :=
      occupationWeight_tendsto.eventually_lt_const (hm _ (by omega))
    obtain ⟨N,hN,hjN⟩ := ((eventually_ge_atTop m).and (eventually_all.mpr hj)).exists
    exact mem_iUnion.mpr ⟨N,mem_separatedBlocks.mpr ⟨⟨m,Nat.lt_succ_of_le hN⟩,hjN⟩⟩
  have hK : IsCompact {x | ε ≤ E x} := (isClosed_le continuous_const hE).isCompact
  obtain ⟨N,hN⟩ := hK.elim_directed_cover U hopen hcover hmono.directed_le
  refine ⟨N,fun x hx => ?_⟩
  obtain ⟨m,hm⟩ := mem_separatedBlocks.mp (hN hx)
  exact ⟨m.val,Nat.le_of_lt_succ m.isLt,fun j hj => hm ⟨j,Nat.lt_succ_of_le hj⟩⟩

#print axioms compact_block_separation

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
