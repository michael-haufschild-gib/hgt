import GaloisForLFunctions.HTGeometry.CompletionKernelPairTransversalityLaw

/-!
# Pairwise first-coalescence conservation

A deterministic serial transport can preserve distinctions or erase them; it cannot recreate a
distinction after erasing it.  Consequently every terminal identification of two distinct source
states has a unique first coalescing edge.  This pairwise law strictly precedes the pointed
zero-fibre law: the latter is its specialization to the pair `(x, 0)` under zero-preserving maps.

If a terminal observation recovers a target distinction, that pair must remain distinct at every
earlier stage.  In particular, recovery of a nonzero reflection-odd charge requires its reflected
source pair to be separated before transport and through every edge.  Orientation can be preserved
or lost downstream, never created there.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Composite of first `n` stages of a homogeneous deterministic transport chain. -/
def iteratedObservationTransport
    {X : ℕ → Type*} (T : (n : ℕ) → X n → X (n + 1)) : (n : ℕ) → X 0 → X n
  | 0 => id
  | n + 1 => T n ∘ iteratedObservationTransport T n

/-- Two source states first coalesce across edge `k` of a deterministic transport chain. -/
def PairFirstCoalescesAt
    {X : ℕ → Type*} (T : (n : ℕ) → X n → X (n + 1)) (x y : X 0) (k : ℕ) : Prop :=
  ¬ MapKernelPair (iteratedObservationTransport T k) x y ∧
    MapKernelPair (iteratedObservationTransport T (k + 1)) x y

/-- Once deterministic transport identifies two states, every later stage identifies them. -/
theorem iteratedTransport_mapKernelPair_of_le
    {X : ℕ → Type*} (T : (n : ℕ) → X n → X (n + 1)) {x y : X 0} {m n : ℕ}
    (hmn : m ≤ n)
    (hm : MapKernelPair (iteratedObservationTransport T m) x y) :
    MapKernelPair (iteratedObservationTransport T n) x y := by
  induction n, hmn using Nat.le_induction with
  | base => exact hm
  | succ n _ ih =>
      change T n (iteratedObservationTransport T n x) =
        T n (iteratedObservationTransport T n y)
      rw [ih]

/-- Every terminal identification of a distinct source pair has a first coalescing edge. -/
theorem exists_pairFirstCoalescesAt_of_terminal_of_source_ne
    {X : ℕ → Type*} (T : (n : ℕ) → X n → X (n + 1)) (x y : X 0) (n : ℕ)
    (hxy : x ≠ y)
    (hterminal : MapKernelPair (iteratedObservationTransport T n) x y) :
    ∃ k, k < n ∧ PairFirstCoalescesAt T x y k := by
  induction n with
  | zero =>
      exact (hxy hterminal).elim
  | succ n ih =>
      by_cases hmid : MapKernelPair (iteratedObservationTransport T n) x y
      · obtain ⟨k, hk, hfirst⟩ := ih hmid
        exact ⟨k, hk.trans_le (Nat.le_succ n), hfirst⟩
      · exact ⟨n, Nat.lt_succ_self n, hmid, hterminal⟩

/-- A deterministic chain has at most one first coalescing edge for a fixed pair. -/
theorem pairFirstCoalescesAt_unique
    {X : ℕ → Type*} (T : (n : ℕ) → X n → X (n + 1)) (x y : X 0) {k l : ℕ}
    (hk : PairFirstCoalescesAt T x y k)
    (hl : PairFirstCoalescesAt T x y l) :
    k = l := by
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · exfalso
    exact hl.1 (iteratedTransport_mapKernelPair_of_le T
      (Nat.succ_le_of_lt hkl) hk.2)
  · exact hkl
  · exfalso
    exact hk.1 (iteratedTransport_mapKernelPair_of_le T
      (Nat.succ_le_of_lt hlk) hl.2)

/-- **Pairwise first-coalescence law.** A terminal identification is either already present at
the source or is created at one unique first transport edge. No algebra, topology, boundedness,
or zero-preservation is required. -/
theorem terminalMapKernelPair_iff_sourcePair_or_existsUnique_firstCoalescesAt
    {X : ℕ → Type*} (T : (n : ℕ) → X n → X (n + 1)) (x y : X 0) (n : ℕ) :
    MapKernelPair (iteratedObservationTransport T n) x y ↔
      x = y ∨ ∃! k, k < n ∧ PairFirstCoalescesAt T x y k := by
  constructor
  · intro hterminal
    by_cases hxy : x = y
    · exact Or.inl hxy
    · right
      obtain ⟨k, hklt, hfirst⟩ :=
        exists_pairFirstCoalescesAt_of_terminal_of_source_ne T x y n hxy hterminal
      refine ⟨k, ⟨hklt, hfirst⟩, ?_⟩
      intro l hl
      exact (pairFirstCoalescesAt_unique T x y hfirst hl.2).symm
  · rintro (rfl | ⟨k, hk, _⟩)
    · rfl
    · exact iteratedTransport_mapKernelPair_of_le T
        (Nat.succ_le_iff.mpr hk.1) hk.2.2

/-- If a terminal observation recovers a target distinction, that pair remains distinct at every
earlier transport stage. Deterministic postprocessing can preserve or erase information, never
create it. -/
theorem pair_distinction_survives_of_terminal_recovers
    {X : ℕ → Type*} {C : Type*} (T : (n : ℕ) → X n → X (n + 1))
    (chi : X 0 → C) (n : ℕ)
    (hrecover : FactorsThroughRange (iteratedObservationTransport T n) chi)
    {x y : X 0} (hchi : chi x ≠ chi y) :
    ∀ k, k ≤ n → ¬ MapKernelPair (iteratedObservationTransport T k) x y := by
  have hrefine : KernelRefines (iteratedObservationTransport T n) chi :=
    (factorsThroughRange_iff_kernelRefines _ _).1 hrecover
  intro k hkn hk
  exact hchi (hrefine x y
    (iteratedTransport_mapKernelPair_of_le T hkn hk))

/-- **Transverse-orientation conservation.** If the terminal record recovers a nonzero
reflection-odd charge, the reflected source pair is distinct at the source and after every edge.
Orientation must therefore be present before transport and survive the entire chain. -/
theorem reflectedPair_distinction_survives_of_terminal_recovers_oddTarget
    {X : ℕ → Type*} (T : (n : ℕ) → X n → X (n + 1))
    (sigma : X 0 → X 0) (chi : X 0 → ℝ) (n : ℕ)
    (hodd : OddUnder (X 0) sigma chi)
    (hrecover : FactorsThroughRange (iteratedObservationTransport T n) chi)
    {x : X 0} (hchi : chi x ≠ 0) :
    ∀ k, k ≤ n →
      ¬ MapKernelPair (iteratedObservationTransport T k) (sigma x) x := by
  apply pair_distinction_survives_of_terminal_recovers T chi n hrecover
  intro heq
  apply hchi
  have hreflection := hodd x
  rw [heq] at hreflection
  linarith

/-- One coalesced reflected pair with nonzero odd charge forbids every terminal recovery, no matter
how many deterministic postprocessing stages follow. -/
theorem not_terminal_recovers_oddTarget_of_reflectedPair_coalescence
    {X : ℕ → Type*} (T : (n : ℕ) → X n → X (n + 1))
    (sigma : X 0 → X 0) (chi : X 0 → ℝ) (n : ℕ)
    (hodd : OddUnder (X 0) sigma chi) {x : X 0} (hchi : chi x ≠ 0)
    {k : ℕ} (hkn : k ≤ n)
    (hk : MapKernelPair (iteratedObservationTransport T k) (sigma x) x) :
    ¬ FactorsThroughRange (iteratedObservationTransport T n) chi := by
  intro hrecover
  exact reflectedPair_distinction_survives_of_terminal_recovers_oddTarget
    T sigma chi n hodd hrecover hchi k hkn hk

end

end GaloisForLFunctions.HTGeometry
