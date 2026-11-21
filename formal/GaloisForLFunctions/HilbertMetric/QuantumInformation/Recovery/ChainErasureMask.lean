import GaloisForLFunctions.HilbertMetric.QuantumInformation.Recovery.ReadyBranch

/-!
# Recovery from an arbitrary set of chain sites

A run survives in the ready slice exactly when all its occupied sites are
accessible. For the sequential chain of Kanno and Soda (arXiv:2611.26368,
Eq. 7.26), a disconnected mask therefore has the same recovery optimum
as its longest accessible initial segment.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric.QuantumInformation.ReadyBranch

open GaloisForLFunctions.HTGeometry

noncomputable section

private theorem cnormSq_single {X : Type*} [Fintype X] [DecidableEq X]
    (x : X) (z : ℂ) : cnormSq (fun y => if y = x then z else 0) = ‖z‖ ^ 2 := by
  unfold cnormSq
  rw [Finset.sum_eq_single x]
  · simp only [if_true]
  · intro y _ hy
    simp only [if_neg hy, norm_zero, zero_pow (Nat.succ_ne_zero 1)]
  · exact fun h => (h (Finset.mem_univ _)).elim

/-- Zero extension along an injection preserves the mass selected by an
arbitrary coordinate predicate. -/
theorem sum_sq_extend_filter {J X : Type*} [Fintype J] [Fintype X]
    (f : J ↪ X) (A : J → ℂ) (P : X → Prop) [DecidablePred P] :
    (∑ x, if P x then ‖Function.extend f A 0 x‖ ^ 2 else 0) =
      ∑ j, if P (f j) then ‖A j‖ ^ 2 else 0 := by
  classical
  let w (x : X) := if P x then ‖Function.extend f A 0 x‖ ^ 2 else (0 : ℝ)
  have hsum : (∑ x ∈ Finset.univ.image f, w x) = ∑ x, w x := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    have hnone : ¬∃ j, f j = x := by
      rintro ⟨j, rfl⟩
      exact hx (Finset.mem_image_of_mem f (Finset.mem_univ j))
    have hz : Function.extend f A (0 : X → ℂ) x = 0 :=
      Function.extend_apply' A (0 : X → ℂ) x hnone
    simp only [w, hz, norm_zero, zero_pow (Nat.succ_ne_zero 1), ite_self]
  change (∑ x, w x) = _
  rw [← hsum, Finset.sum_image (fun _ _ _ _ h => f.injective h)]
  simp only [w, f.injective.extend_apply]

private theorem sum_cnormSq_split {L F J : Type*} [Fintype L] [Fintype F] [Fintype J]
    (f : J ↪ L × F) (A : J → ℂ) :
    (∑ l, cnormSq fun x => Function.extend f A 0 (l, x)) = cnormSq A := by
  calc
    _ = ∑ p : L × F, ‖Function.extend f A 0 p‖ ^ 2 :=
      (Fintype.sum_prod_type (fun p : L × F => ‖Function.extend f A 0 p‖ ^ 2)).symm
    _ = _ := by simpa only [if_true, cnormSq] using sum_sq_extend_filter f A (fun _ => True)

private theorem cnormSq_extend_slice {L F J : Type*} [Fintype L] [Fintype F] [Fintype J]
    [DecidableEq L] (f : J ↪ L × F) (A : J → ℂ) (l : L) :
    cnormSq (fun x => Function.extend f A 0 (l, x)) =
      ∑ j, if (f j).1 = l then ‖A j‖ ^ 2 else 0 := by
  calc
    _ = ∑ z : L, ∑ x : F, if z = l then ‖Function.extend f A 0 (z, x)‖ ^ 2 else 0 := by
      symm
      rw [Finset.sum_eq_single l]
      · simp only [if_true, cnormSq]
      · intro z _ hz
        simp only [if_neg hz, Finset.sum_const_zero]
      · exact fun h => (h (Finset.mem_univ _)).elim
    _ = ∑ p : L × F, if p.1 = l then ‖Function.extend f A 0 p‖ ^ 2 else 0 :=
      (Fintype.sum_prod_type (fun p : L × F =>
        if p.1 = l then ‖Function.extend f A 0 p‖ ^ 2 else (0 : ℝ))).symm
    _ = _ := sum_sq_extend_filter f A (fun p => p.1 = l)

variable {n : ℕ}

/-- A normalized signal indexed by the length of its initial run of ones. -/
abbrev RunAmplitudes (n : ℕ) := {A : Fin (n + 1) → ℂ // cnormSq A = 1}

abbrev RunAvailable (S : Finset (Fin n)) := {i : Fin n // i ∈ S} → Bool

abbrev RunLost (S : Finset (Fin n)) := {i : Fin n // i ∉ S} → Bool

private def runWord (j : Fin (n + 1)) (i : Fin n) : Bool := decide (i.val < j.val)

private theorem runWord_injective : Function.Injective (runWord (n := n)) := by
  intro j k he
  apply Fin.ext
  by_contra h
  have no_lt {u v : Fin (n + 1)} (huv : u.val < v.val) (hword : runWord u = runWord v) :
      False := by
    let i : Fin n := ⟨u.val, huv.trans_le (Nat.le_of_lt_succ v.isLt)⟩
    have hat := congrFun hword i
    simp only [runWord, show i.val = u.val from rfl, Nat.lt_irrefl, decide_false,
      decide_eq_true huv] at hat
    exact Bool.false_ne_true hat
  exact (lt_or_gt_of_ne h).elim (fun hj => no_lt hj he) (fun hk => no_lt hk he.symm)

/-- Splitting a run into the lost and available bit strings retains its index. -/
def runSignature (S : Finset (Fin n)) : Fin (n + 1) ↪ RunLost S × RunAvailable S where
  toFun j := (fun i => runWord j i.val, fun i => runWord j i.val)
  inj' j k h := runWord_injective (funext fun i => by
    by_cases hi : i ∈ S
    · exact congrFun (congrArg Prod.snd h) ⟨i, hi⟩
    · exact congrFun (congrArg Prod.fst h) ⟨i, hi⟩)

private theorem exists_missingOrEnd (S : Finset (Fin n)) :
    ∃ k : ℕ, k = n ∨ ∃ i : Fin n, i.val = k ∧ i ∉ S :=
  ⟨n, Or.inl rfl⟩

/-- The first missing site's index, or n if all sites are available. -/
def accessiblePrefixLength (S : Finset (Fin n)) : ℕ :=
  Nat.find (exists_missingOrEnd S)

theorem accessiblePrefixLength_le (S : Finset (Fin n)) : accessiblePrefixLength S ≤ n :=
  Nat.find_min' (exists_missingOrEnd S) (Or.inl rfl)

theorem accessiblePrefixLength_le_of_missing {S : Finset (Fin n)} {i : Fin n} (hi : i ∉ S) :
    accessiblePrefixLength S ≤ i.val :=
  Nat.find_min' (exists_missingOrEnd S) (Or.inr ⟨i, rfl, hi⟩)

/-- The lost word is all zero exactly for runs contained in the accessible prefix. -/
theorem runSignature_lost_ready_iff (S : Finset (Fin n)) (j : Fin (n + 1)) :
    (runSignature S j).1 = (fun _ => false) ↔ j.val ≤ accessiblePrefixLength S := by
  constructor
  · intro h
    rcases Nat.find_spec (exists_missingOrEnd S) with hend | ⟨i, he, hi⟩
    · exact (Nat.le_of_lt_succ j.isLt).trans_eq hend.symm
    · have ht := congrFun h ⟨i, hi⟩
      change decide (i.val < j.val) = false at ht
      exact (le_of_not_gt (of_decide_eq_false ht)).trans_eq he
  · intro h
    funext i
    change decide (i.val.val < j.val) = false
    exact decide_eq_false (not_lt_of_ge (h.trans (accessiblePrefixLength_le_of_missing i.2)))

/-- The actual available and erased bit strings of the branch-preserving encoding. -/
def maskedRunEncoding (S : Finset (Fin n)) (A : RunAmplitudes n) :
    Encoding (RunAvailable S) (RunLost S) := by
  classical
  exact
    { ready := fun _ => false
      reference := fun x => if x = (fun _ => false) then 1 else 0
      signal := fun l x => Function.extend (runSignature S) A.1 0 (l, x)
      reference_norm := by rw [cnormSq_single, norm_one, one_pow]
      signal_norm := (sum_cnormSq_split (runSignature S) A.1).trans A.2 }

/-- Squared amplitude of the runs contained in the accessible prefix. -/
def maskedRunMass (S : Finset (Fin n)) (A : RunAmplitudes n) : ℝ :=
  ∑ j, if j.val ≤ accessiblePrefixLength S then ‖A.1 j‖ ^ 2 else 0

theorem maskedRun_ready_mass (S : Finset (Fin n)) (A : RunAmplitudes n) :
    cnormSq ((maskedRunEncoding S A).signal (maskedRunEncoding S A).ready) =
      maskedRunMass S A := by
  classical
  change cnormSq (fun x => Function.extend (runSignature S) A.1 0 ((fun _ => false), x)) = _
  rw [cnormSq_extend_slice]
  unfold maskedRunMass
  apply Finset.sum_congr rfl
  intro j _
  exact if_congr (runSignature_lost_ready_iff S j) rfl rfl

/-- No finite recovery using the mask can exceed the prefix optimum. -/
theorem maskedRun_fidelity_le (S : Finset (Fin n)) (A : RunAmplitudes n)
    {K : Type*} [Fintype K] (R : Recovery (RunAvailable S) K) :
    fidelity (maskedRunEncoding S A) R ≤ (1 + Real.sqrt (maskedRunMass S A)) / 2 := by
  have h := fidelity_le (maskedRunEncoding S A) R
  rwa [maskedRun_ready_mass] at h

/-- The prefix optimum is attained by a recovery on the available register. -/
theorem exists_optimal_maskedRun_recovery (S : Finset (Fin n)) (A : RunAmplitudes n) :
    ∃ R : Recovery (RunAvailable S) (Option (RunAvailable S)),
      fidelity (maskedRunEncoding S A) R = (1 + Real.sqrt (maskedRunMass S A)) / 2 := by
  obtain ⟨R, h⟩ := exists_optimal_recovery (maskedRunEncoding S A)
  exact ⟨R, by rwa [maskedRun_ready_mass] at h⟩

private def singleRun (j : Fin (n + 1)) : RunAmplitudes n :=
  ⟨fun k => if k = j then 1 else 0, by rw [cnormSq_single, norm_one, one_pow]⟩

private theorem maskedRunMass_single (S : Finset (Fin n)) (j : Fin (n + 1)) :
    maskedRunMass S (singleRun j) = if j.val ≤ accessiblePrefixLength S then 1 else 0 := by
  unfold maskedRunMass
  rw [Finset.sum_eq_single j]
  · simp [singleRun]
  · intro k _ hk
    simp [singleRun, hk]
  · exact fun h => (h (Finset.mem_univ _)).elim

/-- The accessible prefix length is a complete invariant of the ready
mass as a function of normalized chain amplitudes. -/
theorem maskedRunMass_agree_iff (S T : Finset (Fin n)) :
    (∀ A : RunAmplitudes n, maskedRunMass S A = maskedRunMass T A) ↔
      accessiblePrefixLength S = accessiblePrefixLength T := by
  constructor
  · intro h
    apply le_antisymm
    · by_contra! hlt
      let j : Fin (n + 1) := ⟨accessiblePrefixLength S,
        Nat.lt_succ_of_le (accessiblePrefixLength_le S)⟩
      simpa [maskedRunMass_single, j, not_le_of_gt hlt] using h (singleRun j)
    · by_contra! hlt
      let j : Fin (n + 1) := ⟨accessiblePrefixLength T,
        Nat.lt_succ_of_le (accessiblePrefixLength_le T)⟩
      simpa [maskedRunMass_single, j, not_le_of_gt hlt] using h (singleRun j)
  · intro h A
    simp only [maskedRunMass, h]

#print axioms runSignature_lost_ready_iff
#print axioms exists_optimal_maskedRun_recovery
#print axioms maskedRunMass_agree_iff

end

end GaloisForLFunctions.HilbertMetric.QuantumInformation.ReadyBranch
