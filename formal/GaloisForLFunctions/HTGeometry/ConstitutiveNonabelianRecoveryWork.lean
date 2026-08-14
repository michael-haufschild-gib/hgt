import GaloisForLFunctions.HTGeometry.ConstitutiveConjugacyWordWork
import GaloisForLFunctions.HTGeometry.ConstitutiveNonabelianRecoveryHolonomy

open Equiv

/-!
# Exact nonabelian recovery work on a marked cycle

Connects primitive holonomy gauge classification to finite symmetric-generator word work. For one
marked `m`-cycle, every gauge representative obeys the sharp conjugacy-length and balanced-square
lower bounds, and an explicitly reconstructed ledger attains both minima simultaneously.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option linter.unusedSectionVars false

local instance classicalDecidableSameCycleWork {S : Type*} (T : Perm S) :
    DecidableRel T.SameCycle := Classical.decRel _

variable {S G : Type*} [Fintype S] [Group G]


theorem groupLedgerProduct_eq_reverse_prod_ofFn (T : Perm S) (c : S → G)
    (n : ℕ) (s : S) :
    groupLedgerProduct T c n s =
      (List.ofFn fun j : Fin n ↦ c ((T ^ (j : ℕ)) s)).reverse.prod := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [groupLedgerProduct_succ, List.ofFn_succ']
      rw [ih]
      simp

def cycleReverseWord (T : Perm S) (c : S → G) (m : ℕ) (s : S) : List G :=
  (List.ofFn fun j : Fin m ↦ c ((T ^ (j : ℕ)) s)).reverse

theorem cycleReverseWord_length (T : Perm S) (c : S → G) (m : ℕ) (s : S) :
    (cycleReverseWord T c m s).length = m := by
  simp [cycleReverseWord]

theorem cycleReverseWord_prod (T : Perm S) (c : S → G) (m : ℕ) (s : S) :
    (cycleReverseWord T c m s).prod = groupLedgerProduct T c m s := by
  exact (groupLedgerProduct_eq_reverse_prod_ofFn T c m s).symm

def cycleLinearWordWork (A : SymmetricGeneratingSet G)
    (T : Perm S) (c : S → G) (m : ℕ) (s : S) : ℕ :=
  listWordWork A (cycleReverseWord T c m s)

def cycleQuadraticWordWork (A : SymmetricGeneratingSet G)
    (T : Perm S) (c : S → G) (m : ℕ) (s : S) : ℕ :=
  listQuadraticWordWork A (cycleReverseWord T c m s)

def cycleForwardIndex (T : Perm S) (s : S) {m : ℕ}
    (hcycle : ∀ t, T.SameCycle s t) (hperiod : groupCyclePeriod T s = m)
    (t : S) : Fin m := by
  classical
  have hm : 0 < m := hperiod ▸ groupCyclePeriod_pos T s
  exact ⟨Nat.find (hcycle t).exists_nat_pow_eq % m, Nat.mod_lt _ hm⟩

theorem cycleForwardIndex_pow_apply (T : Perm S) (s : S) {m : ℕ}
    (hcycle : ∀ t, T.SameCycle s t) (hperiod : groupCyclePeriod T s = m)
    (j : Fin m) :
    cycleForwardIndex T s hcycle hperiod ((T ^ (j : ℕ)) s) = j := by
  classical
  apply Fin.ext
  let n := Nat.find (hcycle ((T ^ (j : ℕ)) s)).exists_nat_pow_eq
  have hn : (T ^ n) s = (T ^ (j : ℕ)) s :=
    Nat.find_spec (hcycle ((T ^ (j : ℕ)) s)).exists_nat_pow_eq
  have hmod := groupCycle_pow_mod_eq_of_apply_eq T s hn
  unfold cycleForwardIndex
  change n % m = (j : ℕ)
  simp only [hperiod] at hmod
  exact hmod.trans (Nat.mod_eq_of_lt j.isLt)

def cycleLedgerFromFactors (T : Perm S) (s : S) {m : ℕ}
    (hcycle : ∀ t, T.SameCycle s t) (hperiod : groupCyclePeriod T s = m)
    (factors : Fin m → G) : S → G :=
  fun t ↦ factors (cycleForwardIndex T s hcycle hperiod t)

theorem cycleLedgerFromFactors_apply_pow (T : Perm S) (s : S) {m : ℕ}
    (hcycle : ∀ t, T.SameCycle s t) (hperiod : groupCyclePeriod T s = m)
    (factors : Fin m → G) (j : Fin m) :
    cycleLedgerFromFactors T s hcycle hperiod factors ((T ^ (j : ℕ)) s) = factors j := by
  simp [cycleLedgerFromFactors, cycleForwardIndex_pow_apply]

def listToFinOfLength {A : Type*} (xs : List A) {m : ℕ} (h : xs.length = m) : Fin m → A :=
  fun i ↦ xs.get (Fin.cast h.symm i)

theorem ofFn_listToFinOfLength {A : Type*} (xs : List A) {m : ℕ}
    (h : xs.length = m) :
    List.ofFn (listToFinOfLength xs h) = xs := by
  subst m
  exact List.ofFn_get xs

theorem cycleReverseWord_cycleLedgerFromFactors (T : Perm S) (s : S) {m : ℕ}
    (hcycle : ∀ t, T.SameCycle s t) (hperiod : groupCyclePeriod T s = m)
    (factors : Fin m → G) :
    cycleReverseWord T (cycleLedgerFromFactors T s hcycle hperiod factors) m s =
      (List.ofFn factors).reverse := by
  unfold cycleReverseWord
  apply congrArg List.reverse
  apply congrArg List.ofFn
  funext j
  exact cycleLedgerFromFactors_apply_pow T s hcycle hperiod factors j

theorem cycle_work_lower_bounds (A : SymmetricGeneratingSet G)
    (T : Perm S) (c d : S → G) (s : S) {m : ℕ}
    (hm : 0 < m) (hperiod : groupCyclePeriod T s = m)
    (hgauge : GroupGaugeEquivalent T c d) :
    conjugacyLength A (groupCycleHolonomy T c s) ≤
        cycleLinearWordWork A T d m s ∧
      balancedWordWork m (conjugacyLength A (groupCycleHolonomy T c s)) ≤
        cycleQuadraticWordWork A T d m s := by
  apply conjugacy_work_lower_bounds A hm (cycleReverseWord T d m s)
  · exact cycleReverseWord_length T d m s
  · rw [cycleReverseWord_prod, ← hperiod, groupCycleHolonomy]
    exact (groupGaugeEquivalent_iff_cycleHolonomy_isConj T c d).1 hgauge s

theorem exists_cycle_work_minimizer (A : SymmetricGeneratingSet G)
    (T : Perm S) (c : S → G) (s : S) {m : ℕ}
    (hm : 0 < m) (hperiod : groupCyclePeriod T s = m)
    (hcycle : ∀ t, T.SameCycle s t) :
    ∃ d : S → G,
      GroupGaugeEquivalent T c d ∧
      cycleLinearWordWork A T d m s =
        conjugacyLength A (groupCycleHolonomy T c s) ∧
      cycleQuadraticWordWork A T d m s =
        balancedWordWork m (conjugacyLength A (groupCycleHolonomy T c s)) := by
  obtain ⟨factors, hlen, hconj, hlinear, hquadratic⟩ :=
    exists_conjugacy_work_minimizer A (groupCycleHolonomy T c s) hm
  have hrevlen : factors.reverse.length = m := by simpa using hlen
  let chronological : Fin m → G := listToFinOfLength factors.reverse hrevlen
  let d := cycleLedgerFromFactors T s hcycle hperiod chronological
  have hchron : List.ofFn chronological = factors.reverse :=
    ofFn_listToFinOfLength factors.reverse hrevlen
  have hword : cycleReverseWord T d m s = factors := by
    rw [cycleReverseWord_cycleLedgerFromFactors, hchron, List.reverse_reverse]
  have hhol : groupCycleHolonomy T d s = factors.prod := by
    rw [groupCycleHolonomy, hperiod, ← cycleReverseWord_prod, hword]
  have hgauge : GroupGaugeEquivalent T c d := by
    apply (groupGaugeEquivalent_iff_cycleHolonomy_isConj T c d).2
    intro t
    have hct := groupCycleHolonomy_isConj_of_sameCycle T c (hcycle t)
    have hdt := groupCycleHolonomy_isConj_of_sameCycle T d (hcycle t)
    have hfactorD : IsConj (groupCycleHolonomy T c s) (groupCycleHolonomy T d s) := by
      rw [hhol]
      exact hconj
    exact hct.symm.trans (hfactorD.trans hdt)
  refine ⟨d, hgauge, ?_, ?_⟩
  · simpa [cycleLinearWordWork, hword] using hlinear
  · simpa [cycleQuadraticWordWork, hword] using hquadratic

theorem cycle_work_exact_minima (A : SymmetricGeneratingSet G)
    (T : Perm S) (c : S → G) (s : S) {m : ℕ}
    (hm : 0 < m) (hperiod : groupCyclePeriod T s = m)
    (hcycle : ∀ t, T.SameCycle s t) :
    (∀ d : S → G, GroupGaugeEquivalent T c d →
      conjugacyLength A (groupCycleHolonomy T c s) ≤ cycleLinearWordWork A T d m s ∧
      balancedWordWork m (conjugacyLength A (groupCycleHolonomy T c s)) ≤
        cycleQuadraticWordWork A T d m s) ∧
    (∃ d : S → G, GroupGaugeEquivalent T c d ∧
      cycleLinearWordWork A T d m s = conjugacyLength A (groupCycleHolonomy T c s) ∧
      cycleQuadraticWordWork A T d m s =
        balancedWordWork m (conjugacyLength A (groupCycleHolonomy T c s))) := by
  exact ⟨fun d hd ↦ cycle_work_lower_bounds A T c d s hm hperiod hd,
    exists_cycle_work_minimizer A T c s hm hperiod hcycle⟩

/-- Accumulated linear work when one marked cycle representative is repeated `k` times. -/
def cyclePeriodicLinearAction (A : SymmetricGeneratingSet G) (k : ℕ)
    (factors : List G) : ℕ :=
  k * listWordWork A factors

/-- Accumulated quadratic work under the same cycle-periodic marking. -/
def cyclePeriodicQuadraticAction (A : SymmetricGeneratingSet G) (k : ℕ)
    (factors : List G) : ℕ :=
  k * listQuadraticWordWork A factors

/-- Repeated marked execution has sharp action `k` times the one-cycle minimum. -/
theorem cycle_periodic_repeated_work_exact (A : SymmetricGeneratingSet G) (H : G)
    {m : ℕ} (hm : 0 < m) (k : ℕ) :
    (∀ factors : List G, factors.length = m → IsConj H factors.prod →
      k * conjugacyLength A H ≤ cyclePeriodicLinearAction A k factors ∧
      k * balancedWordWork m (conjugacyLength A H) ≤
        cyclePeriodicQuadraticAction A k factors) ∧
    (∃ factors : List G, factors.length = m ∧ IsConj H factors.prod ∧
      cyclePeriodicLinearAction A k factors = k * conjugacyLength A H ∧
      cyclePeriodicQuadraticAction A k factors =
        k * balancedWordWork m (conjugacyLength A H)) := by
  constructor
  · intro factors hlen hconj
    obtain ⟨hlinear, hquadratic⟩ :=
      conjugacy_work_lower_bounds A hm factors hlen hconj
    exact ⟨Nat.mul_le_mul_left k hlinear, Nat.mul_le_mul_left k hquadratic⟩
  · obtain ⟨factors, hlen, hconj, hlinear, hquadratic⟩ :=
      exists_conjugacy_work_minimizer A H hm
    refine ⟨factors, hlen, hconj, ?_, ?_⟩
    · simp [cyclePeriodicLinearAction, hlinear]
    · simp [cyclePeriodicQuadraticAction, hquadratic]

theorem cycle_periodic_linear_action_pos (A : SymmetricGeneratingSet G) {H : G}
    (hH : H ≠ 1) {k : ℕ} (hk : 0 < k) :
    0 < k * conjugacyLength A H := by
  exact Nat.mul_pos hk (Nat.pos_of_ne_zero (mt (conjugacyLength_eq_zero_iff A H).mp hH))

end

end GaloisForLFunctions.HTGeometry
