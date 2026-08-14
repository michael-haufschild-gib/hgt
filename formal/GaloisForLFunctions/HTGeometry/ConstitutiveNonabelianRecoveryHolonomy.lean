import GaloisForLFunctions.HTGeometry.ConstitutiveRecoveryCocycleHolonomy
import Mathlib.Data.Nat.Periodic
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.GroupTheory.Perm.Cycle.Concrete

open scoped ENNReal
open MeasureTheory InformationTheory ProbabilityTheory
open Equiv

/-!
# Nonabelian recovery holonomy

Primitive-cycle group-valued ledgers on finite permutation observers. Gauge classes are exactly
classified by primitive holonomy conjugacy classes. The module also proves repeated-period,
commutator-schedule, finite-observer recurrence, and automorphic reflection laws.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option linter.unusedSectionVars false

local instance classicalDecidableSameCycle {S : Type*} (T : Perm S) : DecidableRel T.SameCycle :=
  Classical.decRel _

variable {S G : Type*} [Fintype S] [Group G]

/-- Ordered ledger product, with later increments multiplied on the left. -/
def groupLedgerProduct (T : Perm S) (c : S → G) : ℕ → S → G
  | 0, _ => 1
  | n + 1, s => c ((T ^ n) s) * groupLedgerProduct T c n s

@[simp] theorem groupLedgerProduct_zero (T : Perm S) (c : S → G) (s : S) :
    groupLedgerProduct T c 0 s = 1 := rfl

@[simp] theorem groupLedgerProduct_succ (T : Perm S) (c : S → G) (n : ℕ) (s : S) :
    groupLedgerProduct T c (n + 1) s =
      c ((T ^ n) s) * groupLedgerProduct T c n s := rfl

theorem groupLedgerProduct_add (T : Perm S) (c : S → G) (m n : ℕ) (s : S) :
    groupLedgerProduct T c (m + n) s =
      groupLedgerProduct T c n ((T ^ m) s) * groupLedgerProduct T c m s := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, groupLedgerProduct_succ, groupLedgerProduct_succ, ih]
      have hp : (T ^ (m + n)) s = (T ^ n) ((T ^ m) s) := by
        calc
          (T ^ (m + n)) s = ((T ^ m) * (T ^ n)) s := by rw [pow_add]
          _ = ((T ^ n) * (T ^ m)) s := by
            exact congrArg (fun p : Perm S => p s) ((Commute.refl T).pow_pow m n).eq
          _ = (T ^ n) ((T ^ m) s) := rfl
      rw [hp]
      group

def groupLedgerGauge (T : Perm S) (c h : S → G) : S → G :=
  fun s => h (T s) * c s * (h s)⁻¹

theorem groupLedgerProduct_gauge (T : Perm S) (c h : S → G) (n : ℕ) (s : S) :
    groupLedgerProduct T (groupLedgerGauge T c h) n s =
      h ((T ^ n) s) * groupLedgerProduct T c n s * (h s)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [groupLedgerProduct_succ, groupLedgerProduct_succ, ih]
      have hp : T ((T ^ n) s) = (T ^ (n + 1)) s := by
        rw [pow_succ']
        rfl
      rw [groupLedgerGauge, hp]
      group

def groupCyclePeriod (T : Perm S) (s : S) : ℕ :=
  orderOf (T.cycleOf s)

theorem groupCyclePeriod_pos (T : Perm S) (s : S) :
    0 < groupCyclePeriod T s :=
  orderOf_pos _

theorem pow_groupCyclePeriod_apply (T : Perm S) (s : S) :
    (T ^ groupCyclePeriod T s) s = s := by
  rw [groupCyclePeriod, ← Perm.cycleOf_pow_apply_self, pow_orderOf_eq_one]
  rfl

def groupCycleHolonomy (T : Perm S) (c : S → G) (s : S) : G :=
  groupLedgerProduct T c (groupCyclePeriod T s) s

theorem groupCyclePeriod_pow_apply (T : Perm S) (j : ℕ) (s : S) :
    groupCyclePeriod T ((T ^ j) s) = groupCyclePeriod T s := by
  simp [groupCyclePeriod]

theorem groupCycleHolonomy_gauge (T : Perm S) (c h : S → G) (s : S) :
    groupCycleHolonomy T (groupLedgerGauge T c h) s =
      h s * groupCycleHolonomy T c s * (h s)⁻¹ := by
  rw [groupCycleHolonomy, groupLedgerProduct_gauge, pow_groupCyclePeriod_apply]
  rfl

theorem groupCycleHolonomy_pow_apply (T : Perm S) (c : S → G) (j : ℕ) (s : S) :
    groupCycleHolonomy T c ((T ^ j) s) =
      groupLedgerProduct T c j s * groupCycleHolonomy T c s *
        (groupLedgerProduct T c j s)⁻¹ := by
  let p := groupCyclePeriod T s
  let u := groupLedgerProduct T c j s
  have hreturn : (T ^ p) s = s := by
    simpa [p] using pow_groupCyclePeriod_apply T s
  have hperiod : groupCyclePeriod T ((T ^ j) s) = p := by
    simpa [p] using groupCyclePeriod_pow_apply T j s
  have h₁ := groupLedgerProduct_add T c p j s
  have h₂ := groupLedgerProduct_add T c j p s
  rw [hreturn] at h₁
  rw [Nat.add_comm p j] at h₁
  have heq : groupCycleHolonomy T c ((T ^ j) s) * u =
      u * groupCycleHolonomy T c s := by
    simpa [groupCycleHolonomy, p, u, hperiod] using h₂.symm.trans h₁
  calc
    groupCycleHolonomy T c ((T ^ j) s) =
        (groupCycleHolonomy T c ((T ^ j) s) * u) * u⁻¹ := by group
    _ = (u * groupCycleHolonomy T c s) * u⁻¹ := by rw [heq]
    _ = u * groupCycleHolonomy T c s * u⁻¹ := rfl

theorem groupCycleHolonomy_isConj_of_sameCycle (T : Perm S) (c : S → G)
    {s t : S} (hst : T.SameCycle s t) :
    IsConj (groupCycleHolonomy T c s) (groupCycleHolonomy T c t) := by
  obtain ⟨j, rfl⟩ := hst.exists_nat_pow_eq
  let u := groupLedgerProduct T c j s
  refine ⟨toUnits u, ?_⟩
  show u * groupCycleHolonomy T c s = groupCycleHolonomy T c ((T ^ j) s) * u
  rw [groupCycleHolonomy_pow_apply]
  dsimp [u]
  group

/-- A canonical representative of the permutation cycle containing `s`. -/
def groupCycleBase (T : Perm S) (s : S) : S :=
  Quotient.out (Quotient.mk (Perm.SameCycle.setoid T) s)

theorem groupCycleBase_sameCycle (T : Perm S) (s : S) :
    T.SameCycle (groupCycleBase T s) s := by
  change (Perm.SameCycle.setoid T) (groupCycleBase T s) s
  unfold groupCycleBase
  exact Quotient.mk_out s

theorem groupCycleBase_eq_of_sameCycle (T : Perm S) {s t : S}
    (hst : T.SameCycle s t) : groupCycleBase T s = groupCycleBase T t := by
  exact congrArg Quotient.out (Quotient.sound hst)

@[simp] theorem groupCycleBase_apply (T : Perm S) (s : S) :
    groupCycleBase T (T s) = groupCycleBase T s := by
  have h : T.SameCycle s (T s) := ⟨1, by simp⟩
  exact (groupCycleBase_eq_of_sameCycle T h).symm

/-- A chosen nonnegative coordinate from the cycle base to `s`. -/
def groupCycleIndex (T : Perm S) (s : S) : ℕ :=
  by
    classical
    exact Nat.find (groupCycleBase_sameCycle T s).exists_nat_pow_eq

theorem pow_groupCycleIndex_apply_base (T : Perm S) (s : S) :
    (T ^ groupCycleIndex T s) (groupCycleBase T s) = s := by
  classical
  exact Nat.find_spec (groupCycleBase_sameCycle T s).exists_nat_pow_eq

/-- Gauge value transported `n` steps from a cycle base with initial value `u`. -/
def groupGaugePath (T : Perm S) (c d : S → G) (b : S) (u : G) (n : ℕ) : G :=
  groupLedgerProduct T d n b * u * (groupLedgerProduct T c n b)⁻¹

theorem groupGaugePath_periodic (T : Perm S) (c d : S → G) (b : S) (u : G)
    (hconj : u * groupCycleHolonomy T c b = groupCycleHolonomy T d b * u) :
    Function.Periodic (groupGaugePath T c d b u) (groupCyclePeriod T b) := by
  intro n
  rw [groupGaugePath, groupGaugePath, Nat.add_comm n, groupLedgerProduct_add,
    groupLedgerProduct_add, pow_groupCyclePeriod_apply]
  change groupLedgerProduct T d n b * groupCycleHolonomy T d b * u *
      (groupLedgerProduct T c n b * groupCycleHolonomy T c b)⁻¹ =
    groupLedgerProduct T d n b * u * (groupLedgerProduct T c n b)⁻¹
  rw [mul_inv_rev]
  have hcancel : groupCycleHolonomy T d b * u *
      (groupCycleHolonomy T c b)⁻¹ = u := by
    rw [← hconj]
    group
  calc
    groupLedgerProduct T d n b * groupCycleHolonomy T d b * u *
        ((groupCycleHolonomy T c b)⁻¹ * (groupLedgerProduct T c n b)⁻¹) =
      groupLedgerProduct T d n b *
        (groupCycleHolonomy T d b * u * (groupCycleHolonomy T c b)⁻¹) *
          (groupLedgerProduct T c n b)⁻¹ := by group
    _ = groupLedgerProduct T d n b * u * (groupLedgerProduct T c n b)⁻¹ := by
      rw [hcancel]

theorem groupCycle_pow_mod_eq_of_apply_eq (T : Perm S) (b : S) {m n : ℕ}
    (h : (T ^ m) b = (T ^ n) b) :
    m % groupCyclePeriod T b = n % groupCyclePeriod T b := by
  by_cases hb : T b = b
  · have hcycle : T.cycleOf b = 1 := (Perm.cycleOf_eq_one_iff T).2 hb
    simp only [groupCyclePeriod, hcycle, orderOf_one, Nat.mod_one]
  · have hpow : T.cycleOf b ^ m = T.cycleOf b ^ n := by
      apply (Perm.isCycle_cycleOf T hb).pow_eq_pow_iff.2
      refine ⟨b, ?_, ?_⟩
      · simpa using hb
      · simpa using h
    simpa [groupCyclePeriod] using
      ((isOfFinOrder_iff_pow_eq_one).2 ⟨groupCyclePeriod T b,
        groupCyclePeriod_pos T b, by simp [groupCyclePeriod]⟩).pow_inj_mod.mp hpow

theorem groupGaugePath_eq_of_apply_eq (T : Perm S) (c d : S → G) (b : S) (u : G)
    (hconj : u * groupCycleHolonomy T c b = groupCycleHolonomy T d b * u)
    {m n : ℕ} (h : (T ^ m) b = (T ^ n) b) :
    groupGaugePath T c d b u m = groupGaugePath T c d b u n := by
  let hp := groupGaugePath_periodic T c d b u hconj
  calc
    groupGaugePath T c d b u m =
        groupGaugePath T c d b u (m % groupCyclePeriod T b) :=
      (hp.map_mod_nat m).symm
    _ = groupGaugePath T c d b u (n % groupCyclePeriod T b) := by
      rw [groupCycle_pow_mod_eq_of_apply_eq T b h]
    _ = groupGaugePath T c d b u n := hp.map_mod_nat n

/-- A chosen conjugator for each primitive cycle holonomy pair. -/
def groupCycleConjugator (T : Perm S) (c d : S → G)
    (hhol : ∀ s, IsConj (groupCycleHolonomy T c s) (groupCycleHolonomy T d s))
    (s : S) : G :=
  ↑(Classical.choose (hhol s))

theorem groupCycleConjugator_semiconj (T : Perm S) (c d : S → G)
    (hhol : ∀ s, IsConj (groupCycleHolonomy T c s) (groupCycleHolonomy T d s))
    (s : S) :
    groupCycleConjugator T c d hhol s * groupCycleHolonomy T c s =
      groupCycleHolonomy T d s * groupCycleConjugator T c d hhol s := by
  exact Classical.choose_spec (hhol s)

/-- Gauge reconstructed from primitive cycle holonomy conjugators. -/
def classifiedGroupGauge (T : Perm S) (c d : S → G)
    (hhol : ∀ s, IsConj (groupCycleHolonomy T c s) (groupCycleHolonomy T d s))
    (s : S) : G :=
  groupGaugePath T c d (groupCycleBase T s)
    (groupCycleConjugator T c d hhol (groupCycleBase T s)) (groupCycleIndex T s)

theorem classifiedGroupGauge_eq_path (T : Perm S) (c d : S → G)
    (hhol : ∀ s, IsConj (groupCycleHolonomy T c s) (groupCycleHolonomy T d s))
    (s : S) {n : ℕ} (hn : (T ^ n) (groupCycleBase T s) = s) :
    classifiedGroupGauge T c d hhol s =
      groupGaugePath T c d (groupCycleBase T s)
        (groupCycleConjugator T c d hhol (groupCycleBase T s)) n := by
  apply groupGaugePath_eq_of_apply_eq T c d
  · exact groupCycleConjugator_semiconj T c d hhol (groupCycleBase T s)
  · exact (pow_groupCycleIndex_apply_base T s).trans hn.symm

theorem classifiedGroupGauge_spec (T : Perm S) (c d : S → G)
    (hhol : ∀ s, IsConj (groupCycleHolonomy T c s) (groupCycleHolonomy T d s))
    (s : S) :
    d s = groupLedgerGauge T c (classifiedGroupGauge T c d hhol) s := by
  let b := groupCycleBase T s
  let n := groupCycleIndex T s
  have hn : (T ^ n) b = s := by
    simpa [b, n] using pow_groupCycleIndex_apply_base T s
  have hnnext : (T ^ (n + 1)) b = T s := by
    rw [pow_succ']
    exact congrArg T hn
  have hs := classifiedGroupGauge_eq_path T c d hhol s hn
  change classifiedGroupGauge T c d hhol s =
    groupGaugePath T c d b (groupCycleConjugator T c d hhol b) n at hs
  have hbnext : groupCycleBase T (T s) = b := by simp [b]
  have hnnext' : (T ^ (n + 1)) (groupCycleBase T (T s)) = T s := by
    rw [hbnext]
    exact hnnext
  have hTs := classifiedGroupGauge_eq_path T c d hhol (T s) hnnext'
  rw [hbnext] at hTs
  rw [groupLedgerGauge, hs, hTs, groupGaugePath, groupGaugePath,
    groupLedgerProduct_succ, groupLedgerProduct_succ, hn]
  group

/-- Two ledgers differ by a vertex gauge. -/
def GroupGaugeEquivalent (T : Perm S) (c d : S → G) : Prop :=
  ∃ h : S → G, d = groupLedgerGauge T c h

/-- Primitive cycle holonomy conjugacy classes exactly classify group-valued ledgers up to gauge. -/
theorem groupGaugeEquivalent_iff_cycleHolonomy_isConj (T : Perm S) (c d : S → G) :
    GroupGaugeEquivalent T c d ↔
      ∀ s, IsConj (groupCycleHolonomy T c s) (groupCycleHolonomy T d s) := by
  constructor
  · rintro ⟨h, rfl⟩ s
    rw [groupCycleHolonomy_gauge]
    exact isConj_iff.2 ⟨h s, rfl⟩
  · intro hhol
    refine ⟨classifiedGroupGauge T c d hhol, ?_⟩
    funext s
    exact classifiedGroupGauge_spec T c d hhol s

theorem groupLedgerProduct_mul_period (T : Perm S) (c : S → G) {P : ℕ} (s : S)
    (hperiod : (T ^ P) s = s) (k : ℕ) :
    groupLedgerProduct T c (k * P) s = (groupLedgerProduct T c P s) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, groupLedgerProduct_add, ih]
      have hreturn : (T ^ (k * P)) s = s := pow_mul_period_apply T hperiod k
      rw [hreturn, pow_succ']

/-- Four marked executions generate the group commutator as ordered holonomy. -/
theorem four_step_schedule_commutator (T : Perm S) (c : S → G)
    (s₀ s₁ s₂ s₃ : S) (A B : G)
    (h₀ : T s₀ = s₁) (h₁ : T s₁ = s₂) (h₂ : T s₂ = s₃)
    (_h₃ : T s₃ = s₀)
    (hc₀ : c s₀ = B⁻¹) (hc₁ : c s₁ = A⁻¹)
    (hc₂ : c s₂ = B) (hc₃ : c s₃ = A) :
    groupLedgerProduct T c 4 s₀ = A * B * A⁻¹ * B⁻¹ := by
  have hp₁ : (T ^ 1) s₀ = s₁ := by simpa using h₀
  have hp₂ : (T ^ 2) s₀ = s₂ := by simp [pow_succ', h₀, h₁]
  have hp₃ : (T ^ 3) s₀ = s₃ := by simp [pow_succ', h₀, h₁, h₂]
  change c ((T ^ 3) s₀) * (c ((T ^ 2) s₀) * (c ((T ^ 1) s₀) * (c s₀ * 1))) = _
  rw [hp₁, hp₂, hp₃, hc₀, hc₁, hc₂, hc₃]
  group

theorem commutator_eq_one_iff_commute (A B : G) :
    A * B * A⁻¹ * B⁻¹ = 1 ↔ Commute A B := by
  constructor
  · intro h
    rw [Commute]
    calc
      A * B = (A * B * A⁻¹ * B⁻¹) * B * A := by group
      _ = 1 * B * A := by rw [h]
      _ = B * A := by group
  · intro h
    rw [h.eq]
    group

theorem four_step_schedule_holonomy_eq_one_iff_commute (T : Perm S) (c : S → G)
    (s₀ s₁ s₂ s₃ : S) (A B : G)
    (h₀ : T s₀ = s₁) (h₁ : T s₁ = s₂) (h₂ : T s₂ = s₃)
    (h₃ : T s₃ = s₀)
    (hc₀ : c s₀ = B⁻¹) (hc₁ : c s₁ = A⁻¹)
    (hc₂ : c s₂ = B) (hc₃ : c s₃ = A) :
    groupLedgerProduct T c 4 s₀ = 1 ↔ Commute A B := by
  rw [four_step_schedule_commutator T c s₀ s₁ s₂ s₃ A B
    h₀ h₁ h₂ h₃ hc₀ hc₁ hc₂ hc₃]
  exact commutator_eq_one_iff_commute A B

theorem finite_observer_holonomy_powers_periodic {Q : Type*} [Group Q] [Finite Q]
    (π : G →* Q) (H : G) :
    Function.Periodic (fun k : ℕ ↦ π (H ^ k)) (orderOf (π H)) := by
  intro k
  calc
    π (H ^ (k + orderOf (π H))) = π (H ^ k) * π (H ^ orderOf (π H)) := by
      rw [pow_add, map_mul]
    _ = (π H) ^ k * (π H) ^ orderOf (π H) := by rw [map_pow, map_pow]
    _ = π (H ^ k) := by rw [pow_orderOf_eq_one, mul_one, map_pow]

theorem finite_observer_holonomy_period_pos {Q : Type*} [Group Q] [Finite Q]
    (π : G →* Q) (H : G) :
    0 < orderOf (π H) :=
  orderOf_pos _

/-- Reverse every old edge and apply a group automorphism. -/
def reflectedGroupLedger (T : Perm S) (α : G ≃* G) (c : S → G) : S → G :=
  fun s ↦ α ((c (T.symm s))⁻¹)

theorem reflectedGroupLedger_product (T : Perm S) (α : G ≃* G) (c : S → G)
    (n : ℕ) (s : S) :
    groupLedgerProduct T.symm (reflectedGroupLedger T α c) n s =
      α ((groupLedgerProduct T c n ((T.symm ^ n) s))⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
      let b := (T.symm ^ (n + 1)) s
      have hb : T b = (T.symm ^ n) s := by
        simp [b, pow_succ']
      have hadd : groupLedgerProduct T c (n + 1) b =
          groupLedgerProduct T c n ((T.symm ^ n) s) * c b := by
        simpa [Nat.add_comm, hb] using groupLedgerProduct_add T c 1 n b
      rw [groupLedgerProduct_succ, ih]
      unfold reflectedGroupLedger
      have hbn : T.symm ((T.symm ^ n) s) = b := by simp [b, pow_succ']
      rw [hbn]
      change α ((c b)⁻¹) * α ((groupLedgerProduct T c n ((T.symm ^ n) s))⁻¹) =
        α ((groupLedgerProduct T c (n + 1) b)⁻¹)
      rw [← α.map_mul, hadd]
      congr 1
      group

theorem groupCyclePeriod_inv (T : Perm S) (s : S) :
    groupCyclePeriod T.symm s = groupCyclePeriod T s := by
  unfold groupCyclePeriod
  let dinv : DecidableRel (T⁻¹ : Perm S).SameCycle := T.instDecidableRelSameCycleInv
  have hind : @Perm.cycleOf S T.symm (classicalDecidableSameCycle T.symm) s =
      @Perm.cycleOf S T⁻¹ dinv s := by
    ext x
    rw [Perm.cycleOf_apply, Perm.cycleOf_apply]
    rw [← Perm.inv_def T]
    by_cases h : (T⁻¹ : Perm S).SameCycle s x <;> simp [h]
  have hcycle : @Perm.cycleOf S T⁻¹ dinv s = (T.cycleOf s)⁻¹ :=
    (Perm.cycleOf_inv T s).symm
  rw [hind, hcycle, orderOf_inv]

/-- Reversing a primitive cycle sends holonomy to the automorphic inverse. -/
theorem reflectedGroupLedger_holonomy (T : Perm S) (α : G ≃* G) (c : S → G)
    (s : S) :
    groupCycleHolonomy T.symm (reflectedGroupLedger T α c) s =
      α ((groupCycleHolonomy T c s)⁻¹) := by
  rw [groupCycleHolonomy, groupCyclePeriod_inv,
    reflectedGroupLedger_product, groupCycleHolonomy]
  have hreturn : (T.symm ^ groupCyclePeriod T s) s = s := by
    rw [← groupCyclePeriod_inv]
    exact pow_groupCyclePeriod_apply T.symm s
  rw [hreturn]

section GroupSignature

variable [MeasurableSpace S]

/-- KL geometry paired with the complete primitive holonomy conjugacy packet. -/
def nonabelianRecoverySignature (mu nu : Measure S) (T : Perm S) (c : S → G) :
    ℝ≥0∞ × (S → ConjClasses G) :=
  (klDiv mu nu, fun s ↦ ConjClasses.mk (groupCycleHolonomy T c s))

theorem nonabelianRecoverySignature_eq_iff (mu nu mu' nu' : Measure S)
    (T : Perm S) (c d : S → G) :
    nonabelianRecoverySignature mu nu T c =
        nonabelianRecoverySignature mu' nu' T d ↔
      klDiv mu nu = klDiv mu' nu' ∧ GroupGaugeEquivalent T c d := by
  rw [Prod.ext_iff]
  simp only [nonabelianRecoverySignature]
  constructor
  · rintro ⟨hkl, hpacket⟩
    refine ⟨hkl, (groupGaugeEquivalent_iff_cycleHolonomy_isConj T c d).2 ?_⟩
    intro s
    exact ConjClasses.mk_eq_mk_iff_isConj.mp (congrFun hpacket s)
  · rintro ⟨hkl, hgauge⟩
    refine ⟨hkl, funext fun s ↦ ?_⟩
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr
      ((groupGaugeEquivalent_iff_cycleHolonomy_isConj T c d).1 hgauge s)

end GroupSignature

section GroupPacket

variable [MeasurableSpace S] [MeasurableSingletonClass S]
  {H : Type*} [MeasurableSpace H] [MeasurableSpace G]

noncomputable def groupRecoveryLedgerConditional (kappa : Kernel S H)
    (T : Perm S) (c : S → G) (n : ℕ) : Kernel S (H × G) :=
  Kernel.comap kappa (fun s ↦ (T ^ n) s) (measurable_of_finite _) ×ₖ
    Kernel.deterministic (groupLedgerProduct T c n) (measurable_of_finite _)

noncomputable def groupEndpointPacketMeasurableEquiv (T : Perm S) (n : ℕ) :
    S × (H × G) ≃ᵐ S × (H × G) where
  toEquiv := Equiv.prodCongr (T ^ n) (Equiv.refl _)
  measurable_toFun := by
    change Measurable (fun z : S × (H × G) ↦ ((T ^ n) z.1, z.2))
    exact (measurable_of_finite (fun s : S ↦ (T ^ n) s)).comp measurable_fst |>.prodMk
      measurable_snd
  measurable_invFun := by
    change Measurable (fun z : S × (H × G) ↦ ((T ^ n).symm z.1, z.2))
    exact (measurable_of_finite (fun s : S ↦ (T ^ n).symm s)).comp measurable_fst |>.prodMk
      measurable_snd

noncomputable def groupRecoveryCocyclePacket (mu : Measure S) (kappa : Kernel S H)
    (T : Perm S) (c : S → G) (n : ℕ) : Measure (S × (H × G)) :=
  (splitFormation mu (groupRecoveryLedgerConditional kappa T c n)).map
    (groupEndpointPacketMeasurableEquiv (H := H) (G := G) T n)

def groupRecoveryInitialObserver (T : Perm S) (n : ℕ) : S × (H × G) → S :=
  fun z ↦ (T ^ n).symm z.1

theorem groupRecoveryCocyclePacket_recovers_observer
    (mu : Measure S) [IsFiniteMeasure mu]
    (kappa : Kernel S H) [IsMarkovKernel kappa]
    (T : Perm S) (c : S → G) (n : ℕ) :
    (groupRecoveryCocyclePacket mu kappa T c n).map
        (groupRecoveryInitialObserver (H := H) (G := G) T n) = mu := by
  let eta := groupRecoveryLedgerConditional kappa T c n
  haveI : IsMarkovKernel eta := by
    dsimp [eta, groupRecoveryLedgerConditional]
    infer_instance
  have hrecover := splitFormation_recovers_observer mu eta
  rw [Measure.fst] at hrecover
  unfold groupRecoveryCocyclePacket groupRecoveryInitialObserver
  rw [Measure.map_map]
  · simpa [groupEndpointPacketMeasurableEquiv, Function.comp_def] using hrecover
  · exact (measurable_of_finite (fun s : S ↦ (T ^ n).symm s)).comp measurable_fst
  · exact (groupEndpointPacketMeasurableEquiv (H := H) (G := G) T n).measurable

theorem groupRecoveryCocyclePacket_klDiv
    (mu nu : Measure S) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (kappa : Kernel S H) [IsMarkovKernel kappa]
    (T : Perm S) (c : S → G) (n : ℕ) :
    klDiv (groupRecoveryCocyclePacket mu kappa T c n)
        (groupRecoveryCocyclePacket nu kappa T c n) = klDiv mu nu := by
  let eta := groupRecoveryLedgerConditional kappa T c n
  haveI : IsMarkovKernel eta := by
    dsimp [eta, groupRecoveryLedgerConditional]
    infer_instance
  haveI : IsFiniteMeasure (splitFormation mu eta) :=
    IsFiniteMeasure.mk (by
      rw [splitFormation, Measure.compProd_apply_univ]
      exact measure_lt_top mu Set.univ)
  haveI : IsFiniteMeasure (splitFormation nu eta) :=
    IsFiniteMeasure.mk (by
      rw [splitFormation, Measure.compProd_apply_univ]
      exact measure_lt_top nu Set.univ)
  unfold groupRecoveryCocyclePacket
  change klDiv ((splitFormation mu eta).map _)
      ((splitFormation nu eta).map _) = _
  rw [klDiv_map_measurableEmbedding
    (groupEndpointPacketMeasurableEquiv (H := H) (G := G) T n).measurableEmbedding]
  exact klDiv_splitFormation mu nu eta

theorem groupRecoveryCocyclePacket_informationNeutral
    (mu nu : Measure S) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (kappa : Kernel S H) [IsMarkovKernel kappa]
    (T : Perm S) (c d : S → G) (m n : ℕ) :
    klDiv (groupRecoveryCocyclePacket mu kappa T c m)
        (groupRecoveryCocyclePacket nu kappa T c m) =
      klDiv (groupRecoveryCocyclePacket mu kappa T d n)
        (groupRecoveryCocyclePacket nu kappa T d n) := by
  rw [groupRecoveryCocyclePacket_klDiv, groupRecoveryCocyclePacket_klDiv]

end GroupPacket

end

end GaloisForLFunctions.HTGeometry
