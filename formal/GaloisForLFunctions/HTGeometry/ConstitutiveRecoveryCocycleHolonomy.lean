import GaloisForLFunctions.HTGeometry.ConstitutiveFunctionalEquationPacketLift

/-!
# Recovery cocycles: finite holonomy, Hodge work, and reconstruction

For a permutation on a finite state space, this module proves exact recovery-ledger laws:
finite Livšic classification by cycle holonomy, canonical harmonic representatives, sharp positive
quadratic-work decompositions, bounded-history rigidity, skew-product gauge conjugacy, sandpile
local/cumulative work identities, involutive two-cycle law, and joint reconstruction signatures.

`orderHolonomy` traverses global finite order of the permutation. On each primitive cycle this is
primitive holonomy repeated a positive number of times, hence a faithful redundant encoding of the
primitive-cycle packet. Its Reynolds normalization `harmonicLedger` is exactly the primitive-cycle
mean.

The stochastic packet records endpoint state, fresh common conditional history at that endpoint,
and accumulated ledger. It recovers initial observer and preserves extended KL divergence exactly.
-/

open scoped BigOperators
open scoped ENNReal
open MeasureTheory InformationTheory ProbabilityTheory


open Equiv

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option linter.unusedSectionVars false

variable {S L : Type*} [Fintype S]
  [NormedAddCommGroup L] [InnerProductSpace ℝ L]

def ledgerSum (T : Perm S) (c : S → L) (n : ℕ) (s : S) : L :=
  ∑ j ∈ Finset.range n, c ((T ^ j) s)

theorem ledgerSum_succ (T : Perm S) (c : S → L) (n : ℕ) (s : S) :
    ledgerSum T c (n + 1) s = ledgerSum T c n s + c ((T ^ n) s) := by
  simp [ledgerSum, Finset.sum_range_succ]

theorem sum_shift_of_periodic {P : ℕ} (hP : 0 < P) (f : ℕ → L)
    (hperiod : f P = f 0) :
    (∑ j ∈ Finset.range P, f (j + 1)) = ∑ j ∈ Finset.range P, f j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hP.ne'
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hperiod

theorem ledgerSum_order_apply (T : Perm S) (c : S → L) (s : S) :
    ledgerSum T c (orderOf T) (T s) = ledgerSum T c (orderOf T) s := by
  unfold ledgerSum
  rw [show (∑ j ∈ Finset.range (orderOf T), c ((T ^ j) (T s))) =
      ∑ j ∈ Finset.range (orderOf T), c ((T ^ (j + 1)) s) by
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_succ]
    rfl]
  exact sum_shift_of_periodic (orderOf_pos T) (fun j => c ((T ^ j) s)) (by
    rw [pow_orderOf_eq_one]
    rfl)

def ledgerGauge (T : Perm S) (c h : S → L) : S → L :=
  fun s => c s + h (T s) - h s

theorem ledgerSum_gauge (T : Perm S) (c h : S → L) (n : ℕ) (s : S) :
    ledgerSum T (ledgerGauge T c h) n s =
      ledgerSum T c n s + h ((T ^ n) s) - h s := by
  unfold ledgerSum ledgerGauge
  rw [show (∑ j ∈ Finset.range n,
      (c ((T ^ j) s) + h (T ((T ^ j) s)) - h ((T ^ j) s))) =
      (∑ j ∈ Finset.range n, c ((T ^ j) s)) +
        ∑ j ∈ Finset.range n, (h ((T ^ (j + 1)) s) - h ((T ^ j) s)) by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hpow : T ((T ^ j) s) = (T ^ (j + 1)) s := by
      rw [pow_succ']
      rfl
    rw [hpow]
    abel]
  have htel := Finset.sum_range_sub (fun j => h ((T ^ j) s)) n
  rw [htel]
  simp only [pow_zero]
  change _ + (h ((T ^ n) s) - h s) = _
  abel

def canonicalGaugePotential (T : Perm S) (δ : S → L) : S → L :=
  fun s => -((orderOf T : ℝ)⁻¹) •
    ∑ n ∈ Finset.range (orderOf T), ledgerSum T δ n s

theorem ledgerSum_apply (T : Perm S) (δ : S → L) (n : ℕ) (s : S) :
    ledgerSum T δ n (T s) = ledgerSum T δ (n + 1) s - δ s := by
  unfold ledgerSum
  rw [Finset.sum_range_succ']
  simp only [pow_zero]
  have hshift : (∑ j ∈ Finset.range n, δ ((T ^ j) (T s))) =
      ∑ j ∈ Finset.range n, δ ((T ^ (j + 1)) s) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_succ]
    rfl
  rw [hshift]
  simp

theorem canonicalGaugePotential_coboundary (T : Perm S) (δ : S → L)
    (hδ : ∀ s, ledgerSum T δ (orderOf T) s = 0) (s : S) :
    canonicalGaugePotential T δ (T s) - canonicalGaugePotential T δ s = δ s := by
  let P := orderOf T
  have hP : 0 < P := orderOf_pos T
  have hP0 : (P : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hP.ne'
  have hdiff :
      (∑ n ∈ Finset.range P, ledgerSum T δ n (T s)) -
          (∑ n ∈ Finset.range P, ledgerSum T δ n s) = -(P : ℝ) • δ s := by
    rw [← Finset.sum_sub_distrib]
    have hpoint : ∀ n, ledgerSum T δ n (T s) - ledgerSum T δ n s =
        (ledgerSum T δ (n + 1) s - ledgerSum T δ n s) - δ s := by
      intro n
      rw [ledgerSum_apply]
      abel
    rw [show (∑ n ∈ Finset.range P,
        (ledgerSum T δ n (T s) - ledgerSum T δ n s)) =
        ∑ n ∈ Finset.range P,
          ((ledgerSum T δ (n + 1) s - ledgerSum T δ n s) - δ s) by
      apply Finset.sum_congr rfl
      intro n hn
      exact hpoint n]
    rw [Finset.sum_sub_distrib]
    have htel := Finset.sum_range_sub (fun n => ledgerSum T δ n s) P
    rw [htel]
    rw [show ledgerSum T δ P s = 0 by simpa [P] using hδ s]
    simp [ledgerSum, Nat.cast_smul_eq_nsmul]
  unfold canonicalGaugePotential
  rw [← smul_sub, hdiff, smul_smul]
  simp [P, hP0]

def orderHolonomy (T : Perm S) (c : S → L) : S → L :=
  ledgerSum T c (orderOf T)

theorem orderHolonomy_apply (T : Perm S) (c : S → L) (s : S) :
    orderHolonomy T c (T s) = orderHolonomy T c s :=
  ledgerSum_order_apply T c s

theorem orderHolonomy_gauge (T : Perm S) (c h : S → L) :
    orderHolonomy T (ledgerGauge T c h) = orderHolonomy T c := by
  funext s
  rw [orderHolonomy, ledgerSum_gauge]
  rw [pow_orderOf_eq_one]
  simp [orderHolonomy]

theorem finite_livsic_orderHolonomy_iff (T : Perm S) (c d : S → L) :
    (∃ h : S → L, d = ledgerGauge T c h) ↔
      orderHolonomy T d = orderHolonomy T c := by
  constructor
  · rintro ⟨h, rfl⟩
    exact orderHolonomy_gauge T c h
  · intro hhol
    let δ : S → L := fun s => d s - c s
    have hδ : ∀ s, ledgerSum T δ (orderOf T) s = 0 := by
      intro s
      unfold δ orderHolonomy at hhol
      unfold ledgerSum
      rw [Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (congr_fun hhol s)
    let h := canonicalGaugePotential T δ
    refine ⟨h, ?_⟩
    funext s
    dsimp [ledgerGauge, h]
    have hcob := canonicalGaugePotential_coboundary T δ hδ s
    rw [show canonicalGaugePotential T δ (T s) =
        δ s + canonicalGaugePotential T δ s by exact sub_eq_iff_eq_add.mp hcob]
    dsimp [δ]
    abel

theorem finite_livsic_periodicData_iff (T : Perm S) (c d : S → L) :
    (∃ h : S → L, d = ledgerGauge T c h) ↔
      ∀ (s : S) (P : ℕ), (T ^ P) s = s →
        ledgerSum T d P s = ledgerSum T c P s := by
  constructor
  · rintro ⟨h, rfl⟩ s P hperiod
    rw [ledgerSum_gauge, hperiod]
    simp
  · intro hperiodic
    apply (finite_livsic_orderHolonomy_iff T c d).mpr
    funext s
    exact hperiodic s (orderOf T) (by
      rw [pow_orderOf_eq_one]
      rfl)

theorem finite_livsic_coboundary_iff (T : Perm S) (c : S → L) :
    (∃ h : S → L, c = fun s => h (T s) - h s) ↔
      orderHolonomy T c = 0 := by
  have hzero : orderHolonomy T (fun _ => (0 : L)) = 0 := by
    funext s
    simp [orderHolonomy, ledgerSum]
  rw [← hzero, ← finite_livsic_orderHolonomy_iff T (fun _ => 0) c]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_⟩
    rw [hh]
    funext s
    simp [ledgerGauge]
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_⟩
    rw [hh]
    funext s
    simp [ledgerGauge]

theorem finite_livsic_coboundary_periodicData_iff (T : Perm S) (c : S → L) :
    (∃ h : S → L, c = fun s => h (T s) - h s) ↔
      ∀ (s : S) (P : ℕ), (T ^ P) s = s → ledgerSum T c P s = 0 := by
  rw [finite_livsic_coboundary_iff, funext_iff]
  constructor
  · intro hzero s P hperiod
    have hgauge : ∃ h : S → L, c = ledgerGauge T (fun _ => 0) h :=
      (finite_livsic_orderHolonomy_iff T (fun _ => 0) c).mpr (by
        funext t
        simpa [orderHolonomy, ledgerSum] using hzero t)
    obtain ⟨h, rfl⟩ := hgauge
    rw [ledgerSum_gauge, hperiod]
    simp [ledgerSum]
  · intro hperiodic s
    simpa [orderHolonomy] using hperiodic s (orderOf T) (by
        rw [pow_orderOf_eq_one]
        rfl)

def harmonicLedger (T : Perm S) (c : S → L) : S → L :=
  fun s => ((orderOf T : ℝ)⁻¹) • orderHolonomy T c s

theorem harmonicLedger_apply (T : Perm S) (c : S → L) (s : S) :
    harmonicLedger T c (T s) = harmonicLedger T c s := by
  simp [harmonicLedger, orderHolonomy_apply]

theorem orderHolonomy_pow_apply (T : Perm S) (c : S → L) (j : ℕ) (s : S) :
    orderHolonomy T c ((T ^ j) s) = orderHolonomy T c s := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [pow_succ']
      change orderHolonomy T c (T ((T ^ j) s)) = _
      rw [orderHolonomy_apply]
      exact ih

theorem orderHolonomy_eq_of_sameCycle (T : Perm S) (c : S → L) {s t : S}
    (h : T.SameCycle s t) :
    orderHolonomy T c s = orderHolonomy T c t := by
  obtain ⟨j, hj, hst⟩ := h.exists_pow_eq'
  rw [← hst, orderHolonomy_pow_apply]

theorem orderHolonomy_harmonicLedger (T : Perm S) (c : S → L) :
    orderHolonomy T (harmonicLedger T c) = orderHolonomy T c := by
  funext s
  let P := orderOf T
  have hP : 0 < P := orderOf_pos T
  have hP0 : (P : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hP.ne'
  unfold orderHolonomy ledgerSum harmonicLedger
  rw [show (∑ j ∈ Finset.range (orderOf T),
      ((orderOf T : ℝ)⁻¹) • orderHolonomy T c ((T ^ j) s)) =
      ∑ _j ∈ Finset.range (orderOf T),
        ((orderOf T : ℝ)⁻¹) • orderHolonomy T c s by
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    exact orderHolonomy_pow_apply T c j s]
  simp only [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul]
  simp [P, hP0, orderHolonomy, ledgerSum]

theorem harmonicLedger_gaugeEquivalent (T : Perm S) (c : S → L) :
    ∃ h : S → L, harmonicLedger T c = ledgerGauge T c h :=
  (finite_livsic_orderHolonomy_iff T c (harmonicLedger T c)).mpr
    (orderHolonomy_harmonicLedger T c)

structure LedgerMetric (L : Type*) [NormedAddCommGroup L] [InnerProductSpace ℝ L] where
  op : L →ₗ[ℝ] L
  symmetric : ∀ x y, inner ℝ (op x) y = inner ℝ x (op y)
  positive : ∀ x, x ≠ 0 → 0 < inner ℝ (op x) x

def ledgerWork (Q : LedgerMetric L) (x : L) : ℝ := inner ℝ (Q.op x) x

theorem ledgerWork_nonneg (Q : LedgerMetric L) (x : L) : 0 ≤ ledgerWork Q x := by
  by_cases hx : x = 0
  · simp [hx, ledgerWork]
  · exact (Q.positive x hx).le

theorem ledgerWork_eq_zero_iff (Q : LedgerMetric L) (x : L) :
    ledgerWork Q x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact (Q.positive x hx).ne' h
  · rintro rfl
    simp [ledgerWork]

theorem ledgerWork_add (Q : LedgerMetric L) (x y : L) :
    ledgerWork Q (x + y) = ledgerWork Q x + ledgerWork Q y +
      2 * inner ℝ (Q.op x) y := by
  unfold ledgerWork
  rw [map_add, inner_add_left, inner_add_right, inner_add_right]
  rw [Q.symmetric y x, real_inner_comm y (Q.op x)]
  ring

theorem ledgerWork_mean_deviation (Q : LedgerMetric L) (m x : L) :
    ledgerWork Q x = ledgerWork Q m + ledgerWork Q (x - m) +
      2 * inner ℝ (Q.op m) (x - m) := by
  have := ledgerWork_add Q m (x - m)
  simpa only [add_sub_cancel] using this

theorem invariant_pow_apply (T : Perm S) (m : S → L)
    (hm : ∀ s, m (T s) = m s) (j : ℕ) (s : S) :
    m ((T ^ j) s) = m s := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [pow_succ']
      change m (T ((T ^ j) s)) = _
      rw [hm]
      exact ih

theorem sum_inner_comp_pow_of_invariant (T : Perm S) (m e : S → L)
    (hm : ∀ s, m (T s) = m s) (Q : LedgerMetric L) (j : ℕ) :
    ∑ s, inner ℝ (Q.op (m s)) (e ((T ^ j) s)) =
      ∑ s, inner ℝ (Q.op (m s)) (e s) := by
  calc
    _ = ∑ s, inner ℝ (Q.op (m ((T ^ j) s))) (e ((T ^ j) s)) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [invariant_pow_apply T m hm j s]
    _ = _ := Equiv.sum_comp (T ^ j) (fun s => inner ℝ (Q.op (m s)) (e s))

theorem invariant_orthogonal_to_zeroHolonomy (T : Perm S) (m e : S → L)
    (hm : ∀ s, m (T s) = m s) (he : orderHolonomy T e = 0)
    (Q : LedgerMetric L) :
    ∑ s, inner ℝ (Q.op (m s)) (e s) = 0 := by
  let P := orderOf T
  have hP : 0 < P := orderOf_pos T
  have hP0 : (P : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hP.ne'
  let A : ℝ := ∑ s, inner ℝ (Q.op (m s)) (e s)
  have hj : ∀ j, ∑ s, inner ℝ (Q.op (m s)) (e ((T ^ j) s)) = A := by
    intro j
    exact sum_inner_comp_pow_of_invariant T m e hm Q j
  have hPA : (P : ℝ) * A = 0 := by
    calc
      (P : ℝ) * A = ∑ _j ∈ Finset.range P, A := by
        simp
      _ = ∑ j ∈ Finset.range P,
          ∑ s, inner ℝ (Q.op (m s)) (e ((T ^ j) s)) := by
        apply Finset.sum_congr rfl
        intro j hjmem
        rw [hj]
      _ = ∑ s, ∑ j ∈ Finset.range P,
          inner ℝ (Q.op (m s)) (e ((T ^ j) s)) := by
        rw [Finset.sum_comm]
      _ = ∑ s, inner ℝ (Q.op (m s))
          (∑ j ∈ Finset.range P, e ((T ^ j) s)) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [inner_sum]
      _ = 0 := by
        have he' : ∀ s, ∑ j ∈ Finset.range P, e ((T ^ j) s) = 0 := by
          intro s
          have := congr_fun he s
          simpa [P, orderHolonomy, ledgerSum] using this
        simp [he']
  exact (mul_eq_zero.mp hPA).resolve_left hP0

def ledgerEnergy (Q : LedgerMetric L) (c : S → L) : ℝ :=
  ∑ s, ledgerWork Q (c s)

theorem cycle_hodge_work_identity (T : Perm S) (Q : LedgerMetric L)
    (c d : S → L) (hhol : orderHolonomy T d = orderHolonomy T c) :
    ledgerEnergy Q d = ledgerEnergy Q (harmonicLedger T c) +
      ledgerEnergy Q (fun s => d s - harmonicLedger T c s) := by
  let m := harmonicLedger T c
  let e : S → L := fun s => d s - m s
  have hm : ∀ s, m (T s) = m s := harmonicLedger_apply T c
  have he : orderHolonomy T e = 0 := by
    funext s
    unfold e orderHolonomy ledgerSum
    rw [Finset.sum_sub_distrib]
    change orderHolonomy T d s - orderHolonomy T m s = 0
    rw [hhol, orderHolonomy_harmonicLedger]
    simp
  have hortho := invariant_orthogonal_to_zeroHolonomy T m e hm he Q
  unfold ledgerEnergy
  rw [show (∑ s, ledgerWork Q (d s)) =
      ∑ s, (ledgerWork Q (m s) + ledgerWork Q (e s) +
        2 * inner ℝ (Q.op (m s)) (e s)) by
    apply Finset.sum_congr rfl
    intro s hs
    have hd : d s = m s + e s := by simp [e]
    rw [hd, ledgerWork_add]]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hortho]
  simp [m, e]

theorem cycle_hodge_work_lower_bound (T : Perm S) (Q : LedgerMetric L)
    (c d : S → L) (hhol : orderHolonomy T d = orderHolonomy T c) :
    ledgerEnergy Q (harmonicLedger T c) ≤ ledgerEnergy Q d := by
  rw [cycle_hodge_work_identity T Q c d hhol]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun s hs => ledgerWork_nonneg Q _)

theorem cycle_hodge_work_eq_iff (T : Perm S) (Q : LedgerMetric L)
    (c d : S → L) (hhol : orderHolonomy T d = orderHolonomy T c) :
    ledgerEnergy Q d = ledgerEnergy Q (harmonicLedger T c) ↔
      d = harmonicLedger T c := by
  rw [cycle_hodge_work_identity T Q c d hhol]
  constructor
  · intro h
    have hsum : ledgerEnergy Q (fun s => d s - harmonicLedger T c s) = 0 := by
      linarith
    funext s
    have hterm : ledgerWork Q (d s - harmonicLedger T c s) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => ledgerWork_nonneg Q _)).mp hsum s
        (Finset.mem_univ s)
    exact sub_eq_zero.mp ((ledgerWork_eq_zero_iff Q _).mp hterm)
  · rintro rfl
    simp [ledgerEnergy, ledgerWork]

theorem ledgerSum_add (T : Perm S) (c : S → L) (m n : ℕ) (s : S) :
    ledgerSum T c (m + n) s =
      ledgerSum T c m s + ledgerSum T c n ((T ^ m) s) := by
  unfold ledgerSum
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  rw [pow_add]
  change (T ^ m * T ^ j) s = (T ^ j * T ^ m) s
  exact congrArg (fun p : Perm S => p s) ((Commute.refl T).pow_pow m j).eq

theorem pow_mul_period_apply (T : Perm S) {P : ℕ} {s : S}
    (hperiod : (T ^ P) s = s) (k : ℕ) :
    (T ^ (k * P)) s = s := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, pow_add]
      change (T ^ (k * P)) ((T ^ P) s) = s
      rw [hperiod, ih]

theorem ledgerSum_mul_period (T : Perm S) (c : S → L) {P : ℕ} {s : S}
    (hperiod : (T ^ P) s = s) (k : ℕ) :
    ledgerSum T c (k * P) s = k • ledgerSum T c P s := by
  induction k with
  | zero => simp [ledgerSum]
  | succ k ih =>
      rw [Nat.succ_mul, ledgerSum_add, ih, pow_mul_period_apply T hperiod]
      simp [succ_nsmul, add_comm]

theorem pow_mul_order_apply (T : Perm S) (k : ℕ) (s : S) :
    (T ^ (k * orderOf T)) s = s := by
  rw [mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  rfl

theorem ledgerSum_mul_order (T : Perm S) (c : S → L) (k : ℕ) (s : S) :
    ledgerSum T c (k * orderOf T) s = k • orderHolonomy T c s := by
  induction k with
  | zero => simp [ledgerSum]
  | succ k ih =>
      rw [Nat.succ_mul, ledgerSum_add, ih, pow_mul_order_apply]
      simp [orderHolonomy, add_nsmul]

theorem ledgerSum_mul_order_add (T : Perm S) (c : S → L) (k r : ℕ) (s : S) :
    ledgerSum T c (k * orderOf T + r) s =
      k • orderHolonomy T c s + ledgerSum T c r s := by
  rw [ledgerSum_add, ledgerSum_mul_order, pow_mul_order_apply]

theorem ledgerWork_nsmul (Q : LedgerMetric L) (k : ℕ) (x : L) :
    ledgerWork Q (k • x) = (k : ℝ) ^ 2 * ledgerWork Q x := by
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  unfold ledgerWork
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp
  ring

theorem recurrent_periodic_quadratic_work (T : Perm S) (c : S → L)
    (Q : LedgerMetric L) {P : ℕ} {s : S} (hperiod : (T ^ P) s = s) (k : ℕ) :
    ledgerWork Q (ledgerSum T c (k * P) s) =
      (k : ℝ) ^ 2 * ledgerWork Q (ledgerSum T c P s) := by
  rw [ledgerSum_mul_period T c hperiod, ledgerWork_nsmul]

theorem recurrent_quadratic_work (T : Perm S) (c : S → L)
    (Q : LedgerMetric L) (k : ℕ) (s : S) :
    ledgerWork Q (ledgerSum T c (k * orderOf T) s) =
      (k : ℝ) ^ 2 * ledgerWork Q (orderHolonomy T c s) := by
  rw [ledgerSum_mul_order, ledgerWork_nsmul]

def LedgerHistoriesBounded (T : Perm S) (c : S → L) : Prop :=
  ∀ s, ∃ B : ℝ, ∀ n, ‖ledgerSum T c n s‖ ≤ B

theorem ledgerHistoriesBounded_iff_zeroHolonomy (T : Perm S) (c : S → L) :
    LedgerHistoriesBounded T c ↔ orderHolonomy T c = 0 := by
  constructor
  · intro hb
    funext s
    by_contra hhol
    obtain ⟨B, hB⟩ := hb s
    have hnorm : 0 < ‖orderHolonomy T c s‖ := norm_pos_iff.mpr hhol
    obtain ⟨k, hk⟩ := exists_nat_gt (B / ‖orderHolonomy T c s‖)
    have hk' : B < (k : ℝ) * ‖orderHolonomy T c s‖ := by
      apply (div_lt_iff₀ hnorm).mp
      simpa [mul_comm] using hk
    have hbound := hB (k * orderOf T)
    rw [ledgerSum_mul_order] at hbound
    have hnormsmul : ‖k • orderHolonomy T c s‖ =
        (k : ℝ) * ‖orderHolonomy T c s‖ := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul]
      simp
    rw [hnormsmul] at hbound
    exact (not_lt_of_ge hbound) hk'
  · intro hzero s
    let P := orderOf T
    have hP : 0 < P := orderOf_pos T
    refine ⟨∑ r ∈ Finset.range P, ‖ledgerSum T c r s‖, ?_⟩
    intro n
    have hn : n = (n / P) * P + n % P := by
      simpa [mul_comm] using (Nat.div_add_mod n P).symm
    rw [hn, ledgerSum_mul_order_add]
    have hhol : orderHolonomy T c s = 0 := congr_fun hzero s
    rw [hhol]
    simp only [nsmul_zero, zero_add]
    exact Finset.single_le_sum
      (s := Finset.range P) (f := fun r => ‖ledgerSum T c r s‖)
      (fun r hr => norm_nonneg (ledgerSum T c r s))
      (Finset.mem_range.mpr (Nat.mod_lt n hP))

theorem bounded_history_classification (T : Perm S) (c : S → L)
    (Q : LedgerMetric L) :
    LedgerHistoriesBounded T c ↔
      (∃ h : S → L, c = fun s => h (T s) - h s) ∧
        ledgerEnergy Q (harmonicLedger T c) = 0 := by
  rw [ledgerHistoriesBounded_iff_zeroHolonomy,
    ← finite_livsic_coboundary_iff]
  constructor
  · intro hcob
    refine ⟨hcob, ?_⟩
    obtain ⟨h, hh⟩ := hcob
    have hzero : orderHolonomy T c = 0 :=
      (finite_livsic_coboundary_iff T c).mp ⟨h, hh⟩
    simp [ledgerEnergy, harmonicLedger, hzero, ledgerWork]
  · exact fun h => h.1

def ledgerSkewLift (T : Perm S) (c : S → L) : S × L → S × L :=
  fun z => (T z.1, z.2 + c z.1)

def ledgerTranslation (h : S → L) : S × L → S × L :=
  fun z => (z.1, z.2 + h z.1)

theorem ledgerTranslation_conjugates_skewLift (T : Perm S) (c h : S → L) :
    ledgerTranslation h ∘ ledgerSkewLift T c ∘ ledgerTranslation (fun s => -h s) =
      ledgerSkewLift T (ledgerGauge T c h) := by
  funext z
  apply Prod.ext
  · simp [Function.comp_def, ledgerTranslation, ledgerSkewLift, ledgerGauge]
  · simp [Function.comp_def, ledgerTranslation, ledgerSkewLift, ledgerGauge]
    abel

theorem skewLift_conjugate_iff_orderHolonomy (T : Perm S) (c d : S → L) :
    (∃ h : S → L,
      ledgerTranslation h ∘ ledgerSkewLift T c ∘ ledgerTranslation (fun s => -h s) =
        ledgerSkewLift T d) ↔
      orderHolonomy T d = orderHolonomy T c := by
  rw [← finite_livsic_orderHolonomy_iff T c d]
  constructor
  · rintro ⟨h, hconj⟩
    refine ⟨h, ?_⟩
    rw [ledgerTranslation_conjugates_skewLift] at hconj
    funext s
    have hs := congr_fun hconj (s, 0)
    have hsnd := congrArg Prod.snd hs
    simpa [ledgerSkewLift] using hsnd.symm
  · rintro ⟨h, rfl⟩
    exact ⟨h, ledgerTranslation_conjugates_skewLift T c h⟩

theorem ledgerWork_smul (Q : LedgerMetric L) (a : ℝ) (x : L) :
    ledgerWork Q (a • x) = a ^ 2 * ledgerWork Q x := by
  unfold ledgerWork
  rw [map_smul, inner_smul_left, inner_smul_right]
  simp
  ring

def finiteMean {I : Type*} [Fintype I] (f : I → L) : L :=
  ((Fintype.card I : ℝ)⁻¹) • ∑ i, f i

theorem sum_sub_finiteMean_eq_zero {I : Type*} [Fintype I] [Nonempty I]
    (f : I → L) : ∑ i, (f i - finiteMean f) = 0 := by
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_univ]
  unfold finiteMean
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hcard : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [hcard]

theorem finite_hodge_work_identity {I : Type*} [Fintype I] [Nonempty I]
    (Q : LedgerMetric L) (f : I → L) :
    ∑ i, ledgerWork Q (f i) =
      (Fintype.card I : ℝ) * ledgerWork Q (finiteMean f) +
        ∑ i, ledgerWork Q (f i - finiteMean f) := by
  have hdev := sum_sub_finiteMean_eq_zero f
  rw [show (∑ i, ledgerWork Q (f i)) =
      ∑ i, (ledgerWork Q (finiteMean f) +
        ledgerWork Q (f i - finiteMean f) +
          2 * inner ℝ (Q.op (finiteMean f)) (f i - finiteMean f)) by
    apply Finset.sum_congr rfl
    intro i hi
    exact ledgerWork_mean_deviation Q (finiteMean f) (f i)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [← Finset.mul_sum]
  rw [← inner_sum]
  rw [hdev]
  simp

theorem finite_hodge_work_lower_bound {I : Type*} [Fintype I] [Nonempty I]
    (Q : LedgerMetric L) (f : I → L) :
    (Fintype.card I : ℝ) * ledgerWork Q (finiteMean f) ≤
      ∑ i, ledgerWork Q (f i) := by
  rw [finite_hodge_work_identity]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i hi => ledgerWork_nonneg Q _)

theorem finite_hodge_work_eq_iff {I : Type*} [Fintype I] [Nonempty I]
    (Q : LedgerMetric L) (f : I → L) :
    (∑ i, ledgerWork Q (f i) =
      (Fintype.card I : ℝ) * ledgerWork Q (finiteMean f)) ↔
      ∀ i, f i = finiteMean f := by
  rw [finite_hodge_work_identity]
  constructor
  · intro h i
    have hsum : ∑ i, ledgerWork Q (f i - finiteMean f) = 0 := by linarith
    have hterm : ledgerWork Q (f i - finiteMean f) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => ledgerWork_nonneg Q _)).mp hsum i
        (Finset.mem_univ i)
    exact sub_eq_zero.mp ((ledgerWork_eq_zero_iff Q _).mp hterm)
  · intro h
    have hdev0 : ∀ i, f i - finiteMean f = 0 := fun i => sub_eq_zero.mpr (h i)
    have hzero : ledgerWork Q 0 = 0 := by simp [ledgerWork]
    simp [hdev0, hzero]

theorem periodicOrbit_hodge_work_identity {P : ℕ} (hP : 0 < P)
    (T : Perm S) (Q : LedgerMetric L) (c d : S → L) (s : S)
    (_hperiod : (T ^ P) s = s)
    (hhol : ledgerSum T d P s = ledgerSum T c P s) :
    (∑ j ∈ Finset.range P, ledgerWork Q (d ((T ^ j) s))) =
      (P : ℝ)⁻¹ * ledgerWork Q (ledgerSum T c P s) +
        ∑ j ∈ Finset.range P,
          ledgerWork Q (d ((T ^ j) s) -
            (P : ℝ)⁻¹ • ledgerSum T c P s) := by
  letI : Nonempty (Fin P) := ⟨⟨0, hP⟩⟩
  let f : Fin P → L := fun j => d ((T ^ (j : ℕ)) s)
  have hsum : ∑ j, f j = ledgerSum T c P s := by
    calc
      ∑ j, f j = ∑ j ∈ Finset.range P, d ((T ^ j) s) := by
        simpa [f] using Fin.sum_univ_eq_sum_range
          (fun j : ℕ => d ((T ^ j) s)) P
      _ = ledgerSum T c P s := by simpa [ledgerSum] using hhol
  have hmean : finiteMean f = (P : ℝ)⁻¹ • ledgerSum T c P s := by
    unfold finiteMean
    rw [Fintype.card_fin, hsum]
  have hid := finite_hodge_work_identity Q f
  rw [hmean] at hid
  have hP0 : (P : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hP.ne'
  have hbase : (P : ℝ) * ledgerWork Q ((P : ℝ)⁻¹ • ledgerSum T c P s) =
      (P : ℝ)⁻¹ * ledgerWork Q (ledgerSum T c P s) := by
    rw [ledgerWork_smul]
    field_simp [hP0]
  rw [Fintype.card_fin, hbase] at hid
  have hleft : (∑ j : Fin P, ledgerWork Q (f j)) =
      ∑ j ∈ Finset.range P, ledgerWork Q (d ((T ^ j) s)) := by
    simpa [f] using Fin.sum_univ_eq_sum_range
      (fun j : ℕ => ledgerWork Q (d ((T ^ j) s))) P
  have hdev :
      (∑ j : Fin P, ledgerWork Q
        (f j - (P : ℝ)⁻¹ • ledgerSum T c P s)) =
      ∑ j ∈ Finset.range P, ledgerWork Q
        (d ((T ^ j) s) - (P : ℝ)⁻¹ • ledgerSum T c P s) := by
    simpa [f] using Fin.sum_univ_eq_sum_range
      (fun j : ℕ => ledgerWork Q
        (d ((T ^ j) s) - (P : ℝ)⁻¹ • ledgerSum T c P s)) P
  rw [hleft, hdev] at hid
  exact hid

theorem periodicOrbit_hodge_work_lower_bound {P : ℕ} (hP : 0 < P)
    (T : Perm S) (Q : LedgerMetric L) (c d : S → L) (s : S)
    (hperiod : (T ^ P) s = s)
    (hhol : ledgerSum T d P s = ledgerSum T c P s) :
    (P : ℝ)⁻¹ * ledgerWork Q (ledgerSum T c P s) ≤
      ∑ j ∈ Finset.range P, ledgerWork Q (d ((T ^ j) s)) := by
  rw [periodicOrbit_hodge_work_identity hP T Q c d s hperiod hhol]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun j hj => ledgerWork_nonneg Q _)

theorem periodicOrbit_hodge_work_eq_iff {P : ℕ} (hP : 0 < P)
    (T : Perm S) (Q : LedgerMetric L) (c d : S → L) (s : S)
    (hperiod : (T ^ P) s = s)
    (hhol : ledgerSum T d P s = ledgerSum T c P s) :
    ((∑ j ∈ Finset.range P, ledgerWork Q (d ((T ^ j) s))) =
      (P : ℝ)⁻¹ * ledgerWork Q (ledgerSum T c P s)) ↔
      ∀ j < P, d ((T ^ j) s) = (P : ℝ)⁻¹ • ledgerSum T c P s := by
  rw [periodicOrbit_hodge_work_identity hP T Q c d s hperiod hhol]
  constructor
  · intro h j hj
    have hsum : (∑ i ∈ Finset.range P,
        ledgerWork Q (d ((T ^ i) s) -
          (P : ℝ)⁻¹ • ledgerSum T c P s)) = 0 := by
      linarith
    have hterm : ledgerWork Q (d ((T ^ j) s) -
        (P : ℝ)⁻¹ • ledgerSum T c P s) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i hi => ledgerWork_nonneg Q _)).mp hsum j (Finset.mem_range.mpr hj)
    exact sub_eq_zero.mp ((ledgerWork_eq_zero_iff Q _).mp hterm)
  · intro h
    have hzero : (∑ j ∈ Finset.range P,
        ledgerWork Q (d ((T ^ j) s) -
          (P : ℝ)⁻¹ • ledgerSum T c P s)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [h j (Finset.mem_range.mp hj)]
      simp [ledgerWork]
    rw [hzero, add_zero]

theorem sandpile_local_cumulative_work_identity {P : ℕ} (hP : 0 < P)
    (Q : LedgerMetric L) (c : Fin P → L) (g : L)
    (hsum : ∑ j, c j = P • g) :
    ∑ j, ledgerWork Q (c j) =
      (P : ℝ) * ledgerWork Q g + ∑ j, ledgerWork Q (c j - g) := by
  letI : Nonempty (Fin P) := ⟨⟨0, hP⟩⟩
  have hP0 : (P : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hP.ne'
  have hmean : finiteMean c = g := by
    unfold finiteMean
    rw [Fintype.card_fin, hsum, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp [hP0]
  simpa [hmean] using finite_hodge_work_identity Q c

theorem sandpile_local_work_lower_bound {P : ℕ} (hP : 0 < P)
    (Q : LedgerMetric L) (c : Fin P → L) (g : L)
    (hsum : ∑ j, c j = P • g) :
    (P : ℝ) * ledgerWork Q g ≤ ∑ j, ledgerWork Q (c j) := by
  rw [sandpile_local_cumulative_work_identity hP Q c g hsum]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j hj => ledgerWork_nonneg Q _)

theorem sandpile_cumulative_work_identity {P : ℕ} (hP : 0 < P)
    (Q : LedgerMetric L) (c : Fin P → L) (g : L)
    (hsum : ∑ j, c j = P • g) :
    (P : ℝ) * ledgerWork Q g =
      (P : ℝ)⁻¹ * ledgerWork Q (∑ j, c j) := by
  have hP0 : (P : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hP.ne'
  rw [hsum, ledgerWork_nsmul]
  field_simp

theorem sandpile_local_work_eq_iff {P : ℕ} (hP : 0 < P)
    (Q : LedgerMetric L) (c : Fin P → L) (g : L)
    (hsum : ∑ j, c j = P • g) :
    (∑ j, ledgerWork Q (c j) = (P : ℝ) * ledgerWork Q g) ↔
      ∀ j, c j = g := by
  letI : Nonempty (Fin P) := ⟨⟨0, hP⟩⟩
  have hmean : finiteMean c = g := by
    have hP0 : (P : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hP.ne'
    unfold finiteMean
    rw [Fintype.card_fin, hsum, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp [hP0]
  simpa [hmean] using finite_hodge_work_eq_iff Q c

theorem involutive_two_cycle_minimum_work (Q : LedgerMetric L)
    (x y H : L) (hH : x + y = H) :
    ledgerWork Q x + ledgerWork Q y =
      (2 : ℝ)⁻¹ * ledgerWork Q H +
        ledgerWork Q (x - (2 : ℝ)⁻¹ • H) +
        ledgerWork Q (y - (2 : ℝ)⁻¹ • H) := by
  let c : Bool → L := fun b => if b then y else x
  have hsum : ∑ j, c j = H := by
    simpa [c, add_comm] using hH
  have hmean : finiteMean c = (2 : ℝ)⁻¹ • H := by
    unfold finiteMean
    change (2 : ℝ)⁻¹ • (∑ j, c j) = (2 : ℝ)⁻¹ • H
    rw [hsum]
  have hid := finite_hodge_work_identity Q c
  rw [hmean] at hid
  simp only [Fintype.card_bool, Nat.cast_ofNat] at hid
  have hbase : (2 : ℝ) * ledgerWork Q ((2 : ℝ)⁻¹ • H) =
      (2 : ℝ)⁻¹ * ledgerWork Q H := by
    rw [ledgerWork_smul]
    ring
  rw [hbase] at hid
  simpa [c, add_comm, add_left_comm, add_assoc] using hid

section Signature

variable [MeasurableSpace S]

def recoveryLedgerSignature (μ ν : Measure S) (T : Perm S) (c : S → L) :
    ℝ≥0∞ × (S → L) := (klDiv μ ν, orderHolonomy T c)

theorem recoveryLedgerSignature_eq_iff (μ ν μ' ν' : Measure S)
    (T : Perm S) (c d : S → L) :
    recoveryLedgerSignature μ ν T c = recoveryLedgerSignature μ' ν' T d ↔
      klDiv μ ν = klDiv μ' ν' ∧
        ∃ h : S → L, d = ledgerGauge T c h := by
  rw [Prod.ext_iff]
  simp only [recoveryLedgerSignature]
  rw [finite_livsic_orderHolonomy_iff T c d]
  tauto

end Signature

section Packet

variable [MeasurableSpace S] [MeasurableSingletonClass S]
  {H : Type*} [MeasurableSpace H] [MeasurableSpace L]

noncomputable def recoveryLedgerConditional (κ : Kernel S H)
    (T : Perm S) (c : S → L) (n : ℕ) : Kernel S (H × L) :=
  Kernel.comap κ (fun s => (T ^ n) s) (measurable_of_finite _) ×ₖ
    Kernel.deterministic (ledgerSum T c n) (measurable_of_finite _)

noncomputable def endpointPacketMeasurableEquiv (T : Perm S) (n : ℕ) :
    S × (H × L) ≃ᵐ S × (H × L) where
  toEquiv := Equiv.prodCongr (T ^ n) (Equiv.refl _)
  measurable_toFun := by
    change Measurable (fun z : S × (H × L) => ((T ^ n) z.1, z.2))
    exact (measurable_of_finite (fun s : S => (T ^ n) s)).comp measurable_fst |>.prodMk
      measurable_snd
  measurable_invFun := by
    change Measurable (fun z : S × (H × L) => ((T ^ n).symm z.1, z.2))
    exact (measurable_of_finite (fun s : S => (T ^ n).symm s)).comp measurable_fst |>.prodMk
      measurable_snd

noncomputable def recoveryCocyclePacket (μ : Measure S) (κ : Kernel S H)
    (T : Perm S) (c : S → L) (n : ℕ) : Measure (S × (H × L)) :=
  (splitFormation μ (recoveryLedgerConditional κ T c n)).map
    (endpointPacketMeasurableEquiv (H := H) (L := L) T n)

def recoveryInitialObserver (T : Perm S) (n : ℕ) : S × (H × L) → S :=
  fun z => (T ^ n).symm z.1

theorem recoveryCocyclePacket_recovers_observer
    (μ : Measure S) [IsFiniteMeasure μ]
    (κ : Kernel S H) [IsMarkovKernel κ]
    (T : Perm S) (c : S → L) (n : ℕ) :
    (recoveryCocyclePacket μ κ T c n).map
        (recoveryInitialObserver (H := H) (L := L) T n) = μ := by
  let η := recoveryLedgerConditional κ T c n
  haveI : IsMarkovKernel η := by
    dsimp [η, recoveryLedgerConditional]
    infer_instance
  have hrecover := splitFormation_recovers_observer μ η
  rw [Measure.fst] at hrecover
  unfold recoveryCocyclePacket recoveryInitialObserver
  rw [Measure.map_map]
  · simpa [endpointPacketMeasurableEquiv, Function.comp_def] using hrecover
  · exact (measurable_of_finite (fun s : S => (T ^ n).symm s)).comp measurable_fst
  · exact (endpointPacketMeasurableEquiv (H := H) (L := L) T n).measurable

theorem recoveryCocyclePacket_klDiv
    (μ ν : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel S H) [IsMarkovKernel κ]
    (T : Perm S) (c : S → L) (n : ℕ) :
    klDiv (recoveryCocyclePacket μ κ T c n)
        (recoveryCocyclePacket ν κ T c n) = klDiv μ ν := by
  let η := recoveryLedgerConditional κ T c n
  haveI : IsMarkovKernel η := by
    dsimp [η, recoveryLedgerConditional]
    infer_instance
  haveI : IsFiniteMeasure (splitFormation μ η) :=
    IsFiniteMeasure.mk (by
      rw [splitFormation, Measure.compProd_apply_univ]
      exact measure_lt_top μ Set.univ)
  haveI : IsFiniteMeasure (splitFormation ν η) :=
    IsFiniteMeasure.mk (by
      rw [splitFormation, Measure.compProd_apply_univ]
      exact measure_lt_top ν Set.univ)
  unfold recoveryCocyclePacket
  change klDiv ((splitFormation μ η).map _)
      ((splitFormation ν η).map _) = _
  rw [klDiv_map_measurableEmbedding
    (endpointPacketMeasurableEquiv (H := H) (L := L) T n).measurableEmbedding]
  exact klDiv_splitFormation μ ν η

theorem recoveryCocyclePacket_informationNeutral
    (μ ν : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel S H) [IsMarkovKernel κ]
    (T : Perm S) (c d : S → L) (m n : ℕ) :
    klDiv (recoveryCocyclePacket μ κ T c m)
        (recoveryCocyclePacket ν κ T c m) =
      klDiv (recoveryCocyclePacket μ κ T d n)
        (recoveryCocyclePacket ν κ T d n) := by
  rw [recoveryCocyclePacket_klDiv, recoveryCocyclePacket_klDiv]

end Packet

end

end GaloisForLFunctions.HTGeometry
