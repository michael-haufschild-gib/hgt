import GaloisForLFunctions.RHTower.BlindArchimedeanNodeTwoCertificate

/-!
# The pole-weight window at finite level squeezes to `1`

For a level `L > 0` and a pole weight `β`, `PrimeBlindPositiveAtLevel L β` says that the functional
`A(c) + (β − 1) P(c)` (pole counted `β` times) is nonnegative on every nonnegative blind combination
of tests supported in `[−L, L]`.  The **level window** `levelWindow L` is the set of such `β`.

**Theorems.**
* `levelWindow_antitone`: the windows decrease with the level.
* `isClosed_levelWindow`, `levelWindow_subset_Icc`: each window is a closed interval; for
  `L ≥ 3/10` it lies in an explicit compact interval `[β₋, β₊]` given by the two-bump tests of both
  pole signs (`adjTestFn`), so it is compact.
* `exists_level_not_mem_levelWindow`: every `β ≠ 1` is excluded from all windows beyond some level
  (pole-weight rigidity, `exists_blind_arch_add_mul_pole_neg`).
* `exists_level_forall_abs_sub_one_lt`: **the windows squeeze to `{1}` unconditionally**: for every
  `ε > 0` all windows beyond some level lie in `(1 − ε, 1 + ε)`.
* `riemannHypothesis_iff_forall_level_exists_mem_levelWindow`: **RH holds iff every level window is
  nonempty**, i.e. iff at every finite level some pole weight makes the blind functional
  nonnegative.  The pole weight is free at each level and determined only in the limit.  Under RH
  every window contains `1` (`one_mem_levelWindow_of_riemannHypothesis`).

Proof of the criterion.  The windows at the integer levels form a decreasing sequence of nonempty
compact sets, so their intersection contains some `β`; a `β` in every window is prime-blind
positive at pole weight `β` on all compactly supported tests, hence `β = 1` and RH
(`riemannHypothesis_iff_exists_primeBlindPositiveAt`).  The squeeze is the same compactness
argument applied to the windows intersected with `[1 + ε, β₊]` and `[β₋, 1 − ε]`.
-/

open Finsupp Set Zeta23

namespace RHTower.WeilOneSided

noncomputable section

/-- A Weil test supported in `[−L, L]`. -/
def LevelTest (L : ℝ) (f : WeilTestFn) : Prop := ∀ u, f.1 u ≠ 0 → |u| ≤ L

theorem LevelTest.mono {L L' : ℝ} (h : L ≤ L') {f : WeilTestFn} (hf : LevelTest L f) :
    LevelTest L' f := fun u hu => (hf u hu).trans h

/-- Every Weil test has a level. -/
theorem exists_levelTest (f : WeilTestFn) : ∃ L : ℝ, 0 ≤ L ∧ LevelTest L f := by
  obtain ⟨A, hA⟩ := f.2.2.isCompact.isBounded.subset_closedBall 0
  refine ⟨|A|, abs_nonneg A, fun u hu => ?_⟩
  have := hA (subset_tsupport _ hu)
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  exact this.trans (le_abs_self A)

/-- Every finite combination has a level. -/
theorem exists_level_combination (c : WeilTestFn →₀ ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ f ∈ c.support, LevelTest L f := by
  classical
  choose R hR using exists_levelTest
  refine ⟨∑ f ∈ c.support, R f, Finset.sum_nonneg fun f _ => (hR f).1, fun f hf => ?_⟩
  exact (hR f).2.mono (Finset.single_le_sum (fun g _ => (hR g).1) hf)

/-- The two-bump tests have level `3/10`. -/
theorem levelTest_adjTestFn (σ : ℝ) : LevelTest (3 / 10) (adjTestFn σ) :=
  fun _ hu => adjTest_ne_zero_imp hu

/-- **Prime-blind positivity at pole weight `β` and level `L`**: `A(c) + (β − 1) P(c) ≥ 0` on every
nonnegative blind combination of tests supported in `[−L, L]`. -/
def PrimeBlindPositiveAtLevel (L β : ℝ) : Prop :=
  ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) → (∀ f ∈ c.support, LevelTest L f) → nodeVector c = 0 →
    0 ≤ nodeArchEnergy c + (β - 1) * nodePoleMass c

/-- The level window: the pole weights admissible at level `L`. -/
def levelWindow (L : ℝ) : Set ℝ := {β | PrimeBlindPositiveAtLevel L β}

theorem levelWindow_antitone {L L' : ℝ} (h : L ≤ L') : levelWindow L' ⊆ levelWindow L :=
  fun _ hβ c hc hL hv => hβ c hc (fun f hf => (hL f hf).mono h) hv

/-- The windows are intervals. -/
theorem levelWindow_mem_Icc {L β₁ β₂ β : ℝ} (h₁ : β₁ ∈ levelWindow L) (h₂ : β₂ ∈ levelWindow L)
    (hβ : β ∈ Icc β₁ β₂) : β ∈ levelWindow L := by
  intro c hc hL hv
  have a₁ := h₁ c hc hL hv
  have a₂ := h₂ c hc hL hv
  rcases le_total 0 (nodePoleMass c) with hP | hP
  · nlinarith [hβ.1]
  · nlinarith [hβ.2]

/-- The windows are closed. -/
theorem isClosed_levelWindow (L : ℝ) : IsClosed (levelWindow L) := by
  have e : levelWindow L = ⋂ c : {c : WeilTestFn →₀ ℝ //
      (∀ f, 0 ≤ c f) ∧ (∀ f ∈ c.support, LevelTest L f) ∧ nodeVector c = 0},
      {β : ℝ | 0 ≤ nodeArchEnergy c.1 + (β - 1) * nodePoleMass c.1} := by
    ext β
    simp only [levelWindow, PrimeBlindPositiveAtLevel, Set.mem_setOf_eq, Set.mem_iInter,
      Subtype.forall]
    constructor
    · intro h c hc; exact h c hc.1 hc.2.1 hc.2.2
    · intro h c hc hL hv; exact h c ⟨hc, hL, hv⟩
  rw [e]
  exact isClosed_iInter fun c => isClosed_le continuous_const (by fun_prop)

/-- Under RH every window contains `1`. -/
theorem one_mem_levelWindow_of_riemannHypothesis (hRH : RiemannHypothesis) (L : ℝ) :
    (1 : ℝ) ∈ levelWindow L := by
  intro c hc _ hv
  rw [sub_self, zero_mul, add_zero]
  have h := riemannHypothesis_iff_primeBlindPositive_unconditional.mp hRH c hc fun n hn => by
    have := congrArg (fun w : LogIndex →₀ ℝ => w ⟨n, hn⟩) hv
    simpa [nodeVector_eq, linearCombination_logVector_apply] using this
  rwa [sum_weilArchRe_eq, ← nodeArchEnergy_eq] at h

/-- A pole weight admissible at every level is admissible on all compactly supported tests. -/
theorem primeBlindPositiveAt_of_forall_level {β : ℝ} (h : ∀ n : ℕ, β ∈ levelWindow (n + 1)) :
    RHTower.PrimeBlindPositiveAt β := by
  intro c hc hnull
  obtain ⟨L, hL0, hL⟩ := exists_level_combination c
  have hv : nodeVector c = 0 := linearCombination_logVector_eq_zero hnull
  have hb := h ⌈L⌉₊ c hc (fun f hf => (hL f hf).mono (by
    have := Nat.le_ceil L
    linarith)) hv
  rw [RHTower.sum_poleWeightArchRe, sum_weilArchRe_eq, ← nodeArchEnergy_eq, ← nodePoleMass_eq_sum]
  exact hb

/-- **Every pole weight other than `1` is eventually excluded.** -/
theorem exists_level_not_mem_levelWindow {β : ℝ} (hβ : β ≠ 1) :
    ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → β ∉ levelWindow L := by
  obtain ⟨c, hc, hnull, hneg⟩ := RHTower.exists_blind_arch_add_mul_pole_neg (ε := β - 1)
    (sub_ne_zero.mpr hβ)
  obtain ⟨L₀, -, hL₀⟩ := exists_level_combination c
  refine ⟨L₀, fun L hL hmem => ?_⟩
  have hv : nodeVector c = 0 := linearCombination_logVector_eq_zero hnull
  have h := hmem c hc (fun f hf => (hL₀ f hf).mono hL) hv
  rw [sum_weilArchRe_eq, ← nodeArchEnergy_eq, ← nodePoleMass_eq_sum] at hneg
  linarith

/-! ## Compactness: the windows are bounded from level `3/10` on -/

/-- The lower end `1 − A(adj₊)/P(adj₊)` from the even two-bump test. -/
def windowLower : ℝ :=
  1 - nodeArchEnergy (Finsupp.single (adjTestFn 1) 1) /
    nodePoleMass (Finsupp.single (adjTestFn 1) 1)

/-- The upper end `1 − A(adj₋)/P(adj₋)` from the odd two-bump test. -/
def windowUpper : ℝ :=
  1 - nodeArchEnergy (Finsupp.single (adjTestFn (-1)) 1) /
    nodePoleMass (Finsupp.single (adjTestFn (-1)) 1)

theorem single_adjTestFn_nonneg (σ : ℝ) (f : WeilTestFn) : 0 ≤ Finsupp.single (adjTestFn σ) (1 : ℝ) f := by
  classical
  rw [Finsupp.single_apply]; split_ifs <;> norm_num

theorem support_single_adjTestFn_level {L : ℝ} (hL : 3 / 10 ≤ L) (σ : ℝ) :
    ∀ f ∈ (Finsupp.single (adjTestFn σ) (1 : ℝ)).support, LevelTest L f := by
  classical
  intro f hf
  rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hf
  split_ifs at hf with h
  · rw [← h]; exact (levelTest_adjTestFn σ).mono hL
  · exact absurd rfl hf

theorem nodePoleMass_single_adjTestFn_one_pos : 0 < nodePoleMass (Finsupp.single (adjTestFn 1) 1) := by
  rw [nodePoleMass_single, one_mul]; exact pole_adjTestFn_one_pos

theorem nodePoleMass_single_adjTestFn_neg_one_neg :
    nodePoleMass (Finsupp.single (adjTestFn (-1)) 1) < 0 := by
  rw [nodePoleMass_single, one_mul]; exact pole_adjTestFn_neg_one_neg

/-- From level `3/10` on, the window lies in `[windowLower, windowUpper]`. -/
theorem levelWindow_subset_Icc {L : ℝ} (hL : 3 / 10 ≤ L) :
    levelWindow L ⊆ Icc windowLower windowUpper := by
  intro β hβ
  have hpos := hβ (Finsupp.single (adjTestFn 1) 1) (single_adjTestFn_nonneg 1)
    (support_single_adjTestFn_level hL 1) (nodeVector_adjTestFn_single 1 1)
  have hneg := hβ (Finsupp.single (adjTestFn (-1)) 1) (single_adjTestFn_nonneg (-1))
    (support_single_adjTestFn_level hL (-1)) (nodeVector_adjTestFn_single (-1) 1)
  have hPpos := nodePoleMass_single_adjTestFn_one_pos
  have hPneg := nodePoleMass_single_adjTestFn_neg_one_neg
  constructor
  · have h1 : 1 - β ≤ nodeArchEnergy (Finsupp.single (adjTestFn 1) 1) /
        nodePoleMass (Finsupp.single (adjTestFn 1) 1) := by
      rw [le_div_iff₀ hPpos]; linarith
    unfold windowLower; linarith
  · have h2 : β - 1 ≤ -nodeArchEnergy (Finsupp.single (adjTestFn (-1)) 1) /
        nodePoleMass (Finsupp.single (adjTestFn (-1)) 1) := by
      rw [le_div_iff_of_neg hPneg]; linarith
    rw [neg_div] at h2
    unfold windowUpper; linarith

theorem isCompact_levelWindow {L : ℝ} (hL : 3 / 10 ≤ L) : IsCompact (levelWindow L) :=
  isCompact_Icc.of_isClosed_subset (isClosed_levelWindow L) (levelWindow_subset_Icc hL)

/-! ## The squeeze and the RH criterion -/

/-- A pole weight lying in a closed band and in every integer-level window forces `β = 1` and RH;
hence, if the band avoids `1`, some integer-level window misses the band. -/
theorem exists_nat_levelWindow_inter_eq_empty {a b : ℝ} (hab : (1 : ℝ) ∉ Icc a b) :
    ∃ n : ℕ, levelWindow (n + 1) ∩ Icc a b = ∅ := by
  by_contra hne
  have hne' : ∀ n : ℕ, (levelWindow (n + 1) ∩ Icc a b).Nonempty := fun n =>
    Set.nonempty_iff_ne_empty.mpr fun h => hne ⟨n, h⟩
  have hsub : ∀ n : ℕ, levelWindow (((n + 1 : ℕ) : ℝ) + 1) ∩ Icc a b ⊆
      levelWindow (n + 1) ∩ Icc a b :=
    fun n => Set.inter_subset_inter_left _ (levelWindow_antitone (by push_cast; linarith))
  have hcl : ∀ n : ℕ, IsClosed (levelWindow (n + 1) ∩ Icc a b) :=
    fun n => (isClosed_levelWindow _).inter isClosed_Icc
  have hcpt : IsCompact (levelWindow ((0 : ℕ) + 1) ∩ Icc a b) :=
    (isCompact_levelWindow (by norm_num)).inter_right isClosed_Icc
  obtain ⟨β, hβ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n : ℕ => levelWindow (n + 1) ∩ Icc a b) hsub hne' hcpt hcl
  rw [Set.mem_iInter] at hβ
  have hall : ∀ n : ℕ, β ∈ levelWindow (n + 1) := fun n => (hβ n).1
  have hβ1 : β = 1 := RHTower.eq_one_of_primeBlindPositiveAt (primeBlindPositiveAt_of_forall_level hall)
  exact hab (hβ1 ▸ (hβ 0).2)

/-- **The windows squeeze to `{1}`, unconditionally.**  For every `ε > 0` there is a level beyond
which every admissible pole weight satisfies `|β − 1| < ε`. -/
theorem exists_level_forall_abs_sub_one_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → ∀ β ∈ levelWindow L, |β - 1| < ε := by
  obtain ⟨n₁, hn₁⟩ := exists_nat_levelWindow_inter_eq_empty (a := 1 + ε) (b := windowUpper)
    (fun h => by linarith [h.1])
  obtain ⟨n₂, hn₂⟩ := exists_nat_levelWindow_inter_eq_empty (a := windowLower) (b := 1 - ε)
    (fun h => by linarith [h.2])
  refine ⟨max ((n₁ : ℝ) + 1) ((n₂ : ℝ) + 1), fun L hL β hβ => ?_⟩
  have hL3 : 3 / 10 ≤ L := by
    have : (0 : ℝ) ≤ n₁ := Nat.cast_nonneg n₁
    linarith [le_max_left ((n₁ : ℝ) + 1) ((n₂ : ℝ) + 1)]
  have hbox := levelWindow_subset_Icc hL3 hβ
  have hβ₁ : β ∈ levelWindow (n₁ + 1) :=
    levelWindow_antitone (le_trans (le_max_left _ _) hL) hβ
  have hβ₂ : β ∈ levelWindow (n₂ + 1) :=
    levelWindow_antitone (le_trans (le_max_right _ _) hL) hβ
  rw [abs_sub_lt_iff]
  constructor
  · by_contra h
    rw [not_lt] at h
    have : β ∈ levelWindow (n₁ + 1) ∩ Icc (1 + ε) windowUpper :=
      ⟨hβ₁, by linarith, hbox.2⟩
    rw [hn₁] at this
    exact this
  · by_contra h
    rw [not_lt] at h
    have : β ∈ levelWindow (n₂ + 1) ∩ Icc windowLower (1 - ε) :=
      ⟨hβ₂, hbox.1, by linarith⟩
    rw [hn₂] at this
    exact this

/-- **RH is the nonemptiness of every level window.**  RH holds iff at every finite level some pole
weight makes the blind functional nonnegative. -/
theorem riemannHypothesis_iff_forall_level_exists_mem_levelWindow :
    RiemannHypothesis ↔ ∀ L : ℝ, ∃ β : ℝ, β ∈ levelWindow L := by
  constructor
  · intro hRH L
    exact ⟨1, one_mem_levelWindow_of_riemannHypothesis hRH L⟩
  · intro h
    have hne : ∀ n : ℕ, (levelWindow (n + 1)).Nonempty := fun n => h _
    have hsub : ∀ n : ℕ, levelWindow (((n + 1 : ℕ) : ℝ) + 1) ⊆ levelWindow (n + 1) :=
      fun n => levelWindow_antitone (by push_cast; linarith)
    have hcpt : IsCompact (levelWindow ((0 : ℕ) + 1)) := isCompact_levelWindow (by norm_num)
    obtain ⟨β, hβ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n : ℕ => levelWindow (n + 1)) hsub hne hcpt (fun n => isClosed_levelWindow _)
    rw [Set.mem_iInter] at hβ
    exact RHTower.riemannHypothesis_iff_exists_primeBlindPositiveAt.mpr
      ⟨β, primeBlindPositiveAt_of_forall_level hβ⟩

/-- RH holds iff `1` lies in every level window. -/
theorem riemannHypothesis_iff_forall_one_mem_levelWindow :
    RiemannHypothesis ↔ ∀ L : ℝ, (1 : ℝ) ∈ levelWindow L :=
  ⟨fun h L => one_mem_levelWindow_of_riemannHypothesis h L, fun h =>
    riemannHypothesis_iff_forall_level_exists_mem_levelWindow.mpr fun L => ⟨1, h L⟩⟩

end

end RHTower.WeilOneSided

namespace RHTower.WeilOneSided

noncomputable section

/-- **RH as a determinant inequality between pole-positive and pole-negative blind combinations.**
Write `arch(c) = A(c) − P(c)` for the symbol integral.  RH holds iff for all nonnegative blind
combinations `c₁` with `P(c₁) > 0` and `c₂` with `P(c₂) < 0`,
`arch(c₁) P(c₂) ≤ arch(c₂) P(c₁)`.  In terms of the pole weight `q(c) = −arch(c)/P(c)` that would
make `c` null, this says that the weight demanded by every pole-positive combination is at most
the weight allowed by every pole-negative one; under RH both sandwich `1`.  No pole weight appears
in the statement. -/
theorem riemannHypothesis_iff_forall_blind_det_nonpos :
    RiemannHypothesis ↔
      ∀ c₁ c₂ : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c₁ f) → (∀ f, 0 ≤ c₂ f) →
        nodeVector c₁ = 0 → nodeVector c₂ = 0 → 0 < nodePoleMass c₁ → nodePoleMass c₂ < 0 →
        nodeArchOnly c₁ * nodePoleMass c₂ ≤ nodeArchOnly c₂ * nodePoleMass c₁ := by
  constructor
  · intro hRH c₁ c₂ hc₁ hc₂ hv₁ hv₂ hP₁ hP₂
    have hA : ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) → nodeVector c = 0 → 0 ≤ nodeArchEnergy c := by
      intro c hc hv
      have h := riemannHypothesis_iff_primeBlindPositive_unconditional.mp hRH c hc fun n hn => by
        have := congrArg (fun w : LogIndex →₀ ℝ => w ⟨n, hn⟩) hv
        simpa [nodeVector_eq, linearCombination_logVector_apply] using this
      rwa [sum_weilArchRe_eq, ← nodeArchEnergy_eq] at h
    have h₁ := hA c₁ hc₁ hv₁
    have h₂ := hA c₂ hc₂ hv₂
    rw [nodeArchOnly, nodeArchOnly]
    nlinarith
  · intro h
    refine riemannHypothesis_iff_zeroPoleBlindPositive.mpr fun c hc hv hp => ?_
    by_contra hneg
    rw [not_le] at hneg
    set aP := nodeArchOnly (Finsupp.single (adjTestFn 1) 1) with haP
    set aM := nodeArchOnly (Finsupp.single (adjTestFn (-1)) 1) with haM
    set PP := nodePoleMass (Finsupp.single (adjTestFn 1) 1) with hPP
    set PM := nodePoleMass (Finsupp.single (adjTestFn (-1)) 1) with hPM
    have hPP0 : 0 < PP := nodePoleMass_single_adjTestFn_one_pos
    have hPM0 : PM < 0 := nodePoleMass_single_adjTestFn_neg_one_neg
    have harch : nodeArchOnly c < 0 := by rw [nodeArchOnly, hp, sub_zero]; exact hneg
    -- for every `s > 0`, the pair `c + s adj₊`, `adj₋` satisfies the determinant inequality
    have key : ∀ s : ℝ, 0 < s →
        (nodeArchOnly c + s * aP) * PM ≤ aM * (s * PP) := by
      intro s hs
      have := h (c + s • Finsupp.single (adjTestFn 1) 1) (Finsupp.single (adjTestFn (-1)) 1)
        (fun f => by
          rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
          exact add_nonneg (hc f) (mul_nonneg hs.le (single_adjTestFn_nonneg 1 f)))
        (single_adjTestFn_nonneg (-1))
        (by rw [nodeVector_add, nodeVector_smul, hv, nodeVector_adjTestFn_single, smul_zero,
          add_zero])
        (nodeVector_adjTestFn_single (-1) 1)
        (by rw [nodePoleMass_add, nodePoleMass_smul, hp, zero_add]; exact mul_pos hs hPP0)
        hPM0
      rwa [nodeArchOnly_add, nodeArchOnly_smul, nodePoleMass_add, nodePoleMass_smul, hp,
        zero_add] at this
    have hpos : 0 < nodeArchOnly c * PM := mul_pos_of_neg_of_neg harch hPM0
    set K := aM * PP - aP * PM with hK
    have key' : ∀ s : ℝ, 0 < s → nodeArchOnly c * PM ≤ s * K := fun s hs => by
      have := key s hs
      rw [hK]
      nlinarith
    rcases le_or_gt K 0 with hK0 | hK0
    · have := key' 1 one_pos
      nlinarith
    · have hs : 0 < nodeArchOnly c * PM / (2 * K) := by positivity
      have := key' _ hs
      have e : nodeArchOnly c * PM / (2 * K) * K = nodeArchOnly c * PM / 2 := by
        field_simp
      rw [e] at this
      linarith

end

end RHTower.WeilOneSided

namespace RHTower.WeilOneSided

noncomputable section

/-- **Nonemptiness of a level window is two finite-level inequalities.**  For `L ≥ 3/10`, the window
at level `L` is nonempty iff (i) every level-`L` blind combination of pole mass zero has nonnegative
energy, and (ii) for all level-`L` blind `c₁`, `c₂` with `P(c₁) > 0 > P(c₂)`,
`arch(c₁) P(c₂) ≤ arch(c₂) P(c₁)`.  The admissible pole weight is then any number between the
largest weight demanded by a pole-positive combination and the smallest weight allowed by a
pole-negative one. -/
theorem levelWindow_nonempty_iff {L : ℝ} (hL : 3 / 10 ≤ L) :
    (levelWindow L).Nonempty ↔
      (∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) → (∀ f ∈ c.support, LevelTest L f) →
          nodeVector c = 0 → nodePoleMass c = 0 → 0 ≤ nodeArchEnergy c) ∧
        (∀ c₁ c₂ : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c₁ f) → (∀ f, 0 ≤ c₂ f) →
          (∀ f ∈ c₁.support, LevelTest L f) → (∀ f ∈ c₂.support, LevelTest L f) →
          nodeVector c₁ = 0 → nodeVector c₂ = 0 → 0 < nodePoleMass c₁ → nodePoleMass c₂ < 0 →
          nodeArchOnly c₁ * nodePoleMass c₂ ≤ nodeArchOnly c₂ * nodePoleMass c₁) := by
  constructor
  · rintro ⟨β, hβ⟩
    refine ⟨fun c hc hLc hv hp => ?_, fun c₁ c₂ hc₁ hc₂ hL₁ hL₂ hv₁ hv₂ hP₁ hP₂ => ?_⟩
    · have := hβ c hc hLc hv
      rwa [hp, mul_zero, add_zero] at this
    · have h₁ := hβ c₁ hc₁ hL₁ hv₁
      have h₂ := hβ c₂ hc₂ hL₂ hv₂
      rw [nodeArchOnly, nodeArchOnly]
      nlinarith
  · rintro ⟨hzero, hdet⟩
    -- the demanded pole weights of the pole-positive level-`L` combinations
    set D : Set ℝ := {q | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ (∀ f ∈ c.support, LevelTest L f) ∧
      nodeVector c = 0 ∧ 0 < nodePoleMass c ∧ q = 1 - nodeArchEnergy c / nodePoleMass c} with hD
    have hDne : D.Nonempty := ⟨_, Finsupp.single (adjTestFn 1) 1, single_adjTestFn_nonneg 1,
      support_single_adjTestFn_level hL 1, nodeVector_adjTestFn_single 1 1,
      nodePoleMass_single_adjTestFn_one_pos, rfl⟩
    -- every allowed weight of a pole-negative combination bounds `D` from above
    have hbound : ∀ c₂ : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c₂ f) → (∀ f ∈ c₂.support, LevelTest L f) →
        nodeVector c₂ = 0 → nodePoleMass c₂ < 0 →
        ∀ q ∈ D, q ≤ 1 - nodeArchEnergy c₂ / nodePoleMass c₂ := by
      intro c₂ hc₂ hL₂ hv₂ hP₂ q hq
      obtain ⟨c₁, hc₁, hL₁, hv₁, hP₁, rfl⟩ := hq
      have h := hdet c₁ c₂ hc₁ hc₂ hL₁ hL₂ hv₁ hv₂ hP₁ hP₂
      rw [nodeArchOnly, nodeArchOnly] at h
      -- `1 − A₁/P₁ ≤ 1 − A₂/P₂` ⟺ `A₂/P₂ ≤ A₁/P₁` ⟺ (with `P₁ > 0 > P₂`) `A₂ P₁ ≥ A₁ P₂`
      have h1 : nodeArchEnergy c₂ / nodePoleMass c₂ ≤ nodeArchEnergy c₁ / nodePoleMass c₁ := by
        rw [div_le_iff_of_neg hP₂, div_mul_eq_mul_div, div_le_iff₀ hP₁]
        nlinarith
      linarith
    have hDbdd : BddAbove D :=
      ⟨1 - nodeArchEnergy (Finsupp.single (adjTestFn (-1)) 1) /
          nodePoleMass (Finsupp.single (adjTestFn (-1)) 1),
        hbound _ (single_adjTestFn_nonneg (-1)) (support_single_adjTestFn_level hL (-1))
          (nodeVector_adjTestFn_single (-1) 1) nodePoleMass_single_adjTestFn_neg_one_neg⟩
    refine ⟨sSup D, fun c hc hLc hv => ?_⟩
    rcases lt_trichotomy (nodePoleMass c) 0 with hP | hP | hP
    · -- pole-negative: `sSup D ≤ 1 − A/P`
      have := csSup_le hDne (hbound c hc hLc hv hP)
      have h2 : (sSup D - 1) * nodePoleMass c ≥ -nodeArchEnergy c := by
        have h3 : sSup D - 1 ≤ -(nodeArchEnergy c / nodePoleMass c) := by linarith
        have h4 : -(nodeArchEnergy c / nodePoleMass c) * nodePoleMass c = -nodeArchEnergy c := by
          rw [neg_mul, div_mul_cancel₀ _ hP.ne]
        nlinarith [mul_le_mul_of_nonpos_right h3 hP.le]
      linarith
    · have := hzero c hc hLc hv hP
      rw [hP, mul_zero, add_zero]; exact this
    · -- pole-positive: `1 − A/P ≤ sSup D`
      have hmem : 1 - nodeArchEnergy c / nodePoleMass c ∈ D := ⟨c, hc, hLc, hv, hP, rfl⟩
      have := le_csSup hDbdd hmem
      have h3 : -(nodeArchEnergy c / nodePoleMass c) ≤ sSup D - 1 := by linarith
      have h4 : -(nodeArchEnergy c / nodePoleMass c) * nodePoleMass c = -nodeArchEnergy c := by
        rw [neg_mul, div_mul_cancel₀ _ hP.ne']
      nlinarith [mul_le_mul_of_nonneg_right h3 hP.le]

end

end RHTower.WeilOneSided
