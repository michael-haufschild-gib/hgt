import GaloisForLFunctions.HTGeometry.ConstitutivePositiveOverlapDefect

open scoped BigOperators

namespace HTGeometry

noncomputable section

/-!
# Total-variation conflict coloring

A finite family of total-variation tasks generates a sign-conflict graph on source atoms.
Deterministic observers preserve every declared task exactly iff they properly color this graph.
Thus observer alphabet size is a genuine finite resource, distinct from later topological or
regularity admission.
-/

def finitePositiveFiberMass {P K : Type*} [Fintype P] [DecidableEq K]
    (d : P → ℝ) (kappa : P → K) (k : K) : ℝ :=
  finiteSignedFiberMass (fun p => max (d p) 0) kappa k

def finiteNegativeFiberMass {P K : Type*} [Fintype P] [DecidableEq K]
    (d : P → ℝ) (kappa : P → K) (k : K) : ℝ :=
  finiteSignedFiberMass (fun p => max (-d p) 0) kappa k

theorem min_add_max_sub_eq_left (a b : ℝ) :
    min a b + max (a - b) 0 = a := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
    ring

theorem min_add_max_sub_eq_right (a b : ℝ) :
    min a b + max (b - a) 0 = b := by
  simpa [sub_eq_add_neg, add_comm, min_comm] using min_add_max_sub_eq_left b a

theorem finiteSignedFiberMass_eq_meet_add_positive
    {P K : Type*} [Fintype P] [DecidableEq K]
    (u v : P → ℝ) (kappa : P → K) (k : K) :
    finiteSignedFiberMass u kappa k =
      finiteSignedFiberMass (finiteProfileMeet u v) kappa k +
        finitePositiveFiberMass (fun p => u p - v p) kappa k := by
  classical
  simp only [finiteSignedFiberMass, finitePositiveFiberMass]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpk : kappa p = k
  · simp only [hpk, if_true, finiteProfileMeet]
    exact (min_add_max_sub_eq_left (u p) (v p)).symm
  · simp [hpk]

theorem finiteSignedFiberMass_eq_meet_add_negative
    {P K : Type*} [Fintype P] [DecidableEq K]
    (u v : P → ℝ) (kappa : P → K) (k : K) :
    finiteSignedFiberMass v kappa k =
      finiteSignedFiberMass (finiteProfileMeet u v) kappa k +
        finiteNegativeFiberMass (fun p => u p - v p) kappa k := by
  classical
  simp only [finiteSignedFiberMass, finiteNegativeFiberMass]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpk : kappa p = k
  · simp only [hpk, if_true, finiteProfileMeet]
    have hpoint := min_add_max_sub_eq_right (u p) (v p)
    simpa only [neg_sub] using hpoint.symm
  · simp [hpk]

/-- Exact Jordan-overlap formula on one observer fibre. -/
theorem finiteOverlapDefect_eq_min_positive_negative
    {P K : Type*} [Fintype P] [DecidableEq K]
    (u v : P → ℝ) (kappa : P → K) (k : K) :
    finiteOverlapDefect u v kappa k =
      min
        (finitePositiveFiberMass (fun p => u p - v p) kappa k)
        (finiteNegativeFiberMass (fun p => u p - v p) kappa k) := by
  let c := finiteSignedFiberMass (finiteProfileMeet u v) kappa k
  let pos := finitePositiveFiberMass (fun p => u p - v p) kappa k
  let neg := finiteNegativeFiberMass (fun p => u p - v p) kappa k
  have hu : finiteSignedFiberMass u kappa k = c + pos :=
    finiteSignedFiberMass_eq_meet_add_positive u v kappa k
  have hv : finiteSignedFiberMass v kappa k = c + neg :=
    finiteSignedFiberMass_eq_meet_add_negative u v kappa k
  rw [finiteOverlapDefect, hu, hv]
  change min (c + pos) (c + neg) - c = min pos neg
  rcases le_total pos neg with h | h
  · rw [min_eq_left h, min_eq_left (by linarith : c + pos ≤ c + neg)]
    ring
  · rw [min_eq_right h, min_eq_right (by linarith : c + neg ≤ c + pos)]
    ring

theorem finitePositiveFiberMass_nonneg
    {P K : Type*} [Fintype P] [DecidableEq K]
    (d : P → ℝ) (kappa : P → K) (k : K) :
    0 ≤ finitePositiveFiberMass d kappa k := by
  classical
  rw [finitePositiveFiberMass, finiteSignedFiberMass]
  apply Finset.sum_nonneg
  intro p hp
  by_cases hpk : kappa p = k <;> simp [hpk]

theorem finiteNegativeFiberMass_nonneg
    {P K : Type*} [Fintype P] [DecidableEq K]
    (d : P → ℝ) (kappa : P → K) (k : K) :
    0 ≤ finiteNegativeFiberMass d kappa k := by
  classical
  rw [finiteNegativeFiberMass, finiteSignedFiberMass]
  apply Finset.sum_nonneg
  intro p hp
  by_cases hpk : kappa p = k <;> simp [hpk]

theorem finitePositiveFiberMass_pos_of_mem
    {P K : Type*} [Fintype P] [DecidableEq K]
    (d : P → ℝ) (kappa : P → K) (k : K) {x : P}
    (hxk : kappa x = k) (hdx : 0 < d x) :
    0 < finitePositiveFiberMass d kappa k := by
  classical
  rw [finitePositiveFiberMass, finiteSignedFiberMass]
  apply Finset.sum_pos'
  · intro p hp
    by_cases hpk : kappa p = k <;> simp [hpk]
  · refine ⟨x, Finset.mem_univ x, ?_⟩
    simp [hxk, max_eq_left hdx.le, hdx]

theorem finiteNegativeFiberMass_pos_of_mem
    {P K : Type*} [Fintype P] [DecidableEq K]
    (d : P → ℝ) (kappa : P → K) (k : K) {x : P}
    (hxk : kappa x = k) (hdx : d x < 0) :
    0 < finiteNegativeFiberMass d kappa k := by
  classical
  rw [finiteNegativeFiberMass, finiteSignedFiberMass]
  apply Finset.sum_pos'
  · intro p hp
    by_cases hpk : kappa p = k <;> simp [hpk]
  · refine ⟨x, Finset.mem_univ x, ?_⟩
    simp [hxk, max_eq_left (neg_pos.mpr hdx).le, hdx]

theorem finitePositiveFiberMass_eq_zero_of_nonpos
    {P K : Type*} [Fintype P] [DecidableEq K]
    (d : P → ℝ) (kappa : P → K) (k : K)
    (h : ∀ p, kappa p = k → d p ≤ 0) :
    finitePositiveFiberMass d kappa k = 0 := by
  classical
  rw [finitePositiveFiberMass, finiteSignedFiberMass]
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hpk : kappa p = k
  · simp [hpk, max_eq_right (h p hpk)]
  · simp [hpk]

theorem finiteNegativeFiberMass_eq_zero_of_nonneg
    {P K : Type*} [Fintype P] [DecidableEq K]
    (d : P → ℝ) (kappa : P → K) (k : K)
    (h : ∀ p, kappa p = k → 0 ≤ d p) :
    finiteNegativeFiberMass d kappa k = 0 := by
  classical
  rw [finiteNegativeFiberMass, finiteSignedFiberMass]
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hpk : kappa p = k
  · simp [hpk, max_eq_right (neg_nonpos.mpr (h p hpk))]
  · simp [hpk]

def finiteFiberSignCompatible {P K : Type*}
    (d : P → ℝ) (kappa : P → K) (k : K) : Prop :=
  ∀ x y, kappa x = k → kappa y = k → 0 ≤ d x * d y

/-- Zero false overlap on a fibre is exactly absence of an opposite-sign pair in that fibre. -/
theorem finiteOverlapDefect_eq_zero_iff_fiberSignCompatible
    {P K : Type*} [Fintype P] [DecidableEq K]
    (u v : P → ℝ) (kappa : P → K) (k : K) :
    finiteOverlapDefect u v kappa k = 0 ↔
      finiteFiberSignCompatible (fun p => u p - v p) kappa k := by
  let d : P → ℝ := fun p => u p - v p
  constructor
  · intro hzero x y hxk hyk
    by_contra hxy
    have hneg : d x * d y < 0 := lt_of_not_ge hxy
    have hpos : 0 < finitePositiveFiberMass d kappa k := by
      rcases (mul_neg_iff.mp hneg) with h | h
      · exact finitePositiveFiberMass_pos_of_mem d kappa k hxk h.1
      · exact finitePositiveFiberMass_pos_of_mem d kappa k hyk h.2
    have hnegative : 0 < finiteNegativeFiberMass d kappa k := by
      rcases (mul_neg_iff.mp hneg) with h | h
      · exact finiteNegativeFiberMass_pos_of_mem d kappa k hyk h.2
      · exact finiteNegativeFiberMass_pos_of_mem d kappa k hxk h.1
    have hmin : 0 < min
        (finitePositiveFiberMass d kappa k)
        (finiteNegativeFiberMass d kappa k) := lt_min hpos hnegative
    rw [finiteOverlapDefect_eq_min_positive_negative] at hzero
    linarith
  · intro hcompatible
    rw [finiteOverlapDefect_eq_min_positive_negative]
    by_cases hpos : ∃ x, kappa x = k ∧ 0 < d x
    · obtain ⟨x, hxk, hdx⟩ := hpos
      have hnonneg : ∀ y, kappa y = k → 0 ≤ d y := by
        intro y hyk
        by_contra hy
        have hdy : d y < 0 := lt_of_not_ge hy
        exact (not_lt_of_ge (hcompatible x y hxk hyk))
          (mul_neg_of_pos_of_neg hdx hdy)
      rw [finiteNegativeFiberMass_eq_zero_of_nonneg d kappa k hnonneg]
      rw [min_eq_right (finitePositiveFiberMass_nonneg d kappa k)]
    · have hnonpos : ∀ x, kappa x = k → d x ≤ 0 := by
        intro x hxk
        exact le_of_not_gt (fun hdx => hpos ⟨x, hxk, hdx⟩)
      rw [finitePositiveFiberMass_eq_zero_of_nonpos d kappa k hnonpos]
      rw [min_eq_left (finiteNegativeFiberMass_nonneg d kappa k)]

def finiteTaskConflict {J P : Type*} (u v : J → P → ℝ) (x y : P) : Prop :=
  ∃ j, (u j x - v j x) * (u j y - v j y) < 0

def finiteTaskLossless {J P K : Type*} [Fintype P] [Fintype K]
    [DecidableEq K] (u v : J → P → ℝ) (kappa : P → K) : Prop :=
  ∀ j,
    finiteProfileTotalVariation
        (fun k => finiteSignedFiberMass (u j) kappa k)
        (fun k => finiteSignedFiberMass (v j) kappa k) =
      finiteProfileTotalVariation (u j) (v j)

def finiteTaskProperColoring {J P K : Type*}
    (u v : J → P → ℝ) (kappa : P → K) : Prop :=
  ∀ x y, finiteTaskConflict u v x y → kappa x ≠ kappa y

/-- Lossless deterministic observation is exactly proper coloring of task conflicts. -/
theorem finiteTaskLossless_iff_properColoring
    {J P K : Type*} [Fintype P] [Fintype K]
    [DecidableEq P] [DecidableEq K]
    (u v : J → P → ℝ) (kappa : P → K) :
    finiteTaskLossless u v kappa ↔ finiteTaskProperColoring u v kappa := by
  constructor
  · intro hloss x y hconflict hsame
    obtain ⟨j, hneg⟩ := hconflict
    have hmass : finiteOverlapDefectMass (u j) (v j) kappa = 0 := by
      rw [finiteOverlapDefectMass_eq_totalVariation_loss, hloss j]
      ring
    have hfiber : finiteOverlapDefect (u j) (v j) kappa (kappa x) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun k (_ : k ∈ Finset.univ) =>
          finiteOverlapDefect_nonneg (u j) (v j) kappa k)).mp hmass
          (kappa x) (Finset.mem_univ (kappa x))
    have hcompatible :=
      (finiteOverlapDefect_eq_zero_iff_fiberSignCompatible
        (u j) (v j) kappa (kappa x)).mp hfiber
    exact (not_lt_of_ge (hcompatible x y rfl hsame.symm)) hneg
  · intro hproper j
    have hfiber : ∀ k, finiteOverlapDefect (u j) (v j) kappa k = 0 := by
      intro k
      apply (finiteOverlapDefect_eq_zero_iff_fiberSignCompatible
        (u j) (v j) kappa k).mpr
      intro x y hxk hyk
      by_contra hxy
      have hneg : (u j x - v j x) * (u j y - v j y) < 0 := lt_of_not_ge hxy
      exact (hproper x y ⟨j, hneg⟩) (hxk.trans hyk.symm)
    have hmass : finiteOverlapDefectMass (u j) (v j) kappa = 0 := by
      rw [finiteOverlapDefectMass]
      simp [hfiber]
    have hloss := finiteOverlapDefectMass_eq_totalVariation_loss (u j) (v j) kappa
    rw [hmass] at hloss
    linarith

/-- Every collapsed conflict edge forces strict loss for its witnessing task. -/
theorem finiteTaskConflict_collapsed_strict_loss
    {J P K : Type*} [Fintype P] [Fintype K]
    [DecidableEq P] [DecidableEq K]
    (u v : J → P → ℝ) (kappa : P → K)
    {j : J} {x y : P}
    (hneg : (u j x - v j x) * (u j y - v j y) < 0)
    (hsame : kappa x = kappa y) :
    finiteProfileTotalVariation
        (fun k => finiteSignedFiberMass (u j) kappa k)
        (fun k => finiteSignedFiberMass (v j) kappa k) <
      finiteProfileTotalVariation (u j) (v j) := by
  have hfiber_ne : finiteOverlapDefect (u j) (v j) kappa (kappa x) ≠ 0 := by
    intro hzero
    have hcompatible :=
      (finiteOverlapDefect_eq_zero_iff_fiberSignCompatible
        (u j) (v j) kappa (kappa x)).mp hzero
    exact (not_lt_of_ge (hcompatible x y rfl hsame.symm)) hneg
  have hfiber_pos : 0 < finiteOverlapDefect (u j) (v j) kappa (kappa x) :=
    lt_of_le_of_ne
      (finiteOverlapDefect_nonneg (u j) (v j) kappa (kappa x))
      (Ne.symm hfiber_ne)
  have hmass_pos : 0 < finiteOverlapDefectMass (u j) (v j) kappa := by
    rw [finiteOverlapDefectMass]
    apply Finset.sum_pos'
    · intro k hk
      exact finiteOverlapDefect_nonneg (u j) (v j) kappa k
    · exact ⟨kappa x, Finset.mem_univ (kappa x), hfiber_pos⟩
  have hloss := finiteOverlapDefectMass_eq_totalVariation_loss (u j) (v j) kappa
  linarith

def finiteTaskObserverWidthAtMost {J P : Type*} [Fintype P]
    (u v : J → P → ℝ) (q : ℕ) : Prop :=
  ∃ kappa : P → Fin q, finiteTaskLossless u v kappa

def finiteTaskConflictColorable {J P : Type*}
    (u v : J → P → ℝ) (q : ℕ) : Prop :=
  ∃ kappa : P → Fin q, finiteTaskProperColoring u v kappa

/-- Finite observer-width existence is exactly finite conflict colorability. -/
theorem finiteTaskObserverWidthAtMost_iff_conflictColorable
    {J P : Type*} [Fintype P] [DecidableEq P]
    (u v : J → P → ℝ) (q : ℕ) :
    finiteTaskObserverWidthAtMost u v q ↔ finiteTaskConflictColorable u v q := by
  constructor
  · rintro ⟨kappa, hkappa⟩
    exact ⟨kappa, (finiteTaskLossless_iff_properColoring u v kappa).mp hkappa⟩
  · rintro ⟨kappa, hkappa⟩
    exact ⟨kappa, (finiteTaskLossless_iff_properColoring u v kappa).mpr hkappa⟩

def relationEdgeLeftProfile {P : Type*} [DecidableEq P]
    (R : P → P → Prop) [DecidableRel R] (e : P × P) (z : P) : ℝ :=
  if R e.1 e.2 then if z = e.1 then 1 else 0 else 0

def relationEdgeRightProfile {P : Type*} [DecidableEq P]
    (R : P → P → Prop) [DecidableRel R] (e : P × P) (z : P) : ℝ :=
  if R e.1 e.2 then if z = e.2 then 1 else 0 else 0

/-- Every finite simple conflict relation is realized by nonnegative Dirac profile pairs. -/
theorem arbitrary_symmetric_irreflexive_relation_is_taskConflict
    {P : Type*} [Fintype P] [DecidableEq P]
    (R : P → P → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x)
    (hirr : ∀ x, ¬ R x x) (x y : P) :
    finiteTaskConflict
        (relationEdgeLeftProfile R)
        (relationEdgeRightProfile R) x y ↔ R x y := by
  constructor
  · rintro ⟨⟨a, b⟩, hneg⟩
    have hab : R a b := by
      by_contra hn
      simp [relationEdgeLeftProfile, relationEdgeRightProfile, hn] at hneg
    have hane : a ≠ b := by
      intro habEq
      exact hirr a (habEq ▸ hab)
    have hends : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
      by_cases hxa : x = a <;> by_cases hxb : x = b <;>
        by_cases hya : y = a <;> by_cases hyb : y = b <;>
        simp [relationEdgeLeftProfile, relationEdgeRightProfile, hab,
          hane, hane.symm, hxa, hxb, hya, hyb] at hneg ⊢ <;>
          norm_num at hneg
    rcases hends with ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
    · simpa [hxa, hyb] using hab
    · simpa [hxb, hya] using hsymm a b hab
  · intro hxy
    have hne : x ≠ y := by
      intro h
      exact hirr x (h ▸ hxy)
    refine ⟨(x, y), ?_⟩
    simp [relationEdgeLeftProfile, relationEdgeRightProfile, hxy, hne, hne.symm]

/-- Capstone: one theorem packages exact task preservation and its minimal finite-width test. -/
theorem totalVariation_conflictColoring_mechanism_closed
    {J P K : Type*} [Fintype P] [Fintype K]
    [DecidableEq P] [DecidableEq K]
    (u v : J → P → ℝ) (kappa : P → K) (q : ℕ) :
    (finiteTaskLossless u v kappa ↔ finiteTaskProperColoring u v kappa) ∧
      (finiteTaskObserverWidthAtMost u v q ↔ finiteTaskConflictColorable u v q) := by
  exact ⟨finiteTaskLossless_iff_properColoring u v kappa,
    finiteTaskObserverWidthAtMost_iff_conflictColorable u v q⟩

end

end HTGeometry
