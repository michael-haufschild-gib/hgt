import GaloisForLFunctions.HTGeometry.ObserverExcisedUnion

/-!
# The observer-complement order parameter

Every successful inverse-gate path from a state has length at least its robust complexity, so the
discounted first-entrance potential is at most `a` to that power; one shortest word contributes at
least `(a/M)` to that power.  Subtracting the observer's capacity budget from the two bounds turns
the high-mode remainder into an exact order parameter: it is near one at every return and small
whenever the complexity is large.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Complement

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- Reachability into the target within `j` steps along positive-probability edges. -/
def PositiveReach (P : Matrix X X ℝ) (A : Finset X) (j : ℕ) (x : X) : Prop :=
  ∃ k ≤ j, ∃ path : ℕ → X, path 0 = x ∧ path k ∈ A ∧
    ∀ i < k, 0 < P (path i) (path (i + 1))

omit [Fintype X] [DecidableEq X] [Nonempty X] in
theorem positiveReach_of_mem {P : Matrix X X ℝ} {A : Finset X} {j : ℕ} {x : X} (hx : x ∈ A) :
    PositiveReach P A j x :=
  ⟨0, Nat.zero_le _, fun _ => x, rfl, hx, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

/-- **`(11b)`, upper half.**  A state from which no successful inverse-gate path is shorter than
`k` has discounted first-entrance potential at most `a^k`. -/
theorem hittingPotential_le_pow
    {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    {A : Finset X} {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    ∀ (k : ℕ) (x : X), ¬ PositiveReach P A k x →
      hittingPotential P A a hP hrow ha ha1 x ≤ a ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
      intro x hx
      have hnot : x ∉ A := fun h => hx (positiveReach_of_mem h)
      have hfix : hittingPotential P A a hP hrow ha ha1 x
          = a * ∑ y, P x y * hittingPotential P A a hP hrow ha ha1 y := by
        conv_lhs => rw [← hittingPotential_fixed P A a hP hrow ha ha1]
        rw [hittingMap_apply_notMem _ hnot]
      rw [hfix, pow_one]
      have hle : ∑ y, P x y * hittingPotential P A a hP hrow ha ha1 y ≤ 1 := by
        calc ∑ y, P x y * hittingPotential P A a hP hrow ha ha1 y ≤ ∑ y, P x y * 1 :=
              Finset.sum_le_sum fun y _ =>
                mul_le_mul_of_nonneg_left
                  (hittingPotential_mem_unitInterval hP hrow ha ha1 y).2 (hP x y)
          _ = 1 := by rw [← Finset.sum_mul, hrow x, one_mul]
      nlinarith [hle]
  | succ k ih =>
      intro x hx
      have hnot : x ∉ A := fun h => hx (positiveReach_of_mem h)
      have hfix : hittingPotential P A a hP hrow ha ha1 x
          = a * ∑ y, P x y * hittingPotential P A a hP hrow ha ha1 y := by
        conv_lhs => rw [← hittingPotential_fixed P A a hP hrow ha ha1]
        rw [hittingMap_apply_notMem _ hnot]
      have hterm : ∀ y : X, P x y * hittingPotential P A a hP hrow ha ha1 y ≤
          P x y * a ^ (k + 1) := by
        intro y
        by_cases hpos : 0 < P x y
        · have hy : ¬ PositiveReach P A k y := by
            rintro ⟨j, hj, path, hp0, hlast, hstep⟩
            refine hx ⟨j + 1, by omega, fun i => if i = 0 then x else path (i - 1), rfl, ?_, ?_⟩
            · simpa using hlast
            · intro i hi
              by_cases hi0 : i = 0
              · subst hi0
                simpa [hp0] using hpos
              · have hlt : i - 1 < j := by omega
                dsimp only
                rw [if_neg hi0, if_neg (show i + 1 ≠ 0 by omega),
                  show i + 1 - 1 = i - 1 + 1 by omega]
                exact hstep (i - 1) hlt
          exact mul_le_mul_of_nonneg_left (ih y hy) (hP x y)
        · have hzero : P x y = 0 := le_antisymm (le_of_not_gt hpos) (hP x y)
          rw [hzero, zero_mul, zero_mul]
      have hsum : ∑ y, P x y * hittingPotential P A a hP hrow ha ha1 y ≤ a ^ (k + 1) := by
        calc ∑ y, P x y * hittingPotential P A a hP hrow ha ha1 y ≤
              ∑ y, P x y * a ^ (k + 1) := Finset.sum_le_sum fun y _ => hterm y
          _ = a ^ (k + 1) := by rw [← Finset.sum_mul, hrow x, one_mul]
      rw [hfix, pow_succ, mul_comm (a ^ (k + 1)) a]
      exact mul_le_mul_of_nonneg_left hsum ha

end Complement

section OrderParameter

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- **`(11c)`.**  The observer-complement coordinate is at least the discounted path mass of one
witness word minus the observer's capacity budget. -/
theorem le_observerComplement
    {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    {A : Finset X} {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {M : ℝ} (hM : 1 ≤ M) {s : ℕ}
    (proj : X → ℝ) {budget : ℝ} {x : X}
    (hreach : ReachableWithin P A M s x) (hub : proj x ≤ budget) :
    (a / M) ^ s - budget ≤
      hittingPotential P A a hP hrow ha.le ha1 x - proj x := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hratio0 : (0 : ℝ) ≤ a / M := div_nonneg ha.le hM0.le
  have hratio1 : a / M ≤ 1 := by
    rw [div_le_one hM0]; linarith
  obtain ⟨k, hks, path, hpath0, hlast, hstep⟩ := hreach
  have hbase := le_hittingPotential_of_path hP hrow ha.le ha1 hM k path hlast hstep
  rw [hpath0] at hbase
  have hmono : (a / M) ^ s ≤ (a / M) ^ k := pow_le_pow_of_le_one hratio0 hratio1 hks
  linarith [le_trans hmono hbase]

/-- **`(11d)`/`(11f)`.**  The observer-complement coordinate is at most the length-limited
discounted mass minus the observer's capacity floor. -/
theorem observerComplement_le
    {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    {A : Finset X} {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) {k : ℕ}
    (proj : X → ℝ) {floor : ℝ} {x : X}
    (hfar : ¬ PositiveReach P A k x) (hlb : floor ≤ proj x) :
    hittingPotential P A a hP hrow ha ha1 x - proj x ≤ a ^ (k + 1) - floor := by
  have hup := hittingPotential_le_pow hP hrow ha ha1 k x hfar
  linarith

/-- **`(11e)`.**  At a return the observer complement is at least one minus the observer's
capacity budget. -/
theorem one_sub_le_observerComplement_of_mem
    {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    {A : Finset X} {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (proj : X → ℝ) {budget : ℝ} {x : X} (hx : x ∈ A) (hub : proj x ≤ budget) :
    1 - budget ≤ hittingPotential P A a hP hrow ha ha1 x - proj x := by
  rw [hittingPotential_eq_one hP hrow ha ha1 hx]
  linarith

end OrderParameter

end

end GaloisForLFunctions.HTGeometry
