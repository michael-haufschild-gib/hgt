import GaloisForLFunctions.TensorPowerProgramme.TheThreeLinesOfFrames
import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheWallOfASourceClassIsTheLargestAbscissaItRealizes

/-!
# A wall above one half is a world off the line

Whether the frames of the three lines reach the critical line is decided here in two readings.

* **Validity.** The levers that are valid for `ζ` have wall `Θ` below the seed
  (`wall_validLevers_zeta`): a wall above `½` of all valid levers is the negation of RH
  (`half_lt_wall_validLevers_zeta_iff`).
* **Sources.** A source is a class of worlds with abscissas `A`. The wall of its valid levers
  exceeds `½` iff the class has a world with abscissa in `(½, s]`
  (`half_lt_wall_iff_exists_offLine`). For a class through `ζ` the wall below `7/8` is `½` iff
  every world of the class at or below `7/8` lies on the line (`wall_validLevers_eq_half_iff`),
  and levers of the class with wall `½` prove RH (`riemannHypothesis_of_wall_le_half`).
* **The lines have the same sources.** On a class a Deligne lever is valid iff no world lies right
  of `½` (`deligneLever_mem_validLevers_iff`); the sign lever of period `k` is valid iff no world
  lies right of `k/(2(k − 1))` (`signLever_mem_validLevers_iff`); sign levers at unboundedly many
  periods are valid iff no world lies right of `½` (`signLevers_cofinal_iff`). So one Deligne lever
  and the sign levers of unboundedly many periods are valid on the same classes
  (`signLevers_cofinal_iff_deligneLever`).
* **The sign line by periods.** The sign levers with periods in `P` allow the values at or below
  every centre (`allowed_signLevers`). With periods up to `K` their wall is at least
  `min s (K/(2(K − 1))) > ½` (`min_signCentre_le_wall_signLevers`); it is `½` iff `P` is unbounded
  (`wall_signLevers_eq_half_iff`).
* **Estimate floors.** A route of frames `(c j, k j)` with estimate floors `σ j` allows the values
  at or below every level `max (σ j) (c j/(k j − 1))` (`allowed_flooredFrames`); its wall exceeds
  `h` iff some `b ∈ (h, s]` lies at or below every level (`lt_wall_flooredFrames_iff`).
-/

open Set

noncomputable section

namespace GaloisForLFunctions.TensorPowerProgramme

open ExponentDynamicsOfTheCriticalStrip FamilyContinuationTheory

/-! ### 1. The centres of the sign line -/

/-- The centre `k/(2(k − 1))` of the sign line at period `k`. -/
def signCentre (k : ℝ) : ℝ := k / (2 * (k - 1))

theorem signCentre_eq {k : ℝ} (hk : 1 < k) : signCentre k = 1 / 2 + 1 / (2 * (k - 1)) := by
  have hk1 : k - 1 ≠ 0 := (sub_pos.2 hk).ne'
  rw [signCentre]
  field_simp
  ring

theorem half_lt_signCentre {k : ℝ} (hk : 1 < k) : 1 / 2 < signCentre k := by
  rw [signCentre_eq hk]
  have : 0 < 1 / (2 * (k - 1)) := one_div_pos.2 (by linarith)
  linarith

/-- The centres of the sign line decrease with the period. -/
theorem signCentre_anti {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) : signCentre b ≤ signCentre a := by
  rw [signCentre_eq ha, signCentre_eq (ha.trans_le hab)]
  have : 1 / (2 * (b - 1)) ≤ 1 / (2 * (a - 1)) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  linarith

/-- The centres of the sign line fall below every `b > ½`. -/
theorem exists_forall_signCentre_lt {b : ℝ} (hb : 1 / 2 < b) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (1 : ℝ) < k ∧ signCentre k < b := by
  obtain ⟨K, hK⟩ := exists_nat_gt (max 1 (2 * b / (2 * b - 1)))
  refine ⟨K, fun k hk => ?_⟩
  have hKk : (K : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (1 : ℝ) < k := ((le_max_left _ _).trans_lt hK).trans_le hKk
  have h2 : 2 * b / (2 * b - 1) < k := ((le_max_right _ _).trans_lt hK).trans_le hKk
  refine ⟨h1, ?_⟩
  rw [signCentre, div_lt_iff₀ (by linarith)]
  rw [div_lt_iff₀ (by linarith)] at h2
  linarith

/-- A natural period `k ≥ 2` exceeds one as a real number. -/
private theorem one_lt_cast {k : ℕ} (hk : 2 ≤ k) : (1 : ℝ) < k := by
  exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2) hk

/-! ### 2. The levers of the lines on a source class -/

/-- A Deligne lever is a lever of `θ` iff `θ ≤ ½`. -/
theorem isLever_deligneLever_iff {k θ : ℝ} (hk : 1 < k) :
    IsLever θ (deligneLever k) ↔ θ ≤ 1 / 2 := by
  have hk1 : k - 1 ≠ 0 := (sub_pos.2 hk).ne'
  have hc : (k - 1) / 2 / (k - 1) = 1 / 2 := by field_simp
  rw [deligneLever, isLever_pairingStep_iff hk, hc]

/-- The sign lever of period `k` is a lever of `θ` iff `θ` is at most its centre. -/
theorem isLever_signLever_iff {k θ : ℝ} (hk : 1 < k) :
    IsLever θ (signLever k) ↔ θ ≤ signCentre k := by
  rw [signLever, isLever_pairingStep_iff hk, div_div, signCentre]

/-- **A Deligne lever is valid on a source class iff no world lies right of `½`.** -/
theorem deligneLever_mem_validLevers_iff {A : Set ℝ} {k : ℝ} (hk : 1 < k) :
    deligneLever k ∈ validLevers A ↔ ∀ a ∈ A, a ≤ 1 / 2 :=
  forall₂_congr fun _ _ => isLever_deligneLever_iff hk

/-- The sign lever of period `k` is valid on a source class iff no world lies right of its
centre. -/
theorem signLever_mem_validLevers_iff {A : Set ℝ} {k : ℝ} (hk : 1 < k) :
    signLever k ∈ validLevers A ↔ ∀ a ∈ A, a ≤ signCentre k :=
  forall₂_congr fun _ _ => isLever_signLever_iff hk

/-- **Sign levers at unboundedly many periods are valid on a source class iff no world lies right
of `½`.** -/
theorem signLevers_cofinal_iff {A : Set ℝ} :
    (∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ 2 ≤ k ∧ signLever k ∈ validLevers A) ↔ ∀ a ∈ A, a ≤ 1 / 2 := by
  constructor
  · intro h a ha
    by_contra hlt
    rw [not_le] at hlt
    -- a period whose centre lies left of the world `a`
    obtain ⟨K, hK⟩ := exists_forall_signCentre_lt hlt
    obtain ⟨k, hKk, -, hk⟩ := h K
    exact absurd ((signLever_mem_validLevers_iff (hK k hKk).1).1 hk a ha)
      (not_le.mpr (hK k hKk).2)
  · intro h K
    have h1 := one_lt_cast (le_max_right K 2)
    exact ⟨max K 2, le_max_left _ _, le_max_right _ _,
      (signLever_mem_validLevers_iff h1).2 fun a ha => (h a ha).trans (half_lt_signCentre h1).le⟩

/-- **The lines have the same sources.** On a source class the sign levers of unboundedly many
periods are valid iff one Deligne lever is. -/
theorem signLevers_cofinal_iff_deligneLever {A : Set ℝ} {k : ℝ} (hk : 1 < k) :
    (∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧ 2 ≤ n ∧ signLever n ∈ validLevers A) ↔
      deligneLever k ∈ validLevers A :=
  signLevers_cofinal_iff.trans (deligneLever_mem_validLevers_iff hk).symm

/-! ### 3. The sign line by periods -/

/-- The sign levers with periods in `P`. -/
def signLevers (P : Set ℕ) : Set (ℝ → ℝ) := {T | ∃ k ∈ P, T = signLever k}

/-- The sign levers with periods in `P` allow the values at or below every centre. -/
theorem allowed_signLevers {P : Set ℕ} (hP : ∀ k ∈ P, 2 ≤ k) (s : ℝ) :
    allowed (signLevers P) s = {b | b ≤ s ∧ ∀ k ∈ P, b ≤ signCentre k} := by
  have hkey : ∀ k ∈ P, ∀ b : ℝ, b ≤ signLever k b ↔ b ≤ signCentre k := fun k hk b => by
    have h1 := one_lt_cast (hP k hk)
    exact (isLever_iff_le_apply_self (monotone_pairingStep (by linarith))).symm.trans
      (isLever_signLever_iff h1)
  ext b
  constructor
  · exact fun hb => ⟨hb.1, fun k hk => (hkey k hk b).1 (hb.2 _ ⟨k, hk, rfl⟩)⟩
  · rintro ⟨hbs, hb⟩
    refine ⟨hbs, ?_⟩
    rintro T ⟨k, hk, rfl⟩
    exact (hkey k hk b).2 (hb k hk)

/-- **Bounded periods end above `½`.** With periods up to `K` the wall of the sign line is at
least `min s (K/(2(K − 1)))`. -/
theorem min_signCentre_le_wall_signLevers {P : Set ℕ} (hP : ∀ k ∈ P, 2 ≤ k) {K : ℕ}
    (hPK : ∀ k ∈ P, k ≤ K) (s : ℝ) :
    min s (signCentre K) ≤ wall (signLevers P) s := by
  refine le_csSup (bddAbove_allowed _ s) ?_
  rw [allowed_signLevers hP]
  refine ⟨min_le_left _ _, fun k hk => (min_le_right _ _).trans ?_⟩
  exact signCentre_anti (one_lt_cast (hP k hk)) (by exact_mod_cast hPK k hk)

/-- **The wall of the sign line is `½` iff its periods are unbounded.** -/
theorem wall_signLevers_eq_half_iff {P : Set ℕ} (hP : ∀ k ∈ P, 2 ≤ k) {s : ℝ}
    (hs : 1 / 2 < s) : wall (signLevers P) s = 1 / 2 ↔ ¬ BddAbove P := by
  constructor
  · rintro hw ⟨K, hK⟩
    -- periods up to `max K 2` keep the wall at `min s (signCentre (max K 2)) > ½`
    have hle := min_signCentre_le_wall_signLevers hP
      (fun k hk => (hK hk).trans (le_max_left K 2)) s
    rw [hw] at hle
    exact absurd hle
      (not_le.mpr (lt_min hs (half_lt_signCentre (one_lt_cast (le_max_right K 2)))))
  · intro hunb
    have hmem : (1 / 2 : ℝ) ∈ allowed (signLevers P) s := by
      rw [allowed_signLevers hP]
      exact ⟨hs.le, fun k hk => (half_lt_signCentre (one_lt_cast (hP k hk))).le⟩
    refine le_antisymm (csSup_le ⟨_, hmem⟩ fun b hb => ?_) (le_csSup (bddAbove_allowed _ s) hmem)
    rw [allowed_signLevers hP] at hb
    by_contra hlt
    rw [not_le] at hlt
    -- an allowed value right of `½` lies right of the centre of some period of `P`
    obtain ⟨K, hK⟩ := exists_forall_signCentre_lt hlt
    obtain ⟨k, hk, hKk⟩ := not_bddAbove_iff.1 hunb K
    exact absurd (hb.2 k hk) (not_le.mpr (hK k hKk.le).2)

/-! ### 4. Frames with estimate floors -/

/-- The levers of a route: frames `(c j, k j)` with estimate floors `σ j`. -/
def flooredFrames {J : Type*} (σ c k : J → ℝ) : Set (ℝ → ℝ) :=
  {T | ∃ j, T = fun b => max (σ j) (pairingStep (c j) (k j) b)}

/-- A route of floored frames allows the values at or below every level
`max (σ j) (c j/(k j − 1))`. -/
theorem allowed_flooredFrames {J : Type*} {σ c k : J → ℝ} (hk : ∀ j, 1 < k j) (s : ℝ) :
    allowed (flooredFrames σ c k) s =
      {b | b ≤ s ∧ ∀ j, b ≤ max (σ j) (c j / (k j - 1))} := by
  have hkey : ∀ j, ∀ b : ℝ, b ≤ max (σ j) (pairingStep (c j) (k j) b) ↔
      b ≤ max (σ j) (c j / (k j - 1)) := fun j b => by
    have hmono : Monotone fun x => max (σ j) (pairingStep (c j) (k j) x) := fun _ _ hab =>
      max_le_max le_rfl (monotone_pairingStep (by linarith [hk j]) hab)
    exact (isLever_iff_le_apply_self hmono).symm.trans (isLever_flooredFrame_iff (hk j))
  ext b
  constructor
  · exact fun hb => ⟨hb.1, fun j => (hkey j b).1 (hb.2 _ ⟨j, rfl⟩)⟩
  · rintro ⟨hbs, hb⟩
    refine ⟨hbs, ?_⟩
    rintro T ⟨j, rfl⟩
    exact (hkey j b).2 (hb j)

/-- **A route with estimate floors ends above `h` iff some value in `(h, s]` lies at or below
every level.** -/
theorem lt_wall_flooredFrames_iff {J : Type*} {σ c k : J → ℝ} (hk : ∀ j, 1 < k j) {s h : ℝ}
    (hne : (allowed (flooredFrames σ c k) s).Nonempty) :
    h < wall (flooredFrames σ c k) s ↔
      ∃ b, h < b ∧ b ≤ s ∧ ∀ j, b ≤ max (σ j) (c j / (k j - 1)) := by
  rw [wall, lt_csSup_iff (bddAbove_allowed _ s) hne, allowed_flooredFrames hk]
  exact ⟨fun ⟨b, hb, hhb⟩ => ⟨b, hhb, hb.1, hb.2⟩, fun ⟨b, hhb, hbs, hb⟩ => ⟨b, ⟨hbs, hb⟩, hhb⟩⟩

/-! ### 5. The verdict for `ζ` -/

/-- **Validity.** The levers that are valid for `ζ` have wall `Θ` below the seed `7/8`. -/
theorem wall_validLevers_zeta :
    wall (validLevers {RHTower.zetaZeroAbscissa}) (7 / 8) = RHTower.zetaZeroAbscissa :=
  wall_validLevers_singleton zetaZeroAbscissa_le_seven_eighths

/-- A wall above `½` of all levers valid for `ζ` is the negation of RH. -/
theorem half_lt_wall_validLevers_zeta_iff :
    1 / 2 < wall (validLevers {RHTower.zetaZeroAbscissa}) (7 / 8) ↔ ¬ RiemannHypothesis := by
  rw [wall_validLevers_zeta, SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero,
    SquareRootThreshold.zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
  have hlo := RHTower.half_le_zetaZeroAbscissa
  constructor
  · intro h h0
    linarith
  · intro h
    exact lt_of_le_of_ne hlo fun h0 => h (by linarith)

/-- **Sources.** The wall of a source class exceeds `½` iff the class has a world with abscissa in
`(½, s]`. -/
theorem half_lt_wall_iff_exists_offLine {A : Set ℝ} {s : ℝ} (hne : (A ∩ Iic s).Nonempty) :
    1 / 2 < wall (validLevers A) s ↔ ∃ a ∈ A, 1 / 2 < a ∧ a ≤ s :=
  lt_wall_validLevers_iff hne

/-- **Levers of a source class through `ζ` with wall `½` prove RH.** -/
theorem riemannHypothesis_of_wall_le_half {𝒯 : Set (ℝ → ℝ)} {A : Set ℝ}
    (hsub : 𝒯 ⊆ validLevers A) (hζ : RHTower.zetaZeroAbscissa ∈ A)
    (hwall : wall 𝒯 (7 / 8) ≤ 1 / 2) : RiemannHypothesis := by
  have hle := (le_wall_of_mem hsub hζ zetaZeroAbscissa_le_seven_eighths).trans hwall
  have hlo := RHTower.half_le_zetaZeroAbscissa
  rw [SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero,
    SquareRootThreshold.zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
  linarith

/-- **The decision for a source class through `ζ`.** Below the seed `7/8` the valid levers of the
class have wall `½` iff every world of the class at or below the seed lies on the line. -/
theorem wall_validLevers_eq_half_iff {A : Set ℝ} (hζ : RHTower.zetaZeroAbscissa ∈ A)
    (hA : ∀ a ∈ A, 1 / 2 ≤ a) :
    wall (validLevers A) (7 / 8) = 1 / 2 ↔ ∀ a ∈ A, a ≤ 7 / 8 → a = 1 / 2 :=
  wall_validLevers_eq_iff ⟨_, hζ, zetaZeroAbscissa_le_seven_eighths⟩ hA

end GaloisForLFunctions.TensorPowerProgramme
