import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.LeversThatBiteFailInTheWorlds

/-!
# The wall of a source class is the largest abscissa it realizes

A proof of a lever from a list of properties proves the lever for every world with these
properties. A **source class** is therefore a set `A` of abscissas, those of its worlds, and the
levers it can supply are the maps that are levers of every `a ∈ A` (`validLevers A`).

* **Soundness.** Every abscissa `a ≤ s` of the class is allowed by any collection of valid levers
  (`mem_allowed_of_mem`), so its wall below the seed `s` is at least `sup (A ∩ (-∞, s])`
  (`sSup_le_wall`).
* **Completeness.** The envelope `b ↦ sup (A ∩ (-∞, b])` is monotone and a lever of every world of
  the class (`monotone_envelope`, `envelope_mem_validLevers`). It allows exactly the least upper
  bounds of the abscissas below them (`le_envelope_iff`), so the wall of all valid levers, and of
  the monotone ones, is exactly `sup (A ∩ (-∞, s])` (`allowed_eq_of_envelope_mem`,
  `wall_validLevers`, `wall_monotone_validLevers`).
* **Decision.** The wall of a source class exceeds `h` iff the class has a world with abscissa in
  `(h, s]` (`lt_wall_validLevers_iff`); it equals a lower bound `h` of the class iff every world at
  or below the seed has abscissa `h` (`wall_validLevers_eq_iff`). The levers valid for one number
  pin it (`wall_validLevers_singleton`).
* **Frames.** A frame `(c, k)` with an estimate floor `σ₀` is a lever of `θ` iff
  `θ ≤ max σ₀ (c/(k − 1))` (`isLever_pairingStep_iff`, `isLever_flooredFrame_iff`): on a source
  class it is valid iff no world lies right of its level (`pairingStep_mem_validLevers_iff`).
* **The worlds of three structures.** Levers valid on the cosh models leave every seed where it is
  (`wall_eq_seed_of_coshModels`); levers valid on the Euler worlds leave every seed below `2/3`
  where it is (`min_two_thirds_le_wall_of_eulerWorlds`); levers valid on the shifted pairs leave
  every seed in `[Θ, Θ + ½)` where it is (`wall_eq_seed_of_shiftedPairs`).
-/

open Set

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open Zeta23 (ZeroConfig)
open GaloisForLFunctions.FamilyContinuationTheory (pairingStep)
open GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa (zeroAbscissa)
open GaloisForLFunctions.InfiniteRankWeilTheory (coshModel)
open _root_.RHTower (shiftedZetaPair zetaZeroAbscissa)

/-! ### 1. Source classes and soundness -/

/-- The maps that are levers of every abscissa of the class `A`. -/
def validLevers (A : Set ℝ) : Set (ℝ → ℝ) := {T | ∀ a ∈ A, IsLever a T}

/-- A larger class has fewer valid levers. -/
theorem validLevers_anti {A B : Set ℝ} (h : A ⊆ B) : validLevers B ⊆ validLevers A :=
  fun _ hT a ha => hT a (h ha)

/-- **Soundness.** An abscissa of the class at or below the seed is allowed by every collection of
valid levers. -/
theorem mem_allowed_of_mem {𝒯 : Set (ℝ → ℝ)} {A : Set ℝ} (hsub : 𝒯 ⊆ validLevers A) {a s : ℝ}
    (ha : a ∈ A) (has : a ≤ s) : a ∈ allowed 𝒯 s :=
  ⟨has, fun _ hT => (hsub hT a ha).le_apply_self⟩

theorem le_wall_of_mem {𝒯 : Set (ℝ → ℝ)} {A : Set ℝ} (hsub : 𝒯 ⊆ validLevers A) {a s : ℝ}
    (ha : a ∈ A) (has : a ≤ s) : a ≤ wall 𝒯 s :=
  le_csSup (bddAbove_allowed 𝒯 s) (mem_allowed_of_mem hsub ha has)

/-- A world of the class in `(h, s]` keeps the wall of every collection of valid levers above
`h`. -/
theorem lt_wall_of_mem {𝒯 : Set (ℝ → ℝ)} {A : Set ℝ} (hsub : 𝒯 ⊆ validLevers A) {a s h : ℝ}
    (ha : a ∈ A) (hha : h < a) (has : a ≤ s) : h < wall 𝒯 s :=
  hha.trans_le (le_wall_of_mem hsub ha has)

/-- The wall of valid levers is at least the supremum of the abscissas below the seed. -/
theorem sSup_le_wall {𝒯 : Set (ℝ → ℝ)} {A : Set ℝ} (hsub : 𝒯 ⊆ validLevers A) {s : ℝ}
    (hne : (A ∩ Iic s).Nonempty) : sSup (A ∩ Iic s) ≤ wall 𝒯 s :=
  csSup_le hne fun _ ha => le_wall_of_mem hsub ha.1 ha.2

/-! ### 2. The envelope and completeness -/

/-- The **envelope** of a class: the supremum of its abscissas at or below `b`. The point `b - 1`
makes the supremum exist for every `b` and changes no allowed value. -/
noncomputable def envelope (A : Set ℝ) (b : ℝ) : ℝ := sSup (insert (b - 1) (A ∩ Iic b))

private theorem envelopeSet_le {A : Set ℝ} {b x : ℝ} (hx : x ∈ insert (b - 1) (A ∩ Iic b)) :
    x ≤ b := by
  rcases hx with rfl | hx
  · linarith
  · exact hx.2

theorem envelope_le (A : Set ℝ) (b : ℝ) : envelope A b ≤ b :=
  csSup_le (insert_nonempty _ _) fun _ hx => envelopeSet_le hx

theorem le_envelope {A : Set ℝ} {a b : ℝ} (ha : a ∈ A) (hab : a ≤ b) : a ≤ envelope A b :=
  le_csSup ⟨b, fun _ hx => envelopeSet_le hx⟩ (mem_insert_of_mem _ ⟨ha, hab⟩)

theorem monotone_envelope (A : Set ℝ) : Monotone (envelope A) := by
  intro b b' hbb'
  refine csSup_le (insert_nonempty _ _) fun x hx => ?_
  rcases hx with rfl | hx
  · exact (sub_le_sub_right hbb' 1).trans
      (le_csSup ⟨b', fun _ hx => envelopeSet_le hx⟩ (mem_insert _ _))
  · exact le_envelope hx.1 (le_trans hx.2 hbb')

/-- The envelope is a lever of every world of the class. -/
theorem envelope_mem_validLevers (A : Set ℝ) : envelope A ∈ validLevers A :=
  fun _ ha _ hb => le_envelope ha hb

/-- **The envelope allows exactly the suprema of the class**: `b ≤ envelope A b` iff `b` is the
least upper bound of the abscissas at or below it. -/
theorem le_envelope_iff {A : Set ℝ} {b : ℝ} : b ≤ envelope A b ↔ IsLUB (A ∩ Iic b) b := by
  refine ⟨fun h => ⟨fun _ hx => hx.2, fun u hu => ?_⟩, fun h => h.2 fun a ha => le_envelope ha.1 ha.2⟩
  by_contra hub
  rw [not_le] at hub
  -- a bound `u < b` of the class gives the bound `max u (b - 1) < b` of the enlarged set
  have hmax : envelope A b ≤ max u (b - 1) := by
    refine csSup_le (insert_nonempty _ _) fun x hx => ?_
    rcases hx with rfl | hx
    · exact le_max_right _ _
    · exact (hu hx).trans (le_max_left _ _)
  exact absurd (h.trans hmax) (not_le.mpr (max_lt hub (by linarith)))

/-- **Completeness.** A collection of valid levers that contains the envelope allows exactly the
least upper bounds of the class below the seed. -/
theorem allowed_eq_of_envelope_mem {𝒯 : Set (ℝ → ℝ)} {A : Set ℝ} (hsub : 𝒯 ⊆ validLevers A)
    (henv : envelope A ∈ 𝒯) (s : ℝ) :
    allowed 𝒯 s = {b | b ≤ s ∧ IsLUB (A ∩ Iic b) b} := by
  ext b
  refine ⟨fun hb => ⟨hb.1, le_envelope_iff.1 (hb.2 _ henv)⟩, fun hb => ⟨hb.1, fun T hT => ?_⟩⟩
  -- every abscissa `a ≤ b` of the class lies below `T b`
  exact hb.2.2 fun a ha => hsub hT a ha.1 b ha.2

/-- **The wall of a source class is the largest abscissa it realizes below the seed.** -/
theorem wall_eq_of_envelope_mem {𝒯 : Set (ℝ → ℝ)} {A : Set ℝ} (hsub : 𝒯 ⊆ validLevers A)
    (henv : envelope A ∈ 𝒯) {s : ℝ} (hne : (A ∩ Iic s).Nonempty) :
    wall 𝒯 s = sSup (A ∩ Iic s) := by
  refine le_antisymm ?_ (sSup_le_wall hsub hne)
  obtain ⟨a, ha⟩ := hne
  refine csSup_le ⟨a, mem_allowed_of_mem hsub ha.1 ha.2⟩ fun b hb => ?_
  rw [allowed_eq_of_envelope_mem hsub henv] at hb
  exact hb.2.2 fun x hx => le_csSup ⟨s, fun _ hy => hy.2⟩ ⟨hx.1, le_trans hx.2 hb.1⟩

theorem wall_validLevers {A : Set ℝ} {s : ℝ} (hne : (A ∩ Iic s).Nonempty) :
    wall (validLevers A) s = sSup (A ∩ Iic s) :=
  wall_eq_of_envelope_mem Subset.rfl (envelope_mem_validLevers A) hne

/-- The monotone valid levers have the same wall. -/
theorem wall_monotone_validLevers {A : Set ℝ} {s : ℝ} (hne : (A ∩ Iic s).Nonempty) :
    wall {T | Monotone T ∧ T ∈ validLevers A} s = sSup (A ∩ Iic s) :=
  wall_eq_of_envelope_mem (𝒯 := {T | Monotone T ∧ T ∈ validLevers A}) (fun _ hT => hT.2)
    (And.intro (monotone_envelope A) (envelope_mem_validLevers A)) hne

/-! ### 3. The decision -/

private theorem bddAbove_inter_Iic (A : Set ℝ) (s : ℝ) : BddAbove (A ∩ Iic s) :=
  ⟨s, fun _ ha => ha.2⟩

/-- **Decision.** The wall of a source class exceeds `h` iff the class has a world with abscissa in
`(h, s]`. -/
theorem lt_wall_validLevers_iff {A : Set ℝ} {s h : ℝ} (hne : (A ∩ Iic s).Nonempty) :
    h < wall (validLevers A) s ↔ ∃ a ∈ A, h < a ∧ a ≤ s := by
  rw [wall_validLevers hne, lt_csSup_iff (bddAbove_inter_Iic A s) hne]
  exact ⟨fun ⟨a, ha, hha⟩ => ⟨a, ha.1, hha, ha.2⟩, fun ⟨a, ha, hha, has⟩ => ⟨a, ⟨ha, has⟩, hha⟩⟩

theorem wall_validLevers_le_iff {A : Set ℝ} {s h : ℝ} (hne : (A ∩ Iic s).Nonempty) :
    wall (validLevers A) s ≤ h ↔ ∀ a ∈ A, a ≤ s → a ≤ h := by
  rw [wall_validLevers hne, csSup_le_iff (bddAbove_inter_Iic A s) hne]
  exact ⟨fun H a ha has => H a ⟨ha, has⟩, fun H a ha => H a ha.1 ha.2⟩

/-- The wall of a source class is a lower bound `h` of the class iff every world at or below the
seed has abscissa `h`. -/
theorem wall_validLevers_eq_iff {A : Set ℝ} {s h : ℝ} (hne : (A ∩ Iic s).Nonempty)
    (hA : ∀ a ∈ A, h ≤ a) : wall (validLevers A) s = h ↔ ∀ a ∈ A, a ≤ s → a = h := by
  constructor
  · intro hw a ha has
    exact le_antisymm ((wall_validLevers_le_iff hne).1 hw.le a ha has) (hA a ha)
  · intro H
    obtain ⟨a, ha⟩ := hne
    refine le_antisymm ((wall_validLevers_le_iff ⟨a, ha⟩).2 fun x hx hxs => (H x hx hxs).le) ?_
    exact (H a ha.1 ha.2).ge.trans (le_wall_of_mem Subset.rfl ha.1 ha.2)

/-- **The levers valid for one number pin it.** -/
theorem wall_validLevers_singleton {θ s : ℝ} (h : θ ≤ s) : wall (validLevers {θ}) s = θ := by
  have hset : ({θ} : Set ℝ) ∩ Iic s = {θ} := inter_eq_left.2 (singleton_subset_iff.2 h)
  rw [wall_validLevers (by rw [hset]; exact singleton_nonempty θ), hset, csSup_singleton]

/-! ### 4. Frames on a source class -/

/-- A frame `(c, k)` is a lever of `θ` iff `θ` is at most its centre `c/(k − 1)`. -/
theorem isLever_pairingStep_iff {c k θ : ℝ} (hk : 1 < k) :
    IsLever θ (pairingStep c k) ↔ θ ≤ c / (k - 1) := by
  rw [isLever_iff_le_apply_self (monotone_pairingStep (by linarith)), pairingStep,
    le_div_iff₀ (by linarith), le_div_iff₀ (by linarith)]
  constructor <;> intro h <;> linarith

/-- A frame with an estimate floor `σ₀` is a lever of `θ` iff `θ ≤ max σ₀ (c/(k − 1))`. -/
theorem isLever_flooredFrame_iff {c k σ₀ θ : ℝ} (hk : 1 < k) :
    IsLever θ (fun b => max σ₀ (pairingStep c k b)) ↔ θ ≤ max σ₀ (c / (k - 1)) := by
  have hstep : Monotone (pairingStep c k) := monotone_pairingStep (by linarith)
  have hmono : Monotone fun b => max σ₀ (pairingStep c k b) := fun _ _ hab =>
    max_le_max le_rfl (hstep hab)
  rw [isLever_iff_le_apply_self hmono, le_max_iff, le_max_iff]
  exact or_congr Iff.rfl ((isLever_iff_le_apply_self hstep).symm.trans (isLever_pairingStep_iff hk))

/-- **A frame is valid on a source class iff no world lies right of its centre.** -/
theorem pairingStep_mem_validLevers_iff {A : Set ℝ} {c k : ℝ} (hk : 1 < k) :
    pairingStep c k ∈ validLevers A ↔ ∀ a ∈ A, a ≤ c / (k - 1) :=
  forall₂_congr fun _ _ => isLever_pairingStep_iff hk

/-! ### 5. The worlds of three structures -/

/-- **Functional equations alone move no seed.** Levers valid on the cosh models have wall `s`
below every seed `s ≥ ½`. -/
theorem wall_eq_seed_of_coshModels {𝒯 : Set (ℝ → ℝ)}
    (h : ∀ T ∈ 𝒯, ∀ Q : Finset ℂ, IsLever (zeroSupRe (coshModel Q)) T) {s : ℝ}
    (hs : 1 / 2 ≤ s) : wall 𝒯 s = s := by
  have hmem : s ∈ allowed 𝒯 s :=
    ⟨le_rfl, fun T hT => le_apply_of_isLever_coshModels (h T hT) hs⟩
  exact le_antisymm (csSup_le ⟨s, hmem⟩ fun _ hb => hb.1) (le_csSup (bddAbove_allowed 𝒯 s) hmem)

/-- **Euler products alone move no seed below `2/3`.** Levers valid on the Euler worlds have wall
at least `min s (2/3)` below every seed `s > ½`. -/
theorem min_two_thirds_le_wall_of_eulerWorlds {𝒯 : Set (ℝ → ℝ)}
    (h : ∀ T ∈ 𝒯, ∀ Z : ZeroConfig, IsEulerWorld Z → IsLever (zeroAbscissa Z) T) {s : ℝ}
    (hs : 1 / 2 < s) : min s (2 / 3) ≤ wall 𝒯 s := by
  refine le_of_forall_lt fun x hx => ?_
  -- an abscissa of an Euler world between `x` and `min s (2/3)` is allowed
  obtain ⟨b, hb1, hb2⟩ := exists_between (max_lt hx (lt_min hs (by norm_num : (1 / 2 : ℝ) < 2 / 3)))
  have hb : b ∈ Ioo (1 / 2 : ℝ) (2 / 3) :=
    ⟨(le_max_right _ _).trans_lt hb1, hb2.trans_le (min_le_right _ _)⟩
  exact ((le_max_left _ _).trans_lt hb1).trans_le (le_csSup (bddAbove_allowed 𝒯 s)
    ⟨hb2.le.trans (min_le_left _ _), fun T hT => le_apply_of_isLever_eulerWorlds (h T hT) hb⟩)

/-- **Without the Ramanujan bound no seed above the zeros moves.** Levers valid on the shifted
pairs `ζ(s − a) ζ(s + a)` have wall `s` below every seed `s ∈ [Θ, Θ + ½)`. -/
theorem wall_eq_seed_of_shiftedPairs {𝒯 : Set (ℝ → ℝ)}
    (h : ∀ T ∈ 𝒯, ∀ a ∈ Ico (0 : ℝ) (1 / 2), IsLever (zeroSupRe (shiftedZetaPair a)) T) {s : ℝ}
    (hs : s ∈ Ico zetaZeroAbscissa (zetaZeroAbscissa + 1 / 2)) : wall 𝒯 s = s := by
  have hmem : s ∈ allowed 𝒯 s :=
    ⟨le_rfl, fun T hT => le_apply_of_isLever_shiftedPairs (h T hT) hs⟩
  exact le_antisymm (csSup_le ⟨s, hmem⟩ fun _ hb => hb.1) (le_csSup (bddAbove_allowed 𝒯 s) hmem)

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
