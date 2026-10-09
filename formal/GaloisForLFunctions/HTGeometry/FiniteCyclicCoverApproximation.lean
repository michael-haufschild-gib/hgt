import GaloisForLFunctions.HTGeometry.InfinitePacketObstruction
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

open Filter Function

namespace GaloisForLFunctions.HTGeometry.FiniteCyclicCoverApproximation
open InfinitePacketObstruction

abbrev Sheets (n : ℕ) := Option (ZMod (n + 1))

def finiteShifts (n : ℕ) : Multiplicative (ZMod (n + 1)) →* Equiv.Perm (Sheets n) where
  toFun k := Equiv.optionCongr (Equiv.addRight k.toAdd)
  map_one' := by ext j; cases j <;> simp [Equiv.optionCongr]
  map_mul' a b := by ext j; cases j <;> simp [Equiv.optionCongr, add_comm, add_left_comm]

def finiteAction (n : ℕ) : Words →* Equiv.Perm (Sheets n) :=
  FreeGroup.lift fun b => if b then Equiv.swap none (some 0)
    else finiteShifts n (Multiplicative.ofAdd 1)

instance (n : ℕ) : MulAction Words (Sheets n) := MulAction.compHom (Sheets n) (finiteAction n)

def finiteStabilizer (n : ℕ) : Subgroup Words := MulAction.stabilizer Words (none : Sheets n)

def reduceSheet (n : ℕ) : Option ℤ → Sheets n := Option.map Int.cast

@[simp] theorem mem_finiteStabilizer (n : ℕ) (g : Words) :
    g ∈ finiteStabilizer n ↔ finiteAction n g none = none := Iff.rfl

@[simp] theorem finiteAction_x (n : ℕ) :
    finiteAction n x = finiteShifts n (Multiplicative.ofAdd 1) := by
  simp [finiteAction, x]

@[simp] theorem finiteAction_y (n : ℕ) :
    finiteAction n y = Equiv.swap none (some 0) := by simp [finiteAction, y]

@[simp] theorem finiteAction_x_zpow_some (n : ℕ) (k : ℤ) (j : ZMod (n + 1)) :
    finiteAction n (x ^ k) (some j) = some (j + (k : ZMod (n + 1))) := by
  rw [map_zpow, finiteAction_x, ← map_zpow]
  change some (j + ((Multiplicative.ofAdd 1 : Multiplicative (ZMod (n + 1))) ^ k).toAdd) = _
  rw [← ofAdd_zsmul]
  simp

@[simp] theorem finiteAction_x_zpow_none (n : ℕ) (k : ℤ) :
    finiteAction n (x ^ k) none = none := by
  rw [map_zpow, finiteAction_x, ← map_zpow]
  rfl

/-- The finite model has one distinguished coset and one growing cyclic orbit. -/
noncomputable def finiteCosetEquiv (n : ℕ) : (Words ⧸ finiteStabilizer n) ≃ Sheets n :=
  Equiv.ofBijective (MulAction.ofQuotientStabilizer Words (none : Sheets n))
    ⟨MulAction.injective_ofQuotientStabilizer Words none, by
      intro z
      cases z with
      | none => exact ⟨QuotientGroup.mk 1, rfl⟩
      | some j =>
        obtain ⟨k, rfl⟩ := ZMod.intCast_surjective j
        refine ⟨QuotientGroup.mk (x ^ k * y), ?_⟩
        change finiteAction n (x ^ k * y) none = some (k : ZMod (n + 1))
        rw [map_mul, Equiv.Perm.mul_apply, finiteAction_y, Equiv.swap_apply_left,
          finiteAction_x_zpow_some, zero_add]⟩

/-- Every approximating stabilizer has exactly n+2 cosets. -/
theorem card_finiteCosets (n : ℕ) : Nat.card (Words ⧸ finiteStabilizer n) = n + 2 := by
  rw [Nat.card_congr (finiteCosetEquiv n)]
  simp [Sheets, Nat.card_eq_fintype_card, Fintype.card_option, ZMod.card, Nat.add_assoc]

/-- No finite approximant is the full free group. -/
theorem finiteStabilizer_ne_top (n : ℕ) : finiteStabilizer n ≠ ⊤ := by
  intro h
  have hy : y ∈ finiteStabilizer n := h.symm ▸ Subgroup.mem_top y
  simp [mem_finiteStabilizer] at hy

private theorem eventually_intCast_ne_zero {j : ℤ} (hj : j ≠ 0) :
    ∀ᶠ n : ℕ in atTop, (j : ZMod (n + 1)) ≠ 0 := by
  filter_upwards [eventually_ge_atTop j.natAbs] with n hn
  intro hz
  have hd : n + 1 ∣ j.natAbs :=
    Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd j (n + 1)).mp hz)
  have hh := Nat.le_of_dvd (Int.natAbs_pos.mpr hj) hd
  omega

private theorem reduce_x_zpow (n : ℕ) (k : ℤ) (s : Option ℤ) :
    finiteAction n (x ^ k) (reduceSheet n s) = reduceSheet n (action (x ^ k) s) := by
  cases s <;> simp only [reduceSheet, Option.map_none, Option.map_some,
    finiteAction_x_zpow_none, finiteAction_x_zpow_some, action_x_zpow_none,
    action_x_zpow_some, Int.cast_add]

private theorem eventually_reduce_y (s : Option ℤ) :
    ∀ᶠ n : ℕ in atTop, finiteAction n y (reduceSheet n s) = reduceSheet n (action y s) := by
  cases s with
  | none => exact Eventually.of_forall (fun n => by simp [reduceSheet])
  | some j =>
    by_cases hj : j = 0
    · subst j
      exact Eventually.of_forall (fun n => by simp [reduceSheet])
    · filter_upwards [eventually_intCast_ne_zero hj] with n hn
      simp [reduceSheet, Equiv.swap_apply_of_ne_of_ne, hj, hn]

/-- Every fixed word and sheet have eventually exact reduction-compatible action. -/
theorem eventually_action_reduce (g : Words) (s : Option ℤ) :
    ∀ᶠ n : ℕ in atTop,
      finiteAction n g (reduceSheet n s) = reduceSheet n (action g s) := by
  induction g using FreeGroup.induction_on generalizing s with
  | C1 => simp
  | of b =>
    cases b with
    | false =>
      simpa only [x, zpow_one] using Eventually.of_forall (fun n => reduce_x_zpow n 1 s)
    | true => exact eventually_reduce_y s
  | inv_of b _ =>
    cases b with
    | false =>
      simpa only [x, zpow_neg_one] using Eventually.of_forall (fun n => reduce_x_zpow n (-1) s)
    | true =>
      filter_upwards [eventually_reduce_y s] with n hn
      simpa [finiteAction, action, y, Equiv.Perm.inv_def] using hn
  | mul g h hg hh =>
    filter_upwards [hh s, hg (action h s)] with n hn₁ hn₂
    simp only [map_mul, Equiv.Perm.mul_apply]
    rw [hn₁, hn₂]

/-- Stabilizer membership converges exactly for each fixed free-group word. -/
theorem eventually_mem_finiteStabilizer_iff (g : Words) :
    ∀ᶠ n : ℕ in atTop, g ∈ finiteStabilizer n ↔ g ∈ stabilizer := by
  filter_upwards [eventually_action_reduce g none] with n hn
  rw [mem_finiteStabilizer, mem_stabilizer]
  change finiteAction n g (reduceSheet n none) = none ↔ action g none = none
  rw [hn]
  cases action g none <;> simp [reduceSheet]

/-- Every finite collection of words is eventually classified exactly as in the infinite model. -/
theorem eventually_finite_word_membership (T : Finset Words) :
    ∀ᶠ n : ℕ in atTop, ∀ g ∈ T, g ∈ finiteStabilizer n ↔ g ∈ stabilizer := by
  have he (g : T) := eventually_mem_finiteStabilizer_iff g.val
  filter_upwards [Filter.eventually_all.mpr he] with n hn
  exact fun g hg => hn ⟨g, hg⟩

/-- Every fixed finite quotient eventually sees the entire image despite every approximant
being proper with growing index. The cutoff depends on the quotient. -/
theorem eventually_finite_image_eq_range {Q : Type*} [Group Q] [Finite Q] (q : Words →* Q) :
    ∀ᶠ n : ℕ in atTop, (finiteStabilizer n).map q = q.range := by
  have he (a : q.range) : ∀ᶠ n : ℕ in atTop, a.val ∈ (finiteStabilizer n).map q := by
    have ha : a.val ∈ stabilizer.map q :=
      (finite_image_stabilizer_eq_range q).symm ▸ a.property
    obtain ⟨g, hg, hga⟩ := ha
    filter_upwards [eventually_mem_finiteStabilizer_iff g] with n hn
    exact ⟨g, hn.mpr hg, hga⟩
  filter_upwards [Filter.eventually_all.mpr he] with n hn
  apply le_antisymm
  · rintro a ⟨g, _, rfl⟩
    exact ⟨g, rfl⟩
  · intro a ha
    exact hn ⟨a, ha⟩

end GaloisForLFunctions.HTGeometry.FiniteCyclicCoverApproximation
