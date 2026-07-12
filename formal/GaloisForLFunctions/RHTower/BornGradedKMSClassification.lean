import GaloisForLFunctions.RHTower.BornEtaGrading

/-!
# Graded phase classification of the doubled-rung Born system

In the half-dilated gauge (`log √n` Hamiltonian) the doubled-rung welded system carries two
sector presentations: the parity-graded order sector and the half-integer disorder sector.
This module classifies their convergence walls and the action of the two temperature
involutions on the phase labels.

* Both ungraded Gibbs walls sit at `β = 2`: the integer trace `∑(n+1)^{-β/2}` and the
  half-integer trace `∑(m+1/2)^{-β/2}` are summable exactly for `β > 2`.
* Throughout the high-temperature phase `0 < β ≤ 2` the parity supertrace converges while
  the ungraded trace diverges: the strip KMS datum of the order sector is intrinsically
  graded.
* For any labelling obeying the published Bost–Connes diagram in this gauge (one factor
  label on `0 < β ≤ 2`, a different one on `β > 2`): the **sector-swap** reflection
  `β ↦ 2-β` never leaves the high-temperature label — the Kramers–Wannier involution acts
  within the `III₁` phase; the **KMS** reflection of the gauge, `β ↦ 4-β`, matches labels
  exactly at its fixed point `2`, the wall; and the **unit tower shift** `β ↦ β+2` — the
  difference of the two reflections — always crosses the wall.  The involution's action on
  the `III₁`/type-I pair is therefore: swap preserves the phase, shift crosses it, and the
  KMS reflection is their composite.
-/

noncomputable section

namespace RHTower

/-! ## The convergence walls -/

/-- The ungraded Gibbs weights of the half-dilated system are summable exactly at low
temperature: `∑ (n+1)^{-β/2} < ∞ ↔ β > 2`. -/
theorem summable_halfDilatedWeight_iff (β : ℝ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(β / 2))) ↔ 2 < β := by
  constructor
  · intro h
    have hc : Summable (fun m : ℕ => (((m + 1 : ℕ)) : ℝ) ^ (-(β / 2))) :=
      h.congr fun m => by
        congr 1
        push_cast
        ring
    have := Real.summable_nat_rpow.mp
      ((summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(β / 2))) 1).mp hc)
    linarith
  · intro hβ
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(β / 2))) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hc := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(β / 2))) 1).mpr hbase
    exact hc.congr fun m => by
      congr 1
      push_cast
      ring

/-- The disorder (half-integer) Gibbs weights are summable exactly at low temperature:
`∑ (m+1/2)^{-β/2} < ∞ ↔ β > 2` — the same wall as the integer trace, one tower rung up. -/
theorem summable_halfLevelWeight_iff (β : ℝ) :
    Summable (fun m : ℕ => ((m : ℝ) + 1 / 2) ^ (-(β / 2))) ↔ 2 < β := by
  constructor
  · intro h
    by_contra hle
    rw [not_lt] at hle
    rcases le_or_gt β 0 with hb0 | hb0
    · have hzero := h.tendsto_atTop_zero
      have hone : ∀ᶠ m : ℕ in Filter.atTop,
          (1 : ℝ) ≤ ((m : ℝ) + 1 / 2) ^ (-(β / 2)) := by
        filter_upwards [Filter.eventually_ge_atTop 1] with m hm
        apply Real.one_le_rpow
        · have h1m : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          linarith
        · linarith
      have := ge_of_tendsto hzero hone
      linarith
    · have hcomp : ∀ m : ℕ,
          ((m : ℝ) + 1) ^ (-(β / 2)) ≤ ((m : ℝ) + 1 / 2) ^ (-(β / 2)) := by
        intro m
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
      have hsum1 : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(β / 2))) :=
        Summable.of_nonneg_of_le (fun m => by positivity) hcomp h
      exact absurd ((summable_halfDilatedWeight_iff β).mp hsum1) (by linarith)
  · intro hβ
    have hbase : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(β / 2))) :=
      (summable_halfDilatedWeight_iff β).mpr hβ
    have hmaj : ∀ m : ℕ, ((m : ℝ) + 1 / 2) ^ (-(β / 2))
        ≤ (2 : ℝ) ^ (β / 2) * ((m : ℝ) + 1) ^ (-(β / 2)) := by
      intro m
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have h1 : ((m : ℝ) + 1) / 2 ≤ (m : ℝ) + 1 / 2 := by linarith
      have h2 : ((m : ℝ) + 1 / 2) ^ (-(β / 2)) ≤ (((m : ℝ) + 1) / 2) ^ (-(β / 2)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
      refine h2.trans_eq ?_
      rw [Real.div_rpow (by positivity) (by norm_num),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv, inv_inv, mul_comm]
    exact Summable.of_nonneg_of_le (fun m => by positivity) hmaj (hbase.mul_left _)

/-- **The graded datum lives beyond the ungraded wall**: throughout the high-temperature
phase `0 < β ≤ 2` the parity supertrace of the half-dilated system converges while its
Gibbs trace diverges.  The strip KMS data of the order sector is intrinsically graded. -/
theorem gradedOrder_beyond_wall {β : ℝ} (h0 : 0 < β) (h2 : β ≤ 2) :
    Summable (bornSupertraceTerm β)
      ∧ ¬ Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(β / 2))) :=
  ⟨summable_bornSupertraceTerm h0,
    fun h => absurd ((summable_halfDilatedWeight_iff β).mp h) (by linarith)⟩

/-! ## The involution's action on the phase labels

The published Bost–Connes classification enters, as everywhere in this development, only as
a hypothesis on an abstract label function: one fixed value on the high-temperature range
`0 < β ≤ 2` of the half-dilated gauge (unique KMS state, type `III₁`), a different fixed
value on the low-temperature range `β > 2` (extremal type-I Gibbs sectors, which exist there
by `summable_halfDilatedWeight_iff`). -/

/-- **The sector swap acts within the high-temperature phase**: for `0 < β < 2` both members
of the swapped pair `(β, 2-β)` carry the high-temperature label.  The Kramers–Wannier
involution never reaches the type-I phase. -/
theorem label_sectorSwap_within_highTemp {T : Type*} (label : ℝ → T) (tHigh : T)
    (hHigh : ∀ β : ℝ, 0 < β → β ≤ 2 → label β = tHigh)
    {β : ℝ} (h0 : 0 < β) (h2 : β < 2) :
    label β = tHigh ∧ label (2 - β) = tHigh :=
  ⟨hHigh β h0 (by linarith), hHigh (2 - β) (by linarith) (by linarith)⟩

/-- **The KMS reflection crosses the wall at its fixed point.**  The Born-forced state
reflection of the half-dilated gauge is `β ↦ 4-β` with fixed point `2` — exactly the
partition wall; the labels of a reflected pair match iff `β = 2`. -/
theorem label_bornReflect_eq_iff {T : Type*} (label : ℝ → T) (tHigh tLow : T)
    (hne : tHigh ≠ tLow)
    (hHigh : ∀ β : ℝ, 0 < β → β ≤ 2 → label β = tHigh)
    (hLow : ∀ β : ℝ, 2 < β → label β = tLow)
    {β : ℝ} (h0 : 0 < β) (h4 : β < 4) :
    label β = label (4 - β) ↔ β = 2 := by
  constructor
  · intro h
    by_contra hne2
    rcases lt_or_gt_of_ne hne2 with hlt | hgt
    · rw [hHigh β h0 hlt.le, hLow (4 - β) (by linarith)] at h
      exact hne h
    · rw [hLow β hgt, hHigh (4 - β) (by linarith) (by linarith)] at h
      exact hne h.symm
  · rintro rfl
    norm_num

/-- **The unit tower shift is the phase-crossing operator**: on the high-temperature phase
it always changes the label.  Since `4 - β = (2 - β) + 2`, the KMS reflection is the sector
swap followed by the tower shift: the swap preserves the phase, the shift crosses it. -/
theorem label_towerShift_ne {T : Type*} (label : ℝ → T) (tHigh tLow : T)
    (hne : tHigh ≠ tLow)
    (hHigh : ∀ β : ℝ, 0 < β → β ≤ 2 → label β = tHigh)
    (hLow : ∀ β : ℝ, 2 < β → label β = tLow)
    {β : ℝ} (h0 : 0 < β) (h2 : β ≤ 2) :
    label β ≠ label (β + 2) := by
  rw [hHigh β h0 h2, hLow (β + 2) (by linarith)]
  exact hne

end RHTower
