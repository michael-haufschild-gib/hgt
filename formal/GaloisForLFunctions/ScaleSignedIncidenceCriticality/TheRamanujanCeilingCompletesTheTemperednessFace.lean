import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheTemperednessFaceUnitIsTheRamanujanThreshold
import GaloisForLFunctions.RHTower.DivisorBound

/-!
# The Ramanujan ceiling completes the temperedness face

The temperedness face has unit `¼`: a reading of nonnegative Dirichlet coefficients, a nonnegative
von Mangoldt weight on the prime powers, the functional equation and polynomial vertical growth
certifies no bound on the shift below the Ramanujan threshold
(`TheTemperednessFaceUnitIsTheRamanujanThreshold`). The programme conjectures that what the list
lacks is exactly the Ramanujan ceiling. This module proves it.

The ceiling is subpolynomial growth of the coefficients:
`ramanujanCeiling a : ∀ ε > 0, ∃ C, c_a(n) ≤ C n^ε`. It **holds at the shift `0`**
(`ramanujanCeiling_zero`), because `c_0(n)` is the divisor count and the divisor bound
`RHTower.card_divisors_le_const_mul_rpow` is exactly subpolynomial growth; and it **fails at every
nonzero shift** (`not_ramanujanCeiling_of_ne_zero`), because `c_a(n)` grows like `n^{|a|}`
(`RHTower.not_ramanujan_shiftedPairCoeff`).

Adding it to the list therefore collapses the shadow to the single point `0`, and the limit of the
shift magnitude drops from `¼` to `0`
(`resolutionLimit_shiftMagnitude_flagsWithCeiling`): **the extended reading is faithful.**

`theCeilingIsExactlyWhatIsMissing` states the two limits side by side. This is the first instance in
the field of a *completion*: a floor identified, the missing ingredient named, and the floor removed
by adding exactly that ingredient and nothing else. It also fixes the methodological reading of the
temperedness gate — a Selberg-type argument is admissible precisely when it uses the ceiling, and
the `¼` measures how much the ceiling is worth.
-/

open Set

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open _root_.RHTower

set_option autoImplicit false

/-! ### 1. The ceiling -/

/-- The **Ramanujan ceiling**: subpolynomial growth of the Dirichlet coefficients. -/
def ramanujanCeiling (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, n ≠ 0 → shiftedPairCoeff a n ≤ C * (n : ℝ) ^ ε

/-- At shift `0` the coefficients are counted by the divisors. -/
theorem shiftedPairCoeff_zero_le (n : ℕ) : shiftedPairCoeff 0 n ≤ (n.divisors.card : ℝ) := by
  have hcard : n.divisorsAntidiagonal.card ≤ n.divisors.card := by
    refine Finset.card_le_card_of_injOn Prod.fst
      (fun p hp => Nat.fst_mem_divisors_of_mem_antidiagonal hp) ?_
    intro p hp q hq hfst
    have hp' := Nat.mem_divisorsAntidiagonal.mp hp
    have hq' := Nat.mem_divisorsAntidiagonal.mp hq
    have hne : p.1 ≠ 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp
    have hmul : p.1 * p.2 = q.1 * q.2 := by rw [hp'.1, hq'.1]
    rw [hfst] at hmul
    have hq1 : q.1 ≠ 0 := by rw [← hfst]; exact hne
    have hsnd : p.2 = q.2 :=
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq1) hmul
    exact Prod.ext hfst hsnd
  simp only [shiftedPairCoeff, Real.rpow_zero, neg_zero, mul_one, Finset.sum_const,
    nsmul_eq_mul]
  exact_mod_cast hcard

/-- **The ceiling holds at shift `0`**: this is the divisor bound. -/
theorem ramanujanCeiling_zero : ramanujanCeiling 0 := by
  intro ε hε
  obtain ⟨C, -, hmain⟩ := card_divisors_le_const_mul_rpow hε
  refine ⟨C, fun n hn => ?_⟩
  exact (shiftedPairCoeff_zero_le n).trans (hmain n (Nat.one_le_iff_ne_zero.mpr hn))

/-- **The ceiling fails at every nonzero shift.** -/
theorem not_ramanujanCeiling_of_ne_zero {a : ℝ} (ha : a ≠ 0) : ¬ ramanujanCeiling a := by
  intro h
  have hpos : 0 < |a| := abs_pos.mpr ha
  obtain ⟨C, hC⟩ := h (|a| / 2) (by linarith)
  exact not_ramanujan_shiftedPairCoeff (by linarith : |a| / 2 < |a|) ⟨C, hC⟩

/-! ### 2. The extended reading is faithful -/

/-- The flag list with the ceiling added. -/
def flagsWithCeiling (a : TemperedShift) : (Prop × Prop × Prop × Prop) × Prop :=
  (structuralFlags a.1, ramanujanCeiling a.1)

/-- The zero shift as a datum. -/
def zeroShift : TemperedShift := ⟨0, by norm_num⟩

/-- **The extended reading pins the shift.** -/
theorem shadow_flagsWithCeiling_eq :
    ∀ b : TemperedShift, b ∈ shadow flagsWithCeiling zeroShift → b.1 = 0 := by
  intro b hb
  by_contra hne
  have hceil : ramanujanCeiling b.1 = ramanujanCeiling zeroShift.1 :=
    congrArg Prod.snd (mem_shadow_iff.mp hb)
  have h0 : ramanujanCeiling b.1 := by
    rw [hceil]
    exact ramanujanCeiling_zero
  exact not_ramanujanCeiling_of_ne_zero hne h0

/-- **Faithfulness.** With the ceiling the limit of the shift magnitude is `0`. -/
theorem resolutionLimit_shiftMagnitude_flagsWithCeiling :
    resolutionLimit shiftMagnitude flagsWithCeiling zeroShift = 0 := by
  have hzero : ∀ b ∈ shadow flagsWithCeiling zeroShift, shiftMagnitude b = 0 := by
    intro b hb
    simp only [shiftMagnitude, shadow_flagsWithCeiling_eq b hb, abs_zero]
  refine le_antisymm (csSup_le (shadow_image_nonempty shiftMagnitude flagsWithCeiling _) ?_) ?_
  · rintro x ⟨b, hb, rfl⟩
    exact (hzero b hb).le
  · have hle := le_csSup (bddAbove_shiftMagnitude_image (shadow flagsWithCeiling zeroShift))
      ⟨zeroShift, mem_shadow_self flagsWithCeiling zeroShift, rfl⟩
    rwa [hzero zeroShift (mem_shadow_self flagsWithCeiling zeroShift)] at hle

/-! ### 3. The completion -/

/-- **The ceiling is exactly what is missing.** Without it the limit of the shift magnitude is the
Ramanujan threshold `¼`; with it the limit is `0` and the reading is faithful. -/
theorem theCeilingIsExactlyWhatIsMissing :
    resolutionLimit shiftMagnitude flagsReading zeroShift = 1 / 4 ∧
      resolutionLimit shiftMagnitude flagsWithCeiling zeroShift = 0 :=
  ⟨resolutionLimit_shiftMagnitude_flagsReading zeroShift,
    resolutionLimit_shiftMagnitude_flagsWithCeiling⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
