import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniContactFourthCumulant

/-!
# Sharp one-orbit orientation law for degree-one Cassini contact

Normalize one positive real reciprocal atom to `c` and one conjugate reciprocal pair to
`1 ± s i`.  Let `q` be the total weight of the pair.  The unique positive weight which makes the
first shifted Hankel minor flat is

`q = c C / ((1 + s^2) s^2)`,

where

`C = c^2 + 2 (s^2 - 1) c + 1 - 3 s^2`.

At that contact, the terminal flux has the exact factorization

`c C ((c - 1)^2 + s^2) / (c - 1 + s^2)`.

Consequently its orientation is not controlled by angular sector width.  For positive `c,C`, the
sign is exactly the sign of `c - 1 + s^2`: relative radial scale is the missing coordinate.

The exact packet `c=1/2`, `s=1/6`, with common conjugate-atom weight `63/37`, lies in the narrow
sector `|Im z| = Re z / 6`, has a flat first minor, and has terminal flux `-35/612`.  This rules out
every degree-one closure using only contact, positivity of the first four moments, and the Xi
sector chamber.  A successful source theorem must control cross-scale mass transport.
-/

open Complex

namespace RHTower

noncomputable section

/-- Normalized nonreal reciprocal atom used in the one-orbit contact model. -/
def cassiniOneOrbitAtom (s : ℝ) : ℂ :=
  1 + (s : ℂ) * I

/-- Shifted moment of one real atom of weight one and one conjugate pair of total weight `q`. -/
def cassiniOneOrbitMoment (c s q : ℝ) (n : ℕ) : ℝ :=
  c ^ (n + 1) + q * (cassiniOneOrbitAtom s ^ (n + 1)).re

/-- Cross term whose positivity makes the flat-contact pair weight positive. -/
def cassiniOneOrbitContactCross (c s : ℝ) : ℝ :=
  c ^ 2 + 2 * (s ^ 2 - 1) * c + 1 - 3 * s ^ 2

/-- Total conjugate-pair weight producing exact degree-one contact. -/
def cassiniOneOrbitContactWeight (c s : ℝ) : ℝ :=
  c * cassiniOneOrbitContactCross c s / ((1 + s ^ 2) * s ^ 2)

/-- Null root selected by the exact contact packet. -/
def cassiniOneOrbitContactNullRoot (c s : ℝ) : ℝ :=
  ((c - 1) + (3 - c) * s ^ 2) / (c - 1 + s ^ 2)

/-- First shifted Hankel minor of the normalized one-orbit packet. -/
def cassiniOneOrbitMinor (c s q : ℝ) : ℝ :=
  cassiniOneOrbitMoment c s q 0 * cassiniOneOrbitMoment c s q 2 -
    cassiniOneOrbitMoment c s q 1 ^ 2

/-- Degree-one first-omitted pairing evaluated at the moment-selected null root. -/
def cassiniOneOrbitTerminalFlux (c s q : ℝ) : ℝ :=
  let r := cassiniOneOrbitMoment c s q 1 / cassiniOneOrbitMoment c s q 0
  cassiniOneOrbitMoment c s q 3 -
    2 * r * cassiniOneOrbitMoment c s q 2 +
      r ^ 2 * cassiniOneOrbitMoment c s q 1

theorem cassiniOneOrbitMoment_zero (c s q : ℝ) :
    cassiniOneOrbitMoment c s q 0 = c + q := by
  simp [cassiniOneOrbitMoment, cassiniOneOrbitAtom]

private theorem cassiniOneOrbitAtom_sq_re (s : ℝ) :
    (cassiniOneOrbitAtom s ^ 2).re = 1 - s ^ 2 := by
  norm_num [cassiniOneOrbitAtom, pow_succ, Complex.mul_re, Complex.mul_im]

private theorem cassiniOneOrbitAtom_cube_re (s : ℝ) :
    (cassiniOneOrbitAtom s ^ 3).re = 1 - 3 * s ^ 2 := by
  norm_num [cassiniOneOrbitAtom, pow_succ, Complex.mul_re, Complex.mul_im]
  ring

private theorem cassiniOneOrbitAtom_fourth_re (s : ℝ) :
    (cassiniOneOrbitAtom s ^ 4).re = 1 - 6 * s ^ 2 + s ^ 4 := by
  norm_num [cassiniOneOrbitAtom, pow_succ, Complex.mul_re, Complex.mul_im]
  ring

theorem cassiniOneOrbitMoment_one (c s q : ℝ) :
    cassiniOneOrbitMoment c s q 1 = c ^ 2 + q * (1 - s ^ 2) := by
  rw [cassiniOneOrbitMoment, cassiniOneOrbitAtom_sq_re]

theorem cassiniOneOrbitMoment_two (c s q : ℝ) :
    cassiniOneOrbitMoment c s q 2 = c ^ 3 + q * (1 - 3 * s ^ 2) := by
  rw [cassiniOneOrbitMoment, cassiniOneOrbitAtom_cube_re]

theorem cassiniOneOrbitMoment_three (c s q : ℝ) :
    cassiniOneOrbitMoment c s q 3 =
      c ^ 4 + q * (1 - 6 * s ^ 2 + s ^ 4) := by
  rw [cassiniOneOrbitMoment, cassiniOneOrbitAtom_fourth_re]

/-- The displayed weight makes the first shifted minor exactly flat. -/
theorem cassiniOneOrbitMinor_contactWeight_eq_zero
    {c s : ℝ} (hs : s ≠ 0) :
    cassiniOneOrbitMinor c s (cassiniOneOrbitContactWeight c s) = 0 := by
  have hone : 1 + s ^ 2 ≠ 0 := by nlinarith [sq_nonneg s]
  rw [cassiniOneOrbitMinor, cassiniOneOrbitMoment_zero,
    cassiniOneOrbitMoment_one, cassiniOneOrbitMoment_two,
    cassiniOneOrbitContactWeight, cassiniOneOrbitContactCross]
  field_simp [hs, hone]
  ring

private theorem cassiniOneOrbitMoment_zero_contactWeight_eq
    {c s : ℝ} (hs : s ≠ 0) :
    cassiniOneOrbitMoment c s (cassiniOneOrbitContactWeight c s) 0 =
      c * (c - 1 + s ^ 2) ^ 2 / ((1 + s ^ 2) * s ^ 2) := by
  have hone : 1 + s ^ 2 ≠ 0 := by nlinarith [sq_nonneg s]
  rw [cassiniOneOrbitMoment_zero, cassiniOneOrbitContactWeight,
    cassiniOneOrbitContactCross]
  field_simp [hs, hone]
  ring

private theorem cassiniOneOrbitMoment_one_contactWeight_eq
    {c s : ℝ} (hs : s ≠ 0) :
    cassiniOneOrbitMoment c s (cassiniOneOrbitContactWeight c s) 1 =
      c * (c - 1 + s ^ 2) * ((c - 1) + (3 - c) * s ^ 2) /
        ((1 + s ^ 2) * s ^ 2) := by
  have hone : 1 + s ^ 2 ≠ 0 := by nlinarith [sq_nonneg s]
  rw [cassiniOneOrbitMoment_one, cassiniOneOrbitContactWeight,
    cassiniOneOrbitContactCross]
  field_simp [hs, hone]
  ring

/-- Exact null root at one-orbit contact. -/
theorem cassiniOneOrbit_momentRatio_eq_contactNullRoot
    {c s : ℝ} (hc : c ≠ 0) (hs : s ≠ 0) (hh : c - 1 + s ^ 2 ≠ 0) :
    cassiniOneOrbitMoment c s (cassiniOneOrbitContactWeight c s) 1 /
        cassiniOneOrbitMoment c s (cassiniOneOrbitContactWeight c s) 0 =
      cassiniOneOrbitContactNullRoot c s := by
  have hone : 1 + s ^ 2 ≠ 0 := by nlinarith [sq_nonneg s]
  rw [cassiniOneOrbitMoment_zero_contactWeight_eq hs,
    cassiniOneOrbitMoment_one_contactWeight_eq hs,
    cassiniOneOrbitContactNullRoot]
  field_simp [hc, hs, hh, hone, pow_ne_zero]

/-- Sharp terminal factorization at one-real-atom/one-conjugate-pair contact. -/
theorem cassiniOneOrbitTerminalFlux_contactWeight_eq
    {c s : ℝ} (hc : c ≠ 0) (hs : s ≠ 0) (hh : c - 1 + s ^ 2 ≠ 0) :
    cassiniOneOrbitTerminalFlux c s (cassiniOneOrbitContactWeight c s) =
      c * cassiniOneOrbitContactCross c s * ((c - 1) ^ 2 + s ^ 2) /
        (c - 1 + s ^ 2) := by
  have hone : 1 + s ^ 2 ≠ 0 := by nlinarith [sq_nonneg s]
  rw [cassiniOneOrbitTerminalFlux]
  rw [cassiniOneOrbit_momentRatio_eq_contactNullRoot hc hs hh,
    cassiniOneOrbitMoment_one, cassiniOneOrbitMoment_two,
    cassiniOneOrbitMoment_three, cassiniOneOrbitContactNullRoot,
    cassiniOneOrbitContactWeight, cassiniOneOrbitContactCross]
  field_simp [hc, hs, hh, hone]
  ring

/-- Positive contact weight and nonzero angular width leave exactly one orientation coordinate:
the real atom lies below `1-s²` precisely when terminal flux is negative. -/
theorem cassiniOneOrbitTerminalFlux_contactWeight_neg_iff
    {c s : ℝ} (hc : 0 < c) (hs : s ≠ 0)
    (hcross : 0 < cassiniOneOrbitContactCross c s) :
    cassiniOneOrbitTerminalFlux c s (cassiniOneOrbitContactWeight c s) < 0 ↔
      c - 1 + s ^ 2 < 0 := by
  have hs2 : 0 < s ^ 2 := sq_pos_of_ne_zero hs
  have hcrossIdentity :
      cassiniOneOrbitContactCross c s =
        (c - 1 + s ^ 2) ^ 2 - (1 + s ^ 2) * s ^ 2 := by
    rw [cassiniOneOrbitContactCross]
    ring
  have hh : c - 1 + s ^ 2 ≠ 0 := by
    intro hzero
    rw [hcrossIdentity, hzero] at hcross
    nlinarith [sq_nonneg s]
  rw [cassiniOneOrbitTerminalFlux_contactWeight_eq hc.ne' hs hh]
  have hradial : 0 < (c - 1) ^ 2 + s ^ 2 := by nlinarith [sq_nonneg (c - 1)]
  have hnum :
      0 < c * cassiniOneOrbitContactCross c s * ((c - 1) ^ 2 + s ^ 2) := by
    positivity
  rw [div_neg_iff]
  constructor
  · rintro (⟨_hpos, hneg⟩ | hbad)
    · exact hneg
    · exact (not_lt_of_ge hnum.le hbad.1).elim
  · intro hneg
    exact Or.inl ⟨hnum, hneg⟩

/-! ## Exact narrow-sector bad contact -/

/-- Exact counterpacket: real atom `1/2`, pair `1 ± i/6`, common pair weight `63/37`. -/
def cassiniNarrowSectorBadContactMoment (n : ℕ) : ℝ :=
  cassiniOneOrbitMoment (1 / 2) (1 / 6) (126 / 37) n

theorem cassiniNarrowSectorBadContactMoment_values :
    cassiniNarrowSectorBadContactMoment 0 = 289 / 74 ∧
      cassiniNarrowSectorBadContactMoment 1 = 527 / 148 ∧
      cassiniNarrowSectorBadContactMoment 2 = 961 / 296 ∧
      cassiniNarrowSectorBadContactMoment 3 = 15467 / 5328 := by
  norm_num [cassiniNarrowSectorBadContactMoment, cassiniOneOrbitMoment,
    cassiniOneOrbitAtom, pow_succ, Complex.mul_re, Complex.mul_im]

/-- The counterpacket's conjugate-pair weight is exactly the positive contact weight. -/
theorem cassiniNarrowSectorBadContact_contactWeight :
    cassiniOneOrbitContactWeight (1 / 2) (1 / 6) = 126 / 37 := by
  norm_num [cassiniOneOrbitContactWeight, cassiniOneOrbitContactCross]

/-- Its complex atom lies in the strict `1/6` angular sector. -/
theorem cassiniNarrowSectorBadContact_atom_sector :
    0 < (cassiniOneOrbitAtom (1 / 6)).re ∧
      6 * |(cassiniOneOrbitAtom (1 / 6)).im| =
        (cassiniOneOrbitAtom (1 / 6)).re := by
  norm_num [cassiniOneOrbitAtom, abs_of_nonneg]

/-- All first four moments of the bad-contact packet remain strictly positive. -/
theorem cassiniNarrowSectorBadContact_firstFour_pos :
    0 < cassiniNarrowSectorBadContactMoment 0 ∧
      0 < cassiniNarrowSectorBadContactMoment 1 ∧
      0 < cassiniNarrowSectorBadContactMoment 2 ∧
      0 < cassiniNarrowSectorBadContactMoment 3 := by
  rw [cassiniNarrowSectorBadContactMoment_values.1,
    cassiniNarrowSectorBadContactMoment_values.2.1,
    cassiniNarrowSectorBadContactMoment_values.2.2.1,
    cassiniNarrowSectorBadContactMoment_values.2.2.2]
  norm_num

/-- The selected null root is positive and equals `31/34`. -/
theorem cassiniNarrowSectorBadContact_nullRoot :
    cassiniNarrowSectorBadContactMoment 1 /
        cassiniNarrowSectorBadContactMoment 0 = 31 / 34 := by
  rw [cassiniNarrowSectorBadContactMoment_values.1,
    cassiniNarrowSectorBadContactMoment_values.2.1]
  norm_num

/-- Exact flatness of the narrow-sector counterpacket. -/
theorem cassiniNarrowSectorBadContact_minor_eq_zero :
    cassiniNarrowSectorBadContactMoment 0 *
          cassiniNarrowSectorBadContactMoment 2 -
        cassiniNarrowSectorBadContactMoment 1 ^ 2 = 0 := by
  rw [cassiniNarrowSectorBadContactMoment_values.1,
    cassiniNarrowSectorBadContactMoment_values.2.1,
    cassiniNarrowSectorBadContactMoment_values.2.2.1]
  norm_num

/-- Exact negative terminal flux.  Narrow sector, moment positivity, and contact do not exclude a
right-hand degree-one crossing. -/
theorem cassiniNarrowSectorBadContact_terminalFlux :
    cassiniNarrowSectorBadContactMoment 3 -
          2 * (31 / 34) * cassiniNarrowSectorBadContactMoment 2 +
        (31 / 34) ^ 2 * cassiniNarrowSectorBadContactMoment 1 = -35 / 612 := by
  rw [cassiniNarrowSectorBadContactMoment_values.2.1,
    cassiniNarrowSectorBadContactMoment_values.2.2.1,
    cassiniNarrowSectorBadContactMoment_values.2.2.2]
  norm_num

end

end RHTower
