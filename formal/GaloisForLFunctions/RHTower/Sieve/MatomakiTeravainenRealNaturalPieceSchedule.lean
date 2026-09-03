import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRealNaturalBlocks
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPieceTypes
import GaloisForLFunctions.RHTower.Sieve.PolylogRpowDomination
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPaperDilation

/-!
# Natural unit blocks for the actual Proposition 2.2 piece range

The upper-adic terminal factor of a retained box can have a small index, so no floor-window
statement is true for every adic block in isolation.  Proposition 2.2 supplies the missing source
information without an extra assumption: a retained Type-I or Type-I/II piece has product above
`Y / 2`, while its other factors have the paper's power-scale upper bounds.  Since `Y` is almost
`X` and the paper width is only polylogarithmically small, the terminal unit factor contains an
integer eventually.

The capstones below quantify over every paper-range piece datum.  Thus the real unit factor in
each actual retained Type-I and Type-I/II box is exactly the natural Watt block required by the
moment theorems, with a nonempty dyadic natural window.  No adic-index or rounding hypothesis is
exposed.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- A fixed positive power gap absorbs the reciprocal paper width. -/
theorem eventually_two_rpow_le_mtPaperWidth_mul_rpow
    (A : ℕ) {alpha beta : ℝ} (hab : alpha < beta) :
    ∀ᶠ X : ℝ in atTop,
      2 * X ^ alpha ≤ mtPaperWidth A X * X ^ beta := by
  have hdom := eventually_const_mul_rpow_polylog_le_rpow
    (C := (2 : ℝ)) (α := alpha) (β := beta) (10 * A) hab
  filter_upwards [hdom, Filter.eventually_ge_atTop (Real.exp 1)] with X hdomX hX
  have hlogOne : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hlogPos : 0 < Real.log X := zero_lt_one.trans_le hlogOne
  have habs : |Real.log X| = Real.log X := abs_of_pos hlogPos
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlogPowPos : 0 < (Real.log X) ^ (10 * A) := pow_pos hlogPos _
  have hpoly : (Real.log X) ^ (10 * A) ≤
      (1 + |Real.log X|) ^ (10 * A) := by
    gcongr
    rw [habs]
    linarith
  have hdom' : 2 * X ^ alpha * (Real.log X) ^ (10 * A) ≤ X ^ beta :=
    (mul_le_mul_of_nonneg_left hpoly
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hXpos.le _))).trans hdomX
  rw [mtPaperWidth, Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hlogPowPos).2 (by simpa [mul_assoc] using hdom')

/-- Once a half-width unit interval has real length at least one, its length is at most the floor
of its lower endpoint. -/
theorem mtUnitFloor_conditions_of_half_width
    {delta M : ℝ} (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hlow : 1 ≤ delta * M) :
    1 ≤ delta * M ∧ delta * M ≤ (⌊M⌋₊ : ℝ) := by
  have hMtwo : (2 : ℝ) ≤ M := by
    nlinarith
  have hMlt : M < (⌊M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one M
  have hhalfFloor : M / 2 ≤ (⌊M⌋₊ : ℝ) := by linarith
  refine ⟨hlow, ?_⟩
  calc
    delta * M ≤ (1 / 2 : ℝ) * M :=
      mul_le_mul_of_nonneg_right hdeltaHalf (by linarith)
    _ = M / 2 := by ring
    _ ≤ (⌊M⌋₊ : ℝ) := hhalfFloor

/-- Every Type-I piece in the literal Proposition 2.2 source range has its real unit factor equal
to one nonempty natural Watt block.  All paper restrictions are under the eventual quantifier. -/
theorem eventually_mtPaperTypeIPiece_unit_eq_wattBlock (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ epsilon : ℝ,
      0 < epsilon → epsilon ≤ 1 / 100 → ∀ Y : ℝ,
      X ^ (1 - epsilon / 100) < Y →
      ∀ data : MTTypeIPieceData X Y (mtPaperWidth (A + 1) X) epsilon,
      ∀ t : ℝ,
        perronPoly
            (fun n => mtRealIntervalAF (fun _ => (1 : ℂ)) data.M₂
              ((1 + mtPaperWidth (A + 1) X) * data.M₂) n)
            ⌈(1 + mtPaperWidth (A + 1) X) * data.M₂⌉₊ 1 t =
          mtWattUnitBlock ⌊data.M₂⌋₊
            ⌊(1 + mtPaperWidth (A + 1) X) * data.M₂⌋₊ t ∧
        ⌊data.M₂⌋₊ <
            ⌊(1 + mtPaperWidth (A + 1) X) * data.M₂⌋₊ ∧
          ⌊(1 + mtPaperWidth (A + 1) X) * data.M₂⌋₊ ≤
            2 * ⌊data.M₂⌋₊ := by
  have hpower := eventually_two_rpow_le_mtPaperWidth_mul_rpow
    (A + 1) (alpha := (51 / 100 : ℝ)) (beta := (9999 / 10000 : ℝ)) (by norm_num)
  filter_upwards [hpower, eventually_three_mul_mtPaperWidth_succ_le A,
    Filter.eventually_ge_atTop (Real.exp 1)] with X hpowerX hreserve hX
  intro epsilon hepsilon0 hepsilon Y hY data t
  have hXone : 1 ≤ X := by
    exact (Real.one_le_exp (by norm_num)).trans hX
  have hlogOne : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hdeltaPos : 0 < mtPaperWidth (A + 1) X := by
    rw [mtPaperWidth]
    exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hlogOne) _
  have hwidthA : mtPaperWidth A X ≤ 1 := by
    rw [mtPaperWidth]
    simpa using Real.rpow_le_rpow_of_exponent_le hlogOne
      (neg_nonpos.mpr (Nat.cast_nonneg (10 * A)))
  have hdeltaHalf : mtPaperWidth (A + 1) X ≤ 1 / 2 := by
    linarith
  have hM₁cap : data.M₁ ≤ X ^ (51 / 100 : ℝ) :=
    data.M₁_le.trans (Real.rpow_le_rpow_of_exponent_le hXone (by linarith))
  have hYbase : X ^ (9999 / 10000 : ℝ) < Y := by
    exact (Real.rpow_le_rpow_of_exponent_le hXone (by linarith)).trans_lt hY
  have htwoM₁ : 2 * data.M₁ < mtPaperWidth (A + 1) X * Y := by
    calc
      2 * data.M₁ ≤ 2 * X ^ (51 / 100 : ℝ) := by linarith
      _ ≤ mtPaperWidth (A + 1) X * X ^ (9999 / 10000 : ℝ) := hpowerX
      _ < mtPaperWidth (A + 1) X * Y :=
        mul_lt_mul_of_pos_left hYbase hdeltaPos
  have hscaledProduct :
      mtPaperWidth (A + 1) X * Y <
        2 * mtPaperWidth (A + 1) X * (data.M₁ * data.M₂) := by
    have h := mul_lt_mul_of_pos_left data.product_mem.1
      (show 0 < 2 * mtPaperWidth (A + 1) X by positivity)
    nlinarith
  have hmul : 2 * data.M₁ <
      (2 * data.M₁) * (mtPaperWidth (A + 1) X * data.M₂) := by
    calc
      2 * data.M₁ < mtPaperWidth (A + 1) X * Y := htwoM₁
      _ < 2 * mtPaperWidth (A + 1) X * (data.M₁ * data.M₂) := hscaledProduct
      _ = (2 * data.M₁) * (mtPaperWidth (A + 1) X * data.M₂) := by ring
  have hlow : 1 ≤ mtPaperWidth (A + 1) X * data.M₂ := by
    nlinarith [data.M₁_pos]
  have hconditions := mtUnitFloor_conditions_of_half_width
    hdeltaPos hdeltaHalf hlow
  have hupper0 : 0 ≤ (1 + mtPaperWidth (A + 1) X) * data.M₂ :=
    mul_nonneg (by linarith) data.M₂_pos.le
  exact ⟨perronPoly_mtRealUnitInterval_eq_mtWattUnitBlock
      data.M₂_pos.le hupper0 t,
    mtRealUnitFloor_window data.M₂_pos.le hconditions.1 hconditions.2⟩

/-- The first two factors of every paper-range Type-I/II datum have product at most `X^(5/8)`.
This is the exact square-product consequence used to force room in its terminal unit block. -/
theorem MTTypeI_II_PieceData.first_two_product_le_rpow_five_eighth
    {X Y delta epsilon : ℝ} (hXone : 1 ≤ X) (hepsilon0 : 0 ≤ epsilon)
    (data : MTTypeI_II_PieceData X Y delta epsilon) :
    data.M₁ * data.M₂ ≤ X ^ (5 / 8 : ℝ) := by
  have hXpos : 0 < X := zero_lt_one.trans_le hXone
  have hsqFirst :
      (data.M₁ ^ 2 * data.M₂) * data.M₂ ≤
        X ^ (1 - epsilon) * data.M₂ :=
    mul_le_mul_of_nonneg_right data.square_product_le data.M₂_pos.le
  have hsqSecond :
      X ^ (1 - epsilon) * data.M₂ ≤
        X ^ (1 - epsilon) * X ^ (1 / 4 - epsilon) :=
    mul_le_mul_of_nonneg_left data.M₂_le (Real.rpow_nonneg hXpos.le _)
  have hpowEq :
      X ^ (1 - epsilon) * X ^ (1 / 4 - epsilon) =
        (X ^ (5 / 8 - epsilon)) ^ (2 : ℕ) := by
    rw [← Real.rpow_add hXpos]
    calc
      X ^ ((1 - epsilon) + (1 / 4 - epsilon)) =
          X ^ ((5 / 8 - epsilon) * 2) := by
        rw [show (1 - epsilon) + (1 / 4 - epsilon) =
          (5 / 8 - epsilon) * 2 by ring]
      _ = (X ^ (5 / 8 - epsilon)) ^ (2 : ℝ) :=
        Real.rpow_mul hXpos.le _ _
      _ = (X ^ (5 / 8 - epsilon)) ^ (2 : ℕ) :=
        Real.rpow_natCast _ _
  have hsq : (data.M₁ * data.M₂) ^ (2 : ℕ) ≤
      (X ^ (5 / 8 - epsilon)) ^ (2 : ℕ) := by
    rw [← hpowEq]
    calc
      (data.M₁ * data.M₂) ^ 2 =
          (data.M₁ ^ 2 * data.M₂) * data.M₂ := by ring
      _ ≤ X ^ (1 - epsilon) * data.M₂ := hsqFirst
      _ ≤ X ^ (1 - epsilon) * X ^ (1 / 4 - epsilon) := hsqSecond
  have hfirst : data.M₁ * data.M₂ ≤ X ^ (5 / 8 - epsilon) := by
    have hprod0 : 0 ≤ data.M₁ * data.M₂ :=
      mul_nonneg data.M₁_pos.le data.M₂_pos.le
    have hpow0 : 0 ≤ X ^ (5 / 8 - epsilon) := Real.rpow_nonneg hXpos.le _
    nlinarith
  exact hfirst.trans
    (Real.rpow_le_rpow_of_exponent_le hXone (by linarith))

/-- Every Type-I/II piece in the literal Proposition 2.2 source range has its real terminal unit
factor equal to one nonempty natural Watt block.  The square-product scale law is discharged from
the datum itself. -/
theorem eventually_mtPaperTypeI_II_Piece_unit_eq_wattBlock (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ epsilon : ℝ,
      0 < epsilon → epsilon ≤ 1 / 100 → ∀ Y : ℝ,
      X ^ (1 - epsilon / 100) < Y →
      ∀ data : MTTypeI_II_PieceData X Y (mtPaperWidth (A + 1) X) epsilon,
      ∀ t : ℝ,
        perronPoly
            (fun n => mtRealIntervalAF (fun _ => (1 : ℂ)) data.M₃
              ((1 + mtPaperWidth (A + 1) X) * data.M₃) n)
            ⌈(1 + mtPaperWidth (A + 1) X) * data.M₃⌉₊ 1 t =
          mtWattUnitBlock ⌊data.M₃⌋₊
            ⌊(1 + mtPaperWidth (A + 1) X) * data.M₃⌋₊ t ∧
        ⌊data.M₃⌋₊ <
            ⌊(1 + mtPaperWidth (A + 1) X) * data.M₃⌋₊ ∧
          ⌊(1 + mtPaperWidth (A + 1) X) * data.M₃⌋₊ ≤
            2 * ⌊data.M₃⌋₊ := by
  have hpower := eventually_two_rpow_le_mtPaperWidth_mul_rpow
    (A + 1) (alpha := (5 / 8 : ℝ)) (beta := (9999 / 10000 : ℝ)) (by norm_num)
  filter_upwards [hpower, eventually_three_mul_mtPaperWidth_succ_le A,
    Filter.eventually_ge_atTop (Real.exp 1)] with X hpowerX hreserve hX
  intro epsilon hepsilon0 hepsilon Y hY data t
  have hXone : 1 ≤ X := by
    exact (Real.one_le_exp (by norm_num)).trans hX
  have hlogOne : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hdeltaPos : 0 < mtPaperWidth (A + 1) X := by
    rw [mtPaperWidth]
    exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hlogOne) _
  have hwidthA : mtPaperWidth A X ≤ 1 := by
    rw [mtPaperWidth]
    simpa using Real.rpow_le_rpow_of_exponent_le hlogOne
      (neg_nonpos.mpr (Nat.cast_nonneg (10 * A)))
  have hdeltaHalf : mtPaperWidth (A + 1) X ≤ 1 / 2 := by
    linarith
  have hM₁M₂cap : data.M₁ * data.M₂ ≤ X ^ (5 / 8 : ℝ) :=
    data.first_two_product_le_rpow_five_eighth hXone hepsilon0.le
  have hYbase : X ^ (9999 / 10000 : ℝ) < Y := by
    exact (Real.rpow_le_rpow_of_exponent_le hXone (by linarith)).trans_lt hY
  have htwoM₁M₂ : 2 * (data.M₁ * data.M₂) <
      mtPaperWidth (A + 1) X * Y := by
    calc
      2 * (data.M₁ * data.M₂) ≤ 2 * X ^ (5 / 8 : ℝ) := by linarith
      _ ≤ mtPaperWidth (A + 1) X * X ^ (9999 / 10000 : ℝ) := hpowerX
      _ < mtPaperWidth (A + 1) X * Y :=
        mul_lt_mul_of_pos_left hYbase hdeltaPos
  have hscaledProduct :
      mtPaperWidth (A + 1) X * Y <
        2 * mtPaperWidth (A + 1) X *
          ((data.M₁ * data.M₂) * data.M₃) := by
    have h := mul_lt_mul_of_pos_left data.product_mem.1
      (show 0 < 2 * mtPaperWidth (A + 1) X by positivity)
    nlinarith
  have hmul : 2 * (data.M₁ * data.M₂) <
      (2 * (data.M₁ * data.M₂)) *
        (mtPaperWidth (A + 1) X * data.M₃) := by
    calc
      2 * (data.M₁ * data.M₂) < mtPaperWidth (A + 1) X * Y := htwoM₁M₂
      _ < 2 * mtPaperWidth (A + 1) X *
          ((data.M₁ * data.M₂) * data.M₃) := hscaledProduct
      _ = (2 * (data.M₁ * data.M₂)) *
          (mtPaperWidth (A + 1) X * data.M₃) := by ring
  have hlow : 1 ≤ mtPaperWidth (A + 1) X * data.M₃ := by
    by_contra hnot
    have hone : mtPaperWidth (A + 1) X * data.M₃ < 1 := lt_of_not_ge hnot
    have hfactor : 0 < 2 * (data.M₁ * data.M₂) :=
      mul_pos (by norm_num) (mul_pos data.M₁_pos data.M₂_pos)
    have hback :
        (2 * (data.M₁ * data.M₂)) *
            (mtPaperWidth (A + 1) X * data.M₃) <
          2 * (data.M₁ * data.M₂) := by
      simpa using mul_lt_mul_of_pos_left hone hfactor
    exact (lt_asymm hmul hback).elim
  have hconditions := mtUnitFloor_conditions_of_half_width
    hdeltaPos hdeltaHalf hlow
  have hupper0 : 0 ≤ (1 + mtPaperWidth (A + 1) X) * data.M₃ :=
    mul_nonneg (by linarith) data.M₃_pos.le
  exact ⟨perronPoly_mtRealUnitInterval_eq_mtWattUnitBlock
      data.M₃_pos.le hupper0 t,
    mtRealUnitFloor_window data.M₃_pos.le hconditions.1 hconditions.2⟩

end

end RHTower.Sieve
