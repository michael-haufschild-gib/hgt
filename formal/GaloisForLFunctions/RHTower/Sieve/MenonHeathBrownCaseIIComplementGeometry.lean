import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIAggregate

/-!
# Degree-three complement geometry for Menon's Case II

Excising one factor from a degree-three Heath--Brown box leaves at most five factors.  The
resulting exact dyadic width and unraised divisor-energy exponent are therefore fixed uniformly
over every Case-II color.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- Fixed dyadic width of every degree-three erase-complement. -/
def menonHeathBrownCaseIIComplementWidthConstant : ℝ := ((2 ^ 5 : ℕ) : ℝ)

/-- Fixed unraised divisor-moment exponent of every degree-three erase-complement. -/
def menonHeathBrownCaseIIComplementPolylogExponent : ℕ :=
  2 * 5 + (2 ^ (2 * 5) - 1)

/-- Excising one factor from a degree-three box leaves at most five factors. -/
theorem heathBrownBoxFactor_three_complement_card_le_five
    {L X : ℕ} (box : HeathBrownBoxChoice L X 3)
    (j : HeathBrownBoxFactorIndex 3 box.m) :
    Fintype.card {i : HeathBrownBoxFactorIndex 3 box.m //
      i ∈ (Finset.univ.erase j)} ≤ 5 := by
  rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ j),
    Finset.card_univ]
  change Fintype.card (HeathBrownBoxFactorIndex 3 (box.1 : ℕ)) - 1 ≤ 5
  rw [card_heathBrownBoxFactorIndex box.1.isLt]
  omega

/-- The exact complementary divisor-energy exponent is at most `1033`. -/
theorem heathBrownBoxFactor_three_complement_polylogExponent_le
    {L X : ℕ} (box : HeathBrownBoxChoice L X 3)
    (j : HeathBrownBoxFactorIndex 3 box.m) :
    let I := {i : HeathBrownBoxFactorIndex 3 box.m //
      i ∈ (Finset.univ.erase j)}
    2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1) ≤
      menonHeathBrownCaseIIComplementPolylogExponent := by
  let I := {i : HeathBrownBoxFactorIndex 3 box.m //
    i ∈ (Finset.univ.erase j)}
  have hw : Fintype.card I ≤ 5 :=
    heathBrownBoxFactor_three_complement_card_le_five box j
  have hdouble : 2 * Fintype.card I ≤ 2 * 5 := Nat.mul_le_mul_left 2 hw
  have hpow : 2 ^ (2 * Fintype.card I) ≤ 2 ^ (2 * 5) :=
    Nat.pow_le_pow_right (by norm_num) hdouble
  dsimp only [menonHeathBrownCaseIIComplementPolylogExponent]
  exact Nat.add_le_add hdouble (Nat.sub_le_sub_right hpow 1)

/-- The degree-three erase-complement upper edge is at most `32` times its lower edge. -/
theorem heathBrownBoxFactor_three_complement_upper_le_width_mul_lower
    {L X : ℕ} (box : HeathBrownBoxChoice L X 3)
    (j : HeathBrownBoxFactorIndex 3 box.m) :
    let I := {i : HeathBrownBoxFactorIndex 3 box.m //
      i ∈ (Finset.univ.erase j)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent box.a box.b box.q i
    (groupedDyadicUpper q : ℝ) ≤
      menonHeathBrownCaseIIComplementWidthConstant *
        (groupedDyadicLower q : ℝ) := by
  dsimp only
  let I := {i : HeathBrownBoxFactorIndex 3 box.m //
    i ∈ (Finset.univ.erase j)}
  let q : I → ℕ := fun i =>
    heathBrownBoxFactorExponent box.a box.b box.q i
  let w : ℕ := Fintype.card I
  have hw : w ≤ 5 := heathBrownBoxFactor_three_complement_card_le_five box j
  have hpow : 2 ^ w ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hw
  have hwidth := groupedDyadicUpper_eq_lower_mul_twoPow q
  change (groupedDyadicUpper q : ℝ) ≤
    menonHeathBrownCaseIIComplementWidthConstant * (groupedDyadicLower q : ℝ)
  rw [hwidth, Nat.cast_mul]
  dsimp only [menonHeathBrownCaseIIComplementWidthConstant]
  have hpowR : ((2 ^ w : ℕ) : ℝ) ≤ ((2 ^ 5 : ℕ) : ℝ) := by
    exact_mod_cast hpow
  calc
    (groupedDyadicLower q : ℝ) * ((2 ^ w : ℕ) : ℝ) ≤
        (groupedDyadicLower q : ℝ) * ((2 ^ 5 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hpowR (by positivity)
    _ = ((2 ^ 5 : ℕ) : ℝ) * (groupedDyadicLower q : ℝ) := by ring

/-- The full box lower edge factors exactly into the selected edge and erase-complement edge. -/
theorem groupedDyadicLower_heathBrownBoxFactorExponent_eq_factor_mul_complement
    {L X : ℕ} (box : HeathBrownBoxChoice L X 3)
    (j : HeathBrownBoxFactorIndex 3 box.m) :
    let I := {i : HeathBrownBoxFactorIndex 3 box.m //
      i ∈ (Finset.univ.erase j)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent box.a box.b box.q i
    groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) =
      2 ^ heathBrownBoxFactorExponent box.a box.b box.q j *
        groupedDyadicLower q := by
  dsimp only
  simp only [groupedDyadicLower]
  rw [← Finset.prod_subtype (Finset.univ.erase j)
    (fun _ => Iff.rfl)
    (fun i => 2 ^ heathBrownBoxFactorExponent box.a box.b box.q i)]
  exact (Finset.mul_prod_erase Finset.univ
    (fun i => 2 ^ heathBrownBoxFactorExponent box.a box.b box.q i)
      (Finset.mem_univ j)).symm

/-- The erase-complement lower edge is no larger than its window-relevant full box edge. -/
theorem windowRelevant_heathBrownBox_three_complement_lower_le_X
    {L X : ℕ} {N : ℝ} (box : HeathBrownBoxChoice L X 3)
    (j : HeathBrownBoxFactorIndex 3 box.m)
    (hbox : IsHeathBrownBoxWindowRelevant N X 3 box) :
    let I := {i : HeathBrownBoxFactorIndex 3 box.m //
      i ∈ (Finset.univ.erase j)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent box.a box.b box.q i
    (groupedDyadicLower q : ℝ) ≤ X := by
  let I := {i : HeathBrownBoxFactorIndex 3 box.m //
    i ∈ (Finset.univ.erase j)}
  let q : I → ℕ := fun i =>
    heathBrownBoxFactorExponent box.a box.b box.q i
  let A : ℝ := (groupedDyadicLower q : ℝ)
  let M : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
  have hfactor :
      groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) =
        2 ^ heathBrownBoxFactorExponent box.a box.b box.q j *
          groupedDyadicLower q := by
    simpa only [q] using
      groupedDyadicLower_heathBrownBoxFactorExponent_eq_factor_mul_complement box j
  have hfactorReal :
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) = M * A := by
    have hfactorRealRaw :
        (groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) =
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) *
          (groupedDyadicLower q : ℝ) := by
      exact_mod_cast hfactor
    simpa only [M, A] using hfactorRealRaw
  have hM : 1 ≤ M := by
    dsimp only [M]
    exact_mod_cast Nat.one_le_two_pow
  have hA0 : 0 ≤ A := by positivity
  have hAle : A ≤ M * A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hM hA0
  exact hAle.trans (by
    rw [← hfactorReal]
    exact windowRelevant_heathBrownBox_coreLower_le hbox)

/-- Every degree-three erase-complement upper edge is at most `32 X`. -/
theorem windowRelevant_heathBrownBox_three_complement_upper_le_width_mul_X
    {L X : ℕ} {N : ℝ} (box : HeathBrownBoxChoice L X 3)
    (j : HeathBrownBoxFactorIndex 3 box.m)
    (hbox : IsHeathBrownBoxWindowRelevant N X 3 box) :
    let I := {i : HeathBrownBoxFactorIndex 3 box.m //
      i ∈ (Finset.univ.erase j)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent box.a box.b box.q i
    (groupedDyadicUpper q : ℝ) ≤
      menonHeathBrownCaseIIComplementWidthConstant * X := by
  dsimp only
  exact (heathBrownBoxFactor_three_complement_upper_le_width_mul_lower box j).trans
    (mul_le_mul_of_nonneg_left
      (windowRelevant_heathBrownBox_three_complement_lower_le_X box j hbox)
      (by
        dsimp only [menonHeathBrownCaseIIComplementWidthConstant]
        positivity))

/-- The literal Case-II receiver energy has the canonical two-term complement bound with the
exact degree-three width and energy exponent. -/
theorem menonHeathBrownCaseIIReceiverUpper_le_canonical
    {L X cells : ℕ} {sigma Δ T : ℝ}
    (label : MenonHeathBrownCaseIILabel L X cells)
    (hT : 1 ≤ T) (hΔ : 1 ≤ Δ) (hΔT : Δ / 2 ≤ T) :
    let I := {i : HeathBrownBoxFactorIndex 3 label.box.m //
      i ∈ (Finset.univ.erase label.factor)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent label.box.a label.box.b label.box.q i
    let A : ℝ := (groupedDyadicLower q : ℝ)
    let U : ℝ := (groupedDyadicUpper q : ℝ)
    let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
    menonHeathBrownCaseIIReceiverUpper L X sigma Δ T label ≤
      (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
          (1 + Real.log U) ^ (E + 2)) *
        (T * A ^ (1 - 2 * sigma) + A ^ (2 - 2 * sigma)) := by
  let I := {i : HeathBrownBoxFactorIndex 3 label.box.m //
    i ∈ (Finset.univ.erase label.factor)}
  let q : I → ℕ := fun i =>
    heathBrownBoxFactorExponent label.box.a label.box.b label.box.q i
  let A : ℝ := (groupedDyadicLower q : ℝ)
  let U : ℝ := (groupedDyadicUpper q : ℝ)
  let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
  let W : ℝ := menonHeathBrownCaseIIComplementWidthConstant
  have hH : 2 * T + Δ / 2 ≤ 3 * T := by linarith
  have hA : 1 ≤ A := by
    dsimp only [A]
    exact_mod_cast one_le_groupedDyadicLower q
  have hU : 1 ≤ U := by
    dsimp only [U]
    exact_mod_cast one_le_groupedDyadicUpper q
  have hW : 1 ≤ W := by
    dsimp only [W, menonHeathBrownCaseIIComplementWidthConstant]
    norm_num
  have hwidth : U ≤ W * A := by
    dsimp only [U, W, A]
    exact heathBrownBoxFactor_three_complement_upper_le_width_mul_lower
      label.box label.factor
  have hcanonical := montgomery_unraised_factor_le_canonical
    hT hH hΔ hA hU hW hwidth (c := sigma) (E := E)
  have hpow : (A ^ (-sigma)) ^ 2 = A ^ (-2 * sigma) :=
    rpow_neg_sq_eq_rpow_neg_two_mul (zero_lt_one.trans_le hA)
  simpa only [menonHeathBrownCaseIIReceiverUpper, I, q, A, U, E, W, hpow] using
    hcanonical

/-- Window relevance replaces every complementary logarithm and energy exponent by the exact
fixed degree-three envelope, while preserving both complementary power savings. -/
theorem windowRelevant_menonHeathBrownCaseIIReceiverUpper_le_fixedPolylog
    {L X cells : ℕ} {a sigma Δ T : ℝ}
    (label : MenonHeathBrownCaseIILabel L X cells)
    (hbox : IsHeathBrownBoxWindowRelevant a X 3 label.box)
    (hX : 1 ≤ X) (hT : 1 ≤ T) (hΔ : 1 ≤ Δ) (hΔT : Δ / 2 ≤ T) :
    let I := {i : HeathBrownBoxFactorIndex 3 label.box.m //
      i ∈ (Finset.univ.erase label.factor)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent label.box.a label.box.b label.box.q i
    let A : ℝ := (groupedDyadicLower q : ℝ)
    let W : ℝ := menonHeathBrownCaseIIComplementWidthConstant
    menonHeathBrownCaseIIReceiverUpper L X sigma Δ T label ≤
      (12 * W ^ 2 *
          (1 + Real.log (W * (X : ℝ))) ^
            (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
        (T * A ^ (1 - 2 * sigma) + A ^ (2 - 2 * sigma)) := by
  let I := {i : HeathBrownBoxFactorIndex 3 label.box.m //
    i ∈ (Finset.univ.erase label.factor)}
  let q : I → ℕ := fun i =>
    heathBrownBoxFactorExponent label.box.a label.box.b label.box.q i
  let A : ℝ := (groupedDyadicLower q : ℝ)
  let U : ℝ := (groupedDyadicUpper q : ℝ)
  let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
  let W : ℝ := menonHeathBrownCaseIIComplementWidthConstant
  have hcanonical := menonHeathBrownCaseIIReceiverUpper_le_canonical
    (sigma := sigma) label hT hΔ hΔT
  have hU : 1 ≤ U := by
    dsimp only [U]
    exact_mod_cast one_le_groupedDyadicUpper q
  have hW : 1 ≤ W := by
    dsimp only [W, menonHeathBrownCaseIIComplementWidthConstant]
    norm_num
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hWX : 1 ≤ W * (X : ℝ) := one_le_mul_of_one_le_of_one_le hW hXR
  have hUX : U ≤ W * (X : ℝ) := by
    dsimp only [U, W]
    exact windowRelevant_heathBrownBox_three_complement_upper_le_width_mul_X
      label.box label.factor hbox
  have hlog : Real.log U ≤ Real.log (W * (X : ℝ)) :=
    Real.log_le_log (zero_lt_one.trans_le hU) hUX
  have hbase : 1 + Real.log U ≤ 1 + Real.log (W * (X : ℝ)) := by linarith
  have hbaseU : 0 ≤ 1 + Real.log U := by
    have := Real.log_nonneg hU
    linarith
  have hbaseX : 1 ≤ 1 + Real.log (W * (X : ℝ)) := by
    have := Real.log_nonneg hWX
    linarith
  have hE : E ≤ menonHeathBrownCaseIIComplementPolylogExponent := by
    dsimp only [E, I]
    exact heathBrownBoxFactor_three_complement_polylogExponent_le
      label.box label.factor
  have hpow : (1 + Real.log U) ^ (E + 2) ≤
      (1 + Real.log (W * (X : ℝ))) ^
        (menonHeathBrownCaseIIComplementPolylogExponent + 2) := by
    calc
      (1 + Real.log U) ^ (E + 2) ≤
          (1 + Real.log (W * (X : ℝ))) ^ (E + 2) :=
        pow_le_pow_left₀ hbaseU hbase _
      _ ≤ (1 + Real.log (W * (X : ℝ))) ^
          (menonHeathBrownCaseIIComplementPolylogExponent + 2) :=
        pow_le_pow_right₀ hbaseX (Nat.add_le_add_right hE 2)
  have hterm : 0 ≤ T * A ^ (1 - 2 * sigma) + A ^ (2 - 2 * sigma) := by
    positivity
  exact hcanonical.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (by positivity)) hterm)

end RHTower.Sieve
