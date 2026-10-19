import GaloisForLFunctions.RHTower.QuasiRHDetectorScaleBudget

/-!
# Joint Gram requirements for the five-sixths detector budget

The profile `1 + P^ν + P^κ/Y` retains its unit, exceptional, and nonexceptional
contributions. After principal normalization and the reflected allowance, its
five-sixths feasibility region is exactly `ν ≤ 1/15` and `κ + 4ν ≤ 4/3`.
The unit contribution alone prevents reaching three quarters with that allowance.
These statements concern the displayed upper-bound model, not actual energy lower bounds.
-/

noncomputable section

namespace RHTower.QuasiRHDetectorScaleBudget

/-- Gram exponent when `X=Z^x`, `Y=Z^(1-slots-x)`, and `P=Y/X`. -/
def gramProfileExponent (x slots ν κ : ℝ) : ℝ :=
  max 0 (max (ν * (1 - slots - 2 * x))
    ((κ - 1) * (1 - slots) - (2 * κ - 1) * x))

/-- Signal-adjusted boundary retaining all three Gram contributions. -/
def gramProfileBoundary (x slots ν κ : ℝ) : ℝ :=
  x / 2 + gramProfileExponent x slots ν κ / 2 - principalShift x slots +
    reflectedLoss slots / 2

theorem gramProfileBoundary_eq (x slots ν κ : ℝ) :
    gramProfileBoundary x slots ν κ =
      5 / 6 + (x - slots) / 6 + gramProfileExponent x slots ν κ / 2 +
        reflectedLoss slots / 2 := by
  unfold gramProfileBoundary principalShift
  ring

/-- Boundary remaining after both nonunit Gram contributions have been removed. -/
def unitGramBoundary (x slots : ℝ) : ℝ :=
  x / 2 - principalShift x slots + reflectedLoss slots / 2

theorem unitGramBoundary_exact (x slots : ℝ) :
    unitGramBoundary x slots = 29 / 36 + x / 6 +
      max ((1 / 6 - slots) / 6) ((13 / 30) * (slots - 1 / 6)) := by
  unfold unitGramBoundary principalShift reflectedLoss
  by_cases h : slots ≤ 1 / 6
  · rw [max_eq_left (by linarith : (6 * slots - 1) / 5 ≤ 0),
      max_eq_left (by linarith :
        (13 / 30) * (slots - 1 / 6) ≤ (1 / 6 - slots) / 6)]
    ring
  · rw [max_eq_right (by linarith : 0 ≤ (6 * slots - 1) / 5),
      max_eq_right (by linarith :
        (1 / 6 - slots) / 6 ≤ (13 / 30) * (slots - 1 / 6))]
    ring

theorem unitGramBoundary_sharp_minimum (x slots : ℝ) (hx : 0 ≤ x) :
    29 / 36 ≤ unitGramBoundary x slots ∧
      (unitGramBoundary x slots = 29 / 36 ↔ x = 0 ∧ slots = 1 / 6) := by
  rw [unitGramBoundary_exact]
  have hleft := le_max_left ((1 / 6 - slots) / 6) ((13 / 30) * (slots - 1 / 6))
  have hright := le_max_right ((1 / 6 - slots) / 6) ((13 / 30) * (slots - 1 / 6))
  have hn : 0 ≤ max ((1 / 6 - slots) / 6) ((13 / 30) * (slots - 1 / 6)) := by
    linarith
  refine ⟨by linarith, ?_⟩
  constructor
  · intro h
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem unitGramBoundary_le_profile (x slots ν κ : ℝ) :
    unitGramBoundary x slots ≤ gramProfileBoundary x slots ν κ := by
  have h := le_max_left (0 : ℝ)
    (max (ν * (1 - slots - 2 * x)) ((κ - 1) * (1 - slots) - (2 * κ - 1) * x))
  change 0 ≤ gramProfileExponent x slots ν κ at h
  unfold unitGramBoundary gramProfileBoundary
  linarith

/-- Changing the two nonunit powers cannot reach three quarters with the retained allowance. -/
theorem gramProfileBoundary_gt_three_quarters (x slots ν κ : ℝ) (hx : 0 ≤ x) :
    3 / 4 < gramProfileBoundary x slots ν κ := by
  have h := (unitGramBoundary_sharp_minimum x slots hx).1
  have h' := unitGramBoundary_le_profile x slots ν κ
  linarith

/-- Reduced budget after deleting exceptional frequencies but retaining `P²/Y`. -/
def ordinaryGramBoundary (x slots : ℝ) : ℝ :=
  5 / 6 + (x - slots) / 6 + max 0 (1 - slots - 3 * x) / 2 +
    reflectedLoss slots / 2

theorem gramProfileBoundary_zero_exceptional (x slots : ℝ) :
    gramProfileBoundary x slots 0 2 = ordinaryGramBoundary x slots := by
  rw [gramProfileBoundary_eq]
  norm_num [gramProfileExponent, ordinaryGramBoundary, ← max_assoc]

/-- Exact cost of moving either scale or slot length away from the reduced optimum. -/
theorem ordinaryGramBoundary_exact (x slots : ℝ) :
    ordinaryGramBoundary x slots = 23 / 27 +
      max ((2 / 9) * (1 / 6 - slots)) ((17 / 45) * (slots - 1 / 6)) +
      max ((x - (1 - slots) / 3) / 6) ((4 / 3) * ((1 - slots) / 3 - x)) := by
  unfold ordinaryGramBoundary reflectedLoss
  by_cases hs : slots ≤ 1 / 6
  · rw [max_eq_left (by linarith : (6 * slots - 1) / 5 ≤ 0),
      max_eq_left (by linarith :
        (17 / 45) * (slots - 1 / 6) ≤ (2 / 9) * (1 / 6 - slots))]
    by_cases hx : x ≤ (1 - slots) / 3
    · rw [max_eq_right (by linarith : 0 ≤ 1 - slots - 3 * x),
        max_eq_right (by linarith :
          (x - (1 - slots) / 3) / 6 ≤ (4 / 3) * ((1 - slots) / 3 - x))]
      ring
    · rw [max_eq_left (by linarith : 1 - slots - 3 * x ≤ 0),
        max_eq_left (by linarith :
          (4 / 3) * ((1 - slots) / 3 - x) ≤ (x - (1 - slots) / 3) / 6)]
      ring
  · rw [max_eq_right (by linarith : 0 ≤ (6 * slots - 1) / 5),
      max_eq_right (by linarith :
        (2 / 9) * (1 / 6 - slots) ≤ (17 / 45) * (slots - 1 / 6))]
    by_cases hx : x ≤ (1 - slots) / 3
    · rw [max_eq_right (by linarith : 0 ≤ 1 - slots - 3 * x),
        max_eq_right (by linarith :
          (x - (1 - slots) / 3) / 6 ≤ (4 / 3) * ((1 - slots) / 3 - x))]
      ring
    · rw [max_eq_left (by linarith : 1 - slots - 3 * x ≤ 0),
        max_eq_left (by linarith :
          (4 / 3) * ((1 - slots) / 3 - x) ≤ (x - (1 - slots) / 3) / 6)]
      ring

theorem ordinaryGramBoundary_sharp_minimum (x slots : ℝ) :
    23 / 27 ≤ ordinaryGramBoundary x slots ∧
      (ordinaryGramBoundary x slots = 23 / 27 ↔ x = 5 / 18 ∧ slots = 1 / 6) := by
  rw [ordinaryGramBoundary_exact]
  have hs₁ := le_max_left ((2 / 9) * (1 / 6 - slots)) ((17 / 45) * (slots - 1 / 6))
  have hs₂ := le_max_right ((2 / 9) * (1 / 6 - slots)) ((17 / 45) * (slots - 1 / 6))
  have hx₁ := le_max_left ((x - (1 - slots) / 3) / 6) ((4 / 3) * ((1 - slots) / 3 - x))
  have hx₂ := le_max_right ((x - (1 - slots) / 3) / 6) ((4 / 3) * ((1 - slots) / 3 - x))
  have hs0 : 0 ≤ max ((2 / 9) * (1 / 6 - slots)) ((17 / 45) * (slots - 1 / 6)) := by
    linarith
  have hx0 : 0 ≤ max ((x - (1 - slots) / 3) / 6)
      ((4 / 3) * ((1 - slots) / 3 - x)) := by linarith
  refine ⟨by linarith, ?_⟩
  constructor
  · intro h
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem ordinaryGramBoundary_le_profile (x slots ν : ℝ) :
    ordinaryGramBoundary x slots ≤ gramProfileBoundary x slots ν 2 := by
  have he0 : 0 ≤ gramProfileExponent x slots ν 2 := le_max_left _ _
  have he : 1 - slots - 3 * x ≤ gramProfileExponent x slots ν 2 := by
    have h := (le_max_right (ν * (1 - slots - 2 * x))
      ((2 - 1) * (1 - slots) - (2 * 2 - 1) * x)).trans
      (le_max_right (0 : ℝ) _)
    change (2 - 1) * (1 - slots) - (2 * 2 - 1) * x ≤
      gramProfileExponent x slots ν 2 at h
    rw [show (2 - 1) * (1 - slots) - (2 * 2 - 1) * x =
      1 - slots - 3 * x by ring] at h
    exact h
  have hmax := max_le he0 he
  rw [gramProfileBoundary_eq]
  unfold ordinaryGramBoundary
  linarith

/-- Exceptional-frequency improvements alone cannot overcome the nonexceptional budget. -/
theorem gramProfileBoundary_gt_five_sixths_of_ordinary_unchanged (x slots ν : ℝ) :
    5 / 6 < gramProfileBoundary x slots ν 2 := by
  have h := (ordinaryGramBoundary_sharp_minimum x slots).1
  have h' := ordinaryGramBoundary_le_profile x slots ν
  linarith

/-- At slot length one sixth, the target is precisely three elementary Gram inequalities. -/
theorem gramProfileBoundary_one_sixth_le_iff (x ν κ : ℝ) :
    gramProfileBoundary x (1 / 6) ν κ ≤ 5 / 6 ↔
      x ≤ 1 / 6 ∧ ν * (15 - 36 * x) ≤ 1 - 6 * x ∧
        κ * (15 - 36 * x) ≤ 16 - 24 * x := by
  have h : gramProfileBoundary x (1 / 6) ν κ ≤ 5 / 6 ↔
      gramProfileExponent x (1 / 6) ν κ ≤ 1 / 18 - x / 3 := by
    rw [gramProfileBoundary_eq]
    norm_num [reflectedLoss]
    constructor <;> intro h <;> linarith
  rw [h, gramProfileExponent, max_le_iff, max_le_iff]
  constructor
  · rintro ⟨h0, hν, hκ⟩
    exact ⟨by linarith, by nlinarith, by nlinarith⟩
  · rintro ⟨h0, hν, hκ⟩
    exact ⟨by linarith, by nlinarith, by nlinarith⟩

private theorem five_sixths_necessary {x slots ν κ : ℝ} (hx : 0 ≤ x)
    (h : gramProfileBoundary x slots ν κ ≤ 5 / 6) :
    ν ≤ 1 / 15 ∧ κ + 4 * ν ≤ 4 / 3 := by
  let e := gramProfileExponent x slots ν κ
  let r := reflectedLoss slots
  have he0 : 0 ≤ e := le_max_left _ _
  have hr0 : 0 ≤ r := le_max_left _ _
  have hr : (6 * slots - 1) / 5 ≤ r := le_max_right _ _
  have hb : x + 3 * e + 3 * r ≤ slots := by
    rw [gramProfileBoundary_eq] at h
    change 5 / 6 + (x - slots) / 6 + e / 2 + r / 2 ≤ 5 / 6 at h
    linarith
  have ha : x + 3 * e ≤ slots := by linarith
  have hf : 5 * (x + 3 * e) + 13 * slots ≤ 3 := by linarith
  have hc : 5 * (x + 3 * e) + slots ≤ 1 := by linarith
  have ht : 0 < 1 - slots := by linarith
  have hd : 0 < 1 - slots - 2 * x := by linarith
  have hν : ν * (1 - slots - 2 * x) ≤ e :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hκ : κ * (1 - slots - 2 * x) - (1 - slots - x) ≤ e := by
    have he : (κ - 1) * (1 - slots) - (2 * κ - 1) * x ≤ e :=
      (le_max_right _ _).trans (le_max_right _ _)
    nlinarith only [he]
  constructor
  · have hp : (15 * ν - 1) * (1 - slots - 2 * x) ≤ 0 := by
      nlinarith only [hν, hc, hx]
    by_contra hn
    have hp' := mul_pos (by linarith : 0 < 15 * ν - 1) hd
    linarith
  · have hp : (κ + 4 * ν - 4 / 3) * (1 - slots - 2 * x) ≤ 0 := by
      nlinarith only [hν, hκ, hc]
    by_contra hn
    have hp' := mul_pos (by linarith : 0 < κ + 4 * ν - 4 / 3) hd
    linarith

/-- Exact feasibility region for five sixths, allowing both scales and slot length to vary. -/
theorem gramProfile_five_sixths_feasible_iff (ν κ : ℝ) (hν0 : 0 ≤ ν) :
    (∃ x slots : ℝ, 0 ≤ x ∧ gramProfileBoundary x slots ν κ ≤ 5 / 6) ↔
      ν ≤ 1 / 15 ∧ κ + 4 * ν ≤ 4 / 3 := by
  constructor
  · rintro ⟨x, slots, hx, h⟩
    exact five_sixths_necessary hx h
  · rintro ⟨hν, hκ⟩
    let d := 6 - 36 * ν
    let x := (1 - 15 * ν) / d
    have hd : 0 < d := by dsimp [d]; linarith
    have hx : 0 ≤ x := div_nonneg (by linarith) hd.le
    have hxe : x * d = 1 - 15 * ν := by
      dsimp [x]
      exact div_mul_cancel₀ _ hd.ne'
    have hx1 : x ≤ 1 / 6 := by
      dsimp [x]
      apply (div_le_iff₀ hd).2
      dsimp [d]
      linarith
    refine ⟨x, 1 / 6, hx, (gramProfileBoundary_one_sixth_le_iff x ν κ).2
      ⟨hx1, ?_, ?_⟩⟩
    · dsimp [d] at hxe
      nlinarith only [hxe]
    · have hdelta : (15 - 36 * x) * d = 54 := by
        dsimp [d] at hxe ⊢
        nlinarith only [hxe]
      have hright : (16 - 24 * x) * d = 72 - 216 * ν := by
        dsimp [d] at hxe ⊢
        nlinarith only [hxe]
      apply le_of_mul_le_mul_right (a := d) _ hd
      rw [mul_assoc, hdelta, hright]
      linarith

/-- An interior five-sixths profile with positive low-scale exponents. -/
theorem gramProfile_five_sixths_witness :
    gramProfileBoundary (5 / 48) (1 / 6) (1 / 30) (6 / 5) = 5 / 6 ∧
      1 - (1 / 6 : ℝ) - 5 / 48 = 35 / 48 ∧
      0 < (5 / 48 : ℝ) ∧ 0 < (35 / 48 : ℝ) := by
  norm_num [gramProfileBoundary, gramProfileExponent, principalShift, reflectedLoss]

/-- The three-term profile recovers the original seven-eighths normalization. -/
theorem gramProfile_published_boundary :
    gramProfileBoundary (17 / 48) (1 / 6) (1 / 6) 2 = 7 / 8 := by
  norm_num [gramProfileBoundary, gramProfileExponent, principalShift, reflectedLoss]

end RHTower.QuasiRHDetectorScaleBudget
