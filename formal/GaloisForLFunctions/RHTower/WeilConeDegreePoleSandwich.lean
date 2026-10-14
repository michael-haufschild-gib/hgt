import GaloisForLFunctions.RHTower.WeilConeDegreeTwinRigidity

/-!
# Blind tests see only the pole weight: the pole-order sandwich

A test `k` is *blind* (`IsBlindTest`) if `k(log n) + k(−log n) = 0` for every `n ≥ 2`.  On a blind
test the prime sum of every Weil functional vanishes, whatever the weights.  So the degree-`d`
functional with pole order `κ` is

`W_{d,κ}(lam; k) = d · A(k) + (κ − d) · P(k)`   (`weilDegreePoleFunctional_of_blind`),

where `P(k) = k̂(i/2) + k̂(−i/2)` is the pole term (`weilPoleTerm`) and `A(k) = P(k) + arch(k)` is
the blind value of `ζ`'s archimedean datum (`blindWeilValue`).  Neither depends on `lam` or on `ζ`.
Likewise the pole-weight-`β` functional is `A(k) + (β − 1) P(k)` (`weilPoleWeightFunctional_of_blind`).

**Pole-order sandwich** (`le_mul_one_add_div_of_blind_pole_neg`).  Suppose the degree-`d` functional
with pole order `κ` is nonnegative on every autocorrelation, which is what Weil's explicit formula
gives for a Dirichlet series with gamma factor `Γ_ℝ(s)^d`, conductor `1` and pole order `κ` whose
zeros are all critical.  Then every blind autocorrelation `g` with `Re P(g) < 0` gives

`κ ≤ d (1 + Re A(g) / |Re P(g)|)`.

With the lower bound `κ ≥ d` (`not_forall_re_weilDegreePoleFunctional_nonneg`), the pole order is
squeezed between `d` and `d (1 + c*)`, where `c* = inf Re A/|Re P|` over pole-negative blind
autocorrelations is an absolute constant free of `ζ`.

**Pole-weight window** (`le_one_add_div_of_blind_pole_neg`, `one_sub_div_le_of_blind_pole_pos`).
If the pole-weight-`β` functional is nonnegative on every autocorrelation, then
`β ≤ 1 + Re A(g)/|Re P(g)|` for every pole-negative blind autocorrelation `g`, and
`β ≥ 1 − Re A(g)/Re P(g)` for every pole-positive one.
-/

open Complex Zeta23

noncomputable section

namespace RHTower

/-- A test is blind if its symmetric values at every `log n`, `n ≥ 2`, vanish. -/
def IsBlindTest (k : ℝ → ℂ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → k (Real.log n) + k (-Real.log n) = 0

/-- The pole term `k̂(i/2) + k̂(−i/2)`. -/
def weilPoleTerm (k : ℝ → ℂ) : ℂ := paperFT k (I / 2) + paperFT k (-I / 2)

/-- The blind value `A(k) = pole + arch`: the full Weil functional with no prime weights. -/
def blindWeilValue (k : ℝ → ℂ) : ℂ := weilFullFunctional (fun _ => 0) k

/-- On a blind test every weighted prime sum vanishes. -/
theorem tsum_primeSum_eq_zero_of_blind (w : ℕ → ℝ) {k : ℝ → ℂ} (hk : IsBlindTest k) :
    ∑' n : ℕ, ((if 2 ≤ n then w n else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) = 0 := by
  have h : ∀ n : ℕ,
      ((if 2 ≤ n then w n else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) = 0 := by
    intro n
    by_cases hn : 2 ≤ n
    · rw [hk n hn, mul_zero]
    · rw [if_neg hn, ofReal_zero, zero_mul]
  rw [tsum_congr h, tsum_zero]

/-- The full Weil functional of any weights equals the blind value on a blind test. -/
theorem weilFullFunctional_of_blind (lam : ℕ → ℝ) {k : ℝ → ℂ} (hk : IsBlindTest k) :
    weilFullFunctional lam k = blindWeilValue k := by
  unfold blindWeilValue weilFullFunctional
  rw [tsum_primeSum_eq_zero_of_blind (fun n => lam n / Real.sqrt n) hk,
    tsum_primeSum_eq_zero_of_blind (fun n => (0 : ℝ) / Real.sqrt n) hk]

/-- **Degree-`d` functional on a blind test**: `d · A(k) + (κ − d) · P(k)`. -/
theorem weilDegreePoleFunctional_of_blind (d κ : ℝ) (lam : ℕ → ℝ) {k : ℝ → ℂ}
    (hk : IsBlindTest k) :
    weilDegreePoleFunctional d κ lam k =
      (d : ℂ) * blindWeilValue k + ((κ - d : ℝ) : ℂ) * weilPoleTerm k := by
  have hA : blindWeilValue k = paperFT k (I / 2) + paperFT k (-I / 2) +
      (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ) := by
    unfold blindWeilValue weilFullFunctional
    rw [tsum_primeSum_eq_zero_of_blind (fun n => (0 : ℝ) / Real.sqrt n) hk]
    ring
  unfold weilDegreePoleFunctional weilDegreeFunctional weilPoleTerm
  rw [tsum_primeSum_eq_zero_of_blind (fun n => lam n / Real.sqrt n) hk, hA]
  ring

/-- **Pole-weight functional on a blind test**: `A(k) + (β − 1) · P(k)`. -/
theorem weilPoleWeightFunctional_of_blind (β : ℝ) (lam : ℕ → ℝ) {k : ℝ → ℂ}
    (hk : IsBlindTest k) :
    WeilPoleWeight.weilPoleWeightFunctional β lam k =
      blindWeilValue k + ((β : ℂ) - 1) * weilPoleTerm k := by
  unfold WeilPoleWeight.weilPoleWeightFunctional weilPoleTerm
  rw [weilFullFunctional_of_blind lam hk]

/-- **Pole-order sandwich.**  If the degree-`d` functional with pole order `κ` is nonnegative on
every autocorrelation, then every blind autocorrelation with negative pole term gives
`κ ≤ d (1 + Re A/|Re P|)`. -/
theorem le_mul_one_add_div_of_blind_pole_neg {d κ : ℝ} {lam : ℕ → ℝ}
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      0 ≤ (weilDegreePoleFunctional d κ lam (EF.weilTest f f)).re)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hblind : IsBlindTest (EF.weilTest f f)) (hP : (weilPoleTerm (EF.weilTest f f)).re < 0) :
    κ ≤ d * (1 + (blindWeilValue (EF.weilTest f f)).re /
      |(weilPoleTerm (EF.weilTest f f)).re|) := by
  have h := hpos f hf hfc
  rw [weilDegreePoleFunctional_of_blind d κ lam hblind, add_re, re_ofReal_mul,
    re_ofReal_mul] at h
  set A := (blindWeilValue (EF.weilTest f f)).re
  set P := (weilPoleTerm (EF.weilTest f f)).re
  rw [abs_of_neg hP]
  have hP' : 0 < -P := by linarith
  have h1 : (κ - d) * -P ≤ d * A := by linarith
  have h2 : κ - d ≤ d * A / -P := by rw [le_div_iff₀ hP']; linarith
  have h3 : d * (1 + A / -P) = d + d * A / -P := by ring
  linarith

/-- **Upper end of the pole-weight window.**  If the pole-weight-`β` functional is nonnegative on
every autocorrelation, then `β ≤ 1 + Re A/|Re P|` for every pole-negative blind autocorrelation. -/
theorem le_one_add_div_of_blind_pole_neg {β : ℝ} {lam : ℕ → ℝ}
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      0 ≤ (WeilPoleWeight.weilPoleWeightFunctional β lam (EF.weilTest f f)).re)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hblind : IsBlindTest (EF.weilTest f f)) (hP : (weilPoleTerm (EF.weilTest f f)).re < 0) :
    β ≤ 1 + (blindWeilValue (EF.weilTest f f)).re / |(weilPoleTerm (EF.weilTest f f)).re| := by
  have h := hpos f hf hfc
  rw [weilPoleWeightFunctional_of_blind β lam hblind, add_re] at h
  have hmul : (((β : ℂ) - 1) * weilPoleTerm (EF.weilTest f f)).re =
      (β - 1) * (weilPoleTerm (EF.weilTest f f)).re := by
    rw [show ((β : ℂ) - 1) = ((β - 1 : ℝ) : ℂ) by push_cast; ring, re_ofReal_mul]
  rw [hmul] at h
  set A := (blindWeilValue (EF.weilTest f f)).re
  set P := (weilPoleTerm (EF.weilTest f f)).re
  rw [abs_of_neg hP]
  have hP' : 0 < -P := by linarith
  have h1 : (β - 1) * -P ≤ A := by linarith
  have h2 : β - 1 ≤ A / -P := by rw [le_div_iff₀ hP']; linarith
  linarith

/-- **Lower end of the pole-weight window.**  If the pole-weight-`β` functional is nonnegative on
every autocorrelation, then `β ≥ 1 − Re A/Re P` for every pole-positive blind autocorrelation. -/
theorem one_sub_div_le_of_blind_pole_pos {β : ℝ} {lam : ℕ → ℝ}
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      0 ≤ (WeilPoleWeight.weilPoleWeightFunctional β lam (EF.weilTest f f)).re)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hblind : IsBlindTest (EF.weilTest f f)) (hP : 0 < (weilPoleTerm (EF.weilTest f f)).re) :
    1 - (blindWeilValue (EF.weilTest f f)).re / (weilPoleTerm (EF.weilTest f f)).re ≤ β := by
  have h := hpos f hf hfc
  rw [weilPoleWeightFunctional_of_blind β lam hblind, add_re] at h
  have hmul : (((β : ℂ) - 1) * weilPoleTerm (EF.weilTest f f)).re =
      (β - 1) * (weilPoleTerm (EF.weilTest f f)).re := by
    rw [show ((β : ℂ) - 1) = ((β - 1 : ℝ) : ℂ) by push_cast; ring, re_ofReal_mul]
  rw [hmul] at h
  set A := (blindWeilValue (EF.weilTest f f)).re
  set P := (weilPoleTerm (EF.weilTest f f)).re
  have h1 : -A ≤ (β - 1) * P := by linarith
  have h2 : -A / P ≤ β - 1 := by rw [div_le_iff₀ hP]; linarith
  have h3 : -A / P = -(A / P) := neg_div P A
  linarith

end RHTower
