import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheFirstPrimeStageOpensPositive
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheFrozenFormInClosedForm

/-!
# The first-stage complement in closed form

At the first prime stage, window length `A = log 2 + ε`, the frozen form of a stage test is
`F(x_L, y, x_R) = Q(x_L) + Q(x_R) + 2⟨μ, ν⟩ + Q(y) + 2ℓ_{μ,ν}(y)`, with `μ = μ(x_L)`, `ν = ν(x_R)` the
trivial-divisor moment sequences and `ℓ_{μ,ν}(y) = ⟨μ, ν(y)⟩ + ⟨μ(y), ν⟩` linear in the interior test
`y`. Minimizing over `y` is a Schur complement:

* **Closed form** (`twoCollarForm_firstStage_eq`):
  `inf_y F = Q(x_L) + Q(x_R) + Φ_ε(μ, ν)`, `Φ_ε(μ, ν) = 2⟨μ, ν⟩ − ‖ℓ_{μ,ν}‖²`, where
  `‖ℓ‖² = sup_y ℓ(y)²/Q(y)` is the dual norm for Weil's form on the interior `[−log 2, −ε]`. This form
  is positive there, since the interior is shorter than `log 2`, and `Φ_ε` reads only the moments.
* **The dual norm is finite** (`firstStageDual_le`): `‖ℓ‖ ≤ √Q(x_L) + √Q(x_R)`, by Cauchy–Schwarz for
  Weil's form on `x_L + y` and on `y + x_R`, both of length `log 2`. Hence
  `Φ_ε(μ, ν) ≥ 2⟨μ, ν⟩ − Q(x_L) − Q(x_R) − 2√(Q(x_L)Q(x_R))`.
* **The first-stage race in moments** (`stageTests_nonneg_iff_firstStageComplement`): Weil's form is
  nonnegative on the stage tests of `A` iff `2w₂⟨x_L, J x_R⟩ ≤ Q(x_L) + Q(x_R) + Φ_ε(μ, ν)` for all
  collar data.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open CohomologyOfWindowsOfSpecZ DimensionZeroGeometryOfSpecZ WindowTowerOfSpecZ
  SpacingScaleHarmonicAnalysis CanonicalSystemOfTheWindowTower ArithmeticCastelnuovoSeveri
  RHTower.WeilMarkovPole

/-- The moment functional `ℓ_{μ,ν}(y) = ⟨μ, ν(y)⟩ + ⟨μ(y), ν⟩` on interior tests. -/
def interiorMomentFunctional (μ ν : ℝ → ℝ) (y : ℝ → ℝ) : ℝ :=
  (μ (1 / 2) * rightMoment y (1 / 2) - ∑' k : ℕ, μ (trivialExponent k) * rightMoment y (trivialExponent k)) +
    (leftMoment y (1 / 2) * ν (1 / 2) - ∑' k : ℕ, leftMoment y (trivialExponent k) * ν (trivialExponent k))

/-- The squared dual norm `sup_y ℓ(y)²/Q(y)` over the interior tests of the first stage. -/
def firstStageDual (ε : ℝ) (μ ν : ℝ → ℝ) : ℝ :=
  ⨆ y : {y : ℝ → ℝ // IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log (2 : ℕ)) y},
    interiorMomentFunctional μ ν y.1 ^ 2 / weilQuad y.1

/-- **The first-stage complement** `Φ_ε(μ, ν) = 2⟨μ, ν⟩ − ‖ℓ_{μ,ν}‖²`, a function of the two moment
sequences. -/
def firstStageComplement (ε : ℝ) (μ ν : ℝ → ℝ) : ℝ :=
  2 * (μ (1 / 2) * ν (1 / 2) - ∑' k : ℕ, μ (trivialExponent k) * ν (trivialExponent k)) -
    firstStageDual ε μ ν

theorem interiorMomentFunctional_eq (xL xR y : ℝ → ℝ) :
    interiorMomentFunctional (leftMoment xL) (rightMoment xR) y =
      momentPairing xL y + momentPairing y xR := rfl

theorem firstStageComplement_eq (ε : ℝ) (xL xR : ℝ → ℝ) :
    firstStageComplement ε (leftMoment xL) (rightMoment xR) =
      2 * momentPairing xL xR - firstStageDual ε (leftMoment xL) (rightMoment xR) := rfl

theorem leftMoment_mul (t : ℝ) (y : ℝ → ℝ) (σ : ℝ) :
    leftMoment (fun u => t * y u) σ = t * leftMoment y σ := by
  simp only [leftMoment, mul_assoc]
  exact integral_const_mul t _

theorem rightMoment_mul (t : ℝ) (y : ℝ → ℝ) (σ : ℝ) :
    rightMoment (fun u => t * y u) σ = t * rightMoment y σ := by
  simp only [rightMoment, mul_assoc]
  exact integral_const_mul t _

/-- The moment functional is homogeneous. -/
theorem interiorMomentFunctional_mul (μ ν : ℝ → ℝ) (t : ℝ) (y : ℝ → ℝ) :
    interiorMomentFunctional μ ν (fun u => t * y u) = t * interiorMomentFunctional μ ν y := by
  unfold interiorMomentFunctional
  simp only [rightMoment_mul, leftMoment_mul]
  have h1 : ∑' k : ℕ, μ (trivialExponent k) * (t * rightMoment y (trivialExponent k)) =
      t * ∑' k : ℕ, μ (trivialExponent k) * rightMoment y (trivialExponent k) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by ring
  have h2 : ∑' k : ℕ, t * leftMoment y (trivialExponent k) * ν (trivialExponent k) =
      t * ∑' k : ℕ, leftMoment y (trivialExponent k) * ν (trivialExponent k) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by ring
  rw [h1, h2]
  ring

theorem momentPairing_mul_right (f : ℝ → ℝ) (t : ℝ) (g : ℝ → ℝ) :
    momentPairing f (fun u => t * g u) = t * momentPairing f g := by
  simp only [momentPairing, rightMoment_mul]
  have h : ∑' k : ℕ, leftMoment f (trivialExponent k) * (t * rightMoment g (trivialExponent k)) =
      t * ∑' k : ℕ, leftMoment f (trivialExponent k) * rightMoment g (trivialExponent k) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by ring
  rw [h]
  ring

theorem momentPairing_mul_left (t : ℝ) (f g : ℝ → ℝ) :
    momentPairing (fun u => t * f u) g = t * momentPairing f g := by
  simp only [momentPairing, leftMoment_mul]
  have h : ∑' k : ℕ, t * leftMoment f (trivialExponent k) * rightMoment g (trivialExponent k) =
      t * ∑' k : ℕ, leftMoment f (trivialExponent k) * rightMoment g (trivialExponent k) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by ring
  rw [h]
  ring

theorem weilQuad_zero' : weilQuad (fun _ => (0 : ℝ)) = 0 := by
  have := weilQuad_mul_left 0 (fun _ => (0 : ℝ))
  simpa only [zero_mul, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] using this

theorem momentPairing_zero_right (f : ℝ → ℝ) : momentPairing f (fun _ => 0) = 0 := by
  simp [momentPairing, rightMoment]

theorem momentPairing_zero_left (g : ℝ → ℝ) : momentPairing (fun _ => 0) g = 0 := by
  simp [momentPairing, leftMoment]

variable {ε : ℝ} {xL xR y : ℝ → ℝ}

section Stage

variable (hεn : Real.log (2 : ℕ) + ε < Real.log ((2 : ℕ) + 1))

include hεn

/-- A left collar and an interior test couple through the moment pairing alone. -/
theorem weilQuad_collar_add_interior (hxL : ContDiff ℝ 2 xL) (hy : ContDiff ℝ 2 y)
    (hL : ∀ u, u ∉ Icc (-Real.log (2 : ℕ) - ε) (-Real.log (2 : ℕ)) → xL u = 0)
    (hI : ∀ u, u ∉ Icc (-Real.log (2 : ℕ)) (-ε) → y u = 0) :
    weilQuad (fun u => xL u + y u) = weilQuad xL + weilQuad y + 2 * momentPairing xL y := by
  have h := firstStage_frozenTwoCollar_eq hεn hxL hy (contDiff_const (c := (0 : ℝ))) hL hI
    (fun _ _ => rfl)
  simp only [frozenTwoCollar, add_zero, momentPairing_zero_right, weilQuad_zero', mul_zero] at h
  linarith only [h]

/-- An interior test and a right collar couple through the moment pairing alone. -/
theorem weilQuad_interior_add_collar (hy : ContDiff ℝ 2 y) (hxR : ContDiff ℝ 2 xR)
    (hI : ∀ u, u ∉ Icc (-Real.log (2 : ℕ)) (-ε) → y u = 0)
    (hR : ∀ u, u ∉ Icc (-ε) 0 → xR u = 0) :
    weilQuad (fun u => y u + xR u) = weilQuad y + weilQuad xR + 2 * momentPairing y xR := by
  have h := firstStage_frozenTwoCollar_eq hεn (contDiff_const (c := (0 : ℝ))) hy hxR
    (fun _ _ => rfl) hI hR
  simp only [frozenTwoCollar, zero_add, momentPairing_zero_left, weilQuad_zero', mul_zero,
    add_zero] at h
  linarith only [h]

end Stage

/-- Weil's form is nonnegative on tests of support length `log 2`. -/
theorem weilQuad_nonneg_of_length_log_two {H : ℝ → ℝ} (hH : ContDiff ℝ 2 H) {c : ℝ}
    (hv : ∀ u, u ∉ Icc (c - Real.log (2 : ℕ)) c → H u = 0) : 0 ≤ weilQuad H := by
  have hG : IsWindowTest (Real.log (2 : ℕ)) (fun u => H (u - -c)) :=
    ⟨hH.comp (contDiff_id.sub contDiff_const), fun u hu => hv _ fun hm =>
      hu ⟨by linarith only [hm.1], by linarith only [hm.2]⟩⟩
  have hb : Real.log (2 : ℕ) ≤ 181 / 250 := by
    have := log_two_lt_bound
    push_cast
    exact this.le
  have h := weilQuad_nonneg_of_short hb hG
  rwa [weilQuad_translate] at h

/-- Cauchy–Schwarz from positivity on a line. -/
theorem sq_le_mul_of_forall_nonneg {P B Q : ℝ} (hQ : 0 ≤ Q)
    (h : ∀ t : ℝ, 0 ≤ P + 2 * t * B + t ^ 2 * Q) : B ^ 2 ≤ P * Q := by
  rcases hQ.eq_or_lt with rfl | hQ0
  · by_contra hB
    have hne : B ≠ 0 := fun h0 => hB (by simp [h0])
    have ht := h (-(P + 1) / (2 * B))
    have e : P + 2 * (-(P + 1) / (2 * B)) * B + (-(P + 1) / (2 * B)) ^ 2 * 0 = -1 := by
      field_simp
      ring
    rw [e] at ht
    linarith only [ht]
  · have ht := h (-B / Q)
    have e : P + 2 * (-B / Q) * B + (-B / Q) ^ 2 * Q = P - B ^ 2 / Q := by
      field_simp
      ring
    rw [e, sub_nonneg, div_le_iff₀ hQ0] at ht
    exact ht

section Dual

variable (hε : 0 < ε) (hεn : Real.log (2 : ℕ) + ε < Real.log ((2 : ℕ) + 1))
  (hxL : ContDiff ℝ 2 xL) (hxR : ContDiff ℝ 2 xR)
  (hL : ∀ u, u ∉ Icc (-Real.log (2 : ℕ) - ε) (-Real.log (2 : ℕ)) → xL u = 0)
  (hR : ∀ u, u ∉ Icc (-ε) 0 → xR u = 0)

theorem interior_vanish (hh : IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log (2 : ℕ)) y) :
    ∀ u, u ∉ Icc (-Real.log (2 : ℕ)) (-ε) → y u = 0 := fun u hu =>
  hh.vanish u (by rwa [show Real.log (2 : ℕ) - (Real.log (2 : ℕ) + ε) = -ε by ring])

theorem IsInteriorTest.mul_left (t : ℝ)
    (hh : IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log (2 : ℕ)) y) :
    IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log (2 : ℕ)) (fun u => t * y u) :=
  ⟨contDiff_const.mul hh.contDiff, fun u hu => by rw [hh.vanish u hu, mul_zero]⟩

include hε in
/-- Weil's form is nonnegative on interior tests. -/
theorem weilQuad_interior_nonneg (hh : IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log (2 : ℕ)) y) :
    0 ≤ weilQuad y :=
  weilQuad_nonneg_of_length_log_two (c := 0) hh.contDiff fun u hu => interior_vanish hh u fun hm =>
    hu ⟨by linarith only [hm.1], by linarith only [hm.2, hε]⟩

/-- The collar width is below `log 2`. -/
private theorem eps_le_log_two (hεn : Real.log (2 : ℕ) + ε < Real.log ((2 : ℕ) + 1)) :
    ε ≤ Real.log (2 : ℕ) := by
  have h : Real.log (((2 : ℕ) : ℝ) + 1) ≤ Real.log (((2 : ℕ) : ℝ) * 2) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_mul (by norm_num) (by norm_num)] at h
  have e : Real.log (2 : ℝ) = Real.log ((2 : ℕ) : ℝ) := by norm_num
  rw [e] at h
  linarith only [h, hεn]

include hεn hxL hL in
theorem weilQuad_leftCollar_nonneg : 0 ≤ weilQuad xL :=
  weilQuad_nonneg_of_length_log_two (c := -Real.log (2 : ℕ)) hxL fun u hu => hL u fun hm =>
    hu ⟨by linarith only [hm.1, eps_le_log_two hεn], hm.2⟩

include hεn hxR hR in
theorem weilQuad_rightCollar_nonneg : 0 ≤ weilQuad xR :=
  weilQuad_nonneg_of_length_log_two (c := 0) hxR fun u hu => hR u fun hm =>
    hu ⟨by linarith only [hm.1, eps_le_log_two hεn], hm.2⟩

include hε hεn hxL hL in
/-- Cauchy–Schwarz for Weil's form across the left cut. -/
theorem sq_momentPairing_left_le
    (hh : IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log (2 : ℕ)) y) :
    momentPairing xL y ^ 2 ≤ weilQuad xL * weilQuad y := by
  refine sq_le_mul_of_forall_nonneg (weilQuad_interior_nonneg hε hh) fun t => ?_
  have hty := IsInteriorTest.mul_left t hh
  have hIt := interior_vanish hty
  have e := weilQuad_collar_add_interior hεn hxL hty.contDiff hL hIt
  rw [weilQuad_mul_left, momentPairing_mul_right] at e
  have hpos := weilQuad_nonneg_of_length_log_two (c := -ε) (hxL.add hty.contDiff)
    (H := fun u => xL u + t * y u) fun u hu => by
      have h1 : xL u = 0 := hL u fun hm => hu ⟨by linarith only [hm.1], by
        linarith only [hm.2, eps_le_log_two hεn, hε]⟩
      have h2 : t * y u = 0 := hIt u fun hm => hu ⟨by linarith only [hm.1, hε], hm.2⟩
      simp only [h1, h2, add_zero]
  linarith only [e, hpos]

include hε hεn hxR hR in
/-- Cauchy–Schwarz for Weil's form across the right cut. -/
theorem sq_momentPairing_right_le
    (hh : IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log (2 : ℕ)) y) :
    momentPairing y xR ^ 2 ≤ weilQuad xR * weilQuad y := by
  refine sq_le_mul_of_forall_nonneg (weilQuad_interior_nonneg hε hh) fun t => ?_
  have hty := IsInteriorTest.mul_left t hh
  have hIt := interior_vanish hty
  have e := weilQuad_interior_add_collar hεn hty.contDiff hxR hIt hR
  rw [weilQuad_mul_left, momentPairing_mul_left] at e
  have hpos := weilQuad_nonneg_of_length_log_two (c := 0) (hty.contDiff.add hxR)
    (H := fun u => t * y u + xR u) fun u hu => by
      have h1 : t * y u = 0 := hIt u fun hm => hu ⟨by linarith only [hm.1], by
        linarith only [hm.2, hε]⟩
      have h2 : xR u = 0 := hR u fun hm => hu ⟨by
        linarith only [hm.1, eps_le_log_two hεn], hm.2⟩
      simp only [h1, h2, add_zero]
  linarith only [e, hpos]

include hε hεn hxL hxR hL hR in
/-- `ℓ(y)² ≤ (√Q(x_L) + √Q(x_R))² Q(y)`. -/
theorem sq_interiorMomentFunctional_le
    (hh : IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log (2 : ℕ)) y) :
    interiorMomentFunctional (leftMoment xL) (rightMoment xR) y ^ 2 ≤
      (Real.sqrt (weilQuad xL) + Real.sqrt (weilQuad xR)) ^ 2 * weilQuad y := by
  have hQy := weilQuad_interior_nonneg hε hh
  have hQL := weilQuad_leftCollar_nonneg hεn hxL hL
  have hQR := weilQuad_rightCollar_nonneg hεn hxR hR
  have h1 := Real.abs_le_sqrt (sq_momentPairing_left_le hε hεn hxL hL hh)
  have h2 := Real.abs_le_sqrt (sq_momentPairing_right_le hε hεn hxR hR hh)
  rw [Real.sqrt_mul hQL] at h1
  rw [Real.sqrt_mul hQR] at h2
  rw [interiorMomentFunctional_eq, ← sq_abs]
  have htri := abs_add_le (momentPairing xL y) (momentPairing y xR)
  have hs := Real.sqrt_nonneg (weilQuad y)
  have hb : |momentPairing xL y + momentPairing y xR| ≤
      (Real.sqrt (weilQuad xL) + Real.sqrt (weilQuad xR)) * Real.sqrt (weilQuad y) := by
    rw [add_mul]
    linarith only [htri, h1, h2]
  calc |momentPairing xL y + momentPairing y xR| ^ 2
      ≤ ((Real.sqrt (weilQuad xL) + Real.sqrt (weilQuad xR)) * Real.sqrt (weilQuad y)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hQy]

include hε hεn hxL hxR hL hR in
/-- The quotients defining the dual norm are bounded. -/
theorem quotient_le (y : {y : ℝ → ℝ // IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log (2 : ℕ)) y}) :
    interiorMomentFunctional (leftMoment xL) (rightMoment xR) y.1 ^ 2 / weilQuad y.1 ≤
      (Real.sqrt (weilQuad xL) + Real.sqrt (weilQuad xR)) ^ 2 := by
  have hQy := weilQuad_interior_nonneg hε y.2
  rcases hQy.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]
    positivity
  · rw [div_le_iff₀ hpos]
    exact sq_interiorMomentFunctional_le hε hεn hxL hxR hL hR y.2

include hε hεn hxL hxR hL hR in
theorem bddAbove_quotient : BddAbove (Set.range fun y :
    {y : ℝ → ℝ // IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log (2 : ℕ)) y} =>
      interiorMomentFunctional (leftMoment xL) (rightMoment xR) y.1 ^ 2 / weilQuad y.1) :=
  ⟨_, by rintro _ ⟨y, rfl⟩; exact quotient_le hε hεn hxL hxR hL hR y⟩

instance : Nonempty {y : ℝ → ℝ // IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log (2 : ℕ)) y} :=
  ⟨⟨fun _ => 0, isInteriorTest_zero⟩⟩

include hε hεn hxL hxR hL hR in
/-- **The dual norm is finite**: `‖ℓ‖ ≤ √Q(x_L) + √Q(x_R)`. -/
theorem firstStageDual_le :
    firstStageDual ε (leftMoment xL) (rightMoment xR) ≤
      (Real.sqrt (weilQuad xL) + Real.sqrt (weilQuad xR)) ^ 2 :=
  ciSup_le (quotient_le hε hεn hxL hxR hL hR)

include hεn hxL hxR hL hR in
/-- The frozen form on a stage test splits off the collars and the interior energy. -/
theorem frozenTwoCollar_eq_interior {y : ℝ → ℝ}
    (hh : IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log (2 : ℕ)) y) :
    frozenTwoCollar xL y xR =
      (weilQuad xL + weilQuad xR + 2 * momentPairing xL xR) + weilQuad y +
        2 * interiorMomentFunctional (leftMoment xL) (rightMoment xR) y := by
  rw [firstStage_frozenTwoCollar_eq hεn hxL hh.contDiff hxR hL (interior_vanish hh) hR,
    interiorMomentFunctional_eq]
  ring

include hε hεn hxL hxR hL hR in
/-- Completing the square: the frozen form dominates the Schur complement. -/
theorem le_frozenTwoCollar {y : ℝ → ℝ}
    (hh : IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log (2 : ℕ)) y) :
    weilQuad xL + weilQuad xR + firstStageComplement ε (leftMoment xL) (rightMoment xR) ≤
      frozenTwoCollar xL y xR := by
  rw [frozenTwoCollar_eq_interior hεn hxL hxR hL hR hh, firstStageComplement_eq]
  have hq := le_ciSup (bddAbove_quotient hε hεn hxL hxR hL hR) ⟨y, hh⟩
  change interiorMomentFunctional (leftMoment xL) (rightMoment xR) y ^ 2 / weilQuad y ≤
    firstStageDual ε (leftMoment xL) (rightMoment xR) at hq
  set ℓy := interiorMomentFunctional (leftMoment xL) (rightMoment xR) y
  set D := firstStageDual ε (leftMoment xL) (rightMoment xR)
  have hQy := weilQuad_interior_nonneg hε hh
  rcases hQy.eq_or_lt with h0 | hpos
  · have hzero : ℓy = 0 := by
      have h := sq_interiorMomentFunctional_le hε hεn hxL hxR hL hR hh
      rw [← h0, mul_zero] at h
      exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm h (sq_nonneg _))
    have hD : 0 ≤ D := by
      rw [hzero] at hq
      simpa using hq
    rw [hzero, ← h0]
    linarith only [hD]
  · have hsq : 0 ≤ (weilQuad y + ℓy) ^ 2 / weilQuad y := by positivity
    have e : (weilQuad y + ℓy) ^ 2 / weilQuad y = weilQuad y + 2 * ℓy + ℓy ^ 2 / weilQuad y := by
      field_simp
      ring
    rw [e] at hsq
    linarith only [hsq, hq]

include hε hεn hxL hxR hL hR in
/-- A lower bound for the frozen form along all interior tests lies below the Schur complement. -/
theorem le_complement_of_forall_le {r : ℝ}
    (hr : ∀ y : ℝ → ℝ, IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log (2 : ℕ)) y →
      r ≤ frozenTwoCollar xL y xR) :
    r ≤ weilQuad xL + weilQuad xR + firstStageComplement ε (leftMoment xL) (rightMoment xR) := by
  rw [firstStageComplement_eq]
  set K := weilQuad xL + weilQuad xR + 2 * momentPairing xL xR with hK
  have hval (y : ℝ → ℝ) (hh : IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log (2 : ℕ)) y) :
      r ≤ K + weilQuad y +
        2 * interiorMomentFunctional (leftMoment xL) (rightMoment xR) y := by
    have := hr y hh
    rwa [frozenTwoCollar_eq_interior hεn hxL hxR hL hR hh] at this
  have hK0 : r ≤ K := by
    have h := hval (fun _ => 0) isInteriorTest_zero
    have hm : interiorMomentFunctional (leftMoment xL) (rightMoment xR) (fun _ => 0) = 0 := by
      rw [interiorMomentFunctional_eq, momentPairing_zero_right, momentPairing_zero_left, add_zero]
    rw [weilQuad_zero', hm] at h
    linarith only [h]
  have hD : firstStageDual ε (leftMoment xL) (rightMoment xR) ≤ K - r := by
    refine ciSup_le fun y => ?_
    have hQy := weilQuad_interior_nonneg hε y.2
    rcases hQy.eq_or_lt with h0 | hpos
    · rw [← h0, div_zero]
      linarith only [hK0]
    · set ℓy := interiorMomentFunctional (leftMoment xL) (rightMoment xR) y.1
      have h := hval _ (IsInteriorTest.mul_left (-ℓy / weilQuad y.1) y.2)
      rw [weilQuad_mul_left, interiorMomentFunctional_mul] at h
      have e : K + (-ℓy / weilQuad y.1) ^ 2 * weilQuad y.1 +
          2 * (-ℓy / weilQuad y.1 * ℓy) = K - ℓy ^ 2 / weilQuad y.1 := by
        field_simp
        ring
      rw [e] at h
      linarith only [h]
  linarith only [hD]

include hε hεn hxL hxR hL hR in
/-- **The first-stage complement in closed form**: the two-collar form of the first stage is
`Q(x_L) + Q(x_R) + Φ_ε(μ(x_L), ν(x_R))`. -/
theorem twoCollarForm_firstStage_eq :
    twoCollarForm 1 (Real.log (2 : ℕ) + ε) (fun u => xL u + xR u) =
      ((weilQuad xL + weilQuad xR +
        firstStageComplement ε (leftMoment xL) (rightMoment xR) : ℝ) : EReal) := by
  have hεn' : Real.log ((1 + 1 : ℕ) : ℝ) + ε < Real.log ((1 + 2 : ℕ) : ℝ) := by
    have e : ((1 + 2 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) + 1 := by norm_num
    rw [e]
    exact hεn
  have hstage (h : ℝ → ℝ) (hh : IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log (2 : ℕ)) h) :
      stageForm 1 (fun u => (xL u + xR u) + h u) = frozenTwoCollar xL h xR := by
    have hs := stageForm_stageTest (N := 1) le_rfl hε hεn' hxL hh.contDiff hxR hL
      (interior_vanish hh) hR
    rw [← hs]
    congr 1
    funext u
    ring
  unfold twoCollarForm
  apply le_antisymm
  · by_contra hlt
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp (not_le.mp hlt)
    have hle := le_complement_of_forall_le (r := r) hε hεn hxL hxR hL hR fun y hy => by
      have h := hr2.le.trans (iInf_le _ (⟨y, hy⟩ : {h : ℝ → ℝ //
        IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log ((1 + 1 : ℕ) : ℝ)) h}))
      rw [EReal.coe_le_coe_iff] at h
      rwa [show stageForm 1 (fun u => (xL u + xR u) + y u) = frozenTwoCollar xL y xR from
        hstage y hy] at h
    exact absurd (EReal.coe_lt_coe_iff.mp hr1) (not_lt.mpr hle)
  · refine le_iInf fun h => ?_
    rw [EReal.coe_le_coe_iff, show stageForm 1 (fun u => (xL u + xR u) + h.1 u) =
      frozenTwoCollar xL h.1 xR from hstage h.1 h.2]
    exact le_frozenTwoCollar hε hεn hxL hxR hL hR h.2

include hε hεn hxL hxR hL hR in
/-- **Size of the complement**: `Φ_ε(μ, ν) ≥ 2⟨μ, ν⟩ − (√Q(x_L) + √Q(x_R))²`, so the two-collar form
is at least `2⟨μ, ν⟩ − 2√(Q(x_L)Q(x_R))`. -/
theorem two_mul_momentPairing_sub_le :
    2 * momentPairing xL xR - 2 * Real.sqrt (weilQuad xL * weilQuad xR) ≤
      weilQuad xL + weilQuad xR + firstStageComplement ε (leftMoment xL) (rightMoment xR) := by
  have hD := firstStageDual_le hε hεn hxL hxR hL hR
  have hQL := weilQuad_leftCollar_nonneg hεn hxL hL
  have hQR := weilQuad_rightCollar_nonneg hεn hxR hR
  rw [firstStageComplement_eq]
  have e : (Real.sqrt (weilQuad xL) + Real.sqrt (weilQuad xR)) ^ 2 =
      weilQuad xL + weilQuad xR + 2 * Real.sqrt (weilQuad xL * weilQuad xR) := by
    rw [add_sq, Real.sq_sqrt hQL, Real.sq_sqrt hQR, Real.sqrt_mul hQL]
    ring
  rw [e] at hD
  linarith only [hD]

end Dual

/-- **The first-stage race in moments.** Weil's form is nonnegative on the stage tests of
`A = log 2 + ε` iff `2w₂⟨x_L, J x_R⟩ ≤ Q(x_L) + Q(x_R) + Φ_ε(μ(x_L), ν(x_R))` for all collar data. -/
theorem stageTests_nonneg_iff_firstStageComplement (hε : 0 < ε)
    (hεn : Real.log (2 : ℕ) + ε < Real.log ((2 : ℕ) + 1)) :
    (∀ xL y xR : ℝ → ℝ, ContDiff ℝ 2 xL → ContDiff ℝ 2 y → ContDiff ℝ 2 xR →
      (∀ u, u ∉ Icc (-Real.log (2 : ℕ) - ε) (-Real.log (2 : ℕ)) → xL u = 0) →
      (∀ u, u ∉ Icc (-Real.log (2 : ℕ)) (-ε) → y u = 0) → (∀ u, u ∉ Icc (-ε) 0 → xR u = 0) →
        0 ≤ weilQuad (fun u => xL u + y u + xR u)) ↔
    (∀ xL xR : ℝ → ℝ, ContDiff ℝ 2 xL → ContDiff ℝ 2 xR →
      (∀ u, u ∉ Icc (-Real.log (2 : ℕ) - ε) (-Real.log (2 : ℕ)) → xL u = 0) →
      (∀ u, u ∉ Icc (-ε) 0 → xR u = 0) →
        2 * RHTower.vonMangoldtAtom 2 * crossCorr xL xR (Real.log (2 : ℕ)) ≤
          weilQuad xL + weilQuad xR + firstStageComplement ε (leftMoment xL) (rightMoment xR)) := by
  rw [stage_nonneg_iff le_rfl hεn]
  constructor
  · intro h xL xR hxL hxR hL hR
    refine le_complement_of_forall_le hε hεn hxL hxR hL hR fun y hy => ?_
    exact h xL y xR hxL hy.contDiff hxR hL (interior_vanish hy) hR
  · intro h xL y xR hxL hy hxR hL hI hR
    have hint : IsInteriorTest (Real.log (2 : ℕ) + ε) (Real.log (2 : ℕ)) y :=
      ⟨hy, fun u hu => hI u (by
        rwa [show Real.log (2 : ℕ) - (Real.log (2 : ℕ) + ε) = -ε by ring] at hu)⟩
    exact (h xL xR hxL hxR hL hR).trans (le_frozenTwoCollar hε hεn hxL hxR hL hR hint)

end GaloisForLFunctions.GrowingWindowsOfSpecZ

#print axioms GaloisForLFunctions.GrowingWindowsOfSpecZ.twoCollarForm_firstStage_eq
#print axioms GaloisForLFunctions.GrowingWindowsOfSpecZ.stageTests_nonneg_iff_firstStageComplement
#print axioms GaloisForLFunctions.GrowingWindowsOfSpecZ.two_mul_momentPairing_sub_le
