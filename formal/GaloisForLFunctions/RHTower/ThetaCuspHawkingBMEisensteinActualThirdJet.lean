import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualSecondStokesDefect

/-!
# Genuine third jets of the actual completed Eisenstein Poincare series

Corpus conjecture C-A.9t4b requires the differentiated eigen equations entering the literal
second Bochner--Stokes current.  This module constructs the four third real jets in the existing
absolute-convergence chamber.  The direct normal-convergence work is concentrated in `xxx`,
`xxy`, and `xyy`; the final `yyy` component is forced by the vertically differentiated actual
eigen equation.

RH chain:

`actual third jets -> second defect = divergence -> second modular Green/Stokes -> actual
balanced BM ++- coefficient -> negative BM leg -> conserved left-QNM projection -> HC94 -> RH`.
-/

open Complex Real Set Filter Topology
open scoped BigOperators

namespace RHTower
noncomputable section

private def d4BMSeedH1Coefficient
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  -2 * s * (p.pair.1 : ℂ) * (d4BMPoincareHorizontalLinear z p : ℂ) /
    (d4BMPoincareQuadratic z p.pair : ℂ)

private def d4BMSeedH2Coefficient
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  -2 * s * (p.pair.1 : ℂ) ^ 2 /
      (d4BMPoincareQuadratic z p.pair : ℂ) +
    4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 2 *
      (d4BMPoincareHorizontalLinear z p : ℂ) ^ 2 /
        (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2

private def d4BMSeedV1Coefficient
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  s / (z.y : ℂ) -
    2 * s * (p.pair.1 : ℂ) ^ 2 * (z.y : ℂ) /
      (d4BMPoincareQuadratic z p.pair : ℂ)

private def d4BMSeedV2Coefficient
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  s * (s - 1) / (z.y : ℂ) ^ 2 -
    2 * s * (1 + 2 * s) * (p.pair.1 : ℂ) ^ 2 /
      (d4BMPoincareQuadratic z p.pair : ℂ) +
    4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 4 * (z.y : ℂ) ^ 2 /
      (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2

private def d4BMSeedMixedCoefficient
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  4 * s * (p.pair.1 : ℂ) ^ 3 * (z.y : ℂ) *
      (d4BMPoincareHorizontalLinear z p : ℂ) /
      (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2 +
    d4BMSeedV1Coefficient z s p * d4BMSeedH1Coefficient z s p

private def d4BMSeedH2HorizontalDerivativeCoefficient
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  4 * s * (p.pair.1 : ℂ) ^ 3 *
      (d4BMPoincareHorizontalLinear z p : ℂ) /
      (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2 +
    8 * s * (s + 1) * (p.pair.1 : ℂ) ^ 3 *
      (d4BMPoincareHorizontalLinear z p : ℂ) /
      (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2 -
    16 * s * (s + 1) * (p.pair.1 : ℂ) ^ 3 *
      (d4BMPoincareHorizontalLinear z p : ℂ) ^ 3 /
      (d4BMPoincareQuadratic z p.pair : ℂ) ^ 3

private def d4BMSeedH2VerticalDerivativeCoefficient
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  4 * s * (p.pair.1 : ℂ) ^ 4 * (z.y : ℂ) /
      (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2 -
    16 * s * (s + 1) * (p.pair.1 : ℂ) ^ 4 *
      (d4BMPoincareHorizontalLinear z p : ℂ) ^ 2 * (z.y : ℂ) /
      (d4BMPoincareQuadratic z p.pair : ℂ) ^ 3

private def d4BMSeedV2HorizontalDerivativeCoefficient
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  4 * s * (1 + 2 * s) * (p.pair.1 : ℂ) ^ 3 *
      (d4BMPoincareHorizontalLinear z p : ℂ) /
      (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2 -
    16 * s * (s + 1) * (p.pair.1 : ℂ) ^ 5 * (z.y : ℂ) ^ 2 *
      (d4BMPoincareHorizontalLinear z p : ℂ) /
      (d4BMPoincareQuadratic z p.pair : ℂ) ^ 3

/-- Actual `partial_x^3` jet of one primitive Poincare seed. -/
def d4BMPoincareSeedHorizontalThirdJet
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  d4BMSeedH2HorizontalDerivativeCoefficient z s p * d4BMPoincareSeed z s p +
    d4BMSeedH1Coefficient z s p * d4BMPoincareSeedHorizontalSecondJet z s p

/-- Actual `partial_x^2 partial_y` jet of one primitive Poincare seed. -/
def d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  d4BMSeedH2VerticalDerivativeCoefficient z s p * d4BMPoincareSeed z s p +
    d4BMSeedV1Coefficient z s p * d4BMPoincareSeedHorizontalSecondJet z s p

/-- Actual `partial_x partial_y^2` jet of one primitive Poincare seed. -/
def d4BMPoincareSeedHorizontalVerticalVerticalThirdJet
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  s * (s - 1) / (z.y : ℂ) ^ 2 *
      d4BMPoincareSeedHorizontalFirstJet z s p -
    d4BMPoincareSeedHorizontalThirdJet z s p

private theorem d4BM_seedJet_coefficient_eq
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeedHorizontalFirstJet z s p =
        d4BMSeedH1Coefficient z s p * d4BMPoincareSeed z s p ∧
      d4BMPoincareSeedHorizontalSecondJet z s p =
        d4BMSeedH2Coefficient z s p * d4BMPoincareSeed z s p ∧
      d4BMPoincareSeedVerticalFirstJet z s p =
        d4BMSeedV1Coefficient z s p * d4BMPoincareSeed z s p ∧
      d4BMPoincareSeedVerticalSecondJet z s p =
        d4BMSeedV2Coefficient z s p * d4BMPoincareSeed z s p ∧
      d4BMPoincareSeedMixedSecondJet z s p =
        d4BMSeedMixedCoefficient z s p * d4BMPoincareSeed z s p := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · unfold d4BMPoincareSeedMixedSecondJet d4BMSeedMixedCoefficient
      d4BMSeedV1Coefficient d4BMSeedH1Coefficient
    ring

/-- Horizontal differentiation of the horizontal second seed jet gives the genuine `xxx` jet. -/
theorem hasDerivAt_d4BMPoincareSeedHorizontalSecondJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    HasDerivAt
      (fun x : ℝ => d4BMPoincareSeedHorizontalSecondJet
        (d4BMHorizontalCoordinate z x) s p)
      (d4BMPoincareSeedHorizontalThirdJet z s p) z.x := by
  let c : ℝ := p.pair.1
  let d : ℝ := p.pair.2
  let Q : ℝ → ℝ := fun x => (c * z.y) ^ 2 + (c * x + d) ^ 2
  let u : ℝ → ℝ := fun x => c * x + d
  let B : ℝ → ℂ := fun x =>
    -2 * s * (c : ℂ) ^ 2 / (Q x : ℂ) +
      4 * s * (s + 1) * (c : ℂ) ^ 2 * (u x : ℂ) ^ 2 / (Q x : ℂ) ^ 2
  let f : ℝ → ℂ := fun x => d4BMPoincareSeed (d4BMHorizontalCoordinate z x) s p
  have hQpos : 0 < Q z.x := by
    change 0 < d4BMPoincareQuadratic z p.pair
    exact d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hQne : (Q z.x : ℂ) ≠ 0 := by exact_mod_cast hQpos.ne'
  have huR : HasDerivAt u c z.x := by
    simpa [u] using ((hasDerivAt_id z.x).const_mul c).add_const d
  have hu : HasDerivAt (fun x : ℝ => (u x : ℂ)) (c : ℂ) z.x := huR.ofReal_comp
  have hQderivR : HasDerivAt Q (2 * c * u z.x) z.x := by
    dsimp only [Q]
    exact (((hasDerivAt_const z.x (c * z.y)).pow 2).add
      (huR.pow 2)).congr_deriv (by ring)
  have hQderiv : HasDerivAt (fun x : ℝ => (Q x : ℂ))
      ((2 * c * u z.x : ℝ) : ℂ) z.x := hQderivR.ofReal_comp
  have hterm1 :=
    (hasDerivAt_const z.x (-2 * s * (c : ℂ) ^ 2)).div hQderiv hQne
  have hterm2 :=
    ((((hu.pow 2).const_mul (4 * s * (s + 1) * (c : ℂ) ^ 2))).div
      (hQderiv.pow 2) (pow_ne_zero 2 hQne))
  have hBraw := hterm1.add hterm2
  let BX : ℂ :=
    4 * s * (c : ℂ) ^ 3 * (u z.x : ℂ) / (Q z.x : ℂ) ^ 2 +
      8 * s * (s + 1) * (c : ℂ) ^ 3 * (u z.x : ℂ) /
        (Q z.x : ℂ) ^ 2 -
      16 * s * (s + 1) * (c : ℂ) ^ 3 * (u z.x : ℂ) ^ 3 /
        (Q z.x : ℂ) ^ 3
  have hBlocal : HasDerivAt B BX z.x := by
    dsimp only [B, BX]
    apply hBraw.congr_deriv
    simp only [Pi.pow_apply]
    norm_num
    field_simp [hQne]
    ring
  have hBX : BX = d4BMSeedH2HorizontalDerivativeCoefficient z s p := by
    unfold d4BMSeedH2HorizontalDerivativeCoefficient
      d4BMPoincareHorizontalLinear d4BMPoincareQuadratic
    dsimp only [BX, c, d, Q, u]
    push_cast
    rfl
  have hB : HasDerivAt B (d4BMSeedH2HorizontalDerivativeCoefficient z s p) z.x := by
    rw [← hBX]
    exact hBlocal
  have hf := hasDerivAt_d4BMPoincareSeed_horizontal z s p
  have hprod := hB.mul hf
  have hfun :
      (fun x : ℝ => d4BMPoincareSeedHorizontalSecondJet
        (d4BMHorizontalCoordinate z x) s p) = fun x => B x * f x := by
    funext x
    unfold d4BMPoincareSeedHorizontalSecondJet d4BMPoincareHorizontalLinear
      d4BMPoincareQuadratic d4BMHorizontalCoordinate
    dsimp only [B, f, Q, u, c, d]
    push_cast
    rfl
  rw [hfun]
  apply hprod.congr_deriv
  unfold d4BMPoincareSeedHorizontalThirdJet
  rw [d4BM_seedJet_coefficient_eq z s p |>.1,
    d4BM_seedJet_coefficient_eq z s p |>.2.1]
  change d4BMSeedH2HorizontalDerivativeCoefficient z s p *
      d4BMPoincareSeed z s p +
      B z.x * (d4BMSeedH1Coefficient z s p * d4BMPoincareSeed z s p) = _
  have hBvalue : B z.x = d4BMSeedH2Coefficient z s p := by
    unfold d4BMSeedH2Coefficient d4BMPoincareHorizontalLinear
      d4BMPoincareQuadratic
    dsimp only [B, Q, u, c, d]
    rfl
  rw [hBvalue]
  ring

/-- Horizontal differentiation of the mixed seed jet gives the genuine `xxy` jet. -/
theorem hasDerivAt_d4BMPoincareSeedMixedSecondJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    HasDerivAt
      (fun x : ℝ => d4BMPoincareSeedMixedSecondJet
        (d4BMHorizontalCoordinate z x) s p)
      (d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet z s p) z.x := by
  let c : ℝ := p.pair.1
  let d : ℝ := p.pair.2
  let Q : ℝ → ℝ := fun x => (c * z.y) ^ 2 + (c * x + d) ^ 2
  let u : ℝ → ℝ := fun x => c * x + d
  let T : ℝ → ℂ := fun x =>
    4 * s * (c : ℂ) ^ 3 * (z.y : ℂ) * (u x : ℂ) / (Q x : ℂ) ^ 2
  let V : ℝ → ℂ := fun x =>
    s / (z.y : ℂ) - 2 * s * (c : ℂ) ^ 2 * (z.y : ℂ) / (Q x : ℂ)
  let H : ℝ → ℂ := fun x =>
    -2 * s * (c : ℂ) * (u x : ℂ) / (Q x : ℂ)
  let M : ℝ → ℂ := fun x => T x + V x * H x
  let f : ℝ → ℂ := fun x => d4BMPoincareSeed (d4BMHorizontalCoordinate z x) s p
  have hQpos : 0 < Q z.x := by
    change 0 < d4BMPoincareQuadratic z p.pair
    exact d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hQne : (Q z.x : ℂ) ≠ 0 := by exact_mod_cast hQpos.ne'
  have huR : HasDerivAt u c z.x := by
    simpa [u] using ((hasDerivAt_id z.x).const_mul c).add_const d
  have hu : HasDerivAt (fun x : ℝ => (u x : ℂ)) (c : ℂ) z.x := huR.ofReal_comp
  have hQderivR : HasDerivAt Q (2 * c * u z.x) z.x := by
    dsimp only [Q]
    exact (((hasDerivAt_const z.x (c * z.y)).pow 2).add
      (huR.pow 2)).congr_deriv (by ring)
  have hQderiv : HasDerivAt (fun x : ℝ => (Q x : ℂ))
      ((2 * c * u z.x : ℝ) : ℂ) z.x := hQderivR.ofReal_comp
  let TX : ℂ :=
    4 * s * (c : ℂ) ^ 4 * (z.y : ℂ) / (Q z.x : ℂ) ^ 2 -
      16 * s * (c : ℂ) ^ 4 * (z.y : ℂ) * (u z.x : ℂ) ^ 2 /
        (Q z.x : ℂ) ^ 3
  have hTraw :=
    ((hu.const_mul (4 * s * (c : ℂ) ^ 3 * (z.y : ℂ))).div
      (hQderiv.pow 2) (pow_ne_zero 2 hQne))
  have hT : HasDerivAt T TX z.x := by
    dsimp only [T, TX]
    apply hTraw.congr_deriv
    simp only [Pi.pow_apply]
    norm_num
    field_simp [hQne]
    ring
  let VX : ℂ :=
    4 * s * (c : ℂ) ^ 3 * (z.y : ℂ) * (u z.x : ℂ) /
      (Q z.x : ℂ) ^ 2
  have hVraw :=
    (hasDerivAt_const z.x (s / (z.y : ℂ))).sub
      ((hasDerivAt_const z.x (2 * s * (c : ℂ) ^ 2 * (z.y : ℂ))).div
        hQderiv hQne)
  have hV : HasDerivAt V VX z.x := by
    dsimp only [V, VX]
    apply hVraw.congr_deriv
    push_cast
    field_simp [hQne]
    ring
  let HX : ℂ :=
    -2 * s * (c : ℂ) ^ 2 / (Q z.x : ℂ) +
      4 * s * (c : ℂ) ^ 2 * (u z.x : ℂ) ^ 2 / (Q z.x : ℂ) ^ 2
  have hHraw :=
    (hu.const_mul (-2 * s * (c : ℂ))).div hQderiv hQne
  have hH : HasDerivAt H HX z.x := by
    dsimp only [H, HX]
    apply hHraw.congr_deriv
    push_cast
    field_simp [hQne]
    ring
  let H2C : ℂ :=
    -2 * s * (c : ℂ) ^ 2 / (Q z.x : ℂ) +
      4 * s * (s + 1) * (c : ℂ) ^ 2 * (u z.x : ℂ) ^ 2 /
        (Q z.x : ℂ) ^ 2
  let H2Y : ℂ :=
    4 * s * (c : ℂ) ^ 4 * (z.y : ℂ) / (Q z.x : ℂ) ^ 2 -
      16 * s * (s + 1) * (c : ℂ) ^ 4 * (u z.x : ℂ) ^ 2 *
        (z.y : ℂ) / (Q z.x : ℂ) ^ 3
  let MX : ℂ := TX + VX * H z.x + V z.x * HX
  have hM : HasDerivAt M MX z.x := by
    change HasDerivAt (T + V * H) MX z.x
    simpa only [MX, add_assoc] using hT.add (hV.mul hH)
  have hf := hasDerivAt_d4BMPoincareSeed_horizontal z s p
  have hprod := hM.mul hf
  have hfun :
      (fun x : ℝ => d4BMPoincareSeedMixedSecondJet
        (d4BMHorizontalCoordinate z x) s p) = fun x => M x * f x := by
    funext x
    change d4BMPoincareSeedMixedSecondJet (d4BMHorizontalCoordinate z x) s p =
      M x * d4BMPoincareSeed (d4BMHorizontalCoordinate z x) s p
    rw [d4BM_seedJet_coefficient_eq (d4BMHorizontalCoordinate z x) s p |>.2.2.2.2]
    apply congrArg (fun a : ℂ => a *
      d4BMPoincareSeed (d4BMHorizontalCoordinate z x) s p)
    unfold d4BMSeedMixedCoefficient d4BMSeedV1Coefficient
      d4BMSeedH1Coefficient d4BMPoincareHorizontalLinear
      d4BMPoincareQuadratic d4BMHorizontalCoordinate
    dsimp only [M, T, V, H, Q, u, c, d]
    push_cast
    ring
  rw [hfun]
  apply hprod.congr_deriv
  unfold d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet
  rw [d4BM_seedJet_coefficient_eq z s p |>.1,
    d4BM_seedJet_coefficient_eq z s p |>.2.1]
  change MX * d4BMPoincareSeed z s p +
      M z.x * (d4BMSeedH1Coefficient z s p * d4BMPoincareSeed z s p) =
    d4BMSeedH2VerticalDerivativeCoefficient z s p * d4BMPoincareSeed z s p +
      d4BMSeedV1Coefficient z s p *
        (d4BMSeedH2Coefficient z s p * d4BMPoincareSeed z s p)
  have hHvalue : H z.x = d4BMSeedH1Coefficient z s p := by
    unfold d4BMSeedH1Coefficient d4BMPoincareHorizontalLinear
      d4BMPoincareQuadratic
    dsimp only [H, Q, u, c, d]
    push_cast
    rfl
  have hVvalue : V z.x = d4BMSeedV1Coefficient z s p := by
    unfold d4BMSeedV1Coefficient d4BMPoincareQuadratic
    dsimp only [V, Q, c, d]
    push_cast
    rfl
  have hH2value : H2C = d4BMSeedH2Coefficient z s p := by
    unfold d4BMSeedH2Coefficient d4BMPoincareHorizontalLinear
      d4BMPoincareQuadratic
    dsimp only [H2C, Q, u, c, d]
    push_cast
    rfl
  have hH2Yvalue : H2Y = d4BMSeedH2VerticalDerivativeCoefficient z s p := by
    unfold d4BMSeedH2VerticalDerivativeCoefficient
      d4BMPoincareHorizontalLinear d4BMPoincareQuadratic
    dsimp only [H2Y, Q, u, c, d]
    push_cast
    rfl
  rw [← hHvalue, ← hVvalue, ← hH2value, ← hH2Yvalue]
  have hQalg : (Q z.x : ℂ) =
      (c : ℂ) ^ 2 * (z.y : ℂ) ^ 2 + (u z.x : ℂ) ^ 2 := by
    dsimp only [Q, u]
    push_cast
    ring
  dsimp only [MX, TX, VX, M, T, V, H, HX, H2C, H2Y]
  field_simp [hQne]
  rw [hQalg]
  ring

/-- Vertical slice of the horizontal first seed jet. -/
def d4BMPoincareSeedHorizontalFirstJetVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) (y : ℝ) : ℂ :=
  (-2 * s * (p.pair.1 : ℂ) *
      (((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ) : ℝ) : ℂ) /
      ((((p.pair.1 : ℝ) * y) ^ 2 +
        ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ 2 : ℝ) : ℂ)) *
    d4BMPoincareSeedVerticalSlice z s p y

/-- Vertical slice of the horizontal second seed jet. -/
def d4BMPoincareSeedHorizontalSecondJetVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) (y : ℝ) : ℂ :=
  (-2 * s * (p.pair.1 : ℂ) ^ 2 /
        ((((p.pair.1 : ℝ) * y) ^ 2 +
          ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ 2 : ℝ) : ℂ) +
      4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 2 *
        (((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ) : ℝ) : ℂ) ^ 2 /
        ((((p.pair.1 : ℝ) * y) ^ 2 +
          ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ 2 : ℝ) : ℂ) ^ 2) *
    d4BMPoincareSeedVerticalSlice z s p y

/-- Vertical slice of the mixed second seed jet. -/
def d4BMPoincareSeedMixedSecondJetVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) (y : ℝ) : ℂ :=
  (4 * s * (p.pair.1 : ℂ) ^ 3 * (y : ℂ) *
        (((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ) : ℝ) : ℂ) /
        ((((p.pair.1 : ℝ) * y) ^ 2 +
          ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ 2 : ℝ) : ℂ) ^ 2 +
      (s / (y : ℂ) -
        2 * s * (p.pair.1 : ℂ) ^ 2 * (y : ℂ) /
          ((((p.pair.1 : ℝ) * y) ^ 2 +
            ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ 2 : ℝ) : ℂ)) *
        (-2 * s * (p.pair.1 : ℂ) *
          (((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ) : ℝ) : ℂ) /
          ((((p.pair.1 : ℝ) * y) ^ 2 +
            ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ 2 : ℝ) : ℂ))) *
    d4BMPoincareSeedVerticalSlice z s p y

@[simp] theorem d4BM_poincareSeedHorizontalFirstJetVerticalSlice_at_height
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeedHorizontalFirstJetVerticalSlice z s p z.y =
      d4BMPoincareSeedHorizontalFirstJet z s p := by
  rfl

@[simp] theorem d4BM_poincareSeedHorizontalSecondJetVerticalSlice_at_height
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeedHorizontalSecondJetVerticalSlice z s p z.y =
      d4BMPoincareSeedHorizontalSecondJet z s p := by
  rfl

@[simp] theorem d4BM_poincareSeedMixedSecondJetVerticalSlice_at_height
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeedMixedSecondJetVerticalSlice z s p z.y =
      d4BMPoincareSeedMixedSecondJet z s p := by
  rfl

/-- Vertical differentiation of the horizontal first seed jet gives the same actual mixed jet. -/
theorem hasDerivAt_d4BMPoincareSeedHorizontalFirstJetVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    HasDerivAt (d4BMPoincareSeedHorizontalFirstJetVerticalSlice z s p)
      (d4BMPoincareSeedMixedSecondJet z s p) z.y := by
  let c : ℝ := p.pair.1
  let u : ℝ := c * z.x + p.pair.2
  let Q : ℝ → ℝ := fun y => (c * y) ^ 2 + u ^ 2
  let B : ℝ → ℂ := fun y => -2 * s * (c : ℂ) * (u : ℂ) / (Q y : ℂ)
  let f : ℝ → ℂ := d4BMPoincareSeedVerticalSlice z s p
  have hQpos : 0 < Q z.y := by
    change 0 < d4BMPoincareQuadratic z p.pair
    exact d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hQne : (Q z.y : ℂ) ≠ 0 := by exact_mod_cast hQpos.ne'
  have hidR : HasDerivAt (fun y : ℝ => y) 1 z.y := hasDerivAt_id z.y
  have hQderivR : HasDerivAt Q (2 * c ^ 2 * z.y) z.y := by
    dsimp only [Q]
    exact ((((hidR.const_mul c).pow 2).add
      (hasDerivAt_const z.y (u ^ 2)))).congr_deriv (by ring)
  have hQderiv : HasDerivAt (fun y : ℝ => (Q y : ℂ))
      ((2 * c ^ 2 * z.y : ℝ) : ℂ) z.y := hQderivR.ofReal_comp
  let BY : ℂ :=
    4 * s * (c : ℂ) ^ 3 * (u : ℂ) * (z.y : ℂ) / (Q z.y : ℂ) ^ 2
  have hBraw :=
    (hasDerivAt_const z.y (-2 * s * (c : ℂ) * (u : ℂ))).div hQderiv hQne
  have hB : HasDerivAt B BY z.y := by
    dsimp only [B, BY]
    apply hBraw.congr_deriv
    push_cast
    field_simp [hQne]
    ring
  have hf := hasDerivAt_d4BMPoincareSeed_vertical z s p
  have hprod := hB.mul hf
  have hfun : d4BMPoincareSeedHorizontalFirstJetVerticalSlice z s p =
      fun y => B y * f y := by
    funext y
    rfl
  rw [hfun]
  apply hprod.congr_deriv
  rw [d4BM_poincareSeedVerticalSlice_at_height,
    d4BM_seedJet_coefficient_eq z s p |>.2.2.1,
    d4BM_seedJet_coefficient_eq z s p |>.2.2.2.2]
  change BY * d4BMPoincareSeed z s p +
      B z.y * (d4BMSeedV1Coefficient z s p * d4BMPoincareSeed z s p) =
    d4BMSeedMixedCoefficient z s p * d4BMPoincareSeed z s p
  have hBvalue : B z.y = d4BMSeedH1Coefficient z s p := by
    unfold d4BMSeedH1Coefficient d4BMPoincareHorizontalLinear
      d4BMPoincareQuadratic
    dsimp only [B, Q, c, u]
    push_cast
    rfl
  have hBYvalue : BY =
      4 * s * (p.pair.1 : ℂ) ^ 3 * (z.y : ℂ) *
        (d4BMPoincareHorizontalLinear z p : ℂ) /
          (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2 := by
    unfold d4BMPoincareHorizontalLinear d4BMPoincareQuadratic
    dsimp only [BY, Q, c, u]
    push_cast
    ring
  rw [hBvalue, hBYvalue]
  unfold d4BMSeedMixedCoefficient
  ring

/-- Vertical differentiation of the horizontal second seed jet gives the genuine `xxy` jet. -/
theorem hasDerivAt_d4BMPoincareSeedHorizontalSecondJetVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    HasDerivAt (d4BMPoincareSeedHorizontalSecondJetVerticalSlice z s p)
      (d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet z s p) z.y := by
  let c : ℝ := p.pair.1
  let u : ℝ := c * z.x + p.pair.2
  let Q : ℝ → ℝ := fun y => (c * y) ^ 2 + u ^ 2
  let B : ℝ → ℂ := fun y =>
    -2 * s * (c : ℂ) ^ 2 / (Q y : ℂ) +
      4 * s * (s + 1) * (c : ℂ) ^ 2 * (u : ℂ) ^ 2 / (Q y : ℂ) ^ 2
  let f : ℝ → ℂ := d4BMPoincareSeedVerticalSlice z s p
  have hQpos : 0 < Q z.y := by
    change 0 < d4BMPoincareQuadratic z p.pair
    exact d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hQne : (Q z.y : ℂ) ≠ 0 := by exact_mod_cast hQpos.ne'
  have hidR : HasDerivAt (fun y : ℝ => y) 1 z.y := hasDerivAt_id z.y
  have hQderivR : HasDerivAt Q (2 * c ^ 2 * z.y) z.y := by
    dsimp only [Q]
    exact ((((hidR.const_mul c).pow 2).add
      (hasDerivAt_const z.y (u ^ 2)))).congr_deriv (by ring)
  have hQderiv : HasDerivAt (fun y : ℝ => (Q y : ℂ))
      ((2 * c ^ 2 * z.y : ℝ) : ℂ) z.y := hQderivR.ofReal_comp
  let BY : ℂ :=
    4 * s * (c : ℂ) ^ 4 * (z.y : ℂ) / (Q z.y : ℂ) ^ 2 -
      16 * s * (s + 1) * (c : ℂ) ^ 4 * (u : ℂ) ^ 2 *
        (z.y : ℂ) / (Q z.y : ℂ) ^ 3
  have hterm1 :=
    (hasDerivAt_const z.y (-2 * s * (c : ℂ) ^ 2)).div hQderiv hQne
  have hterm2 :=
    (hasDerivAt_const z.y (4 * s * (s + 1) * (c : ℂ) ^ 2 * (u : ℂ) ^ 2)).div
      (hQderiv.pow 2) (pow_ne_zero 2 hQne)
  have hBraw := hterm1.add hterm2
  have hB : HasDerivAt B BY z.y := by
    dsimp only [B, BY]
    apply hBraw.congr_deriv
    simp only [Pi.pow_apply]
    norm_num
    field_simp [hQne]
    ring
  have hf := hasDerivAt_d4BMPoincareSeed_vertical z s p
  have hprod := hB.mul hf
  have hfun : d4BMPoincareSeedHorizontalSecondJetVerticalSlice z s p =
      fun y => B y * f y := by
    funext y
    rfl
  rw [hfun]
  apply hprod.congr_deriv
  unfold d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet
  rw [d4BM_seedJet_coefficient_eq z s p |>.2.1,
    d4BM_seedJet_coefficient_eq z s p |>.2.2.1]
  change BY * d4BMPoincareSeed z s p +
      B z.y * (d4BMSeedV1Coefficient z s p * d4BMPoincareSeed z s p) =
    d4BMSeedH2VerticalDerivativeCoefficient z s p * d4BMPoincareSeed z s p +
      d4BMSeedV1Coefficient z s p *
        (d4BMSeedH2Coefficient z s p * d4BMPoincareSeed z s p)
  have hBvalue : B z.y = d4BMSeedH2Coefficient z s p := by
    unfold d4BMSeedH2Coefficient d4BMPoincareHorizontalLinear
      d4BMPoincareQuadratic
    dsimp only [B, Q, c, u]
    push_cast
    rfl
  have hBYvalue : BY = d4BMSeedH2VerticalDerivativeCoefficient z s p := by
    unfold d4BMSeedH2VerticalDerivativeCoefficient d4BMPoincareHorizontalLinear
      d4BMPoincareQuadratic
    dsimp only [BY, Q, c, u]
    push_cast
    rfl
  rw [hBvalue, hBYvalue]
  ring

/-- Horizontal differentiation of the vertical second seed jet is forced by the differentiated
seed eigen equation and gives the genuine `xyy` jet. -/
theorem hasDerivAt_d4BMPoincareSeedVerticalSecondJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    HasDerivAt
      (fun x : ℝ => d4BMPoincareSeedVerticalSecondJet
        (d4BMHorizontalCoordinate z x) s p)
      (d4BMPoincareSeedHorizontalVerticalVerticalThirdJet z s p) z.x := by
  let F : ℝ → ℂ := fun x =>
    d4BMPoincareSeed (d4BMHorizontalCoordinate z x) s p
  let H2 : ℝ → ℂ := fun x =>
    d4BMPoincareSeedHorizontalSecondJet (d4BMHorizontalCoordinate z x) s p
  let V2 : ℝ → ℂ := fun x =>
    d4BMPoincareSeedVerticalSecondJet (d4BMHorizontalCoordinate z x) s p
  let C : ℂ := s * (s - 1) / (z.y : ℂ) ^ 2
  have hy : (z.y : ℂ) ≠ 0 := by exact_mod_cast z.y_pos.ne'
  have hfun : V2 = fun x => C * F x - H2 x := by
    funext x
    have heig := d4BM_poincareSeed_formalHyperbolicLaplacian_eq_eigenvalue
      (d4BMHorizontalCoordinate z x) s p
    have hsum : H2 x + V2 x = C * F x := by
      dsimp only [H2, V2, C, F, d4BMHorizontalCoordinate] at heig ⊢
      field_simp [hy]
      simpa only [mul_comm] using heig
    linear_combination hsum
  have hF := hasDerivAt_d4BMPoincareSeed_horizontal z s p
  have hH2 := hasDerivAt_d4BMPoincareSeedHorizontalSecondJet_horizontal z s p
  have hderiv := (hF.const_mul C).sub hH2
  change HasDerivAt V2
    (d4BMPoincareSeedHorizontalVerticalVerticalThirdJet z s p) z.x
  rw [hfun]
  have heq :
      ((fun y => C * F y) - H2) =ᶠ[𝓝 z.x]
        (fun x => C * F x - H2 x) :=
    Filter.Eventually.of_forall fun x => rfl
  have hderiv' := heq.hasDerivAt_iff.mp hderiv
  simpa only [C, F, H2,
    d4BMPoincareSeedHorizontalVerticalVerticalThirdJet] using hderiv'

/-- Vertical differentiation of the mixed seed jet gives the same genuine `xyy` jet. -/
theorem hasDerivAt_d4BMPoincareSeedMixedSecondJetVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    HasDerivAt (d4BMPoincareSeedMixedSecondJetVerticalSlice z s p)
      (d4BMPoincareSeedHorizontalVerticalVerticalThirdJet z s p) z.y := by
  let c : ℝ := p.pair.1
  let u : ℝ := c * z.x + p.pair.2
  let Q : ℝ → ℝ := fun y => (c * y) ^ 2 + u ^ 2
  let T : ℝ → ℂ := fun y =>
    4 * s * (c : ℂ) ^ 3 * (u : ℂ) * (y : ℂ) / (Q y : ℂ) ^ 2
  let V : ℝ → ℂ := fun y =>
    s / (y : ℂ) - 2 * s * (c : ℂ) ^ 2 * (y : ℂ) / (Q y : ℂ)
  let H : ℝ → ℂ := fun y =>
    -2 * s * (c : ℂ) * (u : ℂ) / (Q y : ℂ)
  let M : ℝ → ℂ := fun y => T y + V y * H y
  let f : ℝ → ℂ := d4BMPoincareSeedVerticalSlice z s p
  have hQpos : 0 < Q z.y := by
    change 0 < d4BMPoincareQuadratic z p.pair
    exact d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hQne : (Q z.y : ℂ) ≠ 0 := by exact_mod_cast hQpos.ne'
  have hy : (z.y : ℂ) ≠ 0 := by exact_mod_cast z.y_pos.ne'
  have hidR : HasDerivAt (fun y : ℝ => y) 1 z.y := hasDerivAt_id z.y
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 z.y := hidR.ofReal_comp
  have hQderivR : HasDerivAt Q (2 * c ^ 2 * z.y) z.y := by
    dsimp only [Q]
    exact ((((hidR.const_mul c).pow 2).add
      (hasDerivAt_const z.y (u ^ 2)))).congr_deriv (by ring)
  have hQderiv : HasDerivAt (fun y : ℝ => (Q y : ℂ))
      ((2 * c ^ 2 * z.y : ℝ) : ℂ) z.y := hQderivR.ofReal_comp
  let TY : ℂ :=
    4 * s * (c : ℂ) ^ 3 * (u : ℂ) / (Q z.y : ℂ) ^ 2 -
      16 * s * (c : ℂ) ^ 5 * (z.y : ℂ) ^ 2 * (u : ℂ) /
        (Q z.y : ℂ) ^ 3
  have hTraw :=
    ((hid.const_mul (4 * s * (c : ℂ) ^ 3 * (u : ℂ))).div
      (hQderiv.pow 2) (pow_ne_zero 2 hQne))
  have hT : HasDerivAt T TY z.y := by
    dsimp only [T, TY]
    apply hTraw.congr_deriv
    simp only [Pi.pow_apply]
    norm_num
    field_simp [hQne]
    ring
  let VY : ℂ :=
    -s / (z.y : ℂ) ^ 2 -
      2 * s * (c : ℂ) ^ 2 / (Q z.y : ℂ) +
      4 * s * (c : ℂ) ^ 4 * (z.y : ℂ) ^ 2 / (Q z.y : ℂ) ^ 2
  have hVraw :=
    ((hasDerivAt_const z.y s).div hid hy).sub
      ((hid.const_mul (2 * s * (c : ℂ) ^ 2)).div hQderiv hQne)
  have hV : HasDerivAt V VY z.y := by
    dsimp only [V, VY]
    apply hVraw.congr_deriv
    push_cast
    field_simp [hQne, hy]
    ring
  let HY : ℂ :=
    4 * s * (c : ℂ) ^ 3 * (u : ℂ) * (z.y : ℂ) / (Q z.y : ℂ) ^ 2
  have hHraw :=
    (hasDerivAt_const z.y (-2 * s * (c : ℂ) * (u : ℂ))).div hQderiv hQne
  have hH : HasDerivAt H HY z.y := by
    dsimp only [H, HY]
    apply hHraw.congr_deriv
    push_cast
    field_simp [hQne]
    ring
  let MY : ℂ := TY + VY * H z.y + V z.y * HY
  have hM : HasDerivAt M MY z.y := by
    change HasDerivAt (T + V * H) MY z.y
    simpa only [MY, add_assoc] using hT.add (hV.mul hH)
  have hf := hasDerivAt_d4BMPoincareSeed_vertical z s p
  have hprod := hM.mul hf
  have hfun : d4BMPoincareSeedMixedSecondJetVerticalSlice z s p =
      fun y => M y * f y := by
    funext y
    change d4BMPoincareSeedMixedSecondJetVerticalSlice z s p y =
      M y * d4BMPoincareSeedVerticalSlice z s p y
    unfold d4BMPoincareSeedMixedSecondJetVerticalSlice
    apply congrArg (fun a : ℂ => a * d4BMPoincareSeedVerticalSlice z s p y)
    dsimp only [M, T, V, H, Q, u, c]
    push_cast
    ring
  rw [hfun]
  apply hprod.congr_deriv
  unfold d4BMPoincareSeedHorizontalVerticalVerticalThirdJet
    d4BMPoincareSeedHorizontalThirdJet
  rw [d4BM_poincareSeedVerticalSlice_at_height,
    d4BM_seedJet_coefficient_eq z s p |>.1,
    d4BM_seedJet_coefficient_eq z s p |>.2.1]
  change MY * d4BMPoincareSeed z s p +
      M z.y * (d4BMSeedV1Coefficient z s p * d4BMPoincareSeed z s p) =
    s * (s - 1) / (z.y : ℂ) ^ 2 *
        (d4BMSeedH1Coefficient z s p * d4BMPoincareSeed z s p) -
      (d4BMSeedH2HorizontalDerivativeCoefficient z s p *
          d4BMPoincareSeed z s p +
        d4BMSeedH1Coefficient z s p *
          (d4BMSeedH2Coefficient z s p * d4BMPoincareSeed z s p))
  let H2C : ℂ :=
    -2 * s * (c : ℂ) ^ 2 / (Q z.y : ℂ) +
      4 * s * (s + 1) * (c : ℂ) ^ 2 * (u : ℂ) ^ 2 /
        (Q z.y : ℂ) ^ 2
  let H2X : ℂ :=
    4 * s * (c : ℂ) ^ 3 * (u : ℂ) / (Q z.y : ℂ) ^ 2 +
      8 * s * (s + 1) * (c : ℂ) ^ 3 * (u : ℂ) /
        (Q z.y : ℂ) ^ 2 -
      16 * s * (s + 1) * (c : ℂ) ^ 3 * (u : ℂ) ^ 3 /
        (Q z.y : ℂ) ^ 3
  have hHvalue : H z.y = d4BMSeedH1Coefficient z s p := by
    unfold d4BMSeedH1Coefficient d4BMPoincareHorizontalLinear
      d4BMPoincareQuadratic
    dsimp only [H, Q, c, u]
    push_cast
    rfl
  have hVvalue : V z.y = d4BMSeedV1Coefficient z s p := by
    unfold d4BMSeedV1Coefficient d4BMPoincareQuadratic
    dsimp only [V, Q, c, u]
    push_cast
    rfl
  have hMvalue : M z.y = d4BMSeedMixedCoefficient z s p := by
    unfold d4BMSeedMixedCoefficient
    dsimp only [M]
    rw [hHvalue, hVvalue]
    unfold d4BMPoincareHorizontalLinear d4BMPoincareQuadratic
    dsimp only [T, Q, c, u]
    push_cast
    ring
  have hH2value : H2C = d4BMSeedH2Coefficient z s p := by
    unfold d4BMSeedH2Coefficient d4BMPoincareHorizontalLinear
      d4BMPoincareQuadratic
    dsimp only [H2C, Q, c, u]
    push_cast
    rfl
  have hH2Xvalue : H2X = d4BMSeedH2HorizontalDerivativeCoefficient z s p := by
    unfold d4BMSeedH2HorizontalDerivativeCoefficient
      d4BMPoincareHorizontalLinear d4BMPoincareQuadratic
    dsimp only [H2X, Q, c, u]
    push_cast
    rfl
  rw [← hVvalue, ← hHvalue, ← hH2value, ← hH2Xvalue]
  have hQalg : (Q z.y : ℂ) =
      (c : ℂ) ^ 2 * (z.y : ℂ) ^ 2 + (u : ℂ) ^ 2 := by
    dsimp only [Q]
    push_cast
    ring
  dsimp only [MY, TY, VY, M, T, V, H, HY, H2C, H2X]
  field_simp [hQne, hy]
  rw [hQalg]
  ring

private lemma d4BM_abs_c_sq_div_quadratic_le
    (z : D4BMUpperHalfPlaneCoordinate)
    (p : D4BMPrimitiveIntegerPair) :
    |(p.pair.1 : ℝ)| ^ 2 / d4BMPoincareQuadratic z p.pair ≤
      1 / z.y ^ 2 := by
  have hQ := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hy2 : 0 < z.y ^ 2 := sq_pos_of_pos z.y_pos
  apply (div_le_div_iff₀ hQ hy2).2
  rw [sq_abs]
  unfold d4BMPoincareQuadratic
  nlinarith [sq_nonneg ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ))]

private lemma d4BM_abs_c_mul_abs_u_div_quadratic_le
    (z : D4BMUpperHalfPlaneCoordinate)
    (p : D4BMPrimitiveIntegerPair) :
    |(p.pair.1 : ℝ)| * |d4BMPoincareHorizontalLinear z p| /
        d4BMPoincareQuadratic z p.pair ≤ 1 / z.y := by
  let c : ℝ := p.pair.1
  let u : ℝ := d4BMPoincareHorizontalLinear z p
  let Q : ℝ := d4BMPoincareQuadratic z p.pair
  have hQ : 0 < Q := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hamgm : 2 * z.y * |c| * |u| ≤ Q := by
    calc
      2 * z.y * |c| * |u| ≤ (z.y * |c|) ^ 2 + |u| ^ 2 := by
        nlinarith [sq_nonneg (z.y * |c| - |u|)]
      _ = z.y ^ 2 * c ^ 2 + u ^ 2 := by
        rw [mul_pow, sq_abs c, sq_abs u]
      _ = Q := by
        dsimp only [Q, c, u, d4BMPoincareQuadratic,
          d4BMPoincareHorizontalLinear]
        ring
  change |c| * |u| / Q ≤ 1 / z.y
  apply (div_le_div_iff₀ hQ z.y_pos).2
  nlinarith [abs_nonneg c, abs_nonneg u]

private lemma d4BM_abs_u_sq_div_quadratic_le_one
    (z : D4BMUpperHalfPlaneCoordinate)
    (p : D4BMPrimitiveIntegerPair) :
    |d4BMPoincareHorizontalLinear z p| ^ 2 /
        d4BMPoincareQuadratic z p.pair ≤ 1 := by
  have hQ := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  apply (div_le_one hQ).2
  rw [sq_abs]
  unfold d4BMPoincareQuadratic d4BMPoincareHorizontalLinear
  nlinarith [sq_nonneg ((p.pair.1 : ℝ) * z.y)]

private lemma d4BM_abs_c_cubed_abs_u_div_quadratic_sq_le
    (z : D4BMUpperHalfPlaneCoordinate)
    (p : D4BMPrimitiveIntegerPair) :
    |(p.pair.1 : ℝ)| ^ 3 * |d4BMPoincareHorizontalLinear z p| /
        d4BMPoincareQuadratic z p.pair ^ 2 ≤ 1 / z.y ^ 3 := by
  have h1 := d4BM_abs_c_sq_div_quadratic_le z p
  have h2 := d4BM_abs_c_mul_abs_u_div_quadratic_le z p
  have hQ := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  calc
    |(p.pair.1 : ℝ)| ^ 3 * |d4BMPoincareHorizontalLinear z p| /
          d4BMPoincareQuadratic z p.pair ^ 2 =
        (|(p.pair.1 : ℝ)| ^ 2 / d4BMPoincareQuadratic z p.pair) *
          (|(p.pair.1 : ℝ)| * |d4BMPoincareHorizontalLinear z p| /
            d4BMPoincareQuadratic z p.pair) := by
              field_simp [hQ.ne']
    _ ≤ (1 / z.y ^ 2) * (1 / z.y) := by
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 1 / z.y ^ 3 := by field_simp [z.y_pos.ne']

private lemma d4BM_abs_c_cubed_abs_u_cubed_div_quadratic_cubed_le
    (z : D4BMUpperHalfPlaneCoordinate)
    (p : D4BMPrimitiveIntegerPair) :
    |(p.pair.1 : ℝ)| ^ 3 * |d4BMPoincareHorizontalLinear z p| ^ 3 /
        d4BMPoincareQuadratic z p.pair ^ 3 ≤ 1 / z.y ^ 3 := by
  have h := d4BM_abs_c_mul_abs_u_div_quadratic_le z p
  have hQ := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hnonneg : 0 ≤ |(p.pair.1 : ℝ)| *
      |d4BMPoincareHorizontalLinear z p| /
        d4BMPoincareQuadratic z p.pair := by positivity
  have hynonneg : 0 ≤ 1 / z.y := div_nonneg zero_le_one z.y_pos.le
  calc
    |(p.pair.1 : ℝ)| ^ 3 * |d4BMPoincareHorizontalLinear z p| ^ 3 /
          d4BMPoincareQuadratic z p.pair ^ 3 =
        (|(p.pair.1 : ℝ)| * |d4BMPoincareHorizontalLinear z p| /
          d4BMPoincareQuadratic z p.pair) ^ 3 := by
            field_simp [hQ.ne']
    _ ≤ (1 / z.y) ^ 3 := by exact pow_le_pow_left₀ hnonneg h 3
    _ = 1 / z.y ^ 3 := by field_simp [z.y_pos.ne']

private lemma d4BM_abs_c_fourth_mul_y_div_quadratic_sq_le
    (z : D4BMUpperHalfPlaneCoordinate)
    (p : D4BMPrimitiveIntegerPair) :
    |(p.pair.1 : ℝ)| ^ 4 * z.y /
        d4BMPoincareQuadratic z p.pair ^ 2 ≤ 1 / z.y ^ 3 := by
  have h := d4BM_abs_c_sq_div_quadratic_le z p
  have hQ := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hnonneg : 0 ≤ |(p.pair.1 : ℝ)| ^ 2 /
      d4BMPoincareQuadratic z p.pair := by positivity
  calc
    |(p.pair.1 : ℝ)| ^ 4 * z.y /
          d4BMPoincareQuadratic z p.pair ^ 2 =
        (|(p.pair.1 : ℝ)| ^ 2 / d4BMPoincareQuadratic z p.pair) ^ 2 * z.y := by
            field_simp [hQ.ne']
    _ ≤ (1 / z.y ^ 2) ^ 2 * z.y := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnonneg h 2) z.y_pos.le
    _ = 1 / z.y ^ 3 := by field_simp [z.y_pos.ne']

private lemma d4BM_abs_c_fourth_abs_u_sq_mul_y_div_quadratic_cubed_le
    (z : D4BMUpperHalfPlaneCoordinate)
    (p : D4BMPrimitiveIntegerPair) :
    |(p.pair.1 : ℝ)| ^ 4 * |d4BMPoincareHorizontalLinear z p| ^ 2 * z.y /
        d4BMPoincareQuadratic z p.pair ^ 3 ≤ 1 / z.y ^ 3 := by
  have hc := d4BM_abs_c_sq_div_quadratic_le z p
  have hu := d4BM_abs_u_sq_div_quadratic_le_one z p
  have hQ := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hc0 : 0 ≤ |(p.pair.1 : ℝ)| ^ 2 /
      d4BMPoincareQuadratic z p.pair := by positivity
  have hu0 : 0 ≤ |d4BMPoincareHorizontalLinear z p| ^ 2 /
      d4BMPoincareQuadratic z p.pair := by positivity
  calc
    |(p.pair.1 : ℝ)| ^ 4 * |d4BMPoincareHorizontalLinear z p| ^ 2 * z.y /
          d4BMPoincareQuadratic z p.pair ^ 3 =
        (|(p.pair.1 : ℝ)| ^ 2 / d4BMPoincareQuadratic z p.pair) ^ 2 *
          (|d4BMPoincareHorizontalLinear z p| ^ 2 /
            d4BMPoincareQuadratic z p.pair) * z.y := by
              field_simp [hQ.ne']
    _ ≤ (1 / z.y ^ 2) ^ 2 * 1 * z.y := by
      gcongr
      exact z.y_pos.le
    _ = 1 / z.y ^ 3 := by field_simp [z.y_pos.ne']

private lemma norm_d4BMSeedH1Coefficient_le
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    ‖d4BMSeedH1Coefficient z s p‖ ≤ 2 * ‖s‖ / z.y := by
  have hQ := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  unfold d4BMSeedH1Coefficient
  rw [norm_div, norm_mul, norm_mul, norm_mul]
  simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ]
  norm_num
  calc
    2 * ‖s‖ * |(p.pair.1 : ℝ)| * |d4BMPoincareHorizontalLinear z p| /
          d4BMPoincareQuadratic z p.pair =
        2 * ‖s‖ * (|(p.pair.1 : ℝ)| * |d4BMPoincareHorizontalLinear z p| /
          d4BMPoincareQuadratic z p.pair) := by ring
    _ ≤ 2 * ‖s‖ * (1 / z.y) :=
      mul_le_mul_of_nonneg_left
        (d4BM_abs_c_mul_abs_u_div_quadratic_le z p) (by positivity)
    _ = 2 * ‖s‖ / z.y := by ring

private lemma norm_d4BMSeedV1Coefficient_le
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    ‖d4BMSeedV1Coefficient z s p‖ ≤ 3 * ‖s‖ / z.y := by
  have hQ := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hc := d4BM_abs_c_sq_div_quadratic_le z p
  unfold d4BMSeedV1Coefficient
  calc
    ‖s / (z.y : ℂ) - 2 * s * (p.pair.1 : ℂ) ^ 2 * (z.y : ℂ) /
          (d4BMPoincareQuadratic z p.pair : ℂ)‖ ≤
        ‖s / (z.y : ℂ)‖ +
          ‖2 * s * (p.pair.1 : ℂ) ^ 2 * (z.y : ℂ) /
            (d4BMPoincareQuadratic z p.pair : ℂ)‖ := norm_sub_le _ _
    _ = ‖s‖ / z.y +
        2 * ‖s‖ * |(p.pair.1 : ℝ)| ^ 2 * z.y /
          d4BMPoincareQuadratic z p.pair := by
      rw [norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_pow]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos z.y_pos,
        abs_of_pos hQ]
      norm_num
    _ ≤ ‖s‖ / z.y + 2 * ‖s‖ * (1 / z.y ^ 2) * z.y := by
      apply add_le_add le_rfl
      calc
        2 * ‖s‖ * |(p.pair.1 : ℝ)| ^ 2 * z.y /
            d4BMPoincareQuadratic z p.pair =
          (2 * ‖s‖) *
            (|(p.pair.1 : ℝ)| ^ 2 / d4BMPoincareQuadratic z p.pair) * z.y := by
              ring
        _ ≤ (2 * ‖s‖) * (1 / z.y ^ 2) * z.y := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hc (by positivity)) z.y_pos.le
    _ = 3 * ‖s‖ / z.y := by field_simp [z.y_pos.ne']; ring

private lemma norm_d4BMSeedH2HorizontalDerivativeCoefficient_le
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    ‖d4BMSeedH2HorizontalDerivativeCoefficient z s p‖ ≤
      (4 * ‖s‖ + 24 * ‖s‖ * ‖s + 1‖) / z.y ^ 3 := by
  have hQ := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  let a : ℂ := 4 * s * (p.pair.1 : ℂ) ^ 3 *
      (d4BMPoincareHorizontalLinear z p : ℂ) /
        (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2
  let b : ℂ := 8 * s * (s + 1) * (p.pair.1 : ℂ) ^ 3 *
      (d4BMPoincareHorizontalLinear z p : ℂ) /
        (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2
  let c : ℂ := 16 * s * (s + 1) * (p.pair.1 : ℂ) ^ 3 *
      (d4BMPoincareHorizontalLinear z p : ℂ) ^ 3 /
        (d4BMPoincareQuadratic z p.pair : ℂ) ^ 3
  have ha : ‖a‖ ≤ 4 * ‖s‖ / z.y ^ 3 := by
    dsimp only [a]
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ]
    norm_num
    calc
      4 * ‖s‖ * |(p.pair.1 : ℝ)| ^ 3 *
          |d4BMPoincareHorizontalLinear z p| /
            d4BMPoincareQuadratic z p.pair ^ 2 =
          4 * ‖s‖ * (|(p.pair.1 : ℝ)| ^ 3 *
            |d4BMPoincareHorizontalLinear z p| /
              d4BMPoincareQuadratic z p.pair ^ 2) := by ring
      _ ≤ 4 * ‖s‖ * (1 / z.y ^ 3) :=
        mul_le_mul_of_nonneg_left
          (d4BM_abs_c_cubed_abs_u_div_quadratic_sq_le z p) (by positivity)
      _ = 4 * ‖s‖ / z.y ^ 3 := by ring
  have hb : ‖b‖ ≤ 8 * ‖s‖ * ‖s + 1‖ / z.y ^ 3 := by
    dsimp only [b]
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ]
    norm_num
    calc
      8 * ‖s‖ * ‖s + 1‖ * |(p.pair.1 : ℝ)| ^ 3 *
          |d4BMPoincareHorizontalLinear z p| /
            d4BMPoincareQuadratic z p.pair ^ 2 =
          (8 * ‖s‖ * ‖s + 1‖) * (|(p.pair.1 : ℝ)| ^ 3 *
            |d4BMPoincareHorizontalLinear z p| /
              d4BMPoincareQuadratic z p.pair ^ 2) := by ring
      _ ≤ (8 * ‖s‖ * ‖s + 1‖) * (1 / z.y ^ 3) :=
        mul_le_mul_of_nonneg_left
          (d4BM_abs_c_cubed_abs_u_div_quadratic_sq_le z p) (by positivity)
      _ = 8 * ‖s‖ * ‖s + 1‖ / z.y ^ 3 := by ring
  have hc : ‖c‖ ≤ 16 * ‖s‖ * ‖s + 1‖ / z.y ^ 3 := by
    dsimp only [c]
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow,
      norm_pow, norm_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ]
    norm_num
    calc
      16 * ‖s‖ * ‖s + 1‖ * |(p.pair.1 : ℝ)| ^ 3 *
          |d4BMPoincareHorizontalLinear z p| ^ 3 /
            d4BMPoincareQuadratic z p.pair ^ 3 =
          (16 * ‖s‖ * ‖s + 1‖) * (|(p.pair.1 : ℝ)| ^ 3 *
            |d4BMPoincareHorizontalLinear z p| ^ 3 /
              d4BMPoincareQuadratic z p.pair ^ 3) := by ring
      _ ≤ (16 * ‖s‖ * ‖s + 1‖) * (1 / z.y ^ 3) :=
        mul_le_mul_of_nonneg_left
          (d4BM_abs_c_cubed_abs_u_cubed_div_quadratic_cubed_le z p)
          (by positivity)
      _ = 16 * ‖s‖ * ‖s + 1‖ / z.y ^ 3 := by ring
  unfold d4BMSeedH2HorizontalDerivativeCoefficient
  change ‖a + b - c‖ ≤ _
  calc
    ‖a + b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
      exact le_trans (norm_sub_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 4 * ‖s‖ / z.y ^ 3 +
        8 * ‖s‖ * ‖s + 1‖ / z.y ^ 3 +
        16 * ‖s‖ * ‖s + 1‖ / z.y ^ 3 := add_le_add (add_le_add ha hb) hc
    _ = (4 * ‖s‖ + 24 * ‖s‖ * ‖s + 1‖) / z.y ^ 3 := by ring

private lemma norm_d4BMSeedH2VerticalDerivativeCoefficient_le
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    ‖d4BMSeedH2VerticalDerivativeCoefficient z s p‖ ≤
      (4 * ‖s‖ + 16 * ‖s‖ * ‖s + 1‖) / z.y ^ 3 := by
  have hQ := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  let a : ℂ := 4 * s * (p.pair.1 : ℂ) ^ 4 * (z.y : ℂ) /
      (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2
  let b : ℂ := 16 * s * (s + 1) * (p.pair.1 : ℂ) ^ 4 *
      (d4BMPoincareHorizontalLinear z p : ℂ) ^ 2 * (z.y : ℂ) /
        (d4BMPoincareQuadratic z p.pair : ℂ) ^ 3
  have ha : ‖a‖ ≤ 4 * ‖s‖ / z.y ^ 3 := by
    dsimp only [a]
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos z.y_pos,
      abs_of_pos hQ]
    norm_num
    calc
      4 * ‖s‖ * |(p.pair.1 : ℝ)| ^ 4 * z.y /
          d4BMPoincareQuadratic z p.pair ^ 2 =
        4 * ‖s‖ * (|(p.pair.1 : ℝ)| ^ 4 * z.y /
          d4BMPoincareQuadratic z p.pair ^ 2) := by ring
      _ ≤ 4 * ‖s‖ * (1 / z.y ^ 3) :=
        mul_le_mul_of_nonneg_left
          (d4BM_abs_c_fourth_mul_y_div_quadratic_sq_le z p) (by positivity)
      _ = 4 * ‖s‖ / z.y ^ 3 := by ring
  have hb : ‖b‖ ≤ 16 * ‖s‖ * ‖s + 1‖ / z.y ^ 3 := by
    dsimp only [b]
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
      norm_pow, norm_pow, norm_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos z.y_pos,
      abs_of_pos hQ]
    norm_num
    calc
      16 * ‖s‖ * ‖s + 1‖ * |(p.pair.1 : ℝ)| ^ 4 *
          d4BMPoincareHorizontalLinear z p ^ 2 * z.y /
            d4BMPoincareQuadratic z p.pair ^ 3 =
        (16 * ‖s‖ * ‖s + 1‖) * (|(p.pair.1 : ℝ)| ^ 4 *
          |d4BMPoincareHorizontalLinear z p| ^ 2 * z.y /
            d4BMPoincareQuadratic z p.pair ^ 3) := by
              rw [sq_abs]
              ring
      _ ≤ (16 * ‖s‖ * ‖s + 1‖) * (1 / z.y ^ 3) :=
        mul_le_mul_of_nonneg_left
          (d4BM_abs_c_fourth_abs_u_sq_mul_y_div_quadratic_cubed_le z p)
          (by positivity)
      _ = 16 * ‖s‖ * ‖s + 1‖ / z.y ^ 3 := by ring
  unfold d4BMSeedH2VerticalDerivativeCoefficient
  change ‖a - b‖ ≤ _
  calc
    ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le _ _
    _ ≤ 4 * ‖s‖ / z.y ^ 3 + 16 * ‖s‖ * ‖s + 1‖ / z.y ^ 3 := add_le_add ha hb
    _ = (4 * ‖s‖ + 16 * ‖s‖ * ‖s + 1‖) / z.y ^ 3 := by ring

/-- Fixed spectral constant controlling the actual `xxx` Poincare seed jet. -/
def d4BMHorizontalThirdJetNormConstant (s : ℂ) : ℝ :=
  4 * ‖s‖ + 24 * ‖s‖ * ‖s + 1‖ +
    2 * ‖s‖ * (2 * ‖s‖ + 4 * ‖s‖ * ‖s + 1‖)

/-- Fixed spectral constant controlling the actual `xxy` Poincare seed jet. -/
def d4BMHorizontalHorizontalVerticalThirdJetNormConstant (s : ℂ) : ℝ :=
  4 * ‖s‖ + 16 * ‖s‖ * ‖s + 1‖ +
    3 * ‖s‖ * (2 * ‖s‖ + 4 * ‖s‖ * ‖s + 1‖)

/-- Fixed spectral constant controlling the actual `xyy` Poincare seed jet. -/
def d4BMHorizontalVerticalVerticalThirdJetNormConstant (s : ℂ) : ℝ :=
  2 * ‖s‖ ^ 2 * ‖s - 1‖ + d4BMHorizontalThirdJetNormConstant s

lemma d4BMHorizontalThirdJetNormConstant_nonneg (s : ℂ) :
    0 ≤ d4BMHorizontalThirdJetNormConstant s := by
  unfold d4BMHorizontalThirdJetNormConstant
  positivity

lemma d4BMHorizontalHorizontalVerticalThirdJetNormConstant_nonneg (s : ℂ) :
    0 ≤ d4BMHorizontalHorizontalVerticalThirdJetNormConstant s := by
  unfold d4BMHorizontalHorizontalVerticalThirdJetNormConstant
  positivity

lemma d4BMHorizontalVerticalVerticalThirdJetNormConstant_nonneg (s : ℂ) :
    0 ≤ d4BMHorizontalVerticalVerticalThirdJetNormConstant s := by
  unfold d4BMHorizontalVerticalVerticalThirdJetNormConstant
  exact add_nonneg (by positivity) (d4BMHorizontalThirdJetNormConstant_nonneg s)

lemma norm_d4BMPoincareSeedHorizontalThirdJet_le
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    ‖d4BMPoincareSeedHorizontalThirdJet z s p‖ ≤
      (d4BMHorizontalThirdJetNormConstant s / z.y ^ 3) *
        ‖d4BMPoincareSeed z s p‖ := by
  have hA := norm_d4BMSeedH2HorizontalDerivativeCoefficient_le z s p
  have hB := norm_d4BMSeedH1Coefficient_le z s p
  have hH2 := norm_d4BMPoincareSeedHorizontalSecondJet_le z s p
  have hBupper : 0 ≤ 2 * ‖s‖ / z.y :=
    div_nonneg (mul_nonneg (by norm_num) (norm_nonneg s)) z.y_pos.le
  unfold d4BMPoincareSeedHorizontalThirdJet
  calc
    ‖d4BMSeedH2HorizontalDerivativeCoefficient z s p *
          d4BMPoincareSeed z s p +
        d4BMSeedH1Coefficient z s p *
          d4BMPoincareSeedHorizontalSecondJet z s p‖ ≤
      ‖d4BMSeedH2HorizontalDerivativeCoefficient z s p *
          d4BMPoincareSeed z s p‖ +
        ‖d4BMSeedH1Coefficient z s p *
          d4BMPoincareSeedHorizontalSecondJet z s p‖ := norm_add_le _ _
    _ = ‖d4BMSeedH2HorizontalDerivativeCoefficient z s p‖ *
          ‖d4BMPoincareSeed z s p‖ +
        ‖d4BMSeedH1Coefficient z s p‖ *
          ‖d4BMPoincareSeedHorizontalSecondJet z s p‖ := by
            rw [norm_mul, norm_mul]
    _ ≤ ((4 * ‖s‖ + 24 * ‖s‖ * ‖s + 1‖) / z.y ^ 3) *
          ‖d4BMPoincareSeed z s p‖ +
        (2 * ‖s‖ / z.y) *
          (((2 * ‖s‖ + 4 * ‖s‖ * ‖s + 1‖) / z.y ^ 2) *
            ‖d4BMPoincareSeed z s p‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      · exact mul_le_mul hB hH2 (norm_nonneg _) hBupper
    _ = (d4BMHorizontalThirdJetNormConstant s / z.y ^ 3) *
        ‖d4BMPoincareSeed z s p‖ := by
      unfold d4BMHorizontalThirdJetNormConstant
      field_simp [z.y_pos.ne']

lemma norm_d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet_le
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    ‖d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet z s p‖ ≤
      (d4BMHorizontalHorizontalVerticalThirdJetNormConstant s / z.y ^ 3) *
        ‖d4BMPoincareSeed z s p‖ := by
  have hA := norm_d4BMSeedH2VerticalDerivativeCoefficient_le z s p
  have hB := norm_d4BMSeedV1Coefficient_le z s p
  have hH2 := norm_d4BMPoincareSeedHorizontalSecondJet_le z s p
  have hBupper : 0 ≤ 3 * ‖s‖ / z.y :=
    div_nonneg (mul_nonneg (by norm_num) (norm_nonneg s)) z.y_pos.le
  unfold d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet
  calc
    ‖d4BMSeedH2VerticalDerivativeCoefficient z s p *
          d4BMPoincareSeed z s p +
        d4BMSeedV1Coefficient z s p *
          d4BMPoincareSeedHorizontalSecondJet z s p‖ ≤
      ‖d4BMSeedH2VerticalDerivativeCoefficient z s p *
          d4BMPoincareSeed z s p‖ +
        ‖d4BMSeedV1Coefficient z s p *
          d4BMPoincareSeedHorizontalSecondJet z s p‖ := norm_add_le _ _
    _ = ‖d4BMSeedH2VerticalDerivativeCoefficient z s p‖ *
          ‖d4BMPoincareSeed z s p‖ +
        ‖d4BMSeedV1Coefficient z s p‖ *
          ‖d4BMPoincareSeedHorizontalSecondJet z s p‖ := by
            rw [norm_mul, norm_mul]
    _ ≤ ((4 * ‖s‖ + 16 * ‖s‖ * ‖s + 1‖) / z.y ^ 3) *
          ‖d4BMPoincareSeed z s p‖ +
        (3 * ‖s‖ / z.y) *
          (((2 * ‖s‖ + 4 * ‖s‖ * ‖s + 1‖) / z.y ^ 2) *
            ‖d4BMPoincareSeed z s p‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      · exact mul_le_mul hB hH2 (norm_nonneg _) hBupper
    _ = (d4BMHorizontalHorizontalVerticalThirdJetNormConstant s / z.y ^ 3) *
        ‖d4BMPoincareSeed z s p‖ := by
      unfold d4BMHorizontalHorizontalVerticalThirdJetNormConstant
      field_simp [z.y_pos.ne']

lemma norm_d4BMPoincareSeedHorizontalVerticalVerticalThirdJet_le
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    ‖d4BMPoincareSeedHorizontalVerticalVerticalThirdJet z s p‖ ≤
      (d4BMHorizontalVerticalVerticalThirdJetNormConstant s / z.y ^ 3) *
        ‖d4BMPoincareSeed z s p‖ := by
  let C : ℂ := s * (s - 1) / (z.y : ℂ) ^ 2
  have hC : ‖C‖ = ‖s‖ * ‖s - 1‖ / z.y ^ 2 := by
    dsimp only [C]
    rw [norm_div, norm_mul, norm_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos z.y_pos]
  have hfirst := norm_d4BMPoincareSeedHorizontalFirstJet_le z s p
  have hthird := norm_d4BMPoincareSeedHorizontalThirdJet_le z s p
  have hCnonneg : 0 ≤ ‖s‖ * ‖s - 1‖ / z.y ^ 2 := by positivity
  unfold d4BMPoincareSeedHorizontalVerticalVerticalThirdJet
  change ‖C * d4BMPoincareSeedHorizontalFirstJet z s p -
      d4BMPoincareSeedHorizontalThirdJet z s p‖ ≤ _
  calc
    ‖C * d4BMPoincareSeedHorizontalFirstJet z s p -
        d4BMPoincareSeedHorizontalThirdJet z s p‖ ≤
      ‖C * d4BMPoincareSeedHorizontalFirstJet z s p‖ +
        ‖d4BMPoincareSeedHorizontalThirdJet z s p‖ := norm_sub_le _ _
    _ = ‖C‖ * ‖d4BMPoincareSeedHorizontalFirstJet z s p‖ +
        ‖d4BMPoincareSeedHorizontalThirdJet z s p‖ := by rw [norm_mul]
    _ ≤ (‖s‖ * ‖s - 1‖ / z.y ^ 2) *
          ((2 * ‖s‖ / z.y) * ‖d4BMPoincareSeed z s p‖) +
        (d4BMHorizontalThirdJetNormConstant s / z.y ^ 3) *
          ‖d4BMPoincareSeed z s p‖ := by
      rw [hC]
      exact add_le_add (mul_le_mul_of_nonneg_left hfirst hCnonneg) hthird
    _ = (d4BMHorizontalVerticalVerticalThirdJetNormConstant s / z.y ^ 3) *
        ‖d4BMPoincareSeed z s p‖ := by
      unfold d4BMHorizontalVerticalVerticalThirdJetNormConstant
      field_simp [z.y_pos.ne']

/-- Horizontal-disc majorant for the `xxx` seed series. -/
def d4BMHorizontalThirdJetHorizontalLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (p : D4BMPrimitiveIntegerPair) : ℝ :=
  ((d4BMHorizontalThirdJetNormConstant P.s / z.y ^ 3) * 3 ^ P.s.re) *
    ‖d4BMPoincareSeed z P.s p‖

/-- Horizontal-disc majorant for the `xxy` seed series. -/
def d4BMHorizontalHorizontalVerticalThirdJetHorizontalLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (p : D4BMPrimitiveIntegerPair) : ℝ :=
  ((d4BMHorizontalHorizontalVerticalThirdJetNormConstant P.s / z.y ^ 3) *
      3 ^ P.s.re) * ‖d4BMPoincareSeed z P.s p‖

lemma summable_d4BMHorizontalThirdJetHorizontalLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable (d4BMHorizontalThirdJetHorizontalLocalMajorant z P) := by
  exact (summable_d4BMPoincareSeed z P).norm.mul_left _

lemma summable_d4BMHorizontalHorizontalVerticalThirdJetHorizontalLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable
      (d4BMHorizontalHorizontalVerticalThirdJetHorizontalLocalMajorant z P) := by
  exact (summable_d4BMPoincareSeed z P).norm.mul_left _

/-- The actual horizontal second-jet series differentiates termwise to the genuine `xxx` sum. -/
theorem hasDerivAt_tsum_d4BMPoincareSeedHorizontalSecondJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalSecondJet
          (d4BMHorizontalCoordinate z x) P.s p)
      (∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalThirdJet z P.s p) z.x := by
  let t : Set ℝ := Ioo (z.x - z.y) (z.x + z.y)
  let g : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p x =>
    d4BMPoincareSeedHorizontalSecondJet (d4BMHorizontalCoordinate z x) P.s p
  let g' : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p x =>
    d4BMPoincareSeedHorizontalThirdJet (d4BMHorizontalCoordinate z x) P.s p
  let M := d4BMHorizontalThirdJetHorizontalLocalMajorant z P
  have hM : Summable M := summable_d4BMHorizontalThirdJetHorizontalLocalMajorant z P
  have hK : 0 ≤ d4BMHorizontalThirdJetNormConstant P.s / z.y ^ 3 :=
    div_nonneg (d4BMHorizontalThirdJetNormConstant_nonneg P.s)
      (pow_nonneg z.y_pos.le 3)
  have hderiv : ∀ p, ∀ x ∈ t, HasDerivAt (g p) (g' p x) x := by
    intro p x hx
    simpa [g, g', d4BMHorizontalCoordinate] using
      hasDerivAt_d4BMPoincareSeedHorizontalSecondJet_horizontal
        (d4BMHorizontalCoordinate z x) P.s p
  have hbound : ∀ p, ∀ x ∈ t, ‖g' p x‖ ≤ M p := by
    intro p x hx
    calc
      ‖g' p x‖ ≤ (d4BMHorizontalThirdJetNormConstant P.s / z.y ^ 3) *
          ‖d4BMPoincareSeed (d4BMHorizontalCoordinate z x) P.s p‖ := by
        dsimp only [g']
        simpa [d4BMHorizontalCoordinate] using
          norm_d4BMPoincareSeedHorizontalThirdJet_le
            (d4BMHorizontalCoordinate z x) P.s p
      _ ≤ (d4BMHorizontalThirdJetNormConstant P.s / z.y ^ 3) *
          (3 ^ P.s.re * ‖d4BMPoincareSeed z P.s p‖) :=
        mul_le_mul_of_nonneg_left (norm_d4BMPoincareSeed_horizontal_le z P p hx) hK
      _ = M p := by
        simp [M, d4BMHorizontalThirdJetHorizontalLocalMajorant]
        ring
  have hzmem : z.x ∈ t := by
    dsimp only [t]
    constructor <;> linarith [z.y_pos]
  have hbase : Summable fun p => g p z.x := by
    simpa [g, d4BMHorizontalCoordinate] using
      summable_d4BMPoincareSeedHorizontalSecondJet z P
  have h := hasDerivAt_tsum_of_isPreconnected hM isOpen_Ioo isPreconnected_Ioo
    hderiv hbound hzmem hbase hzmem
  simpa [g, g', d4BMHorizontalCoordinate] using h

/-- The actual mixed second-jet series differentiates horizontally to the genuine `xxy` sum. -/
theorem hasDerivAt_tsum_d4BMPoincareSeedMixedSecondJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedMixedSecondJet
          (d4BMHorizontalCoordinate z x) P.s p)
      (∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet z P.s p) z.x := by
  let t : Set ℝ := Ioo (z.x - z.y) (z.x + z.y)
  let g : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p x =>
    d4BMPoincareSeedMixedSecondJet (d4BMHorizontalCoordinate z x) P.s p
  let g' : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p x =>
    d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet
      (d4BMHorizontalCoordinate z x) P.s p
  let M := d4BMHorizontalHorizontalVerticalThirdJetHorizontalLocalMajorant z P
  have hM : Summable M :=
    summable_d4BMHorizontalHorizontalVerticalThirdJetHorizontalLocalMajorant z P
  have hK : 0 ≤
      d4BMHorizontalHorizontalVerticalThirdJetNormConstant P.s / z.y ^ 3 :=
    div_nonneg
      (d4BMHorizontalHorizontalVerticalThirdJetNormConstant_nonneg P.s)
      (pow_nonneg z.y_pos.le 3)
  have hderiv : ∀ p, ∀ x ∈ t, HasDerivAt (g p) (g' p x) x := by
    intro p x hx
    simpa [g, g', d4BMHorizontalCoordinate] using
      hasDerivAt_d4BMPoincareSeedMixedSecondJet_horizontal
        (d4BMHorizontalCoordinate z x) P.s p
  have hbound : ∀ p, ∀ x ∈ t, ‖g' p x‖ ≤ M p := by
    intro p x hx
    calc
      ‖g' p x‖ ≤
          (d4BMHorizontalHorizontalVerticalThirdJetNormConstant P.s / z.y ^ 3) *
            ‖d4BMPoincareSeed (d4BMHorizontalCoordinate z x) P.s p‖ := by
        dsimp only [g']
        simpa [d4BMHorizontalCoordinate] using
          norm_d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet_le
            (d4BMHorizontalCoordinate z x) P.s p
      _ ≤ (d4BMHorizontalHorizontalVerticalThirdJetNormConstant P.s / z.y ^ 3) *
          (3 ^ P.s.re * ‖d4BMPoincareSeed z P.s p‖) :=
        mul_le_mul_of_nonneg_left (norm_d4BMPoincareSeed_horizontal_le z P p hx) hK
      _ = M p := by
        simp [M, d4BMHorizontalHorizontalVerticalThirdJetHorizontalLocalMajorant]
        ring
  have hzmem : z.x ∈ t := by
    dsimp only [t]
    constructor <;> linarith [z.y_pos]
  have hbase : Summable fun p => g p z.x := by
    simpa [g, d4BMHorizontalCoordinate] using summable_d4BMPoincareSeedMixedSecondJet z P
  have h := hasDerivAt_tsum_of_isPreconnected hM isOpen_Ioo isPreconnected_Ioo
    hderiv hbound hzmem hbase hzmem
  simpa [g, g', d4BMHorizontalCoordinate] using h

private lemma d4BM_inv_cube_vertical_local_le
    (z : D4BMUpperHalfPlaneCoordinate) {y : ℝ}
    (hy : y ∈ Ioo (z.y / 2) (2 * z.y)) :
    1 / y ^ 3 ≤ 8 / z.y ^ 3 := by
  have hy0 : 0 < y := by linarith [z.y_pos, hy.1]
  have hpow : z.y ^ 3 ≤ (2 * y) ^ 3 :=
    pow_le_pow_left₀ z.y_pos.le (by linarith [hy.1]) 3
  apply (div_le_div_iff₀ (pow_pos hy0 3) (pow_pos z.y_pos 3)).2
  norm_num
  calc
    z.y ^ 3 ≤ (2 * y) ^ 3 := hpow
    _ = 8 * y ^ 3 := by ring

/-- Vertical-strip majorant for the `xxy` seed series. -/
def d4BMHorizontalHorizontalVerticalThirdJetVerticalLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (p : D4BMPrimitiveIntegerPair) : ℝ :=
  ((8 * d4BMHorizontalHorizontalVerticalThirdJetNormConstant P.s / z.y ^ 3) *
      (2 ^ P.s.re * 4 ^ P.s.re)) * ‖d4BMPoincareSeed z P.s p‖

/-- Vertical-strip majorant for the `xyy` seed series. -/
def d4BMHorizontalVerticalVerticalThirdJetVerticalLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (p : D4BMPrimitiveIntegerPair) : ℝ :=
  ((8 * d4BMHorizontalVerticalVerticalThirdJetNormConstant P.s / z.y ^ 3) *
      (2 ^ P.s.re * 4 ^ P.s.re)) * ‖d4BMPoincareSeed z P.s p‖

lemma summable_d4BMHorizontalHorizontalVerticalThirdJetVerticalLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable
      (d4BMHorizontalHorizontalVerticalThirdJetVerticalLocalMajorant z P) := by
  exact (summable_d4BMPoincareSeed z P).norm.mul_left _

lemma summable_d4BMHorizontalVerticalVerticalThirdJetVerticalLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable (d4BMHorizontalVerticalVerticalThirdJetVerticalLocalMajorant z P) := by
  exact (summable_d4BMPoincareSeed z P).norm.mul_left _

/-- The horizontal second-jet vertical slice differentiates termwise to the genuine `xxy` sum. -/
theorem hasDerivAt_tsum_d4BMPoincareSeedHorizontalSecondJet_vertical
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun y : ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalSecondJetVerticalSlice z P.s p y)
      (∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet z P.s p) z.y := by
  let t : Set ℝ := Ioo (z.y / 2) (2 * z.y)
  let g : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p y =>
    d4BMPoincareSeedHorizontalSecondJetVerticalSlice z P.s p y
  let g' : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p y =>
    if hy0 : 0 < y then
      d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet ⟨z.x, y, hy0⟩ P.s p
    else 0
  let M := d4BMHorizontalHorizontalVerticalThirdJetVerticalLocalMajorant z P
  have hM : Summable M :=
    summable_d4BMHorizontalHorizontalVerticalThirdJetVerticalLocalMajorant z P
  have hderiv : ∀ p, ∀ y ∈ t, HasDerivAt (g p) (g' p y) y := by
    intro p y hy
    have hy0 : 0 < y := by linarith [z.y_pos, hy.1]
    let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy0⟩
    have h := hasDerivAt_d4BMPoincareSeedHorizontalSecondJetVerticalSlice zy P.s p
    have hfun : d4BMPoincareSeedHorizontalSecondJetVerticalSlice zy P.s p =
        d4BMPoincareSeedHorizontalSecondJetVerticalSlice z P.s p := by
      funext v
      rfl
    rw [hfun] at h
    simpa only [g, g', zy, dif_pos hy0] using h
  have hbound : ∀ p, ∀ y ∈ t, ‖g' p y‖ ≤ M p := by
    intro p y hy
    have hy0 : 0 < y := by linarith [z.y_pos, hy.1]
    let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy0⟩
    have hnorm :=
      norm_d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet_le zy P.s p
    have hinv := d4BM_inv_cube_vertical_local_le z hy
    have hK := d4BMHorizontalHorizontalVerticalThirdJetNormConstant_nonneg P.s
    have hcoef : d4BMHorizontalHorizontalVerticalThirdJetNormConstant P.s / y ^ 3 ≤
        8 * d4BMHorizontalHorizontalVerticalThirdJetNormConstant P.s / z.y ^ 3 := by
      calc
        d4BMHorizontalHorizontalVerticalThirdJetNormConstant P.s / y ^ 3 =
            d4BMHorizontalHorizontalVerticalThirdJetNormConstant P.s * (1 / y ^ 3) := by ring
        _ ≤ d4BMHorizontalHorizontalVerticalThirdJetNormConstant P.s *
            (8 / z.y ^ 3) := mul_le_mul_of_nonneg_left hinv hK
        _ = 8 * d4BMHorizontalHorizontalVerticalThirdJetNormConstant P.s /
            z.y ^ 3 := by ring
    calc
      ‖g' p y‖ ≤
          (d4BMHorizontalHorizontalVerticalThirdJetNormConstant P.s / y ^ 3) *
            ‖d4BMPoincareSeed zy P.s p‖ := by
              simpa only [g', zy, dif_pos hy0] using hnorm
      _ ≤ (8 * d4BMHorizontalHorizontalVerticalThirdJetNormConstant P.s / z.y ^ 3) *
          ‖d4BMPoincareSeedVerticalSlice z P.s p y‖ := by
        apply mul_le_mul hcoef le_rfl (norm_nonneg _)
        exact div_nonneg (mul_nonneg (by norm_num) hK) (pow_nonneg z.y_pos.le 3)
      _ ≤ (8 * d4BMHorizontalHorizontalVerticalThirdJetNormConstant P.s / z.y ^ 3) *
          ((2 ^ P.s.re * 4 ^ P.s.re) * ‖d4BMPoincareSeed z P.s p‖) :=
        mul_le_mul_of_nonneg_left (norm_d4BMPoincareSeed_vertical_le z P p hy)
          (div_nonneg (mul_nonneg (by norm_num) hK) (pow_nonneg z.y_pos.le 3))
      _ = M p := by
        simp [M, d4BMHorizontalHorizontalVerticalThirdJetVerticalLocalMajorant]
        ring
  have hymem : z.y ∈ t := by
    dsimp only [t]
    constructor <;> linarith [z.y_pos]
  have hbase : Summable fun p => g p z.y := by
    simpa only [g, d4BM_poincareSeedHorizontalSecondJetVerticalSlice_at_height] using
      summable_d4BMPoincareSeedHorizontalSecondJet z P
  have h := hasDerivAt_tsum_of_isPreconnected hM isOpen_Ioo isPreconnected_Ioo
    hderiv hbound hymem hbase hymem
  simpa only [g, g', dif_pos z.y_pos,
    d4BM_poincareSeedHorizontalSecondJetVerticalSlice_at_height] using h

/-- The mixed second-jet vertical slice differentiates termwise to the genuine `xyy` sum. -/
theorem hasDerivAt_tsum_d4BMPoincareSeedMixedSecondJet_vertical
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun y : ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedMixedSecondJetVerticalSlice z P.s p y)
      (∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalVerticalVerticalThirdJet z P.s p) z.y := by
  let t : Set ℝ := Ioo (z.y / 2) (2 * z.y)
  let g : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p y =>
    d4BMPoincareSeedMixedSecondJetVerticalSlice z P.s p y
  let g' : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p y =>
    if hy0 : 0 < y then
      d4BMPoincareSeedHorizontalVerticalVerticalThirdJet ⟨z.x, y, hy0⟩ P.s p
    else 0
  let M := d4BMHorizontalVerticalVerticalThirdJetVerticalLocalMajorant z P
  have hM : Summable M :=
    summable_d4BMHorizontalVerticalVerticalThirdJetVerticalLocalMajorant z P
  have hderiv : ∀ p, ∀ y ∈ t, HasDerivAt (g p) (g' p y) y := by
    intro p y hy
    have hy0 : 0 < y := by linarith [z.y_pos, hy.1]
    let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy0⟩
    have h := hasDerivAt_d4BMPoincareSeedMixedSecondJetVerticalSlice zy P.s p
    have hfun : d4BMPoincareSeedMixedSecondJetVerticalSlice zy P.s p =
        d4BMPoincareSeedMixedSecondJetVerticalSlice z P.s p := by
      funext v
      rfl
    rw [hfun] at h
    simpa only [g, g', zy, dif_pos hy0] using h
  have hbound : ∀ p, ∀ y ∈ t, ‖g' p y‖ ≤ M p := by
    intro p y hy
    have hy0 : 0 < y := by linarith [z.y_pos, hy.1]
    let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy0⟩
    have hnorm := norm_d4BMPoincareSeedHorizontalVerticalVerticalThirdJet_le zy P.s p
    have hinv := d4BM_inv_cube_vertical_local_le z hy
    have hK := d4BMHorizontalVerticalVerticalThirdJetNormConstant_nonneg P.s
    have hcoef : d4BMHorizontalVerticalVerticalThirdJetNormConstant P.s / y ^ 3 ≤
        8 * d4BMHorizontalVerticalVerticalThirdJetNormConstant P.s / z.y ^ 3 := by
      calc
        d4BMHorizontalVerticalVerticalThirdJetNormConstant P.s / y ^ 3 =
            d4BMHorizontalVerticalVerticalThirdJetNormConstant P.s * (1 / y ^ 3) := by ring
        _ ≤ d4BMHorizontalVerticalVerticalThirdJetNormConstant P.s *
            (8 / z.y ^ 3) := mul_le_mul_of_nonneg_left hinv hK
        _ = 8 * d4BMHorizontalVerticalVerticalThirdJetNormConstant P.s /
            z.y ^ 3 := by ring
    calc
      ‖g' p y‖ ≤ (d4BMHorizontalVerticalVerticalThirdJetNormConstant P.s / y ^ 3) *
          ‖d4BMPoincareSeed zy P.s p‖ := by
            simpa only [g', zy, dif_pos hy0] using hnorm
      _ ≤ (8 * d4BMHorizontalVerticalVerticalThirdJetNormConstant P.s / z.y ^ 3) *
          ‖d4BMPoincareSeedVerticalSlice z P.s p y‖ := by
        apply mul_le_mul hcoef le_rfl (norm_nonneg _)
        exact div_nonneg (mul_nonneg (by norm_num) hK) (pow_nonneg z.y_pos.le 3)
      _ ≤ (8 * d4BMHorizontalVerticalVerticalThirdJetNormConstant P.s / z.y ^ 3) *
          ((2 ^ P.s.re * 4 ^ P.s.re) * ‖d4BMPoincareSeed z P.s p‖) :=
        mul_le_mul_of_nonneg_left (norm_d4BMPoincareSeed_vertical_le z P p hy)
          (div_nonneg (mul_nonneg (by norm_num) hK) (pow_nonneg z.y_pos.le 3))
      _ = M p := by
        simp [M, d4BMHorizontalVerticalVerticalThirdJetVerticalLocalMajorant]
        ring
  have hymem : z.y ∈ t := by
    dsimp only [t]
    constructor <;> linarith [z.y_pos]
  have hbase : Summable fun p => g p z.y := by
    simpa only [g, d4BM_poincareSeedMixedSecondJetVerticalSlice_at_height] using
      summable_d4BMPoincareSeedMixedSecondJet z P
  have h := hasDerivAt_tsum_of_isPreconnected hM isOpen_Ioo isPreconnected_Ioo
    hderiv hbound hymem hbase hymem
  simpa only [g, g', dif_pos z.y_pos,
    d4BM_poincareSeedMixedSecondJetVerticalSlice_at_height] using h

/-- Raw actual `xxx` jet of the primitive-pair Poincare series. -/
def d4BMRawPoincareHorizontalThirdJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
    d4BMPoincareSeedHorizontalThirdJet z P.s p

/-- Raw actual `xxy` jet of the primitive-pair Poincare series. -/
def d4BMRawPoincareHorizontalHorizontalVerticalThirdJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
    d4BMPoincareSeedHorizontalHorizontalVerticalThirdJet z P.s p

/-- Raw actual `xyy` jet of the primitive-pair Poincare series. -/
def d4BMRawPoincareHorizontalVerticalVerticalThirdJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
    d4BMPoincareSeedHorizontalVerticalVerticalThirdJet z P.s p

/-- Raw vertical slice of the horizontal second jet. -/
def d4BMRawPoincareHorizontalSecondJetVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
    d4BMPoincareSeedHorizontalSecondJetVerticalSlice z P.s p y

/-- Raw vertical slice of the mixed second jet. -/
def d4BMRawPoincareMixedSecondJetVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
    d4BMPoincareSeedMixedSecondJetVerticalSlice z P.s p y

theorem hasDerivAt_d4BMRawPoincareHorizontalSecondJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => d4BMRawPoincareHorizontalSecondJet
        (d4BMHorizontalCoordinate z x) P)
      (d4BMRawPoincareHorizontalThirdJet z P) z.x := by
  have h :=
    (hasDerivAt_tsum_d4BMPoincareSeedHorizontalSecondJet_horizontal z P).const_mul
      (1 / 2 : ℂ)
  simpa [d4BMRawPoincareHorizontalSecondJet,
    d4BMRawPoincareHorizontalThirdJet, d4BMHorizontalCoordinate] using h

theorem hasDerivAt_d4BMRawPoincareMixedSecondJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => d4BMRawPoincareMixedSecondJet
        (d4BMHorizontalCoordinate z x) P)
      (d4BMRawPoincareHorizontalHorizontalVerticalThirdJet z P) z.x := by
  have h :=
    (hasDerivAt_tsum_d4BMPoincareSeedMixedSecondJet_horizontal z P).const_mul
      (1 / 2 : ℂ)
  simpa [d4BMRawPoincareMixedSecondJet,
    d4BMRawPoincareHorizontalHorizontalVerticalThirdJet,
    d4BMHorizontalCoordinate] using h

theorem hasDerivAt_d4BMRawPoincareHorizontalSecondJetVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt (d4BMRawPoincareHorizontalSecondJetVerticalSlice z P)
      (d4BMRawPoincareHorizontalHorizontalVerticalThirdJet z P) z.y := by
  have h :=
    (hasDerivAt_tsum_d4BMPoincareSeedHorizontalSecondJet_vertical z P).const_mul
      (1 / 2 : ℂ)
  change HasDerivAt
    (fun y => d4BMRawPoincareHorizontalSecondJetVerticalSlice z P y)
    (d4BMRawPoincareHorizontalHorizontalVerticalThirdJet z P) z.y
  simpa [d4BMRawPoincareHorizontalSecondJetVerticalSlice,
    d4BMRawPoincareHorizontalHorizontalVerticalThirdJet] using h

theorem hasDerivAt_d4BMRawPoincareMixedSecondJetVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt (d4BMRawPoincareMixedSecondJetVerticalSlice z P)
      (d4BMRawPoincareHorizontalVerticalVerticalThirdJet z P) z.y := by
  have h :=
    (hasDerivAt_tsum_d4BMPoincareSeedMixedSecondJet_vertical z P).const_mul
      (1 / 2 : ℂ)
  change HasDerivAt
    (fun y => d4BMRawPoincareMixedSecondJetVerticalSlice z P y)
    (d4BMRawPoincareHorizontalVerticalVerticalThirdJet z P) z.y
  simpa [d4BMRawPoincareMixedSecondJetVerticalSlice,
    d4BMRawPoincareHorizontalVerticalVerticalThirdJet] using h

/-- Completed actual `xxx` jet. -/
def d4BMCompletedPoincareHorizontalThirdJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  reflectedCompletedLambda (2 * P.s) * d4BMRawPoincareHorizontalThirdJet z P

/-- Completed actual `xxy` jet. -/
def d4BMCompletedPoincareHorizontalHorizontalVerticalThirdJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  reflectedCompletedLambda (2 * P.s) *
    d4BMRawPoincareHorizontalHorizontalVerticalThirdJet z P

/-- Completed actual `xyy` jet. -/
def d4BMCompletedPoincareHorizontalVerticalVerticalThirdJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  reflectedCompletedLambda (2 * P.s) *
    d4BMRawPoincareHorizontalVerticalVerticalThirdJet z P

/-- Completed vertical slice of the horizontal second jet. -/
def d4BMCompletedPoincareHorizontalSecondJetVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  reflectedCompletedLambda (2 * P.s) *
    d4BMRawPoincareHorizontalSecondJetVerticalSlice z P y

/-- Completed vertical slice of the mixed second jet. -/
def d4BMCompletedPoincareMixedSecondJetVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  reflectedCompletedLambda (2 * P.s) *
    d4BMRawPoincareMixedSecondJetVerticalSlice z P y

@[simp] theorem d4BM_completedPoincareHorizontalSecondJetVerticalSlice_at_height
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareHorizontalSecondJetVerticalSlice z P z.y =
      d4BMCompletedPoincareHorizontalSecondJet z P := by
  rfl

@[simp] theorem d4BM_completedPoincareMixedSecondJetVerticalSlice_at_height
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareMixedSecondJetVerticalSlice z P z.y =
      d4BMCompletedPoincareMixedSecondJet z P := by
  rfl

theorem hasDerivAt_d4BMCompletedPoincareHorizontalSecondJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => d4BMCompletedPoincareHorizontalSecondJet
        (d4BMHorizontalCoordinate z x) P)
      (d4BMCompletedPoincareHorizontalThirdJet z P) z.x := by
  have h := (hasDerivAt_d4BMRawPoincareHorizontalSecondJet_horizontal z P).const_mul
    (reflectedCompletedLambda (2 * P.s))
  simpa [d4BMCompletedPoincareHorizontalSecondJet,
    d4BMCompletedPoincareHorizontalThirdJet] using h

theorem hasDerivAt_d4BMCompletedPoincareMixedSecondJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => d4BMCompletedPoincareMixedSecondJet
        (d4BMHorizontalCoordinate z x) P)
      (d4BMCompletedPoincareHorizontalHorizontalVerticalThirdJet z P) z.x := by
  have h := (hasDerivAt_d4BMRawPoincareMixedSecondJet_horizontal z P).const_mul
    (reflectedCompletedLambda (2 * P.s))
  simpa [d4BMCompletedPoincareMixedSecondJet,
    d4BMCompletedPoincareHorizontalHorizontalVerticalThirdJet] using h

theorem hasDerivAt_d4BMCompletedPoincareHorizontalSecondJetVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt (d4BMCompletedPoincareHorizontalSecondJetVerticalSlice z P)
      (d4BMCompletedPoincareHorizontalHorizontalVerticalThirdJet z P) z.y := by
  have h :=
    (hasDerivAt_d4BMRawPoincareHorizontalSecondJetVerticalSlice z P).const_mul
      (reflectedCompletedLambda (2 * P.s))
  change HasDerivAt
    (fun y => d4BMCompletedPoincareHorizontalSecondJetVerticalSlice z P y)
    (d4BMCompletedPoincareHorizontalHorizontalVerticalThirdJet z P) z.y
  simpa [d4BMCompletedPoincareHorizontalSecondJetVerticalSlice,
    d4BMCompletedPoincareHorizontalHorizontalVerticalThirdJet] using h

theorem hasDerivAt_d4BMCompletedPoincareMixedSecondJetVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt (d4BMCompletedPoincareMixedSecondJetVerticalSlice z P)
      (d4BMCompletedPoincareHorizontalVerticalVerticalThirdJet z P) z.y := by
  have h :=
    (hasDerivAt_d4BMRawPoincareMixedSecondJetVerticalSlice z P).const_mul
      (reflectedCompletedLambda (2 * P.s))
  change HasDerivAt
    (fun y => d4BMCompletedPoincareMixedSecondJetVerticalSlice z P y)
    (d4BMCompletedPoincareHorizontalVerticalVerticalThirdJet z P) z.y
  simpa [d4BMCompletedPoincareMixedSecondJetVerticalSlice,
    d4BMCompletedPoincareHorizontalVerticalVerticalThirdJet] using h

theorem d4BM_completedPoincareVerticalSlice_eq_at
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    {y : ℝ} (hy : 0 < y) :
    d4BMCompletedPoincareVerticalSlice z P y =
      d4BMCompletedEisensteinPoincareSeries ⟨z.x, y, hy⟩ P := by
  rfl

theorem d4BM_completedPoincareHorizontalSecondJetVerticalSlice_eq_at
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    {y : ℝ} (hy : 0 < y) :
    d4BMCompletedPoincareHorizontalSecondJetVerticalSlice z P y =
      d4BMCompletedPoincareHorizontalSecondJet ⟨z.x, y, hy⟩ P := by
  rfl

theorem d4BM_completedPoincareVerticalSecondJetSlice_eq_eigenSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    {y : ℝ} (hy : 0 < y) :
    d4BMCompletedPoincareVerticalSecondJetSlice z P y =
      P.s * (P.s - 1) / (y : ℂ) ^ 2 *
          d4BMCompletedPoincareVerticalSlice z P y -
        d4BMCompletedPoincareHorizontalSecondJetVerticalSlice z P y := by
  let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy⟩
  rw [d4BMCompletedPoincareVerticalSecondJetSlice_eq_at z P hy,
    d4BM_completedPoincareVerticalSlice_eq_at z P hy,
    d4BM_completedPoincareHorizontalSecondJetVerticalSlice_eq_at z P hy]
  have heig :=
    d4BM_completedEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue zy P
  have hyne : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  dsimp only [zy] at heig ⊢
  field_simp [hyne]
  linear_combination heig

/-- Completed actual `yyy` jet, forced by vertical differentiation of the genuine eigen equation. -/
def d4BMCompletedPoincareVerticalThirdJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (-2 * P.s * (P.s - 1) / (z.y : ℂ) ^ 3) *
      d4BMCompletedEisensteinPoincareSeries z P +
    (P.s * (P.s - 1) / (z.y : ℂ) ^ 2) *
      d4BMCompletedPoincareVerticalFirstJet z P -
    d4BMCompletedPoincareHorizontalHorizontalVerticalThirdJet z P

/-- The actual vertical second jet has the genuine vertically differentiated eigen derivative. -/
theorem hasDerivAt_d4BMCompletedPoincareVerticalSecondJetSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt (d4BMCompletedPoincareVerticalSecondJetSlice z P)
      (d4BMCompletedPoincareVerticalThirdJet z P) z.y := by
  let C : ℝ → ℂ := fun y => P.s * (P.s - 1) / (y : ℂ) ^ 2
  have hy : (z.y : ℂ) ≠ 0 := by exact_mod_cast z.y_pos.ne'
  have hidR : HasDerivAt (fun y : ℝ => y) 1 z.y := hasDerivAt_id z.y
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 z.y := hidR.ofReal_comp
  have hCraw :=
    (hasDerivAt_const z.y (P.s * (P.s - 1))).div (hid.pow 2) (pow_ne_zero 2 hy)
  have hC : HasDerivAt C
      (-2 * P.s * (P.s - 1) / (z.y : ℂ) ^ 3) z.y := by
    dsimp only [C]
    apply hCraw.congr_deriv
    simp only [Pi.pow_apply]
    norm_num
    field_simp [hy]
  have hF := hasDerivAt_d4BMCompletedPoincareVerticalSlice z P
  have hH2 := hasDerivAt_d4BMCompletedPoincareHorizontalSecondJetVerticalSlice z P
  have hderiv := (hC.mul hF).sub hH2
  have heq : d4BMCompletedPoincareVerticalSecondJetSlice z P =ᶠ[𝓝 z.y]
      fun y => C y * d4BMCompletedPoincareVerticalSlice z P y -
        d4BMCompletedPoincareHorizontalSecondJetVerticalSlice z P y := by
    filter_upwards [Ioi_mem_nhds z.y_pos] with y hypos
    exact d4BM_completedPoincareVerticalSecondJetSlice_eq_eigenSlice z P hypos
  have hfinal := heq.hasDerivAt_iff.mpr hderiv
  simpa only [C, d4BMCompletedPoincareVerticalThirdJet,
    d4BMCompletedPoincareVerticalSlice_at_height,
    d4BM_completedPoincareHorizontalSecondJetVerticalSlice_at_height] using hfinal

/-- Horizontal-disc majorant for the `xyy` seed series. -/
def d4BMHorizontalVerticalVerticalThirdJetHorizontalLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (p : D4BMPrimitiveIntegerPair) : ℝ :=
  ((d4BMHorizontalVerticalVerticalThirdJetNormConstant P.s / z.y ^ 3) *
      3 ^ P.s.re) * ‖d4BMPoincareSeed z P.s p‖

lemma summable_d4BMHorizontalVerticalVerticalThirdJetHorizontalLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable (d4BMHorizontalVerticalVerticalThirdJetHorizontalLocalMajorant z P) := by
  exact (summable_d4BMPoincareSeed z P).norm.mul_left _

/-- The vertical second-jet series differentiates horizontally to the genuine `xyy` sum. -/
theorem hasDerivAt_tsum_d4BMPoincareSeedVerticalSecondJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedVerticalSecondJet (d4BMHorizontalCoordinate z x) P.s p)
      (∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalVerticalVerticalThirdJet z P.s p) z.x := by
  let t : Set ℝ := Ioo (z.x - z.y) (z.x + z.y)
  let g : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p x =>
    d4BMPoincareSeedVerticalSecondJet (d4BMHorizontalCoordinate z x) P.s p
  let g' : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p x =>
    d4BMPoincareSeedHorizontalVerticalVerticalThirdJet
      (d4BMHorizontalCoordinate z x) P.s p
  let M := d4BMHorizontalVerticalVerticalThirdJetHorizontalLocalMajorant z P
  have hM : Summable M :=
    summable_d4BMHorizontalVerticalVerticalThirdJetHorizontalLocalMajorant z P
  have hK : 0 ≤ d4BMHorizontalVerticalVerticalThirdJetNormConstant P.s / z.y ^ 3 :=
    div_nonneg (d4BMHorizontalVerticalVerticalThirdJetNormConstant_nonneg P.s)
      (pow_nonneg z.y_pos.le 3)
  have hderiv : ∀ p, ∀ x ∈ t, HasDerivAt (g p) (g' p x) x := by
    intro p x hx
    simpa [g, g', d4BMHorizontalCoordinate] using
      hasDerivAt_d4BMPoincareSeedVerticalSecondJet_horizontal
        (d4BMHorizontalCoordinate z x) P.s p
  have hbound : ∀ p, ∀ x ∈ t, ‖g' p x‖ ≤ M p := by
    intro p x hx
    calc
      ‖g' p x‖ ≤ (d4BMHorizontalVerticalVerticalThirdJetNormConstant P.s / z.y ^ 3) *
          ‖d4BMPoincareSeed (d4BMHorizontalCoordinate z x) P.s p‖ := by
        dsimp only [g']
        simpa [d4BMHorizontalCoordinate] using
          norm_d4BMPoincareSeedHorizontalVerticalVerticalThirdJet_le
            (d4BMHorizontalCoordinate z x) P.s p
      _ ≤ (d4BMHorizontalVerticalVerticalThirdJetNormConstant P.s / z.y ^ 3) *
          (3 ^ P.s.re * ‖d4BMPoincareSeed z P.s p‖) :=
        mul_le_mul_of_nonneg_left (norm_d4BMPoincareSeed_horizontal_le z P p hx) hK
      _ = M p := by
        simp [M, d4BMHorizontalVerticalVerticalThirdJetHorizontalLocalMajorant]
        ring
  have hzmem : z.x ∈ t := by
    dsimp only [t]
    constructor <;> linarith [z.y_pos]
  have hbase : Summable fun p => g p z.x := by
    simpa [g, d4BMHorizontalCoordinate] using summable_d4BMPoincareSeedVerticalSecondJet z P
  have h := hasDerivAt_tsum_of_isPreconnected hM isOpen_Ioo isPreconnected_Ioo
    hderiv hbound hzmem hbase hzmem
  simpa [g, g', d4BMHorizontalCoordinate] using h

theorem hasDerivAt_d4BMRawPoincareVerticalSecondJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => d4BMRawPoincareVerticalSecondJet
        (d4BMHorizontalCoordinate z x) P)
      (d4BMRawPoincareHorizontalVerticalVerticalThirdJet z P) z.x := by
  have h :=
    (hasDerivAt_tsum_d4BMPoincareSeedVerticalSecondJet_horizontal z P).const_mul
      (1 / 2 : ℂ)
  simpa [d4BMRawPoincareVerticalSecondJet,
    d4BMRawPoincareHorizontalVerticalVerticalThirdJet,
    d4BMHorizontalCoordinate] using h

theorem hasDerivAt_d4BMCompletedPoincareVerticalSecondJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => d4BMCompletedPoincareVerticalSecondJet
        (d4BMHorizontalCoordinate z x) P)
      (d4BMCompletedPoincareHorizontalVerticalVerticalThirdJet z P) z.x := by
  have h := (hasDerivAt_d4BMRawPoincareVerticalSecondJet_horizontal z P).const_mul
    (reflectedCompletedLambda (2 * P.s))
  simpa [d4BMCompletedPoincareVerticalSecondJet,
    d4BMCompletedPoincareHorizontalVerticalVerticalThirdJet] using h

/-- Horizontally differentiated completed eigen equation. -/
theorem d4BM_completedPoincare_thirdJet_horizontalEigenEquation
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    (z.y : ℂ) ^ 2 *
        (d4BMCompletedPoincareHorizontalThirdJet z P +
          d4BMCompletedPoincareHorizontalVerticalVerticalThirdJet z P) =
      P.s * (P.s - 1) * d4BMCompletedPoincareHorizontalFirstJet z P := by
  let C : ℂ := P.s * (P.s - 1) / (z.y : ℂ) ^ 2
  let F : ℝ → ℂ := fun x =>
    d4BMCompletedEisensteinPoincareSeries (d4BMHorizontalCoordinate z x) P
  let H2 : ℝ → ℂ := fun x =>
    d4BMCompletedPoincareHorizontalSecondJet (d4BMHorizontalCoordinate z x) P
  let V2 : ℝ → ℂ := fun x =>
    d4BMCompletedPoincareVerticalSecondJet (d4BMHorizontalCoordinate z x) P
  have hy : (z.y : ℂ) ≠ 0 := by exact_mod_cast z.y_pos.ne'
  have hfun : V2 = fun x => C * F x - H2 x := by
    funext x
    have heig :=
      d4BM_completedEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue
        (d4BMHorizontalCoordinate z x) P
    dsimp only [V2, H2, F, C, d4BMHorizontalCoordinate] at heig ⊢
    field_simp [hy]
    linear_combination heig
  have hV2 := hasDerivAt_d4BMCompletedPoincareVerticalSecondJet_horizontal z P
  have hF := hasDerivAt_d4BMCompletedEisensteinPoincareSeries_horizontal z P
  have hH2 := hasDerivAt_d4BMCompletedPoincareHorizontalSecondJet_horizontal z P
  have hRhs := (hF.const_mul C).sub hH2
  change HasDerivAt V2
      (d4BMCompletedPoincareHorizontalVerticalVerticalThirdJet z P) z.x at hV2
  have heq : ((fun x => C * F x) - H2) =ᶠ[𝓝 z.x]
      (fun x => C * F x - H2 x) := Filter.Eventually.of_forall fun x => rfl
  have hRhs' := heq.hasDerivAt_iff.mp hRhs
  rw [hfun] at hV2
  have hunique := hV2.unique hRhs'
  dsimp only [C] at hunique
  field_simp [hy] at hunique ⊢
  linear_combination hunique

/-- Vertical-strip majorant for the mixed derivative of the horizontal first jet. -/
def d4BMMixedSecondJetVerticalLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (p : D4BMPrimitiveIntegerPair) : ℝ :=
  ((4 * (4 * ‖P.s‖ + 6 * ‖P.s‖ ^ 2) / z.y ^ 2) *
      (2 ^ P.s.re * 4 ^ P.s.re)) * ‖d4BMPoincareSeed z P.s p‖

lemma summable_d4BMMixedSecondJetVerticalLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable (d4BMMixedSecondJetVerticalLocalMajorant z P) := by
  exact (summable_d4BMPoincareSeed z P).norm.mul_left _

/-- The horizontal first-jet vertical slice differentiates termwise to the mixed second jet. -/
theorem hasDerivAt_tsum_d4BMPoincareSeedHorizontalFirstJet_vertical
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun y : ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalFirstJetVerticalSlice z P.s p y)
      (∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedMixedSecondJet z P.s p) z.y := by
  let t : Set ℝ := Ioo (z.y / 2) (2 * z.y)
  let g : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p y =>
    d4BMPoincareSeedHorizontalFirstJetVerticalSlice z P.s p y
  let g' : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p y =>
    if hy0 : 0 < y then d4BMPoincareSeedMixedSecondJet ⟨z.x, y, hy0⟩ P.s p else 0
  let M := d4BMMixedSecondJetVerticalLocalMajorant z P
  have hM : Summable M := summable_d4BMMixedSecondJetVerticalLocalMajorant z P
  have hderiv : ∀ p, ∀ y ∈ t, HasDerivAt (g p) (g' p y) y := by
    intro p y hy
    have hy0 : 0 < y := by linarith [z.y_pos, hy.1]
    let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy0⟩
    have h := hasDerivAt_d4BMPoincareSeedHorizontalFirstJetVerticalSlice zy P.s p
    have hfun : d4BMPoincareSeedHorizontalFirstJetVerticalSlice zy P.s p =
        d4BMPoincareSeedHorizontalFirstJetVerticalSlice z P.s p := by
      funext v
      rfl
    rw [hfun] at h
    simpa only [g, g', zy, dif_pos hy0] using h
  have hbound : ∀ p, ∀ y ∈ t, ‖g' p y‖ ≤ M p := by
    intro p y hy
    have hy0 : 0 < y := by linarith [z.y_pos, hy.1]
    let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy0⟩
    have hnorm := norm_d4BMPoincareSeedMixedSecondJet_le zy P.s p
    have hinvSq : 1 / y ^ 2 ≤ 4 / z.y ^ 2 := by
      have hpow : z.y ^ 2 ≤ (2 * y) ^ 2 :=
        pow_le_pow_left₀ z.y_pos.le (by linarith [hy.1]) 2
      apply (div_le_div_iff₀ (sq_pos_of_pos hy0) (sq_pos_of_pos z.y_pos)).2
      norm_num
      calc
        z.y ^ 2 ≤ (2 * y) ^ 2 := hpow
        _ = 4 * y ^ 2 := by ring
    have hK : 0 ≤ 4 * ‖P.s‖ + 6 * ‖P.s‖ ^ 2 := by positivity
    have hcoef : (4 * ‖P.s‖ + 6 * ‖P.s‖ ^ 2) / y ^ 2 ≤
        4 * (4 * ‖P.s‖ + 6 * ‖P.s‖ ^ 2) / z.y ^ 2 := by
      calc
        (4 * ‖P.s‖ + 6 * ‖P.s‖ ^ 2) / y ^ 2 =
            (4 * ‖P.s‖ + 6 * ‖P.s‖ ^ 2) * (1 / y ^ 2) := by ring
        _ ≤ (4 * ‖P.s‖ + 6 * ‖P.s‖ ^ 2) * (4 / z.y ^ 2) :=
          mul_le_mul_of_nonneg_left hinvSq hK
        _ = 4 * (4 * ‖P.s‖ + 6 * ‖P.s‖ ^ 2) / z.y ^ 2 := by ring
    calc
      ‖g' p y‖ ≤ ((4 * ‖P.s‖ + 6 * ‖P.s‖ ^ 2) / y ^ 2) *
          ‖d4BMPoincareSeed zy P.s p‖ := by
            simpa only [g', zy, dif_pos hy0] using hnorm
      _ ≤ (4 * (4 * ‖P.s‖ + 6 * ‖P.s‖ ^ 2) / z.y ^ 2) *
          ‖d4BMPoincareSeedVerticalSlice z P.s p y‖ := by
        apply mul_le_mul hcoef le_rfl (norm_nonneg _)
        exact div_nonneg (mul_nonneg (by norm_num) hK) (sq_nonneg _)
      _ ≤ (4 * (4 * ‖P.s‖ + 6 * ‖P.s‖ ^ 2) / z.y ^ 2) *
          ((2 ^ P.s.re * 4 ^ P.s.re) * ‖d4BMPoincareSeed z P.s p‖) :=
        mul_le_mul_of_nonneg_left (norm_d4BMPoincareSeed_vertical_le z P p hy)
          (div_nonneg (mul_nonneg (by norm_num) hK) (sq_nonneg _))
      _ = M p := by
        simp [M, d4BMMixedSecondJetVerticalLocalMajorant]
        ring
  have hymem : z.y ∈ t := by
    dsimp only [t]
    constructor <;> linarith [z.y_pos]
  have hbase : Summable fun p => g p z.y := by
    simpa only [g, d4BM_poincareSeedHorizontalFirstJetVerticalSlice_at_height] using
      summable_d4BMPoincareSeedHorizontalFirstJet z P
  have h := hasDerivAt_tsum_of_isPreconnected hM isOpen_Ioo isPreconnected_Ioo
    hderiv hbound hymem hbase hymem
  simpa only [g, g', dif_pos z.y_pos,
    d4BM_poincareSeedHorizontalFirstJetVerticalSlice_at_height] using h

/-- Raw vertical slice of the actual horizontal first jet. -/
def d4BMRawPoincareHorizontalFirstJetVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
    d4BMPoincareSeedHorizontalFirstJetVerticalSlice z P.s p y

/-- Completed vertical slice of the actual horizontal first jet. -/
def d4BMCompletedPoincareHorizontalFirstJetVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  reflectedCompletedLambda (2 * P.s) *
    d4BMRawPoincareHorizontalFirstJetVerticalSlice z P y

@[simp] theorem d4BM_completedPoincareHorizontalFirstJetVerticalSlice_at_height
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareHorizontalFirstJetVerticalSlice z P z.y =
      d4BMCompletedPoincareHorizontalFirstJet z P := by
  rfl

theorem hasDerivAt_d4BMCompletedPoincareHorizontalFirstJetVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt (d4BMCompletedPoincareHorizontalFirstJetVerticalSlice z P)
      (d4BMCompletedPoincareMixedSecondJet z P) z.y := by
  have h :=
    ((hasDerivAt_tsum_d4BMPoincareSeedHorizontalFirstJet_vertical z P).const_mul
      (1 / 2 : ℂ)).const_mul (reflectedCompletedLambda (2 * P.s))
  change HasDerivAt
    (fun y => d4BMCompletedPoincareHorizontalFirstJetVerticalSlice z P y)
    (d4BMCompletedPoincareMixedSecondJet z P) z.y
  simpa [d4BMCompletedPoincareHorizontalFirstJetVerticalSlice,
    d4BMRawPoincareHorizontalFirstJetVerticalSlice,
    d4BMCompletedPoincareMixedSecondJet,
    d4BMRawPoincareMixedSecondJet] using h

end
end RHTower
