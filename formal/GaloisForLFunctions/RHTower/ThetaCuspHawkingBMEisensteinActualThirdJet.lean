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
    push_cast
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
    push_cast
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
    push_cast
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
              field_simp [hQ.ne'] <;> ring
    _ ≤ (1 / z.y ^ 2) * (1 / z.y) := by
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 1 / z.y ^ 3 := by field_simp [z.y_pos.ne'] <;> ring

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
            field_simp [hQ.ne'] <;> ring
    _ ≤ (1 / z.y) ^ 3 := by exact pow_le_pow_left₀ hnonneg h 3
    _ = 1 / z.y ^ 3 := by field_simp [z.y_pos.ne'] <;> ring

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
            field_simp [hQ.ne'] <;> ring
    _ ≤ (1 / z.y ^ 2) ^ 2 * z.y := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnonneg h 2) z.y_pos.le
    _ = 1 / z.y ^ 3 := by field_simp [z.y_pos.ne'] <;> ring

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
              field_simp [hQ.ne'] <;> ring
    _ ≤ (1 / z.y ^ 2) ^ 2 * 1 * z.y := by
      gcongr
      exact z.y_pos.le
    _ = 1 / z.y ^ 3 := by field_simp [z.y_pos.ne'] <;> ring

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

end
end RHTower
