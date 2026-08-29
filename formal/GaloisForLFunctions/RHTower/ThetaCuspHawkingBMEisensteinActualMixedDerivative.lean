import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualSignedFourierUniqueness
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPlebanskiMaassSecondJetBridge

/-!
# Actual mixed second derivative of the completed primitive Poincare series

Corpus conjecture C-A.9t2a supplies the missing off-diagonal entry of the
actual completed Poincare second jet.  The existing corpus proves the two pure
second derivatives, but a literal two-step Maass operator also uses
`partial_x partial_y`.  Here the mixed seed jet is certified as an actual
derivative, controlled by a locally summable majorant in the existing chamber
`Re(s) > 1`, and lifted through the raw and completed primitive-pair sums.

RH chain:

actual mixed jet -> actual two-step Maass legs -> canonical raise/lower weld ->
literal truncated Green/Stokes -> full cusp current -> balanced BM `++-`
coefficient -> negative BM leg -> conserved left-QNM projection -> HC94 -> RH.

All statements are unconditional; convergence is carried by the existing
absolute-convergence parameter.
-/

open Complex Real Set
open scoped BigOperators

namespace RHTower
noncomputable section

/-- The mixed `partial_x partial_y` jet of one primitive Poincare seed. -/
def d4BMPoincareSeedMixedSecondJet
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) : ℂ :=
  (4 * s * (p.pair.1 : ℂ) ^ 3 * (z.y : ℂ) *
        (d4BMPoincareHorizontalLinear z p : ℂ) /
        (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2 +
      (s / (z.y : ℂ) -
        2 * s * (p.pair.1 : ℂ) ^ 2 * (z.y : ℂ) /
          (d4BMPoincareQuadratic z p.pair : ℂ)) *
        (-2 * s * (p.pair.1 : ℂ) *
          (d4BMPoincareHorizontalLinear z p : ℂ) /
            (d4BMPoincareQuadratic z p.pair : ℂ))) *
    d4BMPoincareSeed z s p

/-- Differentiating the vertical first seed jet horizontally gives the mixed jet. -/
theorem hasDerivAt_d4BMPoincareSeedVerticalFirstJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    HasDerivAt
      (fun x : ℝ => d4BMPoincareSeedVerticalFirstJet
        (d4BMHorizontalCoordinate z x) s p)
      (d4BMPoincareSeedMixedSecondJet z s p) z.x := by
  let c : ℝ := p.pair.1
  let d : ℝ := p.pair.2
  let Q : ℝ → ℝ := fun x => (c * z.y) ^ 2 + (c * x + d) ^ 2
  let B : ℝ → ℂ := fun x =>
    s / (z.y : ℂ) -
      2 * s * (c : ℂ) ^ 2 * (z.y : ℂ) / (Q x : ℂ)
  let f : ℝ → ℂ := fun x =>
    d4BMPoincareSeed (d4BMHorizontalCoordinate z x) s p
  have hQpos : 0 < Q z.x := by
    change 0 < d4BMPoincareQuadratic z p.pair
    exact d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hQneR : Q z.x ≠ 0 := hQpos.ne'
  have hQne : (Q z.x : ℂ) ≠ 0 := by exact_mod_cast hQneR
  have hlinR : HasDerivAt (fun x : ℝ => c * x + d) c z.x := by
    simpa using ((hasDerivAt_id z.x).const_mul c).add_const d
  have hQderivR : HasDerivAt Q (2 * c * (c * z.x + d)) z.x := by
    dsimp only [Q]
    exact (((hasDerivAt_const z.x (c * z.y)).pow 2).add
      (hlinR.pow 2)).congr_deriv (by ring)
  have hQderiv : HasDerivAt (fun x : ℝ => (Q x : ℂ))
      ((2 * c * (c * z.x + d) : ℝ) : ℂ) z.x := hQderivR.ofReal_comp
  have hBraw :=
    (hasDerivAt_const z.x (s / (z.y : ℂ))).sub
      ((hasDerivAt_const z.x
        (2 * s * (c : ℂ) ^ 2 * (z.y : ℂ))).div hQderiv hQne)
  have hBderiv : HasDerivAt B
      (4 * s * (c : ℂ) ^ 3 * (z.y : ℂ) *
        (((c * z.x + d : ℝ) : ℂ)) / (Q z.x : ℂ) ^ 2) z.x := by
    dsimp only [B]
    apply hBraw.congr_deriv
    push_cast
    field_simp [hQne]
    ring
  have hf : HasDerivAt f
      (d4BMPoincareSeedHorizontalFirstJet z s p) z.x := by
    exact hasDerivAt_d4BMPoincareSeed_horizontal z s p
  have hprod := hBderiv.mul hf
  have hfun :
      (fun x : ℝ => d4BMPoincareSeedVerticalFirstJet
        (d4BMHorizontalCoordinate z x) s p) = fun x => B x * f x := by
    funext x
    unfold d4BMPoincareSeedVerticalFirstJet d4BMPoincareQuadratic
      d4BMHorizontalCoordinate
    dsimp only [B, f, Q]
    push_cast
    rfl
  rw [hfun]
  apply hprod.congr_deriv
  let U : ℂ := ((c * z.x + d : ℝ) : ℂ)
  let QC : ℂ := (Q z.x : ℂ)
  let F : ℂ := f z.x
  have hB : B z.x = s / (z.y : ℂ) -
      2 * s * (c : ℂ) ^ 2 * (z.y : ℂ) / QC := by rfl
  have hFvalue : F = d4BMPoincareSeed z s p := by
    unfold F f d4BMPoincareSeed d4BMPoincareQuadratic d4BMHorizontalCoordinate
    rfl
  have hfirst : d4BMPoincareSeedHorizontalFirstJet z s p =
      (-2 * s * (c : ℂ) * U / QC) * F := by
    rw [hFvalue]
    unfold d4BMPoincareSeedHorizontalFirstJet d4BMPoincareHorizontalLinear
      d4BMPoincareSeed d4BMPoincareQuadratic
    dsimp only [c, d, U, QC, Q, F, f]
    push_cast
    rfl
  have hmixed : d4BMPoincareSeedMixedSecondJet z s p =
      (4 * s * (c : ℂ) ^ 3 * (z.y : ℂ) * U / QC ^ 2 +
        (s / (z.y : ℂ) -
          2 * s * (c : ℂ) ^ 2 * (z.y : ℂ) / QC) *
            (-2 * s * (c : ℂ) * U / QC)) * F := by
    rw [hFvalue]
    unfold d4BMPoincareSeedMixedSecondJet d4BMPoincareHorizontalLinear
      d4BMPoincareSeed d4BMPoincareQuadratic
    dsimp only [c, d, U, QC, Q, F, f]
    push_cast
    rfl
  rw [hB, hfirst, hmixed]
  ring

/-- The mixed jet has the same `y^-2` summability scale as the pure second jets. -/
lemma norm_d4BMPoincareSeedMixedSecondJet_le
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    ‖d4BMPoincareSeedMixedSecondJet z s p‖ ≤
      ((4 * ‖s‖ + 6 * ‖s‖ ^ 2) / z.y ^ 2) *
        ‖d4BMPoincareSeed z s p‖ := by
  let c : ℝ := p.pair.1
  let u : ℝ := d4BMPoincareHorizontalLinear z p
  let Q : ℝ := d4BMPoincareQuadratic z p.pair
  have hQ : 0 < Q := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hy2 : 0 < z.y ^ 2 := sq_pos_of_pos z.y_pos
  have hcQ : c ^ 2 * z.y ^ 2 ≤ Q := by
    dsimp only [Q, c, u, d4BMPoincareQuadratic,
      d4BMPoincareHorizontalLinear]
    nlinarith [sq_nonneg ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ))]
  have hamgm : 2 * z.y * |c| * |u| ≤ Q := by
    calc
      2 * z.y * |c| * |u| ≤ (z.y * |c|) ^ 2 + |u| ^ 2 := by
        nlinarith [sq_nonneg (z.y * |c| - |u|)]
      _ = z.y ^ 2 * |c| ^ 2 + |u| ^ 2 := by ring
      _ = z.y ^ 2 * c ^ 2 + u ^ 2 := by rw [sq_abs c, sq_abs u]
      _ = Q := by
        dsimp only [Q, c, u, d4BMPoincareQuadratic,
          d4BMPoincareHorizontalLinear]
        ring
  have hcuQ : z.y * |c| * |u| ≤ Q := by
    nlinarith [abs_nonneg c, abs_nonneg u, z.y_pos, hQ]
  have hcQabs : |c| ^ 2 * z.y ^ 2 ≤ Q := by
    simpa only [sq_abs] using hcQ
  have hcu_nonneg : 0 ≤ z.y * |c| * |u| :=
    mul_nonneg (mul_nonneg z.y_pos.le (abs_nonneg c)) (abs_nonneg u)
  have hprod :
      (|c| ^ 2 * z.y ^ 2) * (z.y * |c| * |u|) ≤ Q * Q :=
    mul_le_mul hcQabs hcuQ hcu_nonneg hQ.le
  have hratio : |c| ^ 3 * z.y * |u| / Q ^ 2 ≤ 1 / z.y ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hQ) hy2).2
    nlinarith [abs_nonneg c, abs_nonneg u]
  have hcu : |c| * |u| / Q ≤ 1 / z.y := by
    apply (div_le_div_iff₀ hQ z.y_pos).2
    nlinarith [abs_nonneg c, abs_nonneg u]
  let D : ℂ := 4 * s * (c : ℂ) ^ 3 * (z.y : ℂ) * (u : ℂ) / (Q : ℂ) ^ 2
  let A : ℂ := -2 * s * (c : ℂ) * (u : ℂ) / (Q : ℂ)
  have hD : ‖D‖ ≤ 4 * ‖s‖ / z.y ^ 2 := by
    dsimp only [D]
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ,
      abs_of_pos z.y_pos]
    norm_num
    calc
      4 * ‖s‖ * |c| ^ 3 * z.y * |u| / Q ^ 2 =
          4 * ‖s‖ * (|c| ^ 3 * z.y * |u| / Q ^ 2) := by ring
      _ ≤ 4 * ‖s‖ * (1 / z.y ^ 2) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 4 * ‖s‖ / z.y ^ 2 := by ring
  have hA : ‖A‖ ≤ 2 * ‖s‖ / z.y := by
    dsimp only [A]
    rw [norm_div, norm_mul, norm_mul, norm_mul]
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ]
    norm_num
    calc
      2 * ‖s‖ * |c| * |u| / Q = 2 * ‖s‖ * (|c| * |u| / Q) := by ring
      _ ≤ 2 * ‖s‖ * (1 / z.y) :=
        mul_le_mul_of_nonneg_left hcu (by positivity)
      _ = 2 * ‖s‖ / z.y := by ring
  have hAupper : 0 ≤ 2 * ‖s‖ / z.y :=
    div_nonneg (mul_nonneg (by norm_num) (norm_nonneg s)) z.y_pos.le
  have hdecomp :
      d4BMPoincareSeedMixedSecondJet z s p =
        D * d4BMPoincareSeed z s p +
          A * d4BMPoincareSeedVerticalFirstJet z s p := by
    unfold d4BMPoincareSeedMixedSecondJet
      d4BMPoincareSeedVerticalFirstJet
    dsimp only [D, A, c, u, Q]
    push_cast
    ring
  rw [hdecomp]
  calc
    ‖D * d4BMPoincareSeed z s p +
        A * d4BMPoincareSeedVerticalFirstJet z s p‖ ≤
      ‖D * d4BMPoincareSeed z s p‖ +
        ‖A * d4BMPoincareSeedVerticalFirstJet z s p‖ := norm_add_le _ _
    _ = ‖D‖ * ‖d4BMPoincareSeed z s p‖ +
        ‖A‖ * ‖d4BMPoincareSeedVerticalFirstJet z s p‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ (4 * ‖s‖ / z.y ^ 2) * ‖d4BMPoincareSeed z s p‖ +
        (2 * ‖s‖ / z.y) *
          ((3 * ‖s‖ / z.y) * ‖d4BMPoincareSeed z s p‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hD (norm_nonneg _)
      · exact mul_le_mul hA
          (norm_d4BMPoincareSeedVerticalFirstJet_le z s p)
          (norm_nonneg _) hAupper
    _ = ((4 * ‖s‖ + 6 * ‖s‖ ^ 2) / z.y ^ 2) *
        ‖d4BMPoincareSeed z s p‖ := by
      field_simp [z.y_pos.ne']
      ring

/-- Horizontal local majorant for the mixed second seed jet. -/
def d4BMMixedSecondJetHorizontalLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (p : D4BMPrimitiveIntegerPair) : ℝ :=
  (((4 * ‖P.s‖ + 6 * ‖P.s‖ ^ 2) / z.y ^ 2) * 3 ^ P.s.re) *
    ‖d4BMPoincareSeed z P.s p‖

lemma summable_d4BMMixedSecondJetHorizontalLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable (d4BMMixedSecondJetHorizontalLocalMajorant z P) := by
  exact (summable_d4BMPoincareSeed z P).norm.mul_left _

/-- Termwise horizontal differentiation of the actual vertical first-jet sum. -/
theorem hasDerivAt_tsum_d4BMPoincareSeedVerticalFirstJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedVerticalFirstJet
          (d4BMHorizontalCoordinate z x) P.s p)
      (∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedMixedSecondJet z P.s p) z.x := by
  let t : Set ℝ := Ioo (z.x - z.y) (z.x + z.y)
  let g : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p x =>
    d4BMPoincareSeedVerticalFirstJet
      (d4BMHorizontalCoordinate z x) P.s p
  let g' : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p x =>
    d4BMPoincareSeedMixedSecondJet
      (d4BMHorizontalCoordinate z x) P.s p
  let M := d4BMMixedSecondJetHorizontalLocalMajorant z P
  have hM : Summable M :=
    summable_d4BMMixedSecondJetHorizontalLocalMajorant z P
  have hopen : IsOpen t := isOpen_Ioo
  have hconn : IsPreconnected t := isPreconnected_Ioo
  have hderiv : ∀ p, ∀ x ∈ t, HasDerivAt (g p) (g' p x) x := by
    intro p x hx
    simpa [g, g', d4BMHorizontalCoordinate] using
      hasDerivAt_d4BMPoincareSeedVerticalFirstJet_horizontal
        (d4BMHorizontalCoordinate z x) P.s p
  have hK : 0 ≤ (4 * ‖P.s‖ + 6 * ‖P.s‖ ^ 2) / z.y ^ 2 := by
    apply div_nonneg
    · positivity
    · exact sq_nonneg _
  have hbound : ∀ p, ∀ x ∈ t, ‖g' p x‖ ≤ M p := by
    intro p x hx
    calc
      ‖g' p x‖ ≤
          ((4 * ‖P.s‖ + 6 * ‖P.s‖ ^ 2) / z.y ^ 2) *
            ‖d4BMPoincareSeed (d4BMHorizontalCoordinate z x) P.s p‖ := by
        dsimp only [g']
        simpa [d4BMHorizontalCoordinate] using
          norm_d4BMPoincareSeedMixedSecondJet_le
            (d4BMHorizontalCoordinate z x) P.s p
      _ ≤ ((4 * ‖P.s‖ + 6 * ‖P.s‖ ^ 2) / z.y ^ 2) *
          (3 ^ P.s.re * ‖d4BMPoincareSeed z P.s p‖) :=
        mul_le_mul_of_nonneg_left
          (norm_d4BMPoincareSeed_horizontal_le z P p hx) hK
      _ = M p := by
        simp [M, d4BMMixedSecondJetHorizontalLocalMajorant]
        ring
  have hzmem : z.x ∈ t := by
    dsimp only [t]
    constructor <;> linarith [z.y_pos]
  have hbase : Summable fun p => g p z.x := by
    simpa [g, d4BMHorizontalCoordinate] using
      summable_d4BMPoincareSeedVerticalFirstJet z P
  have h := hasDerivAt_tsum_of_isPreconnected hM hopen hconn hderiv hbound
    hzmem hbase hzmem
  simpa [g, g', d4BMHorizontalCoordinate] using h

/-- Absolute summability of the mixed second seed jet at every point. -/
theorem summable_d4BMPoincareSeedMixedSecondJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedMixedSecondJet z P.s p := by
  let K : ℝ := (4 * ‖P.s‖ + 6 * ‖P.s‖ ^ 2) / z.y ^ 2
  have hK : Summable fun p : D4BMPrimitiveIntegerPair =>
      K * ‖d4BMPoincareSeed z P.s p‖ :=
    (summable_d4BMPoincareSeed z P).norm.mul_left K
  refine Summable.of_norm_bounded hK ?_
  intro p
  exact norm_d4BMPoincareSeedMixedSecondJet_le z P.s p

/-- Raw primitive-pair mixed second jet. -/
def d4BMRawPoincareMixedSecondJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
    d4BMPoincareSeedMixedSecondJet z P.s p

/-- The raw vertical first jet has the claimed actual horizontal derivative. -/
theorem hasDerivAt_d4BMRawPoincareVerticalFirstJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => d4BMRawPoincareVerticalFirstJet
        (d4BMHorizontalCoordinate z x) P)
      (d4BMRawPoincareMixedSecondJet z P) z.x := by
  have h :=
    (hasDerivAt_tsum_d4BMPoincareSeedVerticalFirstJet_horizontal z P).const_mul
      (1 / 2 : ℂ)
  simpa [d4BMRawPoincareVerticalFirstJet,
    d4BMRawPoincareMixedSecondJet, d4BMHorizontalCoordinate] using h

/-- Completed primitive-pair mixed second jet. -/
def d4BMCompletedPoincareMixedSecondJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  reflectedCompletedLambda (2 * P.s) * d4BMRawPoincareMixedSecondJet z P

/-- The completed vertical first jet has the claimed actual horizontal derivative. -/
theorem hasDerivAt_d4BMCompletedPoincareVerticalFirstJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => d4BMCompletedPoincareVerticalFirstJet
        (d4BMHorizontalCoordinate z x) P)
      (d4BMCompletedPoincareMixedSecondJet z P) z.x := by
  have h :=
    (hasDerivAt_d4BMRawPoincareVerticalFirstJet_horizontal z P).const_mul
      (reflectedCompletedLambda (2 * P.s))
  simpa [d4BMCompletedPoincareVerticalFirstJet,
    d4BMCompletedPoincareMixedSecondJet] using h

/-- Actual value and first derivatives of the completed scalar Poincare leg,
embedded in the BM chart with inactive `tau` and `xi` directions. -/
def d4BMActualCompletedPoincareFullFirstJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : D4BMFullFirstJet where
  value := d4BMCompletedEisensteinPoincareSeries z P
  tau := 0
  horizonX := d4BMCompletedPoincareHorizontalFirstJet z P
  sigma := d4BMCompletedPoincareVerticalFirstJet z P
  xi := 0

/-- Complete actual scalar Poincare second jet in the active `(x,y)` plane. -/
def d4BMActualCompletedPoincareFullSecondJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : D4BMFullSecondJet where
  first := d4BMActualCompletedPoincareFullFirstJet z P
  tauTau := 0
  tauHorizonX := 0
  tauSigma := 0
  tauXi := 0
  horizonXHorizonX := d4BMCompletedPoincareHorizontalSecondJet z P
  horizonXSigma := d4BMCompletedPoincareMixedSecondJet z P
  horizonXXi := 0
  sigmaSigma := d4BMCompletedPoincareVerticalSecondJet z P
  sigmaXi := 0
  xiXi := 0

/-- Literal actual weight `+4` completed Poincare leg. -/
def d4BMActualCompletedPoincareRaiseLeg
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMMaassRaiseTwoRaiseZeroOnFullSecondJet (z.y : ℂ)
    (d4BMActualCompletedPoincareFullSecondJet z P)

/-- Literal actual weight `-4` completed Poincare leg. -/
def d4BMActualCompletedPoincareLowerLeg
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMMaassLowerNegTwoLowerZeroOnFullSecondJet (z.y : ℂ)
    (d4BMActualCompletedPoincareFullSecondJet z P)

/-- Explicit differential expression for the actual weight `+4` leg. -/
theorem d4BM_actualCompletedPoincareRaiseLeg_eq
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualCompletedPoincareRaiseLeg z P =
      (z.y : ℂ) ^ 2 *
          (d4BMCompletedPoincareVerticalSecondJet z P -
            d4BMCompletedPoincareHorizontalSecondJet z P +
            2 * Complex.I * d4BMCompletedPoincareMixedSecondJet z P) +
        2 * (z.y : ℂ) *
          (d4BMCompletedPoincareVerticalFirstJet z P +
            Complex.I * d4BMCompletedPoincareHorizontalFirstJet z P) := by
  rfl

/-- Explicit differential expression for the actual weight `-4` leg. -/
theorem d4BM_actualCompletedPoincareLowerLeg_eq
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualCompletedPoincareLowerLeg z P =
      (z.y : ℂ) ^ 2 *
          (d4BMCompletedPoincareVerticalSecondJet z P -
            d4BMCompletedPoincareHorizontalSecondJet z P -
            2 * Complex.I * d4BMCompletedPoincareMixedSecondJet z P) +
        2 * (z.y : ℂ) *
          (d4BMCompletedPoincareVerticalFirstJet z P -
            Complex.I * d4BMCompletedPoincareHorizontalFirstJet z P) := by
  rfl

end
end RHTower
