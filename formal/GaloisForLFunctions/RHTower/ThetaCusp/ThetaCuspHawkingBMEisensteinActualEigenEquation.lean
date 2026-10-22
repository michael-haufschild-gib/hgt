import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinPoincareSeedEigenEquation
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Actual hyperbolic eigen-equation for the completed primitive Poincaré series

Corpus conjecture C-A.9r is the normal-convergence weld between the actual seed
calculus and the modular Green/Stokes route.  In the exact corpus convergence
chamber `Re(s) > 1`, this module proves local summable majorants for all first
and second horizontal/vertical seed jets, differentiates the infinite
primitive-pair sum term by term, and proves

`y² (∂ₓ² + ∂ᵧ²) E*(z,s) = s(s-1) E*(z,s)`

for the actual completed Poincaré series.  No stronger artificial convergence
chamber is introduced.  At `s = 1/2 + u`, the eigenvalue is exactly the corpus
geometric eigenvalue `u² - 1/4`.

RH chain:

actual Poincaré eigenfunction → modular Green/Stokes → polarized BM `++−`
source → conserved left-QNM projection → HC94 clock defect → RH.

All theorems are unconditional; convergence inequalities are carried by the
existing parameter structure.
-/

open Complex Real Set
open scoped BigOperators

namespace RHTower
noncomputable section

lemma d4BM_rpow_neg_le_of_le_mul
    {P Q D sigma : ℝ} (hP : 0 < P) (hQ : 0 < Q) (hD : 0 < D)
    (hsigma : 0 ≤ sigma) (hPQ : P ≤ D * Q) :
    Q ^ (-sigma) ≤ D ^ sigma * P ^ (-sigma) := by
  have hanti : (D * Q) ^ (-sigma) ≤ P ^ (-sigma) :=
    Real.rpow_le_rpow_of_nonpos hP hPQ (by linarith)
  have hfactor : D ^ sigma * (D * Q) ^ (-sigma) = Q ^ (-sigma) := by
    rw [Real.mul_rpow hD.le hQ.le, Real.rpow_neg hD.le,
      Real.rpow_neg hQ.le]
    have hDr : D ^ sigma ≠ 0 := (Real.rpow_pos_of_pos hD sigma).ne'
    have hQr : Q ^ sigma ≠ 0 := (Real.rpow_pos_of_pos hQ sigma).ne'
    field_simp
  rw [← hfactor]
  exact mul_le_mul_of_nonneg_left hanti (Real.rpow_nonneg hD.le _)

lemma d4BM_horizontal_quadratic_base_le_three_mul
    (z : D4BMUpperHalfPlaneCoordinate) (p : D4BMPrimitiveIntegerPair)
    {x : ℝ} (hx : x ∈ Ioo (z.x - z.y) (z.x + z.y)) :
    d4BMPoincareQuadratic z p.pair ≤
      3 * d4BMPoincareQuadratic (d4BMHorizontalCoordinate z x) p.pair := by
  have hdelta : |x - z.x| < z.y := by
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hdeltaSq : (x - z.x) ^ 2 ≤ z.y ^ 2 := by
    have hle : |x - z.x| ≤ z.y := le_of_lt hdelta
    nlinarith [sq_abs (x - z.x), abs_nonneg (x - z.x), z.y_pos]
  let c : ℝ := p.pair.1
  let d : ℝ := p.pair.2
  let v : ℝ := c * x + d
  have hu : c * z.x + d = v - c * (x - z.x) := by
    dsimp only [v]
    ring
  have hcdelta : (c * (x - z.x)) ^ 2 ≤ c ^ 2 * z.y ^ 2 := by
    nlinarith [sq_nonneg c]
  rw [d4BMPoincareQuadratic, d4BMPoincareQuadratic]
  dsimp only [d4BMHorizontalCoordinate, c, d, v] at *
  rw [hu]
  nlinarith [sq_nonneg (v + c * (x - z.x)), hcdelta]

lemma norm_d4BMPoincareSeed_horizontal_le
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (p : D4BMPrimitiveIntegerPair) {x : ℝ}
    (hx : x ∈ Ioo (z.x - z.y) (z.x + z.y)) :
    ‖d4BMPoincareSeed (d4BMHorizontalCoordinate z x) P.s p‖ ≤
      3 ^ P.s.re * ‖d4BMPoincareSeed z P.s p‖ := by
  have hsigma : 0 ≤ P.s.re := by linarith [P.re_gt_one]
  have hQz := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hQx := d4BMPoincareQuadratic_pos
    (d4BMHorizontalCoordinate z x) p.pair p.pair_ne_zero
  have hquad := d4BM_horizontal_quadratic_base_le_three_mul z p hx
  have hrpow := d4BM_rpow_neg_le_of_le_mul hQz hQx (by norm_num : (0 : ℝ) < 3)
    hsigma hquad
  rw [norm_d4BMPoincareSeed, norm_d4BMPoincareSeed]
  dsimp only [d4BMHorizontalCoordinate]
  calc
    z.y ^ P.s.re * d4BMPoincareQuadratic
          { x := x, y := z.y, y_pos := z.y_pos } p.pair ^ (-P.s.re) ≤
        z.y ^ P.s.re *
          (3 ^ P.s.re * d4BMPoincareQuadratic z p.pair ^ (-P.s.re)) :=
      mul_le_mul_of_nonneg_left hrpow (Real.rpow_nonneg z.y_pos.le _)
    _ = 3 ^ P.s.re *
        (z.y ^ P.s.re * d4BMPoincareQuadratic z p.pair ^ (-P.s.re)) := by ring

lemma norm_d4BMPoincareSeedHorizontalFirstJet_le
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    ‖d4BMPoincareSeedHorizontalFirstJet z s p‖ ≤
      (2 * ‖s‖ / z.y) * ‖d4BMPoincareSeed z s p‖ := by
  let c : ℝ := p.pair.1
  let u : ℝ := d4BMPoincareHorizontalLinear z p
  let Q : ℝ := d4BMPoincareQuadratic z p.pair
  have hQ : 0 < Q := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hamgm : 2 * z.y * |c| * |u| ≤ Q := by
    calc
      2 * z.y * |c| * |u| ≤ (z.y * |c|) ^ 2 + |u| ^ 2 := by
        nlinarith [sq_nonneg (z.y * |c| - |u|)]
      _ = z.y ^ 2 * |c| ^ 2 + |u| ^ 2 := by ring
      _ = z.y ^ 2 * c ^ 2 + u ^ 2 := by
        rw [sq_abs c, sq_abs u]
      _ = Q := by
        dsimp only [Q, c, u, d4BMPoincareQuadratic,
          d4BMPoincareHorizontalLinear]
        ring
  have hcu : |c| * |u| / Q ≤ 1 / z.y := by
    apply (div_le_div_iff₀ hQ z.y_pos).2
    have hc : 0 ≤ |c| := abs_nonneg _
    have hu : 0 ≤ |u| := abs_nonneg _
    nlinarith
  unfold d4BMPoincareSeedHorizontalFirstJet
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  change ‖-2 * s * (c : ℂ) * (u : ℂ) / (Q : ℂ)‖ ≤ 2 * ‖s‖ / z.y
  rw [norm_div, norm_mul, norm_mul, norm_mul]
  simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ]
  norm_num
  calc
    2 * ‖s‖ * |c| * |u| / Q = 2 * ‖s‖ * (|c| * |u| / Q) := by ring
    _ ≤ 2 * ‖s‖ * (1 / z.y) :=
      mul_le_mul_of_nonneg_left hcu (mul_nonneg (by norm_num) (norm_nonneg s))
    _ = 2 * ‖s‖ / z.y := by ring

lemma norm_d4BMPoincareSeedHorizontalSecondJet_le
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    ‖d4BMPoincareSeedHorizontalSecondJet z s p‖ ≤
      ((2 * ‖s‖ + 4 * ‖s‖ * ‖s + 1‖) / z.y ^ 2) *
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
  have huQ : u ^ 2 ≤ Q := by
    dsimp only [Q, c, u, d4BMPoincareQuadratic,
      d4BMPoincareHorizontalLinear]
    nlinarith [sq_nonneg ((p.pair.1 : ℝ) * z.y)]
  have hc : |c| ^ 2 / Q ≤ 1 / z.y ^ 2 := by
    apply (div_le_div_iff₀ hQ hy2).2
    rw [sq_abs c]
    nlinarith
  have hcu : |c| ^ 2 * |u| ^ 2 / Q ^ 2 ≤ 1 / z.y ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hQ) hy2).2
    rw [sq_abs c, sq_abs u]
    have hprod := mul_le_mul hcQ huQ (sq_nonneg u) hQ.le
    nlinarith
  have hc' : c ^ 2 / Q ≤ 1 / z.y ^ 2 := by
    simpa only [sq_abs] using hc
  have hcu' : c ^ 2 * u ^ 2 / Q ^ 2 ≤ 1 / z.y ^ 2 := by
    simpa only [sq_abs] using hcu
  have hterm1 : ‖-2 * s * (c : ℂ) ^ 2 / (Q : ℂ)‖ ≤
      2 * ‖s‖ / z.y ^ 2 := by
    rw [norm_div, norm_mul, norm_mul, norm_pow]
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ]
    norm_num
    calc
      2 * ‖s‖ * c ^ 2 / Q = 2 * ‖s‖ * (c ^ 2 / Q) := by ring
      _ ≤ 2 * ‖s‖ * (1 / z.y ^ 2) :=
        mul_le_mul_of_nonneg_left hc' (mul_nonneg (by norm_num) (norm_nonneg s))
      _ = 2 * ‖s‖ / z.y ^ 2 := by ring
  have hterm2 :
      ‖4 * s * (s + 1) * (c : ℂ) ^ 2 * (u : ℂ) ^ 2 / (Q : ℂ) ^ 2‖ ≤
        4 * ‖s‖ * ‖s + 1‖ / z.y ^ 2 := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow,
      norm_pow, norm_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ]
    norm_num
    calc
      4 * ‖s‖ * ‖s + 1‖ * c ^ 2 * u ^ 2 / Q ^ 2 =
          (4 * ‖s‖ * ‖s + 1‖) * (c ^ 2 * u ^ 2 / Q ^ 2) := by ring
      _ ≤ (4 * ‖s‖ * ‖s + 1‖) * (1 / z.y ^ 2) :=
        mul_le_mul_of_nonneg_left hcu'
          (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg s)) (norm_nonneg _))
      _ = 4 * ‖s‖ * ‖s + 1‖ / z.y ^ 2 := by ring
  unfold d4BMPoincareSeedHorizontalSecondJet
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖-2 * s * (p.pair.1 : ℂ) ^ 2 /
          (d4BMPoincareQuadratic z p.pair : ℂ) +
        4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 2 *
          (d4BMPoincareHorizontalLinear z p : ℂ) ^ 2 /
            (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2‖ ≤
        ‖-2 * s * (c : ℂ) ^ 2 / (Q : ℂ)‖ +
          ‖4 * s * (s + 1) * (c : ℂ) ^ 2 * (u : ℂ) ^ 2 / (Q : ℂ) ^ 2‖ := by
      dsimp only [c, u, Q]
      exact norm_add_le _ _
    _ ≤ 2 * ‖s‖ / z.y ^ 2 + 4 * ‖s‖ * ‖s + 1‖ / z.y ^ 2 :=
      add_le_add hterm1 hterm2
    _ = (2 * ‖s‖ + 4 * ‖s‖ * ‖s + 1‖) / z.y ^ 2 := by ring

def d4BMRawPoincareHorizontalFirstJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
    d4BMPoincareSeedHorizontalFirstJet z P.s p

def d4BMRawPoincareHorizontalSecondJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
    d4BMPoincareSeedHorizontalSecondJet z P.s p

def d4BMHorizontalFirstJetLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (p : D4BMPrimitiveIntegerPair) : ℝ :=
  (2 * ‖P.s‖ / z.y) * 3 ^ P.s.re * ‖d4BMPoincareSeed z P.s p‖

def d4BMHorizontalSecondJetLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (p : D4BMPrimitiveIntegerPair) : ℝ :=
  ((2 * ‖P.s‖ + 4 * ‖P.s‖ * ‖P.s + 1‖) / z.y ^ 2) *
    3 ^ P.s.re * ‖d4BMPoincareSeed z P.s p‖

lemma summable_d4BMHorizontalFirstJetLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable (d4BMHorizontalFirstJetLocalMajorant z P) := by
  have h := (summable_d4BMPoincareSeed z P).norm.mul_left
    ((2 * ‖P.s‖ / z.y) * 3 ^ P.s.re)
  change Summable fun p =>
    ((2 * ‖P.s‖ / z.y) * 3 ^ P.s.re) * ‖d4BMPoincareSeed z P.s p‖
  exact h

lemma summable_d4BMHorizontalSecondJetLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable (d4BMHorizontalSecondJetLocalMajorant z P) := by
  have h := (summable_d4BMPoincareSeed z P).norm.mul_left
    (((2 * ‖P.s‖ + 4 * ‖P.s‖ * ‖P.s + 1‖) / z.y ^ 2) * 3 ^ P.s.re)
  change Summable fun p =>
    (((2 * ‖P.s‖ + 4 * ‖P.s‖ * ‖P.s + 1‖) / z.y ^ 2) * 3 ^ P.s.re) *
      ‖d4BMPoincareSeed z P.s p‖
  exact h

theorem hasDerivAt_tsum_d4BMPoincareSeed_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeed (d4BMHorizontalCoordinate z x) P.s p)
      (∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalFirstJet z P.s p) z.x := by
  let t : Set ℝ := Ioo (z.x - z.y) (z.x + z.y)
  let g : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p x =>
    d4BMPoincareSeed (d4BMHorizontalCoordinate z x) P.s p
  let g' : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p x =>
    d4BMPoincareSeedHorizontalFirstJet (d4BMHorizontalCoordinate z x) P.s p
  let M := d4BMHorizontalFirstJetLocalMajorant z P
  have hM : Summable M := summable_d4BMHorizontalFirstJetLocalMajorant z P
  have hopen : IsOpen t := isOpen_Ioo
  have hconn : IsPreconnected t := isPreconnected_Ioo
  have hderiv : ∀ p, ∀ x ∈ t, HasDerivAt (g p) (g' p x) x := by
    intro p x hx
    simpa [g, g', d4BMHorizontalCoordinate] using
      hasDerivAt_d4BMPoincareSeed_horizontal (d4BMHorizontalCoordinate z x) P.s p
  have hbound : ∀ p, ∀ x ∈ t, ‖g' p x‖ ≤ M p := by
    intro p x hx
    have hK : 0 ≤ 2 * ‖P.s‖ / z.y :=
      div_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) z.y_pos.le
    calc
      ‖g' p x‖ ≤ (2 * ‖P.s‖ / z.y) * ‖g p x‖ := by
        dsimp only [g, g']
        simpa [d4BMHorizontalCoordinate] using
          norm_d4BMPoincareSeedHorizontalFirstJet_le
            (d4BMHorizontalCoordinate z x) P.s p
      _ ≤ (2 * ‖P.s‖ / z.y) *
          (3 ^ P.s.re * ‖d4BMPoincareSeed z P.s p‖) :=
        mul_le_mul_of_nonneg_left (norm_d4BMPoincareSeed_horizontal_le z P p hx) hK
      _ = M p := by
        simp [M, d4BMHorizontalFirstJetLocalMajorant]
        ring
  have hzmem : z.x ∈ t := by
    dsimp only [t]
    constructor <;> linarith [z.y_pos]
  have hbase : Summable fun p => g p z.x := by
    simpa [g, d4BMHorizontalCoordinate] using summable_d4BMPoincareSeed z P
  have h := hasDerivAt_tsum_of_isPreconnected hM hopen hconn hderiv hbound
    hzmem hbase hzmem
  simpa [g, g', d4BMHorizontalCoordinate] using h

theorem hasDerivAt_tsum_d4BMPoincareSeedHorizontalFirstJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalFirstJet (d4BMHorizontalCoordinate z x) P.s p)
      (∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedHorizontalSecondJet z P.s p) z.x := by
  let t : Set ℝ := Ioo (z.x - z.y) (z.x + z.y)
  let g : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p x =>
    d4BMPoincareSeedHorizontalFirstJet (d4BMHorizontalCoordinate z x) P.s p
  let g' : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p x =>
    d4BMPoincareSeedHorizontalSecondJet (d4BMHorizontalCoordinate z x) P.s p
  let M := d4BMHorizontalSecondJetLocalMajorant z P
  have hM : Summable M := summable_d4BMHorizontalSecondJetLocalMajorant z P
  have hopen : IsOpen t := isOpen_Ioo
  have hconn : IsPreconnected t := isPreconnected_Ioo
  have hderiv : ∀ p, ∀ x ∈ t, HasDerivAt (g p) (g' p x) x := by
    intro p x hx
    simpa [g, g', d4BMHorizontalCoordinate] using
      hasDerivAt_d4BMPoincareSeedHorizontalFirstJet_horizontal
        (d4BMHorizontalCoordinate z x) P.s p
  have hbound : ∀ p, ∀ x ∈ t, ‖g' p x‖ ≤ M p := by
    intro p x hx
    have hK : 0 ≤
        (2 * ‖P.s‖ + 4 * ‖P.s‖ * ‖P.s + 1‖) / z.y ^ 2 := by
      apply div_nonneg
      · positivity
      · exact sq_nonneg _
    calc
      ‖g' p x‖ ≤
          ((2 * ‖P.s‖ + 4 * ‖P.s‖ * ‖P.s + 1‖) / z.y ^ 2) * ‖
            d4BMPoincareSeed (d4BMHorizontalCoordinate z x) P.s p‖ := by
        dsimp only [g']
        simpa [d4BMHorizontalCoordinate] using
          norm_d4BMPoincareSeedHorizontalSecondJet_le
            (d4BMHorizontalCoordinate z x) P.s p
      _ ≤ ((2 * ‖P.s‖ + 4 * ‖P.s‖ * ‖P.s + 1‖) / z.y ^ 2) *
          (3 ^ P.s.re * ‖d4BMPoincareSeed z P.s p‖) :=
        mul_le_mul_of_nonneg_left (norm_d4BMPoincareSeed_horizontal_le z P p hx) hK
      _ = M p := by
        simp [M, d4BMHorizontalSecondJetLocalMajorant]
        ring
  have hzmem : z.x ∈ t := by
    dsimp only [t]
    constructor <;> linarith [z.y_pos]
  have hbase : Summable fun p => g p z.x := by
    have hbaseMaj := (summable_d4BMPoincareSeed z P).norm.mul_left
      (2 * ‖P.s‖ / z.y)
    refine Summable.of_norm_bounded hbaseMaj ?_
    intro p
    simpa [g, d4BMHorizontalCoordinate] using
      norm_d4BMPoincareSeedHorizontalFirstJet_le z P.s p
  have h := hasDerivAt_tsum_of_isPreconnected hM hopen hconn hderiv hbound
    hzmem hbase hzmem
  simpa [g, g', d4BMHorizontalCoordinate] using h

theorem hasDerivAt_d4BMRawEisensteinPoincareSeries_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => d4BMRawEisensteinPoincareSeries
        (d4BMHorizontalCoordinate z x) P)
      (d4BMRawPoincareHorizontalFirstJet z P) z.x := by
  have h := (hasDerivAt_tsum_d4BMPoincareSeed_horizontal z P).const_mul (1 / 2 : ℂ)
  simpa [d4BMRawEisensteinPoincareSeries, d4BMRawPoincareHorizontalFirstJet]
    using h

theorem hasDerivAt_d4BMRawPoincareHorizontalFirstJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => d4BMRawPoincareHorizontalFirstJet
        (d4BMHorizontalCoordinate z x) P)
      (d4BMRawPoincareHorizontalSecondJet z P) z.x := by
  have h :=
    (hasDerivAt_tsum_d4BMPoincareSeedHorizontalFirstJet_horizontal z P).const_mul
      (1 / 2 : ℂ)
  simpa [d4BMRawPoincareHorizontalFirstJet, d4BMRawPoincareHorizontalSecondJet]
    using h

lemma norm_d4BMPoincareSeedVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) {y : ℝ} (hy : 0 < y) :
    ‖d4BMPoincareSeedVerticalSlice z s p y‖ =
      y ^ s.re *
        ((((p.pair.1 : ℝ) * y) ^ 2 +
          ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ 2) : ℝ) ^ (-s.re) := by
  let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy⟩
  have hseed : d4BMPoincareSeedVerticalSlice z s p y =
      d4BMPoincareSeed zy s p := by rfl
  rw [hseed, norm_d4BMPoincareSeed]
  rfl

theorem d4BM_poincareSeedVerticalSlice_rebase
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) (y : ℝ) (hy : 0 < y) :
    d4BMPoincareSeedVerticalSlice ⟨z.x, y, hy⟩ s p =
      d4BMPoincareSeedVerticalSlice z s p := by
  rfl

theorem d4BM_poincareSeedVerticalFirstJetSlice_rebase
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) (y : ℝ) (hy : 0 < y) :
    d4BMPoincareSeedVerticalFirstJetSlice ⟨z.x, y, hy⟩ s p =
      d4BMPoincareSeedVerticalFirstJetSlice z s p := by
  rfl

theorem d4BM_poincareSeedVerticalFirstJetSlice_eq_at
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) (y : ℝ) (hy : 0 < y) :
    d4BMPoincareSeedVerticalFirstJetSlice z s p y =
      d4BMPoincareSeedVerticalFirstJet ⟨z.x, y, hy⟩ s p := by
  rfl

lemma d4BM_vertical_quadratic_base_le_four_mul
    (z : D4BMUpperHalfPlaneCoordinate) (p : D4BMPrimitiveIntegerPair)
    {y : ℝ} (hy : y ∈ Ioo (z.y / 2) (2 * z.y)) :
    d4BMPoincareQuadratic z p.pair ≤
      4 * (((p.pair.1 : ℝ) * y) ^ 2 +
        ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ 2) := by
  have hy0 : 0 < y := by linarith [z.y_pos, hy.1]
  have hySq : z.y ^ 2 ≤ 4 * y ^ 2 := by
    calc
      z.y ^ 2 ≤ (2 * y) ^ 2 :=
        (sq_le_sq₀ z.y_pos.le (mul_nonneg (by norm_num) hy0.le)).2 (by linarith [hy.1])
      _ = 4 * y ^ 2 := by ring
  unfold d4BMPoincareQuadratic
  nlinarith [sq_nonneg ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)),
    sq_nonneg (p.pair.1 : ℝ)]

lemma norm_d4BMPoincareSeed_vertical_le
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (p : D4BMPrimitiveIntegerPair) {y : ℝ}
    (hy : y ∈ Ioo (z.y / 2) (2 * z.y)) :
    ‖d4BMPoincareSeedVerticalSlice z P.s p y‖ ≤
      (2 ^ P.s.re * 4 ^ P.s.re) * ‖d4BMPoincareSeed z P.s p‖ := by
  have hy0 : 0 < y := by linarith [z.y_pos, hy.1]
  have hsigma : 0 ≤ P.s.re := by linarith [P.re_gt_one]
  let Qy : ℝ := ((p.pair.1 : ℝ) * y) ^ 2 +
    ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ 2
  have hQz := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hQy : 0 < Qy := by
    let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy0⟩
    have h := d4BMPoincareQuadratic_pos zy p.pair p.pair_ne_zero
    simpa [zy, Qy, d4BMPoincareQuadratic] using h
  have hquad : d4BMPoincareQuadratic z p.pair ≤ 4 * Qy := by
    simpa only [Qy] using d4BM_vertical_quadratic_base_le_four_mul z p hy
  have hrpow := d4BM_rpow_neg_le_of_le_mul hQz hQy (by norm_num : (0 : ℝ) < 4)
    hsigma hquad
  have hyrpow : y ^ P.s.re ≤ (2 * z.y) ^ P.s.re :=
    Real.rpow_le_rpow hy0.le hy.2.le hsigma
  rw [norm_d4BMPoincareSeedVerticalSlice z P.s p hy0,
    norm_d4BMPoincareSeed]
  change y ^ P.s.re * Qy ^ (-P.s.re) ≤
    (2 ^ P.s.re * 4 ^ P.s.re) *
      (z.y ^ P.s.re * d4BMPoincareQuadratic z p.pair ^ (-P.s.re))
  calc
    y ^ P.s.re * Qy ^ (-P.s.re) ≤
        (2 * z.y) ^ P.s.re *
          (4 ^ P.s.re * d4BMPoincareQuadratic z p.pair ^ (-P.s.re)) :=
      mul_le_mul hyrpow hrpow (Real.rpow_nonneg hQy.le _)
        (Real.rpow_nonneg (mul_nonneg (by norm_num) z.y_pos.le) _)
    _ = (2 ^ P.s.re * 4 ^ P.s.re) *
        (z.y ^ P.s.re * d4BMPoincareQuadratic z p.pair ^ (-P.s.re)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) z.y_pos.le]
      ring

lemma norm_d4BMPoincareSeedVerticalFirstJet_le
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    ‖d4BMPoincareSeedVerticalFirstJet z s p‖ ≤
      (3 * ‖s‖ / z.y) * ‖d4BMPoincareSeed z s p‖ := by
  let c : ℝ := p.pair.1
  let Q : ℝ := d4BMPoincareQuadratic z p.pair
  have hQ : 0 < Q := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hcQ : c ^ 2 * z.y ^ 2 ≤ Q := by
    dsimp only [Q, c, d4BMPoincareQuadratic]
    nlinarith [sq_nonneg ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ))]
  have hc : c ^ 2 * z.y / Q ≤ 1 / z.y := by
    apply (div_le_div_iff₀ hQ z.y_pos).2
    nlinarith
  have hterm1 : ‖s / (z.y : ℂ)‖ ≤ ‖s‖ / z.y := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos z.y_pos]
  have hterm2 :
      ‖2 * s * (c : ℂ) ^ 2 * (z.y : ℂ) / (Q : ℂ)‖ ≤ 2 * ‖s‖ / z.y := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ, abs_of_pos z.y_pos]
    norm_num
    calc
      2 * ‖s‖ * c ^ 2 * z.y / Q = 2 * ‖s‖ * (c ^ 2 * z.y / Q) := by ring
      _ ≤ 2 * ‖s‖ * (1 / z.y) :=
        mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num) (norm_nonneg s))
      _ = 2 * ‖s‖ / z.y := by ring
  unfold d4BMPoincareSeedVerticalFirstJet
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖s / (z.y : ℂ) -
        2 * s * (p.pair.1 : ℂ) ^ 2 * (z.y : ℂ) /
          (d4BMPoincareQuadratic z p.pair : ℂ)‖ ≤
      ‖s / (z.y : ℂ)‖ +
        ‖2 * s * (c : ℂ) ^ 2 * (z.y : ℂ) / (Q : ℂ)‖ := by
      dsimp only [c, Q]
      exact norm_sub_le _ _
    _ ≤ ‖s‖ / z.y + 2 * ‖s‖ / z.y := add_le_add hterm1 hterm2
    _ = 3 * ‖s‖ / z.y := by ring

lemma norm_d4BMPoincareSeedVerticalSecondJet_le
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    ‖d4BMPoincareSeedVerticalSecondJet z s p‖ ≤
      ((‖s‖ * ‖s - 1‖ + 2 * ‖s‖ * ‖1 + 2 * s‖ +
          4 * ‖s‖ * ‖s + 1‖) / z.y ^ 2) *
        ‖d4BMPoincareSeed z s p‖ := by
  let c : ℝ := p.pair.1
  let Q : ℝ := d4BMPoincareQuadratic z p.pair
  have hQ : 0 < Q := d4BMPoincareQuadratic_pos z p.pair p.pair_ne_zero
  have hy2 : 0 < z.y ^ 2 := sq_pos_of_pos z.y_pos
  have hcQ : c ^ 2 * z.y ^ 2 ≤ Q := by
    dsimp only [Q, c, d4BMPoincareQuadratic]
    nlinarith [sq_nonneg ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ))]
  have hc : c ^ 2 / Q ≤ 1 / z.y ^ 2 := by
    apply (div_le_div_iff₀ hQ hy2).2
    nlinarith
  have hc4 : c ^ 4 * z.y ^ 2 / Q ^ 2 ≤ 1 / z.y ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hQ) hy2).2
    have hnonneg : 0 ≤ c ^ 2 * z.y ^ 2 :=
      mul_nonneg (sq_nonneg c) (sq_nonneg z.y)
    have hsquare := mul_self_le_mul_self hnonneg hcQ
    nlinarith
  have habs4 : |c| ^ 4 = c ^ 4 := by
    calc
      |c| ^ 4 = (|c| ^ 2) ^ 2 := by ring
      _ = (c ^ 2) ^ 2 := by rw [sq_abs c]
      _ = c ^ 4 := by ring
  have hc4' : |c| ^ 4 * z.y ^ 2 / Q ^ 2 ≤ 1 / z.y ^ 2 := by
    rwa [habs4]
  have hterm1 : ‖s * (s - 1) / (z.y : ℂ) ^ 2‖ ≤
      (‖s‖ * ‖s - 1‖) / z.y ^ 2 := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos z.y_pos]
  have hterm2 :
      ‖2 * s * (1 + 2 * s) * (c : ℂ) ^ 2 / (Q : ℂ)‖ ≤
        (2 * ‖s‖ * ‖1 + 2 * s‖) / z.y ^ 2 := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ]
    norm_num
    calc
      2 * ‖s‖ * ‖1 + 2 * s‖ * c ^ 2 / Q =
          (2 * ‖s‖ * ‖1 + 2 * s‖) * (c ^ 2 / Q) := by ring
      _ ≤ (2 * ‖s‖ * ‖1 + 2 * s‖) * (1 / z.y ^ 2) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = (2 * ‖s‖ * ‖1 + 2 * s‖) / z.y ^ 2 := by ring
  have hterm3 :
      ‖4 * s * (s + 1) * (c : ℂ) ^ 4 * (z.y : ℂ) ^ 2 / (Q : ℂ) ^ 2‖ ≤
        (4 * ‖s‖ * ‖s + 1‖) / z.y ^ 2 := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow,
      norm_pow, norm_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ,
      abs_of_pos z.y_pos]
    norm_num
    calc
      4 * ‖s‖ * ‖s + 1‖ * |c| ^ 4 * z.y ^ 2 / Q ^ 2 =
          (4 * ‖s‖ * ‖s + 1‖) * (|c| ^ 4 * z.y ^ 2 / Q ^ 2) := by ring
      _ ≤ (4 * ‖s‖ * ‖s + 1‖) * (1 / z.y ^ 2) :=
        mul_le_mul_of_nonneg_left hc4' (by positivity)
      _ = (4 * ‖s‖ * ‖s + 1‖) / z.y ^ 2 := by ring
  unfold d4BMPoincareSeedVerticalSecondJet
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖s * (s - 1) / (z.y : ℂ) ^ 2 -
          2 * s * (1 + 2 * s) * (p.pair.1 : ℂ) ^ 2 /
            (d4BMPoincareQuadratic z p.pair : ℂ) +
        4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 4 * (z.y : ℂ) ^ 2 /
          (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2‖ ≤
      (‖s * (s - 1) / (z.y : ℂ) ^ 2‖ +
          ‖2 * s * (1 + 2 * s) * (c : ℂ) ^ 2 / (Q : ℂ)‖) +
        ‖4 * s * (s + 1) * (c : ℂ) ^ 4 * (z.y : ℂ) ^ 2 / (Q : ℂ) ^ 2‖ := by
      dsimp only [c, Q]
      calc
        ‖s * (s - 1) / (z.y : ℂ) ^ 2 -
              2 * s * (1 + 2 * s) * (p.pair.1 : ℂ) ^ 2 /
                (d4BMPoincareQuadratic z p.pair : ℂ) +
            4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 4 * (z.y : ℂ) ^ 2 /
              (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2‖ ≤
            ‖s * (s - 1) / (z.y : ℂ) ^ 2 -
              2 * s * (1 + 2 * s) * (p.pair.1 : ℂ) ^ 2 /
                (d4BMPoincareQuadratic z p.pair : ℂ)‖ +
              ‖4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 4 * (z.y : ℂ) ^ 2 /
                (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2‖ := norm_add_le _ _
        _ ≤ (‖s * (s - 1) / (z.y : ℂ) ^ 2‖ +
              ‖2 * s * (1 + 2 * s) * (p.pair.1 : ℂ) ^ 2 /
                (d4BMPoincareQuadratic z p.pair : ℂ)‖) +
              ‖4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 4 * (z.y : ℂ) ^ 2 /
                (d4BMPoincareQuadratic z p.pair : ℂ) ^ 2‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ((‖s‖ * ‖s - 1‖) / z.y ^ 2 +
          (2 * ‖s‖ * ‖1 + 2 * s‖) / z.y ^ 2) +
        (4 * ‖s‖ * ‖s + 1‖) / z.y ^ 2 :=
      add_le_add (add_le_add hterm1 hterm2) hterm3
    _ = (‖s‖ * ‖s - 1‖ + 2 * ‖s‖ * ‖1 + 2 * s‖ +
          4 * ‖s‖ * ‖s + 1‖) / z.y ^ 2 := by ring

def d4BMVerticalSecondJetNormConstant (s : ℂ) : ℝ :=
  ‖s‖ * ‖s - 1‖ + 2 * ‖s‖ * ‖1 + 2 * s‖ + 4 * ‖s‖ * ‖s + 1‖

lemma d4BMVerticalSecondJetNormConstant_nonneg (s : ℂ) :
    0 ≤ d4BMVerticalSecondJetNormConstant s := by
  unfold d4BMVerticalSecondJetNormConstant
  positivity

def d4BMPoincareSeedVerticalSecondJetSlice
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) (y : ℝ) : ℂ :=
  (s * (s - 1) / (y : ℂ) ^ 2 -
      2 * s * (1 + 2 * s) * (p.pair.1 : ℂ) ^ 2 /
        ((((p.pair.1 : ℝ) * y) ^ 2 +
          ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ 2 : ℝ) : ℂ) +
      4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 4 * (y : ℂ) ^ 2 /
        ((((p.pair.1 : ℝ) * y) ^ 2 +
          ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ 2 : ℝ) : ℂ) ^ 2) *
    d4BMPoincareSeedVerticalSlice z s p y

theorem d4BM_poincareSeedVerticalSecondJetSlice_at_height
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeedVerticalSecondJetSlice z s p z.y =
      d4BMPoincareSeedVerticalSecondJet z s p := by
  rfl

theorem d4BM_poincareSeedVerticalSecondJetSlice_eq_at
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) (y : ℝ) (hy : 0 < y) :
    d4BMPoincareSeedVerticalSecondJetSlice z s p y =
      d4BMPoincareSeedVerticalSecondJet ⟨z.x, y, hy⟩ s p := by
  rfl

lemma norm_d4BMPoincareSeedVerticalFirstJetSlice_local_le
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (p : D4BMPrimitiveIntegerPair) {y : ℝ}
    (hy : y ∈ Ioo (z.y / 2) (2 * z.y)) :
    ‖d4BMPoincareSeedVerticalFirstJetSlice z P.s p y‖ ≤
      (6 * ‖P.s‖ / z.y) * (2 ^ P.s.re * 4 ^ P.s.re) *
        ‖d4BMPoincareSeed z P.s p‖ := by
  have hy0 : 0 < y := by linarith [z.y_pos, hy.1]
  let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy0⟩
  have hvalue : d4BMPoincareSeedVerticalFirstJetSlice z P.s p y =
      d4BMPoincareSeedVerticalFirstJet zy P.s p := by rfl
  have hinv : 1 / y ≤ 2 / z.y := by
    apply (div_le_div_iff₀ hy0 z.y_pos).2
    linarith [hy.1]
  have hcoef : 3 * ‖P.s‖ / y ≤ 6 * ‖P.s‖ / z.y := by
    calc
      3 * ‖P.s‖ / y = (3 * ‖P.s‖) * (1 / y) := by ring
      _ ≤ (3 * ‖P.s‖) * (2 / z.y) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 6 * ‖P.s‖ / z.y := by ring
  rw [hvalue]
  calc
    ‖d4BMPoincareSeedVerticalFirstJet zy P.s p‖ ≤
        (3 * ‖P.s‖ / y) * ‖d4BMPoincareSeed zy P.s p‖ :=
      norm_d4BMPoincareSeedVerticalFirstJet_le zy P.s p
    _ ≤ (6 * ‖P.s‖ / z.y) *
        ‖d4BMPoincareSeedVerticalSlice z P.s p y‖ := by
      apply mul_le_mul hcoef le_rfl (norm_nonneg _)
      exact div_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) z.y_pos.le
    _ ≤ (6 * ‖P.s‖ / z.y) *
        ((2 ^ P.s.re * 4 ^ P.s.re) * ‖d4BMPoincareSeed z P.s p‖) :=
      mul_le_mul_of_nonneg_left (norm_d4BMPoincareSeed_vertical_le z P p hy)
        (div_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) z.y_pos.le)
    _ = (6 * ‖P.s‖ / z.y) * (2 ^ P.s.re * 4 ^ P.s.re) *
        ‖d4BMPoincareSeed z P.s p‖ := by ring

lemma norm_d4BMPoincareSeedVerticalSecondJetSlice_local_le
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (p : D4BMPrimitiveIntegerPair) {y : ℝ}
    (hy : y ∈ Ioo (z.y / 2) (2 * z.y)) :
    ‖d4BMPoincareSeedVerticalSecondJetSlice z P.s p y‖ ≤
      (4 * d4BMVerticalSecondJetNormConstant P.s / z.y ^ 2) *
        (2 ^ P.s.re * 4 ^ P.s.re) * ‖d4BMPoincareSeed z P.s p‖ := by
  have hy0 : 0 < y := by linarith [z.y_pos, hy.1]
  let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy0⟩
  have hySq : z.y ^ 2 ≤ 4 * y ^ 2 := by
    calc
      z.y ^ 2 ≤ (2 * y) ^ 2 :=
        (sq_le_sq₀ z.y_pos.le (mul_nonneg (by norm_num) hy0.le)).2 (by linarith [hy.1])
      _ = 4 * y ^ 2 := by ring
  have hinvSq : 1 / y ^ 2 ≤ 4 / z.y ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hy0) (sq_pos_of_pos z.y_pos)).2
    nlinarith
  have hCnonneg := d4BMVerticalSecondJetNormConstant_nonneg P.s
  have hcoef : d4BMVerticalSecondJetNormConstant P.s / y ^ 2 ≤
      4 * d4BMVerticalSecondJetNormConstant P.s / z.y ^ 2 := by
    calc
      d4BMVerticalSecondJetNormConstant P.s / y ^ 2 =
          d4BMVerticalSecondJetNormConstant P.s * (1 / y ^ 2) := by ring
      _ ≤ d4BMVerticalSecondJetNormConstant P.s * (4 / z.y ^ 2) :=
        mul_le_mul_of_nonneg_left hinvSq hCnonneg
      _ = 4 * d4BMVerticalSecondJetNormConstant P.s / z.y ^ 2 := by ring
  have hvalue : d4BMPoincareSeedVerticalSecondJetSlice z P.s p y =
      d4BMPoincareSeedVerticalSecondJet zy P.s p := by rfl
  rw [hvalue]
  calc
    ‖d4BMPoincareSeedVerticalSecondJet zy P.s p‖ ≤
        (d4BMVerticalSecondJetNormConstant P.s / y ^ 2) *
          ‖d4BMPoincareSeed zy P.s p‖ := by
      simpa only [d4BMVerticalSecondJetNormConstant] using
        norm_d4BMPoincareSeedVerticalSecondJet_le zy P.s p
    _ ≤ (4 * d4BMVerticalSecondJetNormConstant P.s / z.y ^ 2) *
        ‖d4BMPoincareSeedVerticalSlice z P.s p y‖ := by
      apply mul_le_mul hcoef le_rfl (norm_nonneg _)
      exact div_nonneg (mul_nonneg (by norm_num) hCnonneg) (sq_nonneg _)
    _ ≤ (4 * d4BMVerticalSecondJetNormConstant P.s / z.y ^ 2) *
        ((2 ^ P.s.re * 4 ^ P.s.re) * ‖d4BMPoincareSeed z P.s p‖) :=
      mul_le_mul_of_nonneg_left (norm_d4BMPoincareSeed_vertical_le z P p hy)
        (div_nonneg (mul_nonneg (by norm_num) hCnonneg) (sq_nonneg _))
    _ = (4 * d4BMVerticalSecondJetNormConstant P.s / z.y ^ 2) *
        (2 ^ P.s.re * 4 ^ P.s.re) * ‖d4BMPoincareSeed z P.s p‖ := by ring

def d4BMVerticalFirstJetLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (p : D4BMPrimitiveIntegerPair) : ℝ :=
  ((6 * ‖P.s‖ / z.y) * (2 ^ P.s.re * 4 ^ P.s.re)) *
    ‖d4BMPoincareSeed z P.s p‖

def d4BMVerticalSecondJetLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (p : D4BMPrimitiveIntegerPair) : ℝ :=
  ((4 * d4BMVerticalSecondJetNormConstant P.s / z.y ^ 2) *
      (2 ^ P.s.re * 4 ^ P.s.re)) * ‖d4BMPoincareSeed z P.s p‖

lemma summable_d4BMVerticalFirstJetLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable (d4BMVerticalFirstJetLocalMajorant z P) := by
  exact (summable_d4BMPoincareSeed z P).norm.mul_left _

lemma summable_d4BMVerticalSecondJetLocalMajorant
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable (d4BMVerticalSecondJetLocalMajorant z P) := by
  exact (summable_d4BMPoincareSeed z P).norm.mul_left _

def d4BMRawPoincareVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
    d4BMPoincareSeedVerticalSlice z P.s p y

def d4BMRawPoincareVerticalFirstJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
    d4BMPoincareSeedVerticalFirstJet z P.s p

def d4BMRawPoincareVerticalFirstJetSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
    d4BMPoincareSeedVerticalFirstJetSlice z P.s p y

def d4BMRawPoincareVerticalSecondJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : D4BMPrimitiveIntegerPair,
    d4BMPoincareSeedVerticalSecondJet z P.s p

theorem d4BMRawPoincareVerticalSlice_at_height
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMRawPoincareVerticalSlice z P z.y =
      d4BMRawEisensteinPoincareSeries z P := by
  rfl

theorem d4BMRawPoincareVerticalFirstJetSlice_at_height
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMRawPoincareVerticalFirstJetSlice z P z.y =
      d4BMRawPoincareVerticalFirstJet z P := by
  rfl

theorem hasDerivAt_tsum_d4BMPoincareSeed_vertical
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun y : ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedVerticalSlice z P.s p y)
      (∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedVerticalFirstJet z P.s p) z.y := by
  let t : Set ℝ := Ioo (z.y / 2) (2 * z.y)
  let g : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p y =>
    d4BMPoincareSeedVerticalSlice z P.s p y
  let g' : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p y =>
    d4BMPoincareSeedVerticalFirstJetSlice z P.s p y
  let M := d4BMVerticalFirstJetLocalMajorant z P
  have hM : Summable M := summable_d4BMVerticalFirstJetLocalMajorant z P
  have hopen : IsOpen t := isOpen_Ioo
  have hconn : IsPreconnected t := isPreconnected_Ioo
  have hderiv : ∀ p, ∀ y ∈ t, HasDerivAt (g p) (g' p y) y := by
    intro p y hy
    have hy0 : 0 < y := by linarith [z.y_pos, hy.1]
    let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy0⟩
    have h := hasDerivAt_d4BMPoincareSeed_vertical zy P.s p
    rw [d4BM_poincareSeedVerticalSlice_rebase z P.s p y hy0] at h
    rw [← d4BM_poincareSeedVerticalFirstJetSlice_eq_at z P.s p y hy0] at h
    simpa only [g, g'] using h
  have hbound : ∀ p, ∀ y ∈ t, ‖g' p y‖ ≤ M p := by
    intro p y hy
    simpa [g', M, d4BMVerticalFirstJetLocalMajorant, mul_assoc] using
      norm_d4BMPoincareSeedVerticalFirstJetSlice_local_le z P p hy
  have hymem : z.y ∈ t := by
    dsimp only [t]
    constructor <;> linarith [z.y_pos]
  have hbase : Summable fun p => g p z.y := by
    simpa only [g, d4BM_poincareSeedVerticalSlice_at_height] using
      summable_d4BMPoincareSeed z P
  have h := hasDerivAt_tsum_of_isPreconnected hM hopen hconn hderiv hbound
    hymem hbase hymem
  simpa only [g, g', d4BM_poincareSeedVerticalFirstJetSlice_at_height] using h

theorem hasDerivAt_tsum_d4BMPoincareSeedVerticalFirstJet_vertical
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun y : ℝ => ∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedVerticalFirstJetSlice z P.s p y)
      (∑' p : D4BMPrimitiveIntegerPair,
        d4BMPoincareSeedVerticalSecondJet z P.s p) z.y := by
  let t : Set ℝ := Ioo (z.y / 2) (2 * z.y)
  let g : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p y =>
    d4BMPoincareSeedVerticalFirstJetSlice z P.s p y
  let g' : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p y =>
    d4BMPoincareSeedVerticalSecondJetSlice z P.s p y
  let M := d4BMVerticalSecondJetLocalMajorant z P
  have hM : Summable M := summable_d4BMVerticalSecondJetLocalMajorant z P
  have hopen : IsOpen t := isOpen_Ioo
  have hconn : IsPreconnected t := isPreconnected_Ioo
  have hderiv : ∀ p, ∀ y ∈ t, HasDerivAt (g p) (g' p y) y := by
    intro p y hy
    have hy0 : 0 < y := by linarith [z.y_pos, hy.1]
    let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy0⟩
    have h := hasDerivAt_d4BMPoincareSeedVerticalFirstJetSlice zy P.s p
    rw [d4BM_poincareSeedVerticalFirstJetSlice_rebase z P.s p y hy0] at h
    rw [← d4BM_poincareSeedVerticalSecondJetSlice_eq_at z P.s p y hy0] at h
    simpa only [g, g'] using h
  have hbound : ∀ p, ∀ y ∈ t, ‖g' p y‖ ≤ M p := by
    intro p y hy
    have h := norm_d4BMPoincareSeedVerticalSecondJetSlice_local_le z P p hy
    simpa [g', M, d4BMVerticalSecondJetLocalMajorant, mul_assoc] using h
  have hymem : z.y ∈ t := by
    dsimp only [t]
    constructor <;> linarith [z.y_pos]
  have hbase : Summable fun p => g p z.y := by
    have hbaseMaj := (summable_d4BMPoincareSeed z P).norm.mul_left
      (3 * ‖P.s‖ / z.y)
    refine Summable.of_norm_bounded hbaseMaj ?_
    intro p
    simpa only [g, d4BM_poincareSeedVerticalFirstJetSlice_at_height] using
      norm_d4BMPoincareSeedVerticalFirstJet_le z P.s p
  have h := hasDerivAt_tsum_of_isPreconnected hM hopen hconn hderiv hbound
    hymem hbase hymem
  simpa only [g, g', d4BM_poincareSeedVerticalSecondJetSlice_at_height] using h

theorem hasDerivAt_d4BMRawPoincareVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt (d4BMRawPoincareVerticalSlice z P)
      (d4BMRawPoincareVerticalFirstJet z P) z.y := by
  have h := (hasDerivAt_tsum_d4BMPoincareSeed_vertical z P).const_mul (1 / 2 : ℂ)
  change HasDerivAt (fun y => d4BMRawPoincareVerticalSlice z P y)
    (d4BMRawPoincareVerticalFirstJet z P) z.y
  simpa [d4BMRawPoincareVerticalSlice, d4BMRawPoincareVerticalFirstJet] using h

theorem hasDerivAt_d4BMRawPoincareVerticalFirstJetSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt (d4BMRawPoincareVerticalFirstJetSlice z P)
      (d4BMRawPoincareVerticalSecondJet z P) z.y := by
  have h :=
    (hasDerivAt_tsum_d4BMPoincareSeedVerticalFirstJet_vertical z P).const_mul
      (1 / 2 : ℂ)
  change HasDerivAt (fun y => d4BMRawPoincareVerticalFirstJetSlice z P y)
    (d4BMRawPoincareVerticalSecondJet z P) z.y
  simpa [d4BMRawPoincareVerticalFirstJetSlice, d4BMRawPoincareVerticalSecondJet]
    using h

theorem summable_d4BMPoincareSeedHorizontalSecondJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedHorizontalSecondJet z P.s p := by
  let K : ℝ := (2 * ‖P.s‖ + 4 * ‖P.s‖ * ‖P.s + 1‖) / z.y ^ 2
  have hK : Summable fun p : D4BMPrimitiveIntegerPair =>
      K * ‖d4BMPoincareSeed z P.s p‖ :=
    (summable_d4BMPoincareSeed z P).norm.mul_left K
  refine Summable.of_norm_bounded hK ?_
  intro p
  exact norm_d4BMPoincareSeedHorizontalSecondJet_le z P.s p

theorem summable_d4BMPoincareSeedVerticalSecondJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable fun p : D4BMPrimitiveIntegerPair =>
      d4BMPoincareSeedVerticalSecondJet z P.s p := by
  let K : ℝ := d4BMVerticalSecondJetNormConstant P.s / z.y ^ 2
  have hK : Summable fun p : D4BMPrimitiveIntegerPair =>
      K * ‖d4BMPoincareSeed z P.s p‖ :=
    (summable_d4BMPoincareSeed z P).norm.mul_left K
  refine Summable.of_norm_bounded hK ?_
  intro p
  simpa only [K, d4BMVerticalSecondJetNormConstant] using
    norm_d4BMPoincareSeedVerticalSecondJet_le z P.s p

theorem d4BM_rawEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    (z.y : ℂ) ^ 2 *
        (d4BMRawPoincareHorizontalSecondJet z P +
          d4BMRawPoincareVerticalSecondJet z P) =
      P.s * (P.s - 1) * d4BMRawEisensteinPoincareSeries z P := by
  have hH := summable_d4BMPoincareSeedHorizontalSecondJet z P
  have hV := summable_d4BMPoincareSeedVerticalSecondJet z P
  have hsum :
      (z.y : ℂ) ^ 2 *
          ((∑' p : D4BMPrimitiveIntegerPair,
              d4BMPoincareSeedHorizontalSecondJet z P.s p) +
            ∑' p : D4BMPrimitiveIntegerPair,
              d4BMPoincareSeedVerticalSecondJet z P.s p) =
        P.s * (P.s - 1) *
          ∑' p : D4BMPrimitiveIntegerPair, d4BMPoincareSeed z P.s p := by
    calc
      (z.y : ℂ) ^ 2 *
          ((∑' p : D4BMPrimitiveIntegerPair,
              d4BMPoincareSeedHorizontalSecondJet z P.s p) +
            ∑' p : D4BMPrimitiveIntegerPair,
              d4BMPoincareSeedVerticalSecondJet z P.s p) =
          (z.y : ℂ) ^ 2 *
            ∑' p : D4BMPrimitiveIntegerPair,
              (d4BMPoincareSeedHorizontalSecondJet z P.s p +
                d4BMPoincareSeedVerticalSecondJet z P.s p) := by
        rw [hH.tsum_add hV]
      _ = ∑' p : D4BMPrimitiveIntegerPair,
          (z.y : ℂ) ^ 2 *
            (d4BMPoincareSeedHorizontalSecondJet z P.s p +
              d4BMPoincareSeedVerticalSecondJet z P.s p) :=
        (tsum_mul_left).symm
      _ = ∑' p : D4BMPrimitiveIntegerPair,
          P.s * (P.s - 1) * d4BMPoincareSeed z P.s p := by
        apply tsum_congr
        intro p
        exact d4BM_poincareSeed_formalHyperbolicLaplacian_eq_eigenvalue z P.s p
      _ = P.s * (P.s - 1) *
          ∑' p : D4BMPrimitiveIntegerPair, d4BMPoincareSeed z P.s p :=
        tsum_mul_left
  unfold d4BMRawPoincareHorizontalSecondJet d4BMRawPoincareVerticalSecondJet
    d4BMRawEisensteinPoincareSeries
  calc
    (z.y : ℂ) ^ 2 *
        ((1 / 2 : ℂ) *
            (∑' p : D4BMPrimitiveIntegerPair,
              d4BMPoincareSeedHorizontalSecondJet z P.s p) +
          (1 / 2 : ℂ) *
            ∑' p : D4BMPrimitiveIntegerPair,
              d4BMPoincareSeedVerticalSecondJet z P.s p) =
      (1 / 2 : ℂ) *
        ((z.y : ℂ) ^ 2 *
          ((∑' p : D4BMPrimitiveIntegerPair,
              d4BMPoincareSeedHorizontalSecondJet z P.s p) +
            ∑' p : D4BMPrimitiveIntegerPair,
              d4BMPoincareSeedVerticalSecondJet z P.s p)) := by ring
    _ = (1 / 2 : ℂ) *
        (P.s * (P.s - 1) *
          ∑' p : D4BMPrimitiveIntegerPair, d4BMPoincareSeed z P.s p) := by
      rw [hsum]
    _ = P.s * (P.s - 1) *
        ((1 / 2 : ℂ) *
          ∑' p : D4BMPrimitiveIntegerPair, d4BMPoincareSeed z P.s p) := by ring

def d4BMCompletedPoincareHorizontalFirstJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  reflectedCompletedLambda (2 * P.s) * d4BMRawPoincareHorizontalFirstJet z P

def d4BMCompletedPoincareHorizontalSecondJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  reflectedCompletedLambda (2 * P.s) * d4BMRawPoincareHorizontalSecondJet z P

def d4BMCompletedPoincareVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  reflectedCompletedLambda (2 * P.s) * d4BMRawPoincareVerticalSlice z P y

def d4BMCompletedPoincareVerticalFirstJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  reflectedCompletedLambda (2 * P.s) * d4BMRawPoincareVerticalFirstJet z P

def d4BMCompletedPoincareVerticalFirstJetSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  reflectedCompletedLambda (2 * P.s) * d4BMRawPoincareVerticalFirstJetSlice z P y

def d4BMCompletedPoincareVerticalSecondJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  reflectedCompletedLambda (2 * P.s) * d4BMRawPoincareVerticalSecondJet z P

theorem d4BMCompletedPoincareVerticalSlice_at_height
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareVerticalSlice z P z.y =
      d4BMCompletedEisensteinPoincareSeries z P := by
  rfl

theorem d4BMCompletedPoincareVerticalFirstJetSlice_at_height
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMCompletedPoincareVerticalFirstJetSlice z P z.y =
      d4BMCompletedPoincareVerticalFirstJet z P := by
  rfl

theorem hasDerivAt_d4BMCompletedEisensteinPoincareSeries_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => d4BMCompletedEisensteinPoincareSeries
        (d4BMHorizontalCoordinate z x) P)
      (d4BMCompletedPoincareHorizontalFirstJet z P) z.x := by
  have h := (hasDerivAt_d4BMRawEisensteinPoincareSeries_horizontal z P).const_mul
    (reflectedCompletedLambda (2 * P.s))
  simpa [d4BMCompletedEisensteinPoincareSeries,
    d4BMCompletedPoincareHorizontalFirstJet] using h

theorem hasDerivAt_d4BMCompletedPoincareHorizontalFirstJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => d4BMCompletedPoincareHorizontalFirstJet
        (d4BMHorizontalCoordinate z x) P)
      (d4BMCompletedPoincareHorizontalSecondJet z P) z.x := by
  have h := (hasDerivAt_d4BMRawPoincareHorizontalFirstJet_horizontal z P).const_mul
    (reflectedCompletedLambda (2 * P.s))
  simpa [d4BMCompletedPoincareHorizontalFirstJet,
    d4BMCompletedPoincareHorizontalSecondJet] using h

theorem hasDerivAt_d4BMCompletedPoincareVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt (d4BMCompletedPoincareVerticalSlice z P)
      (d4BMCompletedPoincareVerticalFirstJet z P) z.y := by
  have h := (hasDerivAt_d4BMRawPoincareVerticalSlice z P).const_mul
    (reflectedCompletedLambda (2 * P.s))
  change HasDerivAt (fun y => d4BMCompletedPoincareVerticalSlice z P y)
    (d4BMCompletedPoincareVerticalFirstJet z P) z.y
  simpa [d4BMCompletedPoincareVerticalSlice,
    d4BMCompletedPoincareVerticalFirstJet] using h

theorem hasDerivAt_d4BMCompletedPoincareVerticalFirstJetSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt (d4BMCompletedPoincareVerticalFirstJetSlice z P)
      (d4BMCompletedPoincareVerticalSecondJet z P) z.y := by
  have h := (hasDerivAt_d4BMRawPoincareVerticalFirstJetSlice z P).const_mul
    (reflectedCompletedLambda (2 * P.s))
  change HasDerivAt (fun y => d4BMCompletedPoincareVerticalFirstJetSlice z P y)
    (d4BMCompletedPoincareVerticalSecondJet z P) z.y
  simpa [d4BMCompletedPoincareVerticalFirstJetSlice,
    d4BMCompletedPoincareVerticalSecondJet] using h

theorem d4BM_completedEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    (z.y : ℂ) ^ 2 *
        (d4BMCompletedPoincareHorizontalSecondJet z P +
          d4BMCompletedPoincareVerticalSecondJet z P) =
      P.s * (P.s - 1) * d4BMCompletedEisensteinPoincareSeries z P := by
  rw [d4BMCompletedPoincareHorizontalSecondJet,
    d4BMCompletedPoincareVerticalSecondJet,
    d4BMCompletedEisensteinPoincareSeries]
  have hraw :=
    d4BM_rawEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue z P
  calc
    (z.y : ℂ) ^ 2 *
        (reflectedCompletedLambda (2 * P.s) * d4BMRawPoincareHorizontalSecondJet z P +
          reflectedCompletedLambda (2 * P.s) * d4BMRawPoincareVerticalSecondJet z P) =
      reflectedCompletedLambda (2 * P.s) *
        ((z.y : ℂ) ^ 2 *
          (d4BMRawPoincareHorizontalSecondJet z P +
            d4BMRawPoincareVerticalSecondJet z P)) := by ring
    _ = reflectedCompletedLambda (2 * P.s) *
        (P.s * (P.s - 1) * d4BMRawEisensteinPoincareSeries z P) := by rw [hraw]
    _ = P.s * (P.s - 1) *
        (reflectedCompletedLambda (2 * P.s) *
          d4BMRawEisensteinPoincareSeries z P) := by ring

theorem d4BM_completedEisensteinPoincareSeries_actualSecondDerivative_eigenEquation
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
        (fun x : ℝ => d4BMCompletedEisensteinPoincareSeries
          (d4BMHorizontalCoordinate z x) P)
        (d4BMCompletedPoincareHorizontalFirstJet z P) z.x ∧
      HasDerivAt
        (fun x : ℝ => d4BMCompletedPoincareHorizontalFirstJet
          (d4BMHorizontalCoordinate z x) P)
        (d4BMCompletedPoincareHorizontalSecondJet z P) z.x ∧
      HasDerivAt (d4BMCompletedPoincareVerticalSlice z P)
        (d4BMCompletedPoincareVerticalFirstJet z P) z.y ∧
      HasDerivAt (d4BMCompletedPoincareVerticalFirstJetSlice z P)
        (d4BMCompletedPoincareVerticalSecondJet z P) z.y ∧
      (z.y : ℂ) ^ 2 *
          (d4BMCompletedPoincareHorizontalSecondJet z P +
            d4BMCompletedPoincareVerticalSecondJet z P) =
        P.s * (P.s - 1) * d4BMCompletedEisensteinPoincareSeries z P := by
  exact ⟨hasDerivAt_d4BMCompletedEisensteinPoincareSeries_horizontal z P,
    hasDerivAt_d4BMCompletedPoincareHorizontalFirstJet_horizontal z P,
    hasDerivAt_d4BMCompletedPoincareVerticalSlice z P,
    hasDerivAt_d4BMCompletedPoincareVerticalFirstJetSlice z P,
    d4BM_completedEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue z P⟩

structure D4BMEisensteinCenteredAbsoluteConvergenceParameter where
  u : ℂ
  re_gt_half : 1 / 2 < u.re

def D4BMEisensteinCenteredAbsoluteConvergenceParameter.toAbsolute
    (U : D4BMEisensteinCenteredAbsoluteConvergenceParameter) :
    D4BMEisensteinAbsoluteConvergenceParameter where
  s := 1 / 2 + U.u
  re_gt_one := by
    norm_num
    linarith [U.re_gt_half]

theorem d4BM_completedEisensteinPoincareSeries_geometricEigenvalue_centered
    (z : D4BMUpperHalfPlaneCoordinate)
    (U : D4BMEisensteinCenteredAbsoluteConvergenceParameter) :
    (z.y : ℂ) ^ 2 *
        (d4BMCompletedPoincareHorizontalSecondJet z U.toAbsolute +
          d4BMCompletedPoincareVerticalSecondJet z U.toAbsolute) =
      thetaCuspHawkingEisensteinGeometricEigenvalue U.u *
        d4BMCompletedEisensteinPoincareSeries z U.toAbsolute := by
  rw [d4BM_completedEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue]
  unfold D4BMEisensteinCenteredAbsoluteConvergenceParameter.toAbsolute
    thetaCuspHawkingEisensteinGeometricEigenvalue
  ring

end
end RHTower
