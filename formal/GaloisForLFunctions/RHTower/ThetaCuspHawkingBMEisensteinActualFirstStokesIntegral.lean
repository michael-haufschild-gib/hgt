import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualFirstStokesDefect
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Literal truncated-domain first Green--Stokes identity

Corpus conjecture C-A.9t3c supplies the missing two-dimensional integration step after the actual
pointwise current and its complete cusp finite part were closed.  The first new obstruction is
analytic: the corpus proved genuine vertical second derivatives but had not packaged their local
normal convergence as continuity, which is required by interval-integral FTC.

RH chain:

`literal actual truncated Green/Stokes -> actual balanced BM ++- coefficient -> negative BM leg ->
conserved left-QNM projection -> HC94 -> RH`.
-/

open Complex Real Filter Set Topology MeasureTheory
open scoped Interval

namespace RHTower
noncomputable section

/-- Total vertical second-jet slice of the completed actual Poincare series. -/
def d4BMCompletedPoincareVerticalSecondJetSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  reflectedCompletedLambda (2 * P.s) * ((1 / 2 : ℂ) *
    ∑' p : D4BMPrimitiveIntegerPair,
      d4BMPoincareSeedVerticalSecondJetSlice z P.s p y)

theorem d4BMCompletedPoincareVerticalSecondJetSlice_eq_at
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    {y : ℝ} (hy : 0 < y) :
    d4BMCompletedPoincareVerticalSecondJetSlice z P y =
      d4BMCompletedPoincareVerticalSecondJet ⟨z.x, y, hy⟩ P := by
  unfold d4BMCompletedPoincareVerticalSecondJetSlice
    d4BMCompletedPoincareVerticalSecondJet
    d4BMRawPoincareVerticalSecondJet
  congr 2

/-- Every seed's vertical second-jet slice is continuous on positive height. -/
theorem continuousOn_d4BMPoincareSeedVerticalSecondJetSlice
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    ContinuousOn (d4BMPoincareSeedVerticalSecondJetSlice z s p) (Ioi 0) := by
  intro y hy
  have hy0 : 0 < y := hy
  have hseed : ContinuousAt (d4BMPoincareSeedVerticalSlice z s p) y := by
    let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy0⟩
    have h := (hasDerivAt_d4BMPoincareSeed_vertical zy s p).continuousAt
    rw [d4BM_poincareSeedVerticalSlice_rebase z s p y hy0] at h
    exact h
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy0.ne'
  have hQpos : 0 <
      ((p.pair.1 : ℝ) * y) ^ 2 +
        ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ 2 := by
    change 0 < d4BMPoincareQuadratic ⟨z.x, y, hy0⟩ p.pair
    exact d4BMPoincareQuadratic_pos ⟨z.x, y, hy0⟩ p.pair p.pair_ne_zero
  have hQC :
      (((((p.pair.1 : ℝ) * y) ^ 2 +
        ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hQpos.ne'
  unfold d4BMPoincareSeedVerticalSecondJetSlice
  let qC : ℝ → ℂ := fun q =>
    (((p.pair.1 : ℝ) * q) ^ 2 +
      ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ 2 : ℝ)
  have hqC : ContinuousAt qC y := by
    dsimp only [qC]
    fun_prop
  have hqCne : qC y ≠ 0 := by
    simpa [qC] using hQC
  have hyfun : ContinuousAt (fun q : ℝ => (q : ℂ)) y :=
    Complex.continuous_ofReal.continuousAt
  have hfirst : ContinuousAt
      (fun q : ℝ => s * (s - 1) / (q : ℂ) ^ 2) y :=
    continuousAt_const.div (hyfun.pow 2) (pow_ne_zero 2 hyC)
  have hsecond : ContinuousAt
      (fun q : ℝ =>
        2 * s * (1 + 2 * s) * (p.pair.1 : ℂ) ^ 2 / qC q) y :=
    continuousAt_const.div hqC hqCne
  have hthird : ContinuousAt
      (fun q : ℝ =>
        4 * s * (s + 1) * (p.pair.1 : ℂ) ^ 4 * (q : ℂ) ^ 2 /
          qC q ^ 2) y :=
    (continuousAt_const.mul (hyfun.pow 2)).div (hqC.pow 2)
      (pow_ne_zero 2 hqCne)
  exact (((hfirst.sub hsecond).add hthird).mul hseed).continuousWithinAt

/-- Local normal convergence upgrades the completed vertical second-jet sum to a continuous
positive-height slice. -/
theorem continuousOn_d4BMCompletedPoincareVerticalSecondJetSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    ContinuousOn (d4BMCompletedPoincareVerticalSecondJetSlice z P) (Ioi 0) := by
  intro y hy
  have hy0 : 0 < y := hy
  let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy0⟩
  let t : Set ℝ := Ioo (y / 2) (2 * y)
  let g : D4BMPrimitiveIntegerPair → ℝ → ℂ := fun p q =>
    d4BMPoincareSeedVerticalSecondJetSlice z P.s p q
  let M := d4BMVerticalSecondJetLocalMajorant zy P
  have hM : Summable M := summable_d4BMVerticalSecondJetLocalMajorant zy P
  have htpos : t ⊆ Ioi (0 : ℝ) := by
    intro q hq
    change 0 < q
    dsimp only [t] at hq
    exact (half_pos hy0).trans hq.1
  have hterm : ∀ p, ContinuousOn (g p) t := by
    intro p
    simpa only [g] using
      (continuousOn_d4BMPoincareSeedVerticalSecondJetSlice z P.s p).mono htpos
  have hbound : ∀ p, ∀ q ∈ t, ‖g p q‖ ≤ M p := by
    intro p q hq
    have h := norm_d4BMPoincareSeedVerticalSecondJetSlice_local_le zy P p hq
    have hrebase :
        d4BMPoincareSeedVerticalSecondJetSlice zy P.s p =
          d4BMPoincareSeedVerticalSecondJetSlice z P.s p := by
      rfl
    rw [hrebase] at h
    simpa [g, M, zy, d4BMVerticalSecondJetLocalMajorant, mul_assoc] using h
  have hsumCont : ContinuousOn (fun q => ∑' p, g p q) t :=
    continuousOn_tsum hterm hM hbound
  have hymem : y ∈ t := by
    dsimp only [t]
    constructor <;> linarith
  have hsumAt : ContinuousAt (fun q => ∑' p, g p q) y :=
    hsumCont.continuousAt (isOpen_Ioo.mem_nhds hymem)
  have hhalf : ContinuousAt (fun q => (1 / 2 : ℂ) * ∑' p, g p q) y :=
    continuousAt_const.mul hsumAt
  have hscaled : ContinuousAt
      (fun q => reflectedCompletedLambda (2 * P.s) * ((1 / 2 : ℂ) * ∑' p, g p q)) y :=
    continuousAt_const.mul hhalf
  have hfinal : ContinuousAt (d4BMCompletedPoincareVerticalSecondJetSlice z P) y := by
    dsimp only [g] at hscaled
    change ContinuousAt
      (fun q => reflectedCompletedLambda (2 * P.s) * ((1 / 2 : ℂ) *
        ∑' p : D4BMPrimitiveIntegerPair,
          d4BMPoincareSeedVerticalSecondJetSlice z P.s p q)) y
    exact hscaled
  exact hfinal.continuousWithinAt

theorem hasDerivAt_d4BMCompletedPoincareVerticalSlice_at_positive
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (d4BMCompletedPoincareVerticalSlice z P)
      (d4BMCompletedPoincareVerticalFirstJetSlice z P y) y := by
  let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy⟩
  have h := hasDerivAt_d4BMCompletedPoincareVerticalSlice zy P
  have hfun : d4BMCompletedPoincareVerticalSlice zy P =
      d4BMCompletedPoincareVerticalSlice z P := by
    funext q
    rfl
  have hder : d4BMCompletedPoincareVerticalFirstJet zy P =
      d4BMCompletedPoincareVerticalFirstJetSlice z P y := by
    rfl
  rw [hfun, hder] at h
  simpa [zy] using h

theorem hasDerivAt_d4BMCompletedPoincareVerticalFirstJetSlice_at_positive
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (d4BMCompletedPoincareVerticalFirstJetSlice z P)
      (d4BMCompletedPoincareVerticalSecondJetSlice z P y) y := by
  let zy : D4BMUpperHalfPlaneCoordinate := ⟨z.x, y, hy⟩
  have h := hasDerivAt_d4BMCompletedPoincareVerticalFirstJetSlice zy P
  have hfun : d4BMCompletedPoincareVerticalFirstJetSlice zy P =
      d4BMCompletedPoincareVerticalFirstJetSlice z P := by
    funext q
    rfl
  have hder : d4BMCompletedPoincareVerticalSecondJet zy P =
      d4BMCompletedPoincareVerticalSecondJetSlice z P y :=
    (d4BMCompletedPoincareVerticalSecondJetSlice_eq_at z P hy).symm
  rw [hfun, hder] at h
  simpa [zy] using h

theorem continuousOn_d4BMCompletedPoincareVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    ContinuousOn (d4BMCompletedPoincareVerticalSlice z P) (Ioi 0) := by
  intro y hy
  exact (hasDerivAt_d4BMCompletedPoincareVerticalSlice_at_positive z P hy).continuousAt.continuousWithinAt

theorem continuousOn_d4BMCompletedPoincareVerticalFirstJetSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    ContinuousOn (d4BMCompletedPoincareVerticalFirstJetSlice z P) (Ioi 0) := by
  intro y hy
  exact
    (hasDerivAt_d4BMCompletedPoincareVerticalFirstJetSlice_at_positive z P hy).continuousAt.continuousWithinAt

def d4BMActualFirstStokesVerticalDivergenceSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  2 * d4BMCompletedPoincareVerticalSlice z Q y *
      d4BMCompletedPoincareVerticalFirstJetSlice z P y ^ 2 +
    2 * d4BMCompletedPoincareVerticalSlice z P y *
      d4BMCompletedPoincareVerticalSlice z Q y *
      d4BMCompletedPoincareVerticalSecondJetSlice z P y -
    d4BMCompletedPoincareVerticalSlice z P y ^ 2 *
      d4BMCompletedPoincareVerticalSecondJetSlice z Q y

theorem hasDerivAt_d4BMActualFirstStokesVerticalCurrentSlice_at_positive
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (d4BMActualFirstStokesVerticalCurrentSlice z P Q)
      (d4BMActualFirstStokesVerticalDivergenceSlice z P Q y) y := by
  have hF := hasDerivAt_d4BMCompletedPoincareVerticalSlice_at_positive z P hy
  have hG := hasDerivAt_d4BMCompletedPoincareVerticalSlice_at_positive z Q hy
  have hFy :=
    hasDerivAt_d4BMCompletedPoincareVerticalFirstJetSlice_at_positive z P hy
  have hGy :=
    hasDerivAt_d4BMCompletedPoincareVerticalFirstJetSlice_at_positive z Q hy
  have h := (((hF.const_mul (2 : ℂ)).mul hG).mul hFy).sub ((hF.pow 2).mul hGy)
  simp only [Pi.mul_apply, Pi.pow_apply] at h
  refine h.congr_deriv ?_
  unfold d4BMActualFirstStokesVerticalDivergenceSlice
  ring

theorem continuousOn_d4BMActualFirstStokesVerticalDivergenceSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    ContinuousOn (d4BMActualFirstStokesVerticalDivergenceSlice z P Q) (Ioi 0) := by
  have hF := continuousOn_d4BMCompletedPoincareVerticalSlice z P
  have hG := continuousOn_d4BMCompletedPoincareVerticalSlice z Q
  have hFy := continuousOn_d4BMCompletedPoincareVerticalFirstJetSlice z P
  have hFyy := continuousOn_d4BMCompletedPoincareVerticalSecondJetSlice z P
  have hGyy := continuousOn_d4BMCompletedPoincareVerticalSecondJetSlice z Q
  unfold d4BMActualFirstStokesVerticalDivergenceSlice
  fun_prop

/-- One-dimensional vertical FTC for the literal actual first-Stokes current. -/
theorem intervalIntegral_d4BMActualFirstStokesVerticalDivergenceSlice_eq_sub
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ y in a..b, d4BMActualFirstStokesVerticalDivergenceSlice z P Q y) =
      d4BMActualFirstStokesVerticalCurrentSlice z P Q b -
        d4BMActualFirstStokesVerticalCurrentSlice z P Q a := by
  have hsub : uIcc a b ⊆ Ioi (0 : ℝ) := by
    intro y hy
    change 0 < y
    rcases mem_uIcc.mp hy with hab | hba
    · exact ha.trans_le hab.1
    · exact hb.trans_le hba.1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    exact hasDerivAt_d4BMActualFirstStokesVerticalCurrentSlice_at_positive
      z P Q (hsub hy)
  · exact
      ((continuousOn_d4BMActualFirstStokesVerticalDivergenceSlice z P Q).mono hsub).intervalIntegrable

theorem hasDerivAt_d4BMActualFirstStokesHorizontalCurrent_at
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) :
    HasDerivAt
      (fun q : ℝ => d4BMActualFirstStokesHorizontalCurrent
        (d4BMHorizontalCoordinate z q) P Q)
      (d4BMActualFirstStokesHorizontalDivergence
        (d4BMHorizontalCoordinate z x) P Q) x := by
  simpa [d4BMHorizontalCoordinate] using
    hasDerivAt_d4BMActualFirstStokesHorizontalCurrent
      (d4BMHorizontalCoordinate z x) P Q

theorem continuous_d4BMActualFirstStokesHorizontalDivergence_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    Continuous (fun x : ℝ =>
      d4BMActualFirstStokesHorizontalDivergence
        (d4BMHorizontalCoordinate z x) P Q) := by
  have hF : Continuous (fun x : ℝ =>
      d4BMCompletedEisensteinPoincareSeries (d4BMHorizontalCoordinate z x) P) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hasDerivAt_d4BMCompletedEisensteinPoincareSeries_horizontal
      (d4BMHorizontalCoordinate z x) P).continuousAt
  have hG : Continuous (fun x : ℝ =>
      d4BMCompletedEisensteinPoincareSeries (d4BMHorizontalCoordinate z x) Q) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hasDerivAt_d4BMCompletedEisensteinPoincareSeries_horizontal
      (d4BMHorizontalCoordinate z x) Q).continuousAt
  have hFx : Continuous (fun x : ℝ =>
      d4BMCompletedPoincareHorizontalFirstJet (d4BMHorizontalCoordinate z x) P) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hasDerivAt_d4BMCompletedPoincareHorizontalFirstJet_horizontal
      (d4BMHorizontalCoordinate z x) P).continuousAt
  have hFxx := continuous_d4BMCompletedPoincareHorizontalSecondJet_horizontal z P
  have hGxx := continuous_d4BMCompletedPoincareHorizontalSecondJet_horizontal z Q
  unfold d4BMActualFirstStokesHorizontalDivergence
  fun_prop

/-- One-dimensional horizontal FTC for the literal actual first-Stokes current. -/
theorem intervalIntegral_d4BMActualFirstStokesHorizontalDivergence_eq_sub
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    (a b : ℝ) :
    (∫ x in a..b,
        d4BMActualFirstStokesHorizontalDivergence
          (d4BMHorizontalCoordinate z x) P Q) =
      d4BMActualFirstStokesHorizontalCurrent
          (d4BMHorizontalCoordinate z b) P Q -
        d4BMActualFirstStokesHorizontalCurrent
          (d4BMHorizontalCoordinate z a) P Q := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _hx
    exact hasDerivAt_d4BMActualFirstStokesHorizontalCurrent_at z P Q x
  · exact
      (continuous_d4BMActualFirstStokesHorizontalDivergence_horizontal z P Q).intervalIntegrable a b

/-! ## Literal modular-domain geometry -/

/-- Height of the circular boundary of the standard modular domain above horizontal coordinate
`x`.  Outside the geometric interval this total function is used only as an integration
parameter. -/
def d4BMModularArcHeight (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

/-- Lowest height of the standard modular domain in the strip `|x| ≤ 1/2`. -/
def d4BMModularArcFloor : ℝ := d4BMModularArcHeight (1 / 2)

/-- A total upper-half-plane coordinate for iterated integrands.  On every modular-domain slice
the `max` is definitionally removable because all relevant heights exceed `1/2`. -/
def d4BMStokesCoordinate (x y : ℝ) : D4BMUpperHalfPlaneCoordinate where
  x := x
  y := max y (1 / 2)
  y_pos := lt_of_lt_of_le (by norm_num) (le_max_right y (1 / 2))

def d4BMActualFirstStokesHorizontalCurrentAt
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x y : ℝ) : ℂ :=
  d4BMActualFirstStokesHorizontalCurrent (d4BMStokesCoordinate x y) P Q

def d4BMActualFirstStokesVerticalCurrentAt
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x y : ℝ) : ℂ :=
  d4BMActualFirstStokesVerticalCurrent (d4BMStokesCoordinate x y) P Q

def d4BMActualFirstStokesRadialCurrentAt
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x y : ℝ) : ℂ :=
  d4BMActualFirstStokesRadialCurrent (d4BMStokesCoordinate x y) P Q

def d4BMActualFirstStokesHorizontalDivergenceAt
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x y : ℝ) : ℂ :=
  d4BMActualFirstStokesHorizontalDivergence (d4BMStokesCoordinate x y) P Q

def d4BMActualFirstStokesVerticalDivergenceAt
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x y : ℝ) : ℂ :=
  d4BMActualFirstStokesVerticalDivergence (d4BMStokesCoordinate x y) P Q

theorem d4BMModularArcHeight_pos_of_mem
    {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 2)) (1 / 2)) :
    0 < d4BMModularArcHeight x := by
  have hxlo : -(1 / 2 : ℝ) ≤ x := hx.1
  have hxhi : x ≤ (1 / 2 : ℝ) := hx.2
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (1 / 2 - x)]

theorem d4BMModularArcFloor_pos : 0 < d4BMModularArcFloor := by
  apply d4BMModularArcHeight_pos_of_mem
  constructor <;> norm_num

theorem d4BMModularArcFloor_gt_half : (1 / 2 : ℝ) < d4BMModularArcFloor := by
  unfold d4BMModularArcFloor d4BMModularArcHeight
  have hsq : Real.sqrt (1 - (1 / 2 : ℝ) ^ 2) ^ 2 =
      1 - (1 / 2 : ℝ) ^ 2 := Real.sq_sqrt (by norm_num)
  have hsqrt := Real.sqrt_nonneg (1 - (1 / 2 : ℝ) ^ 2)
  nlinarith

theorem d4BMModularArcHeight_sq
    {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 2)) (1 / 2)) :
    d4BMModularArcHeight x ^ 2 = 1 - x ^ 2 := by
  exact Real.sq_sqrt (le_of_lt (Real.sqrt_pos.1 (d4BMModularArcHeight_pos_of_mem hx)))

theorem d4BMStokesCoordinate_eq_of_half_le
    (x y : ℝ) (hy : (1 / 2 : ℝ) ≤ y) :
    d4BMStokesCoordinate x y = ⟨x, y, lt_of_lt_of_le (by norm_num) hy⟩ := by
  unfold d4BMStokesCoordinate
  rw [max_eq_left hy]

theorem d4BMStokesCoordinate_arc_unitCircle
    {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 2)) (1 / 2)) :
    (d4BMStokesCoordinate x (d4BMModularArcHeight x)).x ^ 2 +
        (d4BMStokesCoordinate x (d4BMModularArcHeight x)).y ^ 2 = 1 := by
  have harc : (1 / 2 : ℝ) ≤ d4BMModularArcHeight x := by
    have hxlo : -(1 / 2 : ℝ) ≤ x := hx.1
    have hxhi : x ≤ (1 / 2 : ℝ) := hx.2
    have hsq := d4BMModularArcHeight_sq hx
    have hsqrt := Real.sqrt_nonneg (1 - x ^ 2)
    nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (1 / 2 - x)]
  change x ^ 2 + max (d4BMModularArcHeight x) (1 / 2) ^ 2 = 1
  rw [max_eq_left harc, d4BMModularArcHeight_sq hx]
  ring

theorem d4BMStokesCoordinate_arc_invert
    {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 2)) (1 / 2)) :
    d4BMEisensteinInvertCoordinate
        (d4BMStokesCoordinate x (d4BMModularArcHeight x)) =
      d4BMStokesCoordinate (-x) (d4BMModularArcHeight x) := by
  have hcircle := d4BMStokesCoordinate_arc_unitCircle hx
  unfold d4BMEisensteinInvertCoordinate
  rw [hcircle]
  simp [d4BMStokesCoordinate]

/-- Pointwise cancellation of the two oriented radial currents along the circular boundary. -/
theorem d4BM_actualFirstStokesRadialCurrentAt_arc_pair_eq_zero
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    d4BMActualFirstStokesRadialCurrentAt P Q (-x) (d4BMModularArcHeight x) +
        d4BMActualFirstStokesRadialCurrentAt P Q x (d4BMModularArcHeight x) = 0 := by
  have hxfull : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith [hx.1], hx.2⟩
  let z : D4BMUnitSemicircleCoordinate :=
    ⟨d4BMStokesCoordinate x (d4BMModularArcHeight x),
      d4BMStokesCoordinate_arc_unitCircle hxfull⟩
  have hinv := d4BM_actualFirstStokesRadialCurrent_invert_unitCircle z P Q
  rw [d4BMStokesCoordinate_arc_invert hxfull] at hinv
  change d4BMActualFirstStokesRadialCurrent
      (d4BMStokesCoordinate (-x) (d4BMModularArcHeight x)) P Q +
    d4BMActualFirstStokesRadialCurrent
      (d4BMStokesCoordinate x (d4BMModularArcHeight x)) P Q = 0
  rw [hinv]
  ring

end
end RHTower
