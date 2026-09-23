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
      ((p.pair.1 : ℝ) * y) ^ (2 : ℕ) +
        ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ (2 : ℕ) := by
    change 0 < d4BMPoincareQuadratic ⟨z.x, y, hy0⟩ p.pair
    exact d4BMPoincareQuadratic_pos ⟨z.x, y, hy0⟩ p.pair p.pair_ne_zero
  have hQC :
      (((((p.pair.1 : ℝ) * y) ^ (2 : ℕ) +
        ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ (2 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hQpos.ne'
  unfold d4BMPoincareSeedVerticalSecondJetSlice
  let qC : ℝ → ℂ := fun q =>
    (((p.pair.1 : ℝ) * q) ^ (2 : ℕ) +
      ((p.pair.1 : ℝ) * z.x + (p.pair.2 : ℝ)) ^ (2 : ℕ) : ℝ)
  have hqC : ContinuousAt qC y := by
    dsimp only [qC]
    fun_prop
  have hqCne : qC y ≠ 0 := by
    simpa [qC] using hQC
  have hyfun : ContinuousAt (fun q : ℝ => (q : ℂ)) y :=
    Complex.continuous_ofReal.continuousAt
  have hfirst : ContinuousAt
      (fun q : ℝ => s * (s - 1) / (q : ℂ) ^ (2 : ℕ)) y :=
    continuousAt_const.div (hyfun.pow 2) (pow_ne_zero 2 hyC)
  have hsecond : ContinuousAt
      (fun q : ℝ =>
        2 * s * (1 + 2 * s) * (p.pair.1 : ℂ) ^ (2 : ℕ) / qC q) y :=
    continuousAt_const.div hqC hqCne
  have hthird : ContinuousAt
      (fun q : ℝ =>
        4 * s * (s + 1) * (p.pair.1 : ℂ) ^ (4 : ℕ) * (q : ℂ) ^ (2 : ℕ) /
          qC q ^ (2 : ℕ)) y :=
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
      d4BMCompletedPoincareVerticalFirstJetSlice z P y ^ (2 : ℕ) +
    2 * d4BMCompletedPoincareVerticalSlice z P y *
      d4BMCompletedPoincareVerticalSlice z Q y *
      d4BMCompletedPoincareVerticalSecondJetSlice z P y -
    d4BMCompletedPoincareVerticalSlice z P y ^ (2 : ℕ) *
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
def d4BMModularArcHeight (x : ℝ) : ℝ := Real.sqrt (1 - x ^ (2 : ℕ))

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

theorem d4BMUpperHalfPlaneCoordinate_eq_of_xy
    {z w : D4BMUpperHalfPlaneCoordinate} (hx : z.x = w.x) (hy : z.y = w.y) : z = w := by
  cases z
  cases w
  simp_all

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
  have hsq : Real.sqrt (1 - (1 / 2 : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) =
      1 - (1 / 2 : ℝ) ^ (2 : ℕ) := Real.sq_sqrt (by norm_num)
  have hsqrt := Real.sqrt_nonneg (1 - (1 / 2 : ℝ) ^ (2 : ℕ))
  nlinarith

theorem d4BMModularArcHeight_sq
    {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 2)) (1 / 2)) :
    d4BMModularArcHeight x ^ (2 : ℕ) = 1 - x ^ (2 : ℕ) := by
  exact Real.sq_sqrt (le_of_lt (Real.sqrt_pos.1 (d4BMModularArcHeight_pos_of_mem hx)))

theorem d4BMStokesCoordinate_eq_of_half_le
    (x y : ℝ) (hy : (1 / 2 : ℝ) ≤ y) :
    d4BMStokesCoordinate x y = ⟨x, y, lt_of_lt_of_le (by norm_num) hy⟩ := by
  apply d4BMUpperHalfPlaneCoordinate_eq_of_xy
  · rfl
  · exact max_eq_left hy

theorem d4BMStokesCoordinate_arc_unitCircle
    {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 2)) (1 / 2)) :
    (d4BMStokesCoordinate x (d4BMModularArcHeight x)).x ^ (2 : ℕ) +
        (d4BMStokesCoordinate x (d4BMModularArcHeight x)).y ^ (2 : ℕ) = 1 := by
  have harc : (1 / 2 : ℝ) ≤ d4BMModularArcHeight x := by
    have hxlo : -(1 / 2 : ℝ) ≤ x := hx.1
    have hxhi : x ≤ (1 / 2 : ℝ) := hx.2
    have hsq := d4BMModularArcHeight_sq hx
    have hsqrt : 0 ≤ d4BMModularArcHeight x := by
      exact Real.sqrt_nonneg (1 - x ^ (2 : ℕ))
    nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (1 / 2 - x)]
  change x ^ (2 : ℕ) + max (d4BMModularArcHeight x) (1 / 2) ^ (2 : ℕ) = 1
  rw [max_eq_left harc, d4BMModularArcHeight_sq hx]
  ring

theorem d4BMStokesCoordinate_arc_invert
    {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 2)) (1 / 2)) :
    d4BMEisensteinInvertCoordinate
        (d4BMStokesCoordinate x (d4BMModularArcHeight x)) =
      d4BMStokesCoordinate (-x) (d4BMModularArcHeight x) := by
  have hcircle := d4BMStokesCoordinate_arc_unitCircle hx
  apply d4BMUpperHalfPlaneCoordinate_eq_of_xy
  · change
      -(d4BMStokesCoordinate x (d4BMModularArcHeight x)).x /
          ((d4BMStokesCoordinate x (d4BMModularArcHeight x)).x ^ (2 : ℕ) +
            (d4BMStokesCoordinate x (d4BMModularArcHeight x)).y ^ (2 : ℕ)) = -x
    rw [hcircle]
    simp [d4BMStokesCoordinate]
  · change
      (d4BMStokesCoordinate x (d4BMModularArcHeight x)).y /
          ((d4BMStokesCoordinate x (d4BMModularArcHeight x)).x ^ (2 : ℕ) +
            (d4BMStokesCoordinate x (d4BMModularArcHeight x)).y ^ (2 : ℕ)) =
        (d4BMStokesCoordinate (-x) (d4BMModularArcHeight x)).y
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

theorem d4BMModularArcHeight_half_le
    {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 2)) (1 / 2)) :
    (1 / 2 : ℝ) ≤ d4BMModularArcHeight x := by
  have hxlo : -(1 / 2 : ℝ) ≤ x := hx.1
  have hxhi : x ≤ (1 / 2 : ℝ) := hx.2
  have hsq := d4BMModularArcHeight_sq hx
  have hsqrt : 0 ≤ d4BMModularArcHeight x := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (1 / 2 - x)]

theorem d4BMModularArcHeight_le_one
    {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 2)) (1 / 2)) :
    d4BMModularArcHeight x ≤ 1 := by
  have hsq := d4BMModularArcHeight_sq hx
  have hsqrt : 0 ≤ d4BMModularArcHeight x := Real.sqrt_nonneg _
  nlinarith [sq_nonneg x]

theorem d4BMActualFirstStokesVerticalDivergenceSlice_eq_at
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    (x y : ℝ) (hy : (1 / 2 : ℝ) ≤ y) :
    d4BMActualFirstStokesVerticalDivergenceSlice
        (d4BMStokesCoordinate x 1) P Q y =
      d4BMActualFirstStokesVerticalDivergenceAt P Q x y := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  let zy : D4BMUpperHalfPlaneCoordinate := ⟨x, y, hy0⟩
  have hcoord : d4BMStokesCoordinate x y = zy := by
    exact d4BMStokesCoordinate_eq_of_half_le x y hy
  unfold d4BMActualFirstStokesVerticalDivergenceAt
  rw [hcoord]
  rfl

theorem d4BMActualFirstStokesVerticalCurrentSlice_eq_at
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    (x y : ℝ) (hy : (1 / 2 : ℝ) ≤ y) :
    d4BMActualFirstStokesVerticalCurrentSlice
        (d4BMStokesCoordinate x 1) P Q y =
      d4BMActualFirstStokesVerticalCurrentAt P Q x y := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  let zy : D4BMUpperHalfPlaneCoordinate := ⟨x, y, hy0⟩
  have hcoord : d4BMStokesCoordinate x y = zy := by
    exact d4BMStokesCoordinate_eq_of_half_le x y hy
  unfold d4BMActualFirstStokesVerticalCurrentAt
  rw [hcoord]
  rfl

/-- Literal vertical part of the Euclidean divergence integral over the truncated modular
fundamental domain. -/
def d4BMActualFirstStokesVerticalBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) : ℂ :=
  ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
    ∫ y in d4BMModularArcHeight x..Y,
      d4BMActualFirstStokesVerticalDivergenceAt P Q x y

/-- Vertical FTC on every genuine modular-domain fibre. -/
theorem d4BM_actualFirstStokesVerticalBulk_eq_boundary
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    d4BMActualFirstStokesVerticalBulk P Q Y =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        (d4BMActualFirstStokesVerticalCurrentAt P Q x Y -
          d4BMActualFirstStokesVerticalCurrentAt P Q x
            (d4BMModularArcHeight x)) := by
  unfold d4BMActualFirstStokesVerticalBulk
  apply intervalIntegral.integral_congr
  intro x hx
  have hxI : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    simpa [uIcc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)] using hx
  have harcpos := d4BMModularArcHeight_pos_of_mem hxI
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  have harcleY : d4BMModularArcHeight x ≤ Y :=
    (d4BMModularArcHeight_le_one hxI).trans hY
  change
    (∫ y in d4BMModularArcHeight x..Y,
      d4BMActualFirstStokesVerticalDivergenceAt P Q x y) = _
  calc
    (∫ y in d4BMModularArcHeight x..Y,
        d4BMActualFirstStokesVerticalDivergenceAt P Q x y) =
        ∫ y in d4BMModularArcHeight x..Y,
          d4BMActualFirstStokesVerticalDivergenceSlice
            (d4BMStokesCoordinate x 1) P Q y := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hyI : y ∈ Set.Icc (d4BMModularArcHeight x) Y := by
        simpa [uIcc_of_le harcleY] using hy
      have hyhalf : (1 / 2 : ℝ) ≤ y :=
        (d4BMModularArcHeight_half_le hxI).trans hyI.1
      exact (d4BMActualFirstStokesVerticalDivergenceSlice_eq_at
        P Q x y hyhalf).symm
    _ = d4BMActualFirstStokesVerticalCurrentSlice
          (d4BMStokesCoordinate x 1) P Q Y -
        d4BMActualFirstStokesVerticalCurrentSlice
          (d4BMStokesCoordinate x 1) P Q (d4BMModularArcHeight x) :=
      intervalIntegral_d4BMActualFirstStokesVerticalDivergenceSlice_eq_sub
        (d4BMStokesCoordinate x 1) P Q harcpos hYpos
    _ = d4BMActualFirstStokesVerticalCurrentAt P Q x Y -
        d4BMActualFirstStokesVerticalCurrentAt P Q x
          (d4BMModularArcHeight x) := by
      rw [d4BMActualFirstStokesVerticalCurrentSlice_eq_at P Q x Y
          (by linarith),
        d4BMActualFirstStokesVerticalCurrentSlice_eq_at P Q x
          (d4BMModularArcHeight x) (d4BMModularArcHeight_half_le hxI)]

/-- Horizontal radius of the circular boundary at height `y`. -/
def d4BMModularSideRadius (y : ℝ) : ℝ := Real.sqrt (1 - y ^ (2 : ℕ))

theorem d4BMStokesCoordinate_right_eq_translate_left (y : ℝ) :
    d4BMStokesCoordinate (1 / 2) y =
      d4BMEisensteinTranslateCoordinate (d4BMStokesCoordinate (-(1 / 2)) y) := by
  apply d4BMUpperHalfPlaneCoordinate_eq_of_xy
  · norm_num [d4BMStokesCoordinate, d4BMEisensteinTranslateCoordinate]
  · rfl

theorem d4BM_actualFirstStokesHorizontalCurrentAt_verticalSides
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) :
    d4BMActualFirstStokesHorizontalCurrentAt P Q (1 / 2) y =
      d4BMActualFirstStokesHorizontalCurrentAt P Q (-(1 / 2)) y := by
  unfold d4BMActualFirstStokesHorizontalCurrentAt
  rw [d4BMStokesCoordinate_right_eq_translate_left,
    d4BM_actualFirstStokesHorizontalCurrent_translate]

theorem intervalIntegral_d4BMActualFirstStokesHorizontalDivergenceAt_eq_sub
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    (y a b : ℝ) (_hy : (1 / 2 : ℝ) ≤ y) :
    (∫ x in a..b, d4BMActualFirstStokesHorizontalDivergenceAt P Q x y) =
      d4BMActualFirstStokesHorizontalCurrentAt P Q b y -
        d4BMActualFirstStokesHorizontalCurrentAt P Q a y := by
  let z := d4BMStokesCoordinate 0 y
  have hcoord (x : ℝ) : d4BMHorizontalCoordinate z x = d4BMStokesCoordinate x y := by
    apply d4BMUpperHalfPlaneCoordinate_eq_of_xy <;> rfl
  calc
    (∫ x in a..b, d4BMActualFirstStokesHorizontalDivergenceAt P Q x y) =
        ∫ x in a..b,
          d4BMActualFirstStokesHorizontalDivergence
            (d4BMHorizontalCoordinate z x) P Q := by
      apply intervalIntegral.integral_congr
      intro x _hx
      simpa [d4BMActualFirstStokesHorizontalDivergenceAt] using
        congrArg (fun w => d4BMActualFirstStokesHorizontalDivergence w P Q)
          (hcoord x).symm
    _ = d4BMActualFirstStokesHorizontalCurrent
          (d4BMHorizontalCoordinate z b) P Q -
        d4BMActualFirstStokesHorizontalCurrent
          (d4BMHorizontalCoordinate z a) P Q :=
      intervalIntegral_d4BMActualFirstStokesHorizontalDivergence_eq_sub z P Q a b
    _ = d4BMActualFirstStokesHorizontalCurrentAt P Q b y -
        d4BMActualFirstStokesHorizontalCurrentAt P Q a y := by
      unfold d4BMActualFirstStokesHorizontalCurrentAt
      rw [hcoord, hcoord]

/-- Horizontal divergence over the two side slivers below height one.  The central interval is
excluded because the standard modular domain satisfies `x^(2 : ℕ) + y^(2 : ℕ) ≥ 1`. -/
def d4BMActualFirstStokesHorizontalLowerBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  ∫ y in d4BMModularArcFloor..1,
    ((∫ x in (-(1 / 2 : ℝ))..(-d4BMModularSideRadius y),
        d4BMActualFirstStokesHorizontalDivergenceAt P Q x y) +
      ∫ x in d4BMModularSideRadius y..(1 / 2),
        d4BMActualFirstStokesHorizontalDivergenceAt P Q x y)

/-- Horizontal divergence over the full strip above height one. -/
def d4BMActualFirstStokesHorizontalUpperBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) : ℂ :=
  ∫ y in 1..Y,
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
      d4BMActualFirstStokesHorizontalDivergenceAt P Q x y

def d4BMActualFirstStokesHorizontalBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) : ℂ :=
  d4BMActualFirstStokesHorizontalLowerBulk P Q +
    d4BMActualFirstStokesHorizontalUpperBulk P Q Y

theorem d4BM_actualFirstStokesHorizontalLowerBulk_eq_arc
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualFirstStokesHorizontalLowerBulk P Q =
      ∫ y in d4BMModularArcFloor..1,
        (d4BMActualFirstStokesHorizontalCurrentAt P Q
            (-d4BMModularSideRadius y) y -
          d4BMActualFirstStokesHorizontalCurrentAt P Q
            (d4BMModularSideRadius y) y) := by
  unfold d4BMActualFirstStokesHorizontalLowerBulk
  apply intervalIntegral.integral_congr
  intro y hy
  have hfloorHalf : (1 / 2 : ℝ) ≤ d4BMModularArcFloor :=
    le_of_lt d4BMModularArcFloor_gt_half
  have hfloorOne : d4BMModularArcFloor ≤ 1 := by
    exact d4BMModularArcHeight_le_one (by constructor <;> norm_num)
  have hyI : y ∈ Set.Icc d4BMModularArcFloor 1 := by
    simpa [uIcc_of_le hfloorOne] using hy
  have hyhalf : (1 / 2 : ℝ) ≤ y := hfloorHalf.trans hyI.1
  change
    (∫ x in (-(1 / 2 : ℝ))..(-d4BMModularSideRadius y),
        d4BMActualFirstStokesHorizontalDivergenceAt P Q x y) +
      (∫ x in d4BMModularSideRadius y..(1 / 2),
        d4BMActualFirstStokesHorizontalDivergenceAt P Q x y) = _
  rw [intervalIntegral_d4BMActualFirstStokesHorizontalDivergenceAt_eq_sub
      P Q y (-(1 / 2)) (-d4BMModularSideRadius y) hyhalf,
    intervalIntegral_d4BMActualFirstStokesHorizontalDivergenceAt_eq_sub
      P Q y (d4BMModularSideRadius y) (1 / 2) hyhalf,
    d4BM_actualFirstStokesHorizontalCurrentAt_verticalSides P Q y]
  ring

theorem d4BM_actualFirstStokesHorizontalUpperBulk_eq_zero
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    d4BMActualFirstStokesHorizontalUpperBulk P Q Y = 0 := by
  unfold d4BMActualFirstStokesHorizontalUpperBulk
  calc
    (∫ y in 1..Y,
        ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
          d4BMActualFirstStokesHorizontalDivergenceAt P Q x y) =
        ∫ _y in 1..Y, (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hyI : y ∈ Set.Icc (1 : ℝ) Y := by
        simpa [uIcc_of_le hY] using hy
      change
        (∫ x in (-(1 / 2 : ℝ))..(1 / 2),
          d4BMActualFirstStokesHorizontalDivergenceAt P Q x y) = 0
      rw [intervalIntegral_d4BMActualFirstStokesHorizontalDivergenceAt_eq_sub
          P Q y (-(1 / 2)) (1 / 2) (by linarith [hyI.1]),
        d4BM_actualFirstStokesHorizontalCurrentAt_verticalSides]
      ring
    _ = 0 := by simp

theorem d4BM_actualFirstStokesHorizontalBulk_eq_arc
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    d4BMActualFirstStokesHorizontalBulk P Q Y =
      ∫ y in d4BMModularArcFloor..1,
        (d4BMActualFirstStokesHorizontalCurrentAt P Q
            (-d4BMModularSideRadius y) y -
          d4BMActualFirstStokesHorizontalCurrentAt P Q
            (d4BMModularSideRadius y) y) := by
  unfold d4BMActualFirstStokesHorizontalBulk
  rw [d4BM_actualFirstStokesHorizontalLowerBulk_eq_arc,
    d4BM_actualFirstStokesHorizontalUpperBulk_eq_zero P Q hY, add_zero]

theorem d4BMModularArcHeight_zero : d4BMModularArcHeight 0 = 1 := by
  norm_num [d4BMModularArcHeight]

theorem d4BMModularArcHeight_half :
    d4BMModularArcHeight (1 / 2) = d4BMModularArcFloor := rfl

theorem d4BMModularSideRadius_arcHeight
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    d4BMModularSideRadius (d4BMModularArcHeight x) = x := by
  have hxfull : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith [hx.1], hx.2⟩
  unfold d4BMModularSideRadius
  rw [d4BMModularArcHeight_sq hxfull]
  ring_nf
  exact Real.sqrt_sq hx.1

theorem hasDerivAt_d4BMModularArcHeight
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt d4BMModularArcHeight
      (-x / d4BMModularArcHeight x) x := by
  have hpos : 0 < 1 - x ^ (2 : ℕ) := by nlinarith [hx.1, hx.2, sq_nonneg (x + 1 / 2)]
  have hinner : HasDerivAt (fun q : ℝ => 1 - q ^ (2 : ℕ)) (-2 * x) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)
    have hfun : ((fun _ : ℝ => 1) - id ^ (2 : ℕ)) = (fun q : ℝ => 1 - q ^ (2 : ℕ)) := by
      funext q
      rfl
    rw [hfun] at h
    exact h.congr_deriv (by norm_num)
  have hsqrt := hinner.sqrt hpos.ne'
  unfold d4BMModularArcHeight
  convert hsqrt using 1
  field_simp [Real.sqrt_ne_zero'.2 hpos]

theorem continuous_d4BMModularArcHeight : Continuous d4BMModularArcHeight := by
  unfold d4BMModularArcHeight
  fun_prop

def d4BMActualFirstStokesHorizontalArcHeightFlux
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  d4BMActualFirstStokesHorizontalCurrentAt P Q (-d4BMModularSideRadius y) y -
    d4BMActualFirstStokesHorizontalCurrentAt P Q (d4BMModularSideRadius y) y

def d4BMActualFirstStokesHorizontalArcParameterFlux
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) : ℂ :=
  (x / d4BMModularArcHeight x) •
    (d4BMActualFirstStokesHorizontalCurrentAt P Q (-x) (d4BMModularArcHeight x) -
      d4BMActualFirstStokesHorizontalCurrentAt P Q x (d4BMModularArcHeight x))

/-- Exact change of variables from horizontal height slices to the right-half circular arc.
This is the orientation-sensitive step absent from the previous pointwise boundary pairing. -/
theorem d4BM_actualFirstStokesHorizontalArc_changeOfVariables
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    (∫ y in d4BMModularArcFloor..1,
        d4BMActualFirstStokesHorizontalArcHeightFlux P Q y) =
      ∫ x in 0..(1 / 2),
        d4BMActualFirstStokesHorizontalArcParameterFlux P Q x := by
  let g : ℝ → ℂ := d4BMActualFirstStokesHorizontalArcHeightFlux P Q
  have hsubst := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
    (g := g) (a := (0 : ℝ)) (b := (1 / 2 : ℝ))
    (f := d4BMModularArcHeight)
    (f' := fun x => -x / d4BMModularArcHeight x)
    continuous_d4BMModularArcHeight.continuousOn
    (by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (1 / 2) := by simpa using hx
      exact hasDerivAt_d4BMModularArcHeight hx')
    (by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (1 / 2) := by simpa using hx
      have harcpos : 0 < d4BMModularArcHeight x := by
        apply d4BMModularArcHeight_pos_of_mem
        constructor <;> linarith [hx'.1, hx'.2]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hx'.1]) harcpos.le)
  have hsubst' :
      (∫ x in 0..(1 / 2),
          (-x / d4BMModularArcHeight x) • (g ∘ d4BMModularArcHeight) x) =
        ∫ y in 1..d4BMModularArcFloor, g y := by
    rw [d4BMModularArcHeight_zero, d4BMModularArcHeight_half] at hsubst
    exact hsubst
  have hleft :
      (∫ x in 0..(1 / 2),
          (-x / d4BMModularArcHeight x) • (g ∘ d4BMModularArcHeight) x) =
        -(∫ x in 0..(1 / 2),
          d4BMActualFirstStokesHorizontalArcParameterFlux P Q x) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) (1 / 2) := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hx
    have hradius := d4BMModularSideRadius_arcHeight hxI
    unfold g d4BMActualFirstStokesHorizontalArcHeightFlux
      d4BMActualFirstStokesHorizontalArcParameterFlux
    simp only [Function.comp_apply, hradius]
    rw [show -x / d4BMModularArcHeight x =
        -(x / d4BMModularArcHeight x) by ring, neg_smul]
  have hright :
      (∫ y in 1..d4BMModularArcFloor, g y) =
        -(∫ y in d4BMModularArcFloor..1, g y) :=
    intervalIntegral.integral_symm d4BMModularArcFloor 1
  have hneg :
      -(∫ x in 0..(1 / 2),
          d4BMActualFirstStokesHorizontalArcParameterFlux P Q x) =
        -(∫ y in d4BMModularArcFloor..1,
          d4BMActualFirstStokesHorizontalArcHeightFlux P Q y) := by
    calc
      _ = ∫ x in 0..(1 / 2),
          (-x / d4BMModularArcHeight x) • (g ∘ d4BMModularArcHeight) x := hleft.symm
      _ = ∫ y in 1..d4BMModularArcFloor, g y := hsubst'
      _ = -(∫ y in d4BMModularArcFloor..1, g y) := hright
      _ = -(∫ y in d4BMModularArcFloor..1,
          d4BMActualFirstStokesHorizontalArcHeightFlux P Q y) := rfl
  exact (neg_inj.mp hneg).symm

theorem d4BM_actualFirstStokesRadialCurrent_eq_components
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualFirstStokesRadialCurrent z P Q =
      (z.x : ℂ) * d4BMActualFirstStokesHorizontalCurrent z P Q +
        (z.y : ℂ) * d4BMActualFirstStokesVerticalCurrent z P Q := by
  unfold d4BMActualFirstStokesRadialCurrent
    d4BMActualFirstStokesHorizontalCurrent d4BMActualFirstStokesVerticalCurrent
  rw [d4BM_completedPoincareRadialFirstJet_eq_gradientContraction z P,
    d4BM_completedPoincareRadialFirstJet_eq_gradientContraction z Q]
  ring

def d4BMActualFirstStokesCircularBoundaryFlux
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) : ℂ :=
  (x / d4BMModularArcHeight x) •
      (d4BMActualFirstStokesHorizontalCurrentAt P Q (-x) (d4BMModularArcHeight x) -
        d4BMActualFirstStokesHorizontalCurrentAt P Q x (d4BMModularArcHeight x)) -
    d4BMActualFirstStokesVerticalCurrentAt P Q (-x) (d4BMModularArcHeight x) -
    d4BMActualFirstStokesVerticalCurrentAt P Q x (d4BMModularArcHeight x)

/-- The exact oriented circular flux vanishes pointwise after both half-arcs are paired.  This is
the radial inversion law with the Jacobian and outward-normal signs made literal. -/
theorem d4BM_actualFirstStokesCircularBoundaryFlux_eq_zero
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    d4BMActualFirstStokesCircularBoundaryFlux P Q x = 0 := by
  have hxfull : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith [hx.1], hx.2⟩
  have hxneg : -x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have harcpos := d4BMModularArcHeight_pos_of_mem hxfull
  have harchalf := d4BMModularArcHeight_half_le hxfull
  have hpair := d4BM_actualFirstStokesRadialCurrentAt_arc_pair_eq_zero P Q hx
  have hneg := d4BM_actualFirstStokesRadialCurrent_eq_components
    (d4BMStokesCoordinate (-x) (d4BMModularArcHeight x)) P Q
  have hpos := d4BM_actualFirstStokesRadialCurrent_eq_components
    (d4BMStokesCoordinate x (d4BMModularArcHeight x)) P Q
  change
    d4BMActualFirstStokesRadialCurrentAt P Q (-x) (d4BMModularArcHeight x) = _
      at hneg
  change
    d4BMActualFirstStokesRadialCurrentAt P Q x (d4BMModularArcHeight x) = _
      at hpos
  simp only [d4BMStokesCoordinate, max_eq_left harchalf] at hneg hpos
  rw [hneg, hpos] at hpair
  unfold d4BMActualFirstStokesCircularBoundaryFlux
  rw [Complex.real_smul, Complex.ofReal_div]
  unfold d4BMActualFirstStokesHorizontalCurrentAt
    d4BMActualFirstStokesVerticalCurrentAt
  simp only [d4BMStokesCoordinate, max_eq_left harchalf]
  have harcC : (d4BMModularArcHeight x : ℂ) ≠ 0 := by
    exact_mod_cast harcpos.ne'
  push_cast at hpair ⊢
  field_simp [harcC]
  linear_combination -hpair

theorem intervalIntegral_d4BMActualFirstStokesVerticalDivergenceAt_eq_sub
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    (x a b : ℝ) (ha : (1 / 2 : ℝ) ≤ a) (hb : (1 / 2 : ℝ) ≤ b) :
    (∫ y in a..b, d4BMActualFirstStokesVerticalDivergenceAt P Q x y) =
      d4BMActualFirstStokesVerticalCurrentAt P Q x b -
        d4BMActualFirstStokesVerticalCurrentAt P Q x a := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) hb
  calc
    (∫ y in a..b, d4BMActualFirstStokesVerticalDivergenceAt P Q x y) =
        ∫ y in a..b,
          d4BMActualFirstStokesVerticalDivergenceSlice
            (d4BMStokesCoordinate x 1) P Q y := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hyhalf : (1 / 2 : ℝ) ≤ y := by
        rcases mem_uIcc.mp hy with hab | hba
        · exact ha.trans hab.1
        · exact hb.trans hba.1
      exact (d4BMActualFirstStokesVerticalDivergenceSlice_eq_at
        P Q x y hyhalf).symm
    _ = d4BMActualFirstStokesVerticalCurrentSlice
          (d4BMStokesCoordinate x 1) P Q b -
        d4BMActualFirstStokesVerticalCurrentSlice
          (d4BMStokesCoordinate x 1) P Q a :=
      intervalIntegral_d4BMActualFirstStokesVerticalDivergenceSlice_eq_sub
        (d4BMStokesCoordinate x 1) P Q ha0 hb0
    _ = d4BMActualFirstStokesVerticalCurrentAt P Q x b -
        d4BMActualFirstStokesVerticalCurrentAt P Q x a := by
      rw [d4BMActualFirstStokesVerticalCurrentSlice_eq_at P Q x b hb,
        d4BMActualFirstStokesVerticalCurrentSlice_eq_at P Q x a ha]

/-- Literal paired-coordinate integral of the vertical divergence on both halves of the truncated
modular domain and the horizontal divergence on both lower side slivers.  The omitted upper-strip
horizontal integral is identically zero by
`d4BM_actualFirstStokesHorizontalUpperBulk_eq_zero`. -/
def d4BMActualFirstStokesPairedTruncatedBulk
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) : ℂ :=
  ∫ x in 0..(1 / 2),
    ((∫ y in d4BMModularArcHeight x..Y,
        d4BMActualFirstStokesVerticalDivergenceAt P Q (-x) y) +
      (∫ y in d4BMModularArcHeight x..Y,
        d4BMActualFirstStokesVerticalDivergenceAt P Q x y) +
      (x / d4BMModularArcHeight x) •
        ((∫ q in (-(1 / 2 : ℝ))..(-x),
            d4BMActualFirstStokesHorizontalDivergenceAt P Q q
              (d4BMModularArcHeight x)) +
          ∫ q in x..(1 / 2),
            d4BMActualFirstStokesHorizontalDivergenceAt P Q q
              (d4BMModularArcHeight x)))

def d4BMActualFirstStokesPairedCuspTop
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (Y : ℝ) : ℂ :=
  ∫ x in 0..(1 / 2),
    (d4BMActualFirstStokesVerticalCurrentAt P Q (-x) Y +
      d4BMActualFirstStokesVerticalCurrentAt P Q x Y)

/-- Literal two-dimensional Green theorem on the truncated standard modular domain.  Every
vertical fibre and both curved side slivers are actual iterated interval integrals; FTC, translation,
the arc Jacobian, and inversion leave exactly the paired cusp-top current. -/
theorem d4BM_actualFirstStokesPairedTruncatedBulk_eq_cuspTop
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    {Y : ℝ} (hY : 1 ≤ Y) :
    d4BMActualFirstStokesPairedTruncatedBulk P Q Y =
      d4BMActualFirstStokesPairedCuspTop P Q Y := by
  unfold d4BMActualFirstStokesPairedTruncatedBulk
    d4BMActualFirstStokesPairedCuspTop
  apply intervalIntegral.integral_congr
  intro x hx
  have hxI : x ∈ Set.Icc (0 : ℝ) (1 / 2) := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hx
  have hxfull : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith [hxI.1], hxI.2⟩
  have harchalf := d4BMModularArcHeight_half_le hxfull
  have hYhalf : (1 / 2 : ℝ) ≤ Y := by linarith
  change
    (∫ y in d4BMModularArcHeight x..Y,
        d4BMActualFirstStokesVerticalDivergenceAt P Q (-x) y) +
      (∫ y in d4BMModularArcHeight x..Y,
        d4BMActualFirstStokesVerticalDivergenceAt P Q x y) +
      (x / d4BMModularArcHeight x) •
        ((∫ q in (-(1 / 2 : ℝ))..(-x),
            d4BMActualFirstStokesHorizontalDivergenceAt P Q q
              (d4BMModularArcHeight x)) +
          ∫ q in x..(1 / 2),
            d4BMActualFirstStokesHorizontalDivergenceAt P Q q
              (d4BMModularArcHeight x)) = _
  rw [intervalIntegral_d4BMActualFirstStokesVerticalDivergenceAt_eq_sub
      P Q (-x) (d4BMModularArcHeight x) Y harchalf hYhalf,
    intervalIntegral_d4BMActualFirstStokesVerticalDivergenceAt_eq_sub
      P Q x (d4BMModularArcHeight x) Y harchalf hYhalf,
    intervalIntegral_d4BMActualFirstStokesHorizontalDivergenceAt_eq_sub
      P Q (d4BMModularArcHeight x) (-(1 / 2)) (-x) harchalf,
    intervalIntegral_d4BMActualFirstStokesHorizontalDivergenceAt_eq_sub
      P Q (d4BMModularArcHeight x) x (1 / 2) harchalf,
    d4BM_actualFirstStokesHorizontalCurrentAt_verticalSides P Q
      (d4BMModularArcHeight x)]
  have hflux := d4BM_actualFirstStokesCircularBoundaryFlux_eq_zero P Q hxI
  unfold d4BMActualFirstStokesCircularBoundaryFlux at hflux
  rw [Complex.real_smul] at hflux ⊢
  linear_combination hflux

/-- Pointwise hyperbolic-measure form of the actual first defect on every literal integration
coordinate.  This is the exact density bridge needed before any Fubini interchange. -/
theorem d4BM_actualFirstStokesDefectDensity_div_heightSq_eq_divergenceAt
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter)
    (x y : ℝ) (hy : (1 / 2 : ℝ) ≤ y) :
    (2 * d4BMActualFirstStokesDefectDensity (d4BMStokesCoordinate x y) P Q) /
        (y : ℂ) ^ (2 : ℕ) =
      d4BMActualFirstStokesHorizontalDivergenceAt P Q x y +
        d4BMActualFirstStokesVerticalDivergenceAt P Q x y := by
  have h := d4BM_actualFirstStokesDefectDensity_eq_divergence
    (d4BMStokesCoordinate x y) P Q
  have hy0 : (y : ℂ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hy).ne'
  unfold d4BMActualFirstStokesHorizontalDivergenceAt
    d4BMActualFirstStokesVerticalDivergenceAt
  simp only [d4BMStokesCoordinate, max_eq_left hy] at h ⊢
  rw [h]
  field_simp

end
end RHTower
