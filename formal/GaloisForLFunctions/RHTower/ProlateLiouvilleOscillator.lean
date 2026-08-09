import GaloisForLFunctions.HTGeometry.PerturbedOscillatorPhase
import GaloisForLFunctions.RHTower.CCMRadialProlateDefect
import GaloisForLFunctions.RHTower.CCMFirstRowDunsterModel
import GaloisForLFunctions.RHTower.ProlateTwoBranch

/-!
# The radial prolate mode as a perturbed oscillator

The Liouville normal form `u = √(x²-1) R` satisfies `u'' + Q u = 0` with
`Q = radialProlateQ s c`, and `Q - c² (ξ')² = 1/(x²-1)²` exactly.  Rescaling by the Liouville
amplitude `h = √(c ξ')` and measuring derivatives against the phase `φ = c ξ` turns this into

```text
DDw + (1 + q) w = 0,        w = h u,   Dw = w'/φ',   DDw = (Dw)'/φ',
```

with `q` built from `h`, `Q` and the first two derivatives of the phase speed.  The first-order
term is eliminated exactly by `2 h' φ' = h φ''`, which is the defining property of the Liouville
amplitude.
-/

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

/-- The phase of the exterior oscillator. -/
def prolatePhase (s c x : ℝ) : ℝ := c * xiEndpointPhase s x

/-- Its speed. -/
def prolatePhaseSpeed (s c x : ℝ) : ℝ := c * xiSpeed s x

/-- The phase acceleration. -/
def prolatePhaseAccel (s c x : ℝ) : ℝ := c * xiSpeedDeriv s x

theorem hasDerivAt_prolatePhase {s c x : ℝ} (hs0 : 0 ≤ s) (hx : 1 < x) :
    HasDerivAt (prolatePhase s c) (prolatePhaseSpeed s c x) x :=
  (hasDerivAt_xiEndpointPhase hs0 hx).const_mul c

theorem hasDerivAt_prolatePhaseSpeed {s c x : ℝ} (hs1 : s ≤ 1) (hx : 1 < x) :
    HasDerivAt (prolatePhaseSpeed s c) (prolatePhaseAccel s c x) x :=
  (hasDerivAt_xiSpeed hs1 hx).const_mul c

theorem hasDerivAt_prolatePhaseAccel {s c x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    HasDerivAt (prolatePhaseAccel s c) (c * xiSpeedSecondDeriv s x) x :=
  (hasDerivAt_xiSpeedDeriv hs1 hx).const_mul c

theorem prolatePhaseSpeed_pos {s c x : ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hx : 1 < x) :
    0 < prolatePhaseSpeed s c x := by
  have := xiSpeed_pos hs1 hx
  rw [prolatePhaseSpeed]
  positivity

/-- The Liouville amplitude `h = √(φ')`. -/
def lgSpeedAmp (s c x : ℝ) : ℝ := Real.sqrt (prolatePhaseSpeed s c x)

/-- Its derivative. -/
def lgSpeedAmpDeriv (s c x : ℝ) : ℝ :=
  prolatePhaseAccel s c x / (2 * Real.sqrt (prolatePhaseSpeed s c x))

/-- Its second derivative, in the shape the quotient rule produces. -/
def lgSpeedAmpSecond (s c x : ℝ) : ℝ :=
  (c * xiSpeedSecondDeriv s x * (2 * Real.sqrt (prolatePhaseSpeed s c x))
      - prolatePhaseAccel s c x * (2 * lgSpeedAmpDeriv s c x))
    / (2 * Real.sqrt (prolatePhaseSpeed s c x)) ^ 2

theorem lgSpeedAmp_pos {s c x : ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hx : 1 < x) :
    0 < lgSpeedAmp s c x := Real.sqrt_pos.mpr (prolatePhaseSpeed_pos hs1 hc hx)

theorem hasDerivAt_lgSpeedAmp {s c x : ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hx : 1 < x) :
    HasDerivAt (lgSpeedAmp s c) (lgSpeedAmpDeriv s c x) x := by
  have hpos := prolatePhaseSpeed_pos hs1 hc hx
  have h := (hasDerivAt_prolatePhaseSpeed (by linarith) hx).sqrt (ne_of_gt hpos)
  have hfun : lgSpeedAmp s c = fun t : ℝ => Real.sqrt (prolatePhaseSpeed s c t) := by
    funext t
    rw [lgSpeedAmp]
  rw [hfun, lgSpeedAmpDeriv]
  exact h

theorem hasDerivAt_lgSpeedAmpDeriv {s c x : ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hx : 1 < x) :
    HasDerivAt (lgSpeedAmpDeriv s c) (lgSpeedAmpSecond s c x) x := by
  have hpos := prolatePhaseSpeed_pos hs1 hc hx
  have hsq : 0 < Real.sqrt (prolatePhaseSpeed s c x) := Real.sqrt_pos.mpr hpos
  have hden : HasDerivAt (fun t : ℝ => 2 * Real.sqrt (prolatePhaseSpeed s c t))
      (2 * lgSpeedAmpDeriv s c x) x := by
    have h := (hasDerivAt_lgSpeedAmp hs1 hc hx).const_mul (2 : ℝ)
    have hfun : (fun t : ℝ => 2 * lgSpeedAmp s c t)
        = fun t : ℝ => 2 * Real.sqrt (prolatePhaseSpeed s c t) := by
      funext t
      rw [lgSpeedAmp]
    rwa [hfun] at h
  have hne : (2 : ℝ) * Real.sqrt (prolatePhaseSpeed s c x) ≠ 0 := by positivity
  have h := (hasDerivAt_prolatePhaseAccel (c := c) hs1 hx).fun_div hden hne
  have hfun : lgSpeedAmpDeriv s c
      = fun t : ℝ => prolatePhaseAccel s c t / (2 * Real.sqrt (prolatePhaseSpeed s c t)) := by
    funext t
    rw [lgSpeedAmpDeriv]
  rw [hfun, lgSpeedAmpSecond]
  exact h

/-- **The Liouville amplitude eliminates the first-order term.**  This single identity is why the
phase parameterization produces a pure oscillator. -/
theorem two_mul_lgSpeedAmpDeriv_mul_speed {s c x : ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hx : 1 < x) :
    2 * lgSpeedAmpDeriv s c x * prolatePhaseSpeed s c x
      = lgSpeedAmp s c x * prolatePhaseAccel s c x := by
  have hpos := prolatePhaseSpeed_pos hs1 hc hx
  have hsq : 0 < Real.sqrt (prolatePhaseSpeed s c x) := Real.sqrt_pos.mpr hpos
  have hss : Real.sqrt (prolatePhaseSpeed s c x) * Real.sqrt (prolatePhaseSpeed s c x)
      = prolatePhaseSpeed s c x := Real.mul_self_sqrt hpos.le
  rw [lgSpeedAmpDeriv, lgSpeedAmp]
  field_simp
  linear_combination (-(prolatePhaseAccel s c x)) * hss

/-- The exterior oscillator attached to a radial mode: the normal-form solution rescaled by the
Liouville amplitude. -/
def prolateOsc (s c : ℝ) (R : ℝ → ℝ) (x : ℝ) : ℝ :=
  lgSpeedAmp s c x * prolateNormalFormSol R x

/-- Its derivative with respect to the phase. -/
def prolateOscD (s c : ℝ) (R DR : ℝ → ℝ) (x : ℝ) : ℝ :=
  (lgSpeedAmpDeriv s c x * prolateNormalFormSol R x
    + lgSpeedAmp s c x * prolateNormalFormSolDeriv R DR x) / prolatePhaseSpeed s c x

/-- Its second derivative with respect to the phase. -/
def prolateOscDD (s c : ℝ) (R DR DDR : ℝ → ℝ) (x : ℝ) : ℝ :=
  ((lgSpeedAmpSecond s c x * prolateNormalFormSol R x
      + 2 * (lgSpeedAmpDeriv s c x * prolateNormalFormSolDeriv R DR x)
      + lgSpeedAmp s c x * prolateNormalFormSolSecondDeriv R DR DDR x)
        * prolatePhaseSpeed s c x
    - (lgSpeedAmpDeriv s c x * prolateNormalFormSol R x
      + lgSpeedAmp s c x * prolateNormalFormSolDeriv R DR x) * prolatePhaseAccel s c x)
  / prolatePhaseSpeed s c x ^ 3

theorem hasDerivAt_prolateOsc {s c x : ℝ} {R DR : ℝ → ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hx : 1 < x) (hR : HasDerivAt R (DR x) x) :
    HasDerivAt (prolateOsc s c R) (prolatePhaseSpeed s c x * prolateOscD s c R DR x) x := by
  have hspos := prolatePhaseSpeed_pos hs1 hc hx
  have h := (hasDerivAt_lgSpeedAmp hs1 hc hx).fun_mul (hasDerivAt_prolateNormalFormSol hx hR)
  have hfun : prolateOsc s c R = fun t : ℝ => lgSpeedAmp s c t * prolateNormalFormSol R t := by
    funext t
    rw [prolateOsc]
  have hval : prolatePhaseSpeed s c x * prolateOscD s c R DR x
      = lgSpeedAmpDeriv s c x * prolateNormalFormSol R x
        + lgSpeedAmp s c x * prolateNormalFormSolDeriv R DR x := by
    rw [prolateOscD]
    field_simp
  rw [hfun, hval]
  exact h

theorem hasDerivAt_prolateOscD {s c x : ℝ} {R DR DDR : ℝ → ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hx : 1 < x) (hR : HasDerivAt R (DR x) x) (hDR : HasDerivAt DR (DDR x) x) :
    HasDerivAt (prolateOscD s c R DR)
      (prolatePhaseSpeed s c x * prolateOscDD s c R DR DDR x) x := by
  have hspos := prolatePhaseSpeed_pos hs1 hc hx
  have hnum : HasDerivAt (fun t : ℝ => lgSpeedAmpDeriv s c t * prolateNormalFormSol R t
      + lgSpeedAmp s c t * prolateNormalFormSolDeriv R DR t)
      (lgSpeedAmpSecond s c x * prolateNormalFormSol R x
          + lgSpeedAmpDeriv s c x * prolateNormalFormSolDeriv R DR x
        + (lgSpeedAmpDeriv s c x * prolateNormalFormSolDeriv R DR x
          + lgSpeedAmp s c x * prolateNormalFormSolSecondDeriv R DR DDR x)) x :=
    ((hasDerivAt_lgSpeedAmpDeriv hs1 hc hx).fun_mul
        (hasDerivAt_prolateNormalFormSol hx hR)).fun_add
      ((hasDerivAt_lgSpeedAmp hs1 hc hx).fun_mul
        (hasDerivAt_prolateNormalFormSolDeriv hx hR hDR))
  have h := hnum.fun_div (hasDerivAt_prolatePhaseSpeed (by linarith) hx) (ne_of_gt hspos)
  have hfun : prolateOscD s c R DR
      = fun t : ℝ => (lgSpeedAmpDeriv s c t * prolateNormalFormSol R t
        + lgSpeedAmp s c t * prolateNormalFormSolDeriv R DR t) / prolatePhaseSpeed s c t := by
    funext t
    rw [prolateOscD]
  have hval : prolatePhaseSpeed s c x * prolateOscDD s c R DR DDR x
      = ((lgSpeedAmpSecond s c x * prolateNormalFormSol R x
            + lgSpeedAmpDeriv s c x * prolateNormalFormSolDeriv R DR x
          + (lgSpeedAmpDeriv s c x * prolateNormalFormSolDeriv R DR x
            + lgSpeedAmp s c x * prolateNormalFormSolSecondDeriv R DR DDR x))
          * prolatePhaseSpeed s c x
        - (lgSpeedAmpDeriv s c x * prolateNormalFormSol R x
          + lgSpeedAmp s c x * prolateNormalFormSolDeriv R DR x) * prolatePhaseAccel s c x)
      / prolatePhaseSpeed s c x ^ 2 := by
    rw [prolateOscDD]
    field_simp
    ring
  rw [hfun, hval]
  exact h

/-- The perturbation of the exterior oscillator. -/
def prolateOscPotential (s c x : ℝ) : ℝ :=
  (lgSpeedAmp s c x * radialProlateQ s c x * prolatePhaseSpeed s c x
      + lgSpeedAmpDeriv s c x * prolatePhaseAccel s c x
      - lgSpeedAmpSecond s c x * prolatePhaseSpeed s c x)
    / (lgSpeedAmp s c x * prolatePhaseSpeed s c x ^ 3) - 1

/-- **The radial prolate mode is a perturbed oscillator in the phase parameterization.**  The
first-order term is eliminated exactly by the Liouville amplitude identity. -/
theorem prolateOsc_ode {s c x : ℝ} {R DR DDR : ℝ → ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hx : 1 < x)
    (hode : (x ^ 2 - 1) * DDR x + 2 * x * DR x - (s * c ^ 2 - c ^ 2 * x ^ 2) * R x = 0) :
    prolateOscDD s c R DR DDR x
      + (1 + prolateOscPotential s c x) * prolateOsc s c R x = 0 := by
  have hspos := prolatePhaseSpeed_pos hs1 hc hx
  have hhpos := lgSpeedAmp_pos hs1 hc hx
  have hamp := two_mul_lgSpeedAmpDeriv_mul_speed hs1 hc hx
  have hnf := prolate_normalForm_ode (s := s) (c := c) hx hode
  have hDDu : prolateNormalFormSolSecondDeriv R DR DDR x
      = -(radialProlateQ s c x * prolateNormalFormSol R x) := by linarith
  rw [prolateOscDD, prolateOscPotential, prolateOsc, hDDu]
  field_simp
  linear_combination (prolateNormalFormSolDeriv R DR x) * hamp

/-- **The perturbation in closed form.**  The pole contributes `1/(c² (ξ')² (x²-1)²)` and the
Liouville error is the Schwarzian combination `(3 (ξ'')² - 2 ξ''' ξ')/(4 c² (ξ')⁴)`. -/
theorem prolateOscPotential_eq {s c x : ℝ} (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hx : 1 < x) :
    prolateOscPotential s c x
      = 1 / (c ^ 2 * xiSpeed s x ^ 2 * (x ^ 2 - 1) ^ 2)
        + (3 * xiSpeedDeriv s x ^ 2 - 2 * xiSpeedSecondDeriv s x * xiSpeed s x)
          / (4 * c ^ 2 * xiSpeed s x ^ 4) := by
  have hsp : 0 < xiSpeed s x := xiSpeed_pos hs1 hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hspd : (0 : ℝ) < c * xiSpeed s x := by positivity
  have hQ : radialProlateQ s c x = c ^ 2 * xiSpeed s x ^ 2 + 1 / (x ^ 2 - 1) ^ 2 := by
    have := radialProlateQ_sub_comparison (s := s) (c := c) (x := x) hs1 hx
    linarith
  rw [prolateOscPotential, lgSpeedAmpSecond, lgSpeedAmpDeriv, lgSpeedAmp, prolatePhaseSpeed,
    prolatePhaseAccel, hQ]
  set P : ℝ := Real.sqrt (c * xiSpeed s x) with hPdef
  have hP0 : 0 < P := Real.sqrt_pos.mpr hspd
  have hP : P ^ 2 = c * xiSpeed s x := Real.sq_sqrt hspd.le
  field_simp
  linear_combination ((x ^ 2 - 1) ^ 2
      * ((8 * xiSpeed s x * xiSpeedSecondDeriv s x - 12 * xiSpeedDeriv s x ^ 2)
          * (P ^ 2 + c * xiSpeed s x)
        + 8 * c * (xiSpeed s x * xiSpeedDeriv s x ^ 2
          - xiSpeed s x ^ 2 * xiSpeedSecondDeriv s x))) * hP

theorem abs_xiSpeedDeriv_le_two_div {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 2 ≤ x) :
    |xiSpeedDeriv s x| ≤ 2 / x ^ 3 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hd34 : (3 / 4) * x ^ 2 ≤ x ^ 2 - 1 := by nlinarith
  have hsp1 : (1 : ℝ) ≤ xiSpeed s x := one_le_xiSpeed (by linarith) hx1
  have hden : (0 : ℝ) < (x ^ 2 - 1) ^ 2 * xiSpeed s x := by positivity
  rw [xiSpeedDeriv, abs_div, abs_of_pos hden, div_le_div_iff₀ hden (by positivity)]
  have hnum : |x * (s - 1)| ≤ x := by
    rw [abs_mul, abs_of_pos hx0, abs_of_nonpos (by linarith : s - 1 ≤ 0)]
    nlinarith [hx0]
  have hlow : (9 / 16) * x ^ 4 ≤ (x ^ 2 - 1) ^ 2 * xiSpeed s x := by
    nlinarith [hd34, hsp1, sq_nonneg x, hd.le]
  nlinarith [hnum, hlow, hx0, pow_pos hx0 3]

theorem abs_xiSpeedSecondDeriv_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 2 ≤ x) :
    |xiSpeedSecondDeriv s x| ≤ 32 / x ^ 4 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hd3 : (3 : ℝ) ≤ x ^ 2 - 1 := by nlinarith
  have hd34 : (3 / 4) * x ^ 2 ≤ x ^ 2 - 1 := by nlinarith
  have hsp1 : (1 : ℝ) ≤ xiSpeed s x := one_le_xiSpeed (by linarith) hx1
  have hsp2 : xiSpeed s x ≤ 2 := xiSpeed_le_two hs0 hx
  have hdd := abs_xiSpeedDeriv_le_two_div hs0 hs1 hx
  have hden : (0 : ℝ) < ((x ^ 2 - 1) ^ 2 * xiSpeed s x) ^ 2 := by positivity
  rw [xiSpeedSecondDeriv, abs_div, abs_of_pos hden, div_le_div_iff₀ hden (by positivity)]
  -- bound the numerator
  have hA : |(s - 1) * ((x ^ 2 - 1) ^ 2 * xiSpeed s x)| ≤ 2 * (x ^ 2 - 1) ^ 2 := by
    rw [abs_mul, abs_of_nonpos (by linarith : s - 1 ≤ 0),
      abs_of_pos (by positivity : (0 : ℝ) < (x ^ 2 - 1) ^ 2 * xiSpeed s x)]
    have h1 : -(s - 1) ≤ 1 := by linarith
    have hsq : (0 : ℝ) ≤ (x ^ 2 - 1) ^ 2 := by positivity
    calc -(s - 1) * ((x ^ 2 - 1) ^ 2 * xiSpeed s x)
        ≤ 1 * ((x ^ 2 - 1) ^ 2 * 2) := by
          refine mul_le_mul h1 ?_ (by positivity) zero_le_one
          exact mul_le_mul_of_nonneg_left hsp2 hsq
      _ = 2 * (x ^ 2 - 1) ^ 2 := by ring
  have hB : |x * (s - 1) * (4 * x * (x ^ 2 - 1) * xiSpeed s x
      + (x ^ 2 - 1) ^ 2 * xiSpeedDeriv s x)|
      ≤ 8 * x ^ 2 * (x ^ 2 - 1) + (x ^ 2 - 1) ^ 2 * (2 / x ^ 3) * x := by
    rw [abs_mul, abs_mul, abs_of_pos hx0, abs_of_nonpos (by linarith : s - 1 ≤ 0)]
    have hinner : |4 * x * (x ^ 2 - 1) * xiSpeed s x + (x ^ 2 - 1) ^ 2 * xiSpeedDeriv s x|
        ≤ 8 * x * (x ^ 2 - 1) + (x ^ 2 - 1) ^ 2 * (2 / x ^ 3) := by
      refine le_trans (abs_add_le _ _) ?_
      have h1 : |4 * x * (x ^ 2 - 1) * xiSpeed s x| ≤ 8 * x * (x ^ 2 - 1) := by
        have hnn : (0 : ℝ) ≤ 4 * x * (x ^ 2 - 1) * xiSpeed s x := by
          have := le_trans zero_le_one hsp1
          positivity
        rw [abs_of_nonneg hnn]
        have := mul_le_mul_of_nonneg_left hsp2
          (by positivity : (0 : ℝ) ≤ 4 * x * (x ^ 2 - 1))
        linarith [this]
      have h2 : |(x ^ 2 - 1) ^ 2 * xiSpeedDeriv s x| ≤ (x ^ 2 - 1) ^ 2 * (2 / x ^ 3) := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (x ^ 2 - 1) ^ 2)]
        exact mul_le_mul_of_nonneg_left hdd (by positivity)
      linarith
    have hsx : (0 : ℝ) ≤ 8 * x * (x ^ 2 - 1) + (x ^ 2 - 1) ^ 2 * (2 / x ^ 3) := by positivity
    calc x * -(s - 1) * |4 * x * (x ^ 2 - 1) * xiSpeed s x
            + (x ^ 2 - 1) ^ 2 * xiSpeedDeriv s x|
        ≤ x * 1 * (8 * x * (x ^ 2 - 1) + (x ^ 2 - 1) ^ 2 * (2 / x ^ 3)) := by
          refine mul_le_mul ?_ hinner (abs_nonneg _) (by positivity)
          nlinarith [hx0.le, hs0]
      _ = 8 * x ^ 2 * (x ^ 2 - 1) + (x ^ 2 - 1) ^ 2 * (2 / x ^ 3) * x := by ring
  have hsplit : |(s - 1) * ((x ^ 2 - 1) ^ 2 * xiSpeed s x)
      - x * (s - 1) * (4 * x * (x ^ 2 - 1) * xiSpeed s x
        + (x ^ 2 - 1) ^ 2 * xiSpeedDeriv s x)|
      ≤ 2 * (x ^ 2 - 1) ^ 2 + (8 * x ^ 2 * (x ^ 2 - 1) + (x ^ 2 - 1) ^ 2 * (2 / x ^ 3) * x) :=
    le_trans (abs_sub _ _) (by linarith [hA, hB])
  have hlow : (x ^ 2 - 1) ^ 4 ≤ ((x ^ 2 - 1) ^ 2 * xiSpeed s x) ^ 2 := by
    have heq : ((x ^ 2 - 1) ^ 2 * xiSpeed s x) ^ 2
        = (x ^ 2 - 1) ^ 4 * xiSpeed s x ^ 2 := by ring
    rw [heq]
    have hsq1 : (1 : ℝ) ≤ xiSpeed s x ^ 2 := by nlinarith [hsp1]
    calc (x ^ 2 - 1) ^ 4 = (x ^ 2 - 1) ^ 4 * 1 := by ring
      _ ≤ (x ^ 2 - 1) ^ 4 * xiSpeed s x ^ 2 :=
        mul_le_mul_of_nonneg_left hsq1 (pow_pos hd 4).le
  have hpow : (x ^ 2 - 1) ^ 2 * (2 / x ^ 3) * x = 2 * (x ^ 2 - 1) ^ 2 / x ^ 2 := by
    field_simp
  rw [hpow] at hsplit
  have hkey : (2 * (x ^ 2 - 1) ^ 2 + (8 * x ^ 2 * (x ^ 2 - 1) + 2 * (x ^ 2 - 1) ^ 2 / x ^ 2))
      * x ^ 4 ≤ 32 * (x ^ 2 - 1) ^ 4 := by
    have hq : 2 * (x ^ 2 - 1) ^ 2 / x ^ 2 * x ^ 4 = 2 * (x ^ 2 - 1) ^ 2 * x ^ 2 := by
      field_simp
    have hx2 : x ^ 2 ≤ (4 / 3) * (x ^ 2 - 1) := by linarith [hd34]
    nlinarith [hx2, hd3, hd.le, sq_nonneg (x ^ 2 - 1), pow_pos hd 3, pow_pos hd 2,
      mul_pos hd hd, hq]
  nlinarith [hsplit, hlow, hkey, pow_pos hx0 4, hden]


/-- **The perturbation is admissible.**  `|q| ≤ 35/φ²` on `[2, ∞)`: the pole and the Liouville
error both decay like `x^{-4}`, which is comfortably inside the `φ^{-2}` budget that Grönwall
requires. -/
theorem abs_prolateOscPotential_le {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hx : 2 ≤ x) :
    |prolateOscPotential s c x| ≤ 35 / prolatePhase s c x ^ 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hd34 : (3 / 4) * x ^ 2 ≤ x ^ 2 - 1 := by nlinarith
  have hsp1 : (1 : ℝ) ≤ xiSpeed s x := one_le_xiSpeed (by linarith) hx1
  have hsp2 : xiSpeed s x ≤ 2 := xiSpeed_le_two hs0 hx
  have hsp0 : (0 : ℝ) < xiSpeed s x := by linarith
  have hdd := abs_xiSpeedDeriv_le_two_div hs0 hs1 hx
  have hDD := abs_xiSpeedSecondDeriv_le hs0 hs1 hx
  have hx4 : (0 : ℝ) < x ^ 4 := by positivity
  rw [prolateOscPotential_eq hs1 hc hx1]
  -- the pole term
  have hApos : (0 : ℝ) < 1 / (c ^ 2 * xiSpeed s x ^ 2 * (x ^ 2 - 1) ^ 2) := by positivity
  have hA : |1 / (c ^ 2 * xiSpeed s x ^ 2 * (x ^ 2 - 1) ^ 2)| ≤ 2 / (c ^ 2 * x ^ 4) := by
    rw [abs_of_pos hApos, div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq1 : (1 : ℝ) ≤ xiSpeed s x ^ 2 := by nlinarith [hsp1]
    have hd2 : (9 / 16) * x ^ 4 ≤ (x ^ 2 - 1) ^ 2 := by
      nlinarith [hd34, hd.le, sq_nonneg (x ^ 2), hx4.le]
    have hlow : (9 / 16) * x ^ 4 ≤ xiSpeed s x ^ 2 * (x ^ 2 - 1) ^ 2 := by
      calc (9 / 16) * x ^ 4 ≤ (x ^ 2 - 1) ^ 2 := hd2
        _ = 1 * (x ^ 2 - 1) ^ 2 := by ring
        _ ≤ xiSpeed s x ^ 2 * (x ^ 2 - 1) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq1 (by positivity)
    nlinarith [hlow, sq_nonneg c, hx4, mul_pos (mul_pos hc hc) hx4]
  -- the Liouville error term
  have hnum : |3 * xiSpeedDeriv s x ^ 2 - 2 * xiSpeedSecondDeriv s x * xiSpeed s x|
      ≤ 12 / x ^ 6 + 128 / x ^ 4 := by
    refine le_trans (abs_sub _ _) ?_
    have h1 : |3 * xiSpeedDeriv s x ^ 2| ≤ 12 / x ^ 6 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_pow, sq_abs]
      have hsq : |xiSpeedDeriv s x| ^ 2 ≤ (2 / x ^ 3) ^ 2 := by
        nlinarith [hdd, abs_nonneg (xiSpeedDeriv s x)]
      have hval : (2 / x ^ 3 : ℝ) ^ 2 = 4 / x ^ 6 := by
        field_simp
        ring
      rw [hval, sq_abs] at hsq
      have h12 : (12 : ℝ) / x ^ 6 = 3 * (4 / x ^ 6) := by ring
      linarith [hsq, h12]
    have h2 : |2 * xiSpeedSecondDeriv s x * xiSpeed s x| ≤ 128 / x ^ 4 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hsp0]
      have hstep : 2 * |xiSpeedSecondDeriv s x| * xiSpeed s x ≤ 2 * (32 / x ^ 4) * 2 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hDD (by norm_num)) hsp2 hsp0.le
          (by positivity)
      have hval : (2 : ℝ) * (32 / x ^ 4) * 2 = 128 / x ^ 4 := by ring
      linarith [hstep, hval]
    linarith
  have hB : |(3 * xiSpeedDeriv s x ^ 2 - 2 * xiSpeedSecondDeriv s x * xiSpeed s x)
      / (4 * c ^ 2 * xiSpeed s x ^ 4)| ≤ 33 / (c ^ 2 * x ^ 4) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * c ^ 2 * xiSpeed s x ^ 4),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hsix : 12 / x ^ 6 ≤ 3 / x ^ 4 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hx4, hx0, pow_pos hx0 6]
    have h131 : (3 : ℝ) / x ^ 4 + 128 / x ^ 4 = 131 / x ^ 4 := by ring
    have htop : |3 * xiSpeedDeriv s x ^ 2 - 2 * xiSpeedSecondDeriv s x * xiSpeed s x|
        ≤ 131 / x ^ 4 := by linarith [hnum, hsix, h131]
    have hsp2' : (1 : ℝ) ≤ xiSpeed s x ^ 2 := by nlinarith [hsp1]
    have hsp4 : (1 : ℝ) ≤ xiSpeed s x ^ 4 := by
      have heq : xiSpeed s x ^ 4 = (xiSpeed s x ^ 2) ^ 2 := by ring
      rw [heq]
      nlinarith [hsp2']
    calc |3 * xiSpeedDeriv s x ^ 2 - 2 * xiSpeedSecondDeriv s x * xiSpeed s x|
          * (c ^ 2 * x ^ 4)
        ≤ 131 / x ^ 4 * (c ^ 2 * x ^ 4) :=
          mul_le_mul_of_nonneg_right htop (by positivity)
      _ = 131 * c ^ 2 := by field_simp
      _ ≤ 33 * (4 * c ^ 2 * xiSpeed s x ^ 4) := by nlinarith [hsp4, mul_pos hc hc]
  -- combine, then compare with the phase
  have htotal : |1 / (c ^ 2 * xiSpeed s x ^ 2 * (x ^ 2 - 1) ^ 2)
      + (3 * xiSpeedDeriv s x ^ 2 - 2 * xiSpeedSecondDeriv s x * xiSpeed s x)
        / (4 * c ^ 2 * xiSpeed s x ^ 4)| ≤ 35 / (c ^ 2 * x ^ 4) := by
    refine le_trans (abs_add_le _ _) ?_
    have hsum : (2 : ℝ) / (c ^ 2 * x ^ 4) + 33 / (c ^ 2 * x ^ 4) = 35 / (c ^ 2 * x ^ 4) := by
      ring
    linarith [hA, hB, hsum]
  refine le_trans htotal ?_
  have hphase : prolatePhase s c x ≤ c * x := by
    have hb := (xiEndpointPhase_bounds hs0 (by linarith : s ≤ 1) hx1.le).2
    have hsx : Real.sqrt (x ^ 2 - 1) ≤ x := by
      have h1 : Real.sqrt (x ^ 2 - 1) ≤ Real.sqrt (x ^ 2) := Real.sqrt_le_sqrt (by linarith)
      rwa [Real.sqrt_sq hx0.le] at h1
    rw [prolatePhase]
    exact mul_le_mul_of_nonneg_left (le_trans hb hsx) hc.le
  have hp0 : 0 < prolatePhase s c x := by
    have := xiEndpointPhase_pos hs0 hs1 hx1
    rw [prolatePhase]
    positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : prolatePhase s c x ^ 2 ≤ c ^ 2 * x ^ 2 := by nlinarith [hphase, hp0.le, hc.le]
  nlinarith [hsq, hx0, hx4, sq_nonneg c, mul_pos hc hc]


/-- **The exact radial mode satisfies every hypothesis of the phase energy method.** -/
theorem prolate_isPhaseOscillator {s c a : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (ha : 2 ≤ a)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    (∀ t : ℝ, a ≤ t → HasDerivAt (prolatePhase s c) (prolatePhaseSpeed s c t) t)
      ∧ (∀ t : ℝ, a ≤ t → 0 < prolatePhase s c t)
      ∧ (∀ t : ℝ, a ≤ t → 0 ≤ prolatePhaseSpeed s c t)
      ∧ (∀ t : ℝ, a ≤ t → HasDerivAt (prolateOsc s c R)
          (prolatePhaseSpeed s c t * prolateOscD s c R DR t) t)
      ∧ (∀ t : ℝ, a ≤ t → HasDerivAt (prolateOscD s c R DR)
          (prolatePhaseSpeed s c t * prolateOscDD s c R DR DDR t) t)
      ∧ (∀ t : ℝ, a ≤ t → prolateOscDD s c R DR DDR t
          + (1 + prolateOscPotential s c t) * prolateOsc s c R t = 0)
      ∧ ∀ t : ℝ, a ≤ t → |prolateOscPotential s c t| ≤ 35 / prolatePhase s c t ^ 2 := by
  have ht1 : ∀ t : ℝ, a ≤ t → (1 : ℝ) < t := fun t ht => by linarith
  have ht2 : ∀ t : ℝ, a ≤ t → (2 : ℝ) ≤ t := fun t ht => by linarith
  refine ⟨fun t ht => hasDerivAt_prolatePhase hs0 (ht1 t ht),
    fun t ht => ?_, fun t ht => (prolatePhaseSpeed_pos hs1 hc (ht1 t ht)).le,
    fun t ht => hasDerivAt_prolateOsc hs1 hc (ht1 t ht) (hR t),
    fun t ht => hasDerivAt_prolateOscD hs1 hc (ht1 t ht) (hR t) (hDR t),
    fun t ht => prolateOsc_ode hs1 hc (ht1 t ht) (hode t),
    fun t ht => abs_prolateOscPotential_le hs0 hs1 hc (ht2 t ht)⟩
  have := xiEndpointPhase_pos hs0 hs1 (ht1 t ht)
  rw [prolatePhase]
  positivity

/-- **The exact radial mode has bounded two-branch coefficients.**  This is the statement the
exterior estimate consumes, for the mode itself rather than for the Bessel model: no transfer
error appears, because no transfer is made. -/
theorem abs_prolateOscCoeff_le {s c a x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (ha : 2 ≤ a) (hax : a ≤ x)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |phaseCosCoeff (prolateOsc s c R) (prolateOscD s c R DR) (prolatePhase s c) x|
        ≤ Real.sqrt (phaseEnergy (prolateOsc s c R) (prolateOscD s c R DR) a
          * Real.exp (35 / prolatePhase s c a))
      ∧ |phaseSinCoeff (prolateOsc s c R) (prolateOscD s c R DR) (prolatePhase s c) x|
        ≤ Real.sqrt (phaseEnergy (prolateOsc s c R) (prolateOscD s c R DR) a
          * Real.exp (35 / prolatePhase s c a)) := by
  obtain ⟨hφd, hφpos, hDφ, hw, hDw, hodew, hq⟩ :=
    prolate_isPhaseOscillator (a := a) hs0 hs1 hc ha hR hDR hode
  exact abs_phaseCoeff_le_base (w := prolateOsc s c R) (Dw := prolateOscD s c R DR)
    (DDw := prolateOscDD s c R DR DDR) (q := prolateOscPotential s c)
    (φ := prolatePhase s c) (Dφ := prolatePhaseSpeed s c) (κ := 35)
    hax (by norm_num) hφd hφpos hDφ hw hDw hodew hq


end GaloisForLFunctions.RHTower
