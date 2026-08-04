import GaloisForLFunctions.RHTower.CCMFirstRowVanDerCorputBlocks
import GaloisForLFunctions.RHTower.BesselJZeroODE

/-!
# The pole-uniform comparison equation of the first-row model

Dunster's pole-uniform approximation compares the radial prolate equation with a Bessel equation in the
Liouville–Green variable.  The comparison itself is an exact identity, and this file proves it: the model

```text
V(x) = J_0(c xi_s(x))
```

satisfies the second-order equation

```text
V'' + (xi'/xi - xi''/xi') V' + c² (xi')² V = 0
```

exactly, for every `c` and every `x > 1`, with no asymptotics anywhere.  This is the equation that
Dunster's expansion compares the true radial equation with: the two differ by a potential of size `O(1)`
rather than `O(c²)`, which is what makes the relative error `O(c^{-1})`.

The proof is the chain rule together with Bessel's equation `besselJ0_ode`: the two `J_0'` terms
produced by the second derivative and by the first-order coefficient cancel identically, and the two
`J_0` terms cancel against `c²(xi')²`.

* `lgBesselModel`, `lgBesselModelDeriv`, `lgBesselModelSecondDeriv` — the model and its two derivatives.
* `hasDerivAt_lgBesselModel`, `hasDerivAt_lgBesselModelDeriv` — that they are the derivatives.
* **`lgBesselModel_ode`** — the comparison equation.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set

/-- The Liouville–Green Bessel model `V(x) = J_0(c xi_s(x))`. -/
def lgBesselModel (s c x : ℝ) : ℝ := besselJ0 (c * xiEndpointPhase s x)

/-- Its derivative. -/
def lgBesselModelDeriv (s c x : ℝ) : ℝ :=
  besselJ0Deriv (c * xiEndpointPhase s x) * (c * xiSpeed s x)

/-- Its second derivative. -/
def lgBesselModelSecondDeriv (s c x : ℝ) : ℝ :=
  besselJ0SecondDeriv (c * xiEndpointPhase s x) * (c * xiSpeed s x) ^ 2
    + besselJ0Deriv (c * xiEndpointPhase s x) * (c * xiSpeedDeriv s x)

theorem hasDerivAt_lgBesselModel {s c x : ℝ} (hs0 : 0 ≤ s) (hx : 1 < x) :
    HasDerivAt (lgBesselModel s c) (lgBesselModelDeriv s c x) x := by
  have hinner : HasDerivAt (fun t : ℝ => c * xiEndpointPhase s t) (c * xiSpeed s x) x :=
    (hasDerivAt_xiEndpointPhase hs0 hx).const_mul c
  have h := (hasDerivAt_besselJ0 (c * xiEndpointPhase s x)).comp x hinner
  exact h

theorem hasDerivAt_lgBesselModelDeriv {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hx : 1 < x) :
    HasDerivAt (lgBesselModelDeriv s c) (lgBesselModelSecondDeriv s c x) x := by
  have hinner : HasDerivAt (fun t : ℝ => c * xiEndpointPhase s t) (c * xiSpeed s x) x :=
    (hasDerivAt_xiEndpointPhase hs0 hx).const_mul c
  have h1 := (hasDerivAt_besselJ0Deriv (c * xiEndpointPhase s x)).comp x hinner
  have h2 : HasDerivAt (fun t : ℝ => c * xiSpeed s t) (c * xiSpeedDeriv s x) x :=
    (hasDerivAt_xiSpeed hs1 hx).const_mul c
  have h := h1.fun_mul h2
  simp only [Function.comp_apply] at h
  have hval : besselJ0SecondDeriv (c * xiEndpointPhase s x) * (c * xiSpeed s x)
        * (c * xiSpeed s x)
      + besselJ0Deriv (c * xiEndpointPhase s x) * (c * xiSpeedDeriv s x)
      = lgBesselModelSecondDeriv s c x := by
    rw [lgBesselModelSecondDeriv]
    ring
  rw [hval] at h
  exact h

/-- **The pole-uniform comparison equation.**  The Bessel model solves it exactly: the `J_0'` term
produced by the second derivative cancels against the first-order coefficient, and the `J_0` terms
cancel against `c²(xi')²`.  This is the equation Dunster's expansion compares the true radial prolate
equation with. -/
theorem lgBesselModel_ode {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) (hc : 0 < c) :
    lgBesselModelSecondDeriv s c x
        + (xiSpeed s x / xiEndpointPhase s x - xiSpeedDeriv s x / xiSpeed s x)
          * lgBesselModelDeriv s c x
        + c ^ 2 * xiSpeed s x ^ 2 * lgBesselModel s c x = 0 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have h1 : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have h2 : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hspeed : 0 < xiSpeed s x := by
    rw [xiSpeed]
    exact Real.sqrt_pos.mpr (div_pos h2 h1)
  have hphase : 0 < xiEndpointPhase s x := by
    have hlow := (xiEndpointPhase_bounds hs0 (by linarith) hx.le).1
    have : (0 : ℝ) < Real.sqrt (1 - s) * Real.sqrt (x ^ 2 - 1) := by
      have hs : (0 : ℝ) < 1 - s := by linarith
      positivity
    linarith
  have hzeta : c * xiEndpointPhase s x ≠ 0 := by positivity
  have hode := besselJ0_ode hzeta
  -- the second Bessel derivative in terms of the first two
  have hsecond : besselJ0SecondDeriv (c * xiEndpointPhase s x)
      = -(besselJ0Deriv (c * xiEndpointPhase s x) / (c * xiEndpointPhase s x))
        - besselJ0 (c * xiEndpointPhase s x) := by linarith [hode]
  rw [lgBesselModelSecondDeriv, lgBesselModelDeriv, lgBesselModel, hsecond]
  have hphne : xiEndpointPhase s x ≠ 0 := hphase.ne'
  have hspne : xiSpeed s x ≠ 0 := hspeed.ne'
  have hcne : c ≠ 0 := hc.ne'
  field_simp
  ring

/-! ## The weighted Wronskian transport law -/

/-- The first-order coefficient of the comparison equation, `xi'/xi - xi''/xi'`. -/
def lgFirstOrderCoeff (s x : ℝ) : ℝ :=
  xiSpeed s x / xiEndpointPhase s x - xiSpeedDeriv s x / xiSpeed s x

/-- The Liouville weight of the comparison equation, `m = xi/xi'`.  It is the exact integrating factor:
`m' = m · (xi'/xi - xi''/xi')`. -/
def lgWeight (s x : ℝ) : ℝ := xiEndpointPhase s x / xiSpeed s x

theorem xiSpeed_pos {s x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x) : 0 < xiSpeed s x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have h1 : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have h2 : (0 : ℝ) < x ^ 2 - s := by nlinarith
  rw [xiSpeed]
  exact Real.sqrt_pos.mpr (div_pos h2 h1)

theorem xiEndpointPhase_pos {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    0 < xiEndpointPhase s x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have h1 : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hlow := (xiEndpointPhase_bounds hs0 (by linarith) hx.le).1
  have hpos : (0 : ℝ) < Real.sqrt (1 - s) * Real.sqrt (x ^ 2 - 1) := by
    have hs : (0 : ℝ) < 1 - s := by linarith
    positivity
  linarith

/-- The weight is the integrating factor of the comparison equation. -/
theorem hasDerivAt_lgWeight {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    HasDerivAt (lgWeight s) (lgWeight s x * lgFirstOrderCoeff s x) x := by
  have hsp := xiSpeed_pos hs1 hx
  have hph := xiEndpointPhase_pos hs0 hs1 hx
  have h1 : HasDerivAt (xiEndpointPhase s) (xiSpeed s x) x := hasDerivAt_xiEndpointPhase hs0 hx
  have h2 : HasDerivAt (xiSpeed s) (xiSpeedDeriv s x) x := hasDerivAt_xiSpeed (by linarith) hx
  have h := h1.fun_div h2 hsp.ne'
  have hval : (xiSpeed s x * xiSpeed s x - xiEndpointPhase s x * xiSpeedDeriv s x)
        / xiSpeed s x ^ 2
      = lgWeight s x * lgFirstOrderCoeff s x := by
    rw [lgWeight, lgFirstOrderCoeff]
    field_simp
  rw [hval] at h
  exact h

/-- **The weighted Wronskian transport law.**  Two solutions of the comparison equation with the same
first-order coefficient and potentials differing by `a - b` have weighted Wronskian with derivative
`m (a - b) U V`.  Every hypothesis is at the single point `x`, and the identity is exact: this is the
Volterra kernel of Dunster's comparison, before any estimate. -/
theorem hasDerivAt_weightedWronskian {s c x a b : ℝ} {U DU V DV : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hU : HasDerivAt U (DU x) x)
    (hDU : HasDerivAt DU
      (-(lgFirstOrderCoeff s x) * DU x - (c ^ 2 * xiSpeed s x ^ 2 + a) * U x) x)
    (hV : HasDerivAt V (DV x) x)
    (hDV : HasDerivAt DV
      (-(lgFirstOrderCoeff s x) * DV x - (c ^ 2 * xiSpeed s x ^ 2 + b) * V x) x) :
    HasDerivAt (fun t : ℝ => lgWeight s t * (U t * DV t - DU t * V t))
      (lgWeight s x * (a - b) * (U x * V x)) x := by
  have hm := hasDerivAt_lgWeight hs0 hs1 hx
  have hw : HasDerivAt (fun t : ℝ => U t * DV t - DU t * V t)
      (-(lgFirstOrderCoeff s x) * (U x * DV x - DU x * V x) + (a - b) * (U x * V x)) x := by
    have h1 := hU.fun_mul hDV
    have h2 := hDU.fun_mul hV
    have h := h1.fun_sub h2
    have hval : DU x * DV x
          + U x * (-(lgFirstOrderCoeff s x) * DV x - (c ^ 2 * xiSpeed s x ^ 2 + b) * V x)
        - ((-(lgFirstOrderCoeff s x) * DU x - (c ^ 2 * xiSpeed s x ^ 2 + a) * U x) * V x
          + DU x * DV x)
        = -(lgFirstOrderCoeff s x) * (U x * DV x - DU x * V x) + (a - b) * (U x * V x) := by
      ring
    rw [hval] at h
    exact h
  have h := hm.fun_mul hw
  have hval : lgWeight s x * lgFirstOrderCoeff s x * (U x * DV x - DU x * V x)
      + lgWeight s x * (-(lgFirstOrderCoeff s x) * (U x * DV x - DU x * V x)
        + (a - b) * (U x * V x))
      = lgWeight s x * (a - b) * (U x * V x) := by ring
  rw [hval] at h
  exact h

/-- The model in the form required by the transport law: it solves the comparison equation with zero
potential defect. -/
theorem hasDerivAt_lgBesselModelDeriv_ode {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hc : 0 < c) :
    HasDerivAt (lgBesselModelDeriv s c)
      (-(lgFirstOrderCoeff s x) * lgBesselModelDeriv s c x
        - (c ^ 2 * xiSpeed s x ^ 2 + 0) * lgBesselModel s c x) x := by
  have h := hasDerivAt_lgBesselModelDeriv (s := s) (c := c) hs0 (by linarith : s ≤ 1) hx
  have hode := lgBesselModel_ode hs0 hs1 hx hc
  have hval : lgBesselModelSecondDeriv s c x
      = -(lgFirstOrderCoeff s x) * lgBesselModelDeriv s c x
        - (c ^ 2 * xiSpeed s x ^ 2 + 0) * lgBesselModel s c x := by
    rw [lgFirstOrderCoeff]
    linarith [hode]
  rw [hval] at h
  exact h

/-- **The exact deviation law of Dunster's comparison.**  For any solution `U` of the true equation —
the comparison equation with potential defect `a` — the weighted Wronskian against the Bessel model has
derivative exactly `m a U V`.  Integrating this is the Volterra equation of the pole-uniform expansion;
the `O(c^{-1})` of `(14)` is the size of that integral. -/
theorem hasDerivAt_lgBesselWronskian {s c x a : ℝ} {U DU : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) (hc : 0 < c)
    (hU : HasDerivAt U (DU x) x)
    (hDU : HasDerivAt DU
      (-(lgFirstOrderCoeff s x) * DU x - (c ^ 2 * xiSpeed s x ^ 2 + a) * U x) x) :
    HasDerivAt (fun t : ℝ =>
        lgWeight s t * (U t * lgBesselModelDeriv s c t - DU t * lgBesselModel s c t))
      (lgWeight s x * a * (U x * lgBesselModel s c x)) x := by
  have h := hasDerivAt_weightedWronskian (s := s) (c := c) (a := a) (b := 0) hs0 hs1 hx hU hDU
    (hasDerivAt_lgBesselModel hs0 hx) (hasDerivAt_lgBesselModelDeriv_ode hs0 hs1 hx hc)
  have hval : lgWeight s x * (a - 0) * (U x * lgBesselModel s c x)
      = lgWeight s x * a * (U x * lgBesselModel s c x) := by ring
  rw [hval] at h
  exact h

/-- **Abel's identity for the comparison equation.**  Two solutions with no potential defect have
constant weighted Wronskian.  This is the normalisation the Green kernel of Dunster's comparison is
built from. -/
theorem hasDerivAt_lgWronskian_const {s c x : ℝ} {V DV W DW : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hV : HasDerivAt V (DV x) x)
    (hDV : HasDerivAt DV
      (-(lgFirstOrderCoeff s x) * DV x - (c ^ 2 * xiSpeed s x ^ 2 + 0) * V x) x)
    (hW : HasDerivAt W (DW x) x)
    (hDW : HasDerivAt DW
      (-(lgFirstOrderCoeff s x) * DW x - (c ^ 2 * xiSpeed s x ^ 2 + 0) * W x) x) :
    HasDerivAt (fun t : ℝ => lgWeight s t * (V t * DW t - DV t * W t)) 0 x := by
  have h := hasDerivAt_weightedWronskian (s := s) (c := c) (a := 0) (b := 0) hs0 hs1 hx hV hDV hW hDW
  have hval : lgWeight s x * (0 - 0) * (V x * W x) = 0 := by ring
  rw [hval] at h
  exact h

end GaloisForLFunctions.RHTower

end
