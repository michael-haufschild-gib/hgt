import GaloisForLFunctions.RHTower.CCMFirstRowVanDerCorputBlocks
import GaloisForLFunctions.RHTower.BesselJZeroSecondSolution

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

/-! ## The second model solution and the Green kernel normalisation -/

/-- The second Liouville–Green model solution `K(c xi_s(x))`. -/
def lgBesselModel2 (s c x : ℝ) : ℝ := besselK (c * xiEndpointPhase s x)

/-- Its derivative. -/
def lgBesselModel2Deriv (s c x : ℝ) : ℝ :=
  besselKDeriv (c * xiEndpointPhase s x) * (c * xiSpeed s x)

/-- Its second derivative. -/
def lgBesselModel2SecondDeriv (s c x : ℝ) : ℝ :=
  besselKSecondDeriv (c * xiEndpointPhase s x) * (c * xiSpeed s x) ^ 2
    + besselKDeriv (c * xiEndpointPhase s x) * (c * xiSpeedDeriv s x)

theorem hasDerivAt_lgBesselModel2 {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hc : 0 < c) : HasDerivAt (lgBesselModel2 s c) (lgBesselModel2Deriv s c x) x := by
  have hph : 0 < c * xiEndpointPhase s x := by
    have := xiEndpointPhase_pos hs0 hs1 hx
    positivity
  have hinner : HasDerivAt (fun t : ℝ => c * xiEndpointPhase s t) (c * xiSpeed s x) x :=
    (hasDerivAt_xiEndpointPhase hs0 hx).const_mul c
  have h := (hasDerivAt_besselK hph).comp x hinner
  exact h

theorem hasDerivAt_lgBesselModel2Deriv {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hc : 0 < c) :
    HasDerivAt (lgBesselModel2Deriv s c) (lgBesselModel2SecondDeriv s c x) x := by
  have hph : 0 < c * xiEndpointPhase s x := by
    have := xiEndpointPhase_pos hs0 hs1 hx
    positivity
  have hinner : HasDerivAt (fun t : ℝ => c * xiEndpointPhase s t) (c * xiSpeed s x) x :=
    (hasDerivAt_xiEndpointPhase hs0 hx).const_mul c
  have h1 := (hasDerivAt_besselKDeriv hph).comp x hinner
  have h2 : HasDerivAt (fun t : ℝ => c * xiSpeed s t) (c * xiSpeedDeriv s x) x :=
    (hasDerivAt_xiSpeed (by linarith) hx).const_mul c
  have h := h1.fun_mul h2
  simp only [Function.comp_apply] at h
  have hval : besselKSecondDeriv (c * xiEndpointPhase s x) * (c * xiSpeed s x)
        * (c * xiSpeed s x)
      + besselKDeriv (c * xiEndpointPhase s x) * (c * xiSpeedDeriv s x)
      = lgBesselModel2SecondDeriv s c x := by
    rw [lgBesselModel2SecondDeriv]
    ring
  rw [hval] at h
  exact h

/-- **The second model solution solves the same comparison equation.**  `K` satisfies Bessel's equation,
so the chain rule gives the identical cancellation. -/
theorem lgBesselModel2_ode {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) (hc : 0 < c) :
    lgBesselModel2SecondDeriv s c x
        + lgFirstOrderCoeff s x * lgBesselModel2Deriv s c x
        + c ^ 2 * xiSpeed s x ^ 2 * lgBesselModel2 s c x = 0 := by
  have hsp := xiSpeed_pos hs1 hx
  have hph := xiEndpointPhase_pos hs0 hs1 hx
  have hzeta : 0 < c * xiEndpointPhase s x := by positivity
  have hode := besselK_ode hzeta
  have hsecond : besselKSecondDeriv (c * xiEndpointPhase s x)
      = (-besselKDeriv (c * xiEndpointPhase s x)
          - c * xiEndpointPhase s x * besselK (c * xiEndpointPhase s x))
        / (c * xiEndpointPhase s x) := by
    field_simp
    linarith [hode]
  rw [lgBesselModel2SecondDeriv, lgBesselModel2Deriv, lgBesselModel2, lgFirstOrderCoeff, hsecond]
  have hphne : xiEndpointPhase s x ≠ 0 := hph.ne'
  have hspne : xiSpeed s x ≠ 0 := hsp.ne'
  have hcne : c ≠ 0 := hc.ne'
  field_simp
  ring

theorem hasDerivAt_lgBesselModel2Deriv_ode {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hc : 0 < c) :
    HasDerivAt (lgBesselModel2Deriv s c)
      (-(lgFirstOrderCoeff s x) * lgBesselModel2Deriv s c x
        - (c ^ 2 * xiSpeed s x ^ 2 + 0) * lgBesselModel2 s c x) x := by
  have h := hasDerivAt_lgBesselModel2Deriv hs0 hs1 hx hc
  have hode := lgBesselModel2_ode hs0 hs1 hx hc
  have hval : lgBesselModel2SecondDeriv s c x
      = -(lgFirstOrderCoeff s x) * lgBesselModel2Deriv s c x
        - (c ^ 2 * xiSpeed s x ^ 2 + 0) * lgBesselModel2 s c x := by linarith [hode]
  rw [hval] at h
  exact h

/-- **The Green kernel normalisation.**  The weighted Wronskian of the model pair is exactly the Bessel
Wronskian constant: the Liouville weight `xi/xi'` cancels the Jacobian `c xi'` of the substitution
against the `1/(c xi)` of Abel's identity for Bessel. -/
theorem lgWronskian_model_eq {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) (hc : 0 < c) :
    lgWeight s x * (lgBesselModel s c x * lgBesselModel2Deriv s c x
        - lgBesselModelDeriv s c x * lgBesselModel2 s c x)
      = besselWronskian (c * xiEndpointPhase s x) := by
  have hsp := xiSpeed_pos hs1 hx
  have hph := xiEndpointPhase_pos hs0 hs1 hx
  rw [lgWeight, lgBesselModel, lgBesselModelDeriv, lgBesselModel2, lgBesselModel2Deriv,
    besselWronskian]
  have hspne : xiSpeed s x ≠ 0 := hsp.ne'
  field_simp

/-- The Green kernel normalisation is positive. -/
theorem lgWronskian_model_pos {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hc : 0 < c) :
    0 < lgWeight s x * (lgBesselModel s c x * lgBesselModel2Deriv s c x
      - lgBesselModelDeriv s c x * lgBesselModel2 s c x) := by
  rw [lgWronskian_model_eq hs0 hs1 hx hc]
  refine besselWronskian_pos ?_
  have := xiEndpointPhase_pos hs0 hs1 hx
  positivity

/-! ## The exact reconstruction of a perturbed solution -/

/-- **The reconstruction identity.**  A solution `U` of the perturbed comparison equation is recovered
algebraically from its two weighted Wronskians against the model pair, divided by the Green kernel
normalisation:

```text
U · [m (V1 V2' - V1' V2)] = F2 · V1 - F1 · V2,      F_i = m (U V_i' - U' V_i).
```

No integral and no hypothesis on the defect are involved: this is the algebraic step that turns the
transport law `F_i' = m a U V_i` into a Volterra equation for `U`. -/
theorem lgReconstruction {s c x : ℝ} {U DU : ℝ → ℝ} :
    U x * (lgWeight s x * (lgBesselModel s c x * lgBesselModel2Deriv s c x
        - lgBesselModelDeriv s c x * lgBesselModel2 s c x))
      = (lgWeight s x * (U x * lgBesselModel2Deriv s c x - DU x * lgBesselModel2 s c x))
          * lgBesselModel s c x
        - (lgWeight s x * (U x * lgBesselModelDeriv s c x - DU x * lgBesselModel s c x))
          * lgBesselModel2 s c x := by
  ring

/-- The reconstruction in solved form. -/
theorem lgReconstruction_eq {s c x : ℝ} {U DU : ℝ → ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hc : 0 < c) :
    U x = ((lgWeight s x * (U x * lgBesselModel2Deriv s c x - DU x * lgBesselModel2 s c x))
          * lgBesselModel s c x
        - (lgWeight s x * (U x * lgBesselModelDeriv s c x - DU x * lgBesselModel s c x))
          * lgBesselModel2 s c x)
      / besselWronskian (c * xiEndpointPhase s x) := by
  have hW := lgWronskian_model_pos (s := s) (c := c) (x := x) hs0 hs1 hx hc
  rw [lgWronskian_model_eq hs0 hs1 hx hc] at hW
  rw [eq_div_iff hW.ne']
  rw [← lgWronskian_model_eq hs0 hs1 hx hc]
  exact lgReconstruction (s := s) (c := c) (x := x) (U := U) (DU := DU)

/-! ## The Volterra equation in integral form -/

/-- The transport law against the second model solution. -/
theorem hasDerivAt_lgBessel2Wronskian {s c x a : ℝ} {U DU : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) (hc : 0 < c)
    (hU : HasDerivAt U (DU x) x)
    (hDU : HasDerivAt DU
      (-(lgFirstOrderCoeff s x) * DU x - (c ^ 2 * xiSpeed s x ^ 2 + a) * U x) x) :
    HasDerivAt (fun t : ℝ =>
        lgWeight s t * (U t * lgBesselModel2Deriv s c t - DU t * lgBesselModel2 s c t))
      (lgWeight s x * a * (U x * lgBesselModel2 s c x)) x := by
  have h := hasDerivAt_weightedWronskian (s := s) (c := c) (a := a) (b := 0) hs0 hs1 hx hU hDU
    (hasDerivAt_lgBesselModel2 hs0 hs1 hx hc) (hasDerivAt_lgBesselModel2Deriv_ode hs0 hs1 hx hc)
  have hval : lgWeight s x * (a - 0) * (U x * lgBesselModel2 s c x)
      = lgWeight s x * a * (U x * lgBesselModel2 s c x) := by ring
  rw [hval] at h
  exact h

/-- **The Volterra equation, first model solution.**  The weighted Wronskian of a perturbed solution
against `V1` moves exactly by the integral of `m a U V1`.  Integrating the transport law is the whole
content; the defect `a` enters only through that integral. -/
theorem integral_lgBesselWronskian {s c A B : ℝ} {U DU a : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hAB : A ≤ B) (hA : 1 < A)
    (hU : ∀ x ∈ Set.uIcc A B, HasDerivAt U (DU x) x)
    (hDU : ∀ x ∈ Set.uIcc A B, HasDerivAt DU
      (-(lgFirstOrderCoeff s x) * DU x - (c ^ 2 * xiSpeed s x ^ 2 + a x) * U x) x)
    (hint : IntervalIntegrable
      (fun t : ℝ => lgWeight s t * a t * (U t * lgBesselModel s c t)) volume A B) :
    (∫ t in A..B, lgWeight s t * a t * (U t * lgBesselModel s c t))
      = lgWeight s B * (U B * lgBesselModelDeriv s c B - DU B * lgBesselModel s c B)
        - lgWeight s A * (U A * lgBesselModelDeriv s c A - DU A * lgBesselModel s c A) := by
  have hsub : Set.uIcc A B ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hAB]
    intro x hx
    exact lt_of_lt_of_le hA hx.1
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ =>
      lgWeight s t * (U t * lgBesselModelDeriv s c t - DU t * lgBesselModel s c t))
    (fun x hx => ?_) hint
  exact hasDerivAt_lgBesselWronskian hs0 hs1 (hsub hx) hc (hU x hx) (hDU x hx)

/-- **The Volterra equation, second model solution.** -/
theorem integral_lgBessel2Wronskian {s c A B : ℝ} {U DU a : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hAB : A ≤ B) (hA : 1 < A)
    (hU : ∀ x ∈ Set.uIcc A B, HasDerivAt U (DU x) x)
    (hDU : ∀ x ∈ Set.uIcc A B, HasDerivAt DU
      (-(lgFirstOrderCoeff s x) * DU x - (c ^ 2 * xiSpeed s x ^ 2 + a x) * U x) x)
    (hint : IntervalIntegrable
      (fun t : ℝ => lgWeight s t * a t * (U t * lgBesselModel2 s c t)) volume A B) :
    (∫ t in A..B, lgWeight s t * a t * (U t * lgBesselModel2 s c t))
      = lgWeight s B * (U B * lgBesselModel2Deriv s c B - DU B * lgBesselModel2 s c B)
        - lgWeight s A * (U A * lgBesselModel2Deriv s c A - DU A * lgBesselModel2 s c A) := by
  have hsub : Set.uIcc A B ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hAB]
    intro x hx
    exact lt_of_lt_of_le hA hx.1
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ =>
      lgWeight s t * (U t * lgBesselModel2Deriv s c t - DU t * lgBesselModel2 s c t))
    (fun x hx => ?_) hint
  exact hasDerivAt_lgBessel2Wronskian hs0 hs1 (hsub hx) hc (hU x hx) (hDU x hx)

/-- **The deviation bound.**  The change in either weighted Wronskian is at most the absolute integral
of the defect against the corresponding model solution.  This is the inequality the pole-uniform
`O(c^{-1})` of `(14)` is read off from, once the two envelopes and the size of `a` are inserted. -/
theorem abs_lgBesselWronskian_deviation_le {s c A B : ℝ} {U DU a : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hAB : A ≤ B) (hA : 1 < A)
    (hU : ∀ x ∈ Set.uIcc A B, HasDerivAt U (DU x) x)
    (hDU : ∀ x ∈ Set.uIcc A B, HasDerivAt DU
      (-(lgFirstOrderCoeff s x) * DU x - (c ^ 2 * xiSpeed s x ^ 2 + a x) * U x) x)
    (hint : IntervalIntegrable
      (fun t : ℝ => lgWeight s t * a t * (U t * lgBesselModel s c t)) volume A B) :
    |lgWeight s B * (U B * lgBesselModelDeriv s c B - DU B * lgBesselModel s c B)
        - lgWeight s A * (U A * lgBesselModelDeriv s c A - DU A * lgBesselModel s c A)|
      ≤ ∫ t in A..B, |lgWeight s t * a t * (U t * lgBesselModel s c t)| := by
  rw [← integral_lgBesselWronskian hs0 hs1 hc hAB hA hU hDU hint, ← Real.norm_eq_abs]
  have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun t : ℝ => lgWeight s t * a t * (U t * lgBesselModel s c t)) hAB
  simpa [Real.norm_eq_abs] using h

/-! ## Monotonicity of the phase and the model envelopes -/

/-- The endpoint phase is nondecreasing: its increment is the integral of the nonnegative speed. -/
theorem xiEndpointPhase_le_of_le {s A x : ℝ} (hs0 : 0 ≤ s) (_hs1 : s ≤ 1 / 2) (hA : 1 ≤ A)
    (hAx : A ≤ x) : xiEndpointPhase s A ≤ xiEndpointPhase s x := by
  have h1A : IntervalIntegrable (xiSpeed s) volume 1 A := intervalIntegrable_xiSpeed hs0 hA
  have h1x : IntervalIntegrable (xiSpeed s) volume 1 x :=
    intervalIntegrable_xiSpeed hs0 (le_trans hA hAx)
  have hAx' : IntervalIntegrable (xiSpeed s) volume A x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hAx]
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (le_trans hA hAx)] at h1x
    exact h1x.mono_set (fun t ht => ⟨lt_of_le_of_lt hA ht.1, ht.2⟩)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h1A hAx'
  have hnn : 0 ≤ ∫ t in A..x, xiSpeed s t := by
    refine intervalIntegral.integral_nonneg hAx fun t ht => ?_
    rw [xiSpeed]
    positivity
  rw [xiEndpointPhase, xiEndpointPhase]
  linarith [hsplit, hnn]

/-- The first model solution inherits the Bessel envelope. -/
theorem abs_lgBesselModel_le {s c x : ℝ} (h1 : 1 ≤ c * xiEndpointPhase s x) :
    |lgBesselModel s c x| ≤ 72 * Real.sqrt 2 / Real.sqrt (c * xiEndpointPhase s x) := by
  rw [lgBesselModel]
  exact abs_besselJ0_le_envelope h1

/-- The second model solution inherits the envelope of `K`, with a constant independent of every
parameter. -/
theorem exists_lgBesselModel2_envelope :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s c x : ℝ, 1 ≤ c * xiEndpointPhase s x →
      |lgBesselModel2 s c x| ≤ C / Real.sqrt (c * xiEndpointPhase s x) := by
  obtain ⟨C, hC0, hC⟩ := exists_besselK_envelope
  refine ⟨C, hC0, fun s c x h1 => ?_⟩
  rw [lgBesselModel2]
  exact hC _ h1

/-- A common envelope for the model pair. -/
theorem exists_lgBesselModel_common_envelope :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s c x : ℝ, 1 ≤ c * xiEndpointPhase s x →
      |lgBesselModel s c x| ≤ C / Real.sqrt (c * xiEndpointPhase s x)
        ∧ |lgBesselModel2 s c x| ≤ C / Real.sqrt (c * xiEndpointPhase s x) := by
  obtain ⟨C, hC0, hC⟩ := exists_lgBesselModel2_envelope
  refine ⟨72 * Real.sqrt 2 + C, by positivity, fun s c x h1 => ?_⟩
  have hs : (0 : ℝ) < Real.sqrt (c * xiEndpointPhase s x) :=
    Real.sqrt_pos.mpr (by linarith)
  have h72 : (0 : ℝ) ≤ 72 * Real.sqrt 2 := by positivity
  refine ⟨le_trans (abs_lgBesselModel_le h1) ?_, le_trans (hC s c x h1) ?_⟩
  · rw [div_le_div_iff₀ hs hs]
    nlinarith [hs.le, hC0]
  · rw [div_le_div_iff₀ hs hs]
    nlinarith [hs.le, h72]

/-! ## Interior continuity of the model objects -/

theorem continuousOn_lgWeight {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    ContinuousOn (lgWeight s) (Set.Ioi 1) :=
  fun _ hx => ((hasDerivAt_lgWeight hs0 hs1 hx).continuousAt).continuousWithinAt

theorem continuousOn_lgBesselModel {s c : ℝ} (hs0 : 0 ≤ s) :
    ContinuousOn (lgBesselModel s c) (Set.Ioi 1) :=
  fun _ hx => ((hasDerivAt_lgBesselModel hs0 hx).continuousAt).continuousWithinAt

theorem continuousOn_lgBesselModelDeriv {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ContinuousOn (lgBesselModelDeriv s c) (Set.Ioi 1) :=
  fun _ hx => ((hasDerivAt_lgBesselModelDeriv hs0 hs1 hx).continuousAt).continuousWithinAt

theorem continuousOn_lgBesselModel2 {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) :
    ContinuousOn (lgBesselModel2 s c) (Set.Ioi 1) :=
  fun _ hx => ((hasDerivAt_lgBesselModel2 hs0 hs1 hx hc).continuousAt).continuousWithinAt

theorem continuousOn_lgBesselModel2Deriv {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) :
    ContinuousOn (lgBesselModel2Deriv s c) (Set.Ioi 1) :=
  fun _ hx => ((hasDerivAt_lgBesselModel2Deriv hs0 hs1 hx hc).continuousAt).continuousWithinAt

theorem continuousOn_xiEndpointPhase' {s : ℝ} (hs0 : 0 ≤ s) :
    ContinuousOn (xiEndpointPhase s) (Set.Ioi 1) :=
  fun _ hx => ((hasDerivAt_xiEndpointPhase hs0 hx).continuousAt).continuousWithinAt

/-! ## The reconstruction against the endpoint-normalised Green constant -/

/-- The Bessel argument grows along the ray, so the Green kernel constant may be evaluated once, at the
left endpoint of the interval. -/
theorem besselWronskian_phase_eq {s c A x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hA : 1 < A) (hAx : A ≤ x) :
    besselWronskian (c * xiEndpointPhase s x) = besselWronskian (c * xiEndpointPhase s A) := by
  have hposA : 0 < c * xiEndpointPhase s A := by
    have := xiEndpointPhase_pos hs0 hs1 hA
    positivity
  have hmono : c * xiEndpointPhase s A ≤ c * xiEndpointPhase s x :=
    mul_le_mul_of_nonneg_left (xiEndpointPhase_le_of_le hs0 hs1 hA.le hAx) hc.le
  exact besselWronskian_const hposA hmono

/-- **The reconstruction with the endpoint-normalised constant.**  The Green kernel constant is the same
throughout the interval, so the algebraic reconstruction holds with the single constant
`W = besselWronskian (c xi_s(A))`. -/
theorem lgReconstruction_const {s c A x : ℝ} {U DU : ℝ → ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (hA : 1 < A) (hAx : A ≤ x) :
    U x * besselWronskian (c * xiEndpointPhase s A)
      = (lgWeight s x * (U x * lgBesselModel2Deriv s c x - DU x * lgBesselModel2 s c x))
          * lgBesselModel s c x
        - (lgWeight s x * (U x * lgBesselModelDeriv s c x - DU x * lgBesselModel s c x))
          * lgBesselModel2 s c x := by
  have hx : (1 : ℝ) < x := lt_of_lt_of_le hA hAx
  rw [← besselWronskian_phase_eq hs0 hs1 hc hA hAx, ← lgWronskian_model_eq hs0 hs1 hx hc]
  exact lgReconstruction (s := s) (c := c) (x := x) (U := U) (DU := DU)

/-- The Green kernel constant is positive. -/
theorem besselWronskian_phase_pos {s c A : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hA : 1 < A) : 0 < besselWronskian (c * xiEndpointPhase s A) := by
  refine besselWronskian_pos ?_
  have := xiEndpointPhase_pos hs0 hs1 hA
  positivity

/-- **The pointwise envelope bound on a perturbed solution.**  From the reconstruction and the common
envelope of the model pair: the solution is at most the envelope times the total Wronskian size, divided
by the Green kernel constant.  This is the inequality that closes the Volterra loop. -/
theorem abs_perturbed_le_envelope_mul_wronskianSum {s c A x C : ℝ} {U DU : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hA : 1 < A) (hAx : A ≤ x)
    (henv : |lgBesselModel s c x| ≤ C / Real.sqrt (c * xiEndpointPhase s x)
      ∧ |lgBesselModel2 s c x| ≤ C / Real.sqrt (c * xiEndpointPhase s x)) :
    |U x| * besselWronskian (c * xiEndpointPhase s A)
      ≤ C / Real.sqrt (c * xiEndpointPhase s x)
        * (|lgWeight s x * (U x * lgBesselModelDeriv s c x - DU x * lgBesselModel s c x)|
          + |lgWeight s x * (U x * lgBesselModel2Deriv s c x - DU x * lgBesselModel2 s c x)|) := by
  have hW := besselWronskian_phase_pos hs0 hs1 hc hA
  have hrec := lgReconstruction_const (s := s) (c := c) (A := A) (x := x) (U := U) (DU := DU)
    hs0 hs1 hc hA hAx
  set F₁ : ℝ := lgWeight s x * (U x * lgBesselModelDeriv s c x - DU x * lgBesselModel s c x)
    with hF₁
  set F₂ : ℝ := lgWeight s x * (U x * lgBesselModel2Deriv s c x - DU x * lgBesselModel2 s c x)
    with hF₂
  have habs : |U x| * besselWronskian (c * xiEndpointPhase s A)
      = |U x * besselWronskian (c * xiEndpointPhase s A)| := by
    rw [abs_mul, abs_of_pos hW]
  rw [habs, hrec]
  calc |F₂ * lgBesselModel s c x - F₁ * lgBesselModel2 s c x|
      ≤ |F₂ * lgBesselModel s c x| + |F₁ * lgBesselModel2 s c x| := abs_sub _ _
    _ = |F₂| * |lgBesselModel s c x| + |F₁| * |lgBesselModel2 s c x| := by
        rw [abs_mul F₂ (lgBesselModel s c x), abs_mul F₁ (lgBesselModel2 s c x)]
    _ ≤ |F₂| * (C / Real.sqrt (c * xiEndpointPhase s x))
          + |F₁| * (C / Real.sqrt (c * xiEndpointPhase s x)) := by
        have h1 := mul_le_mul_of_nonneg_left henv.1 (abs_nonneg F₂)
        have h2 := mul_le_mul_of_nonneg_left henv.2 (abs_nonneg F₁)
        linarith
    _ = C / Real.sqrt (c * xiEndpointPhase s x) * (|F₁| + |F₂|) := by ring

end GaloisForLFunctions.RHTower

end
