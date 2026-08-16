import Mathlib

/-!
# Comparison transport for a second-order equation in drift form

A second-order equation written with a first-order coefficient,

```text
U'' = -B U' - (kappa + a) U ,
```

compares two solutions through the integrating factor `m` of the drift, i.e. any nonvanishing `m`
with `m' = m B`.  Three facts are recorded, all exact and all local:

* the drift Wronskian `m (U V' - U' V)` of two solutions whose potentials differ by `a - b` has
  derivative `m (a - b) U V` — the Volterra kernel of the comparison, before any estimate;
* dividing a solution of the normal form `u'' + Q u = 0` by an amplitude `g` produces a solution of
  the drift form with `B = 2 g'/g` and potential `g''/g + Q`;
* `g = sqrt |m|` is such an amplitude, with `g''/g = B²/4 + B'/2`.

Everything is stated for arbitrary `m`, `B`, `g`, so the same statements serve an oscillatory
comparison (where the drift weight is positive) and a barrier comparison (where it is negative);
only `|m|` enters the amplitude.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.HTGeometry

variable {m B B' g Dg DDg u Du DDu Q U DU V DV : ℝ → ℝ} {x κ a b : ℝ}

/-! ## The quotient by an amplitude -/

/-- The comparison unknown `U = u/g`. -/
def comparisonQuotient (g u : ℝ → ℝ) (x : ℝ) : ℝ := u x / g x

/-- Its derivative. -/
def comparisonQuotientDeriv (g Dg u Du : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Du x * g x - u x * Dg x) / (g x * g x)

theorem hasDerivAt_comparisonQuotient (hg : HasDerivAt g (Dg x) x) (hg0 : g x ≠ 0)
    (hu : HasDerivAt u (Du x) x) :
    HasDerivAt (comparisonQuotient g u) (comparisonQuotientDeriv g Dg u Du x) x := by
  have h := hu.fun_div hg hg0
  have hfun : comparisonQuotient g u = fun t : ℝ => u t / g t := by
    funext t; rw [comparisonQuotient]
  rw [hfun]
  refine h.congr_deriv ?_
  rw [comparisonQuotientDeriv]
  ring

/-- **The drift form of the normal form.**  If `u'' + Q u = 0` then `U = u/g` satisfies
`U'' = -(2g'/g) U' - (g''/g + Q) U`. -/
theorem hasDerivAt_comparisonQuotientDeriv
    (hg : HasDerivAt g (Dg x) x) (hDg : HasDerivAt Dg (DDg x) x) (hg0 : g x ≠ 0)
    (hu : HasDerivAt u (Du x) x) (hDu : HasDerivAt Du (DDu x) x)
    (hode : DDu x + Q x * u x = 0) :
    HasDerivAt (comparisonQuotientDeriv g Dg u Du)
      (-(2 * Dg x / g x) * comparisonQuotientDeriv g Dg u Du x
        - (DDg x / g x + Q x) * comparisonQuotient g u x) x := by
  have hne : g x * g x ≠ 0 := mul_ne_zero hg0 hg0
  have hDDu : DDu x = -(Q x * u x) := by linarith
  have hfun : comparisonQuotientDeriv g Dg u Du
      = fun t : ℝ => (Du t * g t - u t * Dg t) / (g t * g t) := by
    funext t; rw [comparisonQuotientDeriv]
  rw [hfun]
  refine (((hDu.fun_mul hg).fun_sub (hu.fun_mul hDg)).fun_div (hg.fun_mul hg) hne).congr_deriv ?_
  simp only [comparisonQuotient, hDDu]
  field_simp
  ring

/-! ## The drift Wronskian -/

/-- The drift Wronskian of two solutions of a drift-form equation. -/
def driftWronskian (m U DU V DV : ℝ → ℝ) (x : ℝ) : ℝ := m x * (U x * DV x - DU x * V x)

/-- **The transport law.**  Two solutions of the same drift-form equation whose potentials differ
by `a - b` have drift Wronskian with derivative exactly `m (a - b) U V`.  Every hypothesis is at
the single point `x`, and the identity is exact. -/
theorem hasDerivAt_driftWronskian
    (hm : HasDerivAt m (m x * B x) x)
    (hU : HasDerivAt U (DU x) x)
    (hDU : HasDerivAt DU (-(B x) * DU x - (κ + a) * U x) x)
    (hV : HasDerivAt V (DV x) x)
    (hDV : HasDerivAt DV (-(B x) * DV x - (κ + b) * V x) x) :
    HasDerivAt (driftWronskian m U DU V DV) (m x * (a - b) * (U x * V x)) x := by
  have hw : HasDerivAt (fun t : ℝ => U t * DV t - DU t * V t)
      (-(B x) * (U x * DV x - DU x * V x) + (a - b) * (U x * V x)) x := by
    refine ((hU.fun_mul hDV).fun_sub (hDU.fun_mul hV)).congr_deriv ?_
    ring
  have hfun : driftWronskian m U DU V DV = fun t : ℝ => m t * (U t * DV t - DU t * V t) := by
    funext t; rw [driftWronskian]
  rw [hfun]
  refine (hm.fun_mul hw).congr_deriv ?_
  ring

/-- **Abel's identity in drift form.**  Two solutions with the same potential have constant drift
Wronskian. -/
theorem hasDerivAt_driftWronskian_const
    (hm : HasDerivAt m (m x * B x) x)
    (hU : HasDerivAt U (DU x) x)
    (hDU : HasDerivAt DU (-(B x) * DU x - κ * U x) x)
    (hV : HasDerivAt V (DV x) x)
    (hDV : HasDerivAt DV (-(B x) * DV x - κ * V x) x) :
    HasDerivAt (driftWronskian m U DU V DV) 0 x := by
  have hDU' : HasDerivAt DU (-(B x) * DU x - (κ + 0) * U x) x := by
    refine hDU.congr_deriv ?_; ring
  have hDV' : HasDerivAt DV (-(B x) * DV x - (κ + 0) * V x) x := by
    refine hDV.congr_deriv ?_; ring
  refine (hasDerivAt_driftWronskian hm hU hDU' hV hDV').congr_deriv ?_
  ring

/-! ## The amplitude built from the integrating factor -/

/-- The comparison amplitude `g = sqrt |m|` attached to an integrating factor of the drift. -/
def driftAmplitude (m : ℝ → ℝ) (x : ℝ) : ℝ := Real.sqrt |m x|

/-- Its derivative. -/
def driftAmplitudeDeriv (m B : ℝ → ℝ) (x : ℝ) : ℝ := driftAmplitude m x * B x / 2

/-- Its second derivative. -/
def driftAmplitudeSecondDeriv (m B B' : ℝ → ℝ) (x : ℝ) : ℝ :=
  driftAmplitude m x * (B x ^ 2 / 4 + B' x / 2)

theorem driftAmplitude_pos (hm0 : m x ≠ 0) : 0 < driftAmplitude m x :=
  Real.sqrt_pos.2 (abs_pos.2 hm0)

theorem hasDerivAt_abs_of_integratingFactor (hm : HasDerivAt m (m x * B x) x) (hm0 : m x ≠ 0) :
    HasDerivAt (fun t => |m t|) (|m x| * B x) x := by
  rcases lt_or_gt_of_ne hm0 with hneg | hpos
  · have hev : (fun t => |m t|) =ᶠ[nhds x] fun t => -m t := by
      filter_upwards [hm.continuousAt.eventually_lt_const hneg] with t ht
      exact abs_of_neg ht
    refine (hm.neg.congr_deriv ?_).congr_of_eventuallyEq hev
    rw [abs_of_neg hneg]; ring
  · have hev : (fun t => |m t|) =ᶠ[nhds x] m := by
      filter_upwards [hm.continuousAt.eventually_const_lt hpos] with t ht
      exact abs_of_pos ht
    refine (hm.congr_deriv ?_).congr_of_eventuallyEq hev
    rw [abs_of_pos hpos]

/-- **The amplitude has logarithmic derivative `B/2`.**  This is what makes `U = u/g` land in drift
form with first-order coefficient `B`. -/
theorem hasDerivAt_driftAmplitude (hm : HasDerivAt m (m x * B x) x) (hm0 : m x ≠ 0) :
    HasDerivAt (driftAmplitude m) (driftAmplitudeDeriv m B x) x := by
  have habs := hasDerivAt_abs_of_integratingFactor hm hm0
  have hpos : (0 : ℝ) < |m x| := abs_pos.2 hm0
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt |m x|)) |m x| :=
    Real.hasDerivAt_sqrt hpos.ne'
  have h := hsq.comp x habs
  refine h.congr_deriv ?_
  have hs : (0 : ℝ) < Real.sqrt |m x| := Real.sqrt_pos.2 hpos
  have hsq2 : Real.sqrt |m x| ^ 2 = |m x| := Real.sq_sqrt hpos.le
  rw [driftAmplitudeDeriv, driftAmplitude]
  field_simp
  rw [hsq2]

theorem hasDerivAt_driftAmplitudeDeriv (hm : HasDerivAt m (m x * B x) x) (hm0 : m x ≠ 0)
    (hB : HasDerivAt B (B' x) x) :
    HasDerivAt (driftAmplitudeDeriv m B) (driftAmplitudeSecondDeriv m B B' x) x := by
  have hg := hasDerivAt_driftAmplitude hm hm0
  have hfun : driftAmplitudeDeriv m B = fun t : ℝ => driftAmplitude m t * B t / 2 := by
    funext t; rw [driftAmplitudeDeriv]
  rw [hfun]
  refine ((hg.fun_mul hB).div_const 2).congr_deriv ?_
  rw [driftAmplitudeSecondDeriv, driftAmplitudeDeriv]
  ring

/-- **The defect produced by the amplitude.**  `g''/g = B²/4 + B'/2`, the classical normal-form
contribution of the drift. -/
theorem driftAmplitudeSecondDeriv_div (hm0 : m x ≠ 0) :
    driftAmplitudeSecondDeriv m B B' x / driftAmplitude m x = B x ^ 2 / 4 + B' x / 2 := by
  rw [driftAmplitudeSecondDeriv]
  field_simp [(driftAmplitude_pos hm0).ne']

/-- **The comparison equation of a normal-form solution.**  Dividing a solution of `u'' + Q u = 0`
by `g = sqrt |m|` produces a solution of the drift form with first-order coefficient `B` and
potential `Q + B²/4 + B'/2`. -/
theorem hasDerivAt_comparisonQuotientDeriv_driftAmplitude
    (hm : HasDerivAt m (m x * B x) x) (hm0 : m x ≠ 0) (hB : HasDerivAt B (B' x) x)
    (hu : HasDerivAt u (Du x) x) (hDu : HasDerivAt Du (DDu x) x)
    (hode : DDu x + Q x * u x = 0) :
    HasDerivAt (comparisonQuotient (driftAmplitude m) u)
        (comparisonQuotientDeriv (driftAmplitude m) (driftAmplitudeDeriv m B) u Du x) x
      ∧ HasDerivAt (comparisonQuotientDeriv (driftAmplitude m) (driftAmplitudeDeriv m B) u Du)
        (-(B x) *
            comparisonQuotientDeriv (driftAmplitude m) (driftAmplitudeDeriv m B) u Du x
          - (Q x + (B x ^ 2 / 4 + B' x / 2)) *
              comparisonQuotient (driftAmplitude m) u x) x := by
  have hg := hasDerivAt_driftAmplitude hm hm0
  have hDg := hasDerivAt_driftAmplitudeDeriv hm hm0 hB
  have hg0 : driftAmplitude m x ≠ 0 := (driftAmplitude_pos hm0).ne'
  refine ⟨hasDerivAt_comparisonQuotient hg hg0 hu, ?_⟩
  have h := hasDerivAt_comparisonQuotientDeriv hg hDg hg0 hu hDu hode
  refine h.congr_deriv ?_
  rw [driftAmplitudeSecondDeriv_div (B := B) (B' := B') hm0]
  have hdrift : 2 * driftAmplitudeDeriv m B x / driftAmplitude m x = B x := by
    rw [driftAmplitudeDeriv]
    field_simp
  rw [hdrift]
  ring

/-! ## The integrated transport law -/

/-- **The Volterra equation.**  Integrating the transport law: the drift Wronskian of a perturbed
solution against an unperturbed one moves exactly by the integral of `m a U V`. -/
theorem integral_driftWronskian {A C : ℝ} {aa : ℝ → ℝ}
    (hm : ∀ y ∈ uIcc A C, HasDerivAt m (m y * B y) y)
    (hU : ∀ y ∈ uIcc A C, HasDerivAt U (DU y) y)
    (hDU : ∀ y ∈ uIcc A C, HasDerivAt DU (-(B y) * DU y - (κ + aa y) * U y) y)
    (hV : ∀ y ∈ uIcc A C, HasDerivAt V (DV y) y)
    (hDV : ∀ y ∈ uIcc A C, HasDerivAt DV (-(B y) * DV y - κ * V y) y)
    (hint : IntervalIntegrable (fun t : ℝ => m t * aa t * (U t * V t)) MeasureTheory.volume A C) :
    (∫ t in A..C, m t * aa t * (U t * V t))
      = driftWronskian m U DU V DV C - driftWronskian m U DU V DV A := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => ?_) hint
  have hDV' : HasDerivAt DV (-(B y) * DV y - (κ + 0) * V y) y := by
    refine (hDV y hy).congr_deriv ?_; ring
  have h := hasDerivAt_driftWronskian (hm y hy) (hU y hy) (hDU y hy) (hV y hy) hDV'
  refine h.congr_deriv ?_
  ring

end GaloisForLFunctions.HTGeometry

end
