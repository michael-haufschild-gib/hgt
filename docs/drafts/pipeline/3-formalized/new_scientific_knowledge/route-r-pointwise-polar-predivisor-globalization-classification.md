# Route R pointwise polar and pre-divisor globalization classification

- **Status:** `[LEAN-PROVED] [ROUTE-R DEPENDENCY CLOSURE] [NOT RH]`
- **Date:** 2026-08-13
- **Lean modules:**
  - `RHTower/RouteRHyperbolicGaugePositivePolarUniversalityNoGo.lean`
  - `RHTower/RouteRPreDivisorGammaCoronaGlobalizationNoGo.lean`
  - `RHTower/RouteRPrepolarTerminalNoGo.lean`

## Result A: one-carrier, two-orientation positive collapse

Let `Q` be any nonnegative real quadratic form on the retained forward/reciprocal source plane and
let `T_a(x,y)=(exp(a)x,exp(-a)y)`.  For one fixed carrier `z`, no naturality, fixed metric, or
whole-space contraction is required:

```text
Q(T_(log 2) z) <= Q(z)  and  Q(T_(-log 2) z) <= Q(z)
  ==> Q(z)=0.
```

Writing `z=x+y` along the two retained axes and expanding with a companion bilinear form gives

```text
Q(T_h z) + Q(T_(-h) z) - 2 Q(z)
  = 2 (cosh(2h)-1) (Q(x)+Q(y)).
```

Both inequalities and positivity force both axis energies to vanish.  Positivity then kills the
mixed term at this same carrier.  Lean theorem:

```text
routeR_pointwise_twoOrientationGaugeNonamplification_energy_eq_zero
```

Consequently, even a fibre-dependent and nonfunctorially selected quadratic form satisfying only
the two inequalities on its chosen carrier compares with the fixed physical Stokes excess on all
Xi fibres exactly under RH:

```text
routeRPointwiseTwoOrientationPositivePolarHandoff_iff_rh
```

This closes the quadratic positive-polar escape at its weakest pointwise interface.  It does not
annihilate the nonlinear gauge-invariant quartic amplitude.

## Result B: exact pre-divisor Gamma-corona globalization locus

Before divisor specialization, let `a` be the variable horizontal grade and `c` the variable
retained Cartier coefficient.  The literal `(2,3)` source action is supported in one packet
coordinate, hence lies in the finite arithmetic core and is zero in the singular corona.  The
fixed physical action on the full-support horizon is

```text
(GammaOdd_(2,3)(a) * c) · horizon.
```

The horizon is nonzero and the cooriented Gamma coefficient satisfies

```text
GammaOdd_(2,3)(a)=0 <-> a=0.
```

Therefore Lean proves the exact classification

```text
globalAction(a,c)=corona(localAction(a,c)) <-> a=0 or c=0.
```

The main declarations are:

```text
routeRTwoThreePreDivisorGamma_global_eq_local_iff
not_forall_routeRTwoThreePreDivisorGamma_global_eq_local
routeR_no_preDivisorGammaCoronaGlobalizer
```

The explicit countermodel is `(a,c)=(1,1)`.  Thus a uniform source globalization genuinely valid
before divisor specialization is impossible: it must either neutralize the grade or erase the
retained coefficient.  The new impossible interface is included in
`RouteRPrepolarIntrinsicAnnihilator`.

## Strongest positive survivor

The source-local/full-support fracture is now dependency-closed.  Any surviving comparison must
use actual divisor specialization essentially and act nonlocally on the full-support horizon.
After specialization its equality is the already classified physical charge `a_rho=0`, hence an
RH-strength receiver.  The forced singular first-Xi-jet Calkin class remains nonzero off centre;
no unconditional source-specific annihilator is produced here.

## Topology / observer dichotomy

`RouteRSourceTopologyObserverDichotomy.lean` closes the two remaining choices surrounding this
singular quotient.

1. For every normed Hausdorff target, a continuous linear reporter that kills the finite
   arithmetic packet core is zero, since the core is dense.  It cannot retain the full-support
   horizon (`routeR_no_continuousArithmeticCoreHorizonLanding`).
2. On algebraic prime-isotropy `H¹`, marking a Stokes splitting realizes every target vector,
   including the actual physical corona value
   (`exists_routeRPrimeIsotropyMarkedPhysicalObserver`).  Mere algebraic descent has no selector.
3. Invariance under the full Haar vertical-shear gauge erases the retained class.  An invariant
   observer taking the retained class to the actual physical corona target exists at `rho` iff
   `Re rho=1/2`; globally, iff RH
   (`global_routeRPrimeIsotropyGaugeInvariantPhysicalObserver_iff_rh`).
4. A gauge-invariant observer valid uniformly before divisor specialization is impossible at the
   explicit unit-grade/unit-coefficient witness
   (`routeR_no_preDivisorGaugeInvariantCoronaObserver`).

Hence current source topology has an exact trilemma: continuous descent erases, algebraic marked
descent is arbitrary, and source-gauge-invariant descent erases.  Any remaining comparison must be
both singular/non-Hausdorff and nonfunctorially selected by additional arithmetic data; at actual
Xi fibres its required value is still the forced nonzero principal Calkin/corona charge off centre.
