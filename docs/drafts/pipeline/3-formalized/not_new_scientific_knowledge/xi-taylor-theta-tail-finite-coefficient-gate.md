# Xi Taylor theta-tail finite coefficient gate

- **ID:** `xi-taylor-theta-tail-finite-coefficient-gate`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT THE OPEN PRODUCER]`
- **Parent target:**
  `../../5-failed/xi-taylor-oriented-finite-coefficient-sublinear-flux.md`

## Statement

There exists a source-selected super-accurate canonical Xi Taylor schedule consisting entirely of
odd cutoffs

```text
N(k) = 2(D(k)+1)+1.                                      (1)
```

The schedule may be chosen simultaneously so that, on the closed ball of radius `k`, both the
top defect `E_(D(k))` and its derivative are smaller than the same super-accurate tolerance used
for the Taylor approximation.

For each `d` and `z`, define the entirely finite theta-tail envelope

```text
A_d(z)
 = J_(U_d)(z)
   + |U_d'(z)| |E_d(z)|
   + |E_d'(z)| |U_d(z)|,                                (2)
```

where `U_d` and `E_d` are the explicit core and top-defect polynomials formed from the first
`d+2` normalized theta-tail moments.  If `Im z>=0` and

```text
A_d(z) < B |P_(2d+3)(z)|^2,                              (3)
```

then

```text
P_(2d+3)(z) != 0,
Im(P_(2d+3)'(z)/P_(2d+3)(z)) < B.                        (4)
```

Consequently, if the finite inequalities

```text
A_(D(k_n))(z_n)
 < epsilon (n+1) |P_(N(k_n))(z_n)|^2                    (5)
```

hold eventually on every left-strip anisotropic mesh fibre, then the canonical Xi Taylor
logarithmic derivatives have sublinear upper flux there.  Together with the super-accurate odd
schedule, `(5)` implies the Riemann hypothesis.

The cross-interference in `(2)` is unconditional on this joint schedule.  For every mesh fibre
and every `epsilon>0`, eventually

```text
|U_d'||E_d|+|E_d'||U_d|
 < epsilon (n+1)|P_(2d+3)|^2.                            (6)
```

The local analytic order supplies the required polynomial lower bound for the Taylor value without
assuming or locating a zero.  Hence the entire remaining source obligation is

```text
J_(U_d)(z_n)
 < epsilon (n+1)|P_(2d+3)(z_n)|^2.                       (7)
```

Condition `(7)` alone forces anisotropic sublinear upper flux and RH.

No Xi zero location, real-rootedness, anti-Herglotz positivity, or limiting measure is used in
this gate.

## Proof

Local uniform convergence of the Taylor sections and their derivatives gives a threshold after
which every degree meets the required expanding-ball error.  Recursively choose increasing source
indices and replace each by the larger odd degree `(1)`.  This proves the odd super-accurate
schedule.

The oriented top-defect theorem gives

```text
J_(P_(2d+3))(z) <= A_d(z)                                (8)
```

in the upper half-plane.  Combining `(3)` and `(8)` produces the strict denominator-cleared
current inequality.  It excludes a polynomial zero at `z` and division by the positive squared
modulus gives `(4)`.  Apply this pointwise along the mesh to prove the sublinear-flux implication.

The final RH implication is the already formalized anisotropic pole-amplification theorem.

## Lean realization

File:

```text
formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailFiniteCoefficientGate.lean
```

Principal declarations:

```text
xiCTaylorOddDegreeSchedule
exists_xiCTaylorSuperaccurateOddSchedule
XiCTaylorOddThetaTailSuperaccurateSchedule
exists_xiCTaylorOddThetaTailSuperaccurateSchedule
xiCTaylorThetaTailCoreInterference
xiCTaylorThetaTailCrossInterference
xiCTaylor_logDeriv_im_lt_of_thetaTailCoreInterference_lt
XiCTaylorThetaTailCoreInterferenceSublinearUpper
XiCTaylorThetaTailCoreCurrentSublinearUpper
eventually_xiCTaylorThetaTailCrossInterference_lt_scaled_normSq
xiCTaylorThetaTailCoreInterferenceSublinearUpper_of_coreCurrent
xiCTaylorAnisotropicOrientedCoefficientSublinearUpper_of_thetaTailCoreInterference
xiCTaylorAnisotropicLogDerivSublinearUpper_of_thetaTailCoreInterference
riemannHypothesis_of_xiCTaylorThetaTailCoreInterferenceSublinearUpper
xiCTaylorAnisotropicLogDerivSublinearUpper_of_thetaTailCoreCurrent
riemannHypothesis_of_xiCTaylorThetaTailCoreCurrentSublinearUpper
xiCTaylorOddThetaTailCanonicalSchedule
xiCTaylorOddThetaTailCanonicalSchedule_spec
riemannHypothesis_of_xiCTaylorThetaTailCanonicalCoreCurrentSublinearUpper
```

The capstones use only the standard mathlib axioms
`[propext, Classical.choice, Quot.sound]`.

## Status boundary

This card proves the finite orientation-sensitive forcing theorem and discharges every explicit
top-defect term from source estimates.  The unconditionally existing joint schedule is now fixed
once and for all as `xiCTaylorOddThetaTailCanonicalSchedule`; consequently the interface-free
capstone has only `(7)` for this canonical schedule as a hypothesis.  The card does not prove that
the theta-tail core satisfies `(7)`.  Claiming that source inequality without a new proof would be
circular.

## Gates

- [x] odd source-selected super-accurate schedule constructed
- [x] schedule strengthened to make the top defect and derivative super-accurate
- [x] finite theta-tail envelope defined from actual coefficients
- [x] pointwise envelope-to-logarithmic-flux theorem proved
- [x] top-defect cross-interference discharged unconditionally on every mesh fibre
- [x] target reduced to the theta-tail core current alone
- [x] anisotropic sublinear-flux implication proved
- [x] existential schedule interface discharged by a fixed canonical source schedule
- [x] RH terminal implication proved
- [x] all statements formalized in Lean
- [ ] unconditional theta-tail core-current estimate `(7)`
