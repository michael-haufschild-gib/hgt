# Xi Taylor theta-tail finite coefficient gate

- **ID:** `xi-taylor-theta-tail-finite-coefficient-gate`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT THE OPEN PRODUCER]`
- **Parent target:**
  `../../1-in-progress/xi-taylor-oriented-finite-coefficient-sublinear-flux.md`

## Statement

There exists a source-selected super-accurate canonical Xi Taylor schedule consisting entirely of
odd cutoffs

```text
N(k) = 2(D(k)+1)+1.                                      (1)
```

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

No Xi zero location, real-rootedness, anti-Herglotz positivity, or limiting measure is used in
this gate.

## Proof

Local uniform convergence of the Taylor sections and their derivatives gives a threshold after
which every degree meets the required expanding-ball error.  Recursively choose increasing source
indices and replace each by the larger odd degree `(1)`.  This proves the odd super-accurate
schedule.

The oriented top-defect theorem gives

```text
J_(P_(2d+3))(z) <= A_d(z)                                (6)
```

in the upper half-plane.  Combining `(3)` and `(6)` produces the strict denominator-cleared
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
xiCTaylorThetaTailCoreInterference
xiCTaylor_logDeriv_im_lt_of_thetaTailCoreInterference_lt
XiCTaylorThetaTailCoreInterferenceSublinearUpper
xiCTaylorAnisotropicOrientedCoefficientSublinearUpper_of_thetaTailCoreInterference
xiCTaylorAnisotropicLogDerivSublinearUpper_of_thetaTailCoreInterference
riemannHypothesis_of_xiCTaylorThetaTailCoreInterferenceSublinearUpper
```

The capstones use only the standard mathlib axioms
`[propext, Classical.choice, Quot.sound]`.

## Status boundary

This card proves the requested finite orientation-sensitive forcing theorem.  It does not prove
that the theta-tail core satisfies `(5)`.  Since `(5)` plus the unconditionally existing odd
schedule implies RH, claiming the source inequality without a new proof would be circular.

## Gates

- [x] odd source-selected super-accurate schedule constructed
- [x] finite theta-tail envelope defined from actual coefficients
- [x] pointwise envelope-to-logarithmic-flux theorem proved
- [x] anisotropic sublinear-flux implication proved
- [x] RH terminal implication proved
- [x] all statements formalized in Lean
- [ ] unconditional theta-tail core-current estimate `(5)`
