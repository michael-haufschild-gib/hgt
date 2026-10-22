# Variable-width two-edge profiles are exactly the full aperture parity sectors

- **ID:** `ccm-variable-width-two-edge-principalization-law`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper) / FRONTIER-CONJECTURE CALIBRATION
- **Scientific status:** `[PROVED HERE] [ELEMENTARY STRUCTURAL LAW]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Statement:** At every aperture, positive- and negative-reflection functions supported in the
  aperture are each linearly equivalent to one-sided boundary profiles whose width equals the
  aperture.  Consequently a variable-width two-edge channel is the whole parity sector; uniform
  profile tightness is compulsory in every nonvacuous semilocal profile decomposition.

## Setup

Let `a>=0`, let `E` be a real vector space, and let

```text
H_a^+
 ={u:R->E : u(-x)=u(x),  u(x)=0 when |x|>a},

H_a^-
 ={u:R->E : u(-x)=-u(x), u(x)=0 when |x|>a},

P_a^+
 ={f:R->E : f(s)=0 when s notin [0,a]},

P_a^-
 ={f in P_a^+ : f(a)=0}.                                     (VW1)
```

Define the positive-edge readout

```text
R_a u(s)=1_[0,a](s)u(a-s),                                  (VW2)
```

and the two parity reconstructions

```text
T_a^+ f(x)=f(a-|x|),

T_a^- f(x)
 =f(a-x)   if x>=0,
 =-f(a+x)  if x<0.                                          (VW3)
```

## Theorem `[PROVED HERE]`

For every `a>=0`,

```text
R_a T_a^+=id_(P_a^+),     T_a^+ R_a=id_(H_a^+),

R_a T_a^-=id_(P_a^-),     T_a^- R_a=id_(H_a^-).             (VW4)
```

All four maps are linear.  Hence

```text
H_a^+ ~=_lin P_a^+,
H_a^- ~=_lin P_a^-.                                         (VW5)
```

### Proof

If `0<=s<=a`, then `a-s>=0`, so

```text
R_a T_a^+f(s)
 =f(a-|a-s|)=f(s),

R_a T_a^-f(s)
 =f(a-(a-s))=f(s).                                          (VW6)
```

The odd endpoint condition `f(a)=0` is exactly the reflection-fixed value `u(0)=0`.  Both sides
vanish outside `[0,a]`.  Conversely, if `|x|<=a`, then

```text
T_a^+R_au(x)=u(|x|)=u(x)        for u in H_a^+;              (VW7)
```

and the signed version gives `u(x)` for `u in H_a^-`.  If `|x|>a`, the readout argument
`a-|x|` is negative and both sides vanish.  This proves `(VW4)`.  Linearity is pointwise, proving
`(VW5)`.

## Positive semilocal consequence

The representation

```text
u_a(x)=f_a(a-|x|)                                           (VW8)
```

does not identify a special boundary state when the allowed profile width is `a`: every even
aperture vector has exactly this form.  The same is true in the odd sector.  Thus the expression
"all loss of compactness is carried by two-edge profiles" has mathematical content only after a
uniform tightness condition is imposed, for example

```text
lim_(L->infinity) sup_n
  integral_(L)^(a_n)|f_n(s)|^2 ds=0,                         (VW9)
```

or after an equivalent fixed-width profile decomposition with a coercive vanishing/diffuse
remainder.

This is a positive carrier law:

```text
nontrivial two-edge localization
  = boundary coordinate + uniform profile tightness.         (VW10)
```

Profile geometry without `(VW9)` carries no selection information because it is merely a linear
coordinate on the entire aperture space.

## Effect on the frontier conjecture

The conjecture
`cofinal-prolate-weil-relative-normal-form-conjecture.md` must use fixed profiles, a square-summable
family of translated fixed-width profiles, and a quantitative tightness/vanishing alternative.
Allowing one arbitrary `a_n`-dependent boundary profile would make its exhaustion clause tautological
by `(VW4)`.

The exact remaining structural research problem is therefore not existence of a boundary readout.
It is a source-specific concentration--compactness theorem proving that every bounded-frame
sequence splits into:

```text
uniformly tight translated boundary profiles
  + the Fuchs-safe constrained-prolate sector
  + a coercive diffuse/oscillatory remainder.                 (VW11)
```

## Novelty classification

The linear equivalences `(VW4)`--`(VW5)` are elementary changes of coordinate and are not claimed
as new scientific knowledge.  Their research value is a sharp anti-theatre calibration: they
remove a vacuous formulation of the proposed universal profile law and identify uniform tightness
as a load-bearing hypothesis.

## Lean status

The complete theorem is formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/CCM/CCMTwoEdgeVariableWidthPrincipalization.lean` for arbitrary
real vector-valued functions.  The module constructs the even aperture, odd aperture, unrestricted
one-sided profile, and midpoint-vanishing odd-profile submodules and the two explicit linear
equivalences `(VW5)`.

## Gates

- [x] positive-edge readout defined
- [x] even reconstruction proved
- [x] odd reconstruction proved
- [x] support preservation proved
- [x] both linear equivalences constructed
- [x] variable-width vacuity isolated positively as the tightness obligation
- [x] narrow Lean verification — `VERIFIED 2026-07-27`.
      `lake build GaloisForLFunctions.RHTower.CCM.CCMTwoEdgeVariableWidthPrincipalization`
      completes successfully (1976 jobs), the module is registered in the
      `GaloisForLFunctions.RHTower` umbrella, and a targeted axiom audit of all six headline
      declarations — `evenTwoEdgePacket_apertureBoundaryReadout`,
      `oddTwoEdgePacket_apertureBoundaryReadout`, `apertureBoundaryReadout_evenTwoEdgePacket`,
      `apertureBoundaryReadout_oddTwoEdgePacket`, `evenApertureBoundaryLinearEquiv`,
      `oddApertureBoundaryLinearEquiv` — reports only
      `[propext, Classical.choice, Quot.sound]`.  Project `formal_tools.py lint` passes.
- [ ] connect the tightness obligation to the frontier conjecture's profile-exhaustion statement

## Log

- 2026-07-19 -- Proved the exact variable-width principalization and used it to replace the naive
  "boundary channel" formulation by a fixed-width/tight-profile obligation.
