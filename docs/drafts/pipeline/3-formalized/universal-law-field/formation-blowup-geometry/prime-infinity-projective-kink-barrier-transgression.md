# Prime-infinity projective kink and barrier transgression

- **ID:** `ULF-FBG-001`
- **Stage:** 3-formalized
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/FormationBlowupProjectiveKinkBarrierTransgression.lean`
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [UNCONDITIONAL] [NOT A SELECTOR]`
- **Type:** unconditional pre-divisor blow-up geometry and four-organ reconstruction
- **RH used:** no
- **Divisor used:** no
- **Parents:** `ULF-PHPTCIS-001`, theta likelihood polarization,
  cofinal Gamma Bockstein/Schatten wall, prime--Hodge integral--nuclear defect

## 1. Big-picture reversal

The singular point is not a zero. It is the corner

```text
horizontal grade a = 0,       prime scale log(p) = infinity.
```

Blowing up this corner by the normal coordinate `u=a log(p)` turns the apparently unrelated
theta visibility, likelihood contrast, multiplicative Euler tilt, Gamma Bockstein divergence,
phase quotient, and integral winding into different tensors of one explicit curve. The curve is
the minimal projective kink

```text
z(u)=(v(u),c(u))=(sech(u/2),tanh(u/2)).                (FBG.1)
```

The nuclear object `T` measures its finite closed/open marginals. Its noncompact cotangent is the
Gamma Bockstein. The universal unit is the projective degree and the exact kink action, not either
marginal trace.

## 2. Formation blow-up

For `u in R`, define

```text
v(u)=sech(u/2),
c(u)=tanh(u/2),
R(u)=[[v(u),-c(u)],[c(u),v(u)]].                       (FBG.2)
```

Then

```text
v(u)^2+c(u)^2=1,
R(u) in SO(2),
v(-u)=v(u),          c(-u)=-c(u),
lim_(u->+infinity) R(u)= J,
lim_(u->-infinity) R(u)=-J,                            (FBG.3)
```

where `J=[[0,-1],[1,0]]`. Although the oriented frames have opposite limits, their first columns
define the same line at both ends. Hence `u |-> [z(u)]` extends over the one-point compactification
of `R`:

```text
zbar : R union {infinity} ~= S1  ->  RP1.              (FBG.4)
```

### Theorem A: the blow-up is the projective line

`zbar` is an orientation-preserving homeomorphism. In particular,

```text
degree(zbar)=1.                                        (FBG.5)
```

**Proof.** Every nonvertical real line has a unique unit representative with positive first
coordinate. For `(v(u),c(u))`,

```text
c(u)/v(u)=sinh(u/2),
```

which is a strictly increasing bijection from `R` to `R`. The two missing limits are the same
vertical line in `RP1`. Thus `(FBG.4)` is a continuous bijection between compact Hausdorff circles,
hence a homeomorphism. Its slope coordinate is increasing, so its degree is `+1`. QED.

This integer is created before any divisor is supplied. Reflection does not cancel it: reflection
reverses both the normal coordinate and the oriented frame, while the phase quotient identifies
the antipodal endpoint.

## 3. Exact unit action

Let

```text
theta(u)=arctan(sinh(u/2)).                             (FBG.6)
```

Then

```text
cos(theta(u))=v(u),
sin(theta(u))=c(u),
theta'(u)=v(u)/2,
theta(-infinity)=-pi/2,
theta(+infinity)= pi/2.                                (FBG.7)
```

For any absolutely continuous lift `vartheta` with these endpoint limits, define the formation
blow-up action

```text
A(vartheta)=1/2 integral_R
  (vartheta'(u)^2 + cos(vartheta(u))^2/4) du.           (FBG.8)
```

### Theorem B: sharp projective properness

Every such finite-action lift satisfies

```text
A(vartheta)>=1.                                        (FBG.9)
```

Equality holds exactly when

```text
vartheta'=cos(vartheta)/2                              (FBG.10)
```

almost everywhere. With anchor `vartheta(0)=0`, the unique equality profile is `(FBG.6)`. Hence

```text
A(theta)=1.                                            (FBG.11)
```

**Proof.** Complete the square:

```text
A(vartheta)
 =1/2 integral (vartheta'-cos(vartheta)/2)^2 du
  +1/2 integral vartheta' cos(vartheta) du
 =1/2 integral (vartheta'-cos(vartheta)/2)^2 du
  +1/2 [sin(vartheta)]_(-infinity)^(+infinity)
 =1/2 integral (vartheta'-cos(vartheta)/2)^2 du+1.
```

This proves the bound and equality condition. Separating variables in `(FBG.10)` and imposing the
anchor gives `(FBG.6)`. Directly, `integral_R sech(u/2)^2 du=4`, so `(FBG.11)` also follows from
`theta'=v/2`. QED.

The integer degree and unit action are therefore the same boundary event: topology gives the
lower bound, and the literal theta profile saturates it.

## 4. Prime sampling and the integral--nuclear object

At grade `a` and prime `p`, the corpus visibility and contrast are exactly the blow-up samples

```text
v_a(p)=v(a log(p)),
c_a(p)=c(a log(p)).                                    (FBG.12)
```

Let `V_a,C_a` be their diagonal operators on `ell2(Nat x Primes)` and let `T` be the positive
prime--Hodge integral--nuclear defect. The Stinespring column

```text
W_a x=(V_a x,C_a x)
```

is the operator sampling of the first column of `R`. Equation `(FBG.3)` gives

```text
W_a* W_a=I,
Tr(V_a T V_a)+Tr(C_a T C_a)=1.                         (FBG.13)
```

The same identity holds after every history-tail compression and reconstructs all Kummer
first-exit weights. Thus `T` is a finite normal measure on the blow-up, while `(FBG.5)` is its
ambient projective charge. Off wall, both normal marginals are fractional; the integral lives in
the complete frame.

## 5. Cotangent barrier and Gamma Bockstein

Let the literal one-prime occupancy Fisher weight be

```text
d(p)=p/(p+1)^2.
```

On the open projective chart `|c|<1`, define the logarithmic formation barrier

```text
B_p(c)=-2 d(p) log(1-c^2).                             (FBG.14)
```

Its cotangent is

```text
dB_p/dc = 4 d(p)c/(1-c^2).                             (FBG.15)
```

At the prime sample `c=c_a(p)`, the odds coordinate is

```text
p^a=(1+c_a(p))/(1-c_a(p)),                             (FBG.16)
```

and therefore

```text
dB_p/dc(c_a(p))
 =d(p)(p^a-p^(-a)).                                    (FBG.17)
```

With the corpus orientation

```text
beta_a(p)=d(p)(p^(-a)-p^a),
```

one obtains the exact transgression

```text
beta_a(p)=-dB_p/dc(c_a(p)).                            (FBG.18)
```

**Proof.** Equation `(FBG.16)` is the standard inverse relation between `tanh` and rapidity.
Also `1-c_a(p)^2=v_a(p)^2`. Hence

```text
4c_a(p)/(1-c_a(p)^2)=p^a-p^(-a),
```

which inserted into `(FBG.15)` proves `(FBG.17)--(FBG.18)`. QED.

This identifies the bounded likelihood contrast and the noncompact cofinal Bockstein as tangent
and cotangent coordinates of the same singular projective metric. Multiplicative Euler growth is
the barrier blow-up at the two phase-quotient endpoints; it is not a separate obstruction.

## 6. Fourth-organ prediction and confirmation

For `a!=0`, `(FBG.18)` and `d(p) asymptotic p^(-1)` give

```text
|beta_a(p)| asymptotic p^(-1+|a|).                    (FBG.19)
```

Consequently, for `q>0`, the blow-up geometry predicts

```text
sum_p |beta_a(p)|^q < infinity
  iff 1<q(1-|a|),                                     (FBG.20)
```

with the separate neutral case `beta_0=0`. In particular,

```text
beta_a belongs to every ell^q, q>1  iff a=0.           (FBG.21)
```

This prediction is independently Lean-certified by
`summable_primeGammaCofinalBocksteinSchattenMass_iff` and
`all_order_summable_primeGammaCofinalBocksteinSchattenMass_iff`. The existing Schatten wall is
therefore a cotangent shadow of `(FBG.4)`, while the visibility/contrast trace split is its normal
shadow.

## 7. Direct-subunit consequence

The universal projective defect cannot itself be the residual quantity bounded by the primitive
Euler collision budget. The corpus proves `B_Euler<115/216<1`, whereas `(FBG.9)` proves every
formation blow-up carrying the nonzero projective charge has action at least one.

Thus the proposal

```text
"the whole visibility--contrast blow-up action is <= B_Euler"
```

is mathematically impossible. The direct-subunit programme must first subtract this unit
projective kink as the universal metric anomaly and then bound a genuinely relative residual. A
scalar subtraction is insufficient: `(FBG.18)` shows the anomaly has a bounded normal coordinate,
a divergent cotangent coordinate, and a degree-one projective boundary simultaneously.

## 8. Surviving higher-law target

The new candidate structure is **formation blow-up geometry**: a completion is admissible only if
its normal state, cotangent barrier, projective degree, and open-history transgression are carried
by one map of the blown-up corner. This is stronger than matching any one reader.

For RH selection, one still needs a zero-independent theorem identifying the common divergent
formation/completion metric with the universal kink `(FBG.1)` and proving that, after removing
that full projective object, the remaining prime-mixed relative boundary has nuclear action at
most `B_Euler`. The already proved escape-capacity gap would then exclude an additional completed
escape unit. Merely declaring the Xi horizon to be this residual is forbidden: that is the old
same-boundary receiver.

## 9. Hostile audit

- Hyperbolic parametrization, `RP1 ~= S1`, completion of squares, and logarithmic barriers are
  classical. No novelty is claimed for them separately.
- New corpus content is the exact simultaneous reconstruction `(FBG.12)--(FBG.21)` across theta
  polarization, prime--Hodge nuclear charge, Euler odds, Gamma corona, and the all-order Schatten
  wall.
- `ULF-RPGT-001` already uses restricted-unitary winding on a completed contour. This construction
  is different: its loop is the pre-divisor normal blow-up of `a=0,p=infinity`, contains no Xi
  contour, and its action is exactly one before completion.
- `ThetaCuspHawkingUnitWindingSelectionNoGo` shows generic lossless/KMS mixing does not force onset
  order one. Here order one comes from the literal exponential odds relation `(FBG.16)`, not from
  generic two-channel dynamics.
- The projective unit is not by itself RH selection; it exists for every nonzero grade. Its new
  leverage is to identify the full universal anomaly that must be removed and to forbid using the
  entire blow-up action as a subunit residual.

## 10. Formal status

Fully formalized in Lean by
`FormationBlowupProjectiveKinkBarrierTransgression.lean`. The module constructs the bundled
one-point projective homeomorphism, proves orientation/degree one, both frame limits, the phase
identities, and the exact square-completion theorem on the full absolutely-continuous finite-action
class. Equality is characterized almost everywhere by the kink ODE and the anchored equality case
is uniquely the canonical profile. Prime sampling, marginal trace conservation, exact barrier
transgression, Schatten threshold, all-order neutral classification, and the strict primitive
Euler-budget obstruction are included in the closed certificate
`formationBlowupProjectiveKinkBarrierTransgression_closed`.

Targeted `lake env lean` and leaf-only `lake build` checks pass. `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`; no project axiom, `sorry`, premise, divisor, or RH
hypothesis is used.
