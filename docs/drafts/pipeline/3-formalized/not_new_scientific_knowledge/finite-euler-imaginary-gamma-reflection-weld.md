# Finite Euler multipliers are imaginary-slope Gamma-reflection welds

- **ID:** `finite-euler-imaginary-gamma-reflection-weld`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (Lean), `[VALUE RELATION]`, `[REFLECTION]`, `[CONSTRAINT]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** Euler's Gamma reflection formula;
  `semilocal-dual-pair-euler-connection-source-law.md`;
  `finite-euler-connection-cauchy-phase-chambers.md`;
  `../needs-audit/neutral-gamma-ratio-full-differential-boundary-depth-law.md`

## Goal

Expose the exact Gamma object already hidden in each finite Euler local factor.  This supplies a
literal value bridge between the semilocal Euler connection and the Gamma-reflection corpus, and it
produces a two-prime static orientation selector.  The bridge does not assert that the selector is
positive or real on Xi zeros.

## One local factor as a reciprocal Gamma pair

Fix a prime `p`, put `L=log(p)`, and define

```text
g_p(s)=1-p^(-s),
u_p(s)=i L s/(2 pi).                                      (1)
```

Euler reflection and `sin(iw)=i sinh(w)` give

```text
Gamma(u_p(s)) Gamma(1-u_p(s))
  =pi/sin(pi u_p(s))
  =pi/(i sinh(Ls/2)).                                     (2)
```

Since `1-exp(-Ls)=2exp(-Ls/2)sinh(Ls/2)`, equation `(2)` yields the exact entire identity

```text
g_p(s)
  =-2 i pi exp(-Ls/2)
     /[Gamma(u_p(s)) Gamma(1-u_p(s))].                    (3)
```

The apparent Gamma poles cause no difficulty: `(3)` is a product of reciprocal Gamma functions,
and both sides are entire in `s`.

For a finite prime set `S`, multiplication gives the semilocal place multiplier

```text
g_S(s)=product_(p in S)g_p(s)

 =(-2 i pi)^|S| exp(-s/2 sum_(p in S)log(p))
   product_(p in S)
     [Gamma(u_p(s)) Gamma(1-u_p(s))]^(-1).                (4)
```

Thus the finite Euler carrier is already a signed Gamma product, but not one covered by the
positive-real-slope Gamma boundary laws: its slopes occur in prime-dependent imaginary pairs
`+i log(p)/(2pi)` and `-i log(p)/(2pi)`.

## The Euler connection is a digamma-reflection anomaly

Logarithmic differentiation of `(3)` gives

```text
Phi_p(s)
  =d/ds log g_p(s)
  =log(p) p^(-s)/(1-p^(-s))

  =-L/2+iL/(2pi)
       [psi(1-u_p(s))-psi(u_p(s))].                       (5)
```

The digamma reflection identity

```text
psi(1-u)-psi(u)=pi cot(pi u)                              (6)
```

turns `(5)` into the equivalent hyperbolic formula

```text
Phi_p(s)=L/2 [coth(Ls/2)-1].                              (7)
```

Therefore the connection in the semilocal dual-pair theorem is exactly a finite sum of scaled
digamma-reflection anomalies.  This is not an analogy between Euler and Gamma sources: `(3)` and
`(5)` are equality of the source values and their logarithmic connections.

Differentiating once more identifies the literal actual Euler-parameter tangent with both the
spectral curvature and the trigamma-reflection curvature.  If

```text
T_p(s)=log(p)p^(-s)/(1-p^(-s))^2,
```

then

```text
Phi_p'(s)=-log(p) T_p(s),                                (7a)

T_p(s)=-log(p)/(4 pi^2)
  [psi'(u_p(s))+psi'(1-u_p(s))].                         (7b)
```

Equation `(7b)` follows from the trigamma reflection formula
`psi'(u)+psi'(1-u)=pi^2/sin(pi u)^2` and `sin(iw)=i sinh(w)`.  It is the curvature-level companion
to the value-level digamma law `(5)`.

The top-down use is exact.  On the open strip, equality of either side of `(7a)` at `conj(rho)`
and `1-rho`, for any one prime, is equivalent to vanishing of that prime seam and hence to
`Re(rho)=1/2`.  This does not prove the equality on Xi fibres.  It shows that a completed Gamma
normal-curvature reader and an Euler-parameter Hessian reader have the same finite target, rather
than requiring a conversion through the full Lambert tail.

## FE-symmetric Gamma quartet

Define the FE-symmetric local determinant

```text
B_p(s)=g_p(s)g_p(1-s)
      =(1-p^(-s))(1-p^(-(1-s))).                          (8)
```

Then

```text
B_p(1-s)=B_p(s),
d/ds log B_p(s)=Phi_p(s)-Phi_p(1-s).                      (9)
```

The right side of `(9)` is exactly the FE-paired Euler connection used by the Cauchy phase-chamber
law.  Applying `(3)` to `s` and `1-s` writes `B_p` as a quartet of reciprocal Gamma factors.  Hence
the Cauchy Poisson radial difference is the centered divided-difference shadow of this
imaginary-slope Gamma-reflection quartet.

On the critical line,

```text
B_p(1/2+i t)=|1-p^(-1/2-it)|^2>0.                        (10)
```

So every local quartet lies in the positive-real determinant chamber there.

## Two-prime reality selector

Let `s=sigma+i t`, with `t!=0`.  Put

```text
a_p=p^(-sigma),
b_p=p^(sigma-1),
theta_p=t log(p).                                        (11)
```

Expanding `(8)` gives the exact imaginary part

```text
Im B_p(s)=(a_p-b_p) sin(theta_p).                         (12)
```

Since `p>1`,

```text
a_p=b_p iff sigma=1/2.                                   (13)
```

Let `p` and `q` be distinct primes.  If both `B_p(s)` and `B_q(s)` are real and
`sigma!=1/2`, equations `(12)`--`(13)` force

```text
t log(p)=k pi,
t log(q)=ell pi                                           (14)
```

for nonzero integers `k,ell`.  Then `log(p)/log(q)=k/ell` is rational, contradicting unique
factorization.  Conversely `(10)` gives strict positivity on the line.  Therefore

```text
sigma=1/2
  iff B_p(s) and B_q(s) are both real
  iff B_p(s) and B_q(s) are both positive real,           (15)
```

for every `t!=0` and every pair of distinct primes.

This is a finite source constraint, not a flow and not an asymptotic criterion.  It is also
stronger than a one-prime test: one prime has exceptional resonant horizontal lines, while the
second prime removes them arithmetically.

## Top-down Xi consequence and exact open premise

Every nontrivial Xi zero has nonzero height.  Thus for any fixed distinct primes, for example
`p=2,q=3`, equation `(15)` gives the formal target

```text
[OPEN SOURCE THEOREM]
for every Xi zero rho, B_2(rho) and B_3(rho) are real

  -> every Xi zero has Re(rho)=1/2
  -> RH.                                                   (16)
```

The first line of `(16)` is not proved and must not be inferred from the functional equation.
Functional-equation symmetry gives `B_p(1-rho)=B_p(rho)`; it does not make `B_p(rho)` real.
Equation `(16)` is useful only if a determinant, Sonin, or source constraint independently forces
reality of the two explicit semilocal values.

## Relation to the Gamma boundary laws

The neutral signed-Gamma boundary theorem proves that finite positive-real-slope Gamma jets cannot
supply the complementary prime-character module.  Identity `(4)` identifies the positive escape
rather than contradicting that theorem:

```text
finite positive-real-slope Gamma family
  -> finite boundary carrier,

cofinal prime Euler family
  = cofinal imaginary-slope Gamma-reflection family
  -> full independent prime character carrier.            (17)
```

The missing prime information is carried by the unbounded collection of incommensurable imaginary
slopes `log(p)/(2pi)`.  A Gamma-based RH construction that uses `(4)` must retain those slopes; if it
collapses them to finitely many positive-real-slope Gamma jets, it loses precisely the arithmetic
complement required by the boundary theorem.

## Formal interfaces and status

- `RHTower/DigammaBounds.lean` contains the digamma reflection identity `(6)`.
- `RHTower/PolygammaReflection.lean` contains its differentiated hierarchy.
- `HTGeometry/KroneckerFlow.lean` formalizes finite prime-log nonresonance, the arithmetic input of
  the two-prime selector.
- `RHTower/XiWeilOneCauchyGate.lean` is the completed one-Cauchy RH consumer, but `(15)` does not
  discharge its source sign.

`RHTower/FiniteEulerGammaReflectionWeld.lean` now formalizes the entire reciprocal-Gamma
packaging, the exact one-prime Gamma factorization, and its finite semilocal product and quartet
forms. `RHTower/FiniteEulerLocalQuartet.lean` formalizes the two-prime reality/positive-real
selector, while `RHTower/FiniteEulerGammaConnection.lean` supplies the exact finite derivative
identities. `RHTower/FiniteEulerGammaDifferentialWeld.lean` supplies the direct digamma-reflection,
hyperbolic-cotangent, and quartet logarithmic-derivative identities. The exact tangent/trigamma
identity is already formalized as `primeEulerUnitTangent_eq_trigammaReflection`. Targeted checks and
axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.

No independent unconditional source theorem yet forces the two selected local values real on
arbitrary Xi fibres. That premise is equation `(16)`, explicitly outside this finite weld theorem;
it does not block stage-3 formalization of equations `(3)`--`(15)`.

## Literature

- [DLMF 5.5.E3](https://dlmf.nist.gov/5.5.E3), Euler's Gamma reflection formula.
- [DLMF 5.5.E4](https://dlmf.nist.gov/5.5.E4), the digamma reflection formula.
- A. Connes, C. Consani, H. Moscovici,
  [*Zeta zeros and prolate wave operators: semilocal adelic operators*](https://arxiv.org/abs/2310.18423),
  for the finite semilocal multiplier represented by `(4)`.

## Gates

- [x] local Euler factor Gamma-reflection factorization
- [x] finite semilocal multiplier factorization
- [x] exact digamma-reflection connection value
- [x] exact spectral-curvature/actual-tangent identity
- [x] exact actual-tangent/trigamma-reflection identity formalized as
      `primeEulerUnitTangent_eq_trigammaReflection`
- [x] FE-symmetric Gamma quartet and logarithmic derivative
- [x] critical-line positive-real chamber
- [x] two-prime reality selector away from height zero
- [x] formalize the Gamma-reflection factorization and finite two-prime selector
- [ ] find an independent source theorem forcing the two selected values real on Xi fibres
- [ ] conclude RH

The two unchecked items are the separate RH-facing premise and its consumer, not claims of this
finite Euler--Gamma weld theorem.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/FiniteEulerGammaDifferentialWeld.lean` -- pass
- `lake build GaloisForLFunctions.RHTower.FiniteEulerGammaDifferentialWeld` -- pass
- new differential-weld theorem axioms: `[propext, Classical.choice, Quot.sound]`

## Log

- 2026-08-23 (Codex) — reused the existing reciprocal-Gamma, trigamma, and two-prime-selector
  corpus rather than duplicating them. Added the missing direct digamma anomaly, coth form, and
  quartet log-derivative bridge in `FiniteEulerGammaDifferentialWeld.lean`; focused source check,
  target build, and axiom audit pass. Every theorem asserted in `(3)`--`(15)` is now formalized;
  moved to stage 3.
