# Route J: four-atom literal profiles encode exactly one transverse reflection orbit

**Status:** `[PAPER+LEAN-PROVED] [CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]`

## Frontier

The sharp arity-four construction in
`../../3-formalized/new_scientific_knowledge/route-j-literal-reflection-profile-four-atom-threshold.md`
shows that one common four-atom coefficient vector can carry equal nonzero charge at one
off-center reflected full-turn pair. Its coefficients were constructed from the reciprocal
damping radius `r`.

That construction leaves a source-provenance question:

> Can the same projective four-atom profile work at two different transverse reflection orbits,
> or does its coefficient ray already reveal the orbit for which it was fitted?

The answer is rigid. Every nonzero four-atom equal-charge profile at one orbit is the previously
constructed canonical ray. Two canonical rays are projectively equal only when their radii are
equal or reciprocal. Consequently one literal arity-four leading profile has transverse
information capacity exactly one reflection orbit.

This does not prove RH and does not close Route J. It proves that the minimal local survivor is
target-informative: a divisor-independent construction of that ray must itself predict the
transverse displacement rather than obtain it from local interpolation.

## Setup

For real weights `a=(a_1,a_2,a_3,a_4)`, define

```text
Phi_a(X)=sum_(j=1)^4 a_j(1-X^j).                       (1)
```

Then `Phi_a(1)=0` and `deg Phi_a<=4`. Fix `T!=0`, `r>0`, `r!=1`, and put `q=r^(-1)`. At the
reflected full-turn pair, one common leading profile carries equal reflected charge `m` precisely
when

```text
Phi_a(r)=Phi_a(q)=0,
T r Phi_a'(r)=T q Phi_a'(q)=m.                         (2)
```

Define

```text
A_r(X)=(X-1)(X-r)(X-q),                                (3)

s(r)=(1+r+r^2+r^3+r^4)/(r(1+r+r^2)),                  (4)

P_r(X)=A_r(X)(X-s(r)).                                 (5)
```

Let `B(r)` be the unique weight vector satisfying `Phi_(B(r))=P_r`. Its fourth coordinate is
`B_4(r)=-1`.

## Theorem A: complete classification of arity-four equal-charge profiles

**Theorem.** Suppose the two value equations in `(2)` hold and the two derivative charges are
equal (the common charge may be zero). Then there is a unique scalar `C` such that

```text
Phi_a=C P_r,
a=C B(r).                                              (6)
```

Thus the entire solution space is the canonical line. If the common charge is nonzero, then
`C!=0`, so the nonzero solution space of `(2)` is exactly one projective ray.

**Proof.**

The three numbers `1,r,q` are distinct. Indeed, positivity and `r!=1` give `r!=q`, while neither
`r` nor `q` equals `1`. The three roots in `(2)` and the degree bound imply

```text
Phi_a=A_r Q                                             (7)
```

for a polynomial `Q` of degree at most one. At the two simple reciprocal roots,

```text
r A_r'(r)=r(r-1)(r-q),
q A_r'(q)=(r-1)(r-q)/r^2.                              (8)
```

Consequently the equality of the two derivative charges in `(2)` is equivalent to

```text
Q(q)=r^3 Q(r).                                         (9)
```

On the two-dimensional vector space of affine polynomials, define

```text
ell_r(Q)=Q(q)-r^3 Q(r).                                (10)
```

This functional is nonzero because

```text
ell_r(1)=1-r^3!=0.                                     (11)
```

Hence `ker ell_r` is one-dimensional. Direct substitution of `(4)` gives

```text
q-s(r)=r^3(r-s(r)),                                    (12)
```

so `X-s(r)` is a nonzero element of `ker ell_r`. Therefore `(9)` forces

```text
Q=C(X-s(r))                                            (13)
```

for a unique scalar `C`. Equations `(5)`, `(7)`, and `(13)` prove `Phi_a=C P_r`. If the common
charge is nonzero, `C=0` would give `Phi_a=0` and hence zero charge, a contradiction.

Finally, every polynomial of degree at most four that vanishes at `1` has a unique representation
of the form `(1)`: its nonconstant coefficients are `-a_j`, and its value at `1` determines the
constant coefficient. Comparing this representation for `Phi_a` and `C P_r` gives `a=C B(r)`.
∎

## Theorem B: the canonical ray determines the reciprocal radius orbit

**Theorem.** Let `r,t>0`. If `B(r)` and `B(t)` are projectively equal, then

```text
t=r or t=r^(-1).                                       (14)
```

**Proof.**

Projective equality gives `B(t)=lambda B(r)` for some nonzero `lambda`. Since both fourth
coordinates equal `-1`, necessarily `lambda=1`. In particular,

```text
B_3(r)=B_3(t).                                         (15)
```

Put

```text
x=r+r^(-1),       y=t+t^(-1).                          (16)
```

Positivity gives `x,y>=2`. Dividing numerator and denominator in `(4)` by `r^2` yields

```text
s(r)=(x^2+x-1)/(x+1)=x-1/(x+1).                       (17)
```

The third weight is the sum of the four roots:

```text
B_3(r)=1+x+s(r)=1+2x-1/(x+1).                         (18)
```

Define `g(u)=1+2u-1/(u+1)`. For `u,v>=2`,

```text
g(u)-g(v)
  =(u-v)(2+1/((u+1)(v+1))).                           (19)
```

The second factor is strictly positive. Equations `(15)` and `(18)` therefore imply `x=y`.
Clearing the positive denominator `rt` in

```text
r+r^(-1)=t+t^(-1)
```

gives

```text
(r-t)(rt-1)=0.                                        (20)
```

Thus `t=r` or `t=r^(-1)`. ∎

## Theorem C: one four-atom profile cannot screen two transverse orbits

**Theorem.** Fix one weight vector `a`. Suppose it satisfies `(2)` with nonzero charge at
`r>0`, `r!=1`, and also satisfies the analogous two value-kernel equations and equal-reflected-
charge equation at `t>0`, `t!=1`. The common charge at `t` may be zero. Then

```text
t=r or t=r^(-1).                                       (21)
```

**Proof.**

Theorem A gives scalars `C,D` with

```text
a=C B(r)=D B(t).
```

The nonzero charge at `r` forces `C!=0`; the fourth coordinate identity then forces `D=C!=0`.
Hence the two canonical rays are projectively equal. Theorem B gives `(21)`. ∎

## Source consequence

For a full-turn atom lattice `T,2T,3T,4T`, the reciprocal damping radius is

```text
r=exp(-T y),
```

where `y` is the transverse displacement from the centered line. The support already records
`T`; Theorem B shows that the projective coefficient vector records `{r,r^(-1)}`, hence `|y|`.
Therefore the complete minimal local screen records the reflected divisor pair up to the
functional-equation involution.

This yields the exact source-provenance trichotomy for the arity-four survivor:

```text
one fixed four-atom ray
  -> at most one transverse reflection orbit;

multiple transverse orbits
  -> changing coefficient ray, larger support, or non-atomic/singular carrier;

divisor-independent four-atom construction
  -> must prove the matching orbit from source data.
```

The theorem does not declare a coincidental source/orbit match impossible. It proves that such a
match is a substantive arithmetic prediction, not a reflection-symmetric free parameter.

## Novelty and theatre audit

- `[LITERATURE]` Hermite interpolation and degree-bounded interpolation at prescribed value and
  derivative nodes are classical. See B. Sadiq and D. Viswanath, *Barycentric Hermite
  Interpolation*, arXiv:1105.3466, and S. Bossoney and M. Troyanov, *A Direct Approach to Hermite
  Interpolation*, arXiv:2607.17998.
- `[LITERATURE]` Reciprocal and self-inversive polynomial theory is classical; derivative
  questions for that class occur, for example, in A. Dubickas and J. Jankauskas, *On Mahler
  measures of a self-inversive polynomial and its derivative*, Bull. London Math. Soc. 42 (2010),
  DOI 10.1112/blms/bdp104.
- `[BRIDGE]` Factorization by three distinct roots, the one-dimensional kernel computation, and
  injectivity of `u+u^(-1)` modulo inversion are elementary and receive no standalone novelty
  claim.
- `[CORPUS AUDIT]` Targeted search found the arity-four existence theorem, two-atom projective
  rigidity, and unrelated finite-transverse exponential-series rigidity, but no classification
  showing that every arity-four equal-charge profile is the canonical ray or that this ray
  determines exactly one reciprocal damping orbit.
- `[EXTERNAL AUDIT]` Targeted primary-source searches found generic Hermite and reciprocal
  polynomial theory but no source-current theorem combining one literal coefficient vector,
  reciprocal full-turn value kernels, equal weighted derivative charge, and orbit reconstruction.
- `[CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]` The exact classification `(6)` and transverse
  information-capacity law `(21)` are the candidate new conjunction. External priority is not
  certified.
- `[THEATRE CHECK]` The result is not presented as an RH selector. It instead proves that the
  explicit survivor is target-informative and identifies the precise additional source theorem
  required to use it without divisor fitting.

## Lean certificate

Formalized unconditionally in

```text
formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedFourAtomTransverseOrbitRigidity.lean
```

The formal proof uses direct symmetric coefficient elimination. It derives three linear rows in
`x=r+r⁻¹`; the combination

```text
hsum - 2 hder - (2 - 3x) hdelta
```

factors as

```text
-2(x-2)((1+x)a₃+x(2x+3)a₄)=0.
```

Positivity and `r!=1` give `x>2`, determining `a₃`, then `a₂` and `a₁`. The orbit theorem proves
injectivity of the third canonical coordinate and composes the two classifications. Principal
declarations:

```text
signedFourAtom_literalReflection_equalCharge_profile_classification
signedFourAtomLiteralRayThree_orbit_injective
signedFourAtom_literalReflection_twoOrbit_rigidity
```

Direct leaf verification with `lake env lean` and the exact-module build both pass. Scratch
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for every declaration
above; no project axiom enters the theorem.
