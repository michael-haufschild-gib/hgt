# A geometric CDD product gives a hypertranscendental local interacting QFT

- **ID:** `geometric-cdd-hypertranscendental-local-qft`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE THEOREM / CONSTRUCTIVE QFT / PHYSICAL HT EXISTENCE
- **Scientific status:** `[PAPER PROOF COMPLETE; INDEPENDENT AUDIT PENDING]`
  `[PHYSICAL EXISTENCE BRIDGE] [NOVELTY UNVERIFIED AND LIKELY PARENT-DERIVABLE]`
- **Scope:** general hypertranscendence in factorizing quantum field theory; no RH or distinguished
  special-function input
- **Statement:** A geometrically spaced infinite Blaschke--CDD product is a regular factorizing
  scattering function, is hypertranscendental in its crossing coordinate, and therefore defines
  through the inverse-scattering construction an asymptotically complete local interacting
  two-dimensional QFT whose exact two-particle scattering observable is hypertranscendental.

## Goal

Produce a literal physical carrier of hypertranscendence for which interaction is not inferred
from a reporter or a composite observable.  Nontrivial scattering is the interaction witness, and
the constructive inverse-scattering theorem supplies the local quantum field theory.

## Construction

Fix real parameters

```text
0 < q < 1,       C > 1.
```

Define the meromorphic product

```text
P_q(t) = product_(k>=0) ((1-q^k t)/(1+q^k t))^2             (1)
```

and the rapidity scattering function

```text
t_C(theta) = -i sinh(theta)/C,
S_(q,C)(theta) = -P_q(t_C(theta)).                           (2)
```

The square in `(1)` is physical rather than decorative.  The zeros in the physical strip occur
in the reality-paired set

```text
beta_k^+ =  arcosh(C q^(-k)) + i pi/2,
beta_k^- = -arcosh(C q^(-k)) + i pi/2,
```

and both have the same value `sinh(beta_k^+)=sinh(beta_k^-)=i C q^(-k)`.  Thus `(1)` is the infinite analogue of
the paired finite CDD products in the standard regular-scattering family.

## Claim A -- meromorphic product and exact constraint

The products `(t;q)_infinity` and `(-t;q)_infinity` converge uniformly on compact subsets of the
complex plane.  Hence

```text
P_q(t) = ((t;q)_infinity/(-t;q)_infinity)^2
```

is meromorphic, analytic at `t=0`, and satisfies

```text
P_q(t)  = ((1-t)/(1+t))^2 P_q(qt),                          (3)
P_q(-t) = P_q(t)^(-1).                                      (4)
```

It has double zeros at `q^(-k)` and double poles at `-q^(-k)`.

## Claim B -- factorizing-scattering axioms

In the upper-half-plane crossing coordinate the paired zero sequence is
`g_k^+=iCq^(-k)` and `g_k^-=-conj(g_k^+)=g_k^+`, counted with multiplicity two.  It has no finite
limit point and satisfies the Blaschke condition

```text
sum_k 2 Im(g_k)/(1+|g_k|^2)
  = sum_k 2 Cq^(-k)/(1+C^2q^(-2k)) < infinity.               (5a)
```

Lechner's zero-set characterization therefore already supplies compact convergence, continuity
on the physical boundary, and bounded analyticity on the physical strip.

For real `theta`, `t_C(theta)` is purely imaginary, so every factor in `(1)` has modulus one.
Equations `(2)` and `(4)`, together with `sinh(theta+i pi)=-sinh(theta)`, give

```text
conj(S(theta)) = S(theta)^(-1) = S(-theta) = S(theta+i pi).  (5)
```

If `0 < Im(theta) < pi`, then

```text
Re(t_C(theta)) = cosh(Re theta) sin(Im theta)/C > 0.
```

For `a>0` and `Re t>0`, one has `|1-a t|<|1+a t|`.  Every finite partial product is therefore
bounded by one on the physical strip, and compact convergence gives

```text
|S_(q,C)(theta)| <= 1,       0 < Im(theta) < pi.             (6)
```

The poles solve `sinh(theta)=-i Cq^(-k)`.  Their nearest imaginary parts are `-pi/2` and
`3pi/2`.  Hence `(2)` is analytic on every enlarged strip

```text
-kappa < Im(theta) < pi+kappa,      0 < kappa < pi/2.       (7)
```

### Uniform boundedness lemma on the enlarged strip `[PROVED ON PAPER]`

Fix `0<kappa<pi/2`.  On `0<=Im(theta)<=kappa`, write `theta=u+iy`.  Then

```text
|t_C(theta)|^2 = (sinh(u)^2 + sin(y)^2)/C^2,
Re(t_C(theta)) = cosh(u) sin(y)/C >= 0.                       (7a)
```

Choose `u_0>0`.  If `|u|>=u_0`, the argument of `t_C(theta)` is separated from the positive real
axis by

```text
delta = arctan(tanh(u_0) cot(kappa)) > 0.                    (7b)
```

The case `|u|<=u_0` is compact.  It contains no zero because every zero has imaginary rapidity
`pi/2`; hence `P_q(t_C(theta))` has a positive minimum and finite maximum there.

For the noncompact part put `z=t_C(theta)` and choose `n` so that

```text
1 <= |q^n z| < q^(-1).
```

Iteration of `(3)` gives

```text
P_q(z) = P_q(q^n z)
         product_(j=0)^(n-1) ((1-q^j z)/(1+q^j z))^2.       (7c)
```

All `q^j z` have the same argument.  For `|q^j z|>=2`,

```text
|log |(1-q^j z)/(1+q^j z)|| <= A/|q^j z|                   (7d)
```

with an absolute `A`; this follows from the power series for `log(1+w)` at `w=1/(q^jz)`.
The reverse geometric sum of the right side before the orbit reaches modulus `2` is bounded by a
constant depending only on `q`.  Between moduli `1` and `2`, only a bounded number of orbit points
occur, and `(7b)` gives a uniform positive lower bound on `|1-q^jz|`; `Re(q^jz)>=0` gives one for
`|1+q^jz|`.  Finally `q^nz` lies in the compact annular half-sector

```text
1 <= |w| <= q^(-1),       Re(w) >= 0,
delta <= |arg w| <= pi/2,
```

which contains no zero or pole.  Thus `(7c)` is uniformly bounded above and away from zero on the
upper lower-edge substrip.  Equation `(4)` bounds the reflected strip below the real axis, and
crossing bounds the corresponding strip above `Im(theta)=pi`.  This proves uniform boundedness on
the closure of every strip `(7)`.

No numerical estimate enters the argument.

Consequently `S_(q,C)` is a regular scattering function.  Since `S_(q,C)(0)=-1`, it belongs to the
fermionic regularity class for which modular nuclearity holds at every splitting distance.

## Claim C -- hypertranscendence

Equation `(3)` is a homogeneous first-order linear `q`-difference equation over `C(t)`.  The main
`q`-difference theorem of Adamczewski--Dreyfus--Hardouin says that a Puiseux--Laurent solution is
either ramified rational or hypertranscendental.

The germ `P_q` lies in `C[[t]]`.  If it were ramified rational, the intersection identity
`C((t)) intersect C(t^(1/j))=C(t)` (equivalently, invariance under the Galois roots of unity of a
ramified coordinate) would put it in `C(t)`.  But `(1)` has infinitely many distinct zeros and
poles, so it is not rational.  The theorem is stated for the Euler derivation `t d/dt`; over
`C(t)` differential algebraicity for that derivation is equivalent to differential algebraicity
for `d/dt`.  Therefore

```text
P_q is hypertranscendental over C(t).                        (8)
```

The exact physical scattering observable is thus HT in the crossing coordinate
`t=-i sinh(theta)/C`.  Promotion should state the base differential field explicitly; no
unproved claim about arbitrary nonlinear rapidity reparametrizations is needed.

### Real-axis reporter -- the phase slope is HT

For real rapidity put `x=sinh(theta)/C`.  The unitary boundary value has the continuous
unwrapped phase

```text
S_(q,C)(theta)=exp(i delta_(q,C)(theta)),
delta_(q,C)(theta)=pi+4 sum_(k>=0) arctan(q^k x).             (9)
```

The series and its derivative converge locally uniformly, and

```text
delta_(q,C)'(theta)=
  (4 cosh(theta)/C)
  sum_(k>=0) q^k/(1+q^(2k) sinh(theta)^2/C^2) > 0.          (10)
```

Thus the construction has a monotone real-axis scattering-phase reporter.  More importantly,
the already formalized abstract differential-algebra theorem

```text
HT(f'/f over K)  iff  HT(f over K)                          (11)
```

shows that the logarithmic scattering derivative is HT whenever `S` is.  Multiplying by the
nonzero algebraic Jacobian from `t` to rapidity, or from rapidity to equal-mass center-of-mass
energy away from threshold, preserves this conclusion after passing to the corresponding
algebraic kinematic base.  The Wigner--Smith phase-delay observable is therefore HT; the physical
claim is not confined to inaccessible complex zeros.

Lean proves `(10)` for every nonempty finite truncation, including strict positivity, in
`GeometricCDDConstraint.lean`.  The infinite locally-uniform passage is part of the paper analytic
interface.  Equation `(11)` is `hypertranscendentalOver_deriv_div_self_iff` in
`SourceLogarithmicBoundary.lean`.

## Claim D -- constructive local QFT

Lechner's inverse-scattering construction takes every regular factorizing scattering function to
a wedge-local model.  For the class with `S(0)=-1`, modular nuclearity holds for every positive
splitting distance.  The resulting Haag--Kastler net has observables in arbitrarily small double
cones and the Reeh--Schlieder property.  The model is asymptotically complete and its scattering
operator is the factorized operator built from the input `S`.

Since `(2)` is nonconstant, the scattering operator is not the free identity.  Combining the
parent construction with `(8)` gives a local, asymptotically complete, interacting QFT with an
exact HT scattering observable.

## Anti-theatre attacks

1. **Special-function relabeling.**  Writing `(1)` as a quotient of `q`-Pochhammer symbols proves
   nothing by itself.  The load-bearing facts are regular strip geometry, nontrivial scattering,
   the rational `q`-difference constraint, and the rational-or-HT theorem.
2. **Wedge-local only.**  A scattering function alone gives at most the first construction step.
   Regularity and the `S(0)=-1` nuclearity theorem are required for arbitrarily small local
   observables.
3. **Boundary accumulation.**  Geometric zeros tending to the real boundary would destroy the
   enlarged strip.  Here the zeros remain on `Im(theta)=pi/2` and escape in real rapidity; poles
   remain on `Im(theta)=-pi/2` and `3pi/2`.
4. **Interaction by naming.**  Interaction is certified by the reconstructed nonidentity
   scattering operator, not by non-Gaussianity or by the HT label.
5. **Coordinate inflation.**  The theorem claims HT in the canonical crossing coordinate only.
6. **Parent collision.**  Infinite CDD products, `q`-deformed Jost functions, and integrable
   `S`-matrices are old.  Novelty can lie only in the exact regular product plus its HT theorem and
   constructive local-QFT consequence.
7. **Limit-cycle inflation.**  Geometric resonance spacing is an old signature of cyclic RG.
   Exact rapidity-periodic elliptic `S`-matrices can be differentially algebraic, so discrete scale
   invariance alone does not imply HT.  The load-bearing structure here is the nontrivial rational
   decimation cocycle `(3)`, not the words “Russian doll”.

## Novelty gate

The focused search found:

- classical infinite Blaschke/CDD and `q`-deformed integrable scattering constructions;
- Freund--Zabrodin's hierarchy of `q`-deformed Jost and `S`-matrix functions;
- Lechner's constructive inverse-scattering theorem for regular factorizing `S`-matrices;
- Adamczewski--Dreyfus--Hardouin's rational-or-HT theorem.

It did not find the exact product `(1)` used as a regular Lechner scattering function, nor a
hypertranscendence theorem for a rigorously reconstructed local QFT scattering matrix.  This is
negative search evidence, not yet a novelty proof.  A wider formula-level audit of integrable
models and CDD classifications is mandatory before promotion.

## Significance gate

Independently of novelty, this is not a classification label.  It establishes the
physical existence of HT as an exact measurable scattering law in a mathematically constructed
interacting relativistic QFT, while retaining locality, arbitrarily small observables,
Reeh--Schlieder, inverse scattering, and asymptotic completeness.

## Exact open core

1. Obtain an independent analytic audit of the enlarged-strip proof and its boundary continuity.
2. Complete a formula-level novelty audit against infinite CDD, `q`-gamma, XXZ/XYZ, and
   factorizing-model literature.
3. Extend the now-formalized finite-product symmetries and geometric `q`-constraint to the
   nonrational zero/pole certificate and analytic-limit interfaces in `HTGeometry`.
4. Derive the one-shell rational CDD cocycle from a source-minimal QFT coarse-graining law rather
   than selecting it after the desired divisor is known.
5. Construct a cosmological model whose flat-space residue produces the HT amplitude dynamically,
   rather than prescribing it as an initial-state or transfer-function input.

## Primary literature

- G. Lechner, *Construction of Quantum Field Theories with Factorizing S-Matrices*,
  <https://arxiv.org/abs/math-ph/0601022>.
- B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and linear difference
  equations*, <https://arxiv.org/abs/1910.01874>.
- P. G. O. Freund and A. V. Zabrodin, *A Hierarchical Array of Integrable Models*,
  <https://arxiv.org/abs/hep-th/9208033>.
- A. LeClair and G. Sierra, *Renormalization group limit-cycles and field theories for elliptic
  S-matrices*, <https://arxiv.org/abs/hep-th/0403178>.

## Lean boundary

`formal/GaloisForLFunctions/HTGeometry/GeometricCDDConstraint.lean` now proves unconditionally:

- the finite geometric `q`-constraint;
- factor inversion under `t -> -t` away from the finite divisor;
- reversal of the crossing coordinate under rapidity negation and the `i pi` crossing shift;
- finite rapidity unitarity and crossing-period inversion.

The exact module build and axiom audit pass; only `propext`, `Classical.choice`, and `Quot.sound`
occur.  Infinite-product convergence, regular-strip bounds, the external difference-Galois
theorem, and constructive local-QFT reconstruction remain paper-level interfaces rather than
claims hidden in the finite algebraic module.
