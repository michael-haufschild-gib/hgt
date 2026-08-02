# Route J: literal reflected source profiles have a sharp four-atom threshold

**Status:** `[LEAN-PROVED]`; dependency-closed paper proof and unconditional Lean 4 formalization.

## Frontier

`[LOCAL-RESEARCH]` The two-active-atom theorem proves that equality of reflected projective
leading directions forces the centered line. The three-atom construction proves that projective
coherence alone is insufficient: its two leading directions differ by the scalar `r^3`.

That scalar is harmless in projective space but is not harmless for one literal source law. A
single finite signed source multiplier has one coefficient vector. It cannot rescale its
coefficients when evaluated at the reflected fibre. This leaves the following sharper question.

> What is the least number of full-turn atoms for which one common real coefficient vector can
> lie in both reflected value kernels and carry the same nonzero derivative charge at both
> fibres?

The answer is four. Moreover four atoms support exact, not merely leading-order, unit
source-connection charge at both reflected fibres with one common coefficient vector.

## Polynomial encoding

Fix `T != 0`, `r > 0`, and `r != 1`, and put `q=r^(-1)`. For real weights
`a=(a_1,...,a_N)`, define

```text
Phi_a(X) = sum_{j=1}^N a_j(1-X^j).                     (1)
```

Then `Phi_a(1)=0` and `deg Phi_a <= N`. At the reflected full-turn points

```text
z_+ = 2*pi/T + i y,       z_- = 2*pi/T - i y,
r = exp(-T y),
```

the value rows are

```text
G_+(a)=Phi_a(r),       G_-(a)=Phi_a(q).                (2)
```

The spectral derivatives are purely imaginary:

```text
H_+(a)=i T r Phi_a'(r),
H_-(a)=i T q Phi_a'(q).                                (3)
```

Thus a common leading coefficient vector carrying equal real charge `m` satisfies

```text
Phi_a(r)=Phi_a(q)=0,
T r Phi_a'(r)=T q Phi_a'(q)=m.                         (4)
```

This encoding is an equivalence, not a relaxation. Conversely, every real polynomial `Phi` of
degree at most `N` with `Phi(1)=0` has a unique representation `(1)`: if

```text
Phi(X)=c_0+c_1 X+...+c_N X^N,
```

take `a_j=-c_j`; the relation `Phi(1)=0` gives
`c_0=sum_j a_j`.

## Theorem A: three or fewer literal atoms carry no off-center common charge

**Theorem.** Suppose `N <= 3` and a real polynomial `Phi` of degree at most `N` satisfies `(4)`
with `r>0`, `r!=1`, and `T!=0`. Then `m=0`.

**Proof.**

The three numbers `1,r,q` are distinct. If `N<=2`, the three roots force `Phi=0`, hence `m=0`.

It remains to treat `N=3`. The three roots and the degree bound give

```text
Phi(X)=C(X-1)(X-r)(X-q)                                (5)
```

for some real `C`. Differentiating `(5)` at the two reciprocal roots gives

```text
r Phi'(r)
  = C r(r-1)(r-q),
q Phi'(q)
  = C q(q-1)(q-r)
  = C (r-1)(r-q)/r^2.                                 (6)
```

Their equality implies

```text
C(r-1)(r-q)(r-r^(-2))=0.                              (7)
```

Every factor except `C` is nonzero: `r!=1`, positivity gives `q>0`,
`r!=q` because `r^2!=1`, and `r-r^(-2)=(r^3-1)/r^2!=0`. Therefore `C=0`,
so `Phi=0` and `m=0`. ∎

This strictly strengthens the previous three-atom projective result. The vector there is common
only after multiplying the reflected representative by `r^3`; one literal source profile cannot
perform that fibre-dependent rescaling.

## Theorem B: four literal atoms carry equal nonzero reflected charge

Define

```text
s(r) = (1-r^5)/(r(1-r^3))
     = (1+r+r^2+r^3+r^4)/(r(1+r+r^2))                 (8)
```

and

```text
P_r(X)=(X-1)(X-r)(X-q)(X-s(r)).                        (9)
```

The denominators in `(8)` are nonzero. The second expression shows `s(r)>0`. Direct subtraction
gives

```text
s(r)-r = (1+r)/(r(1+r+r^2)),
s(r)-q = r^2(1+r)/(1+r+r^2),
s(r)-1 = (1+r^4)/(r(1+r+r^2)).                        (10)
```

Hence all four roots in `(9)` are distinct.

The value conditions are immediate:

```text
P_r(1)=P_r(r)=P_r(q)=0.                               (11)
```

At the reciprocal roots,

```text
P_r'(r)=(r-1)(r-q)(r-s),
P_r'(q)=(q-1)(q-r)(q-s).                              (12)
```

After cancelling the nonzero common factors, the equality

```text
r P_r'(r)=q P_r'(q)                                   (13)
```

is equivalent to

```text
r^3(r-s)=q-s,
```

which is exactly the first formula in `(8)`. The common charge is nonzero because all roots are
simple. More explicitly,

```text
M(T,r)=T r P_r'(r)
      =-T (r-1)^2(r+1)^2/[r(1+r+r^2)] != 0.           (14)
```

By the converse part of the polynomial encoding, there is a unique real four-vector
`B(r)=(b_1,...,b_4)` such that `Phi_B=P_r`. Normalize it by

```text
b=B(r)/M(T,r).                                         (15)
```

Equations `(11)`--`(15)` give

```text
Phi_b(r)=Phi_b(q)=0,
T r Phi_b'(r)=T q Phi_b'(q)=1.                         (16)
```

Thus four atoms admit one literal, not merely projective, reflected leading source profile with
equal nonzero charge.

## Theorem C: one common four-atom law gives exact reflected unit-charge jets

Let `eta_+,eta_-` be arbitrary real bounded derivative corrections. There is a real polynomial
`Q` of degree at most four satisfying

```text
Q(1)=0,
Q(r)=Q(q)=1,
T r Q'(r)=eta_+,
T q Q'(q)=eta_-.                                      (17)
```

Here is a dependency-closed existence proof. Let `V` be the five-dimensional real vector space
of polynomials of degree at most four and define

```text
E : V -> R^5,
E(Q)=(Q(1), Q(r), Q'(r), Q(q), Q'(q)).                (18)
```

If `E(Q)=0`, then `1` is a root and `r,q` are double roots. Therefore

```text
(X-1)(X-r)^2(X-q)^2 divides Q.                         (19)
```

The divisor in `(19)` has degree five, while `deg Q<=4`; hence `Q=0`. Thus `E` is injective.
Its domain and codomain both have dimension five, so it is bijective. Apply its inverse to

```text
(0,1,eta_+/(Tr),1,eta_-/(Tq))
```

to obtain `(17)`. This is precisely finite Hermite interpolation at the distinct nodes
`1,r,q` with multiplicities `1,2,2`; no analytic or arithmetic hypothesis is hidden in it.

Encode `Q` by the unique real four-vector `v` from `(1)`. For every `delta>0`, put

```text
a(delta)=b/delta+v.                                   (20)
```

Using `(16)` and `(17)`,

```text
Phi_a(r)=Phi_a(q)=1,
T r Phi_a'(r)=1/delta+eta_+,
T q Phi_a'(q)=1/delta+eta_-.                          (21)
```

Consequently one and the same coefficient vector `a(delta)` gives

```text
G_+(z_+)=G_-(z_-)=1,
H_+(z_+)=i(1/delta+eta_+),
H_-(z_-)=i(1/delta+eta_-).                            (22)
```

For the source connection

```text
F=iG/z,       D=(iH-F)/z,
```

one has `D/F=H/G-1/z`. Choose

```text
eta_+=Im(1/z_+),       eta_-=Im(1/z_-).                (23)
```

Then `(22)` gives the exact identities

```text
delta Im(D_+/F_+)=delta Im(D_-/F_-)=1                 (24)
```

for every `delta>0`, while

```text
delta a(delta) -> b.                                  (25)
```

No fibre-dependent scalar, coefficient vector, or bounded correction is used.

## Sharp classification

Combining Theorems A--C:

```text
at most three full-turn atoms
  + one literal reflected coefficient profile
  + equal nonzero charge
  => impossible off center;

four full-turn atoms
  => one common exact reflected unit-charge law exists. (26)
```

Thus the literal-source threshold is exactly four. Projective reflection has threshold three;
literal equal-charge reflection has threshold four.

## Hostile novelty and theatre audit

`[LITERATURE]` Polynomial Hermite interpolation and confluent Vandermonde invertibility are
classical. Bossoney--Troyanov give a modern direct account of arbitrary-multiplicity Hermite
interpolation, including uniqueness and explicit basis polynomials:
<https://arxiv.org/abs/2607.17998>. Higham studies confluent Vandermonde-like systems and their
invertibility/stability:
<https://doi.org/10.1137/0611002>. Reciprocal and self-inversive root symmetry is also a mature
subject; for a representative source see Suzuki:
<https://arxiv.org/abs/1211.2953>.

`[BRIDGE]` The interpolation theorem, root-counting argument, and reciprocal polynomial language
are not new scientific knowledge.

`[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` The source-specific weld is the exact arity jump `(26)`:

1. exponential source weights become a polynomial automatically rooted at one;
2. the two reflected fibres impose reciprocal roots;
3. equality of anisotropic derivative charge imposes the nonstandard weighted derivative law
   `(13)`;
4. the fourth root `(8)` is the unique degree-four freedom that solves that law;
5. one Hermite correction then produces exact source-connection charge at both fibres with the
   same weights.

The exact conjunction was not found in the internal corpus or the audited parent literature.
Priority remains provisional pending independent expert review.

This is not an RH proof. Parameters `T,y` still select one reflected full-turn pair, and no theorem
shows that a divisor-independent canonical theta/prime--Gamma law realizes the required parameters
simultaneously at every Xi zero or satisfies the global Julia budget. Conversely this is not a
target-fitted multiplicity witness: `T,y,delta` are arbitrary, the same profile acts at both
fibres, and unit charge follows from source normalization rather than an inserted Xi order.

## Route consequence

The three-atom projective survivor is now completely classified: it is killed by literal
same-profile normalization. Its strongest positive survivor is the sharp four-atom law above.
Therefore Route J remains open, with a narrower scalar core:

> exclude the four-atom polynomial `P_r` from every canonical source-defined theta/prime--Gamma
> family, or lift it source-faithfully across the Xi mesh and prove the global Julia capacity.

## Lean certificate

```text
formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedFourAtomLiteralReflectionEscape.lean
```

Principal declarations:

```text
exists_real_polynomial_iterateDerivative_eval_eq_degree_lt_modulus
signedThreeAtom_literalReflection_equalCharge_zero
signedFourAtomLiteralRay_value_plus
signedFourAtomLiteralRay_value_minus
signedFourAtomLiteralRay_derivative_plus
signedFourAtomLiteralRay_derivative_minus
signedFourAtomLiteralRayCharge_ne_zero
exists_signedFourAtomLiteralCorrection
exists_signedFourAtomLiteralExactCoefficientPair
tendsto_signedFourAtomLiteralNormalizedWeights
exists_signedFourAtomFullTurn_literalReflectionExactPair
```

Verification:

```text
lake env lean \
  GaloisForLFunctions/RHTower/XiCTaylorSignedFourAtomLiteralReflectionEscape.lean

lake build \
  GaloisForLFunctions.RHTower.XiCTaylorSignedFourAtomLiteralReflectionEscape
```

The direct leaf check emits no warnings. The exact-module build succeeds. `#print axioms` for all
principal theorems reports only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`,
`admit`, new `axiom`, `opaque`, or `unsafe` declaration occurs.
