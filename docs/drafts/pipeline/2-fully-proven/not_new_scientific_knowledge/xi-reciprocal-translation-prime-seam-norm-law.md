# The Xi prime seam is the norm-growth defect of one reciprocal Cauchy orbit

- **ID:** `xi-reciprocal-translation-prime-seam-norm-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / TOP-DOWN VALUE RELATION / NOT NEW SCIENTIFIC KNOWLEDGE
- **Formal parents:** `XiGlobalReflectionDefectEnergy.lean`,
  `XiPrimeSeamReflectionEnergy.lean`, `XiWeilLineConjHilbert.lean`,
  `XiCTaylorThetaTailSquareIndexPolarization.lean`,
  `CCMRectangularTwoEdge.lean`, `CCMSharpPrimeWindowDivisorTomography.lean`
- **Paper parents:** `prime-seam-damping-aperture-law.md`,
  `xi-global-meixner-shape-landau-rh.md`
- **Statement:** `[PROVED HERE]` The complete prime-seam coefficient at a prime `p` is exactly a
  positive scalar times the increase in the squared norm of the single centered reciprocal
  Cauchy vector after spectral translation by `log p`.  Functional-equation reflection makes this
  norm orbit even and increasing away from zero.  Contractivity at any one nonzero translation,
  or subexponential growth of the orbit, therefore implies RH.  The Weil quadratic value of the
  translated vector is independent of the translation and remains the explicit prime--Gamma
  central curvature.

## 1. The canonical translated reciprocal vector

For a multiplicity copy `q` of the Xi divisor put

```text
alpha_q=xiSpectralPoint(q),
y_q=Im(alpha_q),
r_q=|alpha_q|,
v_0(q)=1/alpha_q.                                         (1)
```

The formal corpus proves

```text
alpha_q != 0,
|y_q|<1/2,
sum_q r_q^(-2)<infinity.                                  (2)
```

For real `L`, define the diagonal spectral translation

```text
(U_L v)(q)=exp(-i L alpha_q)v(q),
v_L=U_L v_0.                                              (3)
```

Because

```text
|exp(-i L alpha_q)|=exp(L y_q)<=exp(|L|/2),               (4)
```

`U_L` is bounded and invertible on the Xi `ell^2` carrier, with inverse `U_(-L)`.  In particular,
every `v_L` is square-summable.  Its squared norm is

```text
N(L)=||v_L||^2
    =sum_q exp(2 L y_q)/r_q^2.                            (5)
```

The same formula defines an entire function of a complex variable `L`: on every compact set the
summands are bounded by a fixed multiple of the summable sequence `r_q^(-2)`.

## 2. Reflection, evenness, and exact norm growth

Let `J=xiWeilLineConjLp`.  The functional-equation reflection permutes multiplicity copies and
satisfies

```text
alpha_(Jq)=conj(alpha_q),
y_(Jq)=-y_q,
r_(Jq)=r_q.                                               (6)
```

Reindexing `(5)` by this involution gives

```text
N(-L)=N(L).                                               (7)
```

Averaging the two absolutely convergent expansions yields the pointwise-positive formula

```text
N(L)=sum_q cosh(2 L y_q)/r_q^2,

N(L)-N(0)
 =sum_q (cosh(2 L y_q)-1)/r_q^2 >=0.                      (8)
```

For `L!=0`, every summand in the second line vanishes exactly when `y_q=0`.  Consequently

```text
N(L)=N(0) for one L!=0
  iff N(L)<=N(0) for one L!=0
  iff every alpha_q is real
  iff RH.                                                 (9)
```

Thus a complete conservative divisor metric is much stronger than necessary for the orientation
conclusion.  It is enough to prove contractivity of one translated reciprocal Cauchy vector at
one nonzero time.

Termwise differentiation at zero also gives

```text
N'(0)=0,
N''(0)=4 sum_q y_q^2/r_q^2,
N''(0)=0 iff RH.                                         (10)
```

The first equality is the unconditional reflected-charge cancellation.  The second derivative,
not the first, is the faithful orientation coefficient.

## 3. The Weil value is frozen along the orbit

The Weil quadratic form is

```text
Q(v)=Re <Jv,v>.                                          (11)
```

At one coordinate,

```text
conj(v_L(Jq))*v_L(q)
 =conj(exp(-i L conj(alpha_q))/conj(alpha_q))
    *exp(-i L alpha_q)/alpha_q
 =1/alpha_q^2.                                           (12)
```

Therefore the translation phase cancels exactly in the reflected quadratic value:

```text
Q(v_L)
 =Re sum_q 1/alpha_q^2
 =primeArchCentralCurvature                              (13)
```

for every real `L`.  The elementary polarization identity for the involutive isometry `J` now
gives

```text
1/2 ||v_L-Jv_L||^2
 =N(L)-primeArchCentralCurvature.                         (14)
```

At `L=0`, `(14)` is precisely the already formalized global reciprocal reflection-defect law.
For arbitrary `L`, equations `(8)` and `(14)` split the defect into two nonnegative pieces:

```text
N(L)-primeArchCentralCurvature
 =[N(L)-N(0)]
   +xiGlobalReflectionDefectEnergy/2.                     (15)
```

The first bracket is the translation/orientation growth defect.  The second is the static
Hermitian-versus-holomorphic source gap.  This is a constraint--orientation decomposition: the
prime--Gamma constraint value stays fixed while the anti-holomorphic orientation norm grows.

## 4. Exact collision with the prime seam

Write an Xi divisor point as

```text
rho=sigma+i t,
d=sigma-1/2,
alpha=t-i d,
y=-d.                                                     (16)
```

For a rational prime `p`, let

```text
C_p(rho)=orbitwiseNatPrimeSeamCharge(p,rho)
        =log(p)(p^(-conj(rho))-p^(-(1-rho))).             (17)
```

Its norm is

```text
|C_p(rho)|^2
 =2 (log p)^2 p^(-1)
    (cosh(2(log p)d)-1).                                  (18)
```

Define, with exact Xi multiplicities retained,

```text
A_p=sum_rho mult_Xi(rho)|C_p(rho)|^2/|rho-1/2|^2.         (19)
```

Since `|rho-1/2|=|alpha|` and `cosh` is even, comparison of `(8)` and `(18)` proves the exact value
relation

```text
A_p
 =2 (log p)^2/p * (N(log p)-N(0)).                       (20)
```

In particular, for every single rational prime,

```text
A_p=0
 iff N(log p)=N(0)
 iff RH.                                                  (21)
```

This is not a similarity between two RH readers.  It identifies the complete divisor-weighted
Euler seam coefficient with the norm defect of one explicit Cauchy orbit.

For the Gamma--Meixner shape trace from the parent card, `(20)` yields

```text
G_Xi(z)
 =sum_p 2(log p)^2/p * w_z(p) * (N(log p)-N(0)),          (22)

w_z(p)=exp(-z log(cosh(2log p))/2).                       (23)
```

Thus the Landau coefficients are prime samples of one entire even norm curve.  The open source
continuation theorem can equivalently be sought as a source formula for this sampled reciprocal
Cauchy orbit.

## 5. Exponential type and a weaker sufficient input

Put

```text
a_Xi=sup_q |y_q| in [0,1/2].                              (24)
```

Equation `(5)` gives the upper bound

```text
N(L)<=exp(2L a_Xi)N(0),       L>=0.                       (25)
```

Conversely, for every `a<a_Xi`, choose a divisor copy with `|y_q|>a`; reflection supplies the
positive sign, and its single summand gives

```text
N(L)>=c_q exp(2La),        c_q>0.                         (26)
```

Hence

```text
lim_(L->infinity) log N(L)/L=2 a_Xi.                      (27)
```

It follows that any one of the source estimates

```text
N(L)=O(L^k) for some finite k,
log N(L)=o(L),
or sup_(L>=0)N(L)<infinity                               (28)
```

forces `a_Xi=0` and therefore RH.  These are strictly weaker than one-time norm equality and give
a cofinal-growth implementation of the same chain.

## 6. The orbit increment is the sharp prime-window residue

The required source-to-divisor value identification is already present in the sharp-window
tomography.  Put

```text
B_L(z)=rectangularWindowAmplitude(L,i*z)
      =sharpPrimeWindowMellin(L,1+i*z).                  (29)
```

At every centered divisor coordinate `alpha_q`, the removable-value convention at zero is
irrelevant because `alpha_q!=0`, and direct algebra gives

```text
B_L(alpha_q)=(1-exp(-i*L*alpha_q))/(i*alpha_q),
v_0(q)-v_L(q)=i*B_L(alpha_q).                            (30)
```

Let `b_L` be the `ell^2` evaluation vector of `B_L`.  It is square-summable because
`|Im(alpha_q)|<1/2` and

```text
|B_L(alpha_q)|<=(1+exp(|L|/2))/|alpha_q|.               (31)
```

Consequently the one-vector norm defect is the exact anchored sharp-window residue current

```text
N(L)-N(0)
 =||v_0-i*b_L||^2-||v_0||^2
 =||b_L||^2+2*Im <v_0,b_L>.                              (32)
```

Now write the underlying Xi point as `rho_q`.  Since

```text
1+i*alpha_q=rho_q+1/2,                                  (33)
```

the formal dyadic tomography theorem gives, at every right-half shifted pole and with analytic
multiplicity `m_q`,

```text
meromorphicTrailingCoeffAt(dyadicSharpPrimeContinuedSource,rho_q+1/2)
  =2*m_q*B_(log 2)(alpha_q).                             (34)
```

Thus the phase-orbit displacement is not merely analogous to a prime-source residue.  It is the
normalized residue value itself:

```text
v_(log 2)(q)
 =v_0(q)-i*meromorphicTrailingCoeffAt(...)/(2*m_q).      (35)
```

Functional-equation reflection supplies the left-half partner of every right-half pole.  A
critical-line copy contributes zero to the anchored current `(32)` pointwise, because its
`y_q` is zero.  Therefore the formal right-half residue formula `(34)`, reflection, and this
critical-line cancellation determine the complete norm *defect*, even though `(34)` alone is not
a construction of the full vector `b_L`.

Equations `(32)`--`(35)` discharge the algebraic source-to-divisor value identification in the
one-prime route.  What they do not supply is bounded quadratic transport of the reflected residue
family into the complete Xi `ell^2` norm.  The remaining positive theorem can therefore be stated
without an unspecified coordinate intertwiner:

```text
||b_(log 2)||^2+2*Im <v_0,b_(log 2)> <=0.               (36)
```

By `(8)` and `(32)`, the left side is already unconditionally nonnegative on the divisor side.
Hence `(36)` forces equality and RH.  Equivalently, `(36)` may be stated directly for the
right-pole residues after adjoining their functional-equation reflections; the critical-line
terms then disappear from the anchored current.  This is a fixed sharp-window residue
contraction, not the active anisotropic rectangular-mesh/subpower problem.

## 7. Top-down source target

The shortest new chains are

```text
source contractivity on the single vector v_0 at L=log 2
  -> N(log 2)<=N(0)
  -> A_2=0
  -> RH,                                                  (37)
```

or

```text
source subexponential bound for the orbit U_L v_0
  -> a_Xi=0
  -> RH.                                                  (38)
```

Here `v_0` is the centered Cauchy evaluation at the fixed point zero, and `U_L` is the ordinary
Mellin spectral-translation phase already present in the formal corpus.  A source proof of `(36)`
does not need a conservative metric on every theta eigenfunction, completeness, simplicity of Xi
zeros, or positivity on a full Cauchy packet span.  It needs a norm comparison for one canonical
source vector and one canonical prime translation.

The missing theorem is not supplied here:

```text
prove the anchored dyadic sharp-window residue inequality `(36)`, equivalently
realize its normalized residue map as a contraction into the Xi divisor norm. (39)
```

The dyadic residue formula proves the coordinate values in `(35)`, so an additional algebraic
source-to-divisor intertwiner is no longer missing.  Merely observing that Mellin translation is
unitary before the Xi divisor evaluation still does not prove `(39)`: the missing statement is
boundedness of the normalized residue map for the anchored quadratic combination `(36)`.

## 8. Literature boundary

Multiplication by `exp(-iLz)` as the spectral form of logarithmic translation is standard
Mellin--Plancherel theory.  Hedenmalm's 2026 Xi eigenvalue construction places the missing
self-adjoint metric problem on a theta-defined differential pair; the present theorem only
reduces the RH part of such a metric theorem to one reciprocal Cauchy orbit.  The prime-seam
identity `(20)` is an elementary combination of the formal reflection laws and does not claim
independent scientific novelty.

## Gates

- [x] define the translated reciprocal Xi vector and prove square summability on paper
- [x] prove evenness, convexity, and the exact norm-growth formula
- [x] prove the frozen Weil/source value along the whole orbit
- [x] identify the prime seam coefficient with the sampled norm defect
- [x] identify the orbit increment with the normalized dyadic sharp-window source residue
- [x] replace the unspecified value intertwiner by one anchored residue-contraction inequality
- [x] identify the exact exponential type with maximal horizontal displacement
- [x] reduce RH to one-vector one-prime contractivity or subexponential orbit growth
- [ ] formalize `(3)`--`(35)` in Lean using targeted checks only
- [ ] prove the anchored source residue inequality `(36)`
- [ ] RH

No numerical experiment, Lean build, lint run, or scratch computation was used in this proof.
