# Von Mangoldt successor--Bianchi Hankel-curvature weld

- **ID:** `von-mangoldt-successor-bianchi-hankel-curvature-weld`
- **Stage:** 3-formalized / external novelty audit pending
- **Type:** `[UNIVERSAL RIGIDITY]`, `[SOURCE-SPECIFIC FAILED CLASS]`,
  `[SOURCE-SPECIFIC POSITIVE WELD]`
- **Scientific status:** `[PROVED] [LEAN-VERIFIED DIRECTLY] [NOT RH]`
- **Frontier changed:** finite operator-placement part of `SR-39` is solved; cofinal singular
  completion is now `SR-40`.
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/ConservativeHankelRigidity.lean`;
  - `formal/GaloisForLFunctions/RHTower/VonMangoldtAdditiveLogJetHankelCurvature.lean`;
  - `formal/GaloisForLFunctions/RHTower/VonMangoldtSuccessorBianchiHankelWeld.lean`.

## 1. Frontier and containing problem

Corpus had two positive source legs:

1. the successor Dirichlet carrier, which makes every positive logarithmic jet square summable;
2. the pointed Gamma--Bianchi raw-moment Gram, which reconstructs every positive-depth Euler jet.

Corpus also warned that their direct sum discards the mixed terms, but did not prove what those
terms must be or whether they can restore Hankel compatibility.  This is a special case of the
general problem:

> When can a conservative carré-du-champ, which kills the unit, be welded to a pointed boundary
> so that the coupled form is a unital moment-Hankel form?

## 2. Universal conservative--Hankel rigidity

For a kernel `K : N x N -> A`, write

```text
K(r+1,s)=K(r,s+1).                                      (1)
```

Repeated transport of degree gives

```text
K(r,s)=K(0,r+s).                                        (2)
```

Therefore `(1)` plus `K(0,s)=0` for every `s` forces `K=0`.  In Hilbert form: if `v_0=0` and
`<v_(r+1),v_s>=<v_r,v_(s+1)>` for every `r,s`, then every `v_r=0`.

For one monomial edge `b -> a`, the exact shift curvature is

```text
(a^(r+1)-b^(r+1))(a^s-b^s)
 -(a^r-b^r)(a^(s+1)-b^(s+1))
 =(a-b)(a^s*b^r-a^r*b^s).                              (3)
```

At adjacent orders `r=s+1`,

```text
curvature_s(a,b)=-(a-b)^2*(a*b)^s<0                    (4)
```

for positive distinct nodes.  This universal layer is elementary `FORMAL-CLOSURE`, not the
scientific novelty claim.

## 3. Actual all-order von Mangoldt anti-Hankel law

Put

```text
x_n=log n,
c_n=Lambda(n)/n,
v_r(n)=sqrt(c_n)*(x_(n+1)^r-x_n^r),
K(r,s)=sum_n v_r(n)v_s(n),
C_s(n)=c_n*(x_(n+1)-x_n)^2*(x_(n+1)*x_n)^s.            (5)
```

Lean proves for every `s>=0`:

```text
C_s(n)>=0,
C_s(2)>0,
sum_n C_s(n)<infinity,
K(s+2,s)-K(s+1,s+1)=-sum_n C_s(n)<0.                   (6)
```

Thus failure of Hankel balance is an all-order strictly signed source law, not only the previously
known zero-row mismatch.  Every additive boundary `B` which is itself Hankel has zero shift
curvature, so `K+B` remains non-Hankel.  In particular, no direct addition of an ordinary raw
moment boundary can produce any moment-Hankel target.

## 4. Exact finite pointed weld

The no-go identifies the missing datum: mixed terms on a common source carrier.  For a finite
aperture `n=2,...,M+1` and positive jet depth `r`, define

```text
d_r(n)=sqrt(c_n)*(x_(n+1)^r-x_n^r),
b_r(n)=sqrt(c_n)*x_n^r,
h_r(n)=sqrt(c_n)*x_(n+1)^r.                             (7)
```

Here `b_r` is exactly the `x=0` pointed Gamma--Bianchi raw feature already formalized in corpus.
Coordinatewise,

```text
d_r+b_r=h_r.                                            (8)
```

Let `G^d`, `G^b`, and `X` be the successor Gram, pointed Bianchi Gram, and forced symmetrized mixed
block.  Lean proves the exact decomposition

```text
Gram(d+b)=G^d+G^b+X,                                    (9)
```

and, simultaneously for every finite aperture `M` and jet size `N`,

```text
Gram(d+b)_(i,j)
 =sum_(n=2)^(M+1) c_n*(log(n+1))^(i+j+2).              (10)
```

Hence the coupled Gram is exactly a positive shifted moment-Hankel matrix.  At the first
nonconstant curvature gate,

```text
X(2,0)-X(1,1)=-(G^d(2,0)-G^d(1,1))>0                  (11)
```

for every nonempty aperture.  The mixed block is neither optional nor fitted from the target: it
is forced by the common von Mangoldt coordinate and cancels the successor defect exactly.

## 5. What changed and what remains open

This closes a real `SR-39` subproblem:

```text
finite successor incidence
 + actual pointed Gamma--Bianchi boundary
 + source-forced mixed block
 -> exact positive Hankel Gram                              PROVED. (12)
```

It also kills the whole additive-Hankel-boundary class.  The finite Green-boundary placement is no
longer conjectural.

It does **not** prove RH. Raw boundary norms in `(7)` do not have required ordinary cofinal Hilbert
limit; corpus already rules out that diagonal positive-log completion. Subsequent `SR-40` work now
solves signed matrix-current part of this frontier:

> Pointed-tail principal subtraction preserves mixed block exactly, converges in every finite jet
> matrix space, and remains Hankel at all orders.

See `von-mangoldt-successor-principal-relative-hankel-current.md`. New `SR-41` frontier is one
inclusion-compatible bivariate prime--jet source object realizing both this jet current and coherent
odd Gamma--Jacobi prime marginal, with completed Euler trace. A separate direct sum is ill-typed
and does not count.

## 6. Scientific method and novelty audit

- **Observation:** successor Gram is positive and summable but not Hankel; pointed Bianchi Gram is
  positive and Hankel but direct addition cannot change curvature.
- **Conjecture:** common-coordinate cross terms restore exact Hankel balance.
- **Falsifiers:** any nonzero conservative Hankel Gram; any order with nonnegative successor
  curvature; failure of `(8)` for actual raw Bianchi feature; failure of `(10)`; zero/nonpositive
  mixed curvature on a nonempty aperture.
- **Outcome:** all falsifiers failed in Lean; `(6)` and `(8)--(11)` hold unconditionally.
- **Negative control:** orthogonal direct sum has `X=0` and remains strictly anti-Hankel.
- **Positive control:** head endpoint evaluation is visibly a moment Gram and is recovered exactly.

Three-tree and pipeline searches found no prior conservative-Hankel rigidity record, no all-order
von Mangoldt successor curvature law, and no successor--Bianchi endpoint weld.  Generic Dirichlet
forms, Hankel matrices on Dirichlet spaces, Gram positivity, and endpoint telescoping are standard
and are not novelty claims.  Suzuki's 2026 screw-function paper proposes nonlocal finite-interval
operator limits but its public abstract does not state this source weld.  External novelty is
therefore **provisional**, not certified by search.

## 7. Lean theorem surface

Universal:

- `hankelShiftBalanced_eq_zero_of_zeroRow`;
- `gramHankelBalanced_iff_all_zero`;
- `monomialEdge_hankelCurvature_eq`;
- `monomialEdge_adjacent_hankelCurvature_neg`.

Actual infinite source:

- `vonMangoldtAdditiveLogJetFeature_adjacentHankelCurvature_eq`;
- `summable_vonMangoldtAdditiveLogJetAdjacentHankelCost`;
- `vonMangoldtAdditiveLogJetKernel_adjacentHankelCurvature_eq`;
- `vonMangoldtAdditiveLogJetKernel_adjacentHankelCurvature_neg`;
- `vonMangoldtAdditivePositiveLogJetGram_add_hankelCorrection_ne_hankelTarget`;
- `vonMangoldtAdditivePositiveLogJetGram_add_pointedBianchiBoundary_ne_momentHankel`.

Finite positive weld:

- `finiteVonMangoldtSuccessor_add_pointedBianchi_eq_headFeature`;
- `finiteVonMangoldtSuccessorPointedWeldGram_decomposition`;
- `finiteVonMangoldtSuccessorPointedWeldGram_eq_momentHankelMatrix`;
- `finiteVonMangoldtSuccessorPositiveFiniteGram_firstCurvature_neg`;
- `finiteVonMangoldtSuccessorPointedBianchiCross_firstCurvature_eq`;
- `finiteVonMangoldtSuccessorPointedBianchiCross_firstCurvature_pos`;
- `finiteVonMangoldtSuccessorPointedWeldGram_posSemidef`.

## Gates

- [x] universal conservative-Hankel rigidity
- [x] exact local edge curvature
- [x] actual all-order strict von Mangoldt curvature
- [x] additive Hankel-boundary class no-go
- [x] actual pointed Bianchi common-coordinate placement
- [x] exact finite all-order Hankel weld
- [x] forced mixed-curvature cancellation and strictness
- [x] direct Lean checks
- [ ] final targeted build, lint, and axiom audit
- [ ] external expert novelty review
- [ ] `SR-40` cofinal singular completion
- [ ] completed Euler trace identity
- [ ] RH
