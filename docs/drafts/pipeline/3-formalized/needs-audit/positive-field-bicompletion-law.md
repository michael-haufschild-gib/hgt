# Positive-field bicompletion law

- **ID:** `positive-field-bicompletion-law`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** One positive Bernstein field on any nonempty open scale window determines its
  complete pointed moment source and, across every admissible atomic presentation, the entire
  exterior confocal upper field and its maximal canonical hull.  More generally the full
  Bernstein--confocal observation has an exact bicompletion quotient: positive divided-power root
  times maximal confocal hull.

## Exact theorem

For a real moment sequence `m`, degree `N`, and a Lorentz source `S`, write

```text
P_(N,m)(X) = sum_(k=0)^N (T_m b_(N,k))(X)^2,
F_(N,m)(T) = sum_(r=0)^N binom(N,r)m_r T^r/r!,
G_S(R) = sup_(q in S) [a(q)+sqrt(R^2-2R x(q)+a(q)^2)].
```

On a radius domain `D`, let `H_D(G)` be the intersection of the Lorentz cone with all branch
sublevel sets encoded by `G`.  If `m_0,m'_0>0` and `G,H` are realized confocal upper fields, then

```text
(P_(N,m)=P_(N,m') and G=H on D)
iff
((m_0,...,m_N)=(m'_0,...,m'_N) and H_D(G)=H_D(H)).       (BC)
```

The decisive connected form uses only the original positive Bernstein observation.  Let two
bounded, cofinally transverse-neutral atomic presentations satisfy the orientation hypotheses of
the Abel-selection theorem, with moment sequences `m,m'` and source-radius bounds `M,M'`.  For any
nonempty open interval `J`,

```text
P_(N,m)|J = P_(N,m')|J for every N
  iff
  [m=m' and
   H_(max(M,M'),infinity)(G_S)=H_(max(M,M'),infinity)(G_T)].     (LG)
```

In the forward direction one also obtains
`G_S=G_T` on `(max(M,M'),infinity)`.  Both upper fields are realized by the Lorentz lifts of their
intrinsic aggregate sources.  Consequently the common hull is not auxiliary packaging: it is the
largest geometric source compatible with the one locally observed positive field.

The two completions are canonical and maximal:

1. The signed divided-power transform satisfies exactly

   ```text
   D(P_(N,m))=F_(N,m)^2.
   ```

   The condition `m_0>0` selects the unique root and hence the complete moment prefix.
2. `H_D(G)` is the largest Lorentz source whose upper field is bounded by `G`; it is closed and
   convex, realizes `G`, and depends only on `G|D`.
3. The source inverse is uniformly stable in the exact weighted tail norm

   ```text
   ||m||_(N,tau),tail =
     sum_(r=1)^N binom(N,r)|m_r| tau^r/r!.
   ```

   If both tail norms are at most `theta mu`, `m_0,m'_0>=mu>0`, `theta<1`, and `|T|<=tau`, then

   ```text
   |F_(N,m)(T)-F_(N,m')(T)|
   <= |F_(N,m)(T)^2-F_(N,m')(T)^2|/[2(1-theta)mu],       (ST)
   ```

   with a constant independent of `N`.
4. The boundaries are exact.  At `m_0=0`, the inverse contains the non-Lipschitz map
   `y_0 -> sqrt(y_0)`.  On the geometric side, adjoining any point of `H_D(G)` preserves the
   complete field; therefore a source point is forced precisely when it is the singleton active
   face of the hull.

## Complete proof

The coefficient computation in `bernstein-divided-power-cofinal-stability` gives

```text
[X^r]P_(N,m)=(-1)^r r! [T^r]F_(N,m)^2.                 (1)
```

Hence equality of purity polynomials is equality of the squares of the divided-power roots.  In
the real polynomial domain, `(F-F')(F+F')=0`.  Since the constant coefficient of `F+F'` is
`m_0+m'_0>0`, the second factor is nonzero and `F=F'`.  Its `r`th coefficient is
`binom(N,r)m_r/r!`, which is nonzero-scaled for `r<=N`, so the pointed prefixes agree.  Conversely,
prefix equality makes the roots equal, and (1) makes the purity polynomials equal.  This proves
the analytic equivalence in (BC).

For a Lorentz point `q=(x,a)`, the exact equivalence

```text
g_R(q)<=L iff a<=L and R x-L a >= (R^2-L^2)/2          (2)
```

identifies every branch sublevel with closed affine half-spaces.  Their intersection is therefore
the closed convex hull `H_D(G)`.  Every realization of `G` is contained in it, and every hull point
has branch value at most `G`; the hull consequently realizes `G` and is maximal.  Thus equality of
realized fields on `D` is equivalent to equality of their hulls.  Conjoining this equivalence with
the analytic equivalence proves (BC).

For (LG), interval equality of all purity polynomials gives `m=m'` by the positive divided-power
root (equivalently, by polynomial interval rigidity followed by the pointed chart).  Apply the
admissible-presentation rigidity theorem at every radius larger than both source bounds.  This
gives equality of the confocal amplitude envelopes pointwise on the entire exterior interval;
multiplication by the radius gives equality of `G_S` and `G_T`.  The identity

```text
g_R(Lambda z)=R (|z/R|+|1-z/R|)
```

and the exact supremum formula show that each `G` is the realized upper field of the Lorentz-lifted
aggregate source.  Field equality now gives hull equality by (2).  This proves (LG) from a single
local observation rather than by independently assuming the geometric field.

For (ST), the weighted tail norm bounds `|F(T)-m_0|` term by term whenever `|T|<=tau`.  Both roots
are therefore at least `(1-theta)mu`, so

```text
|F^2-F'^2|=|F-F'||F+F'| >= 2(1-theta)mu |F-F'|.
```

This proves the uniform bound.  The radical boundary follows from `[X^0]P=m_0^2`.  Finally, (2)
shows that adding any hull point cannot change the upper field.  Equality at an active supporting
line forces a raw active point only when the corresponding face is a singleton.  These are exact
counterpresentations at every stronger proposed identifiability boundary.

## Scientific interpretation

The law is not a generic assertion that observations have quotients.  It identifies the two
quotients explicitly and proves their maximality:

```text
positive scale field
   = pointed divided-power root  x  maximal confocal hull.
```

The first coordinate retains signed source information because positivity fixes the square-root
orientation.  The second retains exactly the branch geometry that survives arbitrary changes of
presentation.  No additional raw-source information is present in the field.

## Novelty audit

- `[LITERATURE]` Exponential generating functions, positive square-root selection, support
  functions, and exposed faces are classical parent mechanisms.
- `[BRIDGE]` Each completion separately specializes a classical mechanism.
- `[NOVELTY UNVERIFIED]` The exact Bernstein divided-power square, the self-consistent confocal
  hull with normal `(R,-G(R))`, and especially the single-observable local-to-global law (LG) were
  not found together in the targeted comparison.  Specialist priority review is still required
  before a novelty claim.
- The theorem is a structural law, not an RH estimate.  Its value is an exact carrier and exact
  identifiability boundary.

## Gates

- [x] paper statement is one equivalence, not a collection of unrelated results
- [x] complete proof and sharp counterboundaries are recorded
- [x] exact formal master theorem and axiom audit
- [ ] specialist novelty audit
- [ ] integrated publication rewrite

## Formalization inventory

- `RHTower.ScaleCovariantBernsteinDividedPowerStability`
  - exact divided-power square factorization
  - exact source quotient equivalence
  - degree-adapted uniform chamber stability
- `HTGeometry.ConfocalEnvelopeHull`
  - Lorentz half-space law
  - closed convex maximal hull and exact quotient
  - physical amplitude field realizes the lifted confocal envelope
- `RHTower.PositiveFieldBicompletionLaw`
  - `positiveField_bicompletion_law`
  - `localPositiveScaleField_selects_maximalConfocalHull`
  - `localPositiveScaleField_agrees_iff_source_and_maximalHull_eq`

The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-07-19 -- extracted from the two formerly open questions of the Abel-selection paper.
- 2026-07-19 -- strengthened from a product equivalence to the single-observable exterior-hull
  selection law (LG); exact source files compile and use only ordinary logical axioms.
