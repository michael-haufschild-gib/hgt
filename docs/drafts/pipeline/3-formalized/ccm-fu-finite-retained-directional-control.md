# CCM-FU: finite retained-source directional control

- **Stage:** 3-formalized
- **Type:** [BRIDGE] / derived theorem
- **Parent:** [finite source control and cofinal coverage](../1-in-progress/ccm-fu-finite-source-cone-exhaustion.md)
- **Result:** Every finite retained prime field has finitely many actual source cutoffs with a uniform positive directional margin, stable under independent sufficiently small adjacent-cutoff clipping.

## Scope

Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints
→ signed curvature → prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green
→ RH. This closes the fixed-field source-control target using the literal
arithmetic source. Complete compatible cofinal prime coverage under a uniform
energy budget remains open. The cutoff family and margin depend on the retained
field; no uniform dependence on the field is asserted.

## Exact source statements

Let S be any finite set of primes. Index the retained field by all subsets R
of S, including the empty subset. For the actual Möbius dilation channels,
define

`V_S(M)(R)=sum_(1<=d<=M, primeFactors(d) intersect S=R) C_d(M)`.

For real coordinates y(R), its pairing is exactly

`<y,V_S(M)>=sum_(1<=d<=M) y(primeFactors(d) intersect S)*C_d(M)`.

All cutoffs are integers and all source channels, including their clipped
endpoints, are retained. Lean proves:

1. If `<y,V_S(M)> >= 0` for every M, then every coordinate y(R) is zero.
2. Every nonzero y has actual cutoffs with strictly positive and strictly
   negative pairings.
3. There exist a nonempty finite cutoff family K and c>0 such that for every
   y, some M in K satisfies `<y,V_S(M)> >= c*norm(y)`.
4. There also exist such K, c>0 and `0<delta<=1` for which every independent
   choice `0<=clip(M)<=delta`, M in K, satisfies: for every y, some M in K has

   `<y,(1-clip(M))*V_S(M)+clip(M)*V_S(M+1)> >= c*norm(y)`.

The coordinate norm is the finite function-space supremum norm. These are
closed source witness theorems; no one-sided source condition or RH premise
is assumed in their existential conclusions. The one-sided condition occurs
inside the proof by contradiction and is shown to force y=0.

## Positive integral carrier

Use the [exact source primitive and Mellin transport](ccm-fu-retained-source-mellin-transport.md).
For real y, H_y is real everywhere, vanishes below one, and equals the source
pairing at every integer cutoff. Between adjacent cutoffs it is affine in
sqrt(x). A hypothesized one-sided functional therefore makes H_y nonnegative
on the whole real ray.

Define the positive measure on x>0 by density

`norm(x^(-5)*H_y(x))`,

and set X(x)=log(x). The measure is finite by the source Mellin theorem at
four. Its density vanishes below one, so X>=0 almost everywhere. Exact
exponential tilting translates the Mellin exponent; all real exponential
moments with t<2 are initially integrable. In particular zero lies in the
interior of the exponential-integrability interval.

Under the hypothesized one-sided functional, reality and positivity remove
the norm from the density. The complex MGF is exactly

`complexMGF(X,measure,z)=mellin(H_y,z-4)`.

On Re(z)<2 it agrees with the existing pole-filled source expression
`M_y(4-z)`. This proves the actual MGF germ, with every Euler and integration
factor retained.

## Landau continuation and pole contradiction

The [finite-source spectral theorem](ccm-fu-finite-retained-spectral-separation.md)
gives differentiability of `z -> M_y(4-z)` on every closed ball of radius
R<7/2. Apply the corpus's continuous Landau Taylor–Tonelli theorem with
R=13/4. Every real exponential moment with t<R exists; negative t already
belong to the initial range. Hence the MGF is analytic on Re(z)<13/4 and

`A_y(s)=complexMGF(X,measure,4-s)`

is analytic on Re(s)>3/4, agreeing with M_y near four.

M_y is meromorphic everywhere. The discrepancy A_y-M_y is meromorphic on
the connected half-plane Re(s)>3/4 and has infinite meromorphic order at
four because its germ vanishes there. The corpus's connected-domain order
theorem forces infinite order at every point in that half-plane. Thus the
two functions agree on a punctured neighborhood of each point and have the
same meromorphic order there.

If y is nonzero, its literal finite Möbius numerator is nonzero. The existing
unconditional simple-critical census and finite-exponential-type bound
supply a surviving pole at s=1+it, with exact order -1. That point belongs
to Re(s)>3/4, where A_y is analytic and has nonnegative order. Contradiction.
Therefore y vanishes on every retained coordinate. Applying the conclusion
to both y and -y supplies the two strict source signs.

## Finite witnesses and clipping

For each cutoff M, the actual pairing is continuous and linear in the finite
coordinate space. Its strictly positive half-space is open. The directional
witness theorem covers the unit sphere by these open sets. Compactness gives
a finite subcover K. The maximum pairing over K is continuous and strictly
positive on the sphere, so its minimum c is positive. Homogeneity gives the
stated margin for every vector.

Put `A(M)=sum_(d<=M) abs(C_d(M))`. The exact source pairing satisfies
`abs(<y,V_S(M)>)<=norm(y)*A(M)`. Take

`L=1+sum_(M in K)(A(M+1)+A(M))`,
`delta=min(1,c/(2L))`.

Every adjacent-cutoff displacement in K has pairing norm at most
`norm(y)*L`. Independent clipping below delta costs at most half the original
margin. All quantities are finite source expressions; no numerical values
or computed cutoff search enter the proof.

## Lean

- `RetainedPrimeLandauCarrier`: 18 public declarations; literal real primitive,
  finite positive measure, exponential tilts and exact MGF germ.
- `FiniteDirichletMellinContinuationObstruction`: 2 public declarations;
  global meromorphicity and the analytic continuation obstruction.
- `RetainedPrimeLandauSeparation`: 6 public declarations; Landau transfer,
  analytic reconstruction, zero classification and both strict source signs.
- `RetainedPrimeFiniteSourceMargin`: 11 public declarations; complete field
  coordinates and profiles, finite uniform witnesses and clipping tolerance.

All four modules passed scratch and exact-file `lake env lean` checks. Only
their needed oleans were emitted. Imports are wired into RHTower; no umbrella
or dependency build was run. No numerical experiment or computational premise
was used. All 37 new public declarations were axiom-audited once: only
`propext`, `Classical.choice` and `Quot.sound` occur. Global formal lint
passed with existing large-file warnings.

## Remaining cofinal gate

The theorem supplies no uniform bound on max(K), inverse margin, inverse
clipping tolerance, prime-window capacity or preparation cost as S changes.
The [actual arbitrary-field batch theorem](ccm-fu-arbitrary-retained-prime-batches.md)
closes exact partial-state identification, common-parent prime windows and
complete finite preparation bounds. For fixed S it gives arbitrarily long
actual batches at cofinal parent cutoffs under `722*2^|core|*M^2`. Keeping
these costs uniform as S changes remains necessary before inherited
middle-singleton energy exceeds the parent budget. The existing obstruction to core-first processing
with scalar reserves remains in force.

The next source-level target is quantitative transport of these arbitrary-field
witnesses through changing retained sets within one complete compatible
schedule. Fixed-field directional control alone does not prove PE4/PE4G/PE4C,
SD1 or RH.
