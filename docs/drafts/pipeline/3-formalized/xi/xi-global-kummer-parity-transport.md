# Global Kummer parity after the actual Xi pullback

- **ID:** RH-XGKPT-20261007
- **Stage:** 3-formalized
- **Type:** source comparison; dependency-closed paper proof, formalization in progress
- **Parent:** `xi-legendre-formal-source-section.md`
- **Objective:** settle global non-divisibility after the meromorphic Xi pullback, which local
  formal divisibility and the generic rational-function calculation do not decide.

## Competing conjectures and selected statement

For `p>=2`, write `d_p(s)=p^(-s)xi(s)` and `F_p=1-d_p`. Let `K` be the field of globally
meromorphic functions on `C`, not the field of meromorphic germs at one point. In an algebraic
closure of `K`, choose `q_p^2=d_p/F_p`. Put `L_S=K(q_p : p in S)` for finite prime sets `S`.

The competing possibilities are: the section's two-division classes remain independent on
`L_S`; they collapse to a common nonzero class; or local divisibility extends globally and
kills them all. The algebraic formulas select the middle candidate, provided the following
global square-class calculation holds.

1. The classes of `xi` and of all `F_p` are independent in `K^*/K^*2`. In fact this
   holds for every integer label `p>=2`, including composite labels.
2. `[L_S:K]=2^|S|`. The class of `xi` remains nonzero on `L_S`, and every `F_p`, `p in S`,
   has that same class there. This persists in the directed union over finite `S`.
3. The full field of halves of each original section `P_p` over `L_S` is the same nontrivial
   quadratic extension `L_S(sqrt(xi))`. Thus every `P_p` remains globally non-two-divisible,
   while all its prime-indexed two-division classes coincide.
4. For nonempty `S`, on the normalized analytic cover over the finite complex plane, this final quadratic
   extension is unramified at every finite point. Its global nontriviality is invisible to
   every local formal division calculation.

This produces an actual global source class and classifies a loss of prime information
under joint base change. It does not select a critical-line component or prove RH.

## Paper mechanism

For a nonempty finite prime set `S`, choose a real `b` strictly between its smallest prime
and every other prime in `S` (any `b>p` if `S={p}`). The previously proved qualitative
real-axis behavior of Xi gives `t>1` with `xi(t)=b^t`: at `t=1`, `xi(1)=1/2<b`, whereas
along the positive even integers `log(xi(t))/t` tends to infinity. Continuity gives the
crossing. No threshold or numerical approximation is needed.

At this `t`, exactly one factor `F_p(t)` is negative and all the others are positive.
At `t=1` all factors are positive. Since Xi is positive on the real axis, the same sign
change holds for `xi^epsilon * product(F_p)`, `epsilon=0,1`.

The same proof covers any nonnegative integer exponent of Xi and arbitrary distinct
integer labels at least two. Choose the rate halfway between `log(p_min)` and
`log(p_min+1)`; every remaining integer label has strictly larger logarithm. Thus no
primality fact is needed for the independence argument.

A globally meromorphic square which is real on the real axis cannot change sign there
away from zeros and poles: reflection of a square root is either that root or its negative,
by the identity theorem and the integral-domain property. In the first case its real
values square nonnegatively; in the second they square nonpositively. A root of an entire
function has no poles. This rules out every nonempty product above. The remaining class
`xi` is nonzero because Xi has an odd-order critical-line zero, already established in
`XiRightHalfSquareRootBoundaryNoExtension.lean`.

Classical Kummer theory now identifies the kernel on square classes after adjoining the
`q_p` with the span of `[xi]+[F_p]`; `p^(-s)` already has the global entire square root
`p^(-s/2)`. Independence proves all degree and persistence assertions. Every element of
the infinite compositum lies in a finite subextension.
The infinite statement concerns this algebraic directed union; persistence under any
further completion requires a separate proof.

For the section `P`, the existing two-descent calculation gives its halves field by
adjoining `sqrt(B)`, where `B=1+q_p^2=1/F_p`. On `L_S`, `[B]=[F_p]=[xi]`, proving (3).

At a finite point where Xi has odd order, every `F_p` is a unit, and adjoining any `q_p`
already makes the Xi order even. At a point where Xi has even order, adjoining `sqrt(xi)`
is locally split over the base complex meromorphic germ field. Complex residue fields
have all square roots. These two cases prove (4) for nonempty `S`, on normalization.
There is no assertion at the essential end at infinity, and no compactness is inferred.

There is also an explicit geometric unit. On the common cover choose coordinate functions
`v^2=xi`, `w_p^2=F_p` and the source-defined entire unit `beta_p=p^(-s/2)`. Then

```
U_p=w_p+i*beta_p*v,       U_p^(-1)=w_p-i*beta_p*v,
U_p^2=1-2*d_p+2*i*beta_p*u_p,       u_p=v*w_p.
```

The identity `w_p^2+(beta_p*v)^2=1` proves invertibility. The simultaneous deck involution
`(v,w_p for all p)->(-v,-w_p for all p)` sends every `U_p` to `-U_p`, and has no fixed
point: `v=0` would force every `w_p^2=1`. Thus the final double cover is visibly free.
Its quotient has functions `u_p^2=xi*F_p`, the same field as the marked `q_p` cover.
The units `U_p/U_q` descend to that quotient: the common mod-two class does not erase all
prime-labelled unit data. Their logarithmic differentials are the next possible integral
source comparison, not an assumed identification with the existing Hochschild class.

## Internal and external audit

- The generic `C(q)` non-divisibility and the explicit two-descent fields are on the parent
  card. They do not prove any claim over `K`; this card addresses that missing passage.
- `MeromorphicPlaneField.lean` supplies a genuine global field modulo codiscrete equality.
  Replacing it by a local germ field would make every `F_p` a square near a Xi zero and
  invalidate the global conclusion.
- `QuadraticTowerSquareClasses.lean` already supplies square-class persistence in finite
  radical towers. Reuse it instead of rebuilding Kummer theory.
- Classical parents: [Milne, Fields and Galois Theory](https://jmilne.org/math/CourseNotes/FT.pdf),
  Theorem 5.30 and Remark 5.32; [Zarhin, Division by 2 on elliptic curves](https://arxiv.org/abs/1605.09279),
  explicit halves fields; Schwarz reflection and the identity theorem.
- The mechanism is classical. The particular global Xi pullback and its shared surviving
  class require an exact source proof; significant novelty is not certified.
- The real-end input is explicitly an existing analytic growth theorem. This route is a
  global divisor-parity calculation, not a proposed positivity or growth-bound proof of RH.

## Checklist

- [x] Exact competing conjectures and source field specified.
- [x] Finish hostile audit and dependency-closed paper proof.
- [x] Formalize global meromorphic square obstruction and actual Xi square-class independence.
- [x] Formalize finite/infinite marked-cover persistence.
- [x] Formalize exact extension degrees and the complete common halves field.
- [x] Formalize actual elliptic-group non-divisibility of the original section `P`.
- [x] Close the translated section `Q` and its literal `P+(0,0)` identification.
- [x] Final targeted builds, direct source checks, axioms, wiring, index, lint snapshot, and scientific audit for the six implemented leaves.

`[OPEN CORE]` for RH: compare this nonzero global class with the arithmetic normal cycle in a
way that retains prime labels and constrains the real form of each zero component. Global
non-divisibility alone, especially a prime-independent surviving class, does not do this.

## Hostile audit verdict

`PROVED ON PAPER`, with classical Kummer and explicit two-descent parents. The finite-set
argument distinguishes the least label strictly, including the singleton case. The only
empty-set obstruction needed is Xi itself, supplied by the already formalized odd-order
critical zero. No generic non-divisibility is transported without a new proof: independence
is proved in the actual global meromorphic field. The normalized double cover is free only
for nonempty prime sets; no assertion at infinity is used. Arbitrary roots are coordinates
on a source-defined cover, not a preferred analytic root. Prime-indexed parity classes
coincide, but their explicit units and ratios remain distinct data.

Scientific verdict: exact source specialization and premise discharge for the parent
global-divisibility question; no certified novel mechanism and no discharged RH premise.
Anti-theatre check: the deliverable must include actual Xi square-class independence and
its persistence, not only a generic Kummer receiver. Anti-laziness check: no unsupported
analytic source assumption is introduced; qualitative growth and odd-order existence are
existing unconditional theorems whose declarations will be audited.

## Formalization checkpoint

- Scratch proof of global meromorphic-root normalization and Schwarz-real square sign
  rigidity passed `lake env lean /tmp/rh-meromorphic-square.lean` with empty output.
- New reusable module: `HTGeometry/MeromorphicPlaneSquareRoot.lean`; targeted build passed
  (only that new leaf compiled). Final direct source audit passed with empty output.
- Actual Xi finite-product proof passed its scratch check, then targeted build as
  `RHTower/XiGlobalKummerSquareClasses.lean` (259 lines). It includes the qualitative
  exponential crossing, real sign separation for all finite integer-label sets, and the
  global meromorphic-field interface. Both new modules are wired into their umbrellas.
  Final direct source check passed with empty output. Both modules' axiom audits use only
  `propext`, `Classical.choice`, and `Quot.sound`. Generated index and lint remain pending.
- Finite/infinite persistence is being checked in `/tmp/rh-xi-global-kummer-tower.lean`.
  The extension adjoins roots of `xi*F_(n+2)` for every natural index, so persistence there
  also excludes square roots on any smaller finite prime-marked cover. No numerical experiment.
- The finite/infinite persistence declarations and generic Legendre doubling identities
  passed elaboration and their axiom audits in the combined scratch. Two later exponential
  helper declarations had namespace errors; those were not promoted. The checked parts are
  now `RHTower/XiGlobalKummerMarkedTower.lean` and `HTGeometry/LegendreDoublingSquare.lean`,
  with targeted builds and final direct source checks passed, and umbrella imports wired.
- `RHTower/XiGlobalKummerLegendre.lean` now formalizes the actual original section,
  non-two-divisibility, marking-coordinate recovery, and explicit nonsquare unit representative.
  Its targeted build and final direct source check passed. All five modules have passed
  actual-source checks with empty logs; all 99 public declarations passed the scratch
  axiom audit with only standard Lean foundations.
- The translated section and its literal equality with `P+(0,0)` are now under check in
  `/tmp/rh-xi-global-kummer-translated.lean`. Degree formulas, complete halves-field
  classification, and geometric unramification remain paper-proven follow-ups.
- Internal searches returned partial results with complete file inventory but many pending
  or stale compiler records. Retrieved generic Laurent-polynomial certificates and Witt
  class declarations do not prove this source statement and were not used. Applicable
  source parents are the checked Xi growth/parity declarations, normal-form API, and
  `QuadraticTowerSquareClasses.lean`.

## Explicit group-law consumer

Use the equivalent marked coordinates `u_n^2=xi*F_n`, for all integers `n>=2`.
These generate the same field as `q_n`, since `q_n=beta_n*u_n/F_n` and
`u_n=q_n*F_n/beta_n`. On this actual joint field, set
`d_n=beta_n^2*xi`, `lambda_n=1+d_n`, and `P_n=(d_n,beta_n*u_n)`.
The curve equation is immediate from `y_n^2=d_n*(1-d_n)`. Its y-coordinate is
nonzero in the function field, hence the point is nonsingular.

The actual affine group law gives

```
x(2R) = ((x(R)^2-lambda_n)/(2*y(R)))^2
```

whenever the double is finite. Therefore a half of `P_n` would make `d_n` a square,
and dividing its root by the nonzero `beta_n` would make Xi a square in the joint
marked field. This is impossible by finite-tower persistence. This formulation directly
consumes the common surviving class and avoids mistaking a rational-function-field
obstruction for an obstruction after the actual Xi pullback.

For the translated section `Q_n=P_n+(0,0)`, its x-coordinate is `(1+d_n)/d_n`, so
`x(Q_n)-1=1/d_n`. The companion doubling identity
`x(2R)-1=((x(R)^2-2*x(R)+lambda_n)/(2*y(R)))^2` also rules out a half of `Q_n`.
Both identities are algebraic group-law statements; the non-divisibility input is the
new actual global Xi square-class theorem.
The common halves-field assertion concerns `P`. For `Q`, the parent descent also carries
the class of `1+d_p`; non-divisibility of `Q` does not identify its full halves field with
that of `P`, or assert that all translated-section classes coincide.

## Unit representative of the surviving class

Already on the marked cover, put
`a_p=1-2*d_p+2*i*beta_p*u_p` and
`a_p_inverse=1-2*d_p-2*i*beta_p*u_p`. The relation `u_p^2=xi*F_p` gives the exact identities

```
a_p*a_p_inverse = 1,
xi = a_p*(u_p-i*beta_p*xi)^2,
F_p = a_p*(F_p-i*beta_p*u_p)^2.
```

Thus the common nonzero square class has an explicit nowhere-vanishing holomorphic
representative, not only a meromorphic representative with an even divisor. Its root
extension is locally given by `T^2-a_p`, whose derivative `2*T` is invertible. This supplies
an algebraic unramified model before invoking analytic normalization. On the common cover,
the exact identity

```
(U_p-U_p^(-1))/(U_q-U_q^(-1)) = beta_p/beta_q
```

recovers the prime exponential ratio from the odd parts of the units. This is an exact
retention statement; a comparison with the arithmetic normal cycle remains unproved.

## Six-module verification closure — 2026-10-07

The translated-section leaf `RHTower/XiGlobalKummerTranslatedSection.lean` passed its
targeted build and final `lake env lean` check on the actual source, with empty output.
All six leaves passed final direct checks; all 112 public declarations use only
`propext`, `Classical.choice`, and `Quot.sound`. The two generic leaves and four
source leaves are wired into the area umbrellas. Index regeneration passed. No
full or umbrella build, admission, new axiom, numerical research, or heartbeat increase.

Global lint exited 1 on these 16 concurrently developed, unrelated unwired leaves:

- `GaloisForLFunctions.RHTower.CCMParityQuartetEvenFloor`
- `GaloisForLFunctions.RHTower.CCMParityQuartetModel`
- `GaloisForLFunctions.RHTower.CCMParityQuartetZeroSum`
- `GaloisForLFunctions.RHTower.WeilConeBoundaryDilationInequality`
- `GaloisForLFunctions.RHTower.WeilConeBoundaryDilationLogAveraging`
- `GaloisForLFunctions.RHTower.WeilConeBoundaryDilationRigidity`
- `GaloisForLFunctions.RHTower.WeilZetaSquareAveraging`
- `GaloisForLFunctions.RHTower.WeilZetaSquareBoundaryInequality`
- `GaloisForLFunctions.RHTower.WeilZetaSquareDilationRigidity`
- `GaloisForLFunctions.RHTower.WeilZetaSquareMoments`
- `GaloisForLFunctions.HTGeometry.ApertureConeCalculus`
- `GaloisForLFunctions.HTGeometry.ApertureConeWinding`
- `GaloisForLFunctions.HTGeometry.ApertureLogTranslation`
- `GaloisForLFunctions.HTGeometry.ApertureOpenHistoryIdeal`
- `GaloisForLFunctions.HTGeometry.BoundaryCoronaCStarAlgebra`
- `GaloisForLFunctions.HTGeometry.GcdWeightedSeriesInversion`

No lint error names one of the six implemented leaves. This is a snapshot, not a
claim that the repository-wide gate passed. Exact degree formulas, complete halves-field
classification, and geometric unramification remain paper-proven formalization work;
this card therefore remains at stage 2. The actual global non-divisibility premise for
both sections is discharged. No RH zero-location premise is discharged.

## Lean certificate (2026-10-09)

Index `n` carries the label `n+2` (`β_n = (n+2)^{-s/2}`, `F_n = 1 - (n+2)^{-s}ξ`); every claim
holds for all integer labels `≥ 2`, primes included.

| Card claim | Lean declaration |
|-|-|
| Exponential crossing `ξ(t) = b^t`; one negative factor at the crossing | `exists_xi_real_exp_crossing`, `realFactor_at_crossing`, `exists_realPacket_neg` |
| A global meromorphic square real on ℝ cannot change sign; roots of entire functions are entire | `MeromorphicPlaneSquareRoot.not_isSquare_plane_of_real_sign_change`, `entire_square_real_sign_product_nonneg`, `entire_sqrt_of_isSquare_plane` |
| (1) `[ξ]`, `[F_p]` independent in `K^*/K^{*2}` | `packetElement_not_isSquare`, `xi_pow_mul_prod_factors_not_isSquare`, `xiElement_not_isSquare` |
| (2) `L_S = K(q_p)` with `q_p² = d_p/F_p`, equal to `K(u_p)`, `u_p² = ξF_p` | `finiteMarkedExtension` (`XiCriticalStripFiniteTensor`), `qRoot_sq`, `finiteMarkedExtension_eq_adjoin_qRoot` |
| (2) `[L_S : K] = 2^|S|`; exact Kummer kernel | `finiteMarkedExtension_finrank`, `isSquare_finiteMarkedExtension_iff` |
| (2) `[ξ] ≠ 0` on `L_S`; `[F_p] = [ξ]` on `L_S` | `xi_not_isSquare_finiteMarkedExtension`, `factor_not_isSquare_finiteMarkedExtension`, `radicand_isSquare_finiteMarkedExtension` |
| (2) persistence in the directed union | `iSup_finiteMarkedExtension`, `xi_not_isSquare_markedExtension`, `xi_mul_factor_isSquare_markedExtension`, `isSquare_markedExtension_iff` |
| Section `P_p = (d_p, β_p u_p)`; group-law halving criterion over every marked field and extension | `markedPoint`, `markedPoint_has_half_iff`, `markedPoint_halvingDecidedBy` |
| (3) `P_p` not two-divisible over `L_S`; its halves field over `L_S` is `L_S(√ξ)` for every `p ∈ S`; degree 2; four halves | `finiteSection_not_double`, `adjoin_finiteSection_half` (with generic `LegendreDoubling.adjoin_half_coordinates`), `finiteHalvesField_finrank`, `finiteSection_ncard_halves` |
| Same over the infinite marked field; translated section `Q = P + (0,0)` | `sourceSection_not_double`, `adjoin_sourceHalf_coordinates`, `translatedSection_eq_add_torsion`, `translatedSection_not_double` |
| Unit representative `a_p a_p⁻¹ = 1`, `ξ = a_p (u_p - iβ_pξ)²`, `F_p = a_p(...)²` | `unitRepresentative_mul_inverse`, `unitRepresentative_mul_square`, `markingUnit_mul_inv`, `markingUnit_mul_sq` |
| (4) unramified at every finite point for nonempty `S`: `a_p` a unit and `X² - a_p` of unit discriminant at every place over the finite plane, `ξ` of even order there, `L_S(√ξ) = L_S(√a_p)` | `XiFiniteMarkedUnramified.IsFinitePlace`, `valuation_markingUnit`, `valuation_discriminant`, `valuation_xi_eq_sq`, `finiteMarked_unramified` |
| Common cover: `w_p² = F_p`, `w_p² + (β_p v)² = 1` (no point with `v = w_p = 0`), `U_p U_p⁻¹ = 1`, `U_p² = a_p` | `coverW_sq`, `coverW_sq_add_sq`, `coverUnit_mul_inv`, `coverUnit_sq` |
| Deck involution `v ↦ -v` of `L_S(√ξ)/L_S`, involutive, `U_p ↦ -U_p` | `finiteDeck`, `finiteDeck_root`, `finiteDeck_involutive`, `finiteDeck_coverUnit` |
| `U_p/U_q` descends to `L_S`, no `U_p` does; `(U_p - U_p⁻¹)/(U_q - U_q⁻¹) = β_p/β_q` | `coverUnit_mul_inv_mem`, `coverUnit_not_mem`, `coverUnit_odd_ratio` |

Formal reading of (4).  A place over the finite plane is any valuation of `L_S` (values in a
linearly ordered commutative group with zero) that is at most one on every entire function; the
points of the normalized analytic cover over finite points give such places, so the statement
covers them all.  At each such place `ξ = a_p t²` with `a_p` a unit, i.e. `L_S(√ξ)/L_S` is generated
by the square root of a unit with unit discriminant.

Audit.
- `lake env lean` passes with no diagnostics on `HTGeometry/{LegendreHalvesField,
  MeromorphicPlaneSquareRoot, QuadraticTowerSquareClasses, QuadraticRootConjugation}` and
  `RHTower/{XiFiniteMarkedFields, XiFiniteMarkedUnramified, XiCriticalStripFiniteTensor,
  XiGlobalKummerSquareClasses,
  XiGlobalKummerMarkedTower, XiGlobalKummerLegendre, XiGlobalKummerTranslatedSection,
  XiKummerUnitRoots}`; the halving modules are certified on `xi-legendre-complete-halving-criterion.md`.
- Axiom audit: 288 declarations, only `propext`, `Classical.choice`, `Quot.sound`.
- All modules wired once into `HTGeometry.lean` / `RHTower.lean`.

## Log (promotion)

- 2026-10-09: finite fields `L_S`, degrees, kernel, halves field, unramified places, cover units and
  deck involution formalized (`LegendreHalvesField`, `XiFiniteMarkedFields`,
  `XiFiniteMarkedUnramified`); promoted to stage 3.
