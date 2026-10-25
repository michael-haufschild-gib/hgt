# The intrinsic golden norm-lattice module is rank one

- **ID:** biarithmetic-intrinsic-golden-module
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (Lean formalization incomplete)
- **Proof status:** Only statements with completed Lean checks and axiom audits are proved. Paper arguments below are proof plans; every significant claim remains a formalization obligation.
- **Parent:** [Golden digital module](../1-in-progress/biarithmetic-golden-digital-module.md)
- **Statement:** For positive golden damping in the escaping range, the intrinsic generalized-integer counting receiver is a nonzero pure geometric row modulo finite shell energy. Every norm-lattice cofactor tangent is therefore the same rank-one kernel. Its one-prime payment domain is an exact weighted partial-sum space.

## Exact centered generating series

The underlying positive generalized-prime counts are already constructed in ACS:
`goldenDatum_beurling` in `TheGoldenCurveIsABeurlingSystem.lean` proves that the
actual golden point counts are divisor sums of natural prime multiplicities.
Its construction counts primitive periodic orbits outside a five-letter subshift.
The statement and source proof were inspected; no positivity premise is added here.

Write `P(u)=1-5u+5u^2=(1-alpha*u)(1-beta*u)`,
`Z(u)=P(u)/[(1-u)(1-5u)]`, and `0<t<1`. The cumulative generalized-integer
count has series `Z(u)/(1-u)`. Convolution with the damped inverse source gives
`Z(u)/[(1-u)Z(tu)]`. Centering by the actual residue mean

`m=1/Z(t/5)=(5-6t+t^2)/(5-5t+t^2)`

therefore gives

`A(u)=Z(u)/(1-u) * [1/Z(tu)-m]`.

Put `D=5-5t+t^2=5(1-t)+t^2>0`, `a=alpha*t`, and `b=beta*t`.
The cancellation of the counting pole is an exact polynomial identity:

`(1-tu)(1-5tu)-m(1-5tu+5t^2u^2)
 =(t/D)(1-5u)(1-t^2u)`.

Thus the centered series is exactly

`A(u)=(t/D) P(u)(1-t^2u) / [(1-u)^2(1-au)(1-bu)]`.

This identity also clarifies both endpoints. At `t=0` the centered row is zero; at
`t=1` the series is `1/(1-u)`, so the intrinsic row is constant and paid. The
positive-damping escape classification below is not asserted at `t=1`.

## A pure geometric row modulo a paid remainder

Assume `sqrt(5)<=a<alpha`, equivalently the positive-damping escape interval.
Then `1<a`, `0<b<sqrt(5)`, and `beta<a`. The coefficient of the simple geometric
factor at `a` is

`C=(t/D) P(1/a)(1-t^2/a) / [(1-1/a)^2(1-b/a)]`.

It is strictly negative: `1-alpha/a=1-1/t<0`, while `1-beta/a`,
`1-t^2/a=1-t/alpha`, `1-1/a`, and `1-b/a` are all positive.
Subtracting `C/(1-au)` from `A(u)` leaves a cubic numerator that vanishes at
`u=1/a`. Division by `1-au` therefore leaves a polynomial of degree at most two,
and

`A(u)-C/(1-au)=R(u)/[(1-u)^2(1-bu)]`.

No separation between `b` and one is needed; their possible collision is already
included in this formula. At radius `1/sqrt(5)`, both remaining geometric factors
are absolutely summable. Consequently the coefficient remainder `r_M` satisfies
`sum_M |r_M|5^(-M/2)<infinity`, and hence has finite shell energy. We have the exact
row decomposition `A_M=C a^M+r_M`, with `C!=0` and a paid remainder. Lean verification of
the decomposition and remainder payment remains an obligation.

## Every intrinsic norm-lattice tangent

Use shell norm `||v||_M^2=sum_(m=0)^M |v_m|^2/5^m`. Right shift by `r` cells,
zero below `r`, contracts the total shell norm by `5^(-r/2)`. The geometric row has
energy `sum_(m<=M)(a^2/5)^m`, which diverges at and above `a=sqrt(5)`.
The paid remainder cannot cancel this divergence by the reverse triangle inequality.

For each fixed shift `r`, `shift_r A-a^(-r)A` has finite total shell energy:
the remainders are paid and the geometric discrepancy has only finitely many
nonzero initial cells. Cauchy–Schwarz after division by the escaping base energy
therefore gives, along every horizon sequence,

`K(r,s)=a^(-r-s)`.

This is the rank-one kernel of the vector `r->a^(-r)`. The completed cyclic
norm-lattice module is one-dimensional and shift by norm `5^r` acts as `a^(-r)`.
The same result holds for the step-prefix pronic normalization: a complete shell
has weight `(4/5)5^(-m)`, and a partial final shell does not change the bounded
perturbation argument.

## Critical Wiener kernels are intrinsically paid

The intrinsic source comparison needs its own mean-correction bound; the ordinary-floor
bound cannot be imported by relabelling the counting kernel. Partial fractions of the
actual cumulative count give exactly

`B_m=(5/16)5^m-m/4+11/16`.

The denominator-free formal-series identity is
`16 B(u)=5/(1-5u)-4/(1-u)^2+15/(1-u)`.
Indeed `16 P(u)=5(1-u)^2-4(1-5u)+15(1-u)(1-5u)`; multiply by
`1/[(1-u)^2(1-5u)]`. Reading coefficients gives the displayed formula directly.

Its successive increments are `(5/4)5^m-1/4>=1`, and `B_0=1`, so
`0<=B_m<=5^m`. For the point kernel at norm `5^r`, the centered row is
`B_(m-r)1_(m>=r)-5^(-r)B_m`. Below `r`, its squared shell norm is at most
`5^(-2r)sum_(m<r)5^m<=5^(-r)/4`. At `m=r+s`, cancellation of the leading
counting term leaves exactly

`-(1/4)[(1-5^(-r))s-r*5^(-r)]+(11/16)(1-5^(-r))`.

Since `r*5^(-r)<=1`, its absolute value is at most `s+1`. The elementary induction
`(s+1)^2<=4^s` bounds the remaining squared norm by
`5^(-r)sum_s(4/5)^s=5*5^(-r)`. Thus each point-kernel receiver has shell norm
at most `sqrt(6)*5^(-r/2)`. Absolute Wiener synthesis now pays every critical
one-prime kernel, uniformly by `sqrt(6)||f||_W`.

For arbitrary absolutely mean-summable intrinsic sources, the generating-series identity
also gives the exact centered convolution law
`A_(f*c)=P_f A_c+m_c A_f`. The proved critical-kernel bound makes the second term
paid. Hence repairing the actual source is equivalent to finite energy of its cofactor
action. This explicitly discharges the mean-correction bridge used next.

## Exact intrinsic one-prime payment domain

For a critical one-prime Wiener kernel `f_r`, let
`S_m=sum_(r<=m) f_r a^(-r)`. Its action on the pure geometric row is exactly
`a^m S_m`, so payment is equivalent to

`sum_m (a^2/5)^m |S_m|^2<infinity`.

The paid remainder preserves this criterion by the bounded shift representation.
For `a>sqrt(5)`, it is equivalent to `sum_r f_r a^(-r)=0`, by the geometric-tail
argument on the ordinary digital-energy card. At `a=sqrt(5)`, it is the stricter
condition that the partial sums of the normalized `ell1` coefficients lie in `ell2`.
The explicit nonclosed boundary kernel and its corrected finite approximants thus
also apply in this intrinsic model, without needing digit moments.

## Scope and verification

This is the action by the golden system's own norm lattice. It differs from ordinary
integer floor incidence, whose full cofactor module is infinite-dimensional on the
parent paper derivation. In particular the intrinsic model at zero damping is paid,
whereas the ordinary-floor inverse-zeta receiver is not. Both the counting kernel
and the admitted cofactor semigroup must therefore be specified in the golden battery.
The polynomial cancellation and partial fractions are classical; no separate novelty
claim is made for them.

- [x] Exact paper source normalization and polynomial cancellation.
- [x] Proof plans recorded for the paid-remainder decomposition, all-horizon rank-one kernel, and one-prime payment domain.
- [x] Lean intrinsic generating-series construction and exact cancellation.
- [x] Lean exact cumulative counting coefficients and both damping endpoints.
- [ ] Lean weighted remainder bound and complete tangent classification.
- [ ] Lean payment criterion, direct checks, axiom audits, and umbrella imports.

The checked generating-series subset has its own stage-3 card:
[Exact intrinsic counting and centering](../3-formalized/biarithmetic-intrinsic-golden-series.md).
`IntrinsicGoldenSeries.lean` passed its direct repository check and six clean
transitive axiom audits. The remaining module and payment statements are
unproved formalization obligations.

## Lean construction obligations

`/tmp/BiarithmeticFiveShellPronicEnergy.lean` drafts the exact shell/step-prefix
bridge. Every signed block pairing has factor `(4/5)5^(-M)`; bounded
ordinary pronic norms at all cutoffs are equivalent to the weighted shell
square sum. It reuses the checked block telescope and finite-prefix method.
Four audits drafted; unchecked. Shift identities and tangent limits remain.

`/tmp/BiarithmeticFiveShellShifts.lean` drafts exact power-of-five floor
dilation, inverse-norm energy scaling, the finite geometric boundary
defect, and the square-root shell convergence radius. `Nat.log_div_base_pow`
was source-inspected after corpus and Mathlib searches. Five audits drafted;
unchecked. These identities supply the norm-lattice tangent comparison.

`/tmp/BiarithmeticGeometricShellTangents.lean` drafts full-horizon escape
for the pure geometric shell row, paid finite cofactor boundaries, its exact
norm-lattice Gram limit, and the rank-one finite-packet identity. Four audits
drafted; unchecked. Actual intrinsic source transfer and a completed-module
isomorphism remain separate obligations.

The completion comparison reuses `HTGeometry.KernelHilbert` rather than a
new quotient carrier. `KernelHilbert.dense_span_vectors` proves that its
canonical Gram vectors are total. `denseFeatureGramUnitary` identifies two
complete Hilbert spaces from equal total feature Grams. For the geometric
kernel, the scalar features are `e_r=a^(-r)` and `e_0=1`, so their span is
the entire complex line. The resulting isometry sends each canonical vector
to `e_r`; conjugating scalar multiplication gives the unique bounded shift
extension, with `shift_r delta_s=delta_(r+s)`. This is a dependency-closed
proof plan for the completed rank-one module. Corpus statements and their
source proofs were inspected. `BiarithmeticGeometry/GeometricShellHilbert.lean`
passed its direct source check and all six transitive audits; its umbrella
import and [stage-3 card](../3-formalized/biarithmetic-geometric-shell-hilbert-module.md)
are present. Actual-source comparison remains the separate tangent transfer.

`/tmp/BiarithmeticIntrinsicGoldenTangentModule.lean` connects that canonical
completion to the actual source limit and records dimension one and all
norm-lattice shift eigenvalues. Four audits drafted; unchecked. Its source
limit theorem retains the precise positive-damping escape interval; the
algebraic geometric kernel is also defined outside that interval without
asserting a source-limit comparison there.

`/tmp/BiarithmeticIntrinsicGoldenTangents.lean` drafts the actual-source
transfer: the weighted absolute remainder has finite shell square energy,
the exact source decomposition holds on every integer block, the actual
receiver escapes, and every power-of-five Gram entry has the geometric
rank-one limit along the full horizon sequence. Five audits drafted;
unchecked. Its residue, shell, and perturbation dependencies also remain
under verification; no completed-module isomorphism is asserted yet.

`BiarithmeticGeometry/GeometricPoleExtraction.lean` proves exact polynomial
division after removing the primary reciprocal evaluation, the residual
degree bound, and absolute summability with both secondary geometric
factors retained. It imports the corpus's actual `geom` series and
`HTGeometry/PowerSeriesAbsoluteEvaluation.lean`. Its direct source check
and all four transitive audits passed; the umbrella import and
[stage-3 card](../3-formalized/biarithmetic-primary-geometric-pole-extraction.md)
are present.

`/tmp/BiarithmeticIntrinsicGoldenRemainder.lean` applies that construction
to the actual centered intrinsic series. Its proposed declarations identify
the real residue, prove its strict negative sign throughout positive-damping
escape, split every source coefficient exactly, and prove weighted absolute
summability of the remainder at radius `1/sqrt(5)`. This draft is also
unchecked. The `IntrinsicGoldenSeries` dependency olean is available.

`/tmp/BiarithmeticIntrinsicPointKernelEnergy.lean` separately formalizes the
paper point-kernel estimate from the checked actual counting formula. Its
exact affine tail, uniform absolute tail bound, square summability, and
total bound `6*5^(-r)` have four drafted audits; unchecked. The dedicated
corpus query returned the actual count and its bounds, but no prior
intrinsic point-kernel payment theorem. Infinite synthesis and the centered
convolution comparison are still required for the full payment criterion.

`/tmp/BiarithmeticIntrinsicWienerSynthesis.lean` drafts the completion step.
The actual point-response vector has coordinates `P_r(M)/sqrt(5)^M`, so
its squared norm is exactly the point shell-energy sum. Divide the vector
by `sqrt(6)` and extend by zero outside powers of five. Its norm obeys the
actual critical Wiener weight, allowing direct reuse of AOT's checked
`WienerAlgebraAt.sequenceExtension`. Rescaling gives a bounded complex-linear
map with norm at most `sqrt(6)` and the prescribed values on every five-power
point mass. Five audits drafted; unchecked. The exact coordinate identity
for an infinite centered kernel, the source convolution law, and the full
payment criterion remain obligations; the bounded extension alone is not
being treated as those source comparisons.

The following coordinate comparison avoids an unproved interchange with
the growing counting kernel. For a fixed shell `M`, its actual centered
receiver is a continuous Wiener functional: a finite coefficient sum minus
`B_M` times the inverse-norm mean. The latter is another instance of AOT's
sequence extension, with value `1/n` on five-power point masses and zero
elsewhere. The completed synthesis followed by its `M`th coordinate is also
continuous. The two maps agree on every actual point mass; the checked
`hasSum_pointMass` expansion makes them equal on every Wiener kernel.
Thus their weighted square sum equals the synthesis norm squared, giving
the claimed bound `6*||k||_W^2`. This is a proof plan until its Lean checks pass.
`/tmp/BiarithmeticIntrinsicKernelPayment.lean` drafts these five main claims.
The arbitrary-source centered convolution identity and the full intrinsic
repairing-domain classification remain separate formalization obligations.

`/tmp/BiarithmeticIntrinsicCenteredConvolution.lean` drafts that exact
convolution identity using actual inverse-norm absolute evaluation, its
finite-coefficient counting comparison, and the paid critical-Wiener mean
correction. It also identifies the generic construction with the actual
golden receiver, proving mean convergence from the already checked
arithmetic-source theorem. Seven audits drafted; unchecked. The bounded
shell action and full repairing-domain classification remain obligations.

Pending source check: `/tmp/BiarithmeticComplexShellShift.lean` constructs complex normalized shell shifts with exact isometry and semigroup laws. This is the missing bounded-operator input for the existing intrinsic infinite-kernel convolution proof plan.

Pending source check: `/tmp/BiarithmeticIntrinsicShellConvolution.lean` constructs bounded convolution by every actual critical Wiener kernel, identifies its finite Cauchy coordinates, and proves weighted shell-energy stability with operator bound `||k||`. This addresses the infinite-kernel action required by the intrinsic centered-convolution proof plan.

Pending source check: `/tmp/BiarithmeticIntrinsicPaymentDomain.lean` identifies the actual centered filtered receiver, pays its mean correction and geometric remainder, and reduces full intrinsic payment to weighted square summability of its geometric causal response. Every analytic input has a queued Lean proof obligation; no additional source hypothesis is used. The draft also identifies intrinsic payment with actual ordinary golden payment on the one-prime algebra throughout positive-damping escape.
