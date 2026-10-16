# 017: Original-source convolution spectral invariance

Status: **FORMALIZED**. One structural contribution, spanning HF and RN.

Main result: for every original all-weight Meyer source g, the complete
Fredholm inverse from 016 equals I+C_h for an actual original source h.
The repaired operator is a continuous automorphism of literal original
Meyer cohomology, and every admitted finite native theta packet has unique
compact absolutely continuous repaired solutions for arbitrary source symbols.

Baseline: **16/100**. The previous goal turn is verified progress: nine
current artifacts and unique umbrella imports implement faithful whole-source
convolution, exact finite resonance reduction, actual causal exceptional
packets and full compact Weil/CCM trace. Routine consequences of 001–016 do
not count again. The 100-contribution goal attachment has been reread.

Mission: unconditional structural RH progress from current Lean evidence,
combining distinct frontier mechanisms. No web, external novelty checks, old
research reports, numerical experiments, subagents, full/umbrella builds,
heartbeat increases, commits or pushes. One owned foreground Lean process
at a time. Keep source admission separate from completion statements.

Session init: Serena memories listed and contribution016 memory read;
architecture/testing docs absent. The current route map's open cores were
scanned across all routes. The hgtl7 research workflow continues with the
user's corpus-only instructions overriding external novelty phases.
`update_plan` remains unavailable; this card is the plan and durable state.

Plan:
1. Search current corpus across source inversion, native infinite synthesis
   and independent sign/transport routes; inspect exact source declarations.
2. Conjecture, attack, and prove a distinct structural construction with all
   original-object admission paid. Record failed conjectures and survivors.
3. Formalize, direct-audit, inspect axioms, wire, lint, index and clean before
   counting the contribution.

## Conjecture log

1. Lift the Hilbert inverse by unrestricted entire interpolation. Rejected
   as a proof: entire interpolation does not supply rapid decay on every
   vertical strip. Hilbert completeness and finite-packet realization also
   do not give that source admission. No impossibility claim is made.
2. Obtain original-Frechet finite spectral synthesis directly from global
   Xi synthesis. Deferred: injective full-jet comparison and Hilbert density
   do not supply this stronger topology. Contour truncation would need its
   own source convergence proof.
3. **Conjecture: the repaired convolution inverse is itself a unitized
   original-source convolution on literal Meyer cohomology.** Every original
   g should admit an original h such that the repair from 016 has inverse
   I+C_h on the original quotient, agreeing with its bounded Hilbert inverse.
   This would give actual continuous source-class solutions for arbitrary
   forcing, retaining the original finite Xi compatibility conditions.

The successful mechanism uses the geometry of the *denominator's* zero set.
Put D=1+M_b, where b represents the actual class [g]-P_g[g]. D is nonzero at every Xi point
and tends uniformly to one at vertical infinity in every fixed strip.
Its zeros, with all multiplicities, are therefore finite in each closed
vertical strip. Full-germ exponential localization on this
horizontally escaping divisor provides an entire strip-rapid H whose
jets there equal those of 1/xi. Then U=(1-xi*H)/D is entire, U-1 is strip
rapid, and reconstruction gives the required original inverse source.

## Dependency-closed paper construction

Write S for the entire all-strip rapid class already reconstructed into the
original Meyer source. For each zero w of D, let m be its full analytic
order and D_w=D/(z-w)^m, with its entire extension. D_w is bounded on each
vertical strip: use bounded D outside the unit disc at w and continuity on
the remaining compact part. The corpus's unconditional source Mellin jet
independence and finite dual surjectivity already realize any finite germ
at any complex w, without a new Gaussian construction. Apply them to the
germ 1/(xi*D_w). Multiplying the resulting Mellin transform by D_w gives
F_w in S, matching the germ 1/xi at w
through order m-1 and vanishing to the required D-order at every other node.

The smallness mechanism is simpler than a variable-width Gaussian. If
|Re w|>r, let sigma be the sign of Re w and delta=|Re w|-r>0. For a positive
integer n put t(z)=exp(n*sigma*(z-w)) and
L(z)=1-(1-t(z))^m. At w, L-1 vanishes to order at least m. On |Re z|<=r,
|t(z)|<=exp(-n*delta), and the finite geometric identity gives
|L(z)|<=m*2^m*exp(-n*delta). L is bounded on every fixed vertical strip,
so F_w*L remains in S. By taking n sufficiently large, this product is
arbitrarily small in any specified finite list of strip seminorms without
changing any interpolation conditions. Negative inner radii give an empty
strip and impose no smallness condition.

The zeros of D are finite in every closed vertical strip: D tends uniformly
to one at vertical infinity, and its remaining zeros lie in a compact set;
the analytic identity theorem excludes accumulation. Thus |Re w| tends to
infinity cofinitely. Choose an injection e of the node set into N. At w
localize on radius |Re w|-1 with polynomial weight order floor(|Re w|),
to bound that seminorm by 2^(-e(w)). Every fixed strip and weight is then
dominated by this summable majorant outside finitely many nodes. The finite
head is already in S. Hence H=sum_w F_w*L_w is entire and belongs to S.
Locally uniform convergence passes to every derivative, giving precisely
the full prescribed germs at all nodes. No separation or multiplicity bound
on the nodes is used, and the empty and finite node cases are included.

Since 1-xi*H vanishes through every D-order, entire analytic division gives
U=(1-xi*H)/D. On each strip D is bounded away from zero outside a compact
rectangle. There U-1=(-M_b-xi*H)/D is rapidly decreasing; continuity handles
the compact rectangle. Thus U-1 is in S and reconstructs an actual h.
The identity (1+M_b)(1+M_h)=1-xi*H makes the convolution error an actual
Poisson boundary by global Xi synthesis. Therefore I+C_h is a two-sided
inverse of I+C_b on the original Meyer quotient; fixed-source convolution
continuity pays the original topology.

For arbitrary g, choose a source b representing [g]-P_g[g], using the
existing complete finite causal projector. Full Hasse multiplication
shows 1+M_b is nonzero at every Xi point: it is one on the resonant blocks
and 1+M_g on the complement. This supplies the preceding hypotheses
unconditionally. Its inverse agrees with 016's Hilbert inverse by faithful
source comparison and uniqueness. This is an original-source inverse
construction, not another assumed admission condition.

Paper attacks: unrestricted interpolation was insufficient; strip geometry
now supplies weighted convergence. Jet multiplicities are retained. Radius
and weight cutoffs depend on horizontal escape, not on an arbitrary
enumeration. No inverse-preservation premise, zero-confinement premise or
uniform source regularity estimate is assumed. The main construction is
unconditional for every original g. The result acts on literal original
cohomology; it does not assert invertibility on the prequotient source space.
The Xi divisor itself does not escape horizontally, so arbitrary infinite
Xi-packet admission does not follow from this interpolation theorem.

## Formal progress

Direct `lake --old env lean -o ...` audits passed, with no heartbeat changes:

- `DeningerMeyerStripJetLocalization`: original finite germ and bounded
  exponential full-jet localizer.
- `DeningerMeyerStripCardinal`: full denominator multiplicities and arbitrary
  smallness in a chosen weighted strip seminorm.
- `DeningerMeyerStripSeries`: all-strip weighted convergence and every jet's
  locally uniform passage to the limit.
- `DeningerMeyerHorizontalInterpolation`: arbitrary full germs on horizontally
  escaping divisors, without separation or multiplicity constraints.
- `DeningerMeyerUnitZeroGeometry`: every unitized source has that geometry.
- `DeningerMeyerStripBezout`: inverse correction and Bezout coefficient are
  both in the original all-weight Mellin class.

The formal construction improves the paper bookkeeping: localize every
node on radius |Re w|-1 with weight floor(|Re w|). Negative radii impose no
condition, so no exceptional-node branch is needed. Both cutoffs are
cofinal. The repair source is selected directly from the class
[g]-P_g[g], avoiding an auxiliary projection kernel.

Direct audits also passed for `DeningerMeyerConvolutionRepairSource`,
`DeningerMeyerConvolutionInverseSource` and
`DeningerMeyerOriginalConvolutionInverse`: the unconditional inverse is an
actual source convolution; the literal original quotient has a continuous
repair automorphism, and the exact finite compatibility reduction now holds
there. `PaperThetaConvolutionFredholm` also passed its direct audit. It
combines RN's faithful finite native spatial comparison and full-jet range
classification with the new source-preserving inverse to construct compact
absolutely continuous native solutions for arbitrary source symbols.
## Final audit

All ten leaves passed direct foreground `lake --old env lean -o ...`
audits, one owned Lean process at a time. All 51 public declarations passed
`#print axioms` in `/tmp`: only `propext`, `Classical.choice`, `Quot.sound`.
The combined final API/axiom audit exited zero. An earlier API-only harness
used unconstrained polymorphic `have` declarations; replacing those checks
by `#check @Name` resolved the harness universe errors. The mathematical
axiom output was standard in both runs.

All ten imports are unique in `RHTower.lean`, every new compiled artifact is
newer than its source, and no admitted proof, added axiom, opaque/unsafe
declaration, native computation or heartbeat increase occurs in these leaves.
No full or umbrella build, numerical experiment, web search, subagent,
external novelty check, commit or push was used. Index generation passed.

Global `scripts/formal_tools.py lint` reports only three concurrent unrelated
missing umbrella imports, preserved rather than wiring unverified work:

- `GaloisForLFunctions.RHTower.CHMDArchMomentPullback`
- `GaloisForLFunctions.RHTower.CHMDOperatorCutoffForm`
- `GaloisForLFunctions.RHTower.CHMDPrimeWindowTail`

No lint error names a module from this contribution. Existing large-file
warnings remain. All 17 owned scratch files were removed by exact path:
nine search JSON files, four exploratory API files, the final axiom/API file
and three logs.

## Scope and next frontier

The removed obstacle was preservation of the original Frechet image by the
general repaired inverse. The construction is a full source-class Bezout
producer, not an inverse-preservation premise or a numerical bound. The
critical distinction is horizontal escape of denominator zeros; arbitrary
Xi-packet interpolation remains unavailable. General prequotient source
inversion, arbitrary infinite native spatial synthesis, identification of
the arithmetic sharp with the Hilbert adjoint, geometric cup/trace
identification, positive Hodge compatibility and directed RN work sign are
not proved here. Routine holomorphic-calculus consequences of this inversion
must not be counted as a new contribution.
