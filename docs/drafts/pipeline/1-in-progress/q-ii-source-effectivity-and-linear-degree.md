# Q-II: source effectivity, Riemann–Roch, and linear degree

- **ID:** q-ii-source-effectivity-and-linear-degree
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/review-2410/opus.md, Q-II and Mechanism B
- **Statement:** Determine a source-defined cone on the original scaling surface satisfying Riemann–Roch at every aperture, and determine whether its Bézout axiom follows from an independent linear degree law.

## Goal

Answer Q-II in full; formalize the answer and its corollaries without extra analytic assumptions, and apply results across the existing programmes. A reformulation of RH, a compensated pairing, a restricted test space, or a degree-positive cone without Bézout does not complete this goal.

## Gates

- [x] Read the full review and inspect the current source frontier.
- [x] Search the Lean corpus before mathlib.
- [ ] Dependency-closed paper proof of the full answer.
- [ ] Lean proofs, individual foreground `lake --old env lean` audits, and transitive axiom checks.
- [ ] Umbrella imports and applications to relevant existing programmes.

## Current evidence

Existing `AllApertureSourceRiemannRochAndCoercivityLaws` proves all-aperture RR for graded cones with negative reserves, and RR on compensated surfaces. Neither provides the requested cone with an independent Bézout law on the original surface. The existing nonnegative source-cone theorem identifies RR with the lower bound `Φ ≤ defect`.

The actual theorem `sourceCone_bezout_of_defect_le` uses the opposite bound `defect ≤ Φ`, together with Hodge index. Corrected the overview's reversed inequality and its unsupported Bézout claims for coercive mass cones; the Lean statements were unchanged.

## Conjecture loop

1. **Boundary rigidity.** For a nonnegative fibre-invariant source functional, RR and Bézout together force `Φ(x) = defect(x,x)` pointwise. Test this by translating each primitive source to the exact determinantal boundary `2 deg_H deg_V = Φ`.
2. **Linear degree limitation.** Fibre degrees alone do not see primitive negative-square directions. Identify the exact positive survivor: all degree-linear tests determine only the fibre quadrant, while Bézout requires the source boundary.
3. **Further source construction.** Use the rigidity result to test candidate source section theories, principal divisors, and payment cohomology; do not stop at the negative result.
4. **Full Bézout classification.** For nonnegative even fibre-invariant `Φ`, conjecture
   `Bezout(EΦ) ↔ ∀x y, δ(x,y)²≤Φ(x)Φ(y)`. Necessity uses balanced fibre lifts with
   degrees `sqrt(Φ(x)/2)` and the two source signs; sufficiency is hyperbolic AM–GM.
   This would identify the exact source contraction obligation without assuming Hodge index.
5. **No finite L² reserve at any aperture.** The Weil Rayleigh quotient is unbounded above
   on `realTestsAt r` for every `r>0`, even in every finite-dimensional reading kernel.
   Use an energy-dependent low grid within the fixed support aperture, together with
   the pole condition. The concentration and grid bounds force the contradiction `π≤1`
   if a mass-normalized energy ceiling holds. This proves failure of Bézout for every
   finite constant `c`, not just for a strict known lower floor.
6. **Signed reserves do not evade rigidity.** Prove that Bézout on a graded source cone
   itself forces `Φ≥0`, without assuming `Φ(0)=0`. Then RR and Bézout on the graded cone
   are equivalent to exact representation of the nonnegative defect.

## Open obligations

- An original-surface, all-aperture source section theory with RR supply and an independently proved Bézout/degree mechanism remains unproved.
- The proposed payment cohomology must have genuine additive/dimensional content; a Boolean rank encoding of a quadratic inequality does not discharge that obligation.
- Preserve unrelated work already present in this worktree.

## Boundary-rigidity paper proof

[PROVED HERE, paper and Lean; core and low-blind modules compile; transitive axiom audit clean.]
Write `δ(x,y)=polar(x,y)-pair(x,y)`.
Let `Φ` be nonnegative, even, and unchanged by adding either fibre. The source cone is
`EΦ={x: deg_H(x)≥0, deg_V(x)≥0, Φ(x)≤2 deg_H(x)deg_V(x)}`.

For any source `x`, translate its fibres to degrees `(Φ(x),1/2)`. This keeps both `Φ` and `δ`
unchanged and produces a member `y` of `EΦ` with `y²=Φ(x)-δ(x,x)`. Hence Bézout forces
`δ≤Φ`. Existing RR classification gives `Φ≤δ`. Both axioms therefore force `Φ=δ`.
Conversely exact equality and nonnegativity give Hodge index, RR, and Bézout by the existing
polar-surface theorems. The resulting cone is exactly the positive cone.

The strict cone has the same rigidity: when `Φ(x)<δ(x,x)`, put its polar capacity strictly
between these two values. The resulting class lies strictly inside the source cone but has
negative square. Thus removing the boundary cannot repair Bézout.

The full mixed classification is also proved on paper: Bézout is equivalent to
`δ(x,y)²≤Φ(x)Φ(y)` for all source pairs. For necessity lift `x,y,-y` to balanced degrees
`sqrt(Φ(x)/2)` and `sqrt(Φ(y)/2)`. Bézout bounds `δ(x,y)` above and below by
`sqrt(Φ(x)Φ(y))`. For sufficiency, hyperbolic AM–GM bounds the mixed polar capacity
below by the geometric mean of the two self capacities. No Hodge-index premise is
needed for this classification.

All fibre-linear degrees are nonnegative on every `EΦ`, irrespective of the defect. With
`Φ=0`, Bézout holds exactly when `δ` vanishes identically: both `prim(x)` and `-prim(x)`
belong to this cone, so their self and mixed intersections force `δ(x,x)=0`. Conversely
zero defect leaves just the nonnegative hyperbolic pairing in the fibre quadrant.

For `Φ=c∫f²`, the simultaneous RR/Bézout criterion is the exact identity `W(f,f)=c∫f²`
on the entire source subspace, not a lower bound. A concrete counterexample family uses
the existing `lowBlindTests a` at every `a>0`: choose `c=lowBlindCoercivity(a)/2`.
RR and ampleness hold by the proved coercive floor, while a nonzero test has strictly
greater Weil energy and supplies the strict negative-square cycle above. This is an
unconditional example on the original, uncompensated subsurface.

### Unbounded-energy strengthening

[PROVED HERE, paper and Lean; module compiles; transitive axiom audit clean.] At each `r>0`, prescribe zeros at the pole and
the finite grid `lowGridOf (horizonFreqEps r (max M 0)) r`. A nonzero real test with this
support and these zeros exists: take `2k+1` independent translates of a bump against
`k` complex conditions. If its Weil energy were at most `max(M,0)∫f²`, the proved
near-radical concentration law would give `π∫f²≤bandMass`. The grid bound gives
`bandMass≤∫f²`, a contradiction since `π>1` and `∫f²>0`. Thus the Rayleigh quotient
exceeds every `M` at every positive aperture. The energy-dependent grid avoids enlarging
the support aperture. Any additional finite set of transform zeros can be imposed.

Consequences: every finite `c∈ℝ` fails Bézout on `l2SourceCone c`, its strict interior,
and `gradedL2SourceCone c` over `realTestsAt r`. The all-aperture negative Chebyshev
reserve is an unconditional RR cone that unconditionally fails Bézout. This refutes
the review's inference from existence of some RR/Bézout cone to equivalence between RH
and Bézout on an arbitrary chosen RR cone.

More generally, no postprocessing `F(samples(f))` of a finite set of transform samples
defines a Bézout source cone. On the finite-blind source fibre its reserve is the constant
`F(0)`, whereas scaling a positive-energy blind test makes its Weil energy arbitrarily large.
Lift such a test to polar capacity `max(F(0),0)`. It is source-effective and has negative
square. This also excludes arbitrary offsets and the normalized reading
`F(samples(f))-F(0)`. The positive survivor is unbounded Weil energy even after finitely
many prescribed transform zeros, not merely failure of one proposed cone.

### Signed-source rigidity

[PROVED HERE, paper and Lean; module compiles; transitive axiom audit clean.] Suppose `Φ(x)<0`. Set
`p=√(-Φ(x)/2)>0` and lift `x` to fibre degrees `(p,-p)`. Its ample degree is zero
and its polar capacity equals `Φ(x)`, so it belongs to the graded source cone.
Let `c=2+max(Φ(0),0)`. The pure-fibre lift of zero with degrees `(c,1)` also belongs
to the cone: its ample degree is positive and its polar capacity `2c` pays `Φ(0)`.
Their defect is zero, and their intersection is `p(1-c)<0`. Thus graded Bézout
forces `Φ≥0`; normalization at zero is unnecessary.

Consequently, for every even fibre-invariant real-valued source functional, graded
Bézout is exactly nonnegativity plus the mixed contraction law. Graded RR and Bézout
together are exactly `0≤Φ=δ`. A negative reserve supplies unconditional RR but cannot
repair Bézout. This gives the sharp positive replacement for the signed-reserve route.

### Section-count application

[PROVED HERE, paper; Lean draft written.] The AOT `1×1` source obstruction matrix has
`sourceH0∈{0,1}` and defines exactly `sourceCone`. The boundary classification therefore
transfers unchanged. Moreover, for every additive constant `M`, pure-fibre degrees `(c,1)`
with `c=2+max(Φ(0),0)+max(M,0)` give a source-effective class with
`sourceH0(x)+M<x²=2c`. Thus the Boolean membership count cannot provide a surface RR
dimension-growth estimate. This does not invalidate its existing role as a cone encoding.

### Principal-divisor direction

Corpus searches found the curve-side numerical radical classified by the Frobenius ideal
(`radical_iff_eq_frobPolyTest`), but no matching scaling-surface principal-divisor degree law.
Do not confuse the spectral vanishing radical with the kernel of every Weil pairing, or
use RH to identify them. An independently constructed motion relation must preserve the
intersection pairings needed by its degree argument; the necessary numerical-equivalence
bridge is still to be proved or refuted.

The broader corpus supplies a stronger lead: `RHTower.compactXiWeilPairing_left_radical_iff_zero`
in `RHTower/XiCompactPolarWeilRealization.lean` proves zero numerical radical on complex compact
polar tests unconditionally, using density in the absolute folded Xi divisor Hilbert space.
It is not merely the conditional positive-definiteness theorem in `InfiniteGenusLaw`.
Next obligation: extend the density argument to unrestricted compact source inputs and identify
its literal polarization with the real scaling `weilPair`. If successful, numerical equivalence
on the existing scaling cycle space is equality; genuine divisor movement must then occur on a
richer source space before passage to these numerical classes.

The finite-reading conjecture has a dependency-closed paper proof and Lean draft: Weil energy
is unbounded in the kernel of every linear map from `realTestsAt r` to a finite-dimensional
real space, not only finite Fourier sampling. The translated-bump kernel construction applies
jointly to the given map, the pole, and the energy-dependent grid. This excludes arbitrary
postprocessing of finitely many linear observations (values, moments, nodes, or transform
samples) as a Bézout source reserve. The exact survivor is unbounded Rayleigh quotient in every
such kernel. The full generalized module compiles; its transitive axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

### Numerical-equivalence conjecture and paper proof

[PROVED HERE, paper; Lean draft written.] The literal real scaling pairing is
nondegenerate, without RH. Its proof uses the existing compact-polar density theorem:

1. A compact complex `C²` source has a square-summable Xi evaluation vector. Critical-line
   reflection is an isometry, and its reflected vector belongs to the folded divisor Hilbert
   space. Compact polar tests are dense in that space.
2. If its Weil pairing against every compact polar test vanishes, the reflected vector is
   orthogonal to a dense subspace containing itself. Its norm is zero. Injectivity of compact
   Xi evaluation then makes the source zero. The tested source need not itself satisfy the
   pole constraints; only the testing family does.
3. The Xi-copy polarization equals the zeta-carrier Weil pairing by the explicit
   `xiDivisorZetaCarrierEquiv` and its multiplicity identity. Absolute summability follows from
   the two square-summable evaluation vectors. This bridge retains the full complex mixed form.
4. For real compact sources the full mixed Weil pairing is real: the convolution is real and
   `WeilWorkPBAP.weilFullFunctional_ofReal_im` applies. A real source annihilating every real
   compact test therefore annihilates the real and imaginary parts of every complex compact
   test. Step 2 makes it zero.
5. A scaling cycle annihilating every cycle has both fibre degrees zero. Pairing it with pure
   test cycles then annihilates its real source, so step 4 makes that source zero. Its two
   remaining pole coefficients are zero as well.

Thus equality of all intersection readings is equality of the existing scaling cycles.
Any intersection-preserving translation in this cycle space is trivial. This is a necessary
scope restriction for a principal-divisor construction, not a proof that richer divisor
presentations cannot exist. The positive survivor is unconditional separation of every
scaling class by the intersection pairing, plus separation by compact polar tests on the
source side. The bridge and dependency audit must be formalized before this route is closed.

The mixed defect radical is consequently exactly the fibre plane: a cycle annihilates every
source defect pairing precisely when its compact source is zero. Combining this with the
primitive-faithfulness criterion gives an exact AOT application on the full scaling surface:
for any fibre-invariant reserve, section-cone ampleness is equivalent to strict positivity
of the reserve on every nonzero compact source. The bridge and this corollary are drafted.

### Primitive faithfulness and ampleness

[PROVED HERE, paper; Lean implementation pending.] For any fibre-invariant reserve `Φ`,
ampleness of the nonnegative-fibre source cone is equivalent to the exact condition
`Φ(x)≤0 ⇒ δ(x,y)=0 for every y`. Necessity follows by translating `x` and `y` to zero
fibre degrees: the first lift is effective with ample degree zero, and their intersection
is `-δ(x,y)`. Conversely, an effective class of ample degree zero has both fibre degrees
zero. Its reserve is nonpositive, so the stated condition kills its defect and hence every
intersection. No evenness or nonnegativity premise is needed for this classification.

Consequently, a normalized reserve `F(Lf)-F(0)` from any finite-dimensional linear reading
fails ampleness at every positive aperture. The unbounded-energy theorem supplies a source
in `ker L` with positive Weil energy; its zero-degree lift is effective and not numerically
trivial. Together with the preceding Bézout obstruction, this excludes both required
intersection axioms for every such normalized finite reading. An arbitrary positive offset
may remove the ampleness obstruction, so the normalization is essential to this conclusion.
Strict source cones have positive ample degree and satisfy the stated ampleness axiom
vacuously; they remain subject to the independently proved Bézout obstruction.

### Exact arithmetic source cone at every aperture

[PROVED HERE, paper; Lean implementation pending.] The existing literal box-node identity
identifies `chebyshevSourceEnergy r R` with the diagonal defect on the odd source surface for
every `0<r<R`. Use this exact arithmetic reserve in the **graded** source cone. Its defining
formula refers only to fibre degrees, the archimedean gauge, and the Chebyshev/node-correlation
source. The cone equals the closed positive cone as a proved theorem, so it has RR at every
aperture without an aperture-dependent loss. Unlike the negative finite-mass reserve, its
Bézout condition is exactly the corresponding Hodge-index condition. Its ampleness condition
has the same equivalence. Over every positive aperture, either condition is equivalent to RH
by the existing odd-source exhaustion theorem.

This supplies an exact arithmetic presentation of the RR cone, but no independent positivity
mechanism: the required nonnegativity is the unresolved source-payment inequality itself.
The original nonnegative-fibre `chebyshevSectionCone` requires that inequality even for RR;
the graded cone moves it into Bézout/ampleness. This distinction corrects the review's
existential-cone inference without claiming that a renamed exact identity forces its sign.

The all-parity critical-deficit identity gives the same construction on **every**
`realTestsAt r`, not only the odd sector. Its reserve is
`(gammaBracket(0)-2)∫f² + biScaleLevyEnergy(f) + 4 horizonEnergy(f)` plus
`2∫_[0,2r] ccmPrimeDeficitIncoming(t) doubleGaugeDerivative(autocorr(f))(t) dt`.
Every term is an explicit arithmetic or archimedean source reading; the existing exact
identity proves equality to the defect without a sign premise. The graded cone therefore
has unconditional RR, while Bézout and ampleness are exactly source nonnegativity. This is
an exact all-parity presentation of the desired RR supply, not an independent proof of
positivity or the missing sheaf duality.

The exact arithmetic reserve cannot factor through any finite-dimensional linear reading,
even with arbitrary nonlinear postprocessing: such a factorization would make its value
constant on that reading's kernel, contradicting the proved unbounded Weil energy there.
The Lean draft includes this irreducibility statement and the all-aperture RH dictionaries.

### Arbitrary finite degree descriptions

[PROVED HERE, paper; Lean implementation pending.] Strengthen the source-reserve obstruction:
at every positive aperture, **every fibre of every finite-dimensional linear reading of
the entire scaling cycle space has self-intersection unbounded below**. Consequently no
nonempty effective set whose membership is determined by finitely many linear degrees
can satisfy Bézout, even with arbitrary nonlinear postprocessing of those degrees.

For a reading `L` of scaling cycles, impose jointly on a compact source `f` the conditions
`L(0,0,f)=0`, `pair((0,0,f),H)=0`, and `pair((0,0,f),V)=0`. The finite-kernel energy theorem
supplies such an `f` with positive Weil energy. Its source cycle `p` lies in `ker L` and
has `p²=-W(f,f)<0`. Given any `x` and target `M`, put
`t²=(max(x²-M,0)+1)/(-p²)`. The average of `(x+tp)²` and `(x-tp)²` is
`x²+t²p²<M`; at least one is below `M`, and both retain `L(x)`. Any nonempty union of
reading fibres therefore contains negative-square classes and fails Bézout on self-pairs.

This conclusion does not exclude infinitely many degree inequalities or a degree law on a
richer divisor presentation. Its positive survivor is the exact affine-fibre unboundedness
law, stronger than failure of any one finite-rank reserve or finite polyhedral cone.

## Next source questions

- [PROVED HERE, paper; Lean draft written.] Glue the exact all-parity source cones over aperture into a source-defined subset of the
  original `ScalingCycle` space, using compact-support exhaustion. Its equality to the global
  positive cone follows from the exact arithmetic formula. Audit the precise remaining
  Hecke/Adams stability obligation using `scalingSurface_adams_riemannRoch_iff`: stability
  at one scale greater than one, together with RR and nonnegative ample degree, already
  forces Hodge index. Thus the new RR supply must not be described as an independently
  proved motion-compatible effective theory.
- After the numerical bridge compiles, test the proposed Hecke principal differences.
  `scalingAction t` translates the compact source and rescales the two raw pole coordinates.
  For `t≠0`, compact translation rigidity should force every fixed scaling cycle to be zero.
  Combined with numerical nondegeneracy, no nonzero such difference is a principal numerical
  relation within the compact cycle space. A richer representative carrier remains necessary.

### Scaling and Hecke fixed classes

[PROVED HERE, paper; Lean draft written.] The corpus already proves that a compact
source satisfying `f(u)=c f(u+t)` at any nonzero lag is zero. Hence every eigenvector of
`scalingAction t`, for `t≠0`, lies in the fibre plane. Its coordinates obey exactly
`(exp(t/2)-c)a=0` and `(exp(-t/2)-c)b=0`. In particular its fixed space is zero.
For positive `q≠1`, the normalized Adams fixed space is therefore zero. The unnormalized
Hecke operator fixes exactly the vertical fibre line: its source must vanish, its horizontal
raw coordinate scales by `q`, and `heckeCorrespondence_V` supplies the converse.

With numerical nondegeneracy, these are also the exact numerically fixed spaces. Thus
nontrivial compact Hecke or Adams motion cannot be mistaken for principal numerical
equivalence. This distinguishes an isometry acting simultaneously on both intersection
arguments from a principal move preserving every reading with the other argument fixed.

## Verification queue

### Removing source symmetry

[PROVED HERE, paper; Lean implementation pending.] Evenness of the reserve is unnecessary
for the RR classification. For every fibre-invariant real reserve, graded RR is equivalent
to `Φ(x)≤δ(x,x)` for every source. For necessity, if `δ(x,x)<Φ(x)`, choose a polar
capacity `c` strictly between them and fibre degrees `b=|c|+1`, `a=c/(2b)`.
Then `2ab=c` and `a+b>0`. The resulting lift has positive square but is not effective;
its negative has negative ample degree and is also not effective. For sufficiency, apply
the source bound to whichever of `x` and `-x` has nonnegative ample degree. No comparison
between the two reserve values is used.

Nonnegative-fibre closed and strict cones only see `Φ₊=max(Φ,0)`, since their polar
capacity is nonnegative (strictly positive in the strict cone). Their RR condition is
therefore exactly `Φ₊≤δ`. Both RR and Bézout hold exactly when `Φ₊=δ`; for graded cones,
both hold exactly when `0≤Φ=δ`. These statements impose neither source evenness nor an
initial sign premise. Negative reserves on zero-defect sources are invisible to the
nonnegative-fibre construction, but graded Bézout excludes them.

For Bézout alone the corresponding asymmetric mixed law is
`max(δ(x,y),0)²≤Φ₊(x)Φ₊(y)` for all sources. Balanced boundary lifts give necessity;
hyperbolic AM–GM gives sufficiency. Only when the reserve is even can this law be replaced
by the symmetric square bound `δ(x,y)²≤Φ(x)Φ(y)`. This identifies exactly where symmetry
was used in the earlier classification. Formalization must retain this distinction.

| Module | Status |
|---|---|
| ACS `SourceConeBoundaryRigidity` | Compiled; main transitive axiom endpoints clean. |
| ACS `SourceConeBoundaryApplications` | Compiled; main transitive axiom endpoint clean. |
| ACS `WeilEnergyIsUnboundedAtEveryAperture` | Compiled; generalized finite-kernel and no-go endpoints axiom-clean. |
| ACS `GradedSourceConeBoundaryRigidity` | Compiled; RR/Bézout endpoint axiom-clean; umbrella wired. |
| ACS `SourceConePrimitiveFaithfulness` | Olean compilation passed; transitive axiom audit pending. |
| ACS `NumericalEquivalenceOnTheScalingSurface` | First compile exposed implicit-function elaboration timeouts and integral/name errors. Proof split into smaller lemmas with explicit functions and a real integral type. Revised olean compilation running; no concurrent Lean process permitted. |
| ACS `HeckeClassesDoNotMoveNumerically` | Draft; needs numerical-equivalence olean, then compile and audit. |
| ACS `FiniteDegreeConesCannotSatisfyBezout` | Draft; compile and transitive audit pending. |
| ACS `ExactArithmeticSourceEffectivity` | Draft; compile and transitive audit pending. |
| AOT `SourceSectionBoundaryRigidity` | Draft; needs numerical-equivalence olean, then compile and audit. |
| AOT `AllApertureChebyshevSourceEffectivity` | Draft; needs preceding AOT olean, then compile and audit. |

The `/tmp/QIIBoundaryAudit.lean` run printed clean axiom lists but exited nonzero because a
scratch `#check` incorrectly qualified the global name `integral_complex_ofReal`. That scratch
name is corrected; no theorem failed. `/tmp/QIINumericalNames.lean` passed with the global
integral lemma and the exp/log names. Final plain Lean audits, remaining
umbrella imports, and the finite-degree failed-route closure are still pending.

## Related ongoing work

The independent `biarithmetic-geometry-foundations` card audits the proposed ordinary
dimension identity `h⁰-h¹=E(s)` and its weighted arithmetic replacement. It already records
the nonintegrality obstruction below the first prime. Avoid duplicating that work; use its
finished theorem when available. This obstruction does not itself construct the requested
payment sheaf or prove duality.

## Log

- 2026-10-25 — Read attachment and full review; discovered existing all-aperture RR results and the opposite inequalities governing RR versus Bézout. Began boundary-rigidity audit.
