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

The actual theorem `sourceCone_bezout_of_defect_le` uses the opposite bound `defect ≤ Φ`, together with Hodge index. The overview of `SourceDeterminantalSectionsAndArithmeticRiemannRoch` incorrectly describes this direction in its first numbered item. Audit the consequences before correcting prose.

## Conjecture loop

1. **Boundary rigidity.** For a nonnegative fibre-invariant source functional, RR and Bézout together force `Φ(x) = defect(x,x)` pointwise. Test this by translating each primitive source to the exact determinantal boundary `2 deg_H deg_V = Φ`.
2. **Linear degree limitation.** Fibre degrees alone do not see primitive negative-square directions. Identify the exact positive survivor: all degree-linear tests determine only the fibre quadrant, while Bézout requires the source boundary.
3. **Further source construction.** Use the rigidity result to test candidate source section theories, principal divisors, and payment cohomology; do not stop at the negative result.
4. **Full Bézout classification.** For nonnegative even fibre-invariant `Φ`, conjecture
   `Bezout(EΦ) ↔ ∀x y, δ(x,y)²≤Φ(x)Φ(y)`. Necessity uses balanced fibre lifts with
   degrees `sqrt(Φ(x)/2)` and the two source signs; sufficiency is hyperbolic AM–GM.
   This would identify the exact source contraction obligation without assuming Hodge index.
5. **No finite L² reserve at any aperture.** Strengthen the half-coercivity counterexample:
   the Weil Rayleigh quotient is unbounded above on `realTestsAt r` for every `r>0`.
   For arbitrarily large auxiliary aperture `A≥r`, impose the finite low grid of `A`
   and pole conditions on tests supported in `[-r,r]`. Finite-dimensional linear
   constraints leave a nonzero test by the translated-bump construction already used
   in `exists_ne_zero_mem_lowBlindTests`. The existing coercive estimate then gives
   `W(f,f)/∫f²≥lowBlindCoercivity(A)`, which grows without bound. This proves failure
   of Bézout for every finite constant `c`, not just for a strict known lower floor.
6. **Signed reserves do not evade rigidity.** Prove that Bézout on a graded source cone
   itself forces `Φ≥0`, without assuming `Φ(0)=0`. Then RR and Bézout on the graded cone
   are equivalent to exact representation of the nonnegative defect.

## Open obligations

- An original-surface, all-aperture source section theory with RR supply and an independently proved Bézout/degree mechanism remains unproved.
- The proposed payment cohomology must have genuine additive/dimensional content; a Boolean rank encoding of a quadratic inequality does not discharge that obligation.
- Preserve unrelated work already present in this worktree.

## Boundary-rigidity paper proof

[PROVED HERE, paper; core and low-blind application modules compile; axiom audit pending.]
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

[PROVED HERE, paper; Lean draft written.] At each `r>0`, prescribe zeros at the pole and
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

[PROVED HERE, paper; Lean draft written.] Suppose `Φ(x)<0`. Set
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
such kernel. The extension is not yet Lean-certified.

### Numerical-equivalence conjecture and paper proof

[PROVED HERE, paper; Lean implementation pending.] The literal real scaling pairing is
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

## Related ongoing work

The independent `biarithmetic-geometry-foundations` card audits the proposed ordinary
dimension identity `h⁰-h¹=E(s)` and its weighted arithmetic replacement. It already records
the nonintegrality obstruction below the first prime. Avoid duplicating that work; use its
finished theorem when available. This obstruction does not itself construct the requested
payment sheaf or prove duality.

## Log

- 2026-10-25 — Read attachment and full review; discovered existing all-aperture RR results and the opposite inequalities governing RR versus Bézout. Began boundary-rigidity audit.
