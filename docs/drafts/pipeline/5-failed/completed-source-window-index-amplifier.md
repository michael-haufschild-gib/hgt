# Completed-source window index amplifier

- **ID:** `completed-source-window-index-amplifier`
- **Stage:** 5-failed
- **Type:** `[RETIRED: NO INDEPENDENT SOURCE PRODUCER]`
- **Source:** Route D verified-height amplification; finite-place quasi-inner local-factor products;
  semilocal Sonin/prolate source geometry
- **Statement:** `[FALSIFIED AS A ROUTE-D CONSTRUCTION]` Every audited realization of the proposed
  completed-source window index either collapses, splits, is nonclosable off RH, is not height
  local, or becomes an exact reader of the unknown free-orbit count.  A relative source homotopy
  estimate would reopen the route, but no Route D object constructs it.

## Goal

Supply the missing **producer** for the already formalized Route D consumers. The theorem must yield
an explicit rational `U>H` from:

```text
the completed Euler--Gamma source
+ a certificate that every zero through H is fixed by FE--Schwarz reflection,
```

and prove

```text
N(U)-N(H) <= 1
```

or, equivalently for the proposed index, that no free reflection orbit enters `(H,U]`.

This card does not ask for another argument-principle identity, divisor-fed Krein form, or conditional
count interface. The source theorem is the existence and quantitative stability of the all-place
Fredholm object itself.

## Why an index is required

An off-line reflected pair can approach an allowed double critical-line zero with arbitrarily small
change in every bounded log-modulus or log-derivative reader below it. Thus a uniform scalar margin
decays at the collision. The free-orbit count does not: it remains an integer until the collision.

The repository already proves that:

- finite Euler data do not select the next reflection-orbit type;
- fixed-degree moment tests are height-limited;
- measured traces are blind to a finite off-line set;
- the standard one-prime Euler commutator with the Sonin projection is noncompact; and
- every nonzero finite additive combination of the canonical positive Euler corners remains
  noncompact in the Calkin quotient.

Therefore the source index cannot be finite, additive, continuously scalar-valued, or constructed
after expanding the Xi divisor.

## Finite-place source object `[SEARCH]`

For a finite set `F` of places containing the archimedean place, put

```text
u_F(s) = rho_infinity(s) * product_(p in F, p finite) rho_p(s),
rho_v(s) = gamma_v(s)/gamma_v(1-s).
```

On the critical line `u_F` is unimodular. Connes--Consani prove that it is quasi-inner for the
left-half-plane Hardy polarization:

```text
(1-P) M_(u_F) P is compact.
```

The archimedean factor is essential. No individual finite-prime ratio is quasi-inner. This is the
known multiplicative compensation that survives the repository's no-go for finite **additive**
Euler-metric corrections.

The finite-place theorem does not itself produce a finite index: the associated semilocal Sonin
kernel is infinite-dimensional. A height window and prolate or relative-resolvent regularization are
required before a Fredholm determinant or relative index can be defined.

Primary source: A. Connes and C. Consani, *Quasi-inner functions and local factors*,
[arXiv:2008.10974](https://arxiv.org/abs/2008.10974).

## Required all-place theorem `[OPEN CORE]`

For every compact positive-ordinate window `I=(H,U]`, construct from the finite-place system a
source-defined family

```text
A_(F,I) = 1 + K_(F,I)
```

on a fixed polarized Hilbert space, or a canonically equivalent relative pair, satisfying all of the
following.

1. **Window localization.** `A_(F,I)` depends on the height interval through the scaling/prolate
   spectral calculus, not through a list of zeros.
2. **Archimedean compensation.** Its finite-place off-diagonal defect is compact because the
   multiplicative local-factor product is used before compression.
3. **All-place convergence.** As `F` exhausts the primes, the relative family converges in a stated
   determinant-compatible ideal after the unique source-prescribed renormalization.
4. **Index identity.** Relative to the certified prefix, the Fredholm index changes by one unit for
   each free FE--Schwarz orbit and is unchanged by a fixed critical-line orbit.
5. **Quantitative tail stability.** For one explicit rational `U>H`, the all-place tail satisfies a
   source-side norm estimate strictly below the index-stability threshold, for example

   ```text
   ||A_(infinity,I)-A_(F,I)||_1 < 1
   ```

   in a normalization for which the finite reference index is zero.
6. **No divisor input.** Neither the renormalization nor the norm estimate may be defined using the
   unknown zero divisor, an RH-equivalent Herglotz hypothesis, or a new zero enumeration.

Items 1--4 define the source index. Item 5 is the actual verified-height amplifier. Omitting item 5
produces only another exact RH encoding.

## Candidate realizations

### A. Semilocal prolate relative resolvent `[LEADING CANDIDATE]`

Use the source cyclic pairs and their formal semilocal prolate operators. The normalized first Jacobi
coefficient has a proved strict all-finite-place contraction, so the place-naturality defect has a
nonzero positive degree-two-to-degree-zero matrix coefficient. Two-sided resolvent smoothing is the
first plausible way to turn that unbounded-core defect into a trace-class relative operator.

The first unresolved statement is not positivity. It is analytic closure and Schatten membership of
the exact Sonin-compressed relative resolvent. The second is whether its determinant boundary has the
required free-orbit index rather than a removable vertexwise coboundary.

### B. Hardy quasi-inner mapping telescope `[SECONDARY CANDIDATE]`

Use the inductive system of semilocal Sonin kernels associated with `u_F`. The all-place object would
be a topological derived-limit defect: the completed product is formally trivial by the functional
equation, while the finite-place kernels do not disappear. A windowed mapping telescope could carry
the missing integer as an Euler characteristic.

This candidate is viable only if the windowed transition maps lie in a nuclear or determinant class.
Algebraic filtered-colimit exactness alone is blind to the topological anomaly and cannot produce a
zero count.

## Attacks already survived or failed

- `[FAILED]` A positive safe-line Poisson or Herglotz reader is too coarse. Positivity in a strip
  imposes a Harnack resolution scale comparable with the distance to the strip boundary; reaching
  the critical Euler line requires the very cancellation being sought.
- `[FAILED]` Local Laguerre, Pick, de Branges, or all-order Hankel positivity is a target-side RH
  criterion unless an independent source factorization is proved.
- `[FAILED]` Uniform self-recurrence or minimal-counterexample descent imports an RH-equivalent
  recurrence uniformity and does not force a lower zero.
- `[FAILED IN LEAN]` One-prime and finite additive Euler Fredholm repairs have noncompact source
  seams.
- `[FAILED]` A continuous normal prime-clock intertwiner vanishes identically; a viable sector
  witness must be on-shell or derived.
- `[SEARCH, INSUFFICIENT]` Finite-place quasi-innerness supplies compactness but not a windowed
  finite index or an all-place determinant limit.

## First paper subclaims

The leading candidate decomposes into four independently falsifiable analytic statements.

1. **Closed prolate realization.** Construct self-adjoint or closed realizations of the finite-place
   operators on a common source-defined core and prove domain compatibility under place transition.
2. **Two-resolvent Schatten lemma.** Prove that the sandwiched naturality defect is trace class from
   explicit resolvent ideal bounds; abstract `S_2 * bounded * S_2 subset S_1` is insufficient until
   the concrete resolvents and defect are controlled.
3. **Nonzero determinant boundary.** Show that the proved low-mode residue survives exact Sonin
   compression and is not killed by the admissible gauge group.
4. **Window index comparison.** Identify the determinant winding with the free-orbit increment and
   derive an explicit source-only `<1` tail bound on a post-certificate window.

Failure of subclaim 1 or 2 kills the prolate realization. Failure of subclaim 3 reduces the source
defect to a coboundary. Failure of subclaim 4 leaves a source operator with no Route D consequence.

## Gates

- [x] 0 -> 1: source object, integer target, finite-place parent theorem, no-go classes, and exact
  analytic subclaims identified
- [ ] 1 -> 2: construct the all-place window family and prove the determinant-compatible tail bound
- [ ] 2 -> 3: formalize the source construction, index identity, quantitative bound, and composition
  with the existing verified-height consumer
- [ ] 3 -> 4: independent proof and literature audit, unconditional Lean endpoint, and explicit
  verified-height improvement

## Current verdict

`[OPEN CORE]` The missing Route D source theorem is an **archimedean-compensated, all-place,
windowed index-stability theorem**. Positive scalar readers and finite source summaries cannot carry
the collision-stable integer. Finite multiplicative quasi-innerness is the correct source seed, but
the all-place trace-ideal limit and its quantitative first-window stability are unproved.

This card reopens Route D only at that source-producing level. Another conditional count, winding,
minimum-modulus interface, or divisor-fed index does not qualify.


## Conditional analytic spine `[PROVED; BRIDGE]`

The functional-analytic implication needed by the leading candidate is elementary once the concrete
source operators exist.  Recording it prevents the route from hiding its difficulty inside the word
"resolvent."

Let `A` and `B` be closed operators on Hilbert spaces `H_A,H_B`, let `J:H_B->H_A` be bounded, and
let `z` lie in both resolvent sets.  Suppose the core identity

```text
A J - J B = Omega
```

extends to a bounded operator `Omega:H_B->H_A`.  Writing `R_A=(A-z)^(-1)` and
`R_B=(B-z)^(-1)`, direct multiplication gives

```text
R_A J - J R_B = - R_A Omega R_B.                       (R)
```

Indeed `R_A(A-z)=1`, `(B-z)R_B=1`, and the two `zJ` terms cancel.  If `R_A` and `R_B`
are Hilbert--Schmidt, then `(R)` is trace class and the ideal inequality gives

```text
||R_A J - J R_B||_1
  <= ||R_A||_2 ||Omega|| ||R_B||_2.                     (S)
```

Thus the abstract Schatten step is closed.  The unresolved content is concrete: closed source
realizations, a bounded extension of `Omega`, Hilbert--Schmidt resolvents on the required window,
and a source estimate making the right side of `(S)` small enough.

There is also no hidden index argument after that estimate.  Let `K(z)` be a trace-class holomorphic
family on and inside a window contour and suppose

```text
sup_(z on boundary) ||K(z)||_1 < 1.
```

Then `||K(z)||<1` on the boundary, so `1+tK(z)` is invertible there for every `0<=t<=1` by the
Neumann series.  The Fredholm determinant loop `det(1+tK(z))` is therefore a homotopy in `C*` from
`det(1+K(z))` to the constant loop `1`; its boundary winding is zero.  An index identity of item 4
then excludes a free orbit in the window.

These lemmas are standard operator-ideal and analytic-Fredholm theory and are `[BRIDGE]`, not new
scientific knowledge.  They sharpen the missing source theorem to the estimate

```text
||R_A||_2 ||Omega|| ||R_B||_2 < 1                       (T)
```

for a correctly normalized, source-constructed all-place family, together with the proof that its
determinant winding is the free-orbit count.  Neither `(T)` nor that source/index identification is
currently proved.

## Ordinary all-place ratio collapse `[PROVED; BRIDGE; CLOSED CANDIDATE]`

The finite quasi-inner product cannot be promoted by taking an ordinary all-place multiplier.  With

```text
gamma_infinity(s)=pi^(-s/2)Gamma(s/2),
gamma_p(s)=(1-p^(-s))^(-1),
rho_v(s)=gamma_v(s)/gamma_v(1-s),
```

the completion-compatible meromorphic regularization is

```text
rho_infinity(s) product_p^reg rho_p(s)
 =rho_infinity(s) zeta(s)/zeta(1-s)
 =Lambda(s)/Lambda(1-s)
 =1.
```

The apparent `0/0` at a reflected zeta zero is removable in the total meromorphic ratio.  Hence its
multiplication operator is the identity, every off-diagonal Hardy corner is zero, and every ordinary
Fredholm index is zero.  The complete proof, including the absence of a nonempty open absolute-product
domain, is banked in
`../2-fully-proven/not_new_scientific_knowledge/completed-local-ratio-all-place-collapse.md`.

Consequences:

- `[CLOSED]` Candidate B cannot use the regularized all-place multiplication symbol itself.
- `[CLOSED]` A functorial window localization applied only after the product has become `1` is divisor
  blind.
- `[SURVIVES ONLY AS SECONDARY DATA]` The finite quasi-inner system can contribute only through the
  failure of its compressions to converge to the regularized symbol: a determinant-line,
  renormalization, or derived-limit anomaly.
- `[UNAFFECTED]` Candidate A is not literally the collapsed multiplier; its genuine semilocal grading
  deformation remains a distinct source object.  The new Route B theorem that this deformation is
  unbounded rules out bounded perturbation theory but not relative-form or two-resolvent control.

## Sharpened missing theorem `[CONJECTURE; OPEN CORE]`

The exact surviving source statement is now the following **completed-source renormalization-anomaly
free-orbit theorem**.

For every positive-ordinate window `I=(H,U]`, construct from a cofinal finite-place system a canonical
integer

```text
alpha_I(E;D_H) in Z,
```

where `E` is the completed Euler--Gamma source and `D_H` is the certified fixed divisor through `H`,
such that:

1. `alpha_I` is independent of the prime exhaustion and of every admissible local counterterm;
2. it is an excisive secondary invariant of the nonconvergence of the finite quasi-inner or semilocal
   compressions, and becomes zero if those compressions are replaced by the ordinary regularized
   multiplier `1`;
3. under the source-to-divisor boundary map, `alpha_I` equals the multiplicity of the
   reflection-anti-invariant principal-part space in `I`, equivalently the number of free
   FE--Schwarz orbits in the window;
4. fixed critical-line orbits, with arbitrary multiplicity, map to zero;
5. for one explicit rational `U>H`, a completed-source estimate proves `alpha_I=0` without evaluating
   a new zero, winding, or boundary value.

Items 1--2 are the missing construction theorem.  Items 3--4 are the missing equivariant index
identity.  Item 5 is the actual Route D amplifier.  This formulation is strictly narrower than the
original all-place Fredholm guess: an ordinary limit is now proved impossible, so the desired integer
must be a secondary obstruction class rather than the index of the completed local-ratio symbol.

## Anti-tautology gate for the secondary class `[PROVED BOUNDARY]`

The proposed anomaly cannot be an arbitrary secondary invariant.  Three existing exact results force
its category.

1. `completed-local-ratio-all-place-collapse.md` proves that every invariant factoring through the
   ordinary completed local-ratio multiplier sees only the identity symbol.
2. `prime-grade-monodromy-divisor-mobius-equivalence.md` proves that the complete prime-grade
   residue/monodromy field is mutually invertible with the zeta divisor.  An anomaly factoring through
   those residues is target-side divisor data, not a source proof.
3. `prime-euler-unit-tangent-completeness.md` proves that, after a zero and its multiplicity are fixed,
   finite Euler-unit changes have dense orbit in the compact-open regular completed-flux germ.  Hence
   no nonconstant continuous local-germ invariant survives that source gauge action.

Therefore `alpha_I` must be a non-residue, non-symbol, non-continuous **joint incidence pairing**

```text
(weighted arithmetic-at-infinity Euler tail, global symmetric divisor)
  -> windowed integer.
```

It must retain the weighted prime-power ray topology that disappears under analytic continuation to a
compact-open germ, while simultaneously using more than the principal-part/monodromy field that already
is the divisor.  Orbit parity, a sign-isotypic principal-part dimension, or closability of the canonical
residue graph supplies only the target reader and is not the missing theorem.

This leaves one concrete source construction problem rather than a family of operator slogans:
construct a canonical index pairing between the surviving arithmetic tail class and the global
reflection-graded divisor graph, then prove a source estimate that its free-orbit component vanishes on
one strict post-certificate window.  No such pairing or vanishing theorem is currently proved.

## Banach/Yoneda and residue-graph pairing collapse `[PROVED; CLOSED]`

The most literal joint coupling is now ruled out.  For the exact sequence

```text
0 -> M_0 -> M_log -> Q_log -> 0
```

and the unit class `u=[one]`, the pullback to the line `C u` splits through the distinguished lift
`one in M_log`.  Every pushout through a bounded scalar reader on `M_0` also splits because
Hahn--Banach extends the reader to `M_log`.  Hence the ordinary Banach-Yoneda product of the unit tail
with any bounded vanishing-tail reader is zero.

The canonical prime-shift residue functional is not a counterexample.  Its graph is closable exactly
when RH holds; on RH it is zero, and off RH it has no closed extension.  It therefore cannot serve as
an unconditional unbounded Fredholm, spectral-triple, or `KK` cycle.  Full proof:

`../2-fully-proven/not_new_scientific_knowledge/marcinkiewicz-tail-residue-yoneda-splitting.md`.

This closes the first precise realization of the proposed secondary anomaly.  In particular, a live
closed source operator cannot extend the canonical scalar residue graph on its whole algebraic domain:
any restriction of a closed operator is closable, contradicting the explicit off-RH nonclosability
sequence.

## Revised source-theorem boundary `[OPEN CORE]`

The missing theorem can no longer be an ordinary all-place multiplier, a prime-grade monodromy,
a continuous regular-germ invariant, a finite algebraic corona expression, a Banach extension class,
or the unbounded graph of the canonical residue reader.

A surviving source theorem must instead construct a **different closed family** before residues are
read, with all four properties:

1. its characteristic noninvertibility divisor is the completed Xi divisor;
2. its reflection-odd kernel/cokernel multiplicity is the free-orbit count, without extending
   `R_res` as a scalar graph functional;
3. its closedness, Fredholmness, and determinant ideal follow unconditionally from Euler--Gamma
   source geometry; and
4. a source-side spectral gap or norm estimate proves the reflection-odd multiplicity is zero on an
   explicit first window above the certified prefix.

This returns the live construction to the semilocal prolate/relative-resolvent type, or to an equally
strong new closed source geometry.  Route D can consume such a theorem immediately, but the tail
quotient by itself does not construct it.

## Lifted `K`-class gate `[PROVED; CLOSED]`

Changing from Banach extensions to ordinary or Real `K`-theory does not revive the unit-tail pairing.
In every unital extension, the connecting map vanishes on a quotient class that already lifts.  The
Euler unit class lifts by the actual unit field, and each critical boundary phase lifts by the bounded
unitary prime character `p |-> p^(-it)`.  Their connecting indices are therefore zero (equivariantly
as well whenever the lift respects the reflection structure).

A nonzero index must begin with a genuinely non-liftable joint symbol.  The source must construct that
non-liftability before its divisor is read; taking the unit tail or phase orbit and changing the
homology theory cannot manufacture it.

## Euler Pick node-window collapse `[PROVED; CLOSED]`

The existing Euler-region Pick kernel is a genuine closed source-side index, but restricting its
sample nodes cannot make it a Route D height localizer.  The negative-square index of an analytic
Hermitian kernel is unchanged on every nonempty open uniqueness subset.  Hence any dense node family
inside an Euler-region band still recovers the complete off-line count in the horizontal half-strip,
not the count in a selected ordinate interval.

An exact analytic pointwise cutoff is also impossible on the connected source domain by the identity
theorem; a nonanalytic cutoff destroys the kernel theorem.  Full proof:

`../2-fully-proven/not_new_scientific_knowledge/euler-pick-node-window-nonlocality.md`.

The surviving exact operation is a Riesz projection of a source-selected closed model operator (or an
equivalent modified symbol).  Constructing that operator, proving its contour resolvent lies in the
required ideal, and bounding the first post-certificate projection are precisely the missing
height-excisive source theorem.

## Final closed-model audit `[TERMINAL]`

The last surviving formulation was a source-selected closed family with a reflection-odd Riesz
projection on the post-certificate window.  The complete analytic-Fredholm audit is banked in

`../2-fully-proven/not_new_scientific_knowledge/window-riesz-gap-target-equivalence.md`.

For any determinant-compatible family whose characteristic multiplicity is the free-orbit count,
all of the following are equivalent:

```text
zero reflection-odd root multiplicity
= zero Riesz projection in the linear compact-resolvent case
= zero determinant winding
= no free orbit in the window.
```

A finite contour resolvent bound is not a gap theorem: the scalar family `F(z)=z` has uniformly
bounded inverse on the unit circle and one zero inside.  What would suffice is a relative boundary
homotopy estimate smaller than one against a zero-index reference.  No audited Route D source object
supplies such a reference and estimate.

## Completion audit

The requested source theorem would have to provide every item below.

1. **Completed source construction.** Failed for the ordinary all-place local-ratio multiplier because
   its completion-compatible regularization is `1`; the tail/residue Banach and `K`-theory extensions
   split or are nonclosable; the genuine semilocal prolate construction remains a Route B open core.
2. **Free-orbit index identity.** Available only for target-faithful Pick, divisor, residue, or
   characteristic families.  These are exact consumers and do not force the index to vanish.
3. **Height excision.** Restricting Euler Pick nodes preserves the global negative index.  Exact
   analytic pointwise cutoffs do not exist.  A Riesz projection requires a new closed model.
4. **Quantitative source gap.** Contour boundedness is insufficient.  The required relative homotopy
   or norm estimate has not been derived from Euler--Gamma data.
5. **Strict numerical extension.** No explicit rational `U>H` follows without the already completed
   Turing enumeration.
6. **Paper and Lean gates.** Since items 1, 3, and 4 are absent, there is no source theorem to promote
   to stage 2 and no unconditional theorem to formalize in Lean.

## Final verdict

`[RETIRED: NO INDEPENDENT SOURCE PRODUCER]`

Route D has a complete and efficient consumer, and its computational branch has already enlarged the
verified height.  It does not contain an independent noncomputational source theorem.  Every audited
producer either

- collapses to a trivial completed symbol or split extension;
- is blind to height or horizontal displacement;
- is nonclosable unless RH already holds;
- reconstructs the divisor and applies a target-equivalent count/positivity/index; or
- requires a new source-selected closed geometry and relative homotopy estimate belonging outside
  Route D.

The exact theorem that would reopen the route is:

```text
There exist a source-constructed determinant-compatible family F_E,
a zero-index source reference F_0, and an explicit post-certificate window D
such that the reflection-odd characteristic divisor of F_E is the free Xi orbit divisor and
sup_(z in boundary D) ||F_0(z)^(-1)(F_E(z)-F_0(z))|| < 1.
```

This is a precise theorem statement, but no construction or proof exists in the audited source
interfaces.  Calling the Riesz projection itself the source theorem merely restates the local RH
conclusion.  The card is therefore retired rather than left in progress.
