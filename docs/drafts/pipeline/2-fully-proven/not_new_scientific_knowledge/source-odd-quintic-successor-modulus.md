# First source-odd successor modulus occurs at arity five

- **ID:** `source-odd-quintic-successor-modulus`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / BRIDGE / NOT NEW MATHEMATICS
- **Source:** `../../1-in-progress/law-valued-actuality-universal-law.md`
- **Statement:** For a labeled two-channel complex source, fully supported source-odd symmetric
  successor tensors have one projective source orbit in arities two through four, while arity
  five carries the invariant \(b^2/(ac)\) and hence infinitely many inequivalent orbits.

## Goal

Test the smallest law-valued-actuality discriminator after source polarity eliminated the
quadratic rank ambiguity. Determine the first symmetric arity at which complete labeled polarity
and source oddness no longer select one fully supported projective orbit.

This is finite invariant theory. It does not prove that physical successor laws are symmetric
tensors, that every coefficient is physically supported, that distinct orbits interfere, or that
law-valued actuality is true.

## Gates

- [x] 0 → 1 in-progress: exact source action and nonselection question
- [x] 1 → 2 fully-proven: complete elementary orbit proof below
- [ ] 2 → 3 formalized: exact unconditional Lean theorem and final audit
- [x] division-free invariant and normalized nonselection core formalized
- [ ] physical bridge: source completeness identifies full support and tensor arity
- [ ] cross-law interference between distinct quintic orbits

## Setup

Let \(P=\mathbb Cx\oplus\mathbb Cy\) carry labeled source polarity

\[
Jx=x,\qquad Jy=-y.
\tag{Q5.1}
\]

A symmetric \(n\)-successor tensor is represented by a binary form
\(f\in\operatorname{Sym}^n(P^*)\). It is **source-odd** when

\[
f(x,-y)=-f(x,y).
\tag{Q5.2}
\]

Source-preserving changes of presentation commute with \(J\), hence act diagonally:

\[
(x,y)\longmapsto(ux,vy),
\qquad u,v\in\mathbb C^\times.
\tag{Q5.3}
\]

The one-dimensional top record may also be rescaled by
\(\lambda\in\mathbb C^\times\). Define projective source equivalence by

\[
f'(x,y)=\lambda f(ux,vy).
\tag{Q5.4}
\]

A source-odd form is **fully supported** when every monomial allowed by `(Q5.2)` has nonzero
coefficient. This is an algebraic condition only. Its identification with physical
source-faithfulness is open.

## Theorem

`[PROVED HERE]`

Among fully supported source-odd binary forms:

1. arity two has one projective source orbit;
2. arity three has one projective source orbit;
3. arity four has one projective source orbit;
4. arity five has infinitely many projective source orbits; and
5. for

   \[
   f_{a,b,c}(x,y)=a x^4y+b x^2y^3+c y^5,
   \qquad abc\ne0,
   \tag{Q5.5}
   \]

   the complete orbit invariant is

   \[
   \boxed{\kappa(f_{a,b,c})={b^2\over ac}.}
   \tag{Q5.6}
   \]

Thus arity five is the first fully supported source-odd symmetric layer carrying a continuous
projective modulus under labeled source equivalence.

## Proof

Condition `(Q5.2)` retains exactly monomials whose exponent of \(y\) is odd.

At arity two,

\[
f=a\,xy,\qquad a\ne0.
\]

The coefficient changes by \(\lambda uv\), so every nonzero coefficient is equivalent to every
other.

At arity three,

\[
f=a x^2y+b y^3,\qquad ab\ne0.
\]

After removing the common projective factor \(\lambda u^2v\), the ratio \(b/a\) changes by
\((v/u)^2\). Every nonzero complex number has a square root, so the action is transitive on
nonzero ratios.

At arity four,

\[
f=a x^3y+bxy^3,\qquad ab\ne0.
\]

After removing \(\lambda u^3v\), the ratio again changes by \((v/u)^2\). The fully supported locus
again has one orbit.

At arity five, `(Q5.3)`--`(Q5.4)` sends the coefficient triple to

\[
(a,b,c)\longmapsto
\left(
  \lambda a u^4v,\,
  \lambda b u^2v^3,\,
  \lambda c v^5
\right).
\tag{Q5.7}
\]

Consequently

\[
{(\lambda b u^2v^3)^2\over
 (\lambda a u^4v)(\lambda c v^5)}
={b^2\over ac},
\]

so \(\kappa\) is invariant.

It is complete. Suppose \(\kappa(a,b,c)=\kappa(a',b',c')\). After factoring the leading
coefficient, diagonal reparametrization acts projectively by

\[
[a:b:c]\longmapsto[a:br:cr^2],
\qquad r=(v/u)^2\in\mathbb C^\times.
\tag{Q5.8}
\]

Set

\[
r={b'a\over a'b}.
\]

Equality of the two \(\kappa\)-values is exactly the remaining equation

\[
{a'\over a}\,c r^2=c'.
\]

Choose \(v/u\) to be a square root of \(r\), then choose the projective scale to match \(a'\).
This gives `(Q5.4)`. Therefore equal \(\kappa\) is also sufficient.

Finally, \(f_{1,b,1}\) is fully supported for every \(b\ne0\) and has
\(\kappa=b^2\). Infinitely many choices of \(b^2\) give infinitely many inequivalent orbits.
This proves all five claims. `QED`

## Strongest positive survivor

The quadratic source-polarity selector was not evidence that one event source recursively fixes
its entire higher law. It proves only low-arity rigidity.

The first surviving algebraic datum in the minimal labeled source is not another state, vector,
or self-composition coefficient. It is a dimensionless ratio comparing three allowed five-way
coexistence channels:

\[
b^2:ac.
\]

This changes the law-valued research question:

```text
old finite question:
  can pairwise source data select one quadratic successor?

answer:
  yes, after labeled polarity and odd transfer are imposed.

new finite question:
  what physical principle fixes, quantizes, or coherently superposes the quintic modulus κ?
```

If complete physical source consequence fixes \(\kappa\), law-valued nonuniqueness moves to still
higher arity. If distinct \(\kappa\)-classes survive and admit future-relative interference, this
is the smallest current model of law-valued quantum alternatives.

## Hostile audit

### Is this new mathematics?

No. This is elementary invariant theory for a one-dimensional torus acting on binary forms.
Binary-form invariants and torus weights are classical. Door grade: `[BRIDGE]`.

### Is arity five physically selected?

No. “Arity” currently counts symmetric higher-record inputs. No physical theorem identifies it
with particles, spacetime dimensions, force sectors, interaction valence, or measurement
outcomes.

### Is \(\kappa\) a quantum amplitude or coupling?

No. It is an orbit invariant. Calling it a phase, probability, force, generation number, or
coupling would be numerology until a source-generated positive comparison and continuum
realization are derived.

### Does full support follow from no spectators?

No. Full coefficient support is only the clean generic stratum. A physical no-spectator law may
impose a different nondegeneracy condition. Boundary strata must be classified separately if the
physics reaches this model.

### Does the theorem prove cross-law interference?

No. It proves inequivalence, not coherent comparability. The cross-law interference problem is
still the load-bearing open core.

## Lean target

The division-free core is now formalized:

\[
(b')^2ac=b^2a'c'
\tag{Q5.9}
\]

for every diagonal projective reparametrization `(Q5.7)`. Lean also proves that normalized
quintics with distinct squared middle coefficients are not source-projectively equivalent.

Module:

`GaloisForLFunctions.HTGeometry.SourceOddQuinticSuccessorModulus`.

The direct source check, final module build, and axiom audit passed. The full complex
fully-supported orbit classification remains Lean-open, so this parent card stays at Stage 2.
The exact formalized core has its own Stage-3 card:
`../../3-formalized/not_new_scientific_knowledge/source-odd-quintic-cross-invariant.md`.

## Log

- 2026-07-30 — quadratic law nonselection collapsed under the existing source-polarity selector.
- 2026-07-30 — checked source-odd symmetric arities successively; the first generic coefficient
  count exceeding diagonal projective freedom occurs at arity five.
- 2026-07-30 — proved the complete quintic invariant \(\kappa=b^2/(ac)\) and the low-arity
  transitivity boundary.
- 2026-07-30 — retained theorem as a standard invariant-theory bridge; physical interpretation
  remains conjectural.
- 2026-07-30 — formalized the division-free cross invariant and normalized nonselection theorem;
  final module build passed and axiom audit reported only `propext`.
