# Observer-restricted temporal-constraint conservation

- **ID:** `observer-restricted-temporal-constraint-conservation`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL LAW / OBSERVER RESTRICTION / SPECTRAL FILTRATION
- **Scientific status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`

## Exact claim

Let \(I\) be any nonempty finite spectral label set and let
\[
 X_I=\{q\in\mathbb Q^I:\sum_iq_i=0\}
\]
be its rational projective character space. Let
\(\epsilon_n:I\to\mathbb C\) be an arbitrary sequence of spectral jets.
An observer is any rational subspace \(O\le X_I\) of phase characters that
its probes can distinguish.

For \(r\in\mathbb N_0\), define
\[
 J_{O,r}:O\longrightarrow\mathbb C^r,\qquad
 J_{O,r}(q)=
 \left(\sum_iq_i\epsilon_n(i)\right)_{0\le n<r}.       \tag{1}
\]
Put
\[
 C_O(r)=\ker J_{O,r},\qquad
 D_O(r)=\operatorname{im}J_{O,r},\qquad
 d_O(r)=\dim_{\mathbb Q}D_O(r).                       \tag{2}
\]

Then, for every jet sequence, every observer and every resolution:
\[
 \boxed{d_O(r)+\dim_{\mathbb Q}C_O(r)=\dim_{\mathbb Q}O.}       \tag{3}
\]
Moreover,
\[
 C_O(s)\subseteq C_O(r),\qquad d_O(r)\le d_O(s)
 \quad(r\le s),                                      \tag{4}
\]
and
\[
 \boxed{
 d_O(s)-d_O(r)
 =
 \dim C_O(r)-\dim C_O(s).
 }                                                    \tag{5}
\]
Finally,
\[
 d_O(0)=0,\qquad d_O(r)\le\dim O\le |I|-1.            \tag{6}
\]

## Dependency-closed proof

Equation `(3)` is rank--nullity for the linear map `(1)`. If \(r\le s\),
the first \(r\) coordinates of \(J_{O,s}(q)\) equal \(J_{O,r}(q)\), so
\(J_{O,s}(q)=0\) implies \(J_{O,r}(q)=0\). This proves the kernel inclusion
in `(4)`. Finite-dimensionality and `(3)` then give dimension monotonicity.
Subtracting `(3)` at \(r\) and \(s\), using the monotonicities to interpret
natural-number subtraction, gives `(5)`. At \(r=0\), the codomain is the
zero vector space, proving the first part of `(6)`; the remaining bounds are
rank bounded by domain dimension and
\(\dim X_I=|I|-1\). \(\square\)

## Meaning

`(5)` is the exact conservation law missing from the prior corpus:

> Every independent temporal direction gained by an observer is exactly one
> independent spectral constraint that has ceased to survive at that
> observer's resolution.

System, observer and time horizon enter one map rather than three adjacent
theorems:

- system supplies the jet sequence;
- observer supplies the character subspace;
- available interaction/time resolution supplies \(r\).

## Hostile verdict

`[BRIDGE]` Rank--nullity itself is classical. This theorem is not stand-alone
new mathematics. Candidate-new content begins only after it is joined
exactly to:

1. the integral character filtration and its non-Archimedean birth
   valuation;
2. inverse-power finite-time wall crossing for every active character;
3. graph/local-interaction lower bounds on when a constraint can break;
4. recurrence-target volume after the resulting direction is resolved.

The law is necessary infrastructure for a universal paper because it makes
“observer-dependent temporal dimension” an invariant, not rhetoric.

## Formal status

`[LEAN-PROVED]`
`formal/GaloisForLFunctions/HTGeometry/ObserverRestrictedTemporalConstraintLaw.lean`
proves `(3)`--`(6)` for every finite-dimensional rational observer carrier
and every linear observer map into projective characters. The carrier
formulation is more general than a literal subspace; an injective observer
recovers the bound \(|I|-1\). Direct `lake env lean` verification passes
without warnings.
