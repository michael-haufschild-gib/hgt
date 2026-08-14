# Split-star formation, positive-profile conservation, and functional-fixedness neutrality

- **ID:** ULF-CRSM-3
- **Stage:** 2-fully-proven
- **Type:** THEOREM + EXACT SELECTION NO-GO
- **Source:** `../packet-formation-mechanics/functional-equation-split-formation-lift-information-isometry-and-work-no-go.md` and `../../../../1-in-progress/rh-current-frontier-map.md`
- **Statement:** A split `*`-homomorphic formation preserves the complete evaluation profile of every source element in every fixed positive receiver; an equivariant formation also preserves functional-equation fixedness. Therefore common recovery is simultaneously information-neutral, positive-detectability-neutral, and fixed-locus-neutral, while any `*`-homomorphic image of a reflected star-isotropic atom remains positively invisible.

## Goal

The functional-equation packet lift proves that a common Markov recovery kernel preserves KL and
Jeffreys information.  The RH frontier asks for something stronger: a positive realization that
retains reduced divisor atoms and thereby annihilates the reflection-odd radical.

This card asks whether split formation can create that positive detectability.  The answer is an
exact no-go, with a stronger positive survivor:

> split `*`-formation conserves the entire receiver-evaluation profile, not merely one norm or one
> scalar statistic.

The conclusion constrains the missing mechanism.  It cannot be a direct `*`-homomorphic completion
of the current reflected-orthogonal source algebra.  It must first change the constitutive law
(product, involution, orthogonality relation, or relative/derived comparison).

## Gates

- [x] 0 -> 1 in-progress: common-recovery question typed independently of any RH route
- [x] 1 -> 2 fully-proven: dependency-closed theorem, exact countermodels, and source-selection consequence
- [x] 2 -> 3 formalized: Lean module `ConstitutivePositiveProfileFormation`
- [ ] 3 -> 4 publication-ready

## 1. Receiver profiles

Let `A`, `B`, and `C` be unital complex `*`-algebras.  Write

\[
 \operatorname{Rep}_C(A)=\operatorname{Hom}_{*\text{-alg}}(A,C).
\]

For `x in A`, define its complete evaluation profile in receiver `C` by

\[
 \operatorname{Prof}_C^A(x)
 =\{\pi(x):\pi\in\operatorname{Rep}_C(A)\}\subseteq C.
 \tag{SPF.1}
\]

The receiver-relative positive radical is

\[
 J_C(A)=\{x\in A:\pi(x)=0\text{ for every }\pi\in\operatorname{Rep}_C(A)\}.
 \tag{SPF.2}
\]

When `C` ranges through `C*`-algebras, the intersection of these receiver-relative radicals is the
usual representational positive radical/minimal closed `*`-ideal.

### Definition 1.1 -- split-star formation

A split-star formation from `A` to `B` is a pair of `*`-algebra homomorphisms

\[
 F:A\longrightarrow B,
 \qquad R:B\longrightarrow A,
 \qquad R\circ F=\operatorname{id}_A.
 \tag{SPF.3}
\]

`F` is formation and `R` is common recovery.

## 2. Exact profile conservation

### Theorem 2.1 -- split-star receiver-profile law

For every split-star formation `(F,R)`, every receiver `C`, and every `x in A`,

\[
 \boxed{\operatorname{Prof}_C^B(Fx)=\operatorname{Prof}_C^A(x).}
 \tag{SPF.4}
\]

Equivalently,

\[
 Fx\in J_C(B)\quad\Longleftrightarrow\quad x\in J_C(A).
 \tag{SPF.5}
\]

Consequently

\[
 \boxed{F^{-1}J_C(B)=J_C(A)}
 \tag{SPF.6}
\]

for every receiver, and the same equality holds after intersecting over any declared class of
receivers, in particular all `C*`-receivers.

### Proof

Restriction along `F` defines

\[
 \operatorname{res}_F:\operatorname{Rep}_C(B)\to\operatorname{Rep}_C(A),
 \qquad \pi\mapsto\pi\circ F.
\]

Extension along `R` defines

\[
 \operatorname{ext}_R:\operatorname{Rep}_C(A)\to\operatorname{Rep}_C(B),
 \qquad \varphi\mapsto\varphi\circ R.
\]

Since `R F=id`,

\[
 \operatorname{res}_F\operatorname{ext}_R(\varphi)
 =\varphi\circ R\circ F=\varphi.
 \tag{SPF.7}
\]

Thus restriction is surjective.  For every `pi`,

\[
 \pi(Fx)=(\pi\circ F)(x),
\]

so the left profile in `(SPF.4)` is contained in the right profile.  Conversely, for every
`varphi`,

\[
 (\varphi\circ R)(Fx)=\varphi(x),
\]

so every right-profile value occurs on the left.  This proves `(SPF.4)`.  Equality `(SPF.5)` is the
special case in which the profile is the singleton `{0}`, and `(SPF.6)` is the same statement in
preimage notation.  Intersections preserve equality.  QED.

### Corollary 2.2 -- monotonicity without recovery

For an arbitrary `*`-homomorphism `F:A->B`, even without a recovery,

\[
 \operatorname{Prof}_C^B(Fx)\subseteq\operatorname{Prof}_C^A(x).
 \tag{SPF.8}
\]

Hence `*`-homomorphic formation can lose positive detectability but cannot create it.  Split recovery
is exactly what upgrades this one-sided data-processing law to equality.

### Corollary 2.3 -- injectivity and joint reconstruction

Every split-star formation is injective.  More strongly, the family of all receiver evaluations of
`Fx` reconstructs exactly the same value set as the family of all receiver evaluations of `x`.
This is not dimension counting or faithfulness of one chosen observer; it is a simultaneous
reconstruction identity for every receiver.

### Proof

If `Fx=Fy`, applying `R` gives `x=y`.  Joint reconstruction is `(SPF.4)`.  QED.

## 3. Functional-equation fixedness

Let `alpha:A->A` and `beta:B->B` be involutions, not necessarily the algebraic star operations.
Assume formation is equivariant:

\[
 F\alpha=\beta F.
 \tag{SPF.9}
\]

### Theorem 3.1 -- split functional-fixedness law

For every `x in A`,

\[
 \boxed{\beta(Fx)=Fx\quad\Longleftrightarrow\quad\alpha(x)=x.}
 \tag{SPF.10}
\]

### Proof

If `alpha x=x`, equivariance gives `beta(Fx)=F(alpha x)=Fx`.  Conversely,

\[
 F(\alpha x)=\beta(Fx)=Fx.
\]

Formation is injective by Corollary 2.3, hence `alpha x=x`.  QED.

Thus equivariant split formation cannot add or remove functional-equation fixed points on the
formed image.

## 4. Positive-star no-go

Suppose `C` is a `C*`-algebra and `x in A` is star-isotropic:

\[
 x^*x=0.
 \tag{SPF.11}
\]

Every `*`-homomorphism `pi:A->C` kills `x`, because

\[
 \pi(x)^*\pi(x)=\pi(x^*x)=0
\]

and the `C*` identity implies `pi(x)=0`.

### Theorem 4.1 -- positive invisibility is formation-hereditary

For every `*`-homomorphism `F:A->B`, split or not,

\[
 x^*x=0\quad\Longrightarrow\quad (Fx)^*(Fx)=0
 \tag{SPF.12}
\]

and therefore every `C*`-representation of `B` kills `Fx`.

### Proof

`F` preserves multiplication, star, and zero:

\[
 (Fx)^*(Fx)=F(x^*)F(x)=F(x^*x)=0.
\]

Apply the preceding `C*` argument.  QED.

### Corollary 4.2 -- direct positive completion cannot be the missing RH selector

In the current reduced-divisor source algebra, an off-line reflection pair gives a nonzero atom
`x` with `x*=y` and `yx=0`, hence `x*x=0`.  Theorem 4.1 shows:

> no direct `*`-homomorphic formation of that algebra into any later algebra can make the atom
> visible to a positive `C*` receiver.

Split recovery is not merely insufficient; abandoning the split while retaining the same
`*`-homomorphic source law is still insufficient.  A successful selector must change at least one
load-bearing constitutive datum before positive realization:

1. the product/orthogonality law;
2. the involution identified with functional-equation reflection;
3. the notion of morphism (relative, derived, or non-`*` comparison);
4. or the source relation itself, so off-line atoms are eliminated before the positive receiver.

This sharpens the open premise in the positive-reflection-radical RH reduction.  The missing theorem
is not “find a faithful positive completion.”  Such a completion is algebraically impossible for
the current source law.  The missing theorem must be a **constitutive transmutation** followed by a
positive conservative realization.

## 5. Three-organ fusion law

The common recovery grammar now has three exact, structurally different faces.

| organ | formation | recovery | exactly conserved quantity |
|---|---|---|---|
| probability/information | common Markov kernel `mu -> mu tensor K` | first marginal | KL and Jeffreys information |
| positive representation | split `*`-homomorphism `F` | `*`-retraction `R` | complete receiver-evaluation profile and positive radical |
| functional equation | equivariant split formation | same `R` | fixed-point locus on the formed image |

These are not analogies.  Each conservation law follows from two opposite data-processing maps:
formation followed by recovery is the identity.  The shared mechanism is:

\[
 \boxed{\text{a split formation cannot manufacture the feature tested after recovery}.}
 \tag{SPF.13}
\]

The fourth-organ prediction is Corollary 4.2: the positive divisor selector cannot be another split
observer/formation chart.  It must be a law-changing transmutation, and its failure to preserve
`x*x=0` is a concrete necessary certificate.

## 6. Hostile countermodels and sharp boundaries

### 6.1 Recovery is load-bearing for equality

Let `A=C x C`, `B=C`, and `F(a,b)=a`, with coordinatewise star.  This is a unital
`*`-homomorphism with no left inverse.  The element `x=(0,1)` is detected by the second projection
of `A`, but `Fx=0`.  Thus `(SPF.8)` can be strict.

### 6.2 Star preservation is load-bearing for positive monotonicity

Let `A=C[epsilon]/(epsilon^2)` with `epsilon*=epsilon`.  Then `epsilon*epsilon=0`, so every positive
`*`-representation kills `epsilon`.  The unital algebra map

\[
 \epsilon\longmapsto
 \begin{pmatrix}0&1\\0&0\end{pmatrix}
\]

into `M_2(C)` detects `epsilon`, but it is not star-preserving.  Hence changing the star law can
escape Theorem 4.1; this is a genuine boundary, not a proof gap.

### 6.3 Equivariance is load-bearing for fixedness

Take `A=B=C x C`, `F=R=id`, let `alpha` swap coordinates, and let `beta=id`.  Split recovery holds,
but fixed loci differ because `(SPF.9)` fails.

### 6.4 A split is not a selection law

All three conservation theorems are neutralities.  They neither force a source element to vanish
nor construct a constitutive transmutation.  Calling the split itself a selector would repeat the
functional-equation-is-selection error already ruled out by the packet theorem.

## 7. Relation to established mathematics

Kernels of `*`-representations, their lattice of closed `*`-ideals, and the minimal ideal are
standard representation-theoretic objects.  Bursztyn and Waldmann prove invariance of this lattice
under formal Morita equivalence in [*Ideals and Formal Morita Equivalence of Algebras*](https://arxiv.org/abs/math/0005227), and develop the corresponding algebraic Rieffel/GNS machinery in
[*Algebraic Rieffel Induction, Formal Morita Equivalence, and Applications to Deformation Quantization*](https://arxiv.org/abs/math/9912182).

Theorem 2.1 is the elementary retract analogue needed here.  Its value is not a priority claim; it
is the exact fusion with the corpus's split Markov-information theorem and positive
reflection-radical frontier.

## 8. Exact output

The theorem changes the final-selection question from

> Which positive completion retains the reflected divisor atoms?

to

> Which source-native constitutive transmutation changes the reflected-orthogonal multiplication or
> star law, and why does its new positive realization remain conservative on reduced divisor atoms?

That is a smaller and falsifiable open core.  Any proposed selector that factors as a
`*`-homomorphic image of the current source algebra is rejected immediately by `(SPF.12)`.

## Log

- 2026-08-14 -- split-recovery profile theorem extracted from functional-equation packet neutrality
- 2026-08-14 -- hostile audit strengthened “non-split required” to “no direct `*`-homomorphic formation can work”
- 2026-08-14 -- promoted to Stage 2 with dependency-closed proof and exact countermodels
