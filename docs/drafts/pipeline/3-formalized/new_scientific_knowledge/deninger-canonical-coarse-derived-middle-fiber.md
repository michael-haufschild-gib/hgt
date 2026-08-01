# Canonical coarse-to-derived endpoint fiber

- **ID:** `deninger-canonical-coarse-derived-middle-fiber`
- **Stage:** 2-fully-proven
- **Type:** ABSTRACT THEOREM / QUARANTINED DIAGNOSTIC
- **Label:** `DAC_CANONICAL_COARSE_DERIVED_MIDDLE_FIBER`
- **Parent:** none; former
  `deninger-coarse-stack-comparison-defect` route is retired
- **Statement:** an abstract fiber lemma identifies a middle term when
  endpoint hypotheses are independently supplied; it is not used to
  construct Deninger's arithmetic cohomology.

## Setup

Let \(\mathcal D\) be a stable category with a \(t\)-structure and let
\[
 f:C_{\mathrm{coarse}}\longrightarrow C_{\mathrm{der}}             \tag{1}
\]
be a morphism.  Put
\[
 C_{\mathrm{mid}}^{\mathrm{can}}
 :=\operatorname{Fib}(f)
 =\operatorname{Cone}(f)[-1].                                      \tag{2}
\]
Assume:

1. \(H^q(C_{\mathrm{coarse}})=H^q(C_{\mathrm{der}})=0\) for
   \(q\notin\{0,1,2\}\);
2. \(H^1(C_{\mathrm{der}})=0\);
3. \(H^0(f)\) and \(H^2(f)\) are isomorphisms.

## Theorem

`[PROVED HERE] [DAC_CANONICAL_COARSE_DERIVED_MIDDLE_FIBER]`

Under these assumptions,
\[
 H^q(C_{\mathrm{mid}}^{\mathrm{can}})
 =
 \begin{cases}
   H^1(C_{\mathrm{coarse}}),&q=1,\\
   0,&q\ne1.
 \end{cases}                                                       \tag{3}
\]
The isomorphism in degree one is canonical.  If `(1)` is equivariant
for a flow or a semigroup of correspondences, `(3)` is equivariant.

## Proof

The fiber triangle
\[
 C_{\mathrm{mid}}^{\mathrm{can}}
 \longrightarrow C_{\mathrm{coarse}}
 \xrightarrow{f}C_{\mathrm{der}}
 \longrightarrow C_{\mathrm{mid}}^{\mathrm{can}}[1]                \tag{4}
\]
gives a long exact cohomology sequence.

In degrees below zero and above three, vanishing is immediate.  Around
degree zero, exactness gives
\[
 0\longrightarrow H^0(C_{\mathrm{mid}}^{\mathrm{can}})
 \longrightarrow H^0(C_{\mathrm{coarse}})
 \xrightarrow[\sim]{H^0(f)}H^0(C_{\mathrm{der}}),
\]
so \(H^0(C_{\mathrm{mid}}^{\mathrm{can}})=0\).  The following segment is
\[
 H^0(C_{\mathrm{der}})
 \longrightarrow H^1(C_{\mathrm{mid}}^{\mathrm{can}})
 \longrightarrow H^1(C_{\mathrm{coarse}})
 \longrightarrow H^1(C_{\mathrm{der}})=0.
\]
Because \(H^0(f)\) is surjective, its connecting morphism is zero.
Therefore the middle arrow is a canonical isomorphism.

Next,
\[
 0=H^1(C_{\mathrm{der}})
 \longrightarrow H^2(C_{\mathrm{mid}}^{\mathrm{can}})
 \longrightarrow H^2(C_{\mathrm{coarse}})
 \xrightarrow[\sim]{H^2(f)}H^2(C_{\mathrm{der}})
\]
forces \(H^2(C_{\mathrm{mid}}^{\mathrm{can}})=0\).  Surjectivity of
\(H^2(f)\), followed by the assumed higher vanishing, also gives
\(H^3(C_{\mathrm{mid}}^{\mathrm{can}})=0\).  This proves `(3)`.
Naturality of the long exact sequence proves equivariance.

## Deninger scope

The former application took \(C_{\mathrm{der}}\) to be quotient-stack
cohomology and proposed computing it as a Milnor--Arakelov endpoint.
That route is retired in
`deninger-derived-quotient-milnor-arakelov-endpoint`: Deninger's
source uses the degreewise invariant sheaf, not derived
\(\mathbb Q_{>0}\)-invariants.

The abstract theorem remains true and may diagnose a comparison if
such endpoint hypotheses arise independently.  It is not a dependency
of the arithmetic-cohomology construction.  Source work proceeds
through `DAC_ARITHMETIC_PROJECTION_LERAY_ROST_SCHMID_RESOLUTION`.

## Hostile audit

- Without arithmetic localization and the real boundary, `(6)` need
  not have endpoint cohomology.
- The free abelian group \(\mathbb Q_{>0}\) has unbounded exterior
  group cohomology.  Steinberg relative cells must kill the higher
  directions; they cannot be truncated by declaration.
- If \(H^1(C_{\mathrm{der}})\ne0\), the canonical fiber maps onto only
  the kernel of
  \(H^1(C_{\mathrm{coarse}})\to H^1(C_{\mathrm{der}})\).
- If the degree-two comparison is not an isomorphism, extra endpoint
  or signature classes survive in the fiber.
- No zero of \(\xi\), RH premise, CCM object, or numerical computation
  enters the construction or proof.

## Novelty status

The abstract fiber lemma is standard homological algebra and is not
new.  Its use to replace a noncanonical endpoint inclusion by
Deninger's canonical coarse-to-derived comparison is a proposed
source reorganization.  No literature source located in the internal
or primary-source audit proves
`DAC_DERIVED_QUOTIENT_MILNOR_ARAKELOV_ENDPOINT`.

**Verdict:** `ABSTRACT THEOREM FULLY PROVEN ON PAPER; QUARANTINED FROM
THE DENINGER SOURCE DEPENDENCY GRAPH`.

## Lean status

### The fibre lemma landed

`formal/GaloisForLFunctions/RHTower/DeningerMiddleFiber.lean`.  Axiom audit: `propext` for the
five exactness theorems, `propext, Classical.choice, Quot.sound` for the equivariance of the
inverse.

mathlib has no stable `∞`-categories, so the theorem is formalized in the form its own proof uses:
the exactness content of the long exact sequence of the fibre triangle `(4)`.  Every statement
therefore applies verbatim to the fibre of a morphism of cochain complexes, which is what the
`t`-structure hypotheses `(1)` amount to.

- `deningerMiddleFiber_connecting_eq_zero` — a surjective comparison kills the connecting
  morphism; this is the step that makes both `H⁰(f)` and `H²(f)` surjectivity bite.
- `deningerMiddleFiber_degree_zero` — `H⁰(C_mid) = 0`, from injectivity of `H⁰(f)`.
- `deningerMiddleFiber_degree_one_injective`, `_surjective`, `_bijective` — **`(3)` in degree
  one**: the vanishing connecting map makes the fibre inject, and `H¹(C_der) = 0` makes it
  surject, so `H¹(C_mid) ≅ H¹(C_coarse)` canonically.
- `deningerMiddleFiber_degree_two` — `H²(C_mid) = 0`, from `H¹(C_der) = 0` and injectivity of
  `H²(f)`.
- `deningerMiddleFiber_degree_three` — `H³(C_mid) = 0`, from surjectivity of `H²(f)`.
- `deningerMiddleFiberEquiv`, `deningerMiddleFiber_symm_equivariant` — the degree-one
  identification as a linear equivalence, and its equivariance: whatever endomorphisms the
  comparison intertwines — a flow or a semigroup of correspondences — the inverse intertwines too.

The theorem stays quarantined from the Deninger source dependency graph, exactly as the card
records; formalizing it only makes the diagnostic reusable.

### Remaining

Nothing.  The hypotheses `(1)`–`(3)` and the conclusion `(3)` are formalized; the only step not
expressible in mathlib is the passage from a fibre triangle in a stable category to its long exact
sequence, which is standard and is the card's own starting point.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  Definition 10.1, Theorem 10.2, and §12:
  https://arxiv.org/abs/1807.06400
- Dustin Clausen and Peter Scholze,
  *Condensed Mathematics and Complex Geometry*, Theorems 9.15 and
  10.1 on compact-Stein derived descent:
  https://arxiv.org/abs/2605.11731
- `DAC_REAL_ARAKELOV_DIVISOR_ENDPOINT`
- `DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION`
- `DAC_COARSE_STACK_EXACTNESS_SCALAR_SPECTRUM_NO_GO`
