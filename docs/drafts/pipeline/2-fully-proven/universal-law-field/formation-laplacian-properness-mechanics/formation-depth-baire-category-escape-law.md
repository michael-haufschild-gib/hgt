# Formation-depth Baire-category escape law

- **ID:** ULF-FDBE-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / NO-GO WITH POSITIVE SURVIVOR
- **Source:** fresh audit of `ConstitutiveFormationDepthProperness`,
  `ConstitutiveFormationDepthCompactness`, and `BoundedFormationRecoveryRigidity`
- **Statement:** The natural formation-depth domain is a compactly embedded Polish source core
  which is dense, sigma-compact, and meagre in the observer Hilbert completion; every null sequence
  with nonzero limiting codiagonal response escapes every bounded formation-gauge set.

## Goal

Identify the exact topology on which singular horizontal recovery is legal. This decides whether
Baire measurability, automatic continuity, or compact properness can themselves force horizontal
grade zero.

## Gates

- [x] 0 → 1 in-progress: source-pure statement and corpus parents identified
- [x] 1 → 2 fully-proven: dependency-closed proof below
- [ ] 2 → 3 formalized: exact Lean theorem pending
- [ ] 3 → 4 publication-ready

## 1. Big-picture interpretation

Corpus completion failures are not accidental losses of estimates. Source execution carries a
strictly finer complete topology than observer completion. Horizontal response is continuous on
that fine source topology while singular on the coarse Hilbert topology. Compact formation
sublevels make this mismatch exact: legal finite-work histories form a dense first-category core,
and every persistent nonzero response runs to infinity in its fine topology while converging to
zero for the observer.

Thus Baire/automatic-continuity cannot be the missing RH producer. It applies only after replacing
the actual meagre executable core by a second-category domain, which is precisely the unproved
global admission step.

## 2. Setup

Let

\[
H=\ell^2(\mathbb N,\mathbb C),\qquad
D=\left\{x\in\ell^1:\sum_{n\ge0}n|x_n|<\infty\right\}.
\]

For `x in D`, put

\[
M(x)=\sum_nx_n,\qquad
W(x)=\sum_n n|x_n|,\qquad
G(x)=|M(x)|+2W(x).
\]

This is the literal `formationMass`, `formationDepthWork`, and `formationGauge` of the Lean
corpus. Write `j:D -> H` for the canonical inclusion and `K_C={x in D:G(x)<=C}`.

## 3. The theorem

### Theorem 3.1 — fine source topology

`G` is a norm on `D`, and `(D,G)` is a separable Banach space. The inclusion `j:(D,G)->H` is
continuous, injective, compact, and has dense proper range.

#### Proof [PROVED HERE]

Homogeneity and the triangle inequality are immediate. The corpus theorem
`formationGauge_eq_zero_iff` gives definiteness. Let

\[
W_0(x)=|x_0|+\sum_{n\ge1}n|x_n|.
\]

Since `sum |x_n| <= G(x)` by `tsum_norm_le_formationGauge`,

\[
W_0(x)\le |x_0|+W(x)\le G(x)+\tfrac12G(x)=\tfrac32G(x).
\]

Conversely,

\[
G(x)\le |x_0|+\sum_{n\ge1}|x_n|+2\sum_{n\ge1}n|x_n|
\le 3W_0(x).
\]

Hence `G` is equivalent to the standard weighted `ell^1` norm `W_0`; completeness and
separability follow. Also

\[
\|j(x)\|_2\le\|x\|_1\le G(x),
\]

so `j` is continuous. The corpus theorem `isCompact_formationLpGaugeSublevel` says every `K_C` is
compact in `ell^1`; the continuous inclusion `ell^1 -> ell^2` makes it compact in `H`. Therefore
the unit ball image is relatively compact and `j` is compact. Finite-support sequences lie in `D`
and are dense in `H`, so the range is dense. It is proper, for example
`x_n=(n+1)^(-1)` after any standard square-summable/non-summable adjustment such as
`x_n=(n+1)^(-1)` lies in `ell^2` but not `ell^1`. QED.

### Theorem 3.2 — dense meagre executable core

As a subset of `H`, `D` is dense, proper, sigma-compact, `F_sigma`, and meagre.

#### Proof [PROVED HERE]

The corpus exhaustion theorem gives

\[
D=\bigcup_{N\in\mathbb N}K_N.
\]

Each `K_N` is compact in `H`, hence closed. No compact subset of the infinite-dimensional normed
space `H` has nonempty interior: otherwise a translate and rescaling would make the closed unit
ball compact, contradicting Riesz's lemma. Thus every `K_N` is nowhere dense. Their countable
union is sigma-compact, `F_sigma`, and meagre. Density and properness are Theorem 3.1. QED.

### Theorem 3.3 — response forces category escape

Let `x_k in D`, suppose `j(x_k)->0` in `H`, and suppose `M(x_k)->c != 0`. Then

\[
G(x_k)\longrightarrow+\infty.
\]

In particular `M:(D,G)->C` is continuous, but it is not sequentially closable relative to
`j:D->H`.

#### Proof [PROVED HERE]

Continuity on `(D,G)` is the defining estimate `|M(x)|<=G(x)`. If `G(x_k)` did not tend to
infinity, some subsequence would lie in one `K_C`. Compactness of `K_C` in `ell^1` gives a further
subsequence converging in `ell^1` to some `y in K_C`. Its `ell^2` limit is also `y`, while the
original Hilbert convergence forces `y=0`. Continuity of the `ell^1` codiagonal then gives
`M(x_k)->0` on that subsequence, contradicting `c!=0`.

For an explicit nonclosability witness set

\[
u_N=N^{-1}\sum_{n=1}^Ne_n.
\]

Then `||u_N||_2=N^(-1/2)->0`, `M(u_N)=1`, and

\[
G(u_N)=1+\frac{2}{N}\sum_{n=1}^Nn=N+2\to\infty.
\]

QED.

### Theorem 3.4 — countable compact-route atlases never cover

Let `H` be an infinite-dimensional Banach space. For each `m in N`, let `E_m` be a Banach space
and `T_m:E_m->H` a compact linear map. Then

\[
H\setminus\bigcup_m T_m(E_m)
\]

is residual and dense. In particular no finite, countable, or recursively enumerable family of
compactly embedded route gauges covers the observer completion.

#### Proof [PROVED HERE]

Write `B_m(n)` for the closed radius-`n` ball of `E_m`. Compactness of `T_m` says the closure of
`T_m(B_m(n))` is compact in `H`; infinite dimensionality makes that closure nowhere dense. Since

\[
T_m(E_m)=\bigcup_{n\ge1}T_m(B_m(n)),
\]

the union of all route images is contained in a countable union of nowhere-dense compact sets.
Baire's theorem makes its complement residual and dense. QED.

## 4. Cross-organ consequence

The theorem fuses three independently formalized organs.

1. Formation-depth properness supplies compact gauge sublevels and their exhaustion.
2. Shell codiagonal rigidity supplies the constant-response nonclosability witness.
3. Completed Green/incidence comparison has the same shape: an algebraic finite-jet range is dense
   and nonclosed in its Hilbert completion, while the infinite admitted horizon lies in
   `closure(range) \ range`.

The shared law is therefore not ordinary curvature or Fredholm index. It is a **change of
executable category**: completion turns a complete fine source into a first-category subspace of a
coarser observer, and horizontal charge survives exactly by escaping every fine compact set.
Theorem 3.4 also proves that adding countably many compact/nuclear/local route completions cannot
repair this failure. One operation with essential, noncompact coverage is mathematically required.

## 5. Exact no-go and positive survivor

- **Exact killing mechanism:** Pettis/automatic-continuity arguments require a nonmeagre subgroup
  or a complete ambient-domain topology. The actual executable domain is a dense meagre `F_sigma`
  subgroup. Borel regularity does not repair this: `(D,G)` is Polish and its inclusion has Borel
  image, yet the codiagonal remains nonclosable in `H`.
- **Strongest positive survivor:** every nonzero recovered horizontal response has quantitatively
  certified formation-depth escape. Any successful selection theorem must either prove that the
  literal source recovery acts on a second-category ambient domain or prove a source law that
  forbids this escape. Merely asking for measurability, graph closedness in the fine norm, compact
  sublevels, or Baire genericity cannot work.
- **New insight:** off-line completion is not an exceptional point inside the source topology. It
  is a legal continuous functional on a fine Polish source whose whole image is exceptional in the
  observer topology. This explains why bounded, normal, nuclear, Fredholm, and finite-work repairs
  repeatedly stop at the same wall.
- **Status:** dependency-closed paper proof. Lean parents already prove compactness, exhaustion,
  and nonclosability; exact meagreness and escape fusion remain to be formalized.

## 6. RH boundary

This theorem does not prove RH. It narrows the missing mechanism sharply. A route-independent RH
closure would follow from a source theorem placing the actual horizontal recovery on a
second-category domain in the observer completion: a nonmeagre linear subgroup of a Banach space
with the Baire property is open, hence all of `H`; ambient automatic continuity would then combine
with `boundedFormationRecoveryRigidityLaw` to force the constant horizontal coefficient to zero.

The corpus proves the opposite for the current finite-work domain. Therefore second-category
admission must be generated by a genuinely new source operation, not declared as regularity.

## Log

- 2026-09-02 — extracted from fresh Lean audit; Baire automatic-continuity proposal retired and
  category-escape survivor proved.
