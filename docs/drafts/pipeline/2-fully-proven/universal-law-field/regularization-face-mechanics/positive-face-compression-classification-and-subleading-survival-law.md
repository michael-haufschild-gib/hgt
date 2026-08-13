# Positive-face compression classification and subleading-survival law

- **ID:** `ulf-rfm-positive-face-compression`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper) / POSITIVE SURVIVOR OF A FAILED FIELD CONJECTURE
- **Source:** `docs/drafts/pipeline/1-in-progress/universal-law-field/stuck-route-obstruction-matrix.md`
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [DEPENDENCY-CLOSED] [FOURTH REGULARIZATION BRANCH]`
  `[POSITIVE FACE COMPRESSION] [JOINT FORMATION CLASSIFICATION] [BRIDGE] [NOT RH]`
- **Formal status:** Certified by `HTGeometry.PositiveFaceCompression`; Stage-3 certificate linked
  below.
- **Statement:** A fixed positive Gram observer makes a divergent positive pencil finite exactly
  when its carrier lies in the leading Gram kernel; on that face the entire subleading Gram survives
  unchanged.

## 1. Goal

The frozen regularization trilemma claimed that every finite observer of a divergent positive
source must become leading-order blind, leave the positive cone by subtraction, or reconstruct a
limiting positive measure. That classification is false. Positive compression to the null face of
the divergent leading form is a fourth branch.

The purpose of this card is not to rename shorting or compression theory. It closes the failed
field conjecture by the strongest exact survivor: a complete classification of fixed linear Gram
observers, including simultaneous observation of a finite family of divergent sources.

## 2. Setup

Let `H`, `Y`, and `U` be real or complex Hilbert spaces. Let

\[
 B,D:H\longrightarrow U,
 \qquad J:Y\longrightarrow H
 \tag{PFC.1}
\]

be bounded linear maps. Think of `B` as the leading feature map, `D` as the subleading feature map,
and `J` as the adjoint-side carrier of a fixed observer. For `t>=0`, define the observed positive
Gram energy

\[
 E_t(y)=t\,\|BJy\|^2+\|DJy\|^2.
 \tag{PFC.2}
\]

Equivalently, before compression the positive pencil is

\[
 G_t=tB^*B+D^*D,
 \tag{PFC.3}
\]

and its congruence compression is `J^*G_tJ`.

## 3. Main theorem

### Theorem 3.1 — fixed positive-face compression classification

The following are equivalent:

1. for every `y in Y`, the ray `t -> E_t(y)` is bounded above on `[0,infinity)`;
2. `BJ=0`;
3. `ran J subset ker B`.

When these conditions hold,

\[
 \boxed{E_t(y)=\|DJy\|^2\quad(t\ge0,y\in Y).}
 \tag{PFC.4}
\]

Thus the observer remains positive and finite while retaining the full subleading Gram `J^*D^*DJ`.
It is nonzero exactly when `DJ` is nonzero.

If `ker B={0}`, every pointwise-bounded fixed carrier has `J=0`. Therefore the fourth branch exists
precisely on a proper positive face: it cannot occur in the interior of the leading positive cone.

### Proof

Fix `y` and put `a=||BJy||^2`, `b=||DJy||^2`. Both are nonnegative. If `a>0`, then

\[
 E_t(y)=ta+b\longrightarrow+\infty.
\]

Pointwise boundedness therefore forces `a=0`, hence `BJy=0`. Since this holds for every `y`,
`BJ=0`. Conversely `BJ=0` reduces `(PFC.2)` to `(PFC.4)`, which is constant in `t`. The equivalence
with `ran J subset ker B` is the definition of a composite kernel. If `ker B={0}`, then
`ran J={0}`, hence `J=0`. QED.

### Theorem 3.2 — simultaneous face formation

Let `I` be a finite set, let `B_i:H->U_i` be bounded linear maps, and let `D_i:H->U_i` be arbitrary
bounded subleading maps. Define

\[
 E_{i,t}(y)=t\|B_iJy\|^2+\|D_iJy\|^2.
 \tag{PFC.5}
\]

All rays `E_(i,t)(y)` are pointwise bounded, for every `i` and `y`, exactly when

\[
 \boxed{\operatorname{ran}J\subseteq\bigcap_{i\in I}\ker B_i.}
 \tag{PFC.6}
\]

If `A:H->direct_sum_i U_i` is the analysis map `Ax=(B_i x)_i`, then this common face is `ker A`.
Equivalently it is the radical of the positive formation Laplacian

\[
 L=\sum_iB_i^*B_i,
 \qquad
 \ker L=\bigcap_i\ker B_i.
 \tag{PFC.7}
\]

On the common face every subleading compressed Gram `J^*D_i^*D_iJ` survives unchanged.

### Proof

Apply Theorem 3.1 to each `i`; intersect the resulting kernel conditions. For `(PFC.7)`,

\[
 \langle Lx,x\rangle=\sum_i\|B_ix\|^2,
\]

so `Lx=0` iff every summand vanishes. QED.

## 4. Sharp counterexample to the frozen trilemma

Take `H=R^2`,

\[
 B(x_1,x_2)=x_1,
 \qquad D(x_1,x_2)=x_2,
 \qquad Jy=(0,y).
 \tag{PFC.8}
\]

Then

\[
 G_t=\begin{pmatrix}t&0\\0&1\end{pmatrix},
 \qquad E_t(y)=y^2.
 \tag{PFC.9}
\]

The source is positive and diverges in the first direction. The observer is positive, finite, and
retains the complete subleading coefficient `1`. It does not:

1. divide by a leading normalizer;
2. factor through leading-order asymptotic data;
3. subtract any positive mass or leave the positive cone;
4. exhibit or reconstruct a limiting positive measure.

It changes carrier by selecting the exposed null face of the leading Gram. This is the missing
fourth branch requested by the frozen conjecture itself.

## 5. Exact boundary and higher interpretation

The theorem does **not** establish a new universal field. Positive compression, support faces,
shorted operators, and formation Laplacians are classical or already present in the corpus. Its
field-level consequence is a correction of the search target:

> Divergence is not classified by normalization/subtraction/circularity. The missing datum is which
> source law authorizes formation or transport of the observer carrier relative to the leading
> positive radical.

That problem is dynamic. A chosen fixed face can hide arbitrary divergent directions. Selection
requires the face itself to be source-generated, cofinally compatible, and sufficiently
intersecting to leave no illicit adaptive carrier. Existing formation-Laplacian mechanics already
classifies the static common-kernel and closed-range parts; they must not be repackaged as a new
theory.

### 5.1 Fourth-organ test: the UV corner has no nonzero finite compact face

The theorem makes a risky prediction in the Sonin UV organ: if a finite quadratic packet can be
made compact by positive-face selection inside its coefficient space, then the corresponding
coefficient packet must have a nonzero kernel in the Calkin quotient. The corpus proves the
opposite. For every finite set of distinct primes, the map

```text
A |-> [sum_(i,j) A_ij L_i^* L_j]  in  B(H)/K(H)
```

is injective. Equivalently, a finite prime quadratic combination is compact exactly when its
coefficient matrix is zero. This is the theorem
`finitePrimeArchimedeanEulerGram_not_isCompactOperator_of_ne_zero`, formalized in
`RHTower.SoninEulerFiniteGramLower` and certified by
`sonin-prime-quadratic-calkin-matrix-injectivity.md`.

Therefore the compact-ideal analogue of the leading null face is `{0}`. Positive face compression
does not repair W8 within the finite prime-quadratic grammar. Any surviving UV construction must be
genuinely infinite, nonlinear, smoothed, or use a different polarization. This is a fourth-organ
falsification of the mechanism's universality, not a route-specific caveat.

## 6. Sharp scope

1. `J` is fixed as `t` varies. Adaptive carriers can track moving kernels and require separate
   compactness/properness laws.
2. The classification is pointwise in `y`. Uniform operator-norm bounds add closed-range and frame
   questions already covered by formation-Laplacian mechanics.
3. Positivity is essential for the exact kernel conclusion. Signed leading coefficients can cancel.
4. The theorem says nothing about which face the arithmetic source permits.
5. It yields no RH selection consequence.

## 7. Parent mathematics and collision audit

The mechanism belongs to positive-operator compression/shorting and Gram factorization. Nearby
parents include Arlinskiĭ's work on
[Kreĭn shorted operators](https://arxiv.org/abs/1109.4020), positive-semidefinite matrix-pencil
analysis such as [Nguyen--Nguyen](https://arxiv.org/abs/2302.14352), and the corpus's own
`source-response-laplacian-properness-pluecker-and-adaptive-escape-law.md`. The theorem is retained
as an exact bridge and as the mandatory positive survivor of a failed central conjecture, not as a
priority claim.

## 8. Lean certificate

The Gram-factor form is formalized directly:

```text
pointwise bounded (t * ||B (J y)||^2 + ||D (J y)||^2)
  <-> B.comp J = 0.
```

The module also certifies simultaneous-family formation, the injective-leading boundary, unchanged
subleading energy, and the explicit diagonal fourth branch. It is wired into
`HTGeometry.UniversalLawField`. Direct and umbrella builds, lint, and axiom audit passed. See
`docs/drafts/pipeline/3-formalized/universal-law-field/regularization-face-mechanics/positive-face-compression-classification-and-subleading-survival-law-formalized.md`.

## 9. Log

- 2026-08-13 — extracted as the exact fourth branch falsifying the frozen regularization trilemma;
  paper proof closed; external collision audit downgrades the mechanism to bridge/survivor.
- 2026-08-13 — tested against the Sonin UV organ; finite Calkin-packet injectivity forces the
  compact face to be zero, so the fourth branch cannot solve W8 at finite prime-quadratic level.
