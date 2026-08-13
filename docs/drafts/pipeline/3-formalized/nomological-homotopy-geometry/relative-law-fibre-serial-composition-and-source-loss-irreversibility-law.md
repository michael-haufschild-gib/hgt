# Relative law-fibre serial composition and source-loss irreversibility law

- **Stage:** 3 — formalized in Lean 4
- **Lean gate:** [LEAN-PROVED] [AXIOM AUDITED] [UMBRELLA BUILD PASSED] (2026-08-13)
- **Status:** [PAPER-PROVED] [ROUTE-INDEPENDENT] [OBSERVER-COMPOSITION]
  [POINTED INFINITY-CATEGORY] [NOT RH] [LEAN FORMALIZED — DOCUMENTED IN PLACE]

## 1. Setup

Let \(\mathcal C\) be a pointed infinity-category with finite limits. For a pointed morphism
\(f:X\to Y\), define

\[
 K_f=\operatorname{fib}(f)=X\times_Y *.
\tag{RLF.1}
\]

NHG applies this construction in the underlying pointed category of anchored filtered
\(Q\)-objects. Gauges are structured equivalences; observers are general declared vertical
morphisms.

## 2. Serial composition theorem

### Theorem 2.1 — relative law-fibre sequence

For composable pointed morphisms

\[
 X\xrightarrow{f}Y\xrightarrow{g}Z,
\tag{RLF.2}
\]

there is a canonical fibre sequence

\[
 \boxed{
 K_f\longrightarrow K_{gf}\longrightarrow K_g.}
\tag{RLF.3}
\]

If the tangent category is stable, (RLF.3) induces an exact triangle

\[
 \mathbb T K_f\longrightarrow
 \mathbb T K_{gf}\longrightarrow
 \mathbb T K_g\longrightarrow
 \mathbb T K_f[1].
\tag{RLF.4}
\]

Consequently serial observer loss is generally an extension, not a direct sum. The connecting map

\[
 \partial:H^n(\mathbb T K_g)\longrightarrow
 H^{n+1}(\mathbb T K_f)
\tag{RLF.5}
\]

is the exact interaction invariant of the two stages.

### Corollary 2.2 — source-loss irreversibility

For every \(n\geq1\), if a source class \(x\in\pi_nX\) satisfies \(f_*x=0\), then

\[
 (gf)_*x=0.
\tag{RLF.6}
\]

No later serial observer can recover a source homotopy class already killed by an earlier observer.

This does not imply that every non-equivalence is irreversible. An observer may add excess target
directions without identifying source classes; a later retraction can remove that excess.

### Corollary 2.3 — exact cancellation boundary

If \(gf\) is an equivalence, then in the stable tangent category

\[
 \mathbb T K_g\simeq\mathbb T K_f[1].
\tag{RLF.7}
\]

Thus nontrivial stage fibres can coexist with a gauge composite only as a shifted exact
cancellation. Such cancellation removes observer-created extension data; by Corollary 2.2 it
cannot resurrect a source class killed by \(f\).

### Corollary 2.4 — parallel repair criterion

For a finite parallel family \(f_i:X\to Y_i\), let

\[
 f=(f_1,\ldots,f_m):X\longrightarrow\prod_iY_i.
\tag{RLF.8}
\]

Then for every \(n\geq1\),

\[
 \ker\pi_n(f)=\bigcap_i\ker\pi_n(f_i).
\tag{RLF.9}
\]

Parallel observers separate source homotopy classes exactly when their homotopy kernels have zero
intersection in every required degree. This is necessary for a joint gauge but does not by itself
prove essential surjectivity, descent, polarization recovery, or global holonomy reconstruction.

## 3. Proof

The map \(K_{gf}\to K_g\) is induced by \(f:X\to Y\). Its homotopy fibre over the basepoint is

\[
 \begin{aligned}
 K_{gf}\times_{K_g}*
 &\simeq
 (X\times_Z*)\times_{(Y\times_Z*)}*\\
 &\simeq X\times_Y*\\
 &=K_f.
 \end{aligned}
\tag{RLF.10}
\]

This proves (RLF.3). Stabilization sends fibre sequences to exact triangles, giving (RLF.4) and
its long exact cohomology sequence. If \(K_{gf}\simeq *\), exactness gives (RLF.7).

Equation (RLF.6) is functoriality:

\[
 (gf)_*x=g_*(f_*x)=0.
\]

For a finite product, \(\pi_n(\prod_iY_i)\cong\prod_i\pi_n(Y_i)\), so \(f_*x=0\) exactly when every
\((f_i)_*x=0\). This proves (RLF.9).

## 4. Hostile countermodel to an overstrong slogan

Let

\[
 f:k\longrightarrow k^2,\qquad f(x)=(x,0),
\]

and

\[
 g:k^2\longrightarrow k,\qquad g(x,y)=x.
\]

Then \(gf=\operatorname{id}_k\), while neither \(f\) nor \(g\) is an isomorphism. The map \(f\)
kills no source vector; it adds an excess target direction, which \(g\) later removes.

Therefore the statement “a later observer can never repair any earlier non-equivalence” is false.
The exact theorem is Corollary 2.2: source identifications are irreversible, while
observer-created excess can cancel through the extension law (RLF.3).

## 5. NHG consequence

The relative law-fibre is compositional. Any tangent, Spencer, holonomy, or completion functor used
as an NHG shadow must respect (RLF.3) whenever it preserves the relevant homotopy limits.
Independent scalar defect scores need not satisfy this law and cannot serve as universal field
strengths.

The nonlinear structured problem is to lift (RLF.3) from the underlying pointed
\(Q\)-objects to the full law equipment with coherent cyclic, polar, connection, and integrated
history data.

## 6. Sharp scope

1. Pointedness and finite homotopy limits are load-bearing.
2. The exact triangle requires stabilization; the fibre sequence does not.
3. The theorem controls source homotopy kernels, not arbitrary notions of information.
4. Polarization and analytic completion need not preserve homotopy fibres automatically.
5. No additive numerical curvature, action, arithmetic relation, or endpoint follows.

## Lean formalization status

- **Module:**
  `GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.RelativeLawFiber`
- **Source:**
  `formal/GaloisForLFunctions/HTGeometry/NomologicalHomotopyGeometry/RelativeLawFiber.lean`
- **Umbrella:** imported by
  `GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry`.
- **Stage handling:** promoted to Stage 3 after umbrella build and capstone axiom audit on 2026-08-13.

Exact coverage:

1. `CategoricalModel.serialFiberConeIsLimit` proves the universal finite-limit content of
   `(RLF.3)`: in every pointed category with pullbacks, `fib f` is the pullback of the canonical
   map `fib (g ∘ f) → fib g` over the zero object.  The canonical arrows and their zero composite
   are constructed explicitly.
2. `PointedModel.fiberFiberMapIso` gives the corresponding dependent-pair/path realization for
   pointed types, including preservation of the distinguished point.
3. `StableTangent.relativeFiberTriangle_distinguished` proves `(RLF.4)` as the shifted
   octahedral mapping-cone triangle in the homotopy category of cochain complexes.
4. `StableTangent.cancellationIso` proves `(RLF.7)`: when `g ∘ f` is an isomorphism, the
   connecting morphism is an isomorphism `fib g ≅ (fib f)[1]`.
5. `sourceLoss_irreversible` proves `(RLF.6)` for the induced pointed additive maps in every
   degree.
6. `ker_jointMap` and `jointMap_injective_iff` prove `(RLF.9)` and the exact parallel-separation
   criterion for arbitrary observer families (hence finite families).
7. `SplitCountermodel.splitCancellation` formalizes the hostile example
   `k → k² → k`: the composite is the identity although the inclusion is not surjective and the
   projection is not injective.

Verification completed with the required foreground leaf command:

```text
lake env lean GaloisForLFunctions/HTGeometry/NomologicalHomotopyGeometry/RelativeLawFiber.lean
```

Result: exit code `0`, no warnings.  Project-wide `lake build`, generated-index check, lint, and
scratch `#print axioms` audit remain reserved for the final all-card audit.
