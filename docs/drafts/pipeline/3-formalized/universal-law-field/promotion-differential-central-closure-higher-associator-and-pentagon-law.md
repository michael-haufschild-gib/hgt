# Promotion differential, central closure, higher associator, and pentagon law

- **ID:** ULF-OPM-6
- **Stage:** 3-formalized
- **Type:** CROSS-PROMOTION SELECTION / COHERENCE-GENESIS MECHANISM
- **Statement:** A binary compensator closes as an associative central promotion exactly when its
  promotion differential vanishes. Otherwise that differential is a nonzero ternary associator,
  and it automatically satisfies the next pentagon coherence law.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [CENTRAL VERSUS HIGHER SELECTION] [GAUGE-INVARIANT] [LEAN-CERTIFIED] [NOT RH]

## 1. Binary promotion attempt

Let `M` be an additive monoid, let `A` be an additive abelian group, and let

\[
 \kappa:M\times M\longrightarrow A
 \tag{PD.1}
\]

be a proposed binary compensator. On `M x A` define

\[
 (x,a)\star_\kappa(y,b)
 =\bigl(x+y,\ a+b+\kappa(x,y)\bigr).
 \tag{PD.2}
\]

Define the promotion differential

\[
 \mathfrak a_\kappa(x,y,z)
 =\kappa(x,y)+\kappa(x+y,z)-\kappa(y,z)-\kappa(x,y+z).
 \tag{PD.3}
\]

This is not named curvature. It is the exact residual left when a binary promotion is executed
twice in the two possible schedules.

## 2. Central-closure selector

### Theorem 2.1

The promoted operation `star_kappa` is associative if and only if

\[
 \mathfrak a_\kappa(x,y,z)=0
 \quad\text{for all }x,y,z\in M.
 \tag{PD.4}
\]

### Proof

The first coordinates of the two triple products agree by associativity in `M`. Their second
coordinates differ by exactly `(PD.3)`:

\[
 ((x,a)\star(y,b))\star(z,c)
 -(x,a)\star((y,b)\star(z,c))
 =\mathfrak a_\kappa(x,y,z).
\]

Hence all triple products agree exactly when the residual vanishes. QED.

This is a mode-selection law:

- `a_kappa=0`: binary central/history promotion closes;
- `a_kappa!=0`: no associative binary promotion with this compensator exists, so its failure must
  be abandoned, quotiented away, or promoted again.

## 3. Coherent higher birth

### Theorem 3.1 -- pentagon identity

For every compensator `kappa`, without assuming `(PD.4)`,

\[
\begin{aligned}
 &\mathfrak a_\kappa(w,x,y)
 +\mathfrak a_\kappa(w,x+y,z)
 +\mathfrak a_\kappa(x,y,z)\\
 &\qquad=
 \mathfrak a_\kappa(w+x,y,z)
 +\mathfrak a_\kappa(w,x,y+z).
\end{aligned}
\tag{PD.5}
\]

### Proof

Expand `(PD.3)`. Every value of `kappa` cancels in pairs after using associativity in `M`. QED.

Thus failure of the binary promotion is not arbitrary new data. The same execution mechanism that
produces the ternary residual also forces its first higher coherence. This is the low-degree law

\[
 \delta^2=0.
 \tag{PD.6}
\]

No higher object was postulated to obtain it.

## 4. Gauge invariance

For any unary calibration `b:M->A`, set

\[
 (\partial b)(x,y)=b(x)+b(y)-b(x+y),
 \qquad
 \kappa^b=\kappa+\partial b.
 \tag{PD.7}
\]

### Theorem 4.1

\[
 \mathfrak a_{\kappa^b}=\mathfrak a_\kappa.
 \tag{PD.8}
\]

### Proof

Substitute `(PD.7)` into `(PD.3)`. Every unary term cancels. QED.

Therefore the central-versus-higher selection does not depend on the chosen unary splitting. The
compensator is gauge-dependent; its promotion differential is not.

## 5. Exact calibrations

### 5.1 Central-history closure

On `M=Z^2`, `A=Z`, define

\[
 \kappa((x,y),(x',y'))=xy'.
 \tag{PD.9}
\]

Then `a_kappa=0`; `(PD.2)` is the integer Heisenberg multiplication. Its asymmetric compensator
retains order history while remaining associative.

### 5.2 Forced higher associator

On additive integers define

\[
 \kappa_3(x,y)=x^2y.
 \tag{PD.10}
\]

Direct expansion gives

\[
 \mathfrak a_{\kappa_3}(x,y,z)=2xyz.
 \tag{PD.11}
\]

In particular `a_kappa3(1,1,1)=2`, so the binary promotion is not associative. Nevertheless its
ternary residual obeys `(PD.5)` exactly. This is a finite-formula, non-route example in which
failure of one law produces the next coherent law.

## 6. What has been learned

The first two non-strict modes are selected by one derived test:

\[
 \boxed{
 \text{binary compensator}
 \xrightarrow{\delta}
 \text{ternary associator}
 }
 \tag{PD.12}
\]

- vanishing means central promotion closes;
- nonvanishing means higher promotion is forced;
- applying the mechanism again gives zero at the next coherence boundary;
- unary recalibration cannot change the verdict.

This is stronger than saying both modes exist. It is an exchange law governing when one mode
terminates and when it births the other.

## 7. Sharp boundaries

1. The theorem is algebraic; topology and singular admission are not yet integrated.
2. A nonzero associator need not be physically or arithmetically admitted.
3. `delta^2=0` gives coherence, not convergence of an infinite promotion tower.
4. Nontrivial cohomology, minimality, and universality under changes of coefficient doctrine require
   further laws.
5. No proof route, positivity, recurrence, HT, or RH claim appears.

## Lean certification

Formalized without project axioms in
`GaloisForLFunctions.HTGeometry.ConstitutivePromotionDifferential`:

1. promoted binary operation and exact associator residual;
2. associativity iff residual vanishes;
3. pentagon identity for every compensator;
4. gauge invariance under unary coboundaries;
5. Heisenberg cocycle closure;
6. cubic compensator formula and nonzero associator;
7. bundled central-versus-higher promotion theorem.

The module is wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Log

- 2026-08-09 -- derived promotion differential as exact selector between central closure and higher
  coherence birth.
- 2026-08-11 -- Lean surface audited complete against the card; promoted to stage 3.
