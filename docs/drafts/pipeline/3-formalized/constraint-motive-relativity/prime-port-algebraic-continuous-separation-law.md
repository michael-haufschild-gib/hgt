# Prime-port algebraic--continuous separation law

- **ID:** `cmr-prime-port-algebraic-continuous-separation`
- **Stage:** 3-formalized
- **Type:** THEOREM / SOURCE-SPECIFIC TOPOLOGICAL CALIBRATION
- **Status:** `[PAPER-PROVED] [HOSTILE ACCEPT AFTER INTERPRETATION REPAIR]`
  `[EXACT HAUSDORFF COTANGENT-LOSS DEFECT]`
  `[CLASSICAL SYMPLECTIC/TOPOLOGICAL INGREDIENTS] [CORPUS INTERFACE]`
  `[NOT RH] [LEAN-FORMALIZED UNCONDITIONALLY]`
- **Formalized companion:** `prime-port-algebraic-continuous-separation-law-formalized.md`
- **Stage-1 field:**
  `../../1-in-progress/constraint-motive-relativity/polarized-constraint-cotangent-geometry.md`.
- **Parent:**
  `../constraint-relativity/prime-coframe-completion-port-uncertainty-law.md`.
- **Statement:** Algebraic prime augmentation reduction leaves one hyperbolic port. Completing in
  `ell^1` preserves that port, while completing in `ell^p`, `1<p<infinity`, or `c0` makes the
  augmentation constraint dense and makes Hausdorff reduction zero. With quotient topology
  transported correctly, completion and reduction commute; exact defect instead measures loss
  from algebraic/discrete reduction to continuous Hausdorff realization.

## Goal

Identify an exact higher obstruction that is not another RH-equivalent selector. Explain why the
same all-prime relation has a faithful one-port reduction in one observer topology and no
continuous port in another. Couple the corpus's prime-coframe topology wall to a coordinate-free
cotangent reduction square.

## 1. Algebraic prime cotangent space

Let `P` be a countably infinite set of primes and put

\[
 K_0=c_{00}(\mathcal P),
 \qquad
 \varepsilon(x)=\sum_{p\in\mathcal P}x_p,
 \qquad
 I_0=\ker\varepsilon.
\tag{RC.1}
\]

The algebraic dual is `K_0^*=C^P`, with evaluation well-defined because every `x` has finite
support. On

\[
 \mathbb H_0=K_0\oplus K_0^*
\]

use the canonical cotangent form

\[
 \omega((x,\alpha),(y,\beta))=\alpha(y)-\beta(x).
\tag{RC.2}
\]

Regard `I_0` as an isotropic subspace of the first summand.

### Theorem 1 — algebraic one-port reduction

Let `1=(1,1,...) in C^P`. Then

\[
 I_0^\omega=K_0\oplus\mathbb C\mathbf 1
\tag{RC.3}
\]

and the coisotropic quotient is canonically

\[
 \boxed{
 I_0^\omega/I_0
 \cong (K_0/I_0)\oplus\mathbb C\mathbf1
 \cong\mathbb H(\mathbb C).}
\tag{RC.4}
\]

#### Proof

A covector `alpha in K_0^*` annihilates `I_0` exactly when it has equal values on all standard
basis vectors: every difference `e_p-e_q` belongs to `I_0`, so
`alpha_p-alpha_q=0`. Hence `I_0^perp=C 1`, proving `(RC.3)`. Augmentation induces
`K_0/I_0~=C`; evaluation of `1` on a class is its augmentation. Therefore the quotient pairing is
the standard hyperbolic pairing. `[PROVED HERE]`

This theorem is the hostile counterexample to the false claim that large prime Witt rank forces a
singular one-port reduction. Algebraically the reduction is regular.

## 2. Continuous Hausdorff realization

Let `X` be a Banach sequence completion containing `K_0` densely. Use its continuous cotangent
space

\[
 \mathbb H(X)=X\oplus X'
\tag{RC.5}
\]

with the same evaluation form. For a subspace `I subset X`, its symplectic orthogonal is

\[
 I^\omega=X\oplus I^\perp,
 \qquad
 I^\perp=\{\alpha\in X':\alpha(I)=0\}.
\tag{RC.6}
\]

If `I` is nonclosed, the topological quotient `I^omega/I` may be non-Hausdorff. Write `//_H` for
coisotropic quotient followed by Hausdorffization.

### Theorem 2 — the `ell^1` phase

In `X=ell^1(P)`, augmentation extends continuously, `closure(I_0)=ker epsilon` is closed of
codimension one, and

\[
 \boxed{
 \mathbb H(\ell^1)//_H\overline{I_0}
 \cong\mathbb H(\mathbb C).}
\tag{RC.7}
\]

#### Proof

The estimate `|epsilon(x)|<=||x||_1` gives continuity. Since `K_0` is dense in `ell^1`, finite
truncations of `x in ker epsilon` can be corrected in one fresh coordinate by the negative of
their finite sum; the correction tends to zero because the tails of `x` tend to zero in `ell^1`.
Thus `closure(I_0)=ker epsilon`. Its annihilator is `C epsilon`, while
`ell^1/ker epsilon~=C`. Equations `(RC.6)` and the quotient pairing give `(RC.7)`.
`[PROVED HERE]`

### Theorem 3 — Hilbert and `c0` erasure phases

For `X=ell^p(P)`, `1<p<infinity`, and for `X=c_0(P)`, the subspace `I_0` is dense. Consequently

\[
 I_0^\perp=0,
 \qquad
 I_0^\omega/I_0\cong X/I_0\text{ is non-Hausdorff},
 \qquad
 \boxed{\mathbb H(X)//_H I_0=0.}
\tag{RC.8}
\]

#### Proof

It is enough to approximate a finite-support vector `x` by elements of `I_0`. Put
`S=epsilon(x)`. Choose `N` fresh prime coordinates and set

\[
 y_N=x-\frac{S}{N}\sum_{j=1}^{N}e_{q_j}.
\tag{RC.9}
\]

Then `epsilon(y_N)=0`. For `1<p<infinity`,

\[
 \|x-y_N\|_p=|S|N^{1/p-1}\longrightarrow0,
\]

and in `c_0`, `||x-y_N||_infinity=|S|/N->0`. Since `K_0` is dense in each `X`, so is `I_0`.
Every continuous functional annihilating a dense subspace is zero, so `(RC.6)` gives
`I_0^omega=X direct-sum 0`. The quotient `X/I_0` has zero Hausdorffization because `I_0` is dense.
This proves `(RC.8)`. `[PROVED HERE]`

In particular the standard Hilbert chart `ell^2` erases the port after Hausdorff reduction.

## 3. The algebraic--continuous separation defect

Dualization reverses arrows, so there is not one untyped arrow between the two hyperbolic
reductions. The coordinate-free comparison is a primal/dual mate pair. Completion induces

\[
 q_X:K_0/I_0\longrightarrow X/\overline{I_0},
\tag{RC.10}
\]

while restriction of continuous covectors induces the opposite-direction map

\[
 a_X:(\overline{I_0})^\perp\longrightarrow I_0^\perp.
\tag{RC.11}
\]

Here `I_0^perp` on the right is computed in the algebraic dual. Define the Hausdorff
cotangent-loss pair

\[
 \mathfrak K_X=\ker q_X\oplus\operatorname{coker}a_X.
\tag{RC.12}
\]

In this prime-port model, algebraic evaluation descends to a perfect pairing between the two
summands, so `mathfrak K_X` is itself a hyperbolic port. This mate-pair definition avoids inventing
a completion map from the full algebraic dual `C^P` to the continuous dual `X'`.

### Corollary 4 — exact phase jump

\[
 \boxed{
 \mathfrak K_{\ell^1}=0,
 \qquad
 \mathfrak K_{\ell^p}\cong\mathbb H(\mathbb C)\ (1<p<\infty),
 \qquad
 \mathfrak K_{c_0}\cong\mathbb H(\mathbb C).}
\tag{RC.13}
\]

#### Proof

For `ell^1`, both `(RC.10)` and `(RC.11)` are isomorphisms between one-dimensional spaces. For
the other stated completions, `X/closure(I_0)=0` and `(closure(I_0))^perp=0`, while
`K_0/I_0=C` and `I_0^perp=C1`. Hence both the kernel and cokernel in `(RC.12)` are
one-dimensional and pair by evaluation. `[PROVED HERE]`

Thus the port is not an invariant of the algebraic relation alone. It is an invariant of relation
plus observer topology and separation doctrine.

### Corollary 4.1 — hostile functor-order correction

Equip the algebraic quotient `K_0/I_0` with the quotient seminorm induced from `X`. Its separated
completion is canonically `X/closure(I_0)`. Therefore ordinary Hausdorff completion and quotient
reduction **do commute** in this example. For `ell^p`, `p>1`, and `c0`, the algebraic one-port
quotient has zero induced seminorm and completes to zero.

Hence `mathfrak K_X` is not a commutator of correctly typed completion/reduction functors. It
compares two doctrines: algebraic/discrete reduction and continuous Hausdorff reduction. The
distinction is load-bearing. `[PROVED HERE]`

## 4. Source meaning and scope

For the literal valuation coframe, each prime basis direction is detected independently. The
augmentation is also literal on the marked prime atom: every prime atom has value one. The theorem
therefore uses actual source coefficients, but it does not assert that the prime classes are
Hochschild boundaries or select any Xi zero.

The result explains a recurring corpus obstruction:

> making the all-prime one-port quotient continuous (`ell^1`) excludes unsigned divergent radial
> histories, while a Hilbert completion admitting square-summable histories makes the port
> discontinuous and its constraint dense.

The generic symplectic facts are classical. The source-specific content is the exact prime
augmentation calculation and its algebraic-to-continuous separation defect.

## 5. Conjecture/failure loops

### Loop A — Witt rank forces singular reduction

**Failed:** Theorem 1 gives a regular algebraic reduction to one hyperbolic port.

**Survivor:** topology decides whether that reduction remains admitted after completion.

### Loop B — every reasonable completion preserves the port

**Failed:** Theorem 3 proves complete erasure in every `ell^p`, `p>1`, and in `c0`.

**Survivor:** the exact separation defect `(RC.13)` distinguishes observer topologies.

### Loop C — completion erasure proves RH

**Failed as irrelevant/circular:** the phase depends on chosen observer topology and occurs for the
prime augmentation independently of Xi zeros.

**Survivor:** any proposed common arithmetic/spectral/positive geometry must derive its topology
and prove which side of `(RC.13)` it occupies. Selecting a convenient topology by desired outcome
is invalid.

## 6. Consequences and predictions

1. No topology-free one-port reduction theorem can connect the prime coframe to physical Stokes
   geometry.
2. Any Hilbert-space realization claiming a nonzero continuous all-prime augmentation must use a
   nonstandard weight/domain; its port continuity criterion is testable.
3. A route transition may be algebraically exact and still lose its entire physical port after
   Hausdorff completion.
4. A successful higher geometry needs algebraic/continuous comparison cells as primitive data;
   kernel, cokernel, Witt index, and energy alone cannot determine them.
5. The missing RH source law cannot be repaired merely by changing completion: `(RC.13)` changes
   observer visibility, not source nullhomology.

## 7. Literature boundary

Weak symplectic reduction, symplectic closure, cotangent doubles, and Tate lattices are established
mathematics. Current infinite-dimensional symplectic reduction identifies double orthogonals with
closure under suitable symplectic topologies. This card claims no generic novelty. Its role is a
  dependency-closed calibration for the new field: the literal all-prime source exhibits a nonzero,
  computable Hausdorff cotangent-loss defect.

## 8. No-go closure

- **Exact killing mechanism:** finite Witt rank does not force singularity; Theorem 1 is its
  counterexample.
- **Strongest positive survivor:** exact phase law `(RC.13)`.
- **New insight:** observer topology is part of geometry. Algebraic and continuous reductions can
  have different separated content even when correctly transported completion commutes with
  reduction.
- **Status:** dependency-closed paper proof; external machinery occupied; Lean formalization
  complete and unconditional.

## Log

- 2026-08-09 — created after hostile audit falsified the Witt-to-singularity inference. Closed
  algebraic, `ell^1`, `ell^p`, and `c0` phases.
- 2026-08-09 — hostile audit corrected interpretation: quotient with induced topology completes to
  `X/closure(I)`, so reduction and Hausdorff completion commute. Retained exact theorem as
  algebraic-to-continuous separation/cotangent-loss law.
