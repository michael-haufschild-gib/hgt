# The graded-adjoint square law for \(K_{\mathbb R}\)

- **ID:** `kreal-graded-adjoint-square-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `kreal-quaternionic-ccm-cokernel` · Attacks G--H
- **Statement:** left multiplication by a self-adjoint grading followed by adjoint is a
  conjugate-linear operator whose square is the grading automorphism.

## Goal

Isolate the exact unconditional algebraic mechanism that produces Deninger's
\(\sigma^2=(-1)^i\) coefficient law, and state precisely which additional source grading a CCM
construction must supply.  This theorem neither constructs arithmetic cohomology nor asserts
positivity.

## Theorem

`[LITERATURE / PROVED HERE]` Let \(A\) be a complex associative \(*\)-algebra and let
\(\gamma\in A\) satisfy
\[
  \gamma^*=\gamma,\qquad \gamma^2=1.
\]
Define
\[
  \alpha_\gamma(a)=\gamma a\gamma,\qquad
  \kappa_\gamma(a)=\gamma a^*.
\]
Then:

1. \(\alpha_\gamma^2=\mathrm{id}\);
2. \(\kappa_\gamma\) is additive and conjugate-linear;
3. \(\kappa_\gamma^2=\alpha_\gamma\);
4. \(\kappa_\gamma\) preserves both eigenspaces
   \(A^\varepsilon=\{a:\alpha_\gamma(a)=\varepsilon a\}\), for
   \(\varepsilon\in\{+1,-1\}\);
5. on \(A^\varepsilon\), \(\kappa_\gamma^2=\varepsilon\,\mathrm{id}\).

Consequently \(A^+\) has an ordinary real structure and \(A^-\) has a quaternionic structure.

If, in addition, \(\pi:B\to A\) is a \(*\)-representation with
\(\alpha_\gamma(\pi(b))=\pi(b)\), and \(F\in A\) satisfies
\(\alpha_\gamma(F)=-F\), then
\[
  [F,\pi(b)]\in A^-.
\]
Every product
\[
  \pi(b_0)[F,\pi(b_1)]\cdots[F,\pi(b_n)]
\]
belongs to \(A^{(-1)^n}\).  Hence its ambient homogeneous operator sector carries the
\(K_{\mathbb R}\) square \((-1)^n\).

## Proof

Because \(\gamma^2=1\),
\[
  \alpha_\gamma^2(a)
   =\gamma(\gamma a\gamma)\gamma=a.
\]
The adjoint is additive and conjugate-linear, so the same is true of
\(a\mapsto\gamma a^*\).  Using \(\gamma^*=\gamma\),
\[
  \kappa_\gamma^2(a)
   =\gamma(\gamma a^*)^*
   =\gamma a\gamma
   =\alpha_\gamma(a).
\]

If \(\alpha_\gamma(a)=\varepsilon a\), adjunction gives
\(\gamma a^*\gamma=\varepsilon a^*\).  Multiplying this identity on the left by \(\gamma\)
gives \(a^*\gamma=\varepsilon\gamma a^*\).  Therefore
\[
  \alpha_\gamma(\kappa_\gamma(a))
   =\gamma(\gamma a^*)\gamma
   =a^*\gamma
   =\varepsilon\gamma a^*
   =\varepsilon\kappa_\gamma(a).
\]
Thus \(\kappa_\gamma\) preserves \(A^\varepsilon\), and the already proved identity
\(\kappa_\gamma^2=\alpha_\gamma\) restricts to
\(\kappa_\gamma^2=\varepsilon\,\mathrm{id}\).

For the last statement, write \(\delta(b)=[F,\pi(b)]\).  Since \(\alpha_\gamma\) is an
algebra automorphism,
\[
  \alpha_\gamma(\delta(b))
   =[\alpha_\gamma(F),\alpha_\gamma(\pi(b))]
   =[-F,\pi(b)]
   =-\delta(b).
\]
Products of homogeneous elements multiply their signs.  The coefficient \(\pi(b_0)\) is even
and there are \(n\) odd commutators, giving parity \((-1)^n\).  No analytic or arithmetic
hypothesis is used.

## Exact boundary

The theorem supplies a \(K_{\mathbb R}\) structure on the ambient homogeneous operator sectors.
It does **not** prove that those sectors calculate the CCM relative cyclic cokernel.  A standard
even doubling manufactures \(\gamma\) but can double the trace and zero multiplicities.  The
arithmetic open core is therefore a no-doubling, \(C_K\)-equivariant relative Chern
quasi-isomorphism from an intrinsic chiral sector to the single CCM realization.

## Novelty audit

The identity is elementary graded \(*\)-algebra/Fredholm-module algebra and is not claimed as new
scientific knowledge.  Searches of the project found no existing formal statement.  Deninger
supplies the target \(K_{\mathbb R}\) sign, while standard even Fredholm modules supply the
coefficient/phase parity used in the final paragraph.

Lean module:
`GaloisForLFunctions.RHTower.KRealGradedAdjoint`.

Formal capstones:

- `gradedAdjoint_sq`;
- `gradedAdjoint_sq_of_even`;
- `gradedAdjoint_sq_of_odd`;
- `quantizedCommutatorProduct_homogeneous`;
- `quantizedForm_homogeneous`;
- `gradedAdjointₛₗ`.

## Gates

- [x] 0 → 1 in-progress: exact source-pure statement and arithmetic boundary identified
- [x] 1 → 2 fully-proven: complete proof above; no open dependency
- [x] 2 → 3 formalized: leaf build green; axiom audit reports only `propext`; formal lint passes
- [ ] 3 → 4 publication-ready: not intended as a standalone new result

## Log

- 2026-07-25 — extracted as the strongest dependency-closed survivor of the quantized-calculus
  attacks.  No numerical evidence and no RH assumption used.
- 2026-07-25 — formalized in `KRealGradedAdjoint.lean`; minimal
  `lake env lean GaloisForLFunctions/RHTower/KRealGradedAdjoint.lean` passed; final
  `lake build GaloisForLFunctions.RHTower.KRealGradedAdjoint` passed; formal lint passed.
