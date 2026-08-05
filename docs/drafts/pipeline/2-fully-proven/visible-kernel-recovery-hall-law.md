# Visible-kernel recovery Hall law

- **ID:** visible-kernel-recovery-hall-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `static-local-complexity-law.md`, two-replica gate O4.12z25
- **Statement:** Forward overlap in a two-layer Hall problem need not be repaid at its full dimension. Visible quotient rank pays the exposed source directions, while an injective return map need recover only the kernel hidden inside already occupied output.

## Goal

Close the logical gap in the previous overlap-compensation route. That route demanded a reverse
channel as large as the complete forward-image overlap. For local two-replica commutators this is
unnecessarily strong: one source direction can generate a whole Pauli-orientation multiplet, so
overlap dimension can exceed source dimension. Correct invariant is kernel of visible quotient map.

## Universal theorem

Let a finite-dimensional space split into disjoint layers `S` and `W`. Let
`U_S <= S`, `U_W <= W`, and let `C <= W` be forward output generated from `U_S`. Suppose a linear
visible detector

\[
  F:U_S\longrightarrow Z
\]

satisfies

\[
 \operatorname{rank}F+\dim U_W\le \dim(U_W+C).                 \tag{1}
\]

Suppose also that there is an injective recovery map

\[
  R:\ker F\longrightarrow S                                      \tag{2}
\]

and total output contains `(U_W+C)+R(ker F)`. Then

\[
 \boxed{\dim(U_S+U_W)\le\dim Y_{\rm out}.}                       \tag{3}
\]

### Proof

Rank-nullity gives

\[
 \dim U_S=\operatorname{rank}F+\dim\ker F.                       \tag{4}
\]

The visible space lies in `W`, whereas recovered kernel lies in `S`; hence their sum is direct.
Using `(1)`, injectivity of `R`, and `(4)`,

\[
\begin{aligned}
 \dim\big((U_W+C)+R(\ker F)\big)
 &=\dim(U_W+C)+\dim\ker F\\
 &\ge \dim U_W+\operatorname{rank}F+\dim\ker F\\
 &=\dim U_W+\dim U_S.
\end{aligned}
\]

Since `U_S` and `U_W` are disjoint and displayed output is contained in `Y_out`, `(3)` follows.

## Two-replica Pauli instantiation

Let `B_(i,a)` be weight-one collective Pauli commutators and let `S` be their common kernel, the
sitewise diagonal-`SU(2)` singlet algebra. Let `P` be independent sitewise Clifford averaging on
the two-replica operator space. The exact one-site Clifford commutant is `span{I,F}`; iterating the
site averages gives `range P=S`. Put `W=ker P`. Product-local Clifford conjugation preserves the
full weight-at-most-two Pauli family, so it fixes the canonical maximum-defect subspace `U_*`.
Since `P` is an idempotent average of these conjugations,

\[
 U_*=U_S\oplus U_W,
 \qquad U_S=U_*\cap S,
 \qquad U_W=U_*\cap W.                                          \tag{5}
\]

No differentiation is needed to make the weight-one quadratic Casimir preserve this split. If
`C_(i,a)` is conjugation by the Pauli quarter-turn and `J_(i,a)` is conjugation by the paired Pauli
half-turn, direct involution algebra gives the exact identity

\[
 B_{i,a}^2=6I-4\big(C_{i,a}+C_{i,a}^{-1}\big)+2J_{i,a}.          \tag{5a}
\]

Every term on the right preserves `U_*`; hence so does every `B_(i,a)^2` and their sum `K_1`.
Hilbert--Schmidt self-adjointness gives
`ker K_1=cap_(i,a) ker B_(i,a)=S`, so `K_1` is injective on `W`. Therefore the quadratic-return
lemma, rather than invariance under each first-order generator, gives

\[
 \dim\operatorname{span}_{i,a}B_{i,a}U_W\geq\dim U_W.           \tag{6}
\]

For each weight-two Pauli edge word `p`, let `A_p` be its collective commutator. Exact Pauli
covariance sends `A_p S` into paired-Pauli character grade `p`. Distinct `p` give independent
grades, and `U_W` is resolved by the same grading. Define

\[
 F(s)=\big(A_p s\bmod (U_W)_p\big)_p.                            \tag{7}
\]

Independent grade assembly gives `(1)` with `C=sum_p A_p U_S`. Its kernel is

\[
 D=\{s\in U_S:A_p s\in U_W\text{ for every }p\}.                \tag{8}
\]

Let

\[
 K_2=\sum_p A_p^2.                                               \tag{9}
\]

For `s in D`, every `A_p s` belongs to input `U_W`; therefore each `A_p(A_p s)` and hence `K_2 s`
belongs to output generated from `U_W`. The exact local-singlet synchronization theorem shows
that kernel of `K_2` on `S` is precisely span of global identity and global replica swap. On global
permutation quotient those two modes are removed, so

\[
 R=K_2|_D:D\longrightarrow S
\]

is injective. Equations `(6)--(9)` supply `(2)` and required output containment. Universal theorem
therefore closes mixed singlet/nonsinglet Hall expansion for canonical obstruction.

## Hostile audit

- No inference from trivial common kernel to Hall expansion is used. Visible quotient rank and
  hidden-kernel recovery are separate hypotheses.
- Reverse channel recovers `ker F`, not full overlap `C intersect U_W`; this is sharp under
  orientation-multiplet expansion.
- Character independence is required. Without it, tuple detector `(7)` need not embed into actual
  output quotient.
- Paired-Pauli signs alone do not justify `(5)`. Exact product-Clifford averaging is required.
- A second-design commutant theorem by itself does not make arbitrary invariant operator subspaces
  Lie-invariant; that would be a fourth-moment leap. Casimir preservation instead uses the explicit
  finite-group-algebra identity `(5a)`.
- Global identity and global swap must be quotiented before `K_2` is injective.
- This closes two-replica Hall on paper. Lean now proves the one-site Clifford normalization,
  twirl range `span{I,F}`, idempotent canonical split, and exact `Fin 2`/Boolean transport. Remaining
  formal work is the product-local lift of those results, identity `(5a)` and `K_1` injectivity,
  quotient detector `(7)`, and physical edge-Casimir restriction.

## Formal target

`HTGeometry/VisibleKernelRecoveryHallExpansion.lean` proves universal theorem as
`visibleKernelRecovery_subspace_finrank`. It also defines quadratic family return
`linearFamilySquare`, proves that first images hidden in `U_W` have quadratic return in one-step
shadow of `U_W`, and packages physical proof pattern as
`quadraticHiddenKernelRecovery_subspace_finrank`. `visibleQuotientDetector_finrank` derives visible
rank from an injective assembly into output modulo occupied target input;
`invariantSubspace_le_shadow_of_linearFamilySquare_injective` derives reproduction of invariant
target input from injective quadratic return; and
`quadraticHiddenKernelRecovery_of_visibleQuotient` combines all mechanisms.
`HTGeometry/TwoReplicaCliffordTwirlHallSymmetryReduction.lean` proves the exact one-site Clifford
normalizer covariance, canonical-maximizer invariance, twirl range `span{I,F}`, the idempotent
range/kernel split, and transport into the Boolean physical convention. Concrete product-local
Casimir/edge-Casimir instantiation remains next formal gate; no complexity or anti-concentration
claim is authorized from the abstract theorem alone. Targeted elaboration passes; exact axiom
audits of all listed capstones contain only `propext`, `Classical.choice`, and `Quot.sound`.
