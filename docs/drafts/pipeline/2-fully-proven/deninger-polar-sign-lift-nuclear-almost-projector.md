# Polar-sign lift of a nuclear almost-projector

- **ID:** `deninger-polar-sign-lift-nuclear-almost-projector`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** `DAC_POLAR_SIGN_LIFT_NUCLEAR_ALMOST_PROJECTOR`
- **Parent:** `deninger-arithmetic-calderon-paugam-hardy-comparison`
- **Statement:** an invertible self-adjoint almost-involution modulo
  the nuclear ideal has a canonical exact self-adjoint involution;
  its Hardy projectors are exact and differ from the original
  almost-projectors by nuclear operators.

## Theorem

Let \(H\) be a Hilbert space, let \(\mathcal N\subset\mathcal B(H)\)
be a two-sided operator ideal stable under multiplication by bounded
operators, and let \(S=S^*\in\mathcal B(H)\).  Assume
\[
  S^{-1}\in\mathcal B(H),\qquad S^2-1\in\mathcal N.           \tag{1}
\]
Define
\[
  |S|=(S^2)^{1/2},\qquad
  C=S|S|^{-1}.                                                \tag{2}
\]

`[PROVED HERE] [DAC_POLAR_SIGN_LIFT_NUCLEAR_ALMOST_PROJECTOR]`

Then:

1. \(C=C^*\);
2. \(C^2=1\);
3. \(C-S\in\mathcal N\);
4. the operators
   \[
     \Pi_\pm=\frac{1\pm C}{2}                                \tag{3}
   \]
   are complementary orthogonal projectors;
5. if \(P_\pm^0=(1\pm S)/2\), then
   \[
     \Pi_\pm-P_\pm^0\in\mathcal N.                           \tag{4}
   \]

The construction is canonical under unitary conjugation.

If moreover \(\mathcal N\) is contained in the compact ideal, the
invertibility assumption in `(1)` may be replaced by
\[
  \ker S=0.                                                    \tag{1a}
\]

## Proof

`[PROVED HERE]`

Functional calculus for the self-adjoint \(S\) shows that
\(|S|\), \(|S|^{-1}\), and \(S\) commute.  Therefore
\[
  C^*=|S|^{-1}S=C
\]
and
\[
  C^2=S^2|S|^{-2}=1,
\]
proving 1--2.  Consequently `(3)` consists of self-adjoint
idempotents with
\[
  \Pi_+\Pi_-=0,\qquad \Pi_++\Pi_-=1,
\]
which proves 4.

For the ideal statement, use
\[
  |S|-1=(S^2-1)(|S|+1)^{-1}.                                \tag{5}
\]
The second factor is bounded, so `(1)` and ideal stability give
\(|S|-1\in\mathcal N\).  Since \(|S|^{-1}\) is bounded,
\[
  |S|^{-1}-1
  =
  -|S|^{-1}(|S|-1)
  \in\mathcal N.
\]
Hence
\[
  C-S=S(|S|^{-1}-1)\in\mathcal N,                            \tag{6}
\]
proving 3.  Equation `(4)` is one half of `(6)`.

If \(U\) is unitary, continuous functional calculus gives
\[
  |USU^{-1}|=U|S|U^{-1},
\]
so the construction commutes with unitary conjugation.

For the final assertion, `(1)` without the inverse says that the image
of \(S\) in the Calkin algebra has square one.  Its Calkin image is
therefore invertible, so Atkinson's theorem makes \(S\) Fredholm.
Self-adjointness gives
\[
  \operatorname{coker}S\cong\ker S^*=\ker S.
\]
Under `(1a)`, \(S\) is injective and surjective with closed range.
The bounded inverse theorem supplies \(S^{-1}\), reducing to the
preceding proof.

## Arithmetic specialization

Suppose the global source relation, represented by Meyer's Poisson
almost-sections, closes on the positive Hodge completion to a bounded
self-adjoint representative \(S\).  In a complementary
almost-projector representative write
\[
  S=P_+^0-P_-^0=2P_+^0-1.                                   \tag{7}
\]
The completed form of Meyer's hereditary nuclear estimates must give
\[
  S^2-1\in\mathcal N.                                       \tag{8}
\]
Because the nuclear ideal is compact, it is enough that the global
arithmetic Calderón--Green theory prove
\[
  \ker S=0.                                                   \tag{9}
\]
Fredholm self-adjointness then supplies a coercive gap automatically.
Equations `(2)`--`(4)`
construct the exact completed Hardy projectors required by
`DAC_ARITHMETIC_CALDERON_PAUGAM_HARDY_COMPARISON`.

Because the correction is nuclear, hereditary quotient traces are
unchanged under commutators with the correction.  Thus the exact
projectors retain the source relative trace class represented by
Meyer's almost-projectors.

## Exact remaining input

Nuclear almost-idempotence alone does not imply `(9)`: a compact
finite-dimensional spectral packet may meet zero.  Required
arithmetic theorem is both Hodge self-adjointness of the closed
representative and vanishing of its middle-degree kernel after every
Milnor incidence and prime/real boundary correction.

Local positive graph--conormal transversality proves kernel vanishing
at each finite packet.  Missing step is preservation of kernel
vanishing in the strict nuclear/coarse limit.  No stage-uniform lower
bound has to be assumed separately: Fredholmness recovers it from the
global kernel statement.

## Lean status

The exact Hardy-projector consequences of a self-adjoint involution
are formalized in
`GaloisForLFunctions.RHTower.DeningerArithmeticExactHardyProjectors`:
idempotence, complementarity, mutual annihilation, self-adjointness,
and recovery of chirality by \(\Pi_+-\Pi_-\).  Required direct-file
check passes.

The continuous-functional-calculus construction
\(C=S|S|^{-1}\), preservation of the nuclear ideal, and the
Fredholm kernel-zero reduction remain to be formalized.

## Gates

- [x] 0 → 1 in-progress: canonical ideal-stable lift
- [x] 1 → 2 fully-proven: complete proof
- [ ] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

## References

- Continuous functional calculus and polar decomposition for bounded
  self-adjoint operators.
- `DAC_MEYER_POISSON_NUCLEAR_POLARIZATION_PAIR`.
- `DAC_POSITIVE_GRAPH_CONORMAL_TRANSVERSALITY`.
- `DAC_ARITHMETIC_CALDERON_PAUGAM_HARDY_COMPARISON`.

## Log

- 2026-07-27 — Constructed exact Hardy projectors by polar sign and
  isolated uniform global Calderón coercivity as the remaining input.
- 2026-07-27 — Formalized all exact Hardy-projector identities after
  the polar sign; functional-calculus and nuclear-ideal transport
  remain.
