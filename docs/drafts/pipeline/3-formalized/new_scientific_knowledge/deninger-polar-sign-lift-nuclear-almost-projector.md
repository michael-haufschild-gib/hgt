# Polar-sign lift of a nuclear almost-projector

- **ID:** `deninger-polar-sign-lift-nuclear-almost-projector`
- **Stage:** 3-formalized
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
`GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticExactHardyProjectors`:
idempotence, complementarity, mutual annihilation, self-adjointness,
and recovery of chirality by \(\Pi_+-\Pi_-\).  Required direct-file
check passes.

The continuous-functional-calculus construction \(C=S|S|^{-1}\),
preservation of the nuclear ideal, and the Fredholm kernel-zero
reduction are formalized; see the sections below.

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

### The polar-sign lift landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerPolarSignLift.lean`.  Axiom audit: only `propext`
and `Quot.sound` — no choice.

The construction is stated algebraically over a ring with involution and a two-sided ideal.  The
positive part enters through exactly the properties continuous functional calculus supplies for
`|S|`: it is self-adjoint, commutes with `S`, squares to `S²`, and is invertible.

- `deningerPolarInv_isSelfAdjoint`, `deningerPolar_commute_inv` — the inverse of the positive
  part is self-adjoint and commutes with `S`.
- `deningerPolarSign S Tinv = S · |S|⁻¹` with `deningerPolarSign_isSelfAdjoint` (clause 1) and
  `deningerPolarSign_sq` (clause 2): the sign is a self-adjoint involution.  Clause 2 uses only
  `T² = S²` and invertibility, exactly as on the card.
- `deningerPolarPositive_sub_one_mem` — clause 3's first step: the factorization
  `|S| - 1 = (S² - 1)(|S| + 1)⁻¹` of `(5)`, taken as a hypothesis since `(|S|+1)⁻¹` is what
  positivity of `|S|` supplies, plus right-ideal stability.
- `deningerPolarInv_sub_one_mem`, `deningerPolarSign_sub_mem` — `(6)`: `|S|⁻¹ - 1 ∈ N` and hence
  `C - S ∈ N`, clause 3.
- `deningerHardyProjector` and `deningerPolarProjector_sub_mem` — `(4)`: the exact Hardy
  projectors differ from the almost-projectors by ideal elements, clause 5.

Together with `DeningerArithmeticExactHardyProjectors`, which already had clause 4, all five
clauses of the theorem are formalized.

### Remaining

Two items, both analytic rather than algebraic:

1. the continuous functional calculus that produces `|S| = (S²)^{1/2}` with the four properties
   above, and the invertibility of `|S| + 1` from positivity;
2. the Fredholm reduction of the invertibility hypothesis `(1)` to `ker S = 0` under `(1a)`,
   which needs Atkinson's theorem and the bounded inverse theorem.

Neither is needed for clauses 1--5 as stated; they are what instantiate the hypotheses at
`T = |S|`.

### The continuous functional calculus construction landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerPolarSignCFC.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

This discharges the first remaining item: the hypotheses of the algebraic theorem are now
*produced* at `T = |S|`, not assumed.

- `deningerAbs S = (S²)^{1/2}` via mathlib's `CFC.sqrt`, with `deningerAbs_nonneg`.
- `deningerAbs_isSelfAdjoint` — self-adjointness, from nonnegativity.
- `deningerAbs_commute` — **`S` commutes with `|S|`**.  `|S|` is a continuous functional calculus
  of `S²`, and `S` commutes with `S²`, so `Commute.cfc_nnreal` applies after rewriting
  `CFC.sqrt` as a `cfc`.
- `deningerAbs_mul_self` — `|S|² = S²`, from `CFC.sqrt_mul_sqrt_self` and `IsSelfAdjoint.sq_nonneg`.
- `deningerAbsInv S = |S| · (S²)⁻¹` with `deningerAbs_mul_absInv` and `deningerAbsInv_mul_abs`:
  **for invertible `S` the positive part is invertible**, the second law using that `|S|`
  commutes with `S²` and hence with its inverse.
- `deningerAbs_polarSign_isSelfAdjoint`, `deningerAbs_polarSign_sq` — **clauses 1 and 2 for the
  actual polar sign** `C = S|S|⁻¹` of an invertible self-adjoint element, with no hypotheses left
  standing beyond `IsSelfAdjoint S` and `Invertible S`.

### Remaining

- the invertibility of `|S| + 1` needed to instantiate the factorization `(5)`, which is
  positivity of `|S|` plus the spectral mapping that `-1` is not in its spectrum;
- the Fredholm reduction of `(1)` to `(1a)`, needing Atkinson's theorem and the bounded inverse
  theorem.

### Clauses 3 and 5 instantiated at the actual positive part

Added to `DeningerPolarSignCFC.lean`.  Axiom audit: `propext, Classical.choice, Quot.sound`.

- `isUnit_one_add_of_nonneg` — **a nonnegative element has invertible `1 + ·`**.  Its spectrum
  misses `-1` (`spectrum_nonneg_of_nonneg`), so `spectrum.mem_iff` gives invertibility of
  `-1 - T`, hence of `1 + T`.  This is the input the factorization `(5)` needed.
- `deningerAbs_sub_one_mem` — **`|S| - 1 ∈ N`**, by the card's `(5)`:
  `(|S| - 1)(1 + |S|) = |S|² - 1 = S² - 1`, so `|S| - 1 = (S² - 1)(1 + |S|)⁻¹` and right-ideal
  stability finishes.
- `deningerAbs_polarSign_sub_mem` — **clause 3** for the actual polar sign `C = S|S|⁻¹`.
- `deningerAbs_polarProjector_sub_mem` — **clause 5** for the actual Hardy projectors.

Clauses 1--5 now hold for the concrete construction `C = S|S|⁻¹` of an invertible self-adjoint
`S` with `S² - 1 ∈ N`, with no hypothesis about `|S|` left standing: it is built by continuous
functional calculus and all its properties are proved.

### Remaining

Only the Fredholm reduction of the invertibility hypothesis `(1)` to `ker S = 0` under `(1a)`,
which needs Atkinson's theorem and the bounded inverse theorem.  It weakens a hypothesis; it is
not needed for clauses 1--5.

### The Fredholm reduction landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerPolarSignFredholm.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerIsUnit_of_ker_eq_bot` — **if `S² - 1` is compact and `S` is injective, then `S` is
  invertible**.  This is the card's reduction of `(1)` to `(1a)`.

The proof does not need Atkinson's theorem: mathlib's Fredholm alternative for compact operators
(`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`) applied to `K = S² - 1` at `-1` gives the
dichotomy directly.  If `-1` were an eigenvalue of `K` there would be a nonzero `x` with
`S(Sx) = 0`, and injectivity applied twice gives `x = 0`.  Otherwise `-1` is in the resolvent set,
which says exactly that `S² = 1 + K` is invertible, and `Commute.isUnit_mul_iff` at
`Commute.refl S` turns invertibility of `S²` into invertibility of `S`.

### Status

All five clauses, the continuous functional calculus that constructs `|S|`, and the reduction of
the invertibility hypothesis to `ker S = 0` are formalized.  Nothing in the theorem's statement
is left on paper.

### Gates

- [x] 0 → 1 in-progress: canonical ideal-stable lift
- [x] 1 → 2 fully-proven: complete proof
- [x] 2 → 3 formalized: clauses 1--5 for `C = S|S|⁻¹`, the CFC construction of `|S|`, and the
      Fredholm reduction of `(1)` to `(1a)`
- [ ] 3 → 4 publication-ready: the arithmetic specialization needs `(8)` and `(9)` — the
      completed nuclear estimate and the vanishing middle-degree kernel — which this card
      identifies as the open input and does not prove
