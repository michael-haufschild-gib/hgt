# Second-Cartier physical order/moderation firewall

- **ID:** source-horizontal-second-cartier-physical-order-moderation-firewall
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `source-horizontal-bilateral-second-cartier-topology.md`
- **Statement:** The nonzero quadratic Cartier class cannot be made both source-faithful and physically admissible by either conventional receiver class: every reduced multiplicative receiver erases the full two-orientation lattice, while every nonzero coefficient-faithful additive Hardy receiver is moderate exactly at unit character modulus and therefore never on a strict-right Xi fibre.

## Goal

Close the physical order/moderation question for the literal second-Cartier class without assuming
RH and without weakening coefficient fidelity.  The theorem is a scoped impossibility result, not
an absolute ban on all future receivers: it identifies the only remaining escape as a receiver that
is simultaneously nonreduced and nonmultiplicative (or relation/Krein-jet valued).

## Gates

- [x] 0 → 1 in-progress: source-pure statement; exact carrier and receiver classes fixed
- [x] 1 → 2 fully-proven: dependency-closed proof below, `[PROVED HERE]`
- [x] 2 → 3 formalized: Lean leaf, axiom audit, exact leaf build, umbrella wiring
- [ ] 3 → 4 publication-ready: standalone exposition and external novelty audit

## Exact setup

Let

\[
  A=\mathbf Z[q,q^{-1}],\qquad g=q-1,\qquad I=(g),\qquad Q=A/I^3.
\]

Write

\[
  F=[g],\qquad R=[q^{-1}-1],\qquad G=[g^2].
\]

The preceding source-topology theorem proves

\[
  F+R=G,\qquad G\ne0,
\]

and that the integral span `L = ZF + ZR` has rank two.  Notice also that the literal Gamma
Hermitian product has the opposite sign:

\[
  F R=[(q-1)(q^{-1}-1)]=-[g^2]=-G.
\]

Thus `G` is the retained even inversion class, while the full Gamma Hermitian ghost is `-G`.

## Conjecture loop and hostile pivots

### C0 — positive physical order on `G`

**Conjecture.** A positive source order makes `G` admissible.

**Fail.** Existing Gamma-six untwisting identifies positivity of the literal Hermitian square with
unitarity of the bilateral character, hence with the critical line.  Taking this as an input is
RH-equivalent rather than a producer.  `[REDISCOVERED / CIRCULAR]`

### C1 — multiplicative physical order through a reduced carrier

**Conjecture.** Preserve source multiplication and descend `Q` to an ordinary reduced ordered
physical algebra.

**Fail, with sharp classification.** In `Q`,

\[
  F^3=0,\qquad R^3=0,\qquad G^2=0.
\]

Any ring homomorphism from `Q` to a reduced commutative ring therefore sends `F`, `R`, and `G` to
zero.  It consequently vanishes on all of `L`; in particular no such receiver is injective on the
source lattice.  Ordinary real-valued ordered physicalization is a special case.  `[PROVED HERE]`

### C2 — forget multiplication but preserve both coefficients

**Conjecture.** An additive reporter can retain `F`, `R`, and moderate `G`.

Fix `c ≠ 0`, `λ ≠ 0`, and suppose an additive receiver `D : L → (Z → C)` is coefficient-faithful:

\[
  D(F)(e)=c\,h_+(\lambda,e),\qquad
  D(R)(e)=c\,h_-(\lambda,e).
\]

Then source additivity and `F+R=G` force

\[
  D(G)(e)=c\bigl(h_+(\lambda,e)+h_-(\lambda,e)\bigr)
         =c\lambda^{-e}.
\]

Multiplication by nonzero `c` neither creates nor removes bilateral polynomial moderation.  The
bilateral eigenfamily `e ↦ λ^{-e}` is moderate exactly when `|λ|=1`.  Therefore

\[
  D(G)\text{ moderate}\quad\Longleftrightarrow\quad |\lambda|=1.
\]

For `λ=χ_p(ρ)` and a strict-right Xi divisor copy `ρ`, the exact prime character law gives
`|χ_p(ρ)|=1 ↔ Re ρ=1/2`, contradicting `Re ρ>1/2`.  Hence no nonzero coefficient-faithful additive
receiver moderates `G` on such a fibre.  `[PROVED HERE]`

### C1.5 — retain nilpotents in a nonreduced ordered target

**Conjecture.** Escape C1 by using a nonreduced ordered physical algebra.

**Fail for simultaneous source positivity.** Reduction is not needed for the core sign collision.
The forward-square presentation is `F²=G`, while the literal Gamma Hermitian presentation is
`FR=-G`.  In any partially ordered additive ring, if a multiplicative receiver declares both
images nonnegative, antisymmetry gives `image(G)=0`.  Therefore a receiver retaining `G` must reject
at least one of the two source-derived positivity laws.  `[PROVED HERE]`

## Theorem — two-horn firewall

For every strict-right Xi copy, prime label, and nonzero common coefficient:

1. every reduced multiplicative physical receiver kills the complete literal source lattice `L`;
2. even without reducedness, any ordered multiplicative receiver retaining `G` must make either
   the forward-square or Gamma-Hermitian source presentation nonpositive;
3. no additive receiver carrying `F` and `R` to the two exact coefficient-faithful Hardy halves has
   a moderate image of the nonzero quadratic class `G`.

**Proof.** The first claim follows from the three displayed nilpotence laws and reducedness.  The
second is the antisymmetry consequence of `G ≥ 0` and `-G ≥ 0`.  For the third, additivity forces
the exact bilateral eigenfamily above; its sharp moderation criterion forces unit modulus, while
the strict-right Xi inequality forces nonunit modulus.  No analytic or RH hypothesis occurs.  ∎
`[PROVED HERE]`

## Lean certificate

Module:
`GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierPhysicalOrderModerationNoGo`

Capstones:

- `sourceHorizontalSecondCartierPhysicalOrderModeration_orderFirewall`
- `sourceHorizontalSecondCartierPhysicalOrderModeration_firewall`
- `sourceHorizontalStrictRightXi_no_coefficientFaithful_secondCartier_moderation`
- `deningerIntegralCartierSecondOrderedPhysicalization_not_bipositive_of_ghost_ne_zero`

Verification:

- `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalSecondCartierPhysicalOrderModerationNoGo.lean` — PASS
- `lake build GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierPhysicalOrderModerationNoGo` — PASS
- capstone axioms — `propext`, `Classical.choice`, `Quot.sound` only
- wired into `GaloisForLFunctions.RHTower`; umbrella intentionally not built

## No-go closure

- **Exact killing mechanism:** reduced multiplication annihilates the nilpotent Cartier directions;
  before reduction, `F²=G` versus `FR=-G` forbids simultaneous physical positivity while retaining
  `G`; additive coefficient fidelity exposes unavoidable two-sided exponential growth off line.
- **Strongest positive survivor:** the literal rank-two lattice and nonzero `G` survive, but only in
  an infinitesimal nonreduced source carrier.  Any viable physical descent must retain that
  infinitesimal information while refusing the multiplicative/reduced and additive-Hardy horns.
- **New insight:** source order and physical moderation are not one missing estimate.  They impose
  incompatible categorical requirements on this carrier.  The open core is now an explicitly
  nonreduced, nonlinear/relation-valued Xi-fibre receiver, not improved scalar domination.
- **Status:** formalized in
  `GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierPhysicalOrderModerationNoGo`;
  exact leaf build passes; capstone axioms are only `propext`, `Classical.choice`, and `Quot.sound`;
  exact external novelty unverified.

## Literature boundary

The generic fact that reduced targets erase nilpotent directions is classical algebraic geometry.
Sonin/Hardy compression and semilocal Weil-positivity frameworks also pre-exist.  The new claim here
is the coefficient-faithful cross-corpus dichotomy for this exact second-Cartier Xi carrier; no
external source located in the bounded audit states it.  `[NOVELTY UNVERIFIED]`

## Log

- 2026-08-18 — C0 failed as circular; C1 and C2 proved; two-horn firewall established on paper.
- 2026-08-18 — formalized unconditionally; exact leaf built and wired into `RHTower.lean` without
  building the umbrella.
