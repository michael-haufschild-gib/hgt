# JAS/RFHM arithmetic restriction-history specialization

- **ID:** JAS-RFHM-ARITH
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** read-only `rh-current-frontier-map.md` · JAS/RFHM comparison burden; corpus
  synchronized-lcm insertion law, BV--Wold determinant-two anomaly, and abstract
  restriction-formation-history partial-isometry carrier
- **Statement:** Synchronized-lcm finite prime states and BV--Wold transport/anomaly admit one
  unconditional RFHM specialization retaining exact prime support and reversible logarithmic
  history.  Gamma insertion and two-prime path independence, and BV anomaly-corrected triangle
  flatness, hold as packet identities and as faithful partial-isometry operator identities.

## Goal

Test RFHM at its hardest stated missing internal gate: specialize the abstract faithful
support/history carrier to actual arithmetic diagrams rather than merely postulating a carrier.
Use the prime-Poisson source-linear superselection theorem to kill any claim that a scalar or RFHM
operator automatically supplies JAS sewing.

## Gates

- [x] 0 → 1 in-progress: mandatory corpus search, route-killing superselection audit,
  source-derived conjectures, current primary-literature search
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact Lean source check, scoped axiom/build audit, umbrella wiring
- [ ] 3 → 4 publication-ready: standalone paper and independent novelty review

## Conjecture loop and result

1. **C1 — ordinary closed source-linear JAS sewing can be obtained from the scalar Mellin
   operator.**  **Killed.**  Corpus theorem
   `primePoisson_reflection_nonzeroClosedSourceLinearSewing_iff` proves a nonzero closed densely
   defined single-valued `C(PrimeTorus)`-source-linear sewing exists exactly on `σ = 1/2`.
   The Mellin operator is only `ℂ`-linear.  This is a terminal obstruction to that identification.
2. **C2 — RFHM can retain actual synchronized-lcm support and history.**  Encode finite support
   `P` by its complement in `Set Nat.Primes`, use trivial grade action, and assign reversible grade
   `-log(weight(P))`.  Intersection of complements is union of occupied supports, while the exact
   corpus weight-insertion law adds log history.  Hence state times insertion equals enlarged state
   as a packet. **[PROVED HERE]**
3. **C3 — state-dependent gains cause path-dependent RFHM histories.**  Failed as a falsifier.
   Both orders around every admissible two-prime square equal the packet of the same enlarged
   support. **[PROVED HERE]**
4. **C4 — BV curvature cannot inhabit the same restriction-history carrier.**  Failed as a
   falsifier.  Unrestricted-support packets graded by negative log transport and negative log
   determinant-two anomaly satisfy transport·transport·anomaly = direct transport exactly.
   **[PROVED HERE]**
5. **C5 — Hilbert realization may erase arithmetic provenance.**  Failed as a falsifier.  The
   abstract packet representation is injective; specialized Gamma state operators are injective in
   finite prime support, and all Gamma/BV laws survive as operator composition identities.
   **[PROVED HERE]**

## Hard-frontier significance and exact remaining burden

This is structural, not numerical.  It closes RFHM's missing **arithmetic-specialization** burden:
one faithful partial-isometry carrier now realizes exact finite-prime formation history and the
independent valuation-depth anomaly without collapsing either into scalar output.

It does not prove RH or close JAS.  Source-linear sewing in the ordinary prime-Poisson model is
already terminal off the critical wall.  Remaining shared hard problem is an unconditional
completed-theta/Xi comparison functor or relation that:

- maps completed theta value/derivative and prime-Poisson first-jet data into this support/history
  carrier without assuming a zero lies on the wall;
- preserves infinite-support provenance and reflection orientation;
- yields a noncircular Xi landing or a new exact no-go/classification.

## Lean artifact

- Module:
  `GaloisForLFunctions.RHTower.JointAncestryRestrictionHistoryArithmeticSpecialization`
- Gamma packet laws:
  - `jasGammaWeight_pos`
  - `jasGammaStatePacket_mul_insertion`
  - `jasGammaStatePacket_twoInsertionPaths`
- BV packet law:
  - `jasBVTransportPacket_triangle`
- Faithful operator realization:
  - `jasGammaStatePacket_injective`
  - `jasGammaStateOperator_injective`
  - `jasGammaStateOperator_mul_insertion`
  - `jasGammaStateOperator_twoInsertionPaths`
  - `jasBVPacketOperator_triangle`
- Verification:
  - `lake env lean GaloisForLFunctions/RHTower/JointAncestryRestrictionHistoryArithmeticSpecialization.lean`
    — PASS
  - `lake build GaloisForLFunctions.RHTower.JointAncestryRestrictionHistoryArithmeticSpecialization`
    — PASS (`Built ...`, 7.1s; dependency leaf rebuilt in 44s)
  - scoped `#print axioms` — only `propext`, `Classical.choice`, `Quot.sound`
  - forbidden-declaration scan and scoped `git diff --check` — PASS
  - leaf wired into `GaloisForLFunctions.RHTower`; no full or umbrella build run
  - global `scripts/formal_tools.py lint` reports unrelated concurrent un-wired modules; this leaf
    is reachable and absent from the failures

## Literature audit (as of 2026-08-28)

- Connes--Consani, *The Scaling Hamiltonian* (arXiv:1910.14368), supplies an operator-theoretic
  semilocal RH framework and analyzes the limits of a Weil-positivity attempt, not this
  support-complement/log-history specialization of synchronized-lcm and BV--Wold diagrams.
- Steinberg--Szakács, *Simplicity of inverse semigroup and étale groupoid algebras*
  (arXiv:2006.13787), studies structural simplicity criteria for inverse-semigroup/groupoid
  algebras, not these arithmetic formation laws.
- Steinberg, *Prime étale groupoid algebras with applications to inverse semigroup and Leavitt path
  algebras* (arXiv:1802.01550), studies primeness and dynamical transitivity, not an RH arithmetic
  support/history representation.
- Targeted current searches found no paper containing the exact combined specialization proved
  here.  The component algebraic mechanism is elementary and the arithmetic inputs are internal
  corpus results. **Novelty status:** `[NOVELTY UNVERIFIED]` pending independent expert review.

## Door passport

- **Unconditional source:** explicit finite prime supports, exact positive synchronized-lcm weights
  and insertion law, exact BV--Wold inverse-holonomy law, abstract faithful RFHM representation.
- **No RH leakage:** no Xi zero, RH premise, zero enumeration, computation, new axiom, or
  target-fitted choice enters any declaration.
- **Burden removed:** RFHM arithmetic specialization for finite synchronized-lcm formation and
  BV--Wold anomaly history, with faithful Hilbert realization.
- **Burden not removed:** ordinary `C(PrimeTorus)`-source-linear sewing off wall, completed-theta/Xi
  comparison, infinite-support continuity, reflection-orientation selection, Xi landing.

## Log

- 2026-08-28 — corpus superselection theorem killed the scalar-source-linear JAS identification;
  prior Mellin card and module documentation corrected.
- 2026-08-28 — support-complement/log-history conjecture, two-prime hostile path test, BV anomaly
  triangle, and faithful operator realization proved in Lean; frontier map remained read-only.
