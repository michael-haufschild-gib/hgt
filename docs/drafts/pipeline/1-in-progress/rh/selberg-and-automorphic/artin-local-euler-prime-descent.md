# Prime-choice descent for Artin local Euler polynomials

- **ID:** `artin-local-euler-prime-descent`
- **Stage:** 1-in-progress
- **Type:** THEOREM (local Artin infrastructure)
- **Status:** `[LITERATURE] [PAPER-PROVED] [BRIDGE] [NOT NEW]`
- **Statement:** construct the local polynomial
  \(\det(1-T\rho(\mathrm{Frob}_Q)\mid V^{I_Q})\) as an actual function of a base prime of a
  number-field Galois extension, with no selected prime ideal above it in its public interface.

## Goal

Build actual ideal-action transport, invariant-subspace conjugacy, and Frobenius transport needed
to index the existing upstairs polynomial by a base prime.  This is a mandatory prerequisite to a
global Artin Euler product.  It must use Mathlib's `Ideal.inertia`, decomposition stabilizers,
`IsArithFrobAt.conj`, and the concrete representation action—not a record postulating prime
independence.

## Paper proof

For `Q' = tau • Q`, conjugation by `tau` identifies decomposition groups and maps `I_Q` to
`I_Q'`.  The representation action of `tau` maps `V^{I_Q}` linearly and bijectively onto
`V^{I_Q'}`.  An arithmetic Frobenius at `Q` conjugates to one at `Q'`; the two induced maps on
invariants are conjugate.  Characteristic polynomials agree, and existing lift-independence
replaces that conjugated lift by the chosen `arithFrobAt` at `Q'`.  Galois transitivity of primes
over a fixed base prime then gives arbitrary prime-choice independence.

## Exact initial Lean target

```text
(Q.inertia (stabilizer G Q)).map
  (stabilizerEquivStabilizer (show tau • Q = tau • Q from rfl)).toMonoidHom
  = (tau • Q).inertia (stabilizer G (tau • Q)).
```

The first lemma is the nontrivial ideal-action transport.  It is a real obstruction boundary: the
fixed-`Q` lift-independence theorem does not establish it.

## Known APIs and non-routes

- `IsArithFrobAt.conj` transports a Frobenius lift to `tau • Q`.
- `Algebra.IsInvariant.exists_smul_of_under_eq` supplies `tau` when two primes lie over the same
  base ideal.
- `MulAction.stabilizerEquivStabilizer` transports decomposition groups.
- `LinearEquiv.charpoly_conj` can consume a concrete invariant-space equivalence.
- `isConj_arithFrobAt` alone is insufficient: its conjugator is not tied to the prime transport.
- `Ideal.inertiaEquiv` is inapplicable because it assumes a fixed ideal/action rather than
  simultaneous conjugation.

## Anti-theatre boundary

This does not define an Euler product, prove convergence or continuation, or establish any
continued-divisor effectivity.  It only removes an essential local choice.  A polynomial indexed
by a base prime cannot be honestly defined before this theorem.

## Formalized sublayer

`formal/GaloisForLFunctions/RHTower/Artin/ArtinLocalEulerPrimeTransport.lean` proves the exact
ideal-action transport lemmas

```text
inertia_map_conj:
  map (conj tau) (Q.inertia G) = (tau • Q).inertia G,

inertia_map_stabilizer_conj:
  map (stabilizerEquivStabilizer tau) (Q.inertia D_Q) = (tau • Q).inertia D_(tau•Q).
```

These use no postulated equivariance: membership is transported directly through the pointwise
ideal action.

`formal/GaloisForLFunctions/RHTower/Artin/ArtinLocalEulerPrimeDescent.lean` completes the conjugate
prime layer.  It defines the concrete linear equivalence
`inertiaInvariantConjLinearEquiv` induced by `rho(tau)`, proves the induced endomorphisms are
conjugate, transports residue-field finiteness via `Ideal.quotientEquiv`, and proves

```text
frobeniusInertiaEulerPolynomial_smul (R := R) tau Q rho
  = frobeniusInertiaEulerPolynomial (R := R) Q rho.
```

The left side is not a new abstract local-data object: it is exactly the existing local polynomial
at `tau • Q`, with its prime and finite-residue instances derived from `Q`.  Targeted source
checks and leaf builds passed; axiom audits report only `[propext, Classical.choice, Quot.sound]`.
Both leaves are wired into `RHTower.lean` without an umbrella build.

The local base-prime carrier is now present in
`formal/GaloisForLFunctions/RHTower/Artin/ArtinNumberFieldLocalEulerFactor.lean`:

```text
numberFieldFinitePlaceLocalEulerPolynomial :
  HeightOneSpectrum (𝓞 K) → Representation ℂ G V → Polynomial ℂ
```

It chooses a maximal ideal above the finite base prime internally by integral going-up, derives
its primality and finite residue quotient from actual number-field instances, and proves

```text
frobeniusInertiaEulerPolynomial_eq_numberFieldFinitePlaceLocalEulerPolynomial:
  Q.LiesOver v.asIdeal →
  frobeniusInertiaEulerPolynomial (R := 𝓞 K) Q ρ =
    numberFieldFinitePlaceLocalEulerPolynomial v ρ.
```

Thus no upstairs prime occurs in the public finite-place factor, and every valid choice computes
the same polynomial.  No global Euler product or analytic statement is implied yet.

## Log

- 2026-08-15 — opened after audit identified exact Mathlib routes and verified that no existing
  Artin prime-choice theorem is present in the project.
- 2026-08-15 — formalized the inertia and decomposition-stabilizer conjugation transport.  This
  closes the initial target but not local-polynomial prime-choice independence.
- 2026-08-15 — formalized invariant-space/Frobenius conjugacy and the exact equality for
  conjugate primes, with residue finiteness transported rather than assumed.  The remaining
  `under R` transitivity and base-prime packaging are open.
- 2026-08-15 — formalized the same-base-prime equality through
  `Algebra.IsInvariant.exists_smul_of_under_eq`.  The equality is complete; only the actual
  number-field base-prime carrier and its supplied prime-above existence remain on this card.
- 2026-08-15 — formalized the number-field finite-place wrapper using a chosen maximal ideal above
  a base maximal ideal and proved its choice independence from the same-base-prime theorem.
  `lake env lean` and the targeted `lake build
  GaloisForLFunctions.RHTower.Artin.ArtinNumberFieldLocalEulerFactor` passed.  Its axiom audit reports
  only `[propext, Classical.choice, Quot.sound]`; it is wired into `RHTower.lean` without an
  umbrella build.  Repository-wide formal lint remains blocked by unrelated concurrent modules,
  so this card remains Stage 1 rather than claiming a whole-tree formal-gate pass.
