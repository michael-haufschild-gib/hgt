# Singular orientation and multiplicity-exact divisor transgression

- **ID:** SODT-1
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** whole-corpus RHTower/HTGeometry audit; Hedenmalm, Deninger, Sonin, projective-horizon, and recurrence shadows
- **Statement:** Nontrivial involutive orientation is supported exactly where the symmetric hyperbolic channel is singular; for Xi, the canonical Hedenmalm orientation current realizes this principle as an infinite translated divisor whose residue is the exact multiplicity difference.

## Goal

Replace the paper's catalogue of observer obstructions by one non-circular law.  The law must
explain why regular positive/hyperbolic completion erases reflection orientation, why singular
Hedenmalm and Sonin boundary carriers retain it, and why the centered zeta--Gamma observer lattice
retains projective curvature at first descent but no common nonconstant observable after the next.
It does not assert RH or assume a zero-location statement.

## Gates

- [x] 0 → 1 in-progress: well-posed, unconditional, source-pure, whole-corpus mechanism identified
- [ ] 1 → 2 fully-proven: consolidated paper proof and literature collision audit
- [ ] 2 → 3 formalized: direct Lean checks green; umbrella, axiom, lint, and final module-build audit pending
- [ ] 3 → 4 publication-ready: rewrite flagship paper and pass antagonistic general-journal review

## Approach

1. Algebraic orientation support.  For `epsilon^2 = 1`,
   `(1-epsilon)(1+epsilon)=0`.  If `1+epsilon` is regular, then `epsilon=1`.  When `2` is regular,
   `epsilon != 1` iff `1+epsilon` is not regular.  Every anti-invariant module vector is killed by
   `1+epsilon`, so an injective symmetric channel contains no nonzero orientation sector.
2. Prime-tail realization.  In the Hadamard reduced product of real prime coefficients modulo
   finite support, every Boolean orientation class `epsilon` satisfies `epsilon^2=1`.  Its class
   has a positive representative exactly when `epsilon=1`.  Since the constant class `2` is a
   unit, this is equivalent to regularity, and also to invertibility, of `1+epsilon`.  Otherwise
   `1-epsilon` is a nonzero explicit annihilator of `1+epsilon`.  Thus positive Euler pointing is
   exactly the regular locus of the symmetric source channel; it is not an external choice of
   cone.
3. Analytic realization.  The translated completed Xi logarithmic-current difference has an
   analytic removable germ at every point with center
   `ord_Xi(rho-h)-ord_Xi(rho)`.  A nonzero order jump forces a nonremovable singularity.  Every
   positive translation has infinitely many order jumps.
4. Hedenmalm coordinate.  Under the affine frequency chart, the same charge is multiplied by
   `-I`; therefore the canonical orientation multiplier carries an infinite multiplicity-exact
   divisor-transgression carrier at every positive aperture.
5. Differential observer phase.  For every hypertranscendental scalar, opposite first derivative
   tails join to the full intrinsic jet field and meet exactly in the Schwarzian differential
   field; advancing either tail to depth two collapses the common field to the coefficient base.
   This specializes to the natural centered zeta--Gamma reflection clock over `C(z)`.
6. Infinite-energy realization.  At every strict Sonin aperture, the successive-layer coupling
   asymptotically preserves arbitrarily large orthonormal packet families, so its Hilbert--Schmidt
   energy tends to infinity.  No bounded-above scalar completion, the actual scalar Burnol term,
   or pairing against any fixed bounded operator restores a lower floor.  Any surviving completion
   must use a scale-dependent channel family whose norm diverges.  This is the global companion to
   the local singular-support theorem: the carrier is first-order locally but infinite-rank
   globally.
7. Corpus consequences.  Hyperbolic localization kills signature; positive Julia layers preserve
   rather than select sign; finite Mellin/finite-time/finite-jet observers miss the singular
   carrier; Sonin's boundary corona retains it with unavoidable energy growth; Hedenmalm theta-null
   positivity forces a dense nonclosed radical.  These become instances, not independent slogans.

## Lean status

- `formal/GaloisForLFunctions/HTGeometry/ReflectionOrientationSingularSupportLaw.lean`
  - `reflectionOrientation_mul_hyperbolic_eq_zero`
  - `reflectionOrientation_eq_one_of_hyperbolic_regular`
  - `reflectionOrientation_ne_one_iff_hyperbolic_not_regular`
  - `map_reflectionOrientation_eq_one_of_hyperbolic_regular`
  - `hyperbolic_smul_antiInvariant_eq_zero`
  - `antiInvariant_eq_zero_of_hyperbolic_smul_injective`
- `formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmOrientationDivisorTransgression.lean`
  - multiplicity-exact removable germ and punctured identification
  - nonzero order-jump singularity theorem
  - infinite positive-translation order-jump carrier
  - exact `-I` Hedenmalm residue and infinite singular frequency image
- Existing exact phase law:
  - `formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonActualSchwarzianDiamond.lean`
  - `formal/GaloisForLFunctions/RHTower/ZetaGammaProjectiveHorizonSchwarzianDiamond.lean`
- Existing exact prime-tail source law:
  - `formal/GaloisForLFunctions/HTGeometry/TailHadamardReducedProduct.lean`
  - positive iff unit and involution facts are proved; the regularity/invertibility specialization
    is paper-proved and awaiting exact formalization.
- Existing exact Sonin energy law:
  - `formal/GaloisForLFunctions/RHTower/SoninCouplingEnergyGrowth.lean`
  - `formal/GaloisForLFunctions/RHTower/SoninBurnolCompletionNoFloor.lean`
  - `formal/GaloisForLFunctions/RHTower/SoninFixedChannelNoFloor.lean`

Direct `lake env lean <file>` checks are green for all four modules.  Final audit deliberately
deferred until corpus stops changing; no `lake build` was run for the two new modules.

## Antagonistic boundary

- The factorization `(1-epsilon)(1+epsilon)=0` is elementary; significance must come from the
  sharp regularity classification and its exact, non-metaphorical Xi/Hedenmalm/projective/Sonin
  realizations.
- The Hedenmalm singularity ceiling and upper-half-plane analyticity statements remain equivalent
  to RH.  They are route coordinates, not zero exclusion.
- The projective-horizon theorem is not a claim that the Schwarzian generates all classical
  projective differential invariants; that fact is known.  Novelty claim is the exact two-observer
  field lattice and its sharp depth-one/depth-two collapse, plus its natural zeta--Gamma instance.
- The prime-tail regularity classification is a short consequence of the involution factorization
  and the already proved positive-unit theorem.  It is structurally exact and useful, but cannot
  carry novelty alone.
- The Sonin conclusion excludes scalars and fixed bounded channels.  It does not exclude an
  unbounded scale-dependent regularized pairing; indeed the theorem proves such growth is
  necessary.  Any claim that all Sonin/Burnol completions fail would be false.
- Paper must not market formalization as novelty or mention Lean.

## Log

- 2026-08-01 — zero-omission census exposed unabsorbed Hedenmalm canonical-orientation singularity
  modules and the centered zeta--Gamma Schwarzian diamond.
- 2026-08-01 — proved regularity-strengthened orientation law: invertibility and positivity are
  unnecessary; a non-zero-divisor symmetric channel already kills orientation.
- 2026-08-01 — proved multiplicity-exact Xi divisor transgression, including infinitely many order
  jumps and their exact affine Hedenmalm residues.  Direct Lean checks green.

## Dependency-closed prime-tail proof

`[PAPER-PROVED] [BRIDGE]`  Put

```text
A = (P -> R)/(finite-support tails),
e = primeOrientationHadamardTail epsilon,
h = 1 + e.
```

The corpus proves `e^2=1` and `TailHadamardPositive(e) <-> e=1`.  The constant tail `2` is a unit:
its inverse is the constant tail `1/2`, and their Hadamard product is the constant tail `1`.
Consequently `2` is regular.

If `e` is positive, then `e=1`, hence `h=2`, so `h` is a unit and therefore regular.  Conversely,
if `h` is regular, `(1-e)h=1-e^2=0` and right cancellation gives `1-e=0`, hence `e=1` and `e` is
positive.  Thus

```text
TailHadamardPositive(e) <-> IsRegular(h).
```

The same argument with `IsUnit(h)` is sharper on the positive side: positivity gives `h=2`, hence
`IsUnit(h)`; a unit is regular, so the reverse implication follows from the preceding equivalence.
Therefore positivity, regularity, and invertibility of the symmetric channel are equivalent.

Finally, if `e != 1`, then `1-e != 0` and `(1-e)h=0`; the nontrivial orientation supplies an
explicit nonzero annihilator of its symmetric channel.  No domain, positivity axiom, topology, or
analytic continuation enters this proof.

Hostile verdict: `BRIDGE`, not an independent novelty claim.  The theorem matters only as the exact
prime-source realization of the wider singular-orientation law.
