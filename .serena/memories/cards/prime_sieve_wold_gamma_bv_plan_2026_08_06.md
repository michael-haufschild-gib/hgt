# Card: prime-sieve-wold-gamma-bv-relative-character — formalization progress

Card: `docs/drafts/pipeline/2-fully-proven/prime-sieve-wold-gamma-bv-relative-character.md`
(its "Formalization status" section carries the full declaration tables).

## DONE — Sections 1, 2, 3 complete; Section 4's coefficient layer complete
(axioms = propext/Classical.choice/Quot.sound; all wired into
`GaloisForLFunctions/HTGeometry.lean`; umbrella builds clean)

- `HTGeometry/PrimeSieveDensityTelescope.lean` — Section 3 (13),(14).
- `HTGeometry/PrimeSieveEulerTrace.lean` — arithmetic of (3), `sievedSum`.
- `HTGeometry/PrimeSieveHarmonicInclusionExclusion.lean` — (11),(12) and
  `∑_{d|M_P} μ(d)/d = a_P`.
- `HTGeometry/PrimeSieveRegularDeterminant.lean` — (5),(6),(7),(9) analytically.
- `HTGeometry/LpDiagonalOperator.lean` — REUSABLE diagonal operators on ℓ²(ι).
- `HTGeometry/PrimeSieveOperator.lean` — (1),(2),(4),(8);
  `sievePhi_eq_exp_sieveLogPhi` welds (4) to (6);
  `sieveOffMultiple_inv_eq_sieveWeight` welds Section 4's `E_P` to Section 1's.
- `HTGeometry/CoefficientDecimationSieve.lean` — Section 4 coefficient layer:
  `decimate`, `inflate`, `decimate_inflate`, `multipleProjection(_apply)`,
  `offMultiple(_apply)`, `sieveOffMultiple(_empty/_insert)`,
  `decimate_sieveOffMultiple` (commutation), `LSeries_inflate` (16b, exact and
  hypothesis-free), `LSeries_multipleProjection`,
  `LSeriesSummable_multipleProjection`, `LSeries_offMultiple` (parent card (14)),
  `J_sieveOffMultiple` ((17)+(18) from the four source laws).

## The one remaining gap in Section 4
`J_sieveOffMultiple` takes as hypotheses exactly the card's source laws:
additivity of `J`, `(15)` `D_q p_a = p_{aq}`, `(16a)` `J(p_{aq}) = q^{s-1}J(p_a)`,
`(16b)` `J(S_q b) = q^{-s}J(b)`.  (16b) is discharged unconditionally here.
(15) and (16a) are corpus theorems in
`RHTower/BVPrimeWindowDilationOrientation.lean`:
`polarCoefficient_argumentDilation_eq_argumentExpansion_sq_mul` and
`continuedSourceResidueValue_argumentDilation`
(with `J = continuedSourceResidueValue · rho`, `s = rho + 1/2`, `q = r^2`).
BLOCKER for full instantiation: the corpus `J` is defined on WINDOWS, not on
coefficient sequences, so `J (inflate q b)` is not even typeable.  Extending `J`
to sequences means the residue of the CONTINUED source
(`RHTower/BVPrimeWindowContinuation.lean`: `continuedSource`,
`LSeries_polarCoefficient_eq_continuedSource`,
`polarCoefficient_LSeriesSummable`), not of the Dirichlet series — at
`s = rho + 1/2` with `Re rho ∈ (0,1)` the series does not converge.
Residue machinery: `RHTower/BVPrimeWindowDivisorTomography.lean`
(`tendsto_continuedSource_residue_of_zeta_zero`,
`meromorphicOrderAt_continuedSource_eq_neg_one_iff_mellin_ne_zero`).
Any such module must live in RHTower (RHTower may import HTGeometry, not
conversely).

## REMAINING
1. Extend `J` to coefficient sequences via the continued source, then instantiate
   `J_sieveOffMultiple` — closes Section 4 fully.
2. Sections 5–6: assemble (19)–(21) and the naive no-go.
Conjecture (24) has no paper proof — NOT a formalization target.

## Traps (cumulative)
- `∘L` binds TIGHTER than `^`; `T^(k+1) = T^k * T`, convert with
  `ContinuousLinearMap.mul_def`.
- `rw` of an `Iff` inside an `if` condition fails on the `Decidable` motive —
  use `by_cases` + `if_pos`/`if_neg` with `.mp`/`.mpr` applied.
- `rw [someDef]` can fail ("Failed to rewrite using equation theorems") for a
  `def f a b : X → Y := fun m => ...`; add an explicit `f_eq ... := rfl` lemma.
- `LSeries_sub` lives in `Mathlib.NumberTheory.LSeries.Linearity`, not `.Basic`.
- `Complex.natCast_mul_natCast_cpow` is the `(q*N)^s = q^s N^s` lemma.
- Name collisions are caught by the umbrella build, not the linter. Grep first.
