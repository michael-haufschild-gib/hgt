# Prime-determinant two-superghost rigidity — Lean certification

- **ID:** `ULF-PD2SG-1`
- **Paper card:**
  `completion-index-transgression-mechanics/prime-determinant-two-superghost-rigidity-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.PrimeDeterminantTwoSuperghostRigidity`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

- `eq_prime_of_primeDeterminant_twoSuperghosts`: if `p` is prime, `XY=p²`,
  `1<Y≤X<p²`, and `X-Y`, `X²-Y²` are integer-valued, then `X=Y=p`.
- `primeConformal_twoSuperghosts_iff_grade_zero`: for `0≤b<1`, integrality of the first two
  parity-odd conformal ghosts at one prime is equivalent to `b=0`.
- `compositeSix_twoSuperghost_counterexample`: primality is necessary; `(9,4)` survives at
  determinant `6²`.
- `evenTraceCounterSeq_cast` and `evenTrace_integrality_does_not_force_neutrality`: parity is
  necessary; the unequal roots of `z²-7z+9` have integral even traces at every depth while lying
  in the base-three reciprocal strip.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/PrimeDeterminantTwoSuperghostRigidity.lean
lake build GaloisForLFunctions.HTGeometry.PrimeDeterminantTwoSuperghostRigidity
lake env lean /tmp/prime_superghost_axioms.lean
```

Direct check and targeted build passed. The module is wired into the universal-law umbrella; no
umbrella build was run. `#print axioms` on both rigidity theorems and both sharpness capstones
reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact field consequence

All-scale descent is not the minimal arithmetic mechanism. Determinant plus two adjacent odd
ghosts reconstruct the reciprocal packet, and primality collapses its factorization chamber to the
neutral point. Even traces retain quadratic nonneutral packets forever. Mixed sign is therefore
the information-bearing arithmetic orientation, not a defect to remove.
