# Prime towers decide the actual finite-stratum Weil kernel

- **ID:** review-2910-w07-actual-zeta-tower-hasse
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W07](../../../reports/review-2910/obstacles-summary.md)
- **Statement:** On the finite-off-line-support stratum, every non-blind prime tower carries the
  full index of the actual cubic-spline Weil kernel; infinitely many positive prime towers, or one
  positive non-blind tower, are equivalent to RH.

## Exact scope

Define the intrinsic blind primes by failure of injectivity of
`ρ ↦ zeroChar (conj ρ) (primeElt p)` on the actual right zeros. If their number is κ, the blind
prime set is finite of cardinality at most `κ.choose 2`. This definition is independent of any
chosen enumeration. The resulting RH criteria include the requested finite-support premise;
they assert no unconditional finite-support or tower-positivity estimate.

## Paper proof

[PROVED HERE] Enumerate the finite set of actual right zeros. The existing
`zetaKernel_eq_onLine_add_pairs_fin` identifies the actual kernel with its positive on-line part
plus one hyperbolic pair per right zero, with exponent the conjugate zero. Conjugation preserves
distinctness and real part. Every pair weight is nonzero by
`Wsummand_ne_zero_of_rightZero`, since the cubic spline sees every right zero.

Apply `ncard_blindPrimes_le` to this enumeration. Its blind set agrees with the intrinsic one
because the enumeration is a bijection. At a non-blind prime,
`negIndex_prime_eq_of_not_blind` gives tower index κ; `negIndex_zetaKernel` gives global index κ.
The actual kernel and every tower restriction are Hermitian. Hence positivity of that tower is
equivalent to zero global index, which is RH. An infinite set of positive towers contains a prime
outside the finite blind set. Conversely RH makes the global kernel positive and every restriction
positive; the prime set is infinite. This proves both requested implications and their converses.

## Verification

- [x] Corpus searches locate actual decomposition, nonzero spline weights and quantitative blind law.
- [x] Intrinsic blind set, full-index theorem and cardinal bound formalized.
- [x] Both actual-kernel RH criteria checked with `lake --old env lean`.
- [x] Transitive axioms standard only; umbrella import present.

Module: `ArithmeticKreinLangerTheory/FiniteSupportMakesAlmostEveryPrimeDecideZeta.lean`.
Declarations: `zetaBlindPrimes_finite_card_le`, `negIndex_zetaKernel_prime_eq`,
`riemannHypothesis_iff_zetaKernel_prime_posDef`, and
`riemannHypothesis_iff_infinitely_many_zetaKernel_prime_posDef`.

Final command, from `formal/`:
`lake --old env lean GaloisForLFunctions/ArithmeticKreinLangerTheory/FiniteSupportMakesAlmostEveryPrimeDecideZeta.lean`.
Exit 0; each of the four `#print axioms` reports exactly `propext`, `Classical.choice`,
`Quot.sound`. No new hypothesis beyond the specified finite-support/non-blind/positivity
conditions, no new axiom, no numerical computation, and no raised limits.

## Dependency observations

`TheCollisionMassIsTheWaveNumber.lean` supplies the exact finite enumeration and weights but its
olean was absent at the start. Its direct `lake --old env lean -o ... -i ...` compilation passed
because the new leaf imports it. No existing olean was rebuilt; no umbrella was compiled.
