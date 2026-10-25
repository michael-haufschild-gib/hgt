# Signed geometric towers have the same exact admission radius

- **ID:** biarithmetic-signed-tower-admission
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (Lean formalization incomplete)
- **Proof status:** Only statements with completed Lean checks and axiom audits are proved. Paper arguments below are proof plans; every significant claim remains a formalization obligation.
- **Parent:** [Digital energy and payment](biarithmetic-digital-energy-and-prime-tower-payment.md)
- **Statement:** For every real `a` with `|a|<5`, the ordinary receiver of `I_a=localFactorInverse 5 a` is paid exactly when `|a|<sqrt(5)`. This includes both critical signs. Flipping the sign on the prime-five generator preserves admission throughout the full mean-convergence interval.

## Proof from the actual source

The checked source theorem gives the exact centered prefix
`A_a(n)=-a/(5-a) W_x(n)`, with `x_l=a^l`, for every `|a|<5`.
For nonzero `a`, its scalar factor is nonzero, so bounded receiver energy is
equivalent to bounded energy of `W_x`. The checked signed digit-energy theorem
identifies this with convergence of

`sum_l x_l^2/5^l = sum_l (a^2/5)^l`.

The ratio is nonnegative. Its geometric series converges exactly when the
ratio is less than one; at or above one its terms do not tend to zero.
Finally `a^2<5` is equivalent to `|a|<sqrt(5)`. At `a=0`, the source is the
unit kernel and its centered prefix vanishes, so the same equivalence holds.

In particular both `a=sqrt(5)` and `a=-sqrt(5)` are unpaid. The sign change
`a -> -a` leaves the criterion unchanged, even beyond the interval where the
Euler factor is a critical Wiener unit. The proof uses exact signed digit
variance; it does not compare negative digit rows pointwise with positive ones.

## Scope and verification

This concerns the specified single-prime source family. It does not show that
arbitrary arithmetic sources preserve payment under a supercritical local
parity change. The existing positive-tower theorem and the subcritical
Wiener-unit parity theorem are compatible but have different scopes.

The dedicated corpus query returned the positive admission theorem in
`GoldenSourceAdmission.lean` and the existing local-factor identities; no
signed admission classification was returned. This is a reuse audit, with
no external originality claim.

- [x] Dependency-closed proof plan from checked source and signed digit-energy laws.
- [ ] Lean signed admission equivalence and both critical endpoints.
- [ ] Direct source check, transitive axiom audits, and umbrella import.
