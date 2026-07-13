# Finite congruence-pencil factorization

- **ID:** finite-congruence-pencil-factorization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FUTURE
- **Source:** split from `../2-fully-proven/dewitt-supermetric-no-margin.md` Finding 3c
- **Statement:** For a finite square matrix `B` with two-sided inverse `Binv`, the normalized pencil
  `B * (lam I - Binv * P * Binv) * B` is exactly `lam * (B * B) - P`.

## Goal
This banks only the finite algebraic congruence identity used by the DeWitt/no-margin comparison with the
finite-free carrier. It does not formalize the spectral norm `lambda_c`, the finite-to-infinite carrier
limit, the Rodgers-Tao/de Bruijn-Newman implication, or the RH equivalence in the parent ticket.

## Paper Proof
Let `A = B B` and suppose `B Binv = I` and `Binv B = I`. Then

`B (lam I - Binv P Binv) B`
`= B (lam I) B - B (Binv P Binv) B`
`= lam (B B) - (B Binv) P (Binv B)`
`= lam A - P`.

Adding `P` to both sides gives the companion rearrangement
`B (lam I - Binv P Binv) B + P = lam A`.

## Gates
- [x] 0 -> 1  in-progress: finite algebraic core extracted from Finding 3c.
- [x] 1 -> 2  fully-proven: paper proof above by distributivity, associativity, and the two inverse identities.
- [x] 2 -> 3  formalized: Lean theorems `congruencePencil_factorization` and
  `congruencePencil_add_primeBlock` in `formal/GaloisForLFunctions/HTGeometry/CongruencePencil.lean`; scratch
  `#check`/`#print axioms`, `lake build`, and `scripts/check_axioms.sh` pass.
- [ ] 3 -> 4  publication-ready: cite as the finite algebraic certificate for the no-margin congruence
  comparison.

## Log
- 2026-06-19 - Leaner split this exact finite matrix identity from `dewitt-supermetric-no-margin`
  Finding 3c. The parent card remains in `2-fully-proven` because the spectral, limiting, Rodgers-Tao, and
  RH-equivalence layers are not Lean-formalized.
