# Log-zeta prime coefficient identities

- **ID:** log-zeta-prime-coefficient-identities
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/c5-jensen-prime-kernel.md` §1
- **Statement:** In the prime part of `log zeta`, the coefficient `Lambda(n)/log(n) * n^(-1/2)` equals `p^(-1/2)` at a prime `p` and equals `p^(-k/2)/k` at a prime power `p^k`.

## Goal
This banks the arithmetic coefficient calculation used by the Jensen prime-kernel card. It does not formalize the Jensen-section kernel, root perturbation, explicit-formula regularization, or any C5 collision criterion.

## Paper Proof
The coefficient is
`c_n = Lambda(n) n^(-1/2) / log n`, where `Lambda` is the von Mangoldt function.

If `n=p` is prime, then `Lambda(p)=log p`, hence
`c_p = (log p/log p) p^(-1/2) = p^(-1/2)`.

If `n=p^k` with `k>0`, then `Lambda(p^k)=log p` and `log(p^k)=k log p`, so
`c_{p^k} = (log p)/(k log p) * (p^k)^(-1/2) = p^(-k/2)/k`.

## Gates
- [x] 0 -> 1  in-progress: von Mangoldt coefficient identities extracted.
- [x] 1 -> 2  fully-proven: paper proof above, using the standard values of `Lambda` on primes and prime powers.
- [x] 2 -> 3  formalized: Lean theorems `logZetaPrimeCoeff_prime` and `logZetaPrimeCoeff_primePower` in `formal/GaloisForLFunctions/C5JensenPrimeKernel.lean`; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the coefficient lemma in the Jensen prime-kernel note.

## Log
- 2026-06-19 — Leaner split this exact arithmetic coefficient lemma from `c5-jensen-prime-kernel`. The parent card remains in `2-fully-proven` because its Jensen kernel, perturbation, regularization, and collision-analysis layers are not fully Lean-formalized.
