# Card: prime-sieve-wold-gamma-bv-relative-character — formalization progress

Card: `docs/drafts/pipeline/2-fully-proven/prime-sieve-wold-gamma-bv-relative-character.md`
(carries a "Formalization status" section with the declaration tables).

## DONE (all unconditional; axioms = propext/Classical.choice/Quot.sound)

### `HTGeometry/PrimeSieveDensityTelescope.lean` — Section 3, eqs (13),(14)
`sieveDensity`, `sieveDensity_pos`, `sieveDensity_le_one`, `sieveDensity_insert` (13),
`sieveDensity_sub_insert` (13), `sievePrefix`, `sievePrefix_succ`,
`notMem_sievePrefix`, `sum_sieveDensity_div_prime` (telescoping),
`tendsto_sieveDensity_sievePrefix` (→0 via `1-x ≤ e^{-x}` and
`Nat.Primes.not_summable_one_div`), `hasSum_sieveDensity_div_prime`,
`tsum_sieveDensity_div_prime` — eq (14) boxed, for every enumeration `ℕ ≃ Nat.Primes`.

### `HTGeometry/PrimeSieveEulerTrace.lean` — arithmetic of (3), trace input to (6)
`sievePrimorial`, `sievePrimorial_insert`, `coprime_sievePrimorial`,
`coprime_sievePrimorial_insert_iff`, `sievedSum`, `summable_sieved_indicator`,
`sievedSum_insert` (the exact splitting of (3)), `sievedSum_eq_mul_prod`
(finite Euler product), `multiplicative_rpow_inv`, `summable_rpow_inv`,
`sievedSum_rpow_inv` (= `Tr(Q_P^k) = ζ(k)∏(1-p^{-k})`).

Both wired into `GaloisForLFunctions/HTGeometry.lean`.

## Corpus assets for the rest
- `HTGeometry/OperatorFredholmGerm.lean`: `operatorFredholmExpGerm`,
  `operatorFredholmDet2Germ` (`det₂(1-zT)` germ), `operatorFredholmDet1Germ`,
  `operatorFredholmDet2Germ_eq_of_powerTrace_eq`; on `HilbertSchmidtTrace.lean`
  (`opTrace`, `IsHilbertSchmidt`, `hsInner`, `hsNormSq`, `hsBasis`).
- mathlib traps hit: `Finset.range_add_one` (not `range_succ`),
  `Summable.tsum_add` (not `tsum_add`), `Function.Injective.tsum_eq`,
  `Real.summable_one_div_nat_rpow`, `Nat.coprime_mul_iff_left/right`,
  `Nat.Prime.coprime_iff_not_dvd`.
- `rw` rewrites ALL occurrences — use `calc` when the RHS repeats the LHS term.

## REMAINING
1. Section 1 (1)–(3) as operators on `ℓ²(ℕ_{>0})`: `Q e_n = n⁻¹e_n`,
   `S_p e_n = e_{pn}`, `E_p = I − S_pS_p*`, `E_P` = coordinate projection onto
   `{n : (n,M_P)=1}`, `Q S_p = p⁻¹ S_p Q`.  The *arithmetic* content of (3) is
   already done (`sievedSum_insert`); what remains is the operator packaging.
2. Section 2 (4)–(9): `Φ_P(t) = det₂(I−tQ_P)/det₂(I+tQ_P)`, enlargement law (5),
   log expansion (6) — the trace input `sievedSum_rpow_inv` is now available —
   the `C_r/p³` bound (7), HS convergence (8), vacuum limit (9)
   `Φ_vac(t)=e^{2t}(1−t)/(1+t)`.
3. Section 3 (11)–(12): `T_P(N)=a_P log N+κ_P+o(1)` and the finite
   inclusion–exclusion `T_P(N)=∑_{d|M_P} μ(d)/d·H_{⌊N/d⌋}`.
4. Section 4 (15)–(18): BV scale-decimation, `J(E_P p_a)=a_P J(p_a)` — needs the
   corpus BV/co-Poisson class `J`; locate it first.
5. Sections 5–6: assemble (19)–(21) and the naive no-go.
Conjecture (24) has no paper proof — NOT a formalization target.
