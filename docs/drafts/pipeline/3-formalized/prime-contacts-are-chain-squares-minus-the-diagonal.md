# Prime contacts are chain squares minus the diagonal

- **Stage:** 3-formalized
- **Assembly:** A97, prime contacts.
- **Module:** `HodgeTheoryOfAFixedPart/TheContactsOfAPrimeAreChainSquares.lean`.

Fix a prime `p`. Give its positive powers weight `log p` and all other integers weight zero. For distinct positive `m,n`, their contact is `log p` exactly when `ordCompl[p] m = ordCompl[p] n`, and zero otherwise (`contactW_primeContactWeight`).

Consequently, for a finite divisor supported on positive integers, its prime contact form is

`log p · (Σ_b (Σ_{ordCompl[p] n=b} c_n)² − Σ_n c_n²)`.

Equality of the prime-free parts gives a positive prime-power quotient after ordering `m,n`. Conversely such a quotient preserves the prime-free part. Grouping by that part gives each chain square; removing the diagonal gives the formula. Declaration: `prime_contact_form_eq_chain_squares`.

Direct Lean audit passed. Both declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
