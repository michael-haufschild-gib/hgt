# The pre-spectral firewall as an explicit genuine/fake separation

- **ID:** euler-firewall-separation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]` composition, axiom-clean
- **Source:** composes EulerProduct.isMultiplicative_iff_bohr_factorization + davenportHeilbronnFakeCoeff_not_isMultiplicative
- **Statement:** `euler_firewall_separation` — for every genuine (multiplicative) Dirichlet coefficient f, the Bohr lift factors over the primes at every n; yet the Davenport–Heilbronn-style fake coefficient fails that factorization at a finite n. The Euler-product/Bohr-factorization property separates genuine from fake, pre-spectrally (no zero examined).
- **Lean:** `GaloisForLFunctions.euler_firewall_separation` in `formal/GaloisForLFunctions/EulerFirewall.lean`. Axiom-clean. MainTheorems gate green.

## What this is
The First-Theorem file proves the iff and, separately, that the fake is non-multiplicative — but never composes them into the separation the firewall names. This one line makes the pre-spectral distinguishing criterion explicit: genuine L-functions Bohr-factor, the DH fake does not, at finite level. HT-field-native (the multiplicative/tensor-irreducible dichotomy).

## Log
- 2026-07-07 — created directly in 3-formalized.
