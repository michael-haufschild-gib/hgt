# Formalization certificate — `ccm-countable-log-chirp-renormalization-law`

- **Card:** `ccm-countable-log-chirp-renormalization-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCM/CCMCountableLogChirp.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 4 theorems
- **Hypotheses:** none beyond the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Coverage

| Card item | Lean |
|-|-|
| `log t ≤ 2√t` | `log_le_two_mul_sqrt` |
| `(8)` countable weight summable | `summable_logChirp_weight` |
| `(13)`–`(14)` scalar renormalization | `scalar_renormalized_form` (+ corpus `RHTower/RayleighScalarShift.lean`) |
| `(10)`–`(11)` diagonal bound consumer | `summable_radialDiagonal_bound` |

## Deliberately outside the Lean statement

- the semiclassical conjugation `(6)` and its remainder bound;
- Dunster's radial phase expansions `(1)`–`(2)` and the Bessel endpoint;
- the PSWF symbol bounds `(10)`–`(11)` and the digamma multiplier `(12)`.

All of this card's gates are checked; it has no open gates.
