# Gauss-paired quantized differential incidence — formalized closure

- **ID:** `ccm-gauss-paired-quantized-differential-incidence-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-gauss-paired-quantized-differential-incidence-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

- `GaloisForLFunctions.RHTower.CCMGaussPairedQuantizedDifferential` (new), on the commutator calculus
  of `RHTower/CCMSoninEdgeTrace`.
- `GaloisForLFunctions.HTGeometry.PrimeEulerProductAperture` — pre-existing, carrying equation `(18)`.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(8a)` | `logQuantizedDifferential`, `logQuantizedDifferential_one` | `ω(U) = U⁻¹[F,U]` |
| `(8b)` | `logQuantizedDifferential_mul` | the crossed-homomorphism law. Only the Leibniz rule and `U⁻¹U = 1` are used: `F² = 1` and self-adjointness are not |
| `(4)`–`(5)` | `channelSum`, `logQuantizedDifferential_list_prod` | the exact conjugated channel decomposition of a finite factorization, with the tail conjugations retained. Stated for `List Rˣ`, so no commutativity of the factors is assumed |
| `(7)` | `trace_logQuantizedDifferential_list_prod` | any conjugation-invariant additive functional turns the channel decomposition into a plain sum over the factors — the exact algebraic content of the trace step |
| `(8c)`–`(8d)` | `conjCoboundary`, `CyclicCoinvariants`, `conj_sub_mem_conjCoboundary`, `coinv_logQuantizedDifferential_mul`, `coinv_logQuantizedDifferential_list_prod` | the additive quotient by conjugation coboundaries, in which `ω` is an honest homomorphism |
| `(8e)` | `coinv_sum_eq_of_prod_eq` | two finite factorizations of the same unit have the same total class: the Gauss splitting and the component/prime pairing create no ambiguity |
| `(15)` | `logQuantizedDifferential_reflection` | `U^*[F_H,U] = 2(U^*PU − P)` for `F_H = 2P − 1` |
| `(18)` | `bohrFrequencyModule_eulerProductLine`, `finrank_bohrFrequencyModule_eulerProductLine` (pre-existing) | the Bohr frequency module of the finite Euler product line is exactly the span of the prime logarithms, with exact rational dimension |
| `(19)` | `coefficientState_quotient_trivial` | a coefficient hull contained in the frequency module leaves no residual state charge |

## Axioms

`#print axioms` on all ten declarations returns exactly `[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- Connes–Consani's Gauss factorization `(10)` and quasi-innerness of the paired multipliers, which
  the card lists under `[SEARCH]`.
- The trace-class hypothesis `(6)`: it is what supplies the conjugation-invariant functional that
  `trace_logQuantizedDifferential_list_prod` consumes, and the card is explicit that it is
  load-bearing and imported.
- The four cofinal obligations of section 5 and the card's own `[NOT PROVED]` items (uniform trace
  ideal estimate, semilocal positivity, index/divisor transport).

## Verification performed

- `lake env lean` on the module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCMGaussPairedQuantizedDifferential`: success.
- `#print axioms` on every theorem: clean.
- Umbrella import added.
