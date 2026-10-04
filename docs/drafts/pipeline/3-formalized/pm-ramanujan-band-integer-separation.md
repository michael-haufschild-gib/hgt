# Route PM: integer cutoff transfer of complete-band profile separation

- **ID:** pm-ramanujan-band-integer-separation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Dependencies:** audited real-cutoff spectral separation; actual primitive periodicity and floor expansion; current divisor subpower bound.

## Exact target

For each epsilon>0, one c>0 works for every fixed physical logarithmic L2 vector G and every integer B: some integer n>=B has ||n^epsilon*g_(n,2n)-G||>=c. No assertion at every dyadic cutoff is included.

## Dependency-closed paper argument

For q>1 let tau(q) be the divisor count. The exact primitive floor expansion and |mu|<=1 give |P_q(N)|<=N*tau(q). Periodicity reduces N to its residue modulo q, so also |P_q(N)|<=q*tau(q). Consequently

    sum_(N>=1) |P_q(N)|^2/[N(N+1)] <= 2*q*tau(q)^2.

Indeed the first q terms are individually bounded by tau(q)^2 and the reciprocal tail telescopes to at most q*tau(q)^2. This is a Hilbert bound on one complete primitive, used only to close the discontinuity at an integer cutoff.

The audited actual coefficient estimate |a_epsilon(q)|<=q^(-1-epsilon) then gives, for q comparable to X,

    X^epsilon*||a_epsilon(q)*P_q|| <= C*tau(q)/sqrt(q) -> 0.

The limit follows from the corpus divisor subpower bound with any exponent less than1/2. No estimate of a sum of different denominators is inferred from this atom bound.

For n=floor X>=1, the actual interval (floor X,floor(2X)] differs from (n,2n] by at most the single denominator 2n+1. Thus its normalized Hilbert-vector difference is a vanishing atom plus the scalar normalization difference between X^epsilon and n^epsilon. If the integer family converged to a fixed G, it would be bounded; X/n->1 then makes the scalar difference vanish too. The real family would converge to G, contradicting the audited real-cutoff separation (after its physical carrier transport).

Completeness of L2 upgrades no integer fixed limit to one common positive radius, using the same non-Cauchy tail-diameter argument as in the real-cutoff theorem.

## Audit and limits

Search156 completed, inventory64673 complete with mixed compiler freshness. All twenty candidate statements, twenty source statements and both ingredients were inspected. It returned no existing whole-primitive Hilbert estimate; the floor/periodicity proof above is the new mechanism. Actual source names read: `pmRamanujanPrimitive_eq_floor`, `pmRamanujanPrimitive_periodic`, `norm_pmPowerDampedRamanujanWeight_le`; the divisor theorem is in `DivisorBound.lean`. The atom Hilbert estimate, the exact floor-band interpolation and the convergence transfer are now Lean-proved (see the Lean certificate). It neither proves the small-damping energy upper ceiling nor RH.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.PMRamanujanBandIntegerSeparation`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Module (clean under `lake env lean`, built as a module, axiom audit `[propext, Classical.choice, Quot.sound]` only):
new `GaloisForLFunctions.RHTower.PMRamanujanBandIntegerSeparation`, on top of the audited corpus modules
`RHTower.PMRamanujanBandPhysicalSeparation` (real-cutoff separation `not_tendsto_pmRamanujanNormalizedBandLogVector`),
`RHTower.PMRamanujanBandHilbert` (energy identity `norm_sq_pmRamanujanBandLogVector_eq_energy`),
`RHTower.PMPowerDampedMobiusRamanujanPrimitive` (`pmRamanujanPrimitive_eq_floor`, `pmRamanujanPrimitive_periodic`),
`RHTower.PMPowerDampedMobiusRamanujanLogMass` (`norm_pmPowerDampedRamanujanWeight_le`), `RHTower.DivisorBound`
(`card_divisors_le_const_mul_rpow`, used with exponent `1/4 < 1/2`).

| Claim | Lean declaration |
|-|-|
| `|P_q(N)| ≤ N τ(q)` (floor expansion, `|μ| ≤ 1`) | `norm_pmRamanujanPrimitive_le_mul_card` |
| `|P_q(N)| ≤ q τ(q)` (periodicity) | `norm_pmRamanujanPrimitive_le_self_mul_card` |
| `Σ_{N≥1} |P_q(N)|²/(N(N+1)) ≤ 2 q τ(q)²` (first `q` terms + telescoping tail) | `tsum_norm_sq_pmRamanujanPrimitive_le` |
| Single-denominator band `= a_ε(q) P_q`; atom Hilbert estimate `‖·‖² ≤ q^{-2-2ε}·2qτ(q)²` | `pmRamanujanDenominatorBand_succ`, `norm_sq_pmRamanujanBandLogVector_succ_le` |
| `X^ε ‖a_ε(q)P_q‖ ≤ √2 τ(q)/√q` for `X ≤ q`, and `→ 0` by the divisor subpower bound | `rpow_mul_norm_pmRamanujanBandLogVector_succ_le`, `tendsto_atom_bound` |
| Band additivity; empty band is zero | `pmRamanujanBandLogVector_add`, `pmRamanujanBandLogVector_self` |
| Integer family `h_n = n^ε g_{(n,2n]}` | `pmRamanujanIntegerBandLogVector` |
| Exact floor-band interpolation `G_X = (X/n)^ε h_n + X^ε g_{(2n,⌊2X⌋]}`, remainder = vanishing atom `2n+1` | `pmRamanujanNormalizedBandLogVector_eq`, `rpow_mul_norm_remainder_le` |
| Convergence transfer: an integer limit would be a real limit (contradiction) | `not_tendsto_pmRamanujanIntegerBandLogVector` |
| Completeness ⇒ non-Cauchy ⇒ **one common radius** `c` for all `G` and all integer `B` | `not_cauchySeq_pmRamanujanIntegerBandLogVector`, `exists_uniform_pmRamanujanIntegerBand_separation` |

## Log

- 2026-10-04 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
