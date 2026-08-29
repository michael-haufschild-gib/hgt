# Infinite critical-current uniform-tail no-go

- **ID:** LI-INF-NUC
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · route LI
- **Statement:** Multiplicity-ordered critical endpoint-current prefixes cannot be uniformly Cauchy in Li mode; more sharply, all sufficiently late dyadic Riemann--von Mangoldt shells have a uniform positive normalized-current floor at an explicit resonant integer mode.

## Goal
Kill the remaining passage from finite critical-packet cofinal sign changes to the full critical
packet. Exact RH chain under attack:

`finite critical-prefix negative excursion`
`=> uniform full-packet negative excursion`
`=> endpoint current nonpositive`
`=> interior current zero`
`=> failure of the LI zero-free premise`
`=> RH`.

The target is closed and unconditional. It does not assume RH. It rules out every
multiplicity-exact critical enumeration with a uniform finite-tail law, rather than only the
previous `ell^1` sufficient condition.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `not_exists_liEvenCrossFullCriticalNormalizedUniformCauchy`, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Write `gamma_j` for `xiOrderedPositiveOrdinate j` and

`a_j = gamma_j / (gamma_j^2 + 1/4)`.

For a critical endpoint atom its exact frequency `omega_j` satisfies
`a_j = sin (omega_j/2)`, with `0 < omega_j < pi`. Prove:

1. The corpus RVM relocation gives eventual bounds `gamma_(2L) <= 8 gamma_L` and
   `gamma_L <= C(L+1)` for one `C > 0`.
2. Choose an integer mode comparable to `gamma_L`. On `j in [L,2L)`, every phase
   `k*omega_j` lies in one fixed positive sine chamber.
3. Every atom in that shell contributes a positive amount. Summing the exact lower bound over
   `L` atoms and applying the RVM bounds gives the index-independent shell floor
   `1/(8192*pi*C)`.
4. Deduce a closed non-uniform-Cauchy theorem for every critical-copy enumeration whose positive
   ordinates equal `gamma_j`.

Conjecture/fail/pivot labels:

- `[LI-FULL-CRITICAL-DRIFT]` eventual positivity of the complete current: not frozen; RVM remainder
  can resonate with the differentiated kernel, so available corpus estimates do not justify it.
- `[LI-INF-NUC]` dyadic-shell non-uniformity: proved. It uses only positive shell alignment and
  coarse RVM density, so no global cancellation estimate is needed.

## Proof [PROVED HERE]
Let `a_j = gamma_j/(gamma_j^2+1/4)` and let `omega_j` be the exact endpoint frequency. Direct
trigonometry gives `a_j = sin(omega_j/2)` and therefore

`2 a_j <= omega_j <= pi a_j`.

For a shell start `L`, put `x_L = (64 a_L)^(-1)` and
`k_L = ceil(x_L)`. Once `gamma_L >= 64`, the amplitude bounds

`a_j <= 2a_L` and `1/(2 gamma_(2L)) <= a_j` for `L <= j < 2L`

give `x_L <= k_L <= 2x_L` and `0 <= k_L omega_j <= pi/16`. Jordan's lower sine bound on this
chamber then yields

`a_j sin(k_L omega_j) >= (4/pi) x_L (1/(2 gamma_(2L)))^2`.

Summing over the `L` indices in `[L,2L)` gives the exact dyadic block lower bound. Since
`a_L <= 1/gamma_L`, `gamma_(2L) <= 8 gamma_L`, and `gamma_L <= C(L+1) <= 2CL` eventually, that
block is at least `1/(8192*pi*C) > 0`, uniformly for all sufficiently large `L`.

Uniform Cauchy tails would make every block `[L,2L)` smaller in absolute value than this
positive floor for all sufficiently large `L` and every integer mode. Taking mode `k_L`
contradicts the dyadic lower bound. Hence no multiplicity-exact critical enumeration has the
claimed uniform tail property.

## Novelty and hostile audit
Corpus search found finite-packet recurrence, the sharp endpoint amplitude boundary
`ell^p \ ell^1`, and RVM relocation, but no uniform-tail obstruction or coherent RVM-shell current
lower bound. Literature search through August 2026 found classical uniform-convergence criteria
for harmonic/non-harmonic sine series and Keiper--Li asymptotics, but not this multiplicity-exact
Xi-ordinate endpoint-current theorem.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** `not_exists_liEvenCrossFullCriticalNormalizedUniformCauchy` rules out every multiplicity-exact critical enumeration with uniform normalized Li-current tails.
- **Strongest positive survivor:** Every such enumeration has a positive constant `delta` such that every sufficiently late dyadic shell has normalized endpoint current at least `delta` at its explicit resonant integer mode.
- **New insight:** Zero-frequency accumulation is not merely failure of absolute summability; RVM density creates coherent non-vanishing current blocks, so uniform finite-prefix transport has the wrong topology.
- **Status:** Exact LI finite-critical-prefix to full-critical-packet uniform-tail passage killed; positive survivor fully formalized.

## Lean certificate
- Module: `GaloisForLFunctions.RHTower.LiEvenCrossInfiniteCriticalCurrentUniformTailNoGo`
- Positive survivor: `exists_pos_eventually_liEvenCrossFullCriticalNormalizedTail_dyadic_lower`
- Closed capstone: `not_exists_liEvenCrossFullCriticalNormalizedUniformCauchy`
- Verification: `lake env lean` PASS; targeted `lake build` PASS; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Log
- 2026-08-29 — created directly in 1-in-progress after corpus and literature hostile audit; exact RH chain and no-go capstone frozen.
- 2026-08-29 — `[LI-INF-NUC]` proved on paper and in Lean; uniform-tail finite-to-full LI passage retired with a stronger positive dyadic-shell floor.
