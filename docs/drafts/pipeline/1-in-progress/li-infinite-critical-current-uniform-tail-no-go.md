# Infinite critical-current uniform-tail no-go

- **ID:** LI-INF-NUC
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md` · route LI
- **Statement:** Multiplicity-ordered critical endpoint-current prefixes cannot be uniformly Cauchy in Li mode; more sharply, cofinal dyadic Riemann--von Mangoldt shells have unbounded positive normalized current.

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
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Write `gamma_j` for `xiOrderedPositiveOrdinate j` and

`a_j = gamma_j / (gamma_j^2 + 1/4)`.

For a critical endpoint atom its exact frequency `omega_j` satisfies
`a_j = sin (omega_j/2)`, with `0 < omega_j < pi`. Prove:

1. `gamma_j` has the corpus RVM asymptotic `2*pi*(j+1)/log(j+1)`, hence
   `gamma_(2L)/gamma_L -> 2` and `L/gamma_(2L) -> infinity`.
2. Choose an integer mode comparable to `gamma_L`. On `j in [L,2L)`, every phase
   `k*omega_j` lies in one fixed positive sine chamber.
3. Every atom in that shell contributes at least a fixed multiple of `1/gamma_(2L)`.
   The shell therefore contributes at least a fixed multiple of `L/gamma_(2L)`, tending to
   infinity.
4. Deduce a closed non-uniform-Cauchy theorem for every critical-copy enumeration whose positive
   ordinates equal `gamma_j`.

Conjecture/fail/pivot labels:

- `[LI-FULL-CRITICAL-DRIFT]` eventual positivity of the complete current: not frozen; RVM remainder
  can resonate with the differentiated kernel, so available corpus estimates do not justify it.
- `[LI-INF-NUC]` dyadic-shell non-uniformity: frozen exact claim above. It uses only positive shell
  alignment and RVM density, so no global cancellation estimate is needed.

## Novelty and hostile audit
Corpus search found finite-packet recurrence, the sharp endpoint amplitude boundary
`ell^p \ ell^1`, and RVM relocation, but no uniform-tail obstruction or coherent RVM-shell current
lower bound. Literature search through August 2026 found classical uniform-convergence criteria
for harmonic/non-harmonic sine series and Keiper--Li asymptotics, but not this multiplicity-exact
Xi-ordinate endpoint-current theorem.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Pending `[LI-INF-NUC]` proof.
- **Strongest positive survivor:** Cofinal dyadic RVM shells carry unbounded positive normalized endpoint current.
- **New insight:** Zero-frequency accumulation is not merely failure of absolute summability; it creates coherent growing current blocks, so uniform finite-prefix transport has the wrong topology.
- **Status:** Frozen for paper proof and Lean formalization.

## Log
- 2026-08-29 — created directly in 1-in-progress after corpus and literature hostile audit; exact RH chain and no-go capstone frozen.
