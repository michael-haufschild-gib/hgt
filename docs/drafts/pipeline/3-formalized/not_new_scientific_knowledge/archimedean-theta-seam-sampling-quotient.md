# Archimedean theta seam survives the prime-power sampling quotient

- **ID:** arch-theta-sampling-quotient
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rhtower-nogo-positive-content-audit.md`, Candidate C
- **Statement:** The positive-half completed-zeta theta pairing does not factor through evaluation on prime-power logarithms: a continuous tent in the explicit gap `(log 2, log 3)` has zero prime-power samples and strictly positive theta pairing.

## Goal

Replace the narrative archimedean pairing no-go by an exact positive separator theorem.  The theorem must name the test space, the prime-power sampling map, the actual RHTower archimedean source, and a witness in the sampling kernel detected by that source.  Its role is a reusable support-separation building block, not an RH implication.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `archimedeanThetaSeamFunctional_not_factors_through_primePowerSamples`, focused build green, axiom audit clean
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact candidate

Let

`S(phi)(n) = phi(log n)` when `n` is a prime power and `0` otherwise,

let `g` be the continuous nonnegative tent

`g(u) = max(0, min(u - log 2, log 3 - u))`,

and let `A(phi)` be the interval pairing of `phi` with the real positive-half theta density underlying `xiThetaLogSource`:

`A(phi) = integral_[log 2, log 3] phi(u) exp(u/4) (evenKernel(0, exp u) - 1) du`.

The target theorem is

`S(g) = 0`, `A(g) > 0`, and consequently there is no map `F`—linearity not assumed—with `A = F composed with S` on continuous real test functions.

## Proof `[PROVED HERE]`

1. Every prime power is a natural number.  If `log 2 < log n < log 3`, strict monotonicity of `exp` gives `2 < n < 3`, impossible.  Hence the tent vanishes at every prime-power logarithm.
2. The interval lies in the positive half-line.  There `xiThetaLogSource` equals `xiThetaPositiveFormula`, whose real density is `exp(u/4) (evenKernel(0, exp u) - 1)`.
3. The density is strictly positive because `exp` is positive and `evenKernel_zero_sub_one_pos` is already formalized.  The tent is continuous, nonnegative on the interval, and positive at its midpoint.  The interval integral is therefore strictly positive.
4. If `A = F composed with S`, then `S(g) = S(0)` forces `A(g) = A(0) = 0`, contradicting positivity.

## Scientific status

- `[BRIDGE]` Support separation itself is classical and is not new scientific knowledge.
- `[BRIDGE]` The exact RHTower identification is stronger than the former no-go narrative because it uses the completed-zeta theta source already tied to the critical Fourier trace, rather than an unnamed “archimedean Gaussian.”
- `[SEARCH]` A future novelty candidate must use this nonzero sampling-quotient class to prove a property not already supplied by classical support separation.  Do not promote the bridge itself as novel.

## Log

- 2026-07-10 — Created in stage 1 from the all-no-go audit.  Selected the canonical gap `(log 2, log 3)` and `xiThetaLogSource` as the actual archimedean source.
- 2026-07-10 — Paper proof completed and formalized in `SeamArchimedeanSamplingQuotient.lean`.  Focused Lean check passed; the two capstones use only `propext`, `Classical.choice`, and `Quot.sound`; formal lint passed.
