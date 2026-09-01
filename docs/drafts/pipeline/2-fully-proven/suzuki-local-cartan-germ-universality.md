# Suzuki local Cartan-germ universality

- **ID:** CCM-FU-LOCAL-CARTAN-GERM
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md` route CCM-FU; `SuzukiNonabelianCartanWardCompletion`
- **Statement:** Every fixed local Cartan germ `phi(x)=x-x^2/2+O(x^3)` produces a completed Suzuki observable equal to Green plus `o(1)`; its uniform boundedness is equivalent to RH.

## Goal

Kill all fixed coefficient-faithful local analytic/nonlinear Stokes-fusion replacements for the
logarithmic `SL₂` Levi coordinate. Full chain:

`local Cartan germ + forced first two jets`
`→ completed observable = Suzuki Green + o(1)`
`→ bounded observable ↔ bounded atomic–continuous imbalance`
`→ RH`.

This does not assume bounded Green, zero placement, or any RH-equivalent cancellation. It proves
that local germ choice cannot create the missing coercive invariant; a survivor must be genuinely
nonlocal or cutoff-dependent before scalar/cofinal passage.

## Gates

- [x] 0 → 1  in-progress: corpus-defined cells and exact RH chain; no literature collision found
- [x] 1 → 2  fully-proven: complete paper proof below, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, targeted build, axiom audit
- [ ] 3 → 4  publication-ready: standalone paper

## Exact class

For a fixed `phi : ℝ → ℝ`, put

`r_phi(x) = phi(x) - x + x^2/2`.

Call `phi` cubic-controlled when some `C ≥ 0` satisfies

`|r_phi(x)| ≤ C x^3` for every `x ≥ 0`.

For aperture `A`, let `x_A(n)` be the existing nonnegative Suzuki center Cartan cell and define

`R_phi(A) = sum_{2≤n≤A} r_phi(x_A(n))`,

`O_phi(A) = 2 sum_{2≤n≤A} phi(x_A(n))
            + sum_{2≤n≤A} x_A(n)^2
            - regularScrewMass(log A)`.

## Theorem and proof

**Theorem `[PROVED HERE]`.** For every cubic-controlled `phi`:

1. `O_phi(A) = Green(log A) + 2 R_phi(A)` for `A ≥ 2`;
2. `R_phi(A) → 0` as `A → ∞`;
3. uniform boundedness of `O_phi(N+2)` is equivalent to RH.

**Proof.** Fix a control constant `C`. Corpus results give, for every
`n ∈ [2,A]`,

`0 ≤ x_A(n) ≤ M_A := log(A)/(2 sqrt(A))`,

and `card([2,A]) ≤ A`. Hence

`|R_phi(A)|
 ≤ sum |r_phi(x_A(n))|
 ≤ C sum x_A(n)^3
 ≤ C A M_A^3
 = C log(A)^3/(8 sqrt(A))`.

The last expression tends to zero because `log(A)^3/sqrt(A) → 0`. This proves (2).

For (1), expand `phi(x)=x-x^2/2+r_phi(x)` inside the finite sum. The quadratic
terms cancel the explicit counterterm, leaving

`O_phi(A) = 2 sum x_A(n) - regularScrewMass(log A) + 2 R_phi(A)`.

Existing source identity gives `2 sum x_A(n)=primeOutgoingCharge(A)`, and the existing Ward
weld gives `primeOutgoingCharge(A)-regularScrewMass(log A)=Green(log A)`.

The error `2R_phi(A)` is convergent, hence uniformly bounded on natural apertures. Therefore
`O_phi(N+2)` is uniformly bounded iff `Green(log(N+2))` is uniformly bounded. Corpus theorem
`riemannHypothesis_iff_suzukiWardAtomicContinuousImbalanceBounded` identifies the latter exactly
with RH. ∎

## No-go closure

- **Exact killing theorem/mechanism:** fixed local germs with forced linear and quadratic jets differ from the literal completed atomic–continuous endpoint by a vanishing aggregate cubic tail.
- **Strongest positive survivor:** genuinely nonlocal/cutoff-dependent cross-label coupling is necessary; local analytic `SL₂`/Cartan functional calculus cannot be the independent producer.
- **New insight:** obstruction is universality of the cofinal endpoint, not special choice `log(1+x)`.
- **Status:** paper proof dependency-closed; Lean formalization in progress. Primary-literature search through 2026-08 found no matching classification.

## Log

- 2026-09-01 — corpus/literature audit; paper proof closed.
