# Closed-discrete positive-clock all-pass jet no-go

- **ID:** HB-CDJ-PC-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` HB source-FE Ward seam
- **Statement:** Every closed-discrete complex frequency set with arbitrary pointwise finite jet depths admits two distinct entire, zero-free, unit-real-boundary, FE--Schwarz responses with strictly positive boundary clocks and identical prescribed jets.

## Goal

Kill all discrete finite-order phase-identification producers for exact source-FE unit gain. Chain:

`discrete finite-order response data -> source-FE gain identification -> fixed Ward/unit gain -> shared HB/FZZ-P/PW-B/RBH extinction -> RH`.

The no-go removes first arrow for whole closed-discrete class. Survivor must use a frequency accumulation/continuum, an infinite jet, or source-global minimum-phase/winding/singular boundary data.

## Gates

- [x] 0 → 1 in-progress: exact corpus declarations, proof chain, construction, falsifiers
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted build, axiom audit
- [ ] 3 → 4 publication-ready

## Corpus basis

- `exists_entire_prescribed_discrete_vanishing_nontrivial`: arbitrary closed-discrete pointwise finite multiplicity passport.
- `exists_symmetric_hypertranscendental_passport_exponent`: nonzero entire Schwarz-real passport carrier.
- `exists_entire_factor_of_natCast_le_analyticOrderAt`: global removal of prescribed zero multiplicity.
- `iteratedDeriv_exp_congr_of_flat`: exponential jets agree through flat order.
- `differentiable_mul_ne_zero`: entire scalar functions have no zero divisors.
- `HBFiniteCrossFrequencyJetPositiveClockNoGo`: finite-packet predecessor only.
- `normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_*`: unit gain is exact common four-route receiver.

## Paper proof

Let `S ⊂ ℂ` be closed discrete and `m : S -> ℕ`. Corpus passport theorem gives nonzero entire Schwarz-real `Q` with `ord_a Q >= m(a)+1`. Set

`H(z) = z Q(z) Q(-z)`.

Then `H` is entire, odd, Schwarz-real, nonzero, and `ord_a H >= m(a)+1`. Put `h=H'` and `G=1+h²`; `G` is entire, even, Schwarz-real. Take an entire primitive `F` of `G`, Schwarz-symmetrize it, then oddify it to obtain entire odd Schwarz-real `K` with `K'=G`.

Define

`A±(z)=exp(i(K(z)±H(z)))`.

Both are entire and zero-free. Oddness plus Schwarz reality gives `A±(-conj z)=conj(A±(z))`; real phases give unit modulus on `ℝ`. Their boundary logarithmic-derivative clocks are

`1+h(x)²±h(x) = (h(x)±1/2)²+3/4 > 0`.

At each `a∈S`, global factorization gives `H(z)=(z-a)^(m(a)+1)U_a(z)`. Hence exponent difference `2iH` is flat to order `m(a)+1`, and exponential flatness gives equality of every response jet `j<=m(a)`. If `A+=A-`, differentiating and cancelling their nonzero common value gives `H'=0`; entire constancy and oddness give `H=0`, contradicting construction. `[PROVED HERE]`

## Hostile falsifiers

- `H=0` despite `Q≠0`: excluded by no-zero-divisors for entire functions.
- Symmetric odd primitive changes derivative: excluded because `G` is even and Schwarz-real.
- Clock sign fails: exact completed-square lower bound is `3/4`.
- Jets fail at complex sample sites: global analytic-order factorization, not real-polynomial factorization.
- Responses coincide through exponential periodicity: derivative cancellation forces `H'=0`, then `H=0`.
- Literature duplication: exact searches through 2026-08 found finite/rational all-pass interpolation, general positive group delay, entire prescribed-zero interpolation, and growth-restricted phase retrieval; no source states this unrestricted closed-discrete, arbitrary finite-jet, FE--Schwarz, strictly-positive-clock ambiguity theorem. Novelty remains to be independently reviewed.

## No-go closure

- **Exact killing mechanism:** arbitrary closed-discrete finite-order data are carried by a nonzero flat entire phase deformation while strict clock positivity survives.
- **Strongest positive survivor:** any successful phase producer must leave closed-discrete pointwise finite jets via accumulation/continuum, infinite jet, or source-global analytic law.
- **New insight:** positive clock and FE--Schwarz symmetry do not turn a discrete set into a uniqueness set without growth/Hardy/source-global restrictions.
- **Status:** Lean theorem `d4HBClosedDiscreteFiniteJetPositiveClockAllPassRouteKilled`; targeted module build passed; axioms only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired. Corpus lint reports unrelated pre-existing unreachable modules, not this module.

## Log

- 2026-09-01 — corpus-first conjecture frozen after exact four-route chain and novelty audit.
- 2026-09-01 — paper proof and unconditional Lean route-class certificate closed.
