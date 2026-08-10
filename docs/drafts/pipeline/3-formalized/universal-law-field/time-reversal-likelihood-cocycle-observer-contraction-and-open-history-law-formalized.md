# Time-reversal likelihood cocycle, observer contraction, open history — Lean certification

- **ID:** ULF-TRLC-1
- **Paper card:** `time-reversal-likelihood-cocycle-observer-contraction-and-open-history-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveTimeReversalLikelihoodCocycle`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## New infrastructure — three lemmas mathlib does not have

- `absolutelyContinuous_map_iff_of_measurableEmbedding`, `klDiv_map_measurableEmbedding` —
  the Kullback–Leibler divergence is invariant under a measurable embedding;
- `measurableEmbedding_graph` — the graph map `ω ↦ (q ω, ω)` of a measurable observer is a
  measurable embedding;
- `rnDeriv_compProd_right`, `klDiv_compProd_right` — the conditional divergence
  `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` equals `∫⁻ y, klDiv (κ y) (η y) ∂μ`.

Together with mathlib's disintegration and chain rule these give the **data-processing inequality
for `klDiv`**, which mathlib also does not have.

## Certified declarations

| Card item | Lean |
|---|---|
| (1) the setup | `revLaw`, `timeAsymmetry`, `revLaw_revLaw`, `comap_of_involution` |
| (2) `Σ∘Θ = −Σ` | `timeAsymmetry_comp_involution` |
| (3) `E e^{−Σ} = 1` | `integral_exp_neg_timeAsymmetry` |
| (4) `E Σ = D(P‖P^Θ) ≥ 0`, equality iff reversible | `integral_timeAsymmetry_eq_klDiv`, `integral_timeAsymmetry_nonneg`, `integral_timeAsymmetry_eq_zero_iff` |
| (5) observer compatibility | `revLaw_map` |
| (7) the conditional formula | `exp_neg_timeAsymmetry_observer` |
| (8) data processing | `jointLaw`, `jointLaw_fst`, `klDiv_jointLaw`, `klDiv_eq_map_add_cond`, `klDiv_map_le` |
| (9) the exact gap | `rnDeriv_compProd_right`, `klDiv_compProd_right`, `klDiv_eq_map_add_integral` |
| sufficiency criterion | `klDiv_map_eq_iff` |
| Theorem 4.1, deterministic core | `exists_hit_of_tendsto`, `le_of_hit`, `returns_unbounded`, `tendsto_atTop_of_rate`, `closed_observer_open_history` |
| (10), (12) | `walkProduction`, `tendsto_walkProduction_rate`, `walkProduction_rate_pos`, `tendsto_production_along_subsequence` |
| increments and mean | `walk`, `walk_step`, `integral_increment` |
| Theorem 4.1, probabilistic form | `ae_closed_observer_open_history` |

### Two points worth recording

**Equation (7) is a mathlib lemma in disguise.**  `MeasureTheory.toReal_rnDeriv_map` says the
pushforward Radon–Nikodym derivative evaluated at `g x` is the conditional expectation of `dμ/dν`
with respect to `comap g`.  That is exactly the card's (7), and the same lemma at `g = Θ` — where
`comap Θ` is the whole σ-algebra because `Θ` is an involution — gives (2).

**Recurrence needs no Markov-chain theory.**  The card's proof of Theorem 4.1 invokes irreducibility
of a finite chain.  The Lean proof instead observes that a `±1` path with positive drift hits *every*
level above its start (`exists_hit_of_tendsto`) and that a level is reached only after at least that
many steps (`le_of_hit`); recurrence of the mod-`m` observer at arbitrarily late times follows, along
with the escape of the underlying path.  This is strictly more elementary and needs nothing about
Markov chains, which mathlib does not have.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveTimeReversalLikelihoodCocycle.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Both pass with no warnings; the umbrella build completed 11,435 jobs.  `#print axioms` on the
eighteen declarations audited reports only `propext`, `Classical.choice`, and `Quot.sound`.  No
project axiom, placeholder, hypothesis interface, or computation proof is used.

## Exact field consequence

The ontology the card proposes — constitutive path law, reversal, observer statistics — is now
certified to force its shadows rather than name them: time orientation is the involution, signed
local history is the likelihood cocycle, positivity is its mean relative entropy, the observer no-go
is strict data-processing loss with an exact gap, and the recurrence/open-lift phenomenon is an
elementary consequence of positive drift.  What an observer loses is measured exactly, by
`∫_Y D(P_y‖P_y^Θ) d(q_*P)(y)`, and it vanishes only for a sufficient observer — not merely for one
whose output happens to recur or close.
