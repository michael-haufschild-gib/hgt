# Finite Ward width-high-pass mass rigidity

- **ID:** G-HP1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** G (`ORD ORIENT`)
- **Statement:** A finite signed mixture of positive-width reflected Ward kernels that pointwise dominates one target kernel has coefficient sum at least one; zero-mass width high-passes cannot dominate.

## RH-chain consequence

`riemannHypothesis_iff_continuedXiWardPrimeLogLeastCertifiedRefinedRealLaw` reduces RH to the
least-certified prime-log Ward sample law; its open producer must bound the continued edge response
by `2 +` adaptive slack `< 1`. Route G's fixed-line source majorant diverges. Finite interior-width
differencing cancels its width-independent leading mode only when coefficients sum to zero. This
theorem kills that entire repair class: source cancellation and pairwise Ward detection cannot
coexist. Any survivor must retain the full zero mode and cancel it arithmetically, or act
nonlocally/source-dependently before positive scalar domination.

## Conjecture loop and proof

- `[FALSIFIED]` A two-width high-pass can dominate the edge kernel.
- `[FALSIFIED]` An arbitrary finite zero-sum width mixture can dominate it.
- `[PAPER-PROVED]` If `c_i∈ℝ`, `x_i,x>0`, and
  `P_x(t) ≤ Σ_i c_i P_{x_i}(t)` for every `t`, then `1 ≤ Σ_i c_i`.

Each reflected Ward profile is integrable with width- and center-independent mass `4π`. The finite
mixture is integrable and has mass `4π Σ_i c_i`. Integrating the pointwise inequality gives
`4π ≤ 4π Σ_i c_i`; since `π>0`, `1≤Σ_i c_i`. In particular `Σ_i c_i=0` is impossible.

## Audit

Corpus contains Poisson semigroup/mass laws, fixed-line divergence, Harnack transport, and finite
shift dissipation, but not this finite-width domination classification. General Poisson mass
preservation and vanishing `L¹` sums are classical; no exact Route-G statement was found. Novelty
remains provisional pending independent priority review.

## No-go closure

- **Kill:** conserved Poisson mass.
- **Positive survivor:** domination forces at least one full mass unit.
- **Insight:** width mixing cannot remove G's divergent scalar mode; cancellation must be arithmetic,
  source-dependent/nonlocal, or occur before positive domination.
- **Lean status:** `XiWardFiniteWidthHighPassMassRigidity`; closed kill
  `xiWardFiniteZeroMassWidthHighPassMajorantRouteKilled`; sharp survivor
  `one_le_sum_of_wardReflectedLorentzianProfile_le_widthMixture`. Direct source check and exact
  target build pass; axioms are only `propext`, `Classical.choice`, `Quot.sound`.
