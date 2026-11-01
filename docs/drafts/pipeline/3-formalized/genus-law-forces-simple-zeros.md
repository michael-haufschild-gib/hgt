# The genus law of ℤ is a simplicity statement: the near radical reads the resolved zeros

- **ID:** acs-genus-law-simple-zeros
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-0111/obstacles-summary.md §2.5.1 (Q2, B27)
- **Statement:** The near radical of Weil's form at level `L` (Hodge-class tests, threshold
  `ε_η(L) = exp(−η²e^{2L}/(300L))`) has dimension at least the Shannon surplus against the
  *distinct* zeros: `g(L, ε_η(L)) ≥ (2 − η)e^{2L} + 2(N(0,T) − N_d(0,T))`, `T = 2πe^{2(L−η/8)}`,
  and at least `(2 − η)e^{2L} + 2N(0,T) − #S` for every set `S` of zeros within
  `exp(−η²e^{2L}/(100L))` of all zeros of height `≤ T`. Hence the upper half asked in Q2,
  `g(L, ε_η(L)) ≤ (2 + η)e^{2L}`, implies `N(0,T) − N_d(0,T) ≤ ηT`, `N(0,T) − N^s(0,T) ≤ 2ηT`,
  `N^s/N → 1`, and that every `exp(−η²T/(20 log T))`-net of the zeros of height `≤ T` has at
  least `2N(0,T) − ηT` points.

## Answer to Q2
The posed statement — "the near radical at degree `a` has dimension `(2 + o(1))e^{2a}` and consists
of tests small at the zeros below `2πe^{2a}`" — is not a time–frequency fact. Weil's form reads a
zero through the *value* of the transform at `γ_ρ`; a zero of multiplicity `m` costs one constraint,
and two distinct zeros closer than the resolution `exp(−η²e^{2L}/(100L))` of the threshold cost one
constraint up to an error the threshold absorbs. The construction of the near radical therefore
spends one dimension per *resolved* zero, and its dimension is the Shannon surplus against the
resolved count, not against `N(0,T)`. The upper half of the genus law is equivalent in strength to
"all but `o(T)` zeros of `ζ` up to height `T` are simple and isolated at a doubly exponential
scale": a statement about multiplicities (rate `1/log T`), beyond what is known (two thirds simple
and critical, `RHTower.two_thirds_simpleCritical_epsilon`). The genus of `ℤ` at degree `a` is
`2e^{2a}` exactly when the zeros are resolved; in general it is larger, by twice the excess.

The characterization half holds in the constructed space: every element of the constructed near
radical has transform vanishing at every zero of height `≤ T` (`exists_nearRadical_blind`). The
converse inclusion (every near-radical test is small at the low zeros and band-concentrated below
`T`) is open for the same reason: it needs the zeros above `T` to sample the Paley–Wiener space,
which fails on unresolved clusters.

## Lean
`formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheGenusFunctionReadsTheResolvedZeros.lean`
- `norm_paperFT_sub_le_of_support`: strip Lipschitz bound `‖f̂(z) − f̂(w)‖ ≤ 2‖z − w‖U e^{|Im w|U}∫|f|`.
- `norm_W_trigTest_le_of_net`: Weil energy of a plateau test vanishing on a `δ`-net of the low zeros.
- `nearRadical_at_level_of_net`: the near radical constrained on a net, dimension
  `≥ (2 − η)e^{2L} + (2N(0,T) + c₀ − #S)`, threshold `ε_η(L) + δ·Q(L)e^{9L}`, blind on `S`.

`formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheGenusLawForcesSimpleZeros.lean`
- `genusFunction`: the genus function `g(L, ε)` (finite by `zeta_near_radical_finrank_le`).
- `genusFunction_ge_distinct`, `exists_nearRadical_blind`: `g ≥ (2 − η)e^{2L} + 2(N − N_d)`.
- `genusFunction_ge_of_net`: `g(L, 2ε_η(L)) ≥ (2 − η)e^{2L} + 2N(0,T) − #S` for every net `S`.
- `multiplicity_excess_le_of_genus_law`, `nonsimple_le_of_genus_law`,
  `nonsimple_isLittleO_of_genusLaw`, `tendsto_simple_ratio_of_genusLaw`,
  `cover_deficiency_le_of_genus_law`: the implications of the genus law.

Both modules compile with `lake --old env lean`; no added hypotheses, no axioms beyond
`propext, Classical.choice, Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof = the Lean proof above)
- [x] 2 → 3  formalized

## Log
- 2026-11-01 — created; Lean modules compiled; wired into the ACS umbrella.
