# Countably many lag progressions cannot see a non-attained top

- **ID:** lag-countable-chain
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** JAS goal loop row 192
- **Statement:** For every sequence of spacings `ℓ_k > 0` there is a locally finite configuration with positive summable weights and real parts increasing strictly to `¼`, such that every progression `j ↦ Σ_n c_n Re e^{jℓ_k s_n}` is bounded above. There is a second such configuration with every progression bounded below.

## Gates
- [x] 0 → 1, 1 → 2 (paper), 2 → 3:
  - `RHTower.exists_chain_configuration_countable_bddAbove`
  - `RHTower.exists_chain_configuration_countable_bddBelow`
  - Module `RHTower/WeilLagCountableChain`, standard axioms.

## No-go closure
- **Killed:** countable families of single-base receivers detect non-attained tops.
- **Survivor:** the non-meagre Baire threshold (MUST-1363) is sharp against countable families. Dense lag sets still decide RH (corpus `WeilLagFunctionDense`). The upper/lower two-sided version along two bases is open: backlog card `two-base-lag-rigidity`.
- **Insight:** chains need only one aliased ring per scale, and simultaneous Dirichlet approximation serves any finite set of bases at each scale. Only infinitely many bases at a single scale, i.e. uncountable or dense families, defeat the construction.
