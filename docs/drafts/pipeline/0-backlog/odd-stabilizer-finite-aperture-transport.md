# Finite aperture transport for the literal odd-conductor row

- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Route:** Argon §4.1.
- **Parent:** [Literal model calibration](../1-in-progress/parity-stabilizer-logarithmic-coalescent-calibration.md).

## Target

Transfer the exact complete Poisson row to the finite logarithmic pair kernel,
retaining `1/sqrt(m(m+2r))`, the taper, the aperture and the upper pair endpoint.
The fixed conductor cutoff and its primitive spatial correction remain explicit.

For a C⁴ window, let `D₄ = ∫|Ω⁽⁴⁾|` over an interval containing its support,
and `O(Q)=Σ_{q≤Q,odd} μ²(q)/φ(q)`. The first target is

`|Σ_{r=1}^R parityStabilizerWeight Q (2r) Ωhat(2r/m) − fullRow|`
`≤ 2 O(Q) D₄ (m/2)^4 / R³`, for R≥1.

Use `abs_cosTransform_le`, the Ramanujan bound `|c_q(h)|≤φ(q)`,
and `HilbertSchmidt.tsum_reciprocal_square_tail_le`: multiply the square tail
by `R⁻²` to bound the fourth-power tail.

## Existing phase transport and remaining boundary

`coalescent_term_linearization_bound` already controls both logarithmic phase
and square-root pair weight for a bounded Lipschitz scaled kernel. For
`Ω_T(t)=u((t−T)/T)^4`, the corpus supplies all derivative bounds.
At bandwidth 4/3 and aperture `θ=T^(-5/6)`, the bulk truncation and logarithm
errors have matching power saving `T^(-1/6)` before logarithmic factors.

Rows with `mθ` bounded and rows near the upper pair endpoint require separate
bounds. The estimate `|parityStabilizerWeight|≤2O(Q)` alone can lose a
logarithm on those short rows. The corpus supplies
`abs_singularSeriesTerm_le` and `Σ μ²(q)/φ(q)²≤16`, giving the candidate
uniform bound `|parityStabilizerWeight Q h|≤32σ(h)` for h≥1.
This removes the conductor logarithm when the lag stays bounded.
Even complete model transport leaves the actual signed prime-minus-model
discrepancy unproved.
