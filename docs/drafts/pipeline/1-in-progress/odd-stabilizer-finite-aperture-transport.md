# Finite aperture transport for the literal odd-conductor row

- **Stage:** 1-in-progress
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

## Conductor-independent short rows

Oddness gives `c_q(2r)=c_q(r)`. The divisor formula bounds `|c_q(r)|≤r²`,
and `Σ μ²(q)/φ(q)²≤16`, hence `|parityStabilizerWeight Q (2r)|≤32r²`.
Fourth-order decay then gives, for every finite truncation and the complete row,

`|row|≤4D₄m⁴`, independently of Q.

Indeed each absolute summand is at most `2D₄m⁴/r²`, and
`Σ_{r≥1}r⁻²≤2`. Together with the cubic aperture-tail bound, this covers both
short rows and bulk truncation without paying an extra conductor logarithm.
The logarithmic phase, taper variation and upper pair boundary remain separate
parts of the literal model transport.

## Decay-preserving logarithmic transport

A stronger phase estimate may avoid the global Lipschitz loss. Write
`Ωhat_T(θ)=T K(Tθ)`. Fourth-order decay for the transform of `tΩ_T(t)`
gives `|Ωhat_T′(θ)|≤min(C T²,D T⁻²/θ⁴)`. On
`h/m≤1`, the logarithmic frequency lies between `h/(2m)` and `h/m`.
The phase error is therefore bounded by
`m⁻¹ min(Cu²,16D/u²)`, `u=Th/m`.

The positive lattice sums of this envelope and the corresponding weight-error
envelope `min(u,u⁻³)` are `O(m/T)`: both are bounded by a constant times
`(1+u)⁻²`, whose lattice sum telescopes. This predicts row error `O(1/T)`,
uniformly in the aperture. At bandwidth two, the global raw error would be
`O(T log²T)`. Keeping the vanishing taper at the upper endpoint gives
boundary cost `O(Xθ² log Q)`. With `θ=T^(-7/12)`, both the cubic tail and
this boundary term have power savings. These derivative and transport
claims remain to be formalized.

## Fixed-base consequence to audit

The conductor-independent bound predicts `row_Q(m)/log Q→0` for fixed m>0.
Combining this with the exact Poisson identity and the odd logarithmic mean
would give `spatialDual_Q(m)/log Q→Ωhat(0)/(2πm)`.
Thus, at a fixed base, the primitive correction cancels the entire leading
negative diagonal; along the moving support horizon the normalized row instead
tends to `−Ωhat(0)/2`. This consequence still needs its Lean proof.
