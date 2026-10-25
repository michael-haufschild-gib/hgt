# Multiplicative Positivity Geometry: foundations

- **ID:** mpg-foundations
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2510/hard-obstacles-summary.md §4 (arithmetic forcing theory / multiplicative positivity geometry)
- **Statement:** Positivity of Euler log-coefficients is positive definiteness of the boundary divisor on the discrete group `ℝ`. This classifies, realizes and sharply bounds every boundary-line forcing law, shows the four boundary invariants are complete and minimal and blind to the interior, and fixes the exact certified width of interior forcing with growth input.

## Goal
Determine the complete content of multiplicative positivity. Programme:
`formal/GaloisForLFunctions/MultiplicativePositivityGeometry/` (umbrella
`MultiplicativePositivityGeometry.lean`, foundational `README.md`).

Non-circularity: ζ inputs are `Λ ≥ 0`, the residue at `1`, the Euler factorization and, for the
calibration only, the corpus inequality `RHTower.dlvp_half` with its pole bound. No zero-free region is
used as input.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: every module checked with `lake --old env lean`; axioms `[propext, Classical.choice, Quot.sound]`

## Paper proofs

**P1 Boundary positivity** (`isEvenPosDef_cosineTrace`, `IsBoundaryDivisor.isEvenPosDef`). For
`wᵢ ≥ 0`, `Σ_{j,k} c_j c_k Σᵢ wᵢ cos(λᵢ(x_j − x_k)) = Σᵢ wᵢ[(Σ_j c_j cos λᵢx_j)² + (Σ_j c_j sin λᵢx_j)²] ≥ 0`.
Gram forms are finite sums, so limits of positive-definite functions are positive definite
(`isEvenPosDef_of_tendsto`), and the boundary divisor is the pointwise limit of `x · trace(w(x))`.

**P2 Simple-pole rigidity** (`intValued_values`, `apply_add_of_eq_neg`, `intValued_mul`,
`boundary_zero_forces_double_pole`). The two-point form gives `|φ(h)| ≤ φ(0) = 1`, so integer
values lie in `{−1, 0, 1}`. If `φ(h) = −φ(0)`, the three-point vector `(s, s, −t)` at `0, h, −u`
gives a quadratic form in `(s, t)` with zero diagonal entry `2φ(0) + 2φ(h) = 0`. Its off-diagonal
entry must vanish: `φ(h + u) = −φ(u)`. Hence `φ(2h) = −φ(h) = 1`, and `{φ ≠ 0}` is a subgroup on
which `φ` is multiplicative.

**P3 Trichotomy** (`nonvanishingSubgroup_cyclic`, `boundary_trichotomy`,
`boundary_trichotomy_realized`). A dense subgroup meets `(−1, 1)` in infinitely many points, which
contradicts local finiteness. So the nonvanishing subgroup is cyclic, `cℤ`, and the character is
`k ↦ D(c)^{|k|}`. Realizations: ζ (`zeta_isBoundaryDivisor`), `progressionWeight (2π/c) (2π/c)` and
`progressionWeight (2π/c) (π/c)`.

**P4 Progression law** (`progression_gram`, `boundary_progression_zero_mass_le`). The constant
vector on `0, h, …, (N−1)h` gives `0 ≤ N D(0) + 2Σ_{r<N}(N−r−1) D((r+1)h)`. Divide by `N`, let
`N → ∞` with `D ≤ 0` on the progression: `Σ_r −D((r+1)h) ≤ D(0)/2`. Sharp: the double-pole profile
`2δ₀ − δ_{±t₀}` has mass `1 = D(0)/2` (`doublePoleProfile_progression_mass`).

**P5 ζ on the line** (`zetaBoundaryDivisor_eq`, `riemannZeta_boundary_ne_zero_of_posDef`). `D_ζ` is
integer valued with `D_ζ(0) = 1` and `D_ζ ≤ 0` off `0` (ζ has no poles there). By P2 a zero at `u`
would give `D_ζ(2u) = 1`, a pole. So `D_ζ = 1_{0}`.

**P6 Realization** (`twisted_isBoundaryDivisor`, `cosinePolynomial_profileCoeff_nonneg`,
`boundary_profile_iff`). Product to sum,
`cos(kt₀ log n) cos(u log n) = ½[cos(log n (u + kt₀)) + cos(log n (u − kt₀))]`, together with
`D_ζ = 1_{0}` gives the twisted divisor `Σ_k (a_k/2)(δ_{−kt₀} + δ_{kt₀})`. Conversely, the
Gram forms with coefficients `cos jθ` and `sin jθ` on `0, …, N−1` sum to `N P_d(θ) − C(θ)`, so
`P_d ≥ 0` by `N → ∞`.

**P7 Completeness and minimality** (`boundary_forcing_law`, `isolation_necessary`,
`simplicity_necessary`, `integrality_necessary`, `nonnegativity_necessary`). Forcing is P2 together
with `D ≤ 0` off `0`. The four countermodels:

- the alternating progression datum with `h = 2π`: `D(k) = (−1)^k`;
- the twist by `2 − 2cos θ`: `D = 2δ₀ − δ_{±1}`;
- the twist by `1 − cos θ`: `D = δ₀ − ½δ_{±1}`;
- the twist by `1 − 2cos θ`: `D = δ₀ − δ_{±1}`. It is not positive definite, since
  `D(1) = −D(0)` would force `D(2) = 1` (`signedTwist_not_posDef`). Therefore its weights are not
  all nonnegative (`signedTwist_weight_not_nonneg`).

**P8 Interior invisibility** (`isBoundaryDivisor_zero_of_bounded`, `interior_zero_invisible`).
`|x · trace| ≤ x Σᵢ wᵢ ≤ xC → 0`. The κ-shifted alternating datum has mass at most
`2ℓ/(1 − e^{−2ℓκ})`. Its trace is `Re(−Φ'/Φ)(s + κ)` for `Φ = periodicPoleZeta ℓ`
(`periodicPole_shifted_trace`), and `Φ(· + κ)` vanishes at `1 − κ + iπ/ℓ`.

**P9 Exact Fejér barrier** (`fejer_quadrature`, `cosinePolynomial_first_le_fejer`,
`fejer_barrier_attained`, `fejer_barrier_sharp`). Let `N = K + 2`, `α = π/N` and `θ_j = (2j+1)α`.
Telescoping `2 sin β Σ_j cos(φ + 2jβ)` shows `Σ_j cos kθ_j = 0` for `1 ≤ k ≤ N − 1`. The weight
`cos α − cos θ_j` is nonnegative because every node lies in `[α, 2π − α]`. Expanding
`(cos α − cos θ)cos kθ` gives the moments `N cos α`, `−N/2`, `0, …, 0`. So
`0 ≤ Σ_j (cos α − cos θ_j)P(θ_j) = N(a₀ cos α − a₁/2)`. Extremal: `b_j = sin((j+1)α)` has
`Σ b_j² = N/2` and `Σ b_j b_{j+1} = (N/2)cos α`, so `|Σ b_j e^{ijθ}|²` is attained.

**P10 Growth-to-forcing law** (`exclusion_iff_quadratic`, `exclusion_at_geometric_mean`,
`exclusion_iff`, `exclusion_iff_lt_width`, `exclusion_iff_restricted`). `A/δ + G < B/(δ+η)` is equivalent to
`Gδ² + (A + Gη − B)δ + Aη < 0`. AM–GM gives `Gδ² + Aη ≥ 2√A√(Gη) δ`. Hence exclusion forces
`(√A + √(Gη))² < B`. Conversely, `δ* = √A√(Gη)/G` gives the value `δ*((√A + √(Gη))² − B) < 0`. Since
`δ*² = Aη/G`, an input valid only on `(0, δ₁]` suffices once `Aη ≤ Gδ₁²`.

**P11 Certificate caps** (`fejer_width_cap`, `degree_one_excludes_nothing`,
`fejer_width_cap_lt_universal`, `multiFrequency_purchase_le_two`, `multiFrequency_width_cap`). With
`G = LS` and `S ≥ a₁`, we get `√(Lη)√a₁ ≤ √(LSη) < √a₁ − √a₀` and `√a₁ ≤ √ρ_K √a₀`, so
`√(Lη) < 1 − ρ_K^{−1/2}`. Moreover `ρ_K ∈ [1, 2)`, with `ρ₁ = 1`. Multi-frequency: sample
`(1 − cos γt)P(t) ≥ 0` at `t = jπ/M`, where `M` exceeds every `|u|`, `|u ± γ|`. Off resonance the
cosine sums are bounded by `1/|sin(vπ/2M)|`, so `0 ≤ N(a(0) − a(γ)/2) + K` for every `N`.

**P12 Calibration** (`xiZero_re_le_dlvp`, `dlvp_input_consistent`). `dlvp_half` is the input
`(3, 4, G_γ)` with `G_γ = (5/2) log γ + C > 2`. If `η < (2 − √3)²/G_γ`, the witness
`δ* = √3√(G_γ η)/G_γ < 1` lies in the range of `dlvp_half` and contradicts it. Barrier: P10 backwards.

## No-go closure
- **Exact killing theorem/mechanism:** positive certificates with constant growth input cannot reach a fixed strip (P10, P11). Boundary data cannot see interior zeros (P8).
- **Strongest positive survivor:** the exact two-sided law `width = (√B − √A)²/G` and the complete, minimal boundary forcing law (P7).
- **New insight:** the interior gain must come from the growth input `G` or from an interior object, never from the certificate. Integrality and pole isolation are independent necessary invariants.
- **Status:** all statements formalized; see README §5.

## Log
- 2026-10-25 — created in 1-in-progress; formalized (14 modules); moved to 3-formalized
