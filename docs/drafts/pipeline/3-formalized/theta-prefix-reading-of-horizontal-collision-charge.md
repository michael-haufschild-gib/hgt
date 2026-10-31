# Theta-prefix reading of horizontal collision charge

- **ID:** hef-theta-collision-reading
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-3010/obstacles-summary.md` Q2/charge.
- **Statement:** Finite integer theta prefixes read the actual multiplicity-weighted
  Xi collision charge on every height window, with a quantitative error and
  eventual exact integer rounding.

## Exact reading and error

Write `Q_k` for the finite theta curvature current, `R=ceil|T|+2`,
`χ=sourceCutoff(R+1)`, and `M_T` for total zero multiplicity in `[0,T)`.
Let

`K_q(z,w)=exp(−q(Im z−Im w)²)(1−exp(−q(Re z−Re w)²))`.

Multiply `K_(n²)` by compact smooth height collars in both variables to obtain
`F_n`. The collars include height zero and exclude height `T`. Let `B_n≥1`
be the defined compact bound for both separate Laplacians and the majorant's
Laplacian. Set

`k_n=n+R+4+ceil B_n`, `C_n=(Q_(k_n)⊗Q_(k_n))(F_n)`,
`ε_n=K B_n exp(−k_n⁴+56k_n²+62)`.

The universal constant `K≥0` is supplied by the scalar theta-current estimate.
The reading and its stage contain no zero locations.

Define `δ_T>0` as the minimum of nonzero real and imaginary coordinate gaps
among window zeros and nonzero imaginary coordinate gaps in the support disc
with endpoint marks `0,iT` adjoined. An empty gap set contributes one.
For every `n≥ceil(1/δ_T)`, Lean proves

`|C_n−charge(T)| ≤ ε_n(2Q_(k_n)(χ)+ε_n)+M_T² exp(−n²δ_T²)`.

Thus `C_n→charge(T)`, and eventually `floor(C_n+1/2)=charge(T)`.
The error uses actual divisor separations; no source-only stopping certificate
or bound below the first nonzero collision quantum is asserted.

## Proof

The scalar current estimate has one constant for all compact C² tests.
Apply it to each row and column of `F_n`; each error is bounded by `ε_nχ`.
Positivity and a telescoping product give `ε_n(Q_(k_n)(χ)+μ(χ))`.
The scalar estimate for `χ` bounds this by `ε_n(2Q_(k_n)(χ)+ε_n)`.
The stage dominates `B_n`, so `ε_n→0`; the fixed-majorant reading converges
and is bounded.

Once `nδ_T≥1`, the collars equal the exact window indicator on the entire
finite support divisor. On each pair, `K_(n²)` differs from the indicator
of distinct points sharing an ordinate by at most `exp(−n²δ_T²)`.
Summing with multiplicities gives the displayed finite-divisor error.
The ordered-pair sum is exactly the existing collision charge. Both errors
vanish; integrality gives eventual rounding.

## Lean declarations

In `GaloisForLFunctions/ConjugateDiagonalGeometry/`:

- `FiniteThetaProductCurrents`: `exists_uniform_finiteTheta_compact_current_error`,
  `abs_finiteThetaProductSourceReading_sub_finitePair_le`,
  `tendsto_thetaTestStage_error`.
- `HorizontalCollisionGaussian`: `abs_horizontalCollisionGaussian_pair_error`,
  `contDiff_collisionWindowPairTest`, `tendsto_collisionGaussian_error`.
- `ThetaPrefixesReadHorizontalCollisionCharge`: `finiteThetaCollisionReading_error`,
  `tendsto_finiteThetaCollisionReading`, `eventually_floor_finiteThetaCollisionReading`.

All three modules passed direct `lake --old env lean`; all printed transitive axiom
sets contain only `propext`, `Classical.choice`, and `Quot.sound`.
