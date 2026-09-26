# Dyadic boundary primitive — root research

- **Stage:** 5-failed (generic winding rigidity); exact positive survivor formalized
- **Type:** FALSIFIED generic rigidity claim; THEOREM (Lean) classification and arbitrary-winding family
- **Owner:** root; independent of other agents' logs
- **Goal:** attack the proposed source-boundary winding producer for RH, not replace RH by a classification problem.
- **Parent claim under attack:** `docs/reports/route-proposals/route2.md`, claim (ii): the dyadic identity of the actual theta boundary potential forces zero off-axis winding.

## Frozen test

Determine exactly what the identity

`F(r+1)+F(r)=F(4r)/2`

forces on bounded 2-periodic boundary data. A proof using this identity must distinguish the actual theta potential from every other solution. Classification is a derived test, not a new universal conjecture.

## Plan

1. Prove or refute rigidity of this identity with the stated continuity, mean and endpoint anchors.
2. Extract and formalize the exact positive survivor: complete bounded-solution normal form and sharp finite-depth remainder.
3. Return the unresolved odd primitive to the actual theta source and attack its complex phase. Do not infer winding from uniqueness or from the dyadic identity alone.

## Paper attack

Put `A(r)=(F(r)-F(r+1))/2`. Period 2 makes `A(r+1)=-A(r)`.
The dyadic identity is exactly `F(r)=A(r)+F(4r)/4`. Iteration gives

`F(r)=sum_{j<N} 4^(-j) A(4^j r)+4^(-N) F(4^N r)`.

If `|F|<=M`, the remainder is at most `M 4^(-N)`. Hence

`F(r)=sum_{j>=0} 4^(-j) A(4^j r)`.

Conversely every bounded anti-periodic `A` gives this uniformly convergent series, a bounded 2-periodic solution; continuous `A` gives continuous `F`. Its anti-periodic part is exactly `A`. Thus the identity retains a whole function, not a scalar degree of freedom.

For `A_m(r)=c exp(-i*pi*m*r)`, each positive odd integer `m` gives a solution with frequencies `m*4^j`, mean zero, and

`F_m(0)=4c/3`, `F_m(1)=-2c/3`.

Taking `c=pi^2/8` matches both theta endpoint values for every odd `m`. Distinct odd seeds have disjoint frequency chains, hence give distinct solutions. This does not make them modular theta sources or prove a counterexample to RH.

## Whole-route consequence

The proposed winding law remains unproved. Dyadic self-similarity, continuity, mean zero and the two endpoint anchors do not recover the theta boundary data. A valid proof must act on the actual odd primitive (or another condition that constrains it), and explain how that condition controls winding. This is a diagnosis of missing content, not retirement of the whole boundary route.

## Second attack: does winding nevertheless remain fixed?

**Test frozen after the classification:** perhaps the free primitive changes the boundary function but its winding remains fixed under the stated constraints.

**Counterexample:** set `A_k(r)=exp(-i*pi*(2k+1)*r)` and reconstruct `F_k` by the exact series above. Its first-term remainder satisfies `|F_k(r)-A_k(r)|<=1/3`. Hence `F_k` never vanishes, and `F_k/A_k` stays in the radius-1/3 disk centered at 1. That quotient has a continuous periodic logarithm and winding zero. Therefore

`wind(F_k, [0,2])=wind(A_k, [0,2])=-(2k+1)`.

Every `F_k` is continuous, 2-periodic, obeys the exact dyadic law, and has the same endpoint values `4/3` and `-2/3`. Mean zero follows already from the law and periodicity: integrating over one period gives `2I=I/2`. Scaling every `F_k` by `pi^2/8` gives exactly the theta endpoint values, with unchanged winding. All Fourier coefficients in these examples are nonnegative, supported on one negative-frequency chain.

**Whole-route consequence:** the listed boundary constraints allow unbounded winding even for nowhere-zero loops. This disproves generic winding rigidity, not the proposal's still-unspecified mapping from the literal theta boundary data to the renewal loop. Any valid argument must use additional arithmetic structure and prove that mapping preserves the required index information.

**Positive survivor:** the complete anti-periodic primitive, exact reconstruction, geometric remainder and norm bounds identify precisely what dyadic renormalization retains. This is stronger than a counterexample alone.

## Status

Exact normal form and arbitrary-winding family verified in `formal/GaloisForLFunctions/RHTower/ThetaBoundaryDyadicClassification.lean`, namespace `RHTower.DyadicBoundary`. Source check and named leaf build pass. All 36 public theorem axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`. The leaf is imported by `RHTower.lean`. Repository lint reports five unrelated missing umbrella imports (`ModularAxisSourceTransform`, `ThetaGroupDeformationPrimeTwo`, `ThetaGroupFormCuspBounds`, `ThetaGroupHauptmodulForms`, `ThetaGroupOffLineStripZero`); none of those files was modified here. No numerical experiment or global novelty claim. The actual theta odd primitive is `sum_{n odd, n>=1} exp(-i*pi*n^2*r)/n^2`; the dyadic law transports these coefficients and imposes no relation between distinct odd squares.

## No-go closure

- **Killing theorem:** `exists_arbitrary_odd_winding` supplies an unconditional family with every winding `-(2*k+1)`, satisfying continuity, nonvanishing, period 2, the dyadic law, zero mean and common normalized endpoint values.
- **Positive survivor:** `reconstruction_primitive`, `primitive_reconstruction`, `finite_reconstruction_error`, and `reconstruction_bound` give the full bounded solution space and quantitative reconstruction.
- **New insight:** odd anti-periodic data carry the index information; dyadic transport does not remove it. The source-specific renewal index map remains the open core.
- **Status:** exact survivor is Lean-closed and axiom-audited. This retires only generic dyadic winding rigidity. The literal theta renewal route and RH remain open.
