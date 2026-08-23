# Kubalalika Unweighted Near-Diagonal Tail

- **ID:** `kubalalika-unweighted-near-diagonal-tail`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / insufficient unweighted shadow
- **Scientific status:** `[PROVED HERE] [INSUFFICIENT] [FORMALIZED] [NOT AN RH DISPROOF]`
- **Source:** Tatenda Kubalalika, *The Riemann Hypothesis is False*, 2026 preprint,
  equations (18)--(26); Titchmarsh's discrete second-derivative test
- **Statement:** The unweighted near-diagonal exponential tail underlying the claimed
  Landau--Gonek disproof is `O(T^(7/8))`, hence `o(T)`. This does **not** control the required
  von-Mangoldt-weighted tail.

## Setup

Let

`epsilon=T^(-1/4)`, `V=T/((1+epsilon)log(T)^2)`, `R=T^(1/4)`.

The unweighted shadow of the tail produced after writing `2n=m+r` has the form

`E_0(T)=sum_(V<=m<=T(1+epsilon))
          sum_(R<=r<=m*epsilon) exp(i*T*log(1+r/m))/r`.

The tail actually required by the preprint is

`E_Lambda(T)=sum_(V<=m<=T(1+epsilon)) Lambda(m)
               sum_(R<=r<=m*epsilon) exp(i*T*log(1+r/m))/r`.

Only an `o(T)` estimate is required downstream. The preprint instead claims the stronger
`O(T^(3/4)log(T)^2)` estimate after differentiating its phase in `r` while applying an exponential
sum theorem to the sum over `m`. That invocation does not match the summation variable.

## Theorem

As `T -> infinity`,

`E_0(T)=O(T^(7/8)+T^(3/8)log(T))=o(T)`.

This theorem makes no claim about `E_Lambda(T)`.

## Proof

Reverse the order of summation. For fixed `r`, the `m`-range is

`max(V,r/epsilon) <= m <= T(1+epsilon)`.

Set

`F_r(u)=T/(2*pi)*log(1+r/u)`.

Direct differentiation in the actual summation variable gives

`F_r''(u)=T*r*(2*u+r)/(2*pi*u^2*(u+r)^2)>0`.             (1)

Partition the `m`-range into dyadic blocks `M<=m<2M`. Since `r<=epsilon*m` and
`epsilon<1/2` for large `T`, equation (1) gives uniformly on such a block

`F_r''(u) asymp T*r/M^3`.                                (2)

The discrete van der Corput second-derivative estimate applied in `m` therefore yields

`|sum_(m in block) exp(2*pi*i*F_r(m))|
  << M*sqrt(T*r/M^3) + sqrt(M^3/(T*r))
  = sqrt(T*r/M) + M^(3/2)/sqrt(T*r)`.                    (3)

Across the dyadic blocks, the first term decreases geometrically and the second increases
geometrically. Since `M>=V` and `M<=T(1+epsilon)`, summing (3) gives

`|sum_m exp(i*T*log(1+r/m))|
  << sqrt(T*r/V) + T/sqrt(r)
  << sqrt(r)*log(T) + T/sqrt(r)`.                         (4)

Now `R<=r<=epsilon*T(1+epsilon)<<T^(3/4)`. Hence

`sum_r (1/r)*(sqrt(r)*log(T)+T/sqrt(r))
  << log(T)*sum_(r<=T^(3/4)) r^(-1/2)
     + T*sum_(r>=T^(1/4)) r^(-3/2)
  << T^(3/8)log(T)+T^(7/8)`.                              (5)

Equation (5) is precisely the asserted estimate for `E_0(T)`.

## Why This Does Not Repair the Claimed Disproof

The preprint's equations (21)--(22) do not prove its displayed `T^(3/4)` bound: equation (21)
differentiates in the integration variable, while equation (22) estimates a sum over `m`. The
correct curvature is (1). The same derivation does not estimate `E_Lambda(T)`: from
`Lambda(m)<=log(T)` one may not infer

`|sum_m Lambda(m)e(F_r(m))| <= log(T)|sum_m e(F_r(m))|`.

That inequality is false for general nonconstant nonnegative weights. Taking absolute values before
inserting the bound for `Lambda` destroys the oscillatory cancellation and only gives the trivial
order, which is not `o(T)`. A valid repair therefore needs a prime-weighted exponential-sum theorem,
for example a Vaughan-identity Type I/II analysis specialized to `F_r`; none is supplied in the
preprint. Such an analysis is now supplied independently, with the mandatory parity restriction
restored, in `kubalalika-parity-weighted-near-diagonal-tail.md`.

The unweighted theorem is retained as exact positive residue and as the phase-curvature input to
such a future weighted analysis. It is not a repair of the RH-disproof argument.

## Gates

- [x] Wrong-variable derivative identified.
- [x] Correct summation-variable curvature computed.
- [x] Dyadic second-derivative estimate proved on paper.
- [x] Unweighted double tail shown to be `o(T)`.
- [x] Invalid insertion of the von Mangoldt weight isolated.
- [x] Prove a uniform prime-weighted exponential-sum estimate strong enough to give
  `E_Lambda(T)=o(T)`.
- [x] Unweighted theorem formalized unconditionally in Lean 4.

## Log

- 2026-07-17 -- Proved the unweighted estimate during the RH-false audit, then rejected the proposed
  weighted promotion: the von Mangoldt weight cannot be pulled through an oscillatory cancellation
  bound. Demoted to an insufficient unweighted shadow before any Lean formalization.

## Lean formalization

All five displayed steps are closed unconditionally in Lean 4 (axioms: `propext`,
`Classical.choice`, `Quot.sound` only).

| Step | Lean |
|---|---|
| (1) curvature `F_r''` | `RHTower.nearDiagonalPhaseD2`, `RHTower/NearDiagonalPhaseCurvature.lean` |
| (2) block pinning `F_r'' asymp T r/M^3` | `RHTower.nearDiagonalLambda_le_D2`, `RHTower.D2_le_nearDiagonalLambda` (ratio `90`) |
| (3) single-block van der Corput | `RHTower.norm_nearDiagonalBlock_le_bound`, `RHTower/NearDiagonalBlockBound.lean` |
| (4) dyadic sum over blocks | `RHTower.norm_nearDiagonalSum_le_final`, `RHTower/NearDiagonalInnerSum.lean` |
| (5) shift summation | `RHTower.norm_kubalalikaTailSum_le`, `RHTower/NearDiagonalTailBound.lean` |

Supporting modules: `RHTower/NearDiagonalDyadicSum.lean` (dyadic recursion with the increasing
scale kept symbolic), `RHTower/NearDiagonalGeometricCollapse.lean` (geometric collapse of the
symbolic top-scale sum), `RHTower/SqrtTelescopeSums.lean` (`sum_r r^{-1/2} <= 2 sqrt(N)` and
`sum_{r>=R} r^{-3/2} <= 2/sqrt(R-1)`, both by telescoping).

The capstone is

```lean
theorem norm_kubalalikaTailSum_le :
    ∀ᶠ T : ℝ in Filter.atTop,
      ‖kubalalikaTailSum T‖
        ≤ 5000 * (T ^ ((7 : ℝ) / 8) + T ^ ((3 : ℝ) / 8) * Real.log T)
```

with

```lean
def kubalalikaEps (T : ℝ) : ℝ := 1 / Real.sqrt (Real.sqrt T)
def kubalalikaTailSum (T : ℝ) : ℂ :=
  nearDiagonalTail T (kubalalikaEps T)
    ⌈T / ((1 + kubalalikaEps T) * (Real.log T) ^ 2)⌉₊
    ⌊T * (1 + kubalalikaEps T)⌋₊
    ⌈Real.sqrt (Real.sqrt T)⌉₊
```

so the three localization parameters are exactly `epsilon = T^{-1/4}`,
`V = T/((1+epsilon) log(T)^2)`, `R = T^{1/4}`, with the natural-number ranges obtained by the
floor/ceiling of the card's real endpoints.

Two deviations from the paper proof, both strengthening it:

- Equations (2)–(4) are proved with explicit numerical constants (`90`, `2500`, `22`, `720`, `12`)
  rather than `<<`, so equation (4) is a fully effective inequality.
- The dyadic recursion of (4) keeps the increasing term as the symbolic sum
  `sum_{j<J} sqrt((A 2^j)^3)` throughout the induction and collapses it geometrically only
  afterwards. Peeling the bottom block with the increasing term already evaluated at the top scale
  leaves an unabsorbable `A^{3/2}`, so the naive induction does not close.

The final constant is `5000`, valid for every `T >= 20^8`.

## Log

- 2026-08-23 -- Formalized unconditionally in Lean 4 and promoted to stage 3. The card's negative
  half (the von Mangoldt weight cannot be pulled through the oscillatory bound) is unchanged and
  remains prose; only the positive unweighted theorem is formalized, which is exactly what the card
  asserts.
