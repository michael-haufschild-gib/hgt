# Kubalalika Parity-Weighted Near-Diagonal Tail

- **ID:** `kubalalika-parity-weighted-near-diagonal-tail`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / RH-disproof proof repair
- **Scientific status:** `[PROVED HERE] [BRIDGE] [LEAN-PROVED] [NOT AN RH DISPROOF ALONE]`
- **Sources:** Granville--Ramaré, *Explicit bounds on exponential sums and the scarcity of
  squarefree binomial coefficients*, Theorems 9 and 9'; Babu--Sankaranarayanan,
  *On an estimate of a certain non-linear exponential sum*, Theorem 1; Tatenda Kubalalika,
  *The Riemann Hypothesis is False*, equations (18)--(30)
- **Statement:** The parity-restricted, von-Mangoldt-weighted near-diagonal tail actually produced
  by `2n=m+r` is `O(T^(53/54) log(T)^C)` for an absolute constant `C`, hence `o(T)`.

## Setup

Let

`epsilon=T^(-1/4)`, `V=T/((1+epsilon)log(T)^2)`, and `R=T^(1/4)`.

The required positive-offset tail is

`E_Lambda(T)=sum_(V<=m<=T(1+epsilon)) Lambda(m)
               sum_(R<=r<=epsilon*m, r congruent m mod 2)
                 exp(i*T*log(1+r/m))/r`.

The congruence is mandatory: `2n=m+r` with integral `n` is equivalent to
`r congruent m (mod 2)`. The preprint omits this restriction when passing from equations
(15)--(17) to its unrestricted `r`-sum.

The preprint's equation (23) controls an unweighted double sum and cannot be multiplied by
`Lambda(m)`. The proof below instead retains the arithmetic weight throughout.

## Reciprocal-Phase Stability Lemma

Put

`X=T*r/(2*pi)` and `H_(T,r)(u)=T/(2*pi)*log(1+r/u)`.

For every fixed derivative order `q>=0`, uniformly when `0<r/u<=epsilon`,

`H_(T,r)^(q)(u)=(-1)^q*q!*X*u^(-q-1)*(1+O_q(epsilon))`.        (1)

Indeed, the absolutely convergent expansion

`H_(T,r)(u)=T/(2*pi)*sum_(j>=1) (-1)^(j+1) r^j/(j*u^j)`

may be differentiated termwise. The `j=1` term is the displayed main term, and the remaining
series is bounded relatively by `O_q(r/u)`.

The same stability holds for every one-variable phase produced after Vaughan's identity. For
example, as a function of `u`,

`H_(T,r)(u*v_1)-H_(T,r)(u*v_2)`

has leading reciprocal parameter

`X*abs(1/v_1-1/v_2)`.

After factoring `abs(1/v_1-1/v_2)`, the `j`th Taylor term divided by the leading term is at most
`O_q((r/(u*min(v_1,v_2)))^(j-1))`. Thus its derivatives also differ from those of the
corresponding reciprocal phase by `O_q(epsilon)`.

The proofs of Granville--Ramaré Theorems 9 and 9' and Babu--Sankaranarayanan Theorem 1 use
Vaughan's identity followed only by finitely many exponent-pair derivative tests of precisely
these one-variable phases. Equation (1) therefore transfers their proofs, with changed absolute
implicit constants, from `e(X/u)` to `e(H_(T,r)(u))`, uniformly as `epsilon -> 0`.

Consequently, on any interval `I` contained in `[M,2M]` on which `r/m<=epsilon`,

`S_r(I)=sum_(m in I) Lambda(m) exp(i*T*log(1+r/m))`

satisfies the following three bounds, with logarithmic factors suppressed as `L^C`, where
`L=log(T)`:

1. if `M >= 2*X^(2/3)`, then

   `S_r(I) << M^(5/4)*X^(-1/4)*L^C`;                    (2)

2. if `c_1*X^(4/7)log(X)^(90/7) <= M <= c_2*X/log(X)^10`, then

   `S_r(I) << (X^(2/9)*M^(11/18)+M^(3/2)*X^(-1/2))*L^C`; (3)

3. if `M <= X^(3/5)/5`, then, taking `k=1` in Granville--Ramaré Theorem 9,

   `S_r(I) << X^(1/4)*M^(1/2)*L^C`.                    (4)

For sufficiently large `X`, the transition range between (2) and (4) lies inside the validity
range of (3), because `4/7<3/5<2/3<1`.

## Weighted Tail Theorem

As `T -> infinity`,

`E_Lambda(T)=O(T^(53/54)log(T)^C)=o(T)`                 (5)

for an absolute constant `C`.

## Parity Reduction

Split the outer sum into odd and even `r`.

For odd `r`, the congruence restricts `m` to odd integers. Removing that restriction changes an
unrestricted von-Mangoldt sum only at even prime powers. Since

`Lambda(m) != 0 and 2 divides m  implies  m=2^j`,

the total correction over any dyadic block is `O(log T)`; after the outer `1/r` summation it is
`O(log(T)^2)`, harmless compared with every power bound below.

For even `r`, the congruence restricts `m` to even integers, so again only `m=2^j` contribute.
Taking absolute values gives a total `O(log(T)^2)`. Therefore it is enough to apply the unrestricted
prime-sum estimates below to odd `r`; the parity correction itself is only polylogarithmic.

## Proof

Reverse the order of summation. For fixed odd `r`, the `m`-range is

`max(V,r/epsilon) <= m <= T(1+epsilon)`.

Partition it into dyadic intervals. There are `O(log T)` such intervals, and every one satisfies
`r/m<=epsilon`. Constants such as `2*pi` and `1+epsilon` do not affect any exponent below.

### Low reciprocal frequency

On blocks satisfying (2), use `M<<T` to obtain

`S_r(I) << T^(5/4)*(T*r)^(-1/4)*L^C
          = T*r^(-1/4)*L^C`.

After the outer `1/r` summation, their total contribution is

`<< T*L^C*sum_(r>=T^(1/4)) r^(-5/4)
  << T^(15/16)*L^C`.                                    (6)

### Transition frequency

The blocks satisfying (3) can occur only while `r<<T^(2/3)` up to an absolute endpoint
constant; beyond that point all `M<<T` blocks satisfy (4). Bounding `M` by `T` in (3) gives

`S_r(I) << (T^(5/6)*r^(2/9)+T*r^(-1/2))*L^C`.

Therefore their total contribution is

`<< T^(5/6)*L^C*sum_(r<=C_0*T^(2/3)) r^(-7/9)
    +T*L^C*sum_(r>=T^(1/4)) r^(-3/2)`

`<< T^(5/6+4/27)*L^C + T^(7/8)*L^C
  = T^(53/54)*L^C + T^(7/8)*L^C`.                       (7)

### High reciprocal frequency

On blocks satisfying (4),

`S_r(I) << (T*r)^(1/4)*T^(1/2)*L^C
          = T^(3/4)*r^(1/4)*L^C`.

Since `r<=epsilon*T(1+epsilon)<<T^(3/4)`, their total contribution is

`<< T^(3/4)*L^C*sum_(r<=C*T^(3/4)) r^(-3/4)
  << T^(15/16)*L^C`.                                    (8)

For the constant-sized overlap near `r=C_0*T^(2/3)`, either (3) or (4) gives the same claimed
power saving after enlarging the implicit constant. Equations (6)--(8), including the dyadic
logarithmic loss and the polylogarithmic parity corrections, prove (5).

## Consequence for the Claimed Disproof

The wrong-variable derivative in the preprint remains a real error, and its original passage from
the unweighted equation (23) to the von-Mangoldt-weighted equation (25) remains invalid. The theorem
above supplies a different repair: Vaughan's identity is applied before estimating the phase.

This closes only the parity-restricted near-diagonal weighted tail. It does not rescue the claimed
disproof. The same parity condition changes the small-offset Fourier main term from a sawtooth to a
square wave, and the corrected large-`n` linear term cancels the small-`n` Landau--Gonek term exactly;
see `../needs-audit/kubalalika-parity-corrected-main-term-cancellation.md`.

## Lean formalization map

Every statement of the theorem is unconditionally proved in Lean 4 (axiom audit: only
`propext, Classical.choice, Quot.sound`).  Build log:
`docs/drafts/pipeline/1-in-progress/kubalalika-weighted-tail-lean.md`.

The Lean chain proves the stronger exponent `15/16` (`= 0.9375 < 53/54 = 0.98148`), because the
two Vaughan parameters are chosen SEPARATELY — `U ≍ T^{1/2}`, `V ≍ T^{1/8}` — and are then
independent of the shift `r`.  Equation `(5)` follows with room to spare.

| Card item | Lean declaration | Module |
|---|---|---|
| `E_Λ(T)` itself | `weightedNearDiagonalTail`, `kubalalikaWeightedTail` | `RHTower/Sieve/WeightedTailDef.lean` |
| parity reduction (odd/even `r`, powers of two) | `norm_sum_even_set_le`, `norm_sum_parity_set_le`, `norm_weightedTail_le_of_blockBound` | `RHTower/Sieve/ParityGeneralSet.lean` |
| reciprocal-phase stability `(1)` and the block estimate feeding `(2)`–`(4)` | `exists_norm_sum_vonMangoldt_ndPhaseExp_le_secondThird_mixed_hybrid` | `RHTower/Sieve/VaughanSecondThirdMixedHybridBlock.lean` |
| block envelope in explicit monomials | `kubalalikaBlockPower`, `exists_norm_sum_vonMangoldt_ndPhaseExp_le_kubalalika_power` | `RHTower/Sieve/KubalalikaPowerEnvelope.lean` |
| the four root terms and the Type-I/Type-II totals | `typeIIHybridVaughanRootEnvelope_le_power`, `secondThirdMixedVaughanTypeIEnvelope_le_power`, `typeIIHybridPieceEnvelope_le_power` | `RHTower/Sieve/KubalalikaPowerEnvelope.lean` |
| second-derivative fibre condition discharged | `nearDiagonalLambda_le_one_of_fibre_crossover`, `exists_norm_sum_vonMangoldt_ndPhaseExp_le_kubalalika_power'` | `RHTower/Sieve/KubalalikaFibreCondition.lean` |
| the parameter substitution `U ≍ T^{1/2}`, `V ≍ T^{1/8}` | `kubalalikaScalePower`, `kubalalikaBlockPower_le_scale` | `RHTower/Sieve/KubalalikaBlockScale.lean` |
| dyadic decomposition of the `m`-range | `sum_Ico_monotone_partition`, `norm_sum_Ico_le_of_blocks` | `RHTower/Sieve/KubalalikaDyadic.lean` |
| the harmonic `r`-total `(6)`–`(8)` | `sum_kubalalikaScalePower_div_le` | `RHTower/Sieve/KubalalikaRSum.lean` |
| every scalar side condition of the block estimate | `KubalalikaLarge`, `eventually_kubalalikaLarge`, `KubalalikaLarge.block_conditions` | `RHTower/Sieve/KubalalikaLargeScale.lean` |
| **`(5)`** | `exists_norm_kubalalikaWeightedTail_le`, `kubalalikaWeightedTail_isBigO` | `RHTower/Sieve/KubalalikaTailBound.lean` |
| **`(5)`, the `o(T)` form** | `kubalalikaWeightedTail_isLittleO` | `RHTower/Sieve/KubalalikaTailBound.lean` |

Mathlib gaps closed on the way, all reusable: the truncated dyadic partition of an integer
interval into blocks with `B ≤ 2A`; the explicit power form of the mixed second/third-derivative
Vaughan envelope; and the statement that a fixed multiple of a fixed power of `1 + log x` is
eventually below every positive power of `x`.

## Gates

- [x] Original invalid insertion of `Lambda(m)` rejected.
- [x] Reciprocal-phase prime theorems located in primary sources.
- [x] Phase-stability lemma proved for all Vaughan one-variable descendants.
- [x] Full `r,m` range covered by three prime-sum regimes.
- [x] Mandatory congruence `r congruent m (mod 2)` restored.
- [x] Odd-`r` restriction reduced to the unrestricted prime sum plus powers of two.
- [x] Even-`r` contribution reduced entirely to powers of two.
- [x] Weighted tail proved `o(T)` with exponent `53/54`.
- [x] Do not formalize as an RH-disproof dependency: the corrected main terms cancel.
- [x] Unconditional Lean 4 proof of `(5)`, with the stronger exponent `15/16`.
- [x] Axiom audit: `propext, Classical.choice, Quot.sound` only.
- [x] All seven new modules wired into `GaloisForLFunctions.RHTower`.

## Log

- 2026-07-17 -- Proved without numerical computation. The first unweighted `7/8` argument was not
  promoted; the arithmetic weight is instead retained through Vaughan's identity and reciprocal-phase
  exponent-pair bounds.
- 2026-07-17 -- Restored the parity condition omitted in the source. It costs only powers-of-two
  corrections in the tail estimate, but it is decisive for the main term.
- 2026-08-29 -- Formalized. The exponent budget was recomputed with `U` and `V` chosen separately:
  `U = ⌈T^{1/2}⌉`, `V = ⌈T^{1/8}⌉`, both independent of `r`, equalise the three surviving
  harmonic totals at `T^{15/16}`.  With `U = V` the same budget gives exactly `T` and the argument
  fails by a hair.  The second-derivative fibre condition, false for the naive range, is
  dischargeable from the crossover hypothesis alone once `T r` dominates the block scale `A` by an
  absolute factor.
