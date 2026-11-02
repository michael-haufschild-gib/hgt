# Cone cancellation with two-sided polynomial weights

- **Stage:** 3-formalized.
- **Parent:** SC2; strengthens `../3-formalized/two-prime-cone-positive-moment-obstruction.md`.
- **Theorem:** For every pair of distinct primes and every `0<d<D`, there is
  countable distinct positive atomic support with mass two, real parts in
  `[d,D)` cofinal at `D`, exact positive-cone cancellation, linear height count,
  and `(1+|gamma|)^(-8) <= w <= C(1+|gamma|)^(-8)` for one `C>0`.
  Its even Hermitian quartet kernel has mixed cone coupling at most twenty.
- **Scope:** Freely chosen weights. They need not equal the prescribed complex
  spline factor times an integer zero multiplicity.

## Finite Fourier grid

Let `Omega={0} union S union (-S)`, `M=|Omega|`, maximum absolute frequency
`L>0`, and minimum separation `sigma>0`. Put
`h=pi/(2L)` and `gamma_j=H+jh`, `0<=j<n`.
The geometric-series identity and `|1-exp(i theta)|>=2|theta|/pi` for
`|theta|<=pi` give

`|(1/n) sum_j exp(i(u-v)gamma_j)| <= 2L/(n sigma)` for `u!=v`.

Choose `n>=16ML/sigma`. The Fourier Gram `G` has diagonal one and induced
column-sum norm `||G-I||_1<=1/8`, uniformly in the translation `H`.
For target vector `b_0=A`, `b_s=-r_s`, `b_-s=-conj(r_s)`, with
`sum_s |r_s|<=A/16`, solve `Gc=b`. Finite-dimensional injectivity follows
from `||c||_1<=||Gc||_1+||c||_1/8`, hence so does surjectivity. Then

`||c-A e_0||_1 <= (8/7)(2 sum_s |r_s|+A/8) <= 2A/7`.

Set `v_j=(1/n) sum_u c_u exp(-iu gamma_j)` and `w_j=Re(v_j)`.
The conjugate symmetry of the target implies that taking real parts
preserves every target moment. Thus `sum w_j=A`, exact correction holds,
and `A/(2n)<=w_j<=3A/(2n)`. The grid has length
`nh=O(M/sigma)` and distinct nodes. This replaces the exponentially large
convolution cloud by polynomially many nodes when separation is polynomial.

## Infinite schedule

Use `delta_k=D-(D-d)2^(-k)` and block masses `A_k=exp(-4^k)`.
The level gap is comparable to `2^(-k)`. Square frequency cutoffs
`N_k=ceil(C*8^k)`, for a sufficiently large fixed `C`, make the next finite
uncancelled tail at most a fixed small multiple of `A_(k+1)`. Indeed every
new frequency is at least `min(a,b)*N_k`, while there are at most
`(N_(k+1)+1)^2` such frequencies. Thus the tail is bounded by

`(N_(k+1)+1)^2 exp(-(delta_(k+1)-delta_k) min(a,b) N_k)`.

The damping exponent is proportional to `4^k`; the cardinal loss is only
exponential in `k`. No infinite-tail estimate is needed at the extension step.
The existing two-prime Baker lower bound gives polynomial separation in
`N_k`, hence only exponential growth in `k` for grid sizes `n_k`, lengths
`B_k`, and cumulative atom counts.

Let `F_k=sum_(j<=k) n_j`, take frequency radii at least one, and set

`H_k=max((2n_k/A_k)^(1/8), (pi+2)F_k)`.

The grid span is at most `pi*n_k/2`, so every height lies in `[H_k,2H_k]`
and exceeds its global atom rank. The lower weight bound follows from
`H_k^8>=2n_k/A_k`. For the upper bound, `1+gamma<=3H_k` and

`A_k H_k^8/n_k <= max(2,(pi+2)^8 A_k F_k^8)`.

The series `sum_k A_k F_k^8` converges because `F_k` grows at most
exponentially. It bounds all these quantities uniformly, including the first
blocks. Thus the height placement gives both eighth-power weight bounds
and the linear counting estimate without a separate finite-exception argument.
Exact moments follow from positive correction and summable mass. Separate
real levels distinguish blocks.

The total mass `M=sum_k A_k` lies in `(0,2]`. Rescaling by `2/M>=1` gives
mass exactly two, preserves the lower bound, and changes only the upper
constant. The established quartet argument then gives cone coupling at most
twenty for the strengthened model as well.

## Lean status

`ConeMoments.exists_two_prime_spline_sized_cone_model` in
`ArithmeticCouplingTheory/ConeMoments/SplineSizedPositiveConeNullseries.lean`
proves the full theorem. Its final direct Lean audit passes with transitive
axioms only `propext`, `Classical.choice`, and `Quot.sound`; the umbrella is wired.
The height count is an embedding of atoms with `|Im z|<=T` into `Fin floor(T)`.
Each cone moment is a `HasSum` statement, including convergence.

Supporting declarations, all in namespace `ConeMoments` and independently
audited with the same axiom set:

- `PositiveGridCorrection.lean`: `exists_positive_grid_correction`, including
  exact positive correction and node bound `16*|Omega|*L/sigma+1`.
- `QuantitativeConeCutoffs.lean`: `exists_two_prime_grid_schedule`,
  `summable_weighted_prefix_count`, and `correctionMass_tsum_le_two`.
- `EighthPowerHeightBounds.lean`: `height_weight_bounds`, deriving both weight
  bounds from `A F^8<=K`.
- `PositiveGridNullseries.lean`: `exists_grid_weights`,
  `hasSum_grid_atomic_moment`, and `PositiveGridSchedule.atomRank_injective`.

Thus polynomial upper and lower weight bounds, sparse counting, and actual
two-prime clock separation do not suffice for the generic cone implication.
The [exact-coefficient construction](two-prime-cone-prescribed-spline-weights.md)
also imposes exact spline coefficients and unit multiplicities. Actual SC2
remains open.
