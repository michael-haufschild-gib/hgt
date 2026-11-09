# Top coefficients force excursion density

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Contribution count:** One (#16), including coefficient recovery, infinite-rank transfer, actual-zeta specialization, and sharpness.
- **Obstacles:** B13, B112; quantitative detection of isolated exceptional zero layers.
- **Statement:** Let an absolutely summable tower have a finite visible top of modulus `R>0`, with all remaining modes of modulus at most `r<R`. Merge coincident top points, obtaining distinct unit phases `p_j` and coefficients `c_j`, and put `H=sum |c_j|>0`. For `0<=rho<R` and `C>=0`, every window `[M,M+N)` contains at least `(N |c_j|-K_j)/H` levels with `|S(n)|>C rho^n`, where
  `K_j=sum_(i!=j) 2|c_i|/|p_i/p_j-1| + C/(1-rho/R) + W/(1-r/R)`
  and `W=sum |b_i|`. Thus every proportion below `max |c_j|/H` holds in all sufficiently long windows, uniformly in their starting point. The coefficient ratio is sharp for equally weighted roots of unity.
- **Novelty boundary:** Existing exceptional-rank results give one excursion per rank-sized window; continuous-lag results give positive upper density. This law gives a coefficient-dependent lower density and an explicit bounded discrepancy for every discrete window. Unequal merged coefficient norms improve the rank bound. Infinite lower layers enter only through their trace norm.

## Proof

Write `P(n)=sum c_i p_i^n`. Demodulation by `p_j^n` gives
`sum_(n=M)^(M+N-1) P(n)/p_j^n = N c_j + sum_(i!=j) c_i (p_i/p_j)^M sum_(n<N) (p_i/p_j)^n`.
Each off-diagonal ratio has modulus one and differs from one, so its geometric sum has norm at most `2/|p_i/p_j-1|`. Consequently `N|c_j|<=sum_window |P(n)|+D_j`, with the first term in `K_j` equal to `D_j`.

Absolute summability splits the tower into its finite top and remainder. Division by `R^n` gives `S(n)/R^n=P(n)+e(n)` with `|e(n)|<=W(r/R)^n`. At a level below the excursion threshold, `|P(n)|<=C(rho/R)^n+W(r/R)^n`; at every other level, `|P(n)|<=H`. Summing gives
`N|c_j|<=H count(excursions)+D_j+C/(1-rho/R)+W/(1-r/R)`.
The two geometric sums are bounded independently of `M,N`. For `dH<|c_j|`, choose `N0>K_j/(|c_j|-dH)` to obtain `dN<=count` for every `M` and `N>=N0`.

For `k` equally weighted `k`th roots of unity, `P(n)=k` on multiples of `k` and zero elsewhere. Their coefficient ratio is `1/k`, and exactly `n` levels in `(0,kn]` have nonzero sums. Thus no universally larger coefficient-ratio bound holds, already for zero threshold.

Failure of the actual zeta AAL supplies a finite isolated rightmost layer through `not_asymptoticAbscissaLaw_iff_hasIsolatedTop`. At every positive base, the actual lag weights are absolutely summable and each merged coefficient is nonzero because its real part is positive. Apply the tower law with `R=exp(ell(Theta-1/2))`, `r=exp(ell(Theta2-1/2))`, and `rho=exp(a ell)` for any `a<Theta-1/2`. This is an unconditional implication from failure of AAL; it does not establish AAL or RH.

## Corpus audit

- `TheExceptionalRankDecidesTheWindow`: bounded-gap detection and trace cost, without coefficient-density bounds.
- `TheRankBarrier`: periodic sharpness examples and divisibility counts.
- `WeilLagFunctionDensityZeroExcursion`: continuous upper-density obstruction, without uniform discrete-window density.
- `UnitPowerSumOscillation`: geometric-sum estimate and real-part oscillation; no weighted density law.
- `TheAmplifierLaw`: qualitative coefficient recovery, without finite-window discrepancy.

## Lean certificate

Paths are relative to `formal/GaloisForLFunctions/InfiniteRankWeilTheory/`.

| Module | Certificate |
|---|---|
| `TopCoefficientWindowDensity.lean` | `coefficient_le_window_norm_add_interference`, `coefficient_le_excursion_count_add_error`, `root_packet_excursion_count` |
| `IsolatedTopExcursionDensity.lean` | `isolatedTop_excursion_count`, `isolatedTop_uniform_excursion_density` |
| `ZetaTopCoefficientDensity.lean` | `not_asymptoticAbscissaLaw_implies_coefficient_density` |

All three modules pass direct `lake --old env lean` audits without warnings. Their capstones use only `propext`, `Classical.choice`, and `Quot.sound` transitively. All three modules are umbrella-wired.

The actual-zeta capstone supplies the isolated top and proves positivity of every merged coefficient norm. It quantifies over every positive base, every top coefficient, every proportion below its share, every sub-top exponent, and every nonnegative threshold constant. No additional analytic premise is introduced. An arithmetic bound excluding these forced excursions remains open; AAL and RH are not established.
