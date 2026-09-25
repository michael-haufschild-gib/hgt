# Bernstein flux rigidifies symmetric prime-power gauges of the theta source

- **ID:** theta-prime-power-bernstein-gauge-rigidity
- **Stage:** 2-fully-proven (paper)
- **Type:** exact infinite gauge classification and charge rigidity
- **Routes:** STC, CSB, U, K-RVM, MPLF, RHist; source-side comparison with EDQ
- **Status:** [PROVED HERE ON PAPER] [LEAN FORMALIZATION OPEN] [NOT AN RH PROOF]
- **Dependencies:** the literal theta flux and half-charge in [theta-euler-critical-boundary-mass-escape.md](theta-euler-critical-boundary-mass-escape.md), plus the finite Bernstein--Widder representation in [BernsteinWidder.lean](../../../../formal/GaloisForLFunctions/HTGeometry/BernsteinWidder.lean) and finite-measure Laplace uniqueness in [RepairedFrequencyDensityLaplace.lean](../../../../formal/GaloisForLFunctions/HTGeometry/RepairedFrequencyDensityLaplace.lean). No numerical computation is used.

## Statement

Write `k` for the positive even completed theta source. Its critical flux

`H_k(x)=∫_[x,∞) exp(y/2) k(y) dy`

has the exact Laplace form, with `t=exp(2x)`,

`b_k(t):=t^(-3/2) H_k(log(t)/2)=2π∑_(n≥1) n² exp(−πn²t)`.       (1)

Fix a prime `p` and a real symmetric sequence `(c_j)_(j∈ℤ)`, `c_(-j)=c_j`, satisfying

`∑_(j∈ℤ) |c_j| p^(|j|/2)<∞`.                                  (2)

Define the two-sided translation gauge

`g(x)=∑_(j∈ℤ)c_j k(x+j log p)`,

its ordinary multiplier `M₀=∑_j c_j`, and its critical multiplier
`M₁/₂=∑_j c_j p^(j/2)`. All sums and the corresponding source moments converge absolutely. Put

`b_g(t)=t^(-3/2)∫_[log(t)/2,∞) exp(y/2)g(y)dy`.

**Theorem.** The function `b_g` is completely monotone on `(0,∞)` if and only if every valuation-prefix coefficient

`A_v=∑_(j≤v)c_j p^(j/2)`, `v∈ℤ`, is nonnegative.             (3)

In particular complete monotonicity forces the negative-valuation tails

`Q_m=A_(-m)=∑_(j≥m)c_j p^(−j/2)≥0`, `m≥1`.                   (4)

For `F_m=(p^(m/2)−1)²`, `F₀=0`, the exact charge-gap identity is

`M₁/₂−M₀=∑_(m≥1)Q_m(F_m−F_(m−1))≥0`.                         (5)

Every factor `F_m−F_(m−1)` is strictly positive. Equality in (5) holds exactly when `c_j=0` for every `j≠0`. Thus a completely monotone flux and **both** original theta anchors `∫g=∫k`, `∫exp(x/2)g=∫exp(x/2)k` force `g=k` within the entire weighted-summable symmetric prime-power gauge class, even though the individual gauge coefficients may be signed. No positivity assumption on `g` is needed for this rigidity.

There is a uniform complex stability statement. Set `a=√p`, `Δ=M₁/₂−M₀≥0`, and

`C_p=(a²+1)/(a−1)²`,

`B_(p,σ)=2C_p[(a^(1−2σ)−1)^(−1)+(a−1)^(−1)]`, `0≤σ<1/2`.

Then, for every `m≥1`,

`|c_m|≤C_p Δ a^(−m)`,                                        (8)

and the holomorphic Mellin multiplier `M(w)=∑_j c_j p^(−jw)` satisfies

`sup_(|Re w|≤σ) |M(w)−M₀| ≤ B_(p,σ) Δ`.                      (9)

The supremum includes **all imaginary heights**. If `M₀=1` and `B_(p,σ)Δ<1`, this gauge creates no new zeros in `|Re w|≤σ`: `M(w)` is nonzero there, so the Mellin transform of `g` has the same zero divisor as that of `k` on this closed substrip. Also

`‖g−M₀k‖_(L¹(ℝ)) ≤ 4 C_p Δ ‖k‖_(L¹(ℝ))/(a−1)`.        (10)

## Proof

Translation of the flux gives

`H_(k(·+j log p))(x)=p^(−j/2)H_k(x+j log p)`,

so (1) yields

`b_g(t)=∑_j c_j p^(5j/2)b_k(p^(2j)t)`

`      =2π∑_j∑_(n≥1)c_j p^(5j/2)n² exp(−π(np^j)²t)`.       (6)

Absolute convergence follows from (2): `H_k≤1/2` gives `b_k(u)≤u^(−3/2)/2`, whence the absolute contribution of shift `j` in (6) is at most `|c_j|p^(−j/2)/(2t^(3/2))`. This also constructs a signed atomic measure with finite exponentially weighted total variation at every positive `t`.

Every positive rational rate in (6) is uniquely `r=p^v u` with `v∈ℤ`, `u≥1` an integer not divisible by `p`. The shift `j` contributes to rate `πr²` precisely when `j≤v`, in which case `n=rp^(−j)`. After collecting all such terms, that rate's atomic weight is

`2πr²∑_(j≤v)c_j p^(j/2)=2πr² A_v`.                       (7)

If all `A_v≥0`, (7) is a positive exponential measure and (6) is completely monotone. Conversely, fix `t₀>0` and apply the corpus's **finite** Bernstein--Widder theorem to `s↦b_g(t₀+s)`. This shifted profile has the finite right limit `b_g(t₀)`, so it is the Laplace transform of a finite positive measure. Formula (6) gives another representation by the finite signed measure obtained from (7) after weighting by `exp(−t₀λ)`. These measures agree: push forward under `λ↦exp(−λ)` to finite measures on `[0,1]`; equality of the transforms at positive integer `s`, together with their common limit at `s↓0`, gives equality of every polynomial moment. Density of polynomials in `C([0,1])` makes the measures equal. Undoing the strictly positive weight proves that every atom in (7) is nonnegative. Since each `v` occurs (take `u=1`), (3) follows.

Symmetry turns `A_(-m)` into (4). Also

`M₁/₂−M₀=∑_(j≥1)c_j[p^(j/2)+p^(−j/2)−2]`

`         =∑_(j≥1)c_j p^(−j/2)F_j`.

Write `F_j=∑_(m=1)^j(F_m−F_(m−1))` and interchange the absolutely convergent sums. This is (5). If its nonnegative sum vanishes, every `Q_m=0`; then `c_m p^(−m/2)=Q_m−Q_(m+1)=0` for all `m≥1`, and symmetry kills the negative shifts. The anchors make `M₀=M₁/₂=1` because the two corresponding moments of `k` are positive, so `c₀=1`.

For the quantitative claims, `F_m−F_(m−1)≥a^(2m−2)(a−1)²`: factor the difference of squares and use `a^(m−1)≥1`. Equation (5) therefore gives `Q_m≤Δ/[a^(2m−2)(a−1)²]`. Since `c_m a^(−m)=Q_m−Q_(m+1)`, the triangle inequality yields (8). Symmetry gives `M(w)−M₀=∑_(m≥1)c_m(p^(mw)+p^(−mw)−2)`. For `|Re w|≤σ`, each parenthesis has magnitude at most `2a^(2σm)+2`; insert (8) and sum the two geometric series to obtain (9). Finally write `g−M₀k=∑_(m≥1)c_m[k(·+m log p)+k(·−m log p)−2k]`; each bracket has `L¹` norm at most `4‖k‖₁`, and summing (8) gives (10). The full-strip transform factorization follows by absolute integration from (2).

The signed case is nonvacuous. For `0<ε<1`, take `c₀=1`, `c_(±2)=ε`, `c_(±1)=−ε/(2√p)`, and all other coefficients zero. Its negative-valuation prefixes are `A_(-2)=ε/p` and `A_(-1)=ε/(2p)`. The next prefixes are `A₀=1+ε/(2p)` and `A₁=1+ε/(2p)−ε/2`, both positive, and `A₂` adds `εp`. Thus its flux is completely monotone despite negative shift coefficients, while its charge gap is strictly positive. Positive rescaling can set its ordinary mass to that of `k` without changing these conclusions.

## What this changes and what it does not

The useful primitive is the **Bernstein measure of the completed flux**, rather than pointwise positivity of `g` or finitely many source moments. Euler atom rates collide along prime-power valuation chains. Their collisions turn complete monotonicity into the cumulative cone (3), and the two boundary anchors pair with that cone through the strictly positive Abel weights in (5). In this class, the scalar charge gap controls the **entire complex Mellin multiplier uniformly in imaginary height** by (9). This is an all-scale, source-specific obstruction to manufacturing off-line zeros by a symmetric signed prime-power translation multiplier while retaining these properties. It strictly extends the positive-convolution rigidity in [theta-prime-deletion-spectral-escape.md](theta-prime-deletion-spectral-escape.md): signed coefficients are allowed, and the gauge may have infinitely many shifts.

The theorem does **not** prove RH. It classifies one deformation class of the actual source; sources outside that class may share complete monotonicity and the two anchors. It supplies no zero-exclusion law for the unmodified `k`. The [full integer-scale divisor theorem](theta-divisor-bernstein-gauge-rigidity.md) extends exact rigidity beyond one prime, while the present prime-power version retains the stronger quantitative complex bound (9). The still-open source problem concerns the literal one-sided Euler chronology and its boundary-mass escape; neither symmetric gauge theorem orients that completion. Literature novelty has not been established.
