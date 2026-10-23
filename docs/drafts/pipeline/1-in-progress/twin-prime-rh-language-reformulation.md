# Twin primes in the RH research language

- **ID:** twin-prime-rh-language-reformulation
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** User request, 2026-10-23: read twelve programme READMEs and develop concrete reformulations using their objects and mechanisms.
- **Statement:** Identify exact arithmetic bridges and genuinely new candidate mechanisms for the lag-two prime correlation, without claiming RH and twin primes are equivalent.

## Goal

Reformulate the actual twin-prime problem through existing arithmetic sources, signed incidence, finite-horizon defects, compensation and critical energy. Distinguish definitions and already-proved bridges from the missing arithmetic estimate. No broad literature survey; no novelty claim without an audit.

## Reading coverage and division of labour

All twelve requested READMEs read completely. The roles below are conclusions of that reading, not claims that their open estimates are available.

| Programme | What transfers to twin primes | What does not transfer for free |
|---|---|---|
| Arithmetic Positivity Theory | Complete signed source; independent comparison norms; mixed-term accounting | Positivity subsidized by growing archimedean energy does not pay a microscopic prime-pair receiver. |
| Bi-Scale Uncertainty | Exact additive-lag Ramanujan multipliers; origin and phase diagnostics | Complete-period moments and twist-invariant extrema do not determine the needed finite-interval correlation. |
| Trans-Horizon Incidence Mechanics | Damped Möbius source, its lag spectrum, noncommuting limits, parity witnesses | A stationary limit is not uniform on a shrinking-damping physical diagonal. |
| Bézout–Valuation Incidence | Exact CRT defects; `gcd(d,e) ∣ 2`; cofactor geometry; singular series | Generic quadratic-window transfer and unsigned truncation bounds leave the critical regime unpaid. |
| Arithmetic Criticality Theory | Complete signed conductances and source-specific numerical ranges | Changing a gauge supplies no new arithmetic information; individual prime payments cannot be spent repeatedly. |
| Square-Root Threshold | Resolution calibration; retain the phase/resolution of the target | Gap `2` is the moving logarithmic separation `log(1+2/n)`, not the multiplicative lag `log 2`. |
| Arithmetic Incidence Positivity | Ratio/product bookkeeping; shared budgets; prime–polar compensation before squaring | Raw comb energy is dominated by a coherent main term and is not a bound for the desired signed pairing. |
| Arithmetic Continuation and Critical Energy | Exact damping derivative, dilation law, signed continuation | RH admission allows constants depending on damping; it does not give the diagonal uniformity used below. |
| Scale-Signed Incidence Criticality | Audit exactly which reading a proposed estimate uses | A faithful description is not a quantitative estimate. A counterexample for a reading is not logical independence of RH and twins. |
| Arithmetic Compensation Theory | Retain head–tail cross terms and moving-cutoff terms; measure an absolute remainder | Relative cancellation, even with a logarithmic rate, need not control the remainder in the target normalization. |
| Arithmetic Castelnuovo–Severi | Distinguish multiplicative Hecke incidence from additive correspondences | Relabeling a prime-pair count as an intersection supplies neither effectivity nor a nonvanishing theorem. |
| Signed Arithmetic Energy Incidence | Receiver as an orbit; signed rather than absolute payment; gauge/cycle audit | Compactness on `c₀`, backward operator stability, or a tensor-product norm estimate does not supply a fixed-lag lower bound. |

## Recommendation

Work with the **same damped divisor source already used for RH**, lifted to two damping parameters and restricted to the actual additive correspondence `m = n+2`. Its mixed zero-damping derivative is the prime-pair kernel. The existing singular-series theorem supplies the stationary main term. The missing arithmetic is a signed, origin-sensitive, finite-horizon discrepancy at damping tending to zero.

This is a concrete common research object. It does **not** establish `RH ↔ twin primes`, nor an implication in either direction. The strongest useful common description is: multiplicative incidence, observed along the actual additive integers, with the required cancellation surviving a critical limiting process. The two conjectures ask different questions of that source.

## 1. Exact common source

For `ε > 0`, set

\[
\tau_\varepsilon(n)=\sum_{d\mid n}\mu(d)d^{-\varepsilon}
 =\prod_{p\mid n}(1-p^{-\varepsilon}),\qquad
\rho_\varepsilon=1/\zeta(1+\varepsilon),
\]

and `A_ε(N) = Σ_{1≤n≤N} τ_ε(n) − ρ_ε N`. The product identity is for `n≥1`; the corpus sets `τ_ε(0)=0`. Set `A_ε(0)=0`.

The existing RH receiver is

\[
E_T(\varepsilon)=\sum_{n=1}^T\frac{A_\varepsilon(n)^2}{n(n+1)}.
\]

RH is admission `∃ B_ε ∀ T, E_T(ε) ≤ B_ε` at positive dampings arbitrarily close to zero. SAEI identifies `A_ε(n)/n` with the centered chain's orbit of the reciprocal observable. The damping constants may deteriorate arbitrarily near zero in this criterion.

Already proved in the corpus:

\[
\partial_\varepsilon\tau_\varepsilon(n)
 =-\sum_{d\mid n}\mu(d)d^{-\varepsilon}\log d,
\qquad \partial_\varepsilon\tau_\varepsilon(n)|_{0}=\Lambda(n).
\]

Consequently the two-parameter field

\[
K_{s,t}(m,n)=\tau_s(m)\tau_t(n)
\]

has mixed derivative `∂_s∂_t K_{0,0}(m,n)=Λ(m)Λ(n)`. After multiplying by `μ(m)² μ(n)²` it is exactly the logarithmically weighted prime-pair indicator. After dividing by `√m √n` it is the existing `TwinPrime.primePairKernel`.

**Exact infinitude formulation.** Define

\[
J_{N,M}(s,t)=\sum_{N<n\le M}
 \mu(n)^2\mu(n+2)^2\tau_s(n)\tau_t(n+2).
\]

Then

\[
\partial_s\partial_tJ_{N,M}(0,0)
 =\sum_{\substack{N<p\le M\\p,\ p+2\;\mathrm{prime}}}
       \log p\log(p+2).
\]

Thus twin-prime infinitude is exactly
`∀ N, ∃ M, ∂_s∂_t J_{N,M}(0,0) > 0`.
No density or Hardy–Littlewood asymptotic is required by this equivalence.

The two separate damping variables also avoid an origin mistake: `τ_s(1)=1`. A diagonal quotient `τ_ε(n)τ_ε(n+2)/ε²` must exclude `n=1`; the mixed derivative is valid there and equals zero.

There is also an exact valuation interpretation. For `n≥2`, the first nonzero term of `τ_s(n)` is `s^{ω(n)} ∏_{p∣n} log p`, where `ω` counts distinct prime factors. Thus the pair source starts in bidegree `(ω(n),ω(n+2))`. After the squarefree projection, bidegree `(1,1)` means precisely two primes. This suggests tracking contamination from higher factor-count levels during a cofactor decomposition; estimate (1) makes the first such separation quantitative. Positivity at a fixed positive damping proves nothing about this coefficient: the unprojected source is positive on every positive integer, composites included.

**Verdict: BRIDGE.** Finite differentiation and the prime filter prove this on paper from checked corpus inputs. This precise new packaging has not been compiled as a Lean leaf in this task. It is not a new analytic estimate.

## 2. A quantitative physical diagonal

Here is a finite estimate derived in this synthesis. Its proof is included so that the diagonal is justified rather than guessed.

For `n≥2` and `ε>0`,

\[
0\le\frac{\tau_\varepsilon(n)}{\varepsilon}\le\log n,
\qquad
\left|\frac{\tau_\varepsilon(n)}{\varepsilon}-\Lambda(n)\right|
 \le\frac{\varepsilon}{2}(\log n)^2. \tag{1}
\]

**Proof.** Every Euler factor lies in `[0,1]` and `1-e^{-u}≤u` for `u≥0`. Keeping one prime divisor proves the first upper bound. If `n=p^a`, then `τ_ε(n)=1-e^{-ε log p}` and `Λ(n)=log p`. The identity
`u−(1−e^{-u})=∫₀ᵘ(1−e^{-v})dv` bounds the error between `0` and `u²/2`, proving (1). Otherwise `n` has two distinct prime divisors `p,q` and `Λ(n)=0`. Keeping these two factors gives
`τ_ε(n)≤ε² log p log q≤ε²(log n)²/4`, since `pq∣n` and `4ab≤(a+b)²`. This is stronger than (1) and exhausts `n≥2`.

Let `X≥2` be an integer, `L=log(X+2)`, and

\[
Q_\varepsilon(X)=\frac1{X\varepsilon^2}
                 \sum_{n=2}^X\tau_\varepsilon(n)\tau_\varepsilon(n+2).
\]

For `a=τ_ε(n)/ε`, `b=τ_ε(n+2)/ε`, use
`ab−Λ(n)Λ(n+2)=(a−Λ(n))b+Λ(n)(b−Λ(n+2))`.
All four unsigned factors are at most `L`; (1) therefore proves

\[
\left|Q_\varepsilon(X)-\frac1X\sum_{n=2}^X\Lambda(n)\Lambda(n+2)\right|
 \le\varepsilon L^3. \tag{2}
\]

The same estimate holds after multiplying each summand by `μ(n)² μ(n+2)²`, since that multiplier is either zero or one. In that version the comparison sum contains only genuine twin primes.

For the unprojected source, the corpus's proper-prime-power count gives
`# {m≤K : m is a proper prime power} ≤ 2√K log K/log 2`.
In either coordinate each exceptional `m≤X+2` determines at most one `n`; each pair has weight at most `L²`. Hence, writing

\[
P(X)=\frac1X\sum_{\substack{p\le X\\p,\ p+2\;\mathrm{prime}}}
                     \log p\log(p+2),
\]

we obtain the explicit bound

\[
|Q_\varepsilon(X)-P(X)|
 \le\varepsilon L^3+
       \frac{4\sqrt{X+2}\,L^3}{X\log2}. \tag{3}
\]

In particular, the deterministic choice

\[
\boxed{\varepsilon_X=(\log(X+2))^{-4}}
\]

gives `Q_{ε_X}(X)−P(X)→0`, unconditionally on paper. More generally any positive schedule with `ε_X log³(X+2)→0` works. The exponent four is a convenient choice, not asserted optimal.

This is stronger than saying pointwise derivatives exist: it fixes an actual simultaneous horizon/damping regime and controls the approximation error there. It does not bound `P(X)` from below.

**Status: quantitative bridge now Lean-certified; no novelty claim.**
[DampedPairDiagonal](../3-formalized/twin-prime-damped-pair-diagonal.md)
certifies (1), finite pair errors with the harmless padded logarithm
`log(X+h+2)`, and the resulting zero-error limit, both unprojected
against von Mangoldt and squarefree-projected against actual primes.
At gap two its explicit schedule is `log⁻⁴(X+4)`. The unprojected
prime-power removal in (3) remains a paper deduction. The corpus search
found the Euler product, one-factor bound, tangent identity, and
exponential quadratic bound before formalization. No novelty follows
from a search not locating this exact estimate.

## 3. The main term exists; the physical transfer is open

Write the corpus's complete-period limiting covariance as `C_ε(h)` to avoid confusing it with the prefix `A_ε` above. Existing Lean theorems give

\[
M_\varepsilon(h)=\rho_\varepsilon^2+C_\varepsilon(h)
 =\rho_\varepsilon^2\mathfrak S_\varepsilon(h),
\qquad
\mathfrak S_\varepsilon(h)
 =\prod_p\left(1+\frac{c_p(h)}{(p^{1+\varepsilon}-1)^2}\right).
\]

They also give `𝔖_ε(h)→𝔖(h)` as `ε↓0`, and positivity at every positive even gap. At gap two,

\[
\mathfrak S(2)=2\prod_{p>2}\left(1-\frac1{(p-1)^2}\right)>0.
\]

Since `ρ_ε/ε→1`, define the concrete discrepancy

\[
\mathcal D(X)=Q_{\varepsilon_X}(X)
             -\left(\frac{\rho_{\varepsilon_X}}{\varepsilon_X}\right)^2
                    \mathfrak S_{\varepsilon_X}(2).
\]

Combining the existing stationary limit with (3) gives the paper identity in asymptotic form

\[
\boxed{\mathcal D(X)=P(X)-\mathfrak S(2)+o(1).} \tag{4}
\]

Two precise targets now have different strength:

- **Strong target:** `𝒟(X)→0`. By (4), this is equivalent to the weighted Hardy–Littlewood asymptotic at gap two. It is an exact reformulation of a harder endpoint, not an independent estimate already supplied by RH.
- **Sufficient weaker target:** some `δ>0` and an unbounded sequence `X_j` satisfy `𝒟(X_j)≥−𝔖(2)+δ`. Then `P(X_j)≥δ/2` eventually, giving infinitely many twins and a positive weighted density along that sequence. This remains stronger than infinitude alone. The exact infinitude formulation is the finite-tail mixed derivative in §1.

**[OPEN CORE]** Prove a lower bound for this actual finite-interval discrepancy that leaves positive mass. No theorem checked here provides it.

**Why the existing limit cannot be substituted.** `tendsto_periodCovariance_cofactor_div_density_sq` is already joint in damping and the Ramanujan cutoff, but still averages over a complete period. Its second parameter is not the physical interval length. Confusing those two limits would silently insert the prime-pair estimate. Even fixed-damping physical convergence, by itself, would not give the needed diagonal uniformity.

The elementary family `1−exp(−ε log X)` illustrates only this quantifier issue: its fixed-positive-ε limit is one, while it tends to zero on `ε=log⁻⁴X`. It is not presented as an arithmetic counterexample.

## 4. Where to seek the missing estimate

### First choice: compensate the actual CRT defect with its cofactor tail

For integer `Q≥1`, let `H_{ε,Q}(n)=Σ_{1≤d≤Q,d∣n} μ(d)d^{-ε}` and `T_{ε,Q}=τ_ε−H_{ε,Q}`. Let `F_ε(X)=ε²Q_ε(X)`, `F_{ε,Q}(X)` be the corresponding head product average on `[2,X]`, and `M_{ε,Q}(2)` its complete-period product mean. Then the exact identity is

\[
F_\varepsilon(X)-M_\varepsilon(2)
 =[F_\varepsilon-F_{\varepsilon,Q}]
  +[F_{\varepsilon,Q}-M_{\varepsilon,Q}]
  +[M_{\varepsilon,Q}-M_\varepsilon]. \tag{5}
\]

The first bracket retains `HT+TH+TT`; it is not a sum of two separate positive tail energies. The last bracket is fixed by the same source. ACCC's compensation language applies to the signed sum of these terms.

The middle bracket has an exact Bézout expansion. For
`N_X(d,e)=#{2≤n≤X : d∣n, e∣n+2}`,

\[
F_{\varepsilon,Q}-\frac{X-1}{X}M_{\varepsilon,Q}
 =\frac1X\sum_{1\le d,e\le Q}\mu(d)\mu(e)(de)^{-\varepsilon}
   \left[N_X(d,e)-(X-1)\frac{[\gcd(d,e)\mid2]}{\operatorname{lcm}(d,e)}\right]. \tag{6}
\]

Every compatible count is one residue class; each bracket has magnitude at most one. The tiny distinction between `M_{ε,Q}` and `(X−1)M_{ε,Q}/X` is an explicit origin normalization term and must stay in (5).

For odd `d,e`, compatibility is coprimality. The local factor at two must be retained separately, rather than applying coprimality indiscriminately. Reindexing actual incidences gives the determinant surface `eℓ−dm=2`.

**Why this targets a real gap.** Absolute summation costs roughly `Q²/X` before normalization by `ε²`. At the same time the usual infinite unsigned divisor-tail majorant involves `Σ_{d>Q}d^{-1−ε}`, of scale `Q^{-ε}/ε`. On the derivative regime `ε log X→0` with `Q≤X`, this cannot be made small by damping. A complete divisor head needs cutoff near `X`, whereas the generic period-transfer estimate becomes useful only far below that. This diagnoses these particular unsigned bounds, not an impossibility theorem for other methods.

**Candidate mechanism:** use overlapping prime/cofactor decompositions to cancel the signed CRT defect against the source's own tail before taking an absolute value. The first serious test is the balanced range `d,e≈√X`, with actual Möbius signs, actual CRT phases and all transfer terms attached. A saving there would be meaningful partial progress; identities alone score zero.

**Update: the balanced head is paid on paper.** The
[balanced CRT deduction](../2-fully-proven/twin-prime-balanced-crt-compensation.md)
uses the checked classical inverse-phase theorem and pays every
smoothing strip and discarded Fourier mode. It gives
`O(Y^(2-1/400))` for `Y^2<=X<=4Y^2`, uniformly even for arbitrary
bounded complex product weights. This is a classical deduction, not
a newly discovered source-specific cancellation theorem. Its analytic
input is not yet Lean-certified here.

The [full-height boundary](../3-formalized/twin-prime-full-height-crt-boundary.md)
is different: for `X/2+2<=d,e<=X`, the exact incidence kernel is
`[e=d+2]`. An explicit odd block with positive constant weights has
normalized discrepancy at least `1/20`. Thus a uniform estimate for
all product weights cannot be extended to this endpoint. Actual
Möbius compensation must be retained across the full decomposition.

There is also an exact finite normalization improvement. Set
`b_epsilon(d)=mu(d)(1-d^(-epsilon))/epsilon`. Cancelling the complete
zero-damping divisor sums gives `tau_epsilon(n)/epsilon=-sum_(d|n)b_epsilon(d)`
for `n>=2`, and `|b_epsilon(d)|<=log d`. The
[axis-compensation card](../3-formalized/twin-prime-compensated-damping-coefficients.md)
records the proof. In these coordinates the balanced paper estimate
costs `log^2(2Y)` uniformly in damping. Its changed head, tails, and
stationary terms must be kept together; no conditional infinite-series
interchange is implied by the finite identity.

A second compensation puts the logarithm on the complementary divisor:

`tau_epsilon(n)/epsilon
 = sum_(dm=n) mu(d)d^(-epsilon)(1-m^(-epsilon))/epsilon`, `n>=2`.

The coefficient has absolute value at most `log m` for positive damping,
and vanishes exactly at `m=1`. Thus the full-height unit-cofactor faces
disappear in this representation. The former isolated boundary block
does not have to be estimated separately: its compensation is part of
the complete source. This is the finite-difference version of the
existing Möbius--logarithm dilation in ACCE, not a new cancellation
theorem. Growing **nonunit** cofactors remain the analytic obligation;
fixed-form cancellation cannot supply uniformity in that range.
Both compensations, coefficient bounds, and the full-height boundary
are now Lean-certified. The next exact target is the
[complete nonunit-cofactor covariance](twin-prime-nonunit-cofactor-dispersion.md),
with the mixed terms retained as separate unproved obligations.

**More precise first test.** For odd coprime `d,e`, choose `dbar` with
`d*dbar=1 (mod e)` and let `r=d*(-2*dbar mod e)`. Then `r` is the
compatible residue modulo `de`. With `e(z)=exp(2 pi i z)`, finite
character orthogonality gives, for `X>=2`, exactly

`N_X(d,e)-(X-1)/(de)
 =(1/(de)) sum_(1<=k<de) e(2k*dbar/e) sum_(2<=n<=X) e(kn/(de))`.

The sign follows from `r/(de)=-2*dbar/e (mod 1)`. This is a complete
finite identity, with the physical interval still in the inner sum.
It identifies the frequency object to estimate: bilinear sums of
inverse-residue phases across the varying modulus `e`, weighted by
`mu(d)mu(e)` and the coupled physical-interval factor. A fixed-modulus
Kloosterman norm bound does not itself estimate this sum over moduli.
The corpus search returned fixed-modulus bilinear bounds and factored
modulus Gram bounds; it did not locate a ready theorem matching this
varying-modulus, coupled-weight expression. No bound is inferred from
that search result, and no external theorem is inserted as a premise.

Taking absolute values of the Fourier coefficients also does not
complete the test. In the balanced range `de` comparable to `X`, their
size is at most a constant times `min(1,1/min(k,de-k))`; summing this
envelope only gives a logarithm per pair. Truncation therefore needs
a proved endpoint-error estimate as well as control of the retained
inverse-residue phases. The balanced paper proof now pays these steps
in the stated square-root range. Outside that range, the Fourier
length and cofactor-tail compensation still require estimates at
their actual scales.

**Attack:** (5) is independent of `Q` by telescoping. Rewriting it at `Q` and `2Q` does not itself give a contraction. A contraction or an absolute remainder bound must come from a separately proved arithmetic estimate. The known relative large-prime/complement cancellation is not that estimate.

### Scale check against the existing prime-horizon crossover

The checked `DampedPrimeHorizonCrossoverScale.lean` identifies the slope
`lambda_epsilon(p)=p^(-epsilon)-2 H_epsilon(p-1)` and the logarithmic
crossover `L_c(epsilon)=-log(2 rho_epsilon)/epsilon`. Its unconditional
limit is `epsilon L_c(epsilon)=log(1/(2 epsilon))+o(1)`.

On the prime-resolving schedule `epsilon=log^(-4)(X+4)`, write
`L=log(X+4)`. Substitution gives

`L_c(epsilon)=L^4 (4 log L-log 2+o(1))`,

so `log X/L_c(epsilon) -> 0`. The crossover theorem therefore places
every sufficiently large prime `p<=X` on its positive-slope side,
uniformly over these primes. This conclusion concerns the literal
slope; the sign of a finite prefix-energy step also has the theorem's
explicit floor/remainder term, which cannot be discarded.

Thus a fixed-damping argument using negative prime slopes beyond the
crossover does not already control the prime-resolving diagonal.
The required compensation must work in the pre-crossover regime.
This scale comparison is a paper deduction from the checked crossover
theorem, not an additional estimate for the lag-two discrepancy.

### Second choice: a two-parameter damping flow on Bézout correspondences

ACCE already proves the exact one-point evolution

\[
\partial_s\tau_s(n)=\sum_{d\mid n}\Lambda(d)d^{-s}\tau_s(n/d).
\]

For `B_{s,t}(X;h)=Σ_{n=2}^X τ_s(n)τ_t(n+h)`, finite differentiation therefore gives

\[
\partial_s B_{s,t}(X;h)
 =\sum_{d=1}^X\Lambda(d)d^{-s}
     \sum_{\substack{m\ge1\\2\le dm\le X}}
                  \tau_s(m)\tau_t(dm+h), \tag{7}
\]

and

\[
\partial_s\partial_t B_{s,t}(X;h)
 =\sum_{d=1}^X\sum_{e=1}^{X+h}\Lambda(d)\Lambda(e)d^{-s}e^{-t}
    \sum_{\substack{m,\ell\ge1\\2\le dm\le X\\e\ell-dm=h}}
                       \tau_s(m)\tau_t(\ell). \tag{8}
\]

All sums are finite; their displayed bounds follow from positive cofactors. These identities have dependency-closed paper proofs by the checked convolution law, the product rule, and reindexing divisors. They have not been compiled here.

This explains why the determinant operator is natural: it is generated by differentiating the RH source along an additive pair. It also specifies the correct state space. The flow at fixed lag does **not** close on fixed-lag scalar correlations: it generates affine/cofactor correspondences. Using a compressed Ramanujan lag multiplier as if it were the true additive shift would lose those terms.

**Candidate mechanism:** a signed continuation law for the compensated family of these correspondences, with a lower bound on the selected gap-two observable. Use the literal source vectors and the known Euler main term; do not ask for a uniform inverse bound for the entire damping chain.

**[OPEN CORE]** A quantitative source-specific signed bound for the generated mixed terms. Differentiating and naming this family does not provide that bound. In particular, backward continuation of the ambient chain is known to be unstable.

### Third choice: the microscopic mixed differences of the RH Gram

Write `u_ε(n)=A_ε(n)−A_ε(n−1)=τ_ε(n)−ρ_ε`. Exactly,

\[
\sum_{n=2}^X\tau_\varepsilon(n)\tau_\varepsilon(n+2)
 =\sum_{n=2}^X u_\varepsilon(n)u_\varepsilon(n+2)
  +\rho_\varepsilon[A_\varepsilon(X)+A_\varepsilon(X+2)
                     -A_\varepsilon(1)-A_\varepsilon(3)]
  +(X-1)\rho_\varepsilon^2. \tag{9}
\]

The centered pair is the mixed discrete difference of the two-horizon Gram
`G_ε(m,n)=A_ε(m)A_ε(n)`, restricted to `n=m+2`. This gives a direct receiver-language formulation: RH controls a weighted diagonal energy of `A`; prime pairs ask for a very particular mixed difference of its Gram at the boundary `ε=0`.

On `ε_X=log⁻⁴(X+2)`, (1), `ρ_ε/ε→1`, and the existing prime number theorem imply
`A_{ε_X}(X+O(1))/(X ε_X)→0`: sum (1), divide by `Xε`, and use `Σ_{n≤X}Λ(n)/X→1` and `Xε_X→∞`. Thus the boundary term in (9), divided by `Xε_X²`, tends to zero. The main term is one. The strong prime-pair target is therefore the microscopic centered covariance limit

\[
\frac1{X\varepsilon_X^2}\sum_{n=2}^X
       u_{\varepsilon_X}(n)u_{\varepsilon_X}(n+2)
 \longrightarrow\mathfrak S(2)-1. \tag{10}
\]

**Candidate mechanism:** a regularity/compensation estimate that preserves this mixed difference under the actual source flow. This is a useful diagnostic formulation, but less direct than (6) for attacking arithmetic cancellation.

**Attack:** RH admission is an upper bound in a smoothed prefix norm, at each fixed damping. It gives neither this microscopic lower bound nor the required uniformity in damping. The existing `RHPairKernelBridge` even proves that deleting the fixed twin slice leaves its RH growth criterion equivalent. That fact limits that particular criterion; it does not prove RH cannot imply twins by another argument.

### Geometric alternative: additive correspondence on the scaling surface

ACS's Hecke incidence changes prime valuations multiplicatively. For odd `n>1`, `n` and `n+2` are coprime, so their multiplicative ratio is not a prime-power divisibility edge. Their additive relation must enter as an additional correspondence. At scale `n`, it sits at logarithmic separation `log(1+2/n)`.

The meaningful geometric question would be an independently defined effective incidence or section count for this additive correspondence whose prime-filtered boundary has nonzero mass. Positivity/Hodge index on the existing scaling surface, or a new name for the same count, supplies no such count.

**Priority: lower.** This may guide the right objects, but currently has less quantitative machinery attached than the damped source and CRT defect. No section or effectivity theorem is claimed.

## 5. Selectivity and failure tests

1. **Keep the additive origin and interval.** Every proposed transfer must state the actual interval, cutoff and damping. Period averages or magnitude-only spectra are different readings.
2. **Keep the source signs.** A bound that remains valid after arbitrary replacement of the Möbius row by its coefficient envelope must be checked against the existing positive-twin and parity witnesses. Their receiver failures are not automatically failures for the new prime-pair target; identify the exact reading before importing a no-go.
3. **Keep local compatibility.** The lag-two CRT condition is `gcd(d,e)∣2`; an odd-gap calibration must recover the vanishing factor at two. A proposed positive universal fixed-gap lower bound fails that calibration.
4. **Keep the diagonal uniformity.** Constants depending on fixed positive damping cannot silently be evaluated on `ε_X` without a bound on their dependence.
5. **Keep mixed terms and coherent main terms.** ACCC/AIP's raw-comb obstruction forbids treating a large unsigned square as the desired signed charge. Head and tail in (5) share coefficients and need joint accounting.
6. **Keep the observable after a gauge change.** SAEI's cycle laws and the determinant-parity bridge warn that operator norms can preserve the shifted Liouville correlation in different coordinates. Gauge invariance is not cancellation. A lower-bound argument must still identify the actual pair mass.
7. **Keep conclusions distinct.** Exact finite-tail positivity is equivalent to infinitude. A positive cofinal normalized mass is stronger. Convergence to the singular series is stronger still. None is supplied by the existence of the stationary Euler product.

## 6. Checked Lean entry points

Searches used `scripts/formal_tools.py research` before source inspection. No mathlib search or web search was needed for this internal synthesis.

| Checked source | Exact input used |
|---|---|
| [PMPowerDampedMobiusDivisorHaar](../../../../formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusDivisorHaar.lean) | `pmPowerDampedDivisorCoeff`, `pmPowerDampedDivisorCoeff_eq_prod`, positivity and the mean-density definition |
| [DampedChebyshevTangentFormOfTheReceiver](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/DampedChebyshevTangentFormOfTheReceiver.lean) | `hasDerivAt_pmPowerDampedDivisorCoeff`, `dampedVonMangoldt_zero`, zero-damping source normalization |
| [HardyLittlewoodSingularSeriesOfTheDampedSource](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/HardyLittlewoodSingularSeriesOfTheDampedSource.lean) | normalized period-covariance limit, joint cofactor-cutoff limit, Euler product and positivity for even gaps |
| [ExactDampedSingularSeriesAndGallagherPrefixDiscrepancy](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/ExactDampedSingularSeriesAndGallagherPrefixDiscrepancy.lean) | exact `lagProductMean_div_density_sq_eq`, damped Euler product and its limit |
| [DampedAutocorrelationAndClockInvisibility](../../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/DampedAutocorrelationAndClockInvisibility.lean) | actual definition of `dampedAutocorrelation`; period and cofactor quantifiers |
| [PolynomialWindowTranslatedMomentTransfer](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/PolynomialWindowTranslatedMomentTransfer.lean) | joint-incidence count error at most one; exact finite product expansion |
| [TheTangentIsADilationAverageOfTheSource](../../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheTangentIsADilationAverageOfTheSource.lean) | `dampedVonMangoldt_eq_dilation_convolution`; exact centered-prefix correction |
| [ProperPrimePowerCount](../../../../formal/GaloisForLFunctions/RHTower/Sieve/ProperPrimePowerCount.lean) | explicit `2√K log K/log 2` proper-prime-power count |
| [RHPairKernelBridge](../../../../formal/GaloisForLFunctions/twin-prime/RHPairKernelBridge.lean) | squarefree prime filter, exact tail-positivity equivalence, existing common-kernel RH criterion |
| [DampedPairDiagonal](../../../../formal/GaloisForLFunctions/twin-prime/DampedPairDiagonal.lean) | explicit uniform error, concrete damping schedule, and both zero-error pair limits |
| [DampedPrimeHorizonCrossoverScale](../../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/DampedPrimeHorizonCrossoverScale.lean) | prime-slope crossover and its small-damping asymptotic; checked for the scale comparison above |
| [TheReceiverIsTheChainOrbitOfTheReciprocal](../../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/TheReceiverIsTheChainOrbitOfTheReciprocal.lean) | `admits_iff_summable_orbit`, `riemannHypothesis_iff_orbit_summable`; exact cofinal damping quantifier |

Suggested new leaves, only after selecting the next implementation task:

- `DampedPairTangentBridge`: mixed derivative equals the existing prime-pair kernel; finite-tail equivalence. All parameters explicit, no analytic premise.
- `DampedPairDiagonal` is now certified for the finite errors and explicit schedule; unprojected prime-power removal remains separate.
- `DampedPairBezoutFlow`: (7)–(8), with exact finite boundaries.
- `DampedPairFiniteHorizonDefect`: (5)–(6) and (9), retaining every correction.

Do not add an assumption asserting the missing discrepancy bound to a Lean theorem and call the resulting implication progress. Keep that estimate open on this card until proved unconditionally.

## 7. Audit and decision

- **Internal context:** all twelve programmes read; selected dependencies checked in Lean source.
- **External novelty audit:** not performed in this task, following the request for work grounded in the local research rather than further web searching. No assertion of novelty relative to the literature.
- **Conjecture/attack:** the exact strong discrepancy target is a Hardy–Littlewood reformulation; verdict **BRIDGE**, not a new theorem. The weaker cofinal lower bound remains open. The balanced block now has a classical paper estimate, but no bound for the complete source-specific compensation has been proved.
- **Paper work:** finite mixed-derivative bridge, quantitative diagonal estimate, exact defect ledger and two-parameter Bézout flow derived above. No conjecture used in those derivations.
- **Formal status:** `DampedPairDiagonal` now certifies the quantitative physical bridge, with five premise-free capstones. The complex `DeterminantParityBridge` has four audited capstones, including exact four-cycle invariance. Both leaf checks passed; all nine capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`. The mixed-derivative, exact flow, and full discrepancy ledger remain paper work. No unproved analytic input is assumed in either leaf.
- **Anti-theatre assessment:** the endpoint frontier has not moved. What improved is the specification of a common source and of the exact finite-horizon, small-damping obligation. The elementary diagonal estimate is bridge work, not a claimed breakthrough.
- **Latest formal batch:** the two finite compensations and their coefficient bounds passed ten capstone axiom audits; the exact full-height shift classification and quantitative boundary passed five. Both leaf checks passed. Every audited capstone has no analytic premise and uses only standard foundational axioms. The uniform full-height route is closed with its positive survivor, while the compensated nonunit source remains open. This is bridge and boundary work, not new number-theoretic knowledge.
- **Damping removed on cofactor rectangles:** five further unconditional
  capstones now certify the error `6/(1+log(X+2))` on every selected
  subset when `ZW<=X`, using the clock `epsilon=(1+log(X+2))^-6`.
  The same clock preserves the projected prime-pair average with
  error `8/(1+log(X+2))^3`. The actual CRT endpoint error is paid.
  See [certificate](../3-formalized/twin-prime-cofactor-damping-removal.md).
  The short-cofactor target therefore concerns the undamped row
  `U_Z(n)=sum_(dm=n,2<=m<=Z) mu(d) log m`.
- **New analytic deduction, paper only:** retaining a coupled
  congruence inside its Fourier expansion gives a rough-shift
  centering bound uniform in a common modulus, arbitrary residue
  assignments and complex shift weights. Square-divisor truncation
  gives the Möbius version against an arbitrary bounded second row.
  See [proof](../2-fully-proven/twin-prime-coupled-residue-centering.md).
  Its normalization is the whole interval. The required
  fixed-determinant estimate must instead resolve the number of
  actual affine samples; that relative estimate remains open.
- **Further use of the RH machinery:** the existing quantitative
  twisted Möbius prefix theorem now gives an unconditional Lean bound
  for the reciprocal-Ramaré cofactor, uniformly in growing
  designated prime sets below a stretched-logarithmic cutoff.
  The proof keeps signed prefixes intact and pays large smooth
  divisors with an independent positive moment. See
  [formalized deduction](../3-formalized/twin-prime-ramare-weighted-cofactor-cancellation.md).
  This is precisely the separation of signed arithmetic payment
  from positive tail payment emphasized by the compensation
  programmes. Six capstones passed their leaf and transitive axiom
  checks. Additive-window assembly remains outstanding; this is
  not a fixed-gap positivity theorem.
- **Next research decision:** attack the source-specific signed CRT/cofactor compensation in §4 first. Use the two-parameter flow to identify the closed family of arithmetic terms. Judge progress by a genuine bound in the normalization `Xε²`, not by the number of equivalent formulations or formalized identities.

## Gates

- [x] Read all twelve READMEs completely.
- [x] Check the actual Lean statements selected for the bridge, corpus search first.
- [x] State concrete candidate laws, their failure tests and first unproved step.
- [x] Compare alternatives and prepare a prioritized mathematical synthesis.
- [ ] Prove the source-specific discrepancy bound; this is research beyond the completed ideation task.

## Log

- 2026-10-23 — Completed requested internal synthesis. Derived a quantitative physical diagonal and exact two-parameter Bézout flow on paper. The prime-pair discrepancy estimate, RH and twin-prime conjecture remain unproved here.
- 2026-10-23 — Certified the physical diagonal and complex parity bridge.
  Checked the source's prime-horizon crossover on the explicit schedule;
  it lies before the dissipative regime. Expanded the balanced CRT defect
  into the exact inverse-residue Fourier expression and identified the
  unresolved varying-modulus and endpoint estimates. No cancellation
  bound, lower prime-pair mass, or infinitude theorem obtained.
- 2026-10-23 — Paid the balanced CRT block on paper using the
  checked classical input and complete endpoint estimates. Certified
  exact axis/cofactor compensation and the full-height boundary in
  Lean. The unit-cofactor faces vanish in the compensated source;
  growing nonunit cofactors and mixed terms remain unestimated.
- 2026-10-23 — Certified uniform damping removal on the cofactor
  rectangles and audited the exact fixed-determinant family.
  The coupled-residue paper calculation pays rough-shift centering,
  including Möbius, but gives no fixed-shift lower prime-pair mass.
