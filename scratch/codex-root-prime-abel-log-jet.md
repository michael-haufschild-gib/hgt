# Prime Abel head: finite-cutoff logarithmic-jet obstruction (paper proof)

Status: paper argument only; no new Lean theorem or external priority claim. This concerns the literal CCM-FU source, not an RH proof.

Let `C(x) = criticalContinuousAbel x` and

`H(X) = Σ_{p≤X} √p C(X/p)`.

The corpus proves that the Mellin transform

`F(δ) = ∫₁^∞ C(y)y^(-5/2-δ)dy`, for `δ>0`, has a zero of some finite order `r≥1` at `δ=0` from the right: `F(δ)/δ^r → c≠0` (`criticalAbelMellin_normalizedJet`). The corpus also supplies a power-log PNT error for `ψ` and a square-root-log error for `π` (`ChebyshevPsiPowerLogPNT`, `Sieve/PrimeCountingBigO`).

**Claim.** With `μ_j = ∫₁^∞ C(y)y^(-5/2)(log y)^j dy`, all moments converge absolutely, `μ_j=0` for `j<r`, `μ_r=(-1)^r r!c≠0`, and

`H(X) = μ_r X^(3/2)/(log X)^(r+1) + o(X^(3/2)/(log X)^(r+1))`.

Consequently, after processing exactly the primes below a square-root threshold `B_X` with `B_X≈√X` and `X<B_X²`, the *literal terminal selection energy* satisfies

`E_X(P_{B_X}) ≥ (μ_r²+o(1)) X³/(log X)^(2r+2)`, hence `E_X(P_{B_X})/X²→∞`.

Proof details to audit/formalize:

1. The continuous square-root primitive is `C(x)=½∫₁ˣ t^(-1/2)(ψ(⌊t⌋)-⌊t⌋+2γ)dt`, hence it is locally absolutely continuous and `C'(x)=½x^(-1/2)ψDefect(⌊x⌋)` almost everywhere. The power-log PNT, with the bounded floor correction, gives for every fixed `A>0`: `C(x)=O_A(x^(3/2)/(log x)^A)` and `C'(x)=O_A(x^(1/2)/(log x)^A)` for large `x`. Thus all `μ_j` converge. Differentiation under the integral from the right at `δ=0` identifies `F^(j)(0+)=(-1)^j μ_j`; compare with the corpus's finite analytic jet.
2. `π(t)=Li(t)+O_A(t/(log t)^A)` for any fixed `A`, by its stronger square-root-log corpus bound. Partial summation applied to `f_X(t)=√t C(X/t)` gives, for every fixed `N`,
   `H(X)=∫₂ˣ √t C(X/t)dt/log t + O_N(X^(3/2)/(log X)^N)`.
   For the error, use `|f_X'(t)| ≲ X^(3/2)t^(-2)` times arbitrarily strong inverse powers of `log(X/t)` when `X/t` is large; split the Stieltjes error integral at `t=√X`. On the lower piece source decay pays the arbitrary log power, on the upper piece prime-count error does. Boundary terms obey the same estimate and `C(1)=0`.
3. Substitute `y=X/t`. The main integral is
   `X^(3/2)∫₁^(X/2) C(y)y^(-5/2)/(log X-log y)dy`.
   The range `y>√X` is `O_N(X^(3/2)/(log X)^N)` for every fixed `N` by source decay. On `y≤√X`, expand the denominator geometrically to order `r`, with remainder bounded by `2(log y)^(r+1)/(log X)^(r+2)`. Extend each moment to infinity using the same source decay. Vanishing of `μ_0,…,μ_(r-1)` leaves the displayed leading term.
4. The square-root terminal transform in `MobiusDivisorTerminalCriticalSourceTransform` makes the terminal head `C(X)+Σ_{p≥B_X}√p C(X/p)`. Both `C(X)` and the removed `p<B_X` sum are `O_N(X^(3/2)/(log X)^N)` for every `N`: for the latter, `X/p≥√X` and `Σ_{p<B_X}1/p≤Σ_{n≤B_X}1/n=O(log X)`. Energy contains the square of this head as a nonnegative summand.

**Meaning for route.** Zero first Mellin mass makes a homogeneous omitted-prime cloud look neutral at leading continuum order. Prime density's factor `1/log p` exposes the first nonzero Mellin jet one logarithmic order later, causing superquadratic finite-cutoff energy. This is a source-specific no-go for the uncorrected square-root terminal checkpoint, not a no-go for adaptive masks or a source-selected full history. A prospective producer must cancel the finite-jet anomaly with prime-scale-dependent selection *and* pay old-cutoff covariance; replacing `1/log p` formally by the von-Mangoldt measure cancels this asymptotic Jacobian but does not itself give a 0/1 prime schedule or RH.

**Positive source survivor: logarithmic clock compensation (paper proof).** Let

`H_log(X)=Σ_{p≤X}(log p)√p C(X/p)`.

Then for every fixed `A>0`, `H_log(X)=O_A(X^(3/2)/(log X)^A)`. Indeed, replace the Stieltjes measure `dθ(t)=Σ_p(log p)δ_p` by `dt` using the corpus's square-root-log PNT remainder for `θ`; the same split and derivative bounds as above make its weighted error `O_A(X^(3/2)/log^A X)`. The continuous main term is

`∫₂ˣ √t C(X/t)dt = X^(3/2)∫₁^(X/2) C(y)y^(-5/2)dy`.

Its full integral is exactly `μ₀=0`, and its omitted tail is smaller than every fixed inverse log power by the source PNT bound. Thus multiplying prime atoms by their clock length `log p` removes *all* polynomial-logarithmic Jacobian terms, not merely the first one. This is a signed source cancellation, not positivity or an RH-scale `O(X)` bound. The weight is not a legal binary processed-prime selector; any use in CCM-FU must construct a coefficient-faithful 0/1 realization and control its covariance at every old cutoff.

**Failed jump test: logarithmic clock as prime survival (paper algebra, not Lean-closed).** At an integer wall `M`, set `q_p(M)=log p/log M` for `√M<p<M`, and `q_p(M)=0` for `p≤√M`. For each prime `p`, one uniform mark `U_p∈[0,1]` defines a nested terminal history by leaving `p` unprocessed exactly when `p≤M<p²` and `U_p≤q_p(M)`. The probabilities decrease from one at birth to zero at `p²`, so each realization is nested and eventually exhaustive, and every wall has processed its square-root core. With `a_p=√p C(M/p)` (using the exact clipped child at integer walls) and completed source `S_M`, independent marks give the *exact finite identity*

`E[E_M] = (S_M+Σ_{p>√M}q_p a_p)² + Σ_{p>√M}q_p(2-q_p)a_p²`.

The first term has the clock-compensated mean (modulo the superlog-small lower-prime tail); the second term is at least `(3/4)Σ_{p>√M}p C(M/p)²`, since `q_p≥1/2`. Thus this stochastic reinterpretation does **not** pay the corpus's child-source second-moment gate, even before old-cutoff covariance is considered. It changes the primitive from a mask at one wall to a causal survival process, but its risky RH-scale prediction fails to follow from known source estimates. Do not present it as an RH producer or a conceptual jump; a viable coupling must be source-adaptive and control the entire history, not merely match the prime-clock mean.
