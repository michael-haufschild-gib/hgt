# The Möbius--Fourier commutator has the exact Meyer--Poisson kernel

- **ID:** deninger-mobius-fourier-commutator-poisson-kernel
- **Stage:** 2-fully-proven
- **Type:** SOURCE-DEFINED OFF-DIAGONAL RANGE DETECTOR / CAUSAL-CURRENT NO-GO /
  ROUTE-L FRONTIER ADVANCE
- **Scientific status:** [PAPER-PROVED] [CORPUS-NEW SYNTHESIS]
  [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]
- **Labels:**
  - DAC_DENINGER_MOBIUS_PREDOMAIN_ALL_MOMENTS;
  - DAC_DENINGER_MOBIUS_FOURIER_COMMUTATOR_EXACT_KERNEL;
  - DAC_DENINGER_MOBIUS_FOURIER_COMMUTATOR_REAL_COVARIANCE;
  - DAC_DENINGER_CAUSAL_VON_MANGOLDT_ENDPOINT_ANOMALY_WALL.
- **Parent:** DAC_DENINGER_CORRECTED_TATE_FLOQUET_POISSON_DESCENT
- **Inputs:**
  - Meyer's strict Poisson embedding;
  - canonical pointwise Möbius right inverse;
  - unconditional PNT-strength estimate
    \(M(X)=O(Xe^{-c(\log X)^{1/3}})\), already formalized in the corpus;
  - ordinary Fourier inversion and Poisson summation on Schwartz functions;
  - Burnol's co-Poisson/Fourier intertwining as literature context.
- **Lean status:** section 5 formalized unconditionally; see *Lean status* below.

## 1. Result

Put

\[
 H_- = \mathscr S_{\exp}(\mathbb R),\qquad
 H_\cap=\{f\in\mathscr S(\mathbb R):f\text{ even},\ f(0)=\widehat f(0)=0\}.
\tag{1}
\]

For \(h\in H_-\), write \(H_h(x)=h(\log x)\) on \(x>0\), and define its canonical Möbius
preimage

\[
 f_h(x)=\sum_{n\ge1}\mu(n)H_h(nx),\qquad x>0.
\tag{2}
\]

The earlier pointwise theorem proves \(Zf_h=H_h\) on the positive ray, but does not control
\(f_h\) at the radial origin. The first theorem below supplies unconditional
integrability needed for a genuine two-collar comparison: \(f_h\) is integrable and has every
nonnegative polynomial moment, although it need not extend smoothly through zero. Its half-line
mass is always zero.

Let \(E f_h\) be the even \(L^1\)-extension of \(f_h\), and put

\[
 (Jh)(t)=e^{-t}h(-t).
\tag{3}
\]

The following operator is therefore defined on every Meyer cochain, without choosing a zeta
zero, divisor, quotient, maximal regularity domain, or Hilbert completion:

\[
 \boxed{\quad
 \mathfrak S_\mu h
   =\mathcal F(Ef_h)-E f_{Jh}\in\mathscr S'(\mathbb R).
 \quad}
\tag{4}
\]

It is continuous in the nuclear Meyer topology and has the exact kernel

\[
 \boxed{\quad
 \ker\mathfrak S_\mu=Z(H_\cap).
 \quad}
\tag{5}
\]

Moreover

\[
 \mathfrak S_\mu(Jh)=-\mathcal F(\mathfrak S_\mu h).
\tag{6}
\]

Thus (4) is a source-defined, off-diagonal, real-Fourier-covariant realization of the
set-theoretic singular target requested by corrected Tate--Floquet descent. This closes the
analytic kernel and Fourier seam parts of that interface. It does not yet identify (4)
with the boundary image of the strict Euler--Gamma source differential, prove the unsquared
Green--Stokes square, or construct the positive weight-one quotient form.

There is also a sharp no-go. The causal von Mangoldt current has one distributional endpoint
anomaly on a general Schwartz preimage, and the two Fourier collars read exactly
\((\widehat f(0),f(0))\). But after canonical Möbius inversion that anomaly vanishes for every
\(h\in H_-\), not only for Poisson boundaries. Hence a leading radial residue, a single
\(\delta_0\)-counterterm, or the causal connection alone cannot replace the off-diagonal
commutator (4).

## 2. Unconditional \(L^1\) and moment domain of the Möbius preimage

Let

\[
 M(T)=\sum_{n\le T}\mu(n).
\tag{7}
\]

The corpus proves an unconditional estimate of the form

\[
 |M(T)|\le C T\exp\bigl(-c(\log T)^{1/3}\bigr)
 \qquad(T\ge T_0).
\tag{8}
\]

Only the consequence

\[
 \int_1^\infty {|M(T)|\over T^2}\,dT<\infty
\tag{9}
\]

is needed. In particular the theorem uses PNT-strength cancellation, not the RH-equivalent
bound \(M(T)=O(T^{1/2+\varepsilon})\).

Abel summation in (2) gives, for \(x>0\),

\[
 f_h(x)=-x\int_1^\infty M(T)H_h'(xT)\,dT.
\tag{10}
\]

The endpoint term at infinity vanishes by rapid multiplicative decay, and the lower endpoint is
taken at \(1^-\), where the summatory function is zero.

[PROVED HERE] [DAC_DENINGER_MOBIUS_PREDOMAIN_ALL_MOMENTS]

For every integer \(r\ge0\),

\[
 \boxed{\quad
 \int_0^\infty x^r|f_h(x)|\,dx
 \le
 \left(\int_1^\infty {|M(T)|\over T^{r+2}}\,dT\right)
 \left(\int_0^\infty y^{r+1}|H_h'(y)|\,dy\right)<\infty.
 \quad}
\tag{11}
\]

Also

\[
 \boxed{\quad \int_0^\infty f_h(x)\,dx=0.\quad}
\tag{12}
\]

The assignments

\[
 h\longmapsto x^r f_h(x)\in L^1(0,\infty)
\tag{13}
\]

are continuous for every \(r\ge0\).

### Proof

Tonelli applied to (10) gives

\[
\begin{aligned}
 \int_0^\infty x^r|f_h(x)|\,dx
 &\le\int_1^\infty |M(T)|
       \int_0^\infty x^{r+1}|H_h'(xT)|\,dx\,dT\\
 &=\left(\int_1^\infty {|M(T)|\over T^{r+2}}\,dT\right)
   \left(\int_0^\infty y^{r+1}|H_h'(y)|\,dy\right).
\end{aligned}
\]

The first factor is finite by (9) for \(r=0\), and a fortiori for \(r>0\). The second is finite
because \(H_h\) and all its derivatives decay faster than every power at both endpoints. This
proves (11). The displayed right-hand side is a continuous Meyer seminorm up to a fixed
constant, proving (13).

For \(\sigma>1\), partial summation gives

\[
 {1\over\zeta(\sigma)}
 =\sum_{n\ge1}{\mu(n)\over n^\sigma}
 =\sigma\int_1^\infty {M(T)\over T^{\sigma+1}}\,dT.
\tag{14}
\]

Estimate (9) permits dominated convergence as \(\sigma\downarrow1\), while
\(1/\zeta(\sigma)\to0\). Hence

\[
 \int_1^\infty {M(T)\over T^2}\,dT=0.
\tag{15}
\]

Fubini in (10) is now justified by (11), and integration by parts in \(y\) yields

\[
\begin{aligned}
 \int_0^\infty f_h(x)\,dx
 &=-\int_1^\infty M(T)
     \left(\int_0^\infty xH_h'(xT)\,dx\right)dT\\
 &=\left(\int_1^\infty {M(T)\over T^2}\,dT\right)
   \left(\int_0^\infty H_h(y)\,dy\right)=0.
\end{aligned}
\]

This proves (12).

Finally, \(f_h\) is smooth on \(x>0\), and every derivative is rapidly decreasing at infinity.
Indeed, for \(x\ge1\), termwise differentiation and any \(A>r+1\) give

\[
 |f_h^{(r)}(x)|
 \le C_Ax^{-A}\sum_{n\ge1}n^{r-A}.
\tag{16}
\]

No regularity at \(x=0\) is asserted.

## 3. Exact kernel of the Möbius--Fourier commutator

Use Fourier normalization

\[
 \widehat f(\xi)=\int_{\mathbb R}f(x)e^{-2\pi i x\xi}\,dx.
\tag{17}
\]

By (11), both \(Ef_h\) and \(Ef_{Jh}\) belong to \(L^1(\mathbb R)\) and have all polynomial
moments. Formula (4) consequently defines a continuous map

\[
 \mathfrak S_\mu:H_-\longrightarrow\mathscr S'(\mathbb R).
\tag{18}
\]

[PROVED HERE] [DAC_DENINGER_MOBIUS_FOURIER_COMMUTATOR_EXACT_KERNEL]

One has exact equality (5).

### Boundary inclusion

If \(h=Zf\) for \(f\in H_\cap\), existing left Möbius inversion gives

\[
 Ef_h=f.
\tag{19}
\]

Meyer--Poisson reflection gives \(Jh=Z\widehat f\), so the same inversion gives

\[
 Ef_{Jh}=\widehat f.
\tag{20}
\]

Equations (19)--(20) imply \(\mathfrak S_\mu h=0\). Thus
\(Z(H_\cap)\subseteq\ker\mathfrak S_\mu\).

### Converse: zero equation forces Schwartz regularity

Suppose \(\mathfrak S_\mu h=0\). Put

\[
 f=Ef_h,\qquad g=Ef_{Jh}.
\tag{21}
\]

Then \(f,g\in L^1(\mathbb R)\), both are even, both have every nonnegative polynomial moment, and

\[
 \widehat f=g
\tag{22}
\]

as tempered distributions. Since \(g\in L^1\), Fourier inversion gives a continuous
representative of \(f\). Since \(\xi^r g(\xi)\in L^1\) for every \(r\), differentiation under the
inverse Fourier integral gives

\[
 f^{(r)}(x)=\int_{\mathbb R}(2\pi i\xi)^r g(\xi)e^{2\pi i x\xi}\,d\xi
\tag{23}
\]

for every \(r\ge0\). Hence \(f\) extends smoothly through the origin.

On the positive ray this smooth representative agrees with the pointwise Möbius preimage. Rapid
estimates (16) therefore show that every derivative of \(f\) decays faster than every power at
\(+\infty\), and evenness gives the same at \(-\infty\). Thus

\[
 f\in\mathscr S(\mathbb R).
\tag{24}
\]

Equation (22) then gives \(g=\widehat f\in\mathscr S(\mathbb R)\).

The pointwise right-inverse theorem gives

\[
 h(\log x)=\sum_{n\ge1}f(nx),\qquad x>0.
\tag{25}
\]

Poisson summation for the even Schwartz pair \((f,g)\) rewrites (25) as

\[
 h(\log x)
 ={g(0)\over2x}-{f(0)\over2}
  +{1\over x}\sum_{m\ge1}g(m/x).
\tag{26}
\]

For every \(N\), last term is \(O(x^N)\) as \(x\downarrow0\). Since \(h\in H_-\), left-hand
side is also \(O(x^N)\) for every \(N\). Multiplying (26) by \(x\) and taking the limit gives
\(g(0)=0\); returning to (26) then gives \(f(0)=0\). Since

\[
 g(0)=\widehat f(0),
\tag{27}
\]

we have \(f\in H_\cap\). Equation (25) says \(h=Zf\), proving converse inclusion and (5).

Load-bearing step is (23)--(24): opposite Möbius collar supplies missing Fourier moments,
which repairs singular radial preimage. Endpoint conditions then follow from rapid source
synthesis; they are not assumed.

## 4. Real-Fourier covariance and Euler depletion

[PROVED HERE] [DAC_DENINGER_MOBIUS_FOURIER_COMMUTATOR_REAL_COVARIANCE]

Since \(J^2=1\) and every preimage is even,

\[
\begin{aligned}
 \mathfrak S_\mu(Jh)
 &=\mathcal F(Ef_{Jh})-Ef_h,\\
 \mathcal F(\mathfrak S_\mu h)
 &=\mathcal F^2(Ef_h)-\mathcal F(Ef_{Jh})
 =Ef_h-\mathcal F(Ef_{Jh}).
\end{aligned}
\]

This proves (6). Thus collar exchange acts on target by \(-\mathcal F\), and kernel is
real-Fourier invariant before any norm square.

For a base prime \(p\), let

\[
 \Delta_p=1-\tau_{\log p}
\tag{28}
\]

and let \(G_p:\Delta_pH_-\to H_-\) be already-constructed continuous Green inverse on closed
zero-periodization sector. Define

\[
 \mathfrak S_{\mu,p}=\mathfrak S_\mu\circ G_p.
\tag{29}
\]

Strict one-prime conservativity theorem and (5) give

\[
 \boxed{\quad
 \ker\mathfrak S_{\mu,p}=\Delta_pZ(H_\cap).
 \quad}
\tag{30}
\]

Thus exact singular detector transports to admitted Euler-depleted coefficient without replacing
literal boundary by a closure.

## 5. Causal von Mangoldt anomaly and its exact wall

For a function \(f\) on positive ray, define truncated causal dilation current

\[
 A_Nf(x)=\sum_{2\le n\le N}\Lambda(n)f(nx),\qquad x>0,
\tag{31}
\]

and

\[
 L_N=\sum_{2\le n\le N}{\Lambda(n)\over n}.
\tag{32}
\]

View \(A_Nf\) as a distribution on \(\mathbb R\) by extension by zero from positive ray.

[PROVED HERE] [DAC_DENINGER_CAUSAL_VON_MANGOLDT_ENDPOINT_ANOMALY_WALL]

If

\[
 f\in L^1(0,\infty),\qquad xf(x)\in L^1(0,\infty),
\tag{33}
\]

then

\[
 A_Nf-L_N\left(\int_0^\infty f(y)\,dy\right)\delta_0
\tag{34}
\]

converges in \(\mathscr D'(\mathbb R)\). Since \(L_N\to\infty\), unrenormalized sequence
\(A_Nf\) converges if and only if

\[
 \int_0^\infty f(y)\,dy=0.
\tag{35}
\]

### Proof

For \(\phi\in C_c^\infty(\mathbb R)\), change variables \(y=nx\):

\[
 \langle A_Nf,\phi\rangle
 =\sum_{2\le n\le N}{\Lambda(n)\over n}
   \int_0^\infty f(y)\phi(y/n)\,dy.
\tag{36}
\]

Subtract value at origin. Remainder is

\[
 \sum_{2\le n\le N}{\Lambda(n)\over n}
 \int_0^\infty f(y)\bigl(\phi(y/n)-\phi(0)\bigr)\,dy.
\tag{37}
\]

Mean-value theorem bounds \(n\)-th absolute value by

\[
 {\Lambda(n)\over n^2}\|\phi'\|_\infty
 \int_0^\infty y|f(y)|\,dy.
\tag{38}
\]

Since \(\sum\Lambda(n)n^{-2}<\infty\), (37) converges absolutely. This proves (34). Classical
asymptotic \(L_N=\log N+O(1)\) and a test function with \(\phi(0)=1\) prove converse in (35).

For even \(f\in\mathscr S(\mathbb R)\),

\[
 \int_0^\infty f={\widehat f(0)\over2},\qquad
 \int_0^\infty\widehat f={f(0)\over2}.
\tag{39}
\]

Therefore pair

\[
 \bigl(A_Nf,A_N\widehat f\bigr)
\tag{40}
\]

converges without counterterms exactly when \(f\in H_\cap\). On regular preimage sector, two
causal anomalies really do read two Poisson endpoint coordinates.

But (12) applies to every canonical preimage \(f_h\) and also to \(f_{Jh}\). Hence

\[
 A_Nf_h\quad\text{and}\quad A_Nf_{Jh}
\tag{41}
\]

converge distributionally for every \(h\in H_-\). Endpoint anomaly is therefore blind on full
source domain. Its apparent exactness on Schwartz preimages cannot be globalized into a
Poisson-range detector.

This is precise failure of leading-residue conjecture: Möbius cancellation kills only divergent
causal counterterm before singular regularity at radial origin is resolved.

## 6. Source connection is still present

Failure in Section 5 is not loss of von Mangoldt current. Introduce tilted Möbius preimage

\[
 f_{h,\alpha}(x)=\sum_{n\ge1}\mu(n)n^{-\alpha}H_h(nx).
\tag{42}
\]

Pointwise differentiation at \(\alpha=0\) gives

\[
 D_\mu h(x)
 :=\left.\partial_\alpha f_{h,\alpha}(x)\right|_{\alpha=0}
 =-\sum_{n\ge1}\mu(n)\log n\,H_h(nx).
\tag{43}
\]

Absolute rearrangement on every fixed positive ray and

\[
 (-\mu\log)*\mathbf1=\Lambda
\tag{44}
\]

give exact connection identity

\[
 \boxed{\quad
 D_\mu h(x)=\sum_{m\ge2}\Lambda(m)f_h(mx).
 \quad}
\tag{45}
\]

In a safe Mellin half-plane,

\[
 \mathcal M(D_\mu h)(s)
 =\left({1\over\zeta}\right)'(s)\mathcal M(H_h)(s)
 =-{\zeta'(s)\over\zeta(s)^2}\mathcal M(H_h)(s).
\tag{46}
\]

Multiplier in (46) is analytic at \(s=1\). This is Mellin explanation of (41): Möbius derivative
retains full Euler connection but cancels its leading pole. Remaining defect is failure of two
canonical preimages to be Fourier partners, exactly (4).

## 7. Conjecture loop disposition

1. **Critical Floquet scalarization destroys causal source orientation.**
   Failed. Polarization recovers symmetric von Mangoldt distribution, whose support gap
   \((-\log2,\log2)\) canonically determines its positive causal half.
2. **Recovered causal current itself cuts literal Poisson range.**
   Failed. Its injective two-collar differential has full reflected graph as kernel, already-known
   overlarge radical.
3. **Leading causal endpoint residue cuts canonical Möbius regularity domain.**
   Failed sharply by (12) and (41). Residue vanishes on every Meyer cochain.
4. **Compare two canonical Möbius preimages before scalarization.**
   Survives and is proved by (5). Fourier equality supplies missing regularity rather than
   assuming it.
5. **Formula (4) alone closes Route L.**
   False. It closes singular target and exact kernel, but not identification with actual
   Gamma/co-Poisson Green boundary, unsquared source chain homotopy, or positivity after descent.

## 8. Exact Route-L consequence

Corrected Tate--Floquet card no longer needs an unspecified singular-germ operator. Canonical
choice is (4), and it already satisfies:

- global source definition on all \(H_-\);
- nuclear-source continuity into tempered distributions;
- exact kernel \(Z(H_\cap)\);
- exact real-Fourier covariance;
- strict Euler-depleted transport through existing Green inverse.

The source-to-boundary identification part is now closed on paper by
`DAC_DENINGER_EULER_GAMMA_MOBIUS_CONNECTION_TRANSGRESSION`: the all-prime-first Möbius family has
a strict PNT endpoint, its forced physical/Fourier connection difference satisfies an unsquared
covariant Green--Stokes law, and its endpoint Gamma/co-Poisson boundary is exactly `(4)`.

First open source producer is correspondingly narrower still:

**`DAC_DENINGER_RESOLVED_GREEN_SOURCE_ANNIHILATOR`**

> Identify the degree-two rational-Witt/Milnor Gamma realization and prove
> \(\Omega_{\mu,\Gamma}=\mathfrak S_\mu\mathcal G_\Gamma D=0\). Canonical Möbius inversion then
> supplies the degree-one chain prelift into
> \(\ker\mathfrak S_\mu=Z(H_\cap)\). Its boundary value must agree coefficient-faithfully with
> already-resolved singular Gamma/Calderón Green transport.

Its fixed prime-2/prime-3 consequence is RH-equivalent endpoint test
`XI_TWO_PRIME_ORIENTED_BOUNDARY_STRICT_TRANSPORT`. Only after source annihilator and comparison
are constructed may one polarize and prove closability with radical precisely
\(Z(H_\cap)\), raw arithmetic weight one, and no raw-Floquet bounded extension. Missing knowledge
is no longer existence or set-theoretic specification of singular detector, nor construction of
an arbitrary degree-one lift. Exact lift obstruction and canonical prelift are proved in
`deninger-source-poisson-chain-lift-obstruction.md`; missing content is source-derived vanishing of
that obstruction and its non-diagonal polarization.

## 9. Hostile audit

- **Unconditional.** Only arithmetic estimate is (8), an unconditional zero-free-region/PNT
  consequence already proved in corpus. No half-power Mertens estimate, zero location, Weil
  positivity, or RH-equivalent premise occurs.
- **No divisor-built target.** Operator (4) uses only ordinary-integer Möbius inversion, radial
  reflection, and Fourier transform.
- **No quotient relabeling.** Target is fixed space \(\mathscr S'(\mathbb R)\), and kernel equality
  is proved by Fourier regularity bootstrap.
- **No endpoint assumption.** Both endpoint vanishings are consequences of (22) and rapid source
  synthesis through (26).
- **No scalar theatre.** Leading scalar/distributional anomaly is proved universally blind in
  (41); survivor compares opposite collars before squaring.
- **No false resolved-Green claim.** The source transgression identifies (4) with the
  Gamma/co-Poisson boundary image, but does not put the independently resolved Xi Green boundary
  in its kernel and does not assert positivity. That incidence is the new open core.
- **Literature boundary.** Burnol proves general multiplicative-convolution/Fourier intertwining,
  Property \(S\), and Mellin characterizations. Those are not claimed as new. Corpus-wide search
  did not locate exact global Meyer-domain theorem (11)--(18) together with kernel bootstrap
  (21)--(27) or causal blindness law (41). External novelty remains unverified.
- **No Lean activity.** Lean sources were inspected read-only. No Lean file, build, or process was
  run or changed.

## References

- Jean-François Burnol, *Entrelacement de co-Poisson*, Ann. Inst. Fourier 57 (2007),
  arXiv:math/0407443.
- Semyon Yakubovich, *New summation and transformation formulas of the Poisson, Müntz, Möbius and
  Voronoi type*, arXiv:1410.7934.
- ../../not_new_scientific_knowledge/deninger-mobius-right-inverse-poisson-range-classification.md.
- ../../../3-formalized/moebius-exponent-upgrade.md.
- deninger-critical-floquet-von-mangoldt-renormalization-wall.md.

## Lean status

### Section 5 — the causal von Mangoldt endpoint anomaly `(34)`--`(35)` `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerCausalVonMangoldtWall.lean`.  Axiom audit for all
declarations: `propext, Classical.choice, Quot.sound`.  No distribution theory is needed: testing
the current against `φ` turns `(34)` into a numerical series, which is the statement proved.

- `deningerCausalTerm`, `deningerCausalRenorm` — the tested current `(Λ(n)/n) ∫ f(y) φ(y/n) dy`
  and its renormalization, subtracting `φ(0)`.
- `deningerCausalRenorm_norm_le` — **`(38)`**: the renormalized term is at most
  `C · (∫_0^∞ y|f|) · Λ(n)/n²`, from the mean-value bound alone.
- `deningerVonMangoldt_summable_div_sq` — `∑ Λ(n)/n² < ∞`, from `Λ ≤ log` and the corpus's
  `Sieve.summable_log_div_sq`.
- `deningerCausalRenorm_summable` — **`(34)`**: the renormalized current always converges.
- `deningerCausalTerm_eq` — **`(36)`--`(37)`**: the two currents differ by exactly
  `(Λ(n)/n) · (∫_0^∞ f) · φ(0)`.
- `deningerCausalL_tendsto_atTop`, `deningerVonMangoldt_not_summable` — `L_N → ∞`, from the
  corpus's `Sieve.mertensFirst_lower` and `Λ(p) = log p`.
- `deningerCausal_summable_iff` — **`(35)`**: the unrenormalized current converges if and only if
  `(∫_0^∞ f) · φ(0) = 0`.  Combined with `(12)` this is the blindness law `(41)`.

The hypothesis on `φ` is the mean-value bound `‖φ(x) - φ(0)‖ ≤ C|x|` together with continuity,
which is what `(38)` uses; every `C_c^∞` test function satisfies it.

### The source and the canonical preimage `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerExpSchwartz.lean` and
`formal/GaloisForLFunctions/RHTower/DeningerMobiusPreimage.lean`.  Axiom audit for all
declarations: `propext, Classical.choice, Quot.sound`.

- `DeningerExpSchwartz` — `H_- = S_exp(ℝ)` of `(1)`, realized as a subspace of `𝓢(ℝ, ℂ)` cut out by
  `∀ A n, ∃ C, ∀ x, e^{A|x|} ‖D^n f(x)‖ ≤ C`.  `deningerShift`, `deningerShift_mem` and
  `deningerPeriodizationDefect L = 1 - τ_L` of `(28)` come with it.
- `deningerLogPull` — `H_h(x) = h(log x)` of `(2)`; `deningerLogPull_norm_le` turns the
  exponential weight into `min(x^A, x^{-A})`, and `deningerLogPull_norm_le_inv_sq` is the `A = 2`
  case.
- `deningerMobiusRay_summable`, `deningerMobiusPreimage` — **`(2)` converges absolutely on every
  positive ray**, by the single comparison `‖H_h(nx)‖ ≤ (C/x²)/n²`.  No cancellation in `μ` is
  used; the two-sided decay of the pullback does it alone.

### What is left

`(11)`--`(12)` (Abel summation, Tonelli, and `∫_1^∞ |M(T)|/T² dT < ∞` from the corpus's
unconditional Mertens rate), `(44)`--`(45)` (mathlib has `log * μ = Λ`; only a Fubini on a fixed
ray is left), `(6)` (formal once `𝔖_μ` is defined), and `(5)` itself — the Fourier-inversion
bootstrap `(23)`--`(24)` followed by Poisson summation `(26)`.  `(25)` and `(45)` share one missing tool — the absolutely convergent product-fibre interchange
`∑'_{(m,k)} F(m,k) = ∑'_N ∑_{d|N} F(d, N/d)` — which is the next thing to build.  `H_∩` and `Z`
already exist as `RHTower.DeningerMeyerCap` and `RHTower.deningerPoissonLM`.

## Gates

- [x] 0 → 1 in-progress: source operator, domain, falsifiers, and literature boundary fixed
- [x] 1 → 2 fully-proven: estimates (10)--(16), exact kernel (5), covariance (6), and causal wall
  (34)--(41) proved
- [x] source Green identification: strict Euler--Gamma/Möbius transgression, unsquared covariant
  identity, and boundary image `(4)` proved on paper
- [ ] source annihilator gate: `DAC_DENINGER_RESOLVED_GREEN_SOURCE_ANNIHILATOR`
- [ ] endpoint falsifier: `XI_TWO_PRIME_ORIENTED_BOUNDARY_STRICT_TRANSPORT`
- [ ] 2 → 3 formalized: section 5 done; `(5)`, `(6)`, `(11)`, `(12)`, `(45)` remain
- [ ] 3 → 4 publication-ready

## Log

- 2026-08-08 — Proved unconditional all-moment \(L^1\) control and zero mass for every canonical
  Möbius preimage. Constructed global Möbius--Fourier commutator and proved its exact
  Meyer--Poisson kernel and Fourier covariance. Proved leading causal von Mangoldt anomaly is
  universally blind after Möbius inversion. Narrowed Route L from construction of an unspecified
  singular detector to one explicit source-to-Gamma Green chain-map identification.
- 2026-08-08 — All-prime-first adiabatic Möbius transgression identified this operator as the
  exact Gamma/co-Poisson endpoint of the forced physical/Fourier Euler-connection difference.
  Remaining gate is arithmetic incidence of the fixed resolved two-prime Green boundary in its
  literal kernel, not construction of the operator or source connection.
