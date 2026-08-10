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

### The product-fibre interchange, `(25)` and `(44)` `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerMobiusRightInverse.lean`.  Axiom audit for all
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerProductFibre_tsum` — **the interchange**: an absolutely summable family on `ℕ × ℕ`
  vanishing on the zero product is summed by grouping along the fibres of `(m,k) ↦ mk`, each of
  which is the divisor antidiagonal.  This is the only interchange the ray calculus needs, and it
  is what `(25)` and `(45)` both reduce to.
- `deningerMobiusDivisorSumInt`, `deningerMobiusDivisorSumReal`, `deningerMobiusDivisorSum` —
  `∑_{d|N} μ(N/d) = [N = 1]` over `ℤ`, `ℝ` and `ℂ`.
- `deningerRaySum`, `deningerMobius_rightInverse` — **`(25)`, the pointwise right inverse**:
  `∑_{n ≥ 1} f_h(nx) = H_h(x)` for every `x > 0`.
- `deningerMobiusLogDivisorSum` — **`(44)`**: `∑_{d|n} μ(d) log d = -Λ(n)`, by writing
  `log d = log n - log(n/d)`; the unit detector is killed by `log n` and what is left is the
  corpus's Möbius--log convolution.

### Section 6 — the Möbius connection `(44)`--`(45)` `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerMobiusConnection.lean`.  Axiom audit for all
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerNegMobiusLog`, `deningerNegMobiusLog_mul_zeta` — `(44)` in convolution form,
  `(-μ · log) * ζ = Λ`.  The sign is carried *inside* the pointwise product on purpose: the
  `Neg` instance of `ArithmeticFunction` is not the ring's `HasDistribNeg` one, so `neg_mul` does
  not fire on a convolution, and every identity here is kept sign-free.
- `deningerVonMangoldt_mul_moebius` — **`Λ * μ = -μ · log`**, by convolving `(44)` with `μ` and
  using `ζ * μ = 1`.
- `deningerVonMangoldtMoebiusDivisorSum` — its divisor form
  `∑_{d|N} Λ(d) μ(N/d) = -μ(N) log N`.
- `deningerMobiusDerivative`, `deningerMobius_connection` — **`(45)`**, the connection identity on
  the ray: `∑_m Λ(m) f_h(mx) = -∑_n μ(n) log n · H_h(nx)` for every `x > 0`.  The pair family
  vanishes on `mk = 0` for free here, since `Λ(0) = 0` and `μ(0) = 0`.

### Section 2 — the unconditional saving `(8)` `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerMertensSummatory.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

The summatory function `M` itself is **corpus-owned** — `RHTower.Sieve.mertensM` in
`Sieve/MoebiusMaximalWindow.lean`, together with `mertensSup` and the PNT form
`tendsto_abs_mertensM_div`.  Do not redefine it.

- `deningerMertensSaving` — the saving factor `exp(-(log N)^{1/3}/108)`.
- `deningerMertensM_rate` — **`(8)`**: the corpus's sharp `κ = 2` contour estimate
  (`Sieve.exists_norm_sum_moebius_kappa_two_rate`, stated at real arguments with `⌊N⌋₊`)
  transported to `Sieve.mertensM` at integer arguments.
- `deningerMertensM_div_sq_le` — the same divided by `N²`, which is the shape the Abel summation
  of `(10)` consumes.

### Section 2 — the convergence `(9)`, in discrete form `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerMertensInvSquare.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

- `deningerCubeRootExp_le`, `deningerCubeRootExp_summable` — `∑_k exp(-c k^{1/3}) < ∞`, from a
  *single term* of the exponential series: `exp(c x^{1/3}) ≥ (c x^{1/3})^7/7!` and `x^{7/3} ≥ x²`
  for `x ≥ 1`.  No asymptotic machinery.
- `deningerSavingRay_antitone`, `deningerSavingRay_summable` —
  `∑_N exp(-(log N)^{1/3}/108)/N < ∞`, by Cauchy condensation
  (`summable_condensed_iff_of_nonneg`); the condensed term is exactly `exp(-c k^{1/3})` with
  `c = (log 2)^{1/3}/108`.
- `deningerMertensM_invSq_summable` — **`(9)` in discrete form: `∑_N |M(N)|/N² < ∞`.**

Condensation is not a convenience here.  No power comparison can prove `(9)`:
`exp(-c(log N)^{1/3})` dominates every `N^{-ε}`, so the series looks borderline divergent under
any polynomial test and only the dyadic grouping separates it.

### Section 2 — Abel summation `(10)` `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerMobiusAbel.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

- `deningerMertensM_abs_le` — `|M(n)| ≤ n + 1`.
- `deningerAbelBoundary_tendsto_zero` — the boundary term `H_h(nx) M(n)` vanishes: the pullback
  decays like an inverse square while `M` grows at most linearly.
- `deningerMobius_abel` — **`(10)` in discrete form**: the partial sums of
  `∑_n M(n) (H_h((n+1)x) - H_h(nx))` converge to `-f_h(x)`, for every `x > 0`.  This is
  `Finset.sum_range_by_parts` plus the vanishing boundary term.

### Section 2 — the weighted derivative of the pullback `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerLogPullDeriv.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

- `deningerLogPullDeriv`, `deningerLogPull_hasDerivAt` — `H_h'(x) = h'(log x)/x` on the ray.
- `deningerExpSchwartz_deriv_norm_le` — the `n = 1` case of the source condition, read as a bound
  on `deriv h` itself.
- `deningerLogPullDeriv_weighted_norm_le` — **the weighted derivative `x H_h'(x)` obeys the same
  two-sided bound `min(x², x^{-2})` as the pullback**, because the chain-rule factor `1/x` cancels
  the weight *exactly*: `x H_h'(x) = h'(log x)`.  This is why `∫_0^∞ u |H_h'(u)| du` is finite with
  no loss of exponent.

### Section 2 — the Abel coefficient `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerAbelCoefficient.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

- `deningerAbelWindow_volume` — the dilation window `{x : ix ≤ u ≤ (i+1)x}` is `Icc (u/(i+1)) (u/i)`.
- `deningerAbelWindow_length` — its length is `u/(i(i+1))`.
- `deningerAbelCoefficient_summable` — **`∑_i |M(i)|/(i(i+1)) < ∞`**, by comparison with `(9)`.

`(11)` is proved at `r = 0`, and at order `r ≥ 1` all three ingredients are proved — the window
moment, the coefficient summability, and the weighted moment — so the order-`r` statement is the
same assembly as the `r = 0` one with `x^r` inserted, following
`DeningerAbelMajorant`/`DeningerPreimageMass` line for line.  Then `(12)` needs `(15)`, whose discrete form is `∑_n μ(n)/n = 0`.  Convergence of that series is
now proved; what is left is only that its **value is zero**, and that does *not* follow from
`M(N) = o(N)`: partial summation the other way turns `A(N) → S` into `M(N)/N → S - S = 0` for any
`S`, so PNT alone cannot pin the constant.  The value needs the analytic input — Abel's theorem
for the Dirichlet series `∑ μ(n) n^{-s} = 1/ζ(s)` on `s ↓ 1` together with the pole of `ζ` at `1`,
which forces `1/ζ(s) → 0`.  The corpus has `LSeries_moebius_eq_inv_riemannZeta` for `Re s > 1`;
the Abelian theorem is the missing piece.

### Section 2 — the first weighted moment `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerWeightedMoment.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

- `deningerWeightedMoment_continuousOn` — the integrand `u ‖H_h'(u)‖` is continuous on the ray.
- `deningerWeightedMoment_integrable` — **`∫_0^∞ u |H_h'(u)| du < ∞`**, the second factor of the
  `(11)` bound: bounded on `Ioc 0 1` (finite measure) and dominated by `u^{-2}` on `Ioi 1`.

### Section 2 — the Tonelli assembly `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerAbelTonelli.lean`,
`DeningerAbelWindowSwap.lean`, `DeningerAbelMassBound.lean`.  Axiom audit for all declarations:
`propext, Classical.choice, Quot.sound`.

- `deningerLogPullDeriv_continuousOn`, `deningerAbelDifference_eq` — the pullback is `C¹` on the
  ray, so each Abel difference *is* `∫_{ix}^{(i+1)x} H_h'(u) du` by the fundamental theorem of
  calculus.
- `deningerWindowKernel`, `deningerWindowKernel_measurable`, `deningerWindowKernel_slice`,
  `deningerWindowKernel_swap` — the window indicator is jointly measurable, its `u`-slice
  integrates to `‖H_h'(u)‖ · u/(i(i+1))`, and the two orders of integration agree.  Working in
  `ℝ≥0∞` throughout removes every integrability side condition.
- `deningerAbelDifference_enorm_le`, `deningerAbelDifference_mass_le` — **one Abel difference has
  total mass at most `(1/(i(i+1))) ∫_0^∞ u|H_h'(u)| du`.**

This is the analytic core of `(11)`: combined with `deningerAbelCoefficient_summable` and
`deningerWeightedMoment_integrable`, the mass of `f_h` is finite.

### Section 2 — `(11)` for `r = 0`: the preimage has finite mass `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerAbelMajorant.lean`,
`DeningerPreimageMass.lean`.  Axiom audit: `propext, Classical.choice, Quot.sound`.

- `deningerWeightedMomentMass_lt_top` — the first weighted moment is finite as an `ℝ≥0∞` integral.
- `deningerAbelMajorant`, `deningerAbelMajorant_mass_lt_top` — the majorant
  `∑_i |M(i)| ‖H_h((i+1)x) - H_h(ix)‖` has finite total mass over the ray: monotone convergence
  exchanges the sum with the integral, each term costs `1/(i(i+1))` times the weighted moment, and
  the coefficient series is summable by `(9)`.
- `deningerMobiusPreimage_enorm_le` — the Abel partial sums are uniformly bounded by the majorant,
  so the preimage is too.
- `deningerMobiusPreimage_mass_lt_top` — **`∫_0^∞ |f_h(x)| dx < ∞`.**

Stating the conclusion as finiteness of the `ℝ≥0∞` integral rather than `IntegrableOn` is
deliberate: it needs no measurability of `f_h` at all, and the comparison is pure `lintegral_mono`.

### Section 2 — all higher weighted moments `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerHigherMoment.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

- `deningerExpWeight_le_pow` — the exponential weight dominates `y^k` and `y^{-k}` together.
- `deningerLogPullDeriv_weightedPow_norm_le` — at exponent `r + 2` the source bound gives
  `u^{r+1}|H_h'(u)| ≤ C min(u^{2r+2}, u^{-2})`.
- `deningerHigherMoment_integrable` — **`∫_0^∞ u^{r+1}|H_h'(u)| du < ∞` for every `r`**, the second
  factor of `(11)` at every order.

### Section 2 — the order-`r` window and coefficients `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerHigherCoefficient.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

- `deningerWindowPow_integral` — the `r`-th moment of the dilation window is
  `(u^{r+1}/(r+1))(i^{-(r+1)} - (i+1)^{-(r+1)})`.
- `deningerHigherBracket_le` — the bracket is nonnegative and at most `i^{-2}` once `r ≥ 1`.
- `deningerHigherCoefficient_summable` — **the order-`r` coefficients are summable for every
  `r ≥ 1`**, by comparison with `(9)`.  So one inverse-square series controls every order at once.

Every ingredient of `(11)` now exists at every order `r`.

### Section 2 — the Möbius harmonic series converges `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerMobiusHarmonic.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

- `deningerMertensHarmonic_summable` — `∑_i M(i)/(i(i+1))` converges absolutely.
- `deningerMobiusHarmonic_tendsto` — **the partial sums of `∑ μ(n)/n` converge**, to
  `∑_i M(i)/(i(i+1))`.  Summation by parts plus the corpus's PNT in Mertens form
  (`Sieve.tendsto_abs_mertensM_div`) for the boundary term.

Note this is stated for partial sums, not as `Summable`: `∑ μ(n)/n` is only *conditionally*
convergent, so it is not summable in Lean's unordered sense and no `Summable` statement can be
true here.

### Section 2 — the Abelian weight `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerAbelianTelescope.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

- `deningerAbelWeight`, `deningerAbelWeight_nonneg`, `deningerAbelWeight_sum_range`,
  `deningerAbelWeight_hasSum_one` — the Abel increments `n^{-σ} - (n+1)^{-σ}` are nonnegative and
  **sum to exactly one** for every `σ > 0`.  They are therefore a probability weight on the partial
  sums, which is the mechanism of the Abelian theorem needed for `(15)`.
- `deningerAbelWeight_tendsto_zero`, `deningerAbelWeight_tendsto_zero_within` — each individual
  increment vanishes as `σ ↓ 0`.  Both ingredients of the ε-split are therefore in place; only the
  Toeplitz assembly remains.

### Section 2 — the Abel average `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerAbelAverage.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

- `deningerAbelAverage_summable` — averaging a bounded sequence against the Abel weight converges
  absolutely.
- `deningerAbelAverage_sub` — **the limit candidate can be subtracted inside the sum**:
  `∑ b_n w_σ(n) - S = ∑ (b_n - S) w_σ(n)`, because the weight sums to one.
- `deningerAbelAverage_tail_bound` — **the tail past the convergence threshold contributes at most
  `ε`**, again because the weight is a probability weight.

These three plus the head-vanishing assemble into `deningerAbelian_tendsto` below.

### Section 2 — the Abelian limit theorem `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerAbelianLimit.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

- `deningerBounded_of_tendsto` — a convergent real sequence is bounded.
- `deningerAbelian_tendsto` — **the Abelian limit theorem**: `b_n → S` implies
  `∑_n b_n w_σ(n) → S` as `σ ↓ 0`.

This is the general Abelian machinery `(15)` needs, built from nothing: the weight is a
probability weight so the tail costs at most `ε`, and the head is a finite sum of terms each
vanishing with the exponent.

### Section 2 — the harmonic partial sums as an Abel input `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerHarmonicPartial.lean`,
`DeningerAbelSummation.lean`.  Axiom audit: `propext, Classical.choice, Quot.sound`.

- `deningerAbelSummation` — Abel summation as a finite identity,
  `∑_{n ≤ N} a_n f_n = A_N f_N + ∑_{n < N} A_n (f_n - f_{n+1})`.
- `deningerHarmonicPartial`, `deningerHarmonicLimit`, `deningerHarmonicPartial_bounded` — the
  partial sums `A_N = ∑_{n ≤ N} μ(n)/n`, their limit, and their boundedness.
- `deningerHarmonicBoundary_tendsto_zero` — **the Abel boundary term `A_N N^{-σ}` vanishes** for
  every `σ > 0`.
- `deningerHarmonicShift_tendsto`, `deningerHarmonicAbel_tendsto` — **the Abel average of the
  partial sums converges to their limit**, i.e. the Abelian theorem applied to this sequence.

So the right-hand side of `(15)` is fully in place.  What is left is the identification of
`∑ μ(n) n^{-1-σ}` with that Abel average — Abel summation plus the vanishing boundary term — and
then `1/ζ(1+σ) → 0` from the pole, which forces the limit to be `0`.

### Section 2 — the Dirichlet series as an Abel average `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerDirichletAbel.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

- `deningerMobiusDirichlet_summable` — `∑ μ(n) n^{-1-σ}` converges absolutely for every `σ > 0`.
- `deningerDirichlet_abelSum` — **the finite Abel identity for the Dirichlet series**:
  `∑_{n < N+2} μ(n) n^{-1-σ} = A_{N+1} (N+1)^{-σ} + ∑_{m < N} A_{m+1} w_σ(m)`.  The `n = 0`
  increment is killed by `μ(0) = 0`, which is what makes the shifted sum come out exactly as the
  Abel average.

With the boundary term already proved to vanish, passing to the limit identifies the Dirichlet
series with the Abel average of the harmonic partial sums.  The only remaining input for `(15)` is
`1/ζ(1+σ) → 0` as `σ ↓ 0`, from the pole.

### Section 2 — the analytic input `1/ζ → 0` `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerInvZetaPole.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

- `deningerInvZeta_tendsto_zero` — **`ζ(s)⁻¹ → 0` as `s → 1`**, from mathlib's
  `riemannZeta_residue_one`: writing `ζ(s)⁻¹ = (s-1)·((s-1)ζ(s))⁻¹` exhibits it as a vanishing
  factor times a factor tending to one.
- `deningerInvZetaRay_tendsto_zero` — the same along the real ray `s = 1 + σ`, `σ ↓ 0`, which is
  the form `(15)` consumes.

Every input of `(15)` is now proved: the Abel identity, the vanishing boundary term, the Abelian
limit theorem, and the pole.  What is left is the composition.

### Section 2 — the Dirichlet series equals the Abel average `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerDirichletLimit.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

- `deningerDirichlet_eq_abelAverage` — **`∑_n μ(n) n^{-1-σ} = ∑_m A_{m+1} w_σ(m)`** for every
  `σ > 0`, by passing to the limit in the finite Abel identity with the vanishing boundary term.

Both limits of this identity are now proved separately: the right side tends to `∑ μ(n)/n` by
`deningerHarmonicAbel_tendsto`, and `ζ(1+σ)⁻¹ → 0` by `deningerInvZetaRay_tendsto_zero`.  The last
step of `(15)` is the real/complex bridge identifying `∑_n μ(n) n^{-1-σ}` (a real `tsum`) with
`ζ(1+σ)⁻¹` — the corpus has `LSeries_moebius_eq_inv_riemannZeta` for `Re s > 1`, so this is a cast
argument between `Real.rpow` and `Complex.cpow`, not new mathematics.

### Section 2 — `(15)` and `(12)`: the Möbius harmonic series sums to zero `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerMobiusHarmonicZero.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

- `deningerDirichletTerm_eq`, `deningerDirichlet_cast` — the real Dirichlet series
  `∑ μ(n) n^{-1-σ}` is `ζ(1+σ)⁻¹`, via the corpus's `LSeries_moebius_eq_inv_riemannZeta` and a
  `Real.rpow`/`Complex.cpow` cast.
- `deningerHarmonicLimit_eq_zero` — **`∑ μ(n)/n = 0`**, hence `(15)`, hence `(12)`.

The full chain, all built here: convergence of `∑ μ(n)/n` (Abel + PNT in Mertens form), the Abel
weight as a probability weight, the **Abelian limit theorem** (absent from mathlib), the Dirichlet
series as an Abel average, and `ζ(1+σ)⁻¹ → 0` from the pole.

The value does **not** follow from PNT alone: partial summation turns `A_N → S` into
`M(N)/N → S - S = 0` for *any* `S`, so `M(N) = o(N)` is consistent with every constant.  Only the
pole pins it.  This corrects the card's own suggestion that `(15)` is a PNT consequence.

### Section 4 — real-Fourier covariance `(6)` `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerCommutatorCovariance.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound` (one lemma needs only `propext`).

- `deningerCollarCommutator` — the commutator `S h = F(E h) - E(J h)`.
- `deningerCollarCommutator_covariance` — **`(6)`: `S(J h) = -F(S h)`**.
- `deningerCollarCommutator_eq_zero_iff` — the commutator vanishes exactly when the two collars
  are Fourier partners.
- `deningerCollarCommutator_kernel_invariant` — the kernel is invariant under collar exchange.

Stated at the generality the card's own proof uses: the only inputs are that the collar exchange is
an involution and that `F` squares to the identity on the preimages (Fourier inversion plus
evenness).  Instantiating it at `𝔖_μ` needs the even `L¹` extension and `F` on that space; the
algebraic content of `(6)` is complete and independent of that choice.

### Section 2 — the pullback is integrable on the ray `[DONE]`

`formal/GaloisForLFunctions/RHTower/DeningerPullIntegrable.lean`.  Axiom audit: `propext,
Classical.choice, Quot.sound`.

- `deningerLogPull_continuousOn`, `deningerLogPull_integrable` — `H_h ∈ L¹(0,∞)`, by the same
  two-branch comparison as the weighted derivative.

This is the second factor of the card's `(12)`: the Abel representation gives
`∫_0^∞ f_h = (∑_i M(i)/(i(i+1))) · ∫_0^∞ H_h`, because
`∫_0^∞ (H_h((i+1)x) - H_h(ix)) dx = -(1/(i(i+1))) ∫_0^∞ H_h` by dilation scaling.  The first factor
is `deningerHarmonicLimit`, **already proved to be zero**, so `(12)` follows once the dilation
scaling and the sum/integral interchange are in place.

### What is left

`(11)`--`(12)` (Abel summation, Tonelli, and `∫_1^∞ |M(T)|/T² dT < ∞` from the corpus's
unconditional Mertens rate), `(44)`--`(45)` (mathlib has `log * μ = Λ`; only a Fubini on a fixed
ray is left), `(6)` (formal once `𝔖_μ` is defined), and `(5)` itself — the Fourier-inversion
bootstrap `(23)`--`(24)` followed by Poisson summation `(26)`.  `(11)` at order `r ≥ 1` (mechanical repetition of the `r = 0` assembly), the instantiation of
`(6)` at the concrete `𝔖_μ` (mathlib's `TemperedDistribution` is the natural home, since
`F² = reflection` is free there), and `(5)`.  `(12)` and the algebraic content of `(6)` are
**done**.  `(8)`, `(9)`, `(10)` and the weighted-derivative bound are all built.  What
remains for `(11)` is one measure-theoretic step: integrating the Abel difference against `dx`.  The clean route is *not* a
decreasing majorant for `H_h'` but Tonelli on the region — for `i ≥ 1`,

    ∫_0^∞ |H_h((i+1)x) - H_h(ix)| dx ≤ ∫_0^∞ |H_h'(u)| · |{x : ix ≤ u ≤ (i+1)x}| du
                                     = (1/(i(i+1))) ∫_0^∞ u |H_h'(u)| du,

because `{x : ix ≤ u ≤ (i+1)x} = [u/(i+1), u/i]` has length `u/(i(i+1))`.  Summing against
`|M(i)|` then lands exactly on `(9)`, which is already proved.  Note `(9)` cannot be avoided by the
two-sided decay of the pullback alone: without Möbius cancellation the bound near the origin is
`‖f_h(x)‖ ≲ C/x` for *every* exponent `A`, which is not integrable at `0`.  `(15)` needs
`1/ζ(σ) → 0` as `σ ↓ 1`.  Then `(6)` — formal once `𝔖_μ`
is defined — and finally `(5)`, the Fourier-inversion bootstrap `(23)`--`(24)` followed by Poisson
summation `(26)`.  `H_∩` and `Z` already exist as `RHTower.DeningerMeyerCap` and
`RHTower.deningerPoissonLM`.

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
