# The all-prime Euler connection transgresses exactly to the Möbius--Fourier defect

- **ID:** `deninger-euler-gamma-mobius-connection-transgression`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / STRICT SOURCE CONSTRUCTION / ROUTE-L FRONTIER ADVANCE
- **Scientific status:** `[PROVED HERE] [CORPUS-NEW SYNTHESIS]`
  `[EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`
- **Labels:**
  - `DAC_DENINGER_ALL_PRIME_MOBIUS_ADIABATIC_STRICT_LIMIT`;
  - `DAC_DENINGER_EULER_GAMMA_MOBIUS_CONNECTION_TRANSGRESSION`;
  - `DAC_DENINGER_MOBIUS_GREEN_STOKES_BOUNDARY_IMAGE`.
- **Parent:** `DAC_ENHANCED_ADIABATIC_MILNOR_CALDERON_VANISHING_CYCLE`, Route L.
- **Inputs:**
  - `DAC_POISSON_KUMMER_KODAIRA_SPENCER_IDENTITY`;
  - `DAC_DENINGER_MOBIUS_PREDOMAIN_ALL_MOMENTS`;
  - `DAC_DENINGER_MOBIUS_FOURIER_COMMUTATOR_EXACT_KERNEL`;
  - Meyer's Poisson/Fourier intertwining;
  - the unconditional PNT-strength Mertens bound already present in the corpus.
- **Lean status:** partially formalized; see *Lean status* below.

## 1. Result

Put

\[
 H_- = \mathscr S_{\exp}(\mathbb R),\qquad
 H_\cap=\{f\in\mathscr S(\mathbb R):f\text{ even},\ f(0)=\widehat f(0)=0\}.
\tag{1}
\]

For \(u\in H_-\), \(x>0\), and \(a\geq0\), define the adiabatic Möbius lift

\[
 (M_a u)(x)=\sum_{n\geq1}\mu(n)n^{-a}u(\log(nx)),
\tag{2}
\]

and write \(E M_a u\) for its even extension to the line.  At \(a=0\), this is the canonical
Möbius preimage from the exact Poisson-range theorem.  Let

\[
 (Ju)(t)=e^{-t}u(-t).
\tag{3}
\]

For \(a>0\), define the two contragredient prime-power connections

\[
 \begin{aligned}
 A_a^+&=\sum_{m\geq2}\Lambda(m)m^{-a}U_m,
 & (U_m f)(x)&=f(mx),\\
 A_a^-&=\mathcal F A_a^+\mathcal F
       =\sum_{m\geq2}\Lambda(m)m^{-a-1}U_{1/m}.
 \end{aligned}
\tag{4}
\]

The second equality is understood first on the Schwartz radial core and then in tempered
distributions.  The factor \(m^{-1}\) is the additive-Fourier modulus, so `(4)` is the literal
weight-one opposite-collar connection, not a chosen renormalization.

Define the source-pointed two-collar lift and Gamma/co-Poisson boundary by

\[
 \mathcal D_a u=
 \bigl(\mathcal F(E M_a u),E M_a(Ju)\bigr),
 \qquad
 b_\Gamma(F,G)=F-G,
\tag{5}
\]

and put

\[
 \mathfrak S_a=b_\Gamma\mathcal D_a.
\tag{6}
\]

Then:

1. \(M_a:H_-\to L^1_{\mathrm{mom}}(0,\infty)\) is continuous for every \(a\geq0\), where
   \(L^1_{\mathrm{mom}}=\bigcap_{r\geq0}L^1(x^r\,dx)\), and
   
   \[
      M_a u\longrightarrow M_0u\quad(a\downarrow0)
   \tag{7}
   \]
   
   in every moment norm.  This is an all-prime-first strict endpoint; no simultaneous prime
   cutoff is used.
2. For \(a>0\), the Möbius lift is the parallel inverse of the Euler connection:
   
   \[
      \partial_a M_a=A_a^+M_a.
   \tag{8}
   \]
3. The two-collar lift obeys the diagonal contragredient connection law
   
   \[
      \partial_a\mathcal D_a u
      =\bigl(A_a^-\pi_+\mathcal D_a u,
             A_a^+\pi_-\mathcal D_a u\bigr),
   \tag{9}
   \]
   
   and its unsquared boundary satisfies the exact covariant Green--Stokes identity
   
   \[
   \boxed{
      (\partial_a-A_a^-)\mathfrak S_a u
      =(A_a^- -A_a^+)E M_a(Ju).}
   \tag{10}
   \]
   
   Thus the non-diagonal source differential is forced: it is the difference of the Fourier-
   contragredient and physical Euler connections before any Hermitian square.
4. At the two adiabatic ends,
   
   \[
   \begin{aligned}
    \lim_{a\to\infty}\mathfrak S_a u
      &=\mathfrak S_\Gamma u
        :=\mathcal F(EH_u)-EH_{Ju},\\
    \lim_{a\downarrow0}\mathfrak S_a u
      &=\mathfrak S_\mu u
        :=\mathcal F(E M_0u)-E M_0(Ju),
   \end{aligned}
   \tag{11}
   \]
   
   in \(\mathscr S'(\mathbb R)\), where \(H_u(x)=u(\log x)\).  Consequently
   
   \[
   \boxed{
    \mathfrak S_\mu u
     =\mathfrak S_\Gamma u
      -\int_0^\infty
       \left(A_a^-\mathcal F(E M_a u)
             -A_a^+E M_a(Ju)\right)\,da .}
   \tag{12}
   \]
   
   The integral is the canonical improper Pettis integral in tempered distributions.  Equation
   `(12)` constructs the strict all-prime Euler--Gamma/Möbius defect and identifies its physical
   Gamma/co-Poisson boundary image with the already-proved operator \(\mathfrak S_\mu\).
5. On every literal Meyer boundary, the identity is a strict chain identity before completion:
   
   \[
     \mathcal D_0(Zf)=(\widehat f,\widehat f),\qquad
     b_\Gamma\mathcal D_0(Zf)=0
     \quad(f\in H_\cap).
   \tag{13}
   \]
   
   Combined with the exact-kernel theorem, `(13)` is sharp:
   
   \[
      b_\Gamma\mathcal D_0u=0
      \quad\Longleftrightarrow\quad u\in Z(H_\cap).
   \tag{14}
   \]

This closes construction and source-to-Gamma identification of the linear defect.  It does **not**
prove that the independently constructed resolved Xi Green boundary belongs to `(14)`.  On the
canonical two-prime Green boundary, that remaining assertion is exactly
`XI_TWO_PRIME_ORIENTED_BOUNDARY_STRICT_TRANSPORT` and hence has RH strength.

## 2. Strict all-prime endpoint

For \(r\geq0\), let

\[
 \|f\|_{1,r}=\int_0^\infty x^r|f(x)|\,dx.
\tag{15}
\]

For (a>0), termwise integration gives

\[
 \|M_a u\|_{1,r}
 \leq
 \left(\sum_{n\geq1}{|\mu(n)|\over n^{a+r+1}}\right)
 \int_0^\infty y^r|H_u(y)|\,dy<\infty.
\tag{16}
\]

This absolute argument deliberately does not include \(a=0,r=0\).  Put

\[
 M_a(T)=\sum_{n\leq T}\mu(n)n^{-a}.
\tag{17}
\]

Partial summation gives

\[
 M_a(T)=T^{-a}M(T)+a\int_1^T M(y)y^{-a-1}\,dy.
\tag{18}
\]

The unconditional bound

\[
 |M(T)|\leq CT\exp\{-c(\log T)^{1/3}\}
\tag{19}
\]

and a split of the integral in `(18)` at \(T^{1/2}\) imply, uniformly for
\(0\leq a\leq1/2\),

\[
 |M_a(T)|\leq C'T\exp\{-c'(\log T)^{1/3}\}.
\tag{20}
\]

Abel summation in `(2)` gives

\[
 M_a u(x)=-x\int_1^\infty M_a(T)H_u'(xT)\,dT.
\tag{21}
\]

For fixed \(T\), \(M_a(T)\to M(T)\).  Equations `(20)`--`(21)`, Tonelli, and the substitution
\(y=xT\) give

\[
 \begin{aligned}
 \|M_a u-M_0u\|_{1,r}
 &\leq
 \left(\int_1^\infty
  {|M_a(T)-M(T)|\over T^{r+2}}\,dT\right)
 \left(\int_0^\infty y^{r+1}|H_u'(y)|\,dy\right).
 \end{aligned}
\tag{22}
\]

The first integrand is dominated, even for \(r=0\), by a constant multiple of

\[
 T^{-1}\exp\{-c'(\log T)^{1/3}\},
\tag{23}
\]

which is integrable.  Dominated convergence proves `(7)`.  The same estimates, with the standard
all-weight seminorms of \(H_-\), prove continuity.  This is the load-bearing strictness statement:
the endpoint is obtained after forming the full all-prime inverse.  It does not assert convergence
of prime-by-prime partial Euler products in the critical \(L^1\) norm.

## 3. Euler connection and contragredient collar

For \(a>0\), differentiation of `(2)` is absolutely valid in every norm `(15)`:

\[
 \partial_aM_au
 =-\sum_{n\geq1}\mu(n)(\log n)n^{-a}U_nH_u.
\tag{24}
\]

The elementary Dirichlet-convolution identity

\[
                  \Lambda*\mu=-\mu\log
\tag{25}
\]

turns `(24)` into

\[
 \partial_aM_au
 =\sum_{d,k\geq1}\Lambda(d)\mu(k)(dk)^{-a}U_{dk}H_u
 =A_a^+M_au,
\tag{26}
\]

proving `(8)`.  This is the inverse-gauge form of the already-known identity
\(-Z_a^{-1}\partial_aZ_a=A_a^+\).

For additive Fourier transform normalized by

\[
 \widehat f(\xi)=\int_\mathbb R f(x)e^{-2\pi ix\xi}\,dx,
\tag{27}
\]

one has

\[
 \mathcal F(U_mf)=m^{-1}U_{1/m}(\mathcal Ff).
\tag{28}
\]

Equations `(4)` and `(28)` give

\[
                  \mathcal F A_a^+=A_a^-\mathcal F.
\tag{29}
\]

Apply `(26)` to \(u\) and \(Ju\), then use `(29)`.  This proves `(9)`.  Subtracting the two
components gives

\[
 \begin{aligned}
 \partial_a\mathfrak S_a u
 &=A_a^-\mathcal F(E M_au)-A_a^+E M_a(Ju)\\
 &=A_a^-\mathfrak S_a u+(A_a^--A_a^+)E M_a(Ju),
 \end{aligned}
\tag{30}
\]

which is `(10)`.  No scalar product, adjoint square, positivity, or divisor parameter occurs.

## 4. Endpoint transgression and strict boundary identity

As \(a\to\infty\), every term \(n\geq2\) in `(2)` tends to zero absolutely in all moment norms;
therefore \(M_au\to H_u\).  Equation `(7)` gives the other endpoint.  Fourier is continuous from
\(L^1\) to tempered distributions, so both limits in `(11)` follow.

For \(0<\varepsilon<R\), the fundamental theorem of calculus applied after pairing with an
arbitrary Schwartz test function gives

\[
 \mathfrak S_\varepsilon u-\mathfrak S_Ru
 =-\int_\varepsilon^R
 \left(A_a^-\mathcal F(E M_au)-A_a^+E M_a(Ju)\right)\,da.
\tag{31}
\]

The endpoint limits prove convergence of this improper weak integral and give `(12)`.  Since
\(\mathscr S(\mathbb R)\) is nuclear Fréchet and the paired integrals are equicontinuous on compact
adiabatic intervals, the weak integral is the canonical Pettis integral in
\(\mathscr S'(\mathbb R)\).

Now take \(f\in H_\cap\).  Exact Möbius inversion and Meyer--Poisson reflection give

\[
 M_0(Zf)=f,\qquad JZf=Z\widehat f,\qquad M_0(JZf)=\widehat f.
\tag{32}
\]

Substitution in `(5)` proves `(13)`.  The existing exact-kernel theorem for
\(\mathfrak S_\mu\) proves `(14)`.  Thus the source transgression lands in the actual
Gamma/co-Poisson conormal and annihilates literal source boundaries without replacing them by a
closure or defining a quotient with the desired kernel.

## 5. Finite gauge exactness and why order matters

For a finite prime set \(P\), put

\[
 Z_{P,a}=\prod_{p\in P}(1-p^{-a}U_p)^{-1},\qquad
 M_{P,a}=Z_{P,a}^{-1}.
\tag{33}
\]

Then

\[
 -Z_{P,a}^{-1}\partial_aZ_{P,a}
 =\sum_{p\in P}\sum_{k\geq1}(\log p)p^{-ka}U_{p^k},
\tag{34}
\]

so every finite connection is a Maurer--Cartan gauge coboundary.  Equations `(8)`--`(10)` hold
with \(P\)-subscripts by finite algebra.

It is false that this permits an unordered primewise passage in the critical \(L^1\) norm.
Already the absolute estimate would require

\[
                    \sum_n{|\mu(n)|\over n}<\infty,
\tag{35}
\]

which fails.  The separate aperture--Stokes theorem also shows that simultaneous
prime-cutoff/adiabatic limits retain path-dependent exponential residue data.  The strict theorem
therefore uses the canonical order

```text
form full all-prime M_a for a>0
→ prove uniform PNT control
→ take a ↓ 0 in the nuclear/moment topology.
```

This is exactly the all-prime-before-specialization order required by Route L.  No arbitrary
cofinal aperture is silently identified.

## 6. Conjecture / proof-or-failure loop

1. **Conjecture:** primewise finite Euler gauges converge absolutely to the critical source
   inverse.  **Failed.**  The \(r=0\) moment would require `(35)`; enhanced aperture limits are
   path-sensitive as well.
2. **Conjecture:** the finite connection has a nonzero ordinary cohomology class.
   **Failed.**  Equation `(34)` makes every finite stage gauge-exact.
3. **Conjecture:** form the full inverse first and use PNT cancellation at the endpoint.
   **Proved.**  Equations `(17)`--`(23)` give the strict limit `(7)`.
4. **Conjecture:** the Möbius--Fourier commutator is the endpoint of the physical/Fourier
   connection difference.  **Proved.**  Equations `(8)`--`(12)` give the exact transgression.
5. **Conjecture:** Fourier-odd covariance alone annihilates the resolved Green defect.
   **Failed.**  It only makes the image a cycle in the next target grade.  The coefficient-faithful
   physical reader is not a chain map on the canonical two-prime boundary off the critical line.
6. **Conjecture:** source exactness of the two-prime Green boundary completes `(13)` for the
   resolved physical landing.  **Failed as an inference.**  Its fixed readout remains
   \(g_2(s)-g_3(s)\), zero exactly at \(\Re s=1/2\).  A new arithmetic incidence theorem is still
   required.

## 7. Frontier change

The following Route-L items are now constructed on paper:

- canonical all-prime-first adiabatic Möbius source family;
- its exact von-Mangoldt/Kummer connection;
- forced Fourier-contragredient opposite connection;
- non-diagonal linear source differential \(A_a^--A_a^+\);
- strict Gamma/co-Poisson two-collar landing;
- exact endpoint identification with \(\mathfrak S_\mu\);
- unsquared covariant Green--Stokes identity `(10)`;
- strict annihilation and exact kernel on every literal Meyer--Poisson boundary.

The remaining first source producer is no longer construction of this differential or its
analytic boundary image. It is `DAC_DENINGER_RESOLVED_GREEN_SOURCE_ANNIHILATOR`:

> identify the degree-two rational-Witt/Milnor Gamma realization and prove the explicit
> source--Poisson obstruction `Omega_(mu,Gamma)=S_mu G_Gamma D` vanishes. Canonical Möbius
> inversion then supplies the degree-one chain prelift and lands the boundary in literal kernel
> `(14)`. Its Xi-jet image must agree coefficient-faithfully with already-resolved singular
> Gamma/Calderón Green transport.

On fixed prime-2/prime-3 boundary, physical value is \(g_2(s)-g_3(s)\). Hence
`XI_TWO_PRIME_ORIENTED_BOUNDARY_STRICT_TRANSPORT` is sharp RH-equivalent endpoint test of the
producer, not a substitute construction. Producer must not be replaced by source exactness,
Fourier oddness, target-cycle nilpotence, or a quotient declaring Green vector regular.

## 8. Hostile audit and novelty boundary

- **Unconditional:** only non-elementary arithmetic input is the unconditional PNT-strength
  Mertens estimate `(19)`.  No RH-equivalent Mertens bound, zero location, or Weil positivity is
  used.
- **No operator-by-kernel definition:** \(M_a,A_a^\pm,\mathcal D_a,b_\Gamma\) are explicit before
  `(14)` is proved.
- **No diagonal scalar repair:** `(10)` is linear and off-diagonal before polarization.
- **No raw-Hilbert claim:** strict endpoint is proved in moment/nuclear-to-distribution topology.
- **No false RH claim:** `(13)` concerns literal Poisson boundaries.  Membership of resolved Xi
  Green boundary in the same kernel remains open and RH-bearing.
- **Parent mathematics:** Euler logarithmic derivatives, Möbius inversion, Fourier dilation
  covariance, Burnol co-Poisson intertwining, and Connes--Consani quantized differentials are not
  claimed as new.
- **Project-specific new synthesis:** exact all-prime-first PNT endpoint `(7)`, connection
  transgression `(10)`--`(12)`, and identification of its endpoint with the previously constructed
  full-Meyer Möbius--Fourier detector.  Corpus and targeted primary-literature searches found the
  ingredients, but not this exact domain-sensitive conjunction.  Priority remains unverified.

## References

- Jean-François Burnol, *Entrelacement de co-Poisson*, Ann. Inst. Fourier 57 (2007),
  arXiv:math/0407443.
- Alain Connes and Caterina Consani, *The Scaling Hamiltonian*, J. Operator Theory 85 (2021),
  arXiv:1910.14368.
- `deninger-mobius-fourier-commutator-poisson-kernel.md`.
- `../../not_new_scientific_knowledge/semilocal-dual-pair-euler-connection-source-law.md`.
- `../../../1-in-progress/deninger-enhanced-adiabatic-milnor-calderon-vanishing-cycle.md`.

## Lean status

`formal/GaloisForLFunctions/RHTower/DeningerAdiabaticMobiusPreimage.lean`,
`DeningerAdiabaticMobiusEndpoint.lean`, `DeningerMobiusFourierCommutator.lean` and
`DeningerVonMangoldtMoebiusConvolution.lean`.  Axiom audit for every declaration:
`propext, Classical.choice, Quot.sound`.

### Done

- **`(2)`: the adiabatic Möbius lift, with no prime cutoff.**  `deningerAdiabaticSource`,
  `deningerAdiabaticMobiusCoefficient`, **`deningerAdiabaticMobiusPreimage`** and
  `deningerAdiabaticMobiusPreimage_eq_tsum`.  The exact gauge factorization
  `M_a h(x) = x^a f_{exp(-a·)h}(x)` places the lift on the already formalized critical Möbius
  preimage domain, so `deningerAdiabaticMobiusPreimage_zero` is the canonical preimage at `a = 0`
  and `deningerAdiabaticMobiusPreimage_moment_integrable` gives every polynomial moment for every
  `a ≥ 0`.  The moment norms `(15)` are `deningerAdiabaticMomentFun`,
  `deningerAdiabaticMomentFun_memLp`, `deningerAdiabaticMomentLp`.
- **`(7)`, and the `a → 0` half of `(11)`: the strict endpoint.**
  `deningerMobiusPreimage_sub_meyer`, `deningerAdiabaticBoundaryError` with its majorant and
  `tendsto_integral_norm_deningerAdiabaticBoundaryError`, `tendsto_deningerAdiabaticSource_zero`,
  `deningerAdiabaticMomentLp_dist_le` and **`tendsto_deningerAdiabaticMomentLp_zero`** — strict `L¹`
  convergence in every polynomial moment, with both singular effects at `a = 0` (the source moving
  in Meyer's projective topology and the physical multiplier `x^a` losing uniform boundedness)
  handled separately.
- **`(14)`: the Möbius--Fourier commutator.**  `deningerFourierSq_apply`,
  `deningerEvenDistribution_fourierSq`, `deningerPreimageDistribution`,
  **`deningerMobiusCommutator`** and **`deningerMobiusCommutator_fourier_covariance`**
  (`𝔖_μ(Jh) = -ℱ(𝔖_μ h)`).
- **`(25)`: the arithmetic step of the Euler connection.**
  `DeningerVonMangoldtMoebiusConvolution.lean`: `arithmeticFunction_mul_zeta_injective` and
  **`vonMangoldt_mul_moebius`**, the identity `Λ * μ = -(μ · log)` that turns the `a`-derivative of
  `(2)` into the Euler connection.  mathlib carries `∑_{d|n} μ(d)log d = -Λ(n)`; the convolution
  form the card uses follows by convolving with `ζ` and inverting.

### Not yet formalized

- `(8)`, `(24)`, `(26)`: the Euler connection `∂_a M_a u = A_a^+ M_a u` itself — the operators
  `A_a^±` and term-by-term differentiation of `(2)` in the moment norms.
- `(9)`, `(28)`, `(29)`: the Fourier intertwining `ℱ A_a^+ = A_a^- ℱ`.
- `(10)`, `(30)`: the transgression ODE for `𝔖_a`.
- `(12)`, `(31)`: the Pettis-integral transgression identity in `𝒮'(ℝ)`.
- `(13)`: the substitution of `M_0(Zf) = f`, `JZf = Z f̂` into `(5)`.

## Gates

- [x] 0 → 1 in-progress: explicit source family, topology, boundary map, and falsifiers fixed
- [x] 1 → 2 fully-proven: dependency-closed proof `(7)`--`(14)` and hostile audit complete
- [ ] 2 → 3 formalized: `(2)`, `(7)`, `(11)`'s endpoint, `(14)` and `(25)` proved
  unconditionally; the connection `(8)`--`(10)` and the transgression `(12)`--`(13)` remain
  (see *Lean status*)
- [ ] 3 → 4 publication-ready
- [ ] source successor: `DAC_DENINGER_RESOLVED_GREEN_SOURCE_ANNIHILATOR`
- [ ] endpoint falsifier: `XI_TWO_PRIME_ORIENTED_BOUNDARY_STRICT_TRANSPORT`

## Log

- 2026-08-12 — Corpus audit: the adiabatic lift, its strict endpoint and the Möbius--Fourier
  commutator were already built.  Added the von Mangoldt--Möbius convolution identity `(25)`, the
  arithmetic step of the Euler connection.

- 2026-08-08 — Constructed all-prime-first adiabatic Möbius family, proved strict PNT endpoint,
  derived physical/Fourier contragredient connection and unsquared Green--Stokes law, and identified
  endpoint boundary image exactly with the Möbius--Fourier commutator.  Primewise absolute passage
  and covariance-only annihilation were falsified.  Remaining Route-L gate reduced to arithmetic
  incidence of one fixed resolved two-prime Green boundary in the literal Poisson kernel.
