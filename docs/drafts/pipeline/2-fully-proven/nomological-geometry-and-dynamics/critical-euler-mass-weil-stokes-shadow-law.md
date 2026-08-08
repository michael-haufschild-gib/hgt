# Critical Euler connection, Mass boundary, Weil torque, and Stokes rapidity shadow law

- **ID:** `ngd-critical-euler-mass-weil-stokes-shadows`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper)
- **Status:** `[PAPER-PROVED] [CROSS-ROUTE SOURCE LAW] [ROUTE-E NONSELECTION]`
  `[GAMMA NORMALIZATION NONSELECTION] [NOT RH] [NO LEAN WRITTEN]`
- **Parent:** `dirichlet-maurer-cartan-mellin-orbit-law.md`
- **Statement:** One pre-divisor Dirichlet source current has exact Route-L, primitive-prime Mass,
  reflection-odd Weil, and prime Stokes-tangent shadows; it does not select Route-E conductance or
  full archimedean completion.

## Setup

Use the Dirichlet algebra and current from the parent card:

\[
 \Theta_E(n)=\Lambda(n),\qquad
 \Theta_a(n)=\Lambda(n)n^{-a},\qquad
 \partial_a\Theta_a=-\delta\Theta_a.
 \tag{1}
\]

Let `[n]` denote the point mass at `n`, so `[m]*[n]=[mn]`. On a common algebraic dilation core let
`U_rf(x)=f(rx)`. Define

\[
 \rho_a^+([n])=n^{-a}U_n,
 \qquad
 \rho_a^-([n])=n^{-a-1}U_{1/n}.
 \tag{2}
\]

Infinite operator series below are interpreted on the strict source cores established in the cited
Route-L parent; all coefficient and finite-chain identities are algebraic.

## Theorem 1 — Route-L connection shadows

Both maps in `(2)` are algebra representations, and

\[
 A_a^+:=\rho_a^+(\Theta_E)
 =\sum_{n\ge2}\Lambda(n)n^{-a}U_n,
 \qquad
 A_a^-:=\rho_a^-(\Theta_E)
 =\sum_{n\ge2}\Lambda(n)n^{-a-1}U_{1/n}.
 \tag{3}
\]

For

\[
 \mathcal M_a=\rho_a^+(M)=\sum_{n\ge1}\mu(n)n^{-a}U_n,
\]

one has

\[
 \boxed{\partial_a\mathcal M_a=A_a^+\mathcal M_a.}
 \tag{4}
\]

Each representation is individually flat. Its first comparison defect is

\[
 \kappa_a=A_a^--A_a^+,
 \tag{5}
\]

which is exactly the coefficient in the already-proved Route-L transgression

\[
 (\partial_a-A_a^-)\mathfrak S_au
 =(A_a^--A_a^+)E\mathcal M_a(Ju).
 \tag{6}
\]

### Proof

Multiplicativity follows from `U_mU_n=U_(mn)` and multiplicativity of the scalar weights. Formula
`(3)` is evaluation of the source coefficients. From the parent identity
`-(delta M)=Theta_E*M`, coefficientwise differentiation gives

\[
 \partial_a\mathcal M_a
 =\rho_a^+(-\delta M)
 =\rho_a^+(\Theta_E*M)
 =A_a^+\mathcal M_a.
\]

The strict-domain statement `(6)` is Theorem 2 of
`../new_scientific_knowledge/deninger/deninger-euler-gamma-mobius-connection-transgression.md`;
`(5)` is its displayed comparison coefficient. `square`

## Theorem 2 — primitive-prime Mass boundary shadow

At half density, restrict `(1)` to ordered primes `p_0<p_1<...`:

\[
 t_j=\Theta_{1/2}(p_j)=\frac{\log p_j}{\sqrt{p_j}},
 \qquad T_m=\sum_{j<m}t_j.
\]

On the oriented path with `partial e_j=v_j-v_(j+1)`, define

\[
 z_N=\sum_{j<N}t_jv_j,
 \quad q_N=\sum_{j<N-1}T_{j+1}e_j,
 \quad b_N=T_Nv_{N-1}.
\]

Then

\[
 \boxed{z_N=\partial q_N+b_N.}
 \tag{7}
\]

The pushforward is coefficient-faithful on the primitive-prime quotient and kills higher
prime-power grades. Its capacity inverse is singular:

\[
 T_{j+1}/t_{j+1}\longrightarrow\infty.
 \tag{8}
\]

### Proof

In `partial q_N`, the coefficient at `v_0` is `T_1=t_0`; at an interior `v_j` it is
`T_(j+1)-T_j=t_j`; at `v_(N-1)` it is `-T_(N-1)`. Adding `b_N` changes the last coefficient to
`T_N-T_(N-1)=t_(N-1)`, proving `(7)`. Distinct prime vertices read every retained coefficient.
Statement `(8)` is the prefix-capacity theorem proved in
`../constraint-relativity/polarized-incidence-stokes-and-e-mass-capacity-phase-law.md`. `square`

## Theorem 3 — reflection-odd Weil tangent

For a coefficient function `f`, define locally finite atomic distributions

\[
 \iota_\pm(f)=\sum_{n\ge2}f(n)
  (\delta_{\log n}\pm\delta_{-\log n}).
 \tag{9}
\]

Let the prime Weil kernel be `K_pr=-iota_+(Theta_(1/2))`, and let `X` multiply a distribution by
its position. Then

\[
 \boxed{XK_{\rm pr}
 =\iota_-\!\left(\partial_a\Theta_a|_{a=1/2}\right)}
 \tag{10}
\]

and explicitly

\[
 XK_{\rm pr}=-\sum_{n\ge2}
 \frac{\Lambda(n)\log n}{\sqrt n}
 (\delta_{\log n}-\delta_{-\log n}).
 \tag{11}
\]

This odd distribution is coefficient-faithful on every prime-power grade.

### Proof

Multiplication by position gives `X iota_+(f)=iota_-(delta f)`. Combine this with
`partial_aTheta_a=-deltaTheta_a` and the sign in `K_pr`. Positive atom locations `log n` are
distinct, and `Lambda(n)log n` is nonzero exactly on prime powers, proving faithfulness. `square`

## Theorem 4 — Stokes prime rapidity and coefficient weld

For `eta(s)=2 Re(s)-1`, prime `p`, and positive rank `M`, define

\[
 \omega_{p,M}(s)=M\eta(s)\log p.
 \tag{12}
\]

Then

\[
 \omega_{p,M}(s)=M\eta(s)\Theta_E(p),
 \qquad
 \delta_p(s)^M=e^{\omega_{p,M}(s)},
 \tag{13}
\]

and reflection sends `omega` to `-omega`. Hence

\[
 -(e^\omega-1)(e^{-\omega}-1)=4\sinh^2(\omega/2).
 \tag{14}
\]

For every prime `p`, the Route-L/Mass/Weil/Stokes coefficient identity is

\[
 \boxed{
 [\delta_{\log p}]XK_{\rm pr}
 =-\frac1M\,t_p\,
   \partial_\eta\omega_{p,M}|_{\eta=0}.}
 \tag{15}
\]

### Proof

Equations `(12)`--`(14)` are direct. The left side of `(15)` is
`-(log p)^2/sqrt(p)`, while the right side is
`-M^(-1)(log p/sqrt(p))(M log p)`. `square`

## Sharp scope: prime powers are a different reduction

On `p^k`, the Stokes clock uses `log(p^k)=k log p`, whereas
`Theta_E(p^k)=Lambda(p^k)=log p`. Thus Stokes sees the bare derivation `delta E`; Route L sees the
Möbius-dressed Maurer--Cartan current `M*delta E`. They coincide on primitive primes, not on all
prime-power grades. At the central fibre `(12)` vanishes; only the full transverse family or its
normal derivative is faithful.

## No-go 1 — arithmetic source does not select Route-E flow

The source algebra determines Möbius orientation and von-Mangoldt fixed current, but not Route-E's
edge relation, conductance, Hall allocation, capacity, or directed seam.

Indeed, take two labeled parallel edges `e_1,e_2` between one positive and one negative vertex.
For `0<=u<=1`,

\[
 q_u=ue_1+(1-u)e_2
\]

has the same signless boundary and arithmetic coefficients for every `u`, while labeled
provenance differs. Hence no functor of `(A,E,M,delta,Theta_E)` alone selects `q_u`.

**Positive survivor:** a Route-E comparison requires additional source relation/capacity data
`R_E`; the Dirichlet current supplies its arithmetic load but not its physical allocation.

## No-go 2 — arithmetic source does not normalize Gamma completion

For real `c`, multiplication of any completed factor by

\[
 H_c(s)=e^{c(s-1/2)^2}
\]

preserves nonvanishing, Schwarz reality, and `s <-> 1-s` reflection, and leaves
`(A,E,M,delta,Theta_E)` unchanged. It changes the completed logarithmic current by
`2c(s-1/2)`. Therefore the arithmetic gauge algebra cannot determine full archimedean torque or
Xi completion. A literal Gamma/theta seed and its normalization are additional source data.

## Circularity audit

Every construction precedes Xi-zero specialization. Theorems use arithmetic convolution,
dilations, finite telescoping, atomic reflection, and the Stokes character for arbitrary `s`.
No zero coefficient, source-null-homology, central-line positivity, or RH-equivalent premise enters.

## NGD consequence

One flat source differential object has nonisomorphic arithmetic, operator, chain-boundary,
reflection-odd, and rapidity shadows. This is an exact model of NGD's multi-coefficient doctrine.
The four-shadow field target remains open precisely at Route-E allocation and normalized
archimedean completion.

## Gates

- [x] Route-L operator shadow proved on declared core
- [x] primitive-prime Mass boundary shadow proved
- [x] odd Weil tangent proved coefficientwise
- [x] Stokes rapidity weld proved
- [x] Route-E and Gamma nonselection countermodels closed
- [ ] physical Route-E relation/capacity supplied by source
- [ ] normalized Gamma/theta comparison supplied by source
- [ ] formalized in Lean 4

## Lean-return note

No Lean code was written or built. Later formalization should reuse the existing formal
Möbius/von-Mangoldt weld and separate finite prime-chain telescoping from distributional/operator
statements. No repository file was edited or nominated here.

## Log

- 2026-08-08 — exact cross-route coefficient theorem and two sharp source nonselection laws closed.
