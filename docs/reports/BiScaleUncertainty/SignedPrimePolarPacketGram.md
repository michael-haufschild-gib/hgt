# Cancellation-sensitive signed prime–polar Gram transport

## Statement

Let f be any real continuous compactly supported source, h(t)=∫f(u)f(u+t)du,
R=h(0), L=log(N+2), a,d,η>0, and p(t)=2cosh(t/2). Write

\[
 \nu_L=\sum_{n=2}^{N+2}v_n\delta_{\log n}-p(t)1_{[0,L]}(t)\,dt,
 \qquad v_n=\Lambda(n)/\sqrt n,
 \qquad D_L(k)=\int k\,d\nu_L.
\]

Construct the **actual signed source packet**

\[
 P_L(u)=\sum_{n=2}^{N+2}v_nf(u+\log n)
       -\int_0^Lp(t)f(u+t)\,dt,
 \qquad Q_L=\int_{\mathbb R}P_L(u)^2\,du.
\]

P_L is continuous and compactly supported. Every term above is finite, without
source differentiability or any additional integrability assumption. Its energy
has the exact signed Gram representation

\[
 Q_L=\iint h(s-t)\,d\nu_L(s)d\nu_L(t)\ge0. \tag{4}
\]

Thus Q_L contains the prime–prime term, **both negative prime–polar terms**, and
the positive polar–polar term. Since h is even, the two mixed terms coincide:

\[
 Q_L=\sum_{m,n}v_mv_nh(\log n-\log m)
 -2\sum_n v_n\int_0^Lp(t)h(t-\log n)\,dt
 +\int_0^L\int_0^Lp(s)p(t)h(s-t)\,ds\,dt. \tag{5}
\]

The unsigned mass M_L=Σv_n+∫₀ᴸp satisfies

\[
 0\le Q_L\le M_L^2R. \tag{6}
\]

For every y∈ℝ, including negative shifts,

\[
 |D_L(h(\cdot+y)-h)|^2\le 2Q_L(R-h(y)). \tag{7}
\]

For the annular average H(t)=d⁻¹∫ₐ^{a+d}h(t+y)dy, define

\[
 K^{\rm signed}_{a,d,L}(f)
 =\frac1d\int_a^{a+d}\sqrt{2Q_L(R-h(y))}\,dy.
\]

Then

\[
 |D_L(h)-D_L(H)|\le K^{\rm signed}_{a,d,L}(f)
 \le M_LK_{a,d}(f), \tag{8}
\]

and the local Lévy estimate is

\[
 K^{\rm signed}_{a,d,L}(f)
 \le\eta\int_a^{a+d}(R-h(y))w_{\rm arch}(y)\,dy
 +\frac{Q_L}{2\eta d^2}\int_a^{a+d}e^{-y/2}\sinh y\,dy. \tag{9}
\]

Substituting the exact Chebyshev work identity from
`SignedPrimePolarTransport.md` for D_L(H) gives the direct arithmetic coupling.
The +H(0) boundary, upper endpoint, and negative-exponential polar shadow remain.
No grid blindness, sign of h(log n), arithmetic estimate, nonzero source, or
finite full Lévy energy is assumed.

## Dependency-closed proof

**Actual-source admission.** Choose B>0 containing supp f in [−B,B]. The polar
packet vanishes outside [−B−L,B]: a nonzero integrand requires both 0≤t≤L and
−B≤u+t≤B. Joint continuity on compact parameter windows implies continuity of
the polar integral. The finite atomic packet is continuous with compact support,
so their difference P_L has the same properties and a finite squared norm.

**Mixed Fubini.** For any actual compact continuous source q, the function
q(u)p(t)f(u+t) has compact support in ℝ². Indeed, if supp q⊂[−C,C], nonzero values
require |u|≤C and |t|≤B+C. It is continuous, hence integrable; Fubini applies also
with t restricted to [0,L]. Finite sum interchange and subtraction now give

\[
 \int q(u)P_L(u)du=D_L\!\left(t\mapsto\int q(u)f(u+t)du\right). \tag{10}
\]

Taking q=P_L and then q(u)=f(u+t), using translation invariance, proves (4).
Expanding the two signed measures, with compact-window Fubini and h(−x)=h(x),
gives (5). The actual coefficients v_n and p(t) are nonnegative. Consequently
|D_L(k)|≤M_L sup|k| for bounded k. Apply this twice to (4), using |h|≤R, to obtain
(6). No cancellation estimate is assumed in this comparison.

**Signed increment geometry.** Put q_y(u)=f(u−y)−f(u), another actual compact
continuous source. Translation invariance gives
∫q_y(u)f(u+t)du=h(t+y)−h(t), while the source chord identity gives
∫q_y²=2(R−h(y)). Cauchy–Schwarz applied to (10) proves (7).

**Annular transport.** Continuity on the compact rectangle [0,L]×[a,a+d]
justifies polar/annular Fubini; the atomic sum is finite. Hence

\[
 D_L(H)-D_L(h)=\frac1d\int_a^{a+d}D_L(h(\cdot+y)-h)dy.
\]

Integrate (7)'s square-root bound to get the first part of (8). Inequality (6)
gives its second part. For each y>0, apply the existing scalar Young inequality
with nonnegative energy Q_L, origin deficit R−h(y), weight 1/d, and parameter
ηw_arch(y). It gives

\[
 d^{-1}\sqrt{2Q_L(R-h(y))}
 \le\eta(R-h(y))w_{\rm arch}(y)
 +\frac{Q_L}{2\eta d^2}w_{\rm arch}(y)^{-1}.
\]

Integrate and use the exact inverse weight exp(−y/2)sinh y to obtain (9).
All annular terms are finite because a>0. This closes every analytic dependency.

## Scope and certification

This is one contribution: construction of the continuum signed packet and its
cancellation-sensitive replacement for unsigned-mass transport. Support helpers,
Fubini, the Gram identity, comparison, and the Chebyshev corollary count together.

Formal leaves: `SignedPrimePolarPacket.lean` and
`SignedPrimePolarGramTransport.lean`. Both direct leaf checks and the final seven-endpoint axiom audit pass.
The only reported axioms are propext, Classical.choice, and Quot.sound. Main
signatures contain only the actual compact source and numerical parameters.
Imports are wired; the companion ledger records the separate global lint result.

The result concerns each actual finite window. Compact support makes the scalar
pairing eventually insensitive to larger cutoffs, but does **not** imply the
same for Q_L: distant source translates can still contribute squared norm.
No cutoff-uniform bound or full-half-line packet is claimed. Corpus search found
finite discrete Gram precedents but no retrieved construction of this mixed
packet; this is an internal gap closure, not an external priority claim.
