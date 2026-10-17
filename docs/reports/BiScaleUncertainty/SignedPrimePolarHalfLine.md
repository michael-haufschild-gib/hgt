# Source-admitted full-half-line signed Chebyshev transport

## The global scalar object

Let f be any real continuous compactly supported source, h(t)=∫f(u)f(u+t)du,
and R=h(0). The literal full signed pairing is

\[
 D_\infty(k)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}k(\log n)
             -\int_0^\infty 2\cosh(x/2)k(x)\,dx.
\]

For every a,d>0, form the already constructed annular average and its derivative

\[
 H(t)=d^{-1}\int_a^{a+d}h(t+y)dy,
 \qquad V(t)=d^{-1}[h(t+a+d)-h(t+a)].
\]

Both D∞(h) and D∞(H) are **admitted**: their atom sequences have finite support,
the series of absolute values converge, and their polar integrands are integrable
on the full positive half-line. These properties are derived from f itself.
No source derivative, grid-zero, finite full Lévy-energy, or arithmetic estimate
is assumed.

Write E(x)=ψ(exp x)−exp x. The two work integrands

\[
 e^{-x/2}(V(x)-H(x)/2)E(x),\qquad e^{-x/2}H(x)
\]

are also integrable on [0,∞). Define the actual global work

\[
 W_\infty(f;a,d)=H(0)
 -\int_0^\infty e^{-x/2}(V(x)-H(x)/2)E(x)dx
 -\int_0^\infty e^{-x/2}H(x)dx.
\]

The exact global identity is

\[
 \boxed{D_\infty(H)=W_\infty(f;a,d).} \tag{10}
\]

The origin contribution and the negative-exponential polar shadow survive.
The upper endpoint vanishes by proved support, not by an unproved limit.

## A common source cutoff and global transport

Compact support of f gives compact support of h. Choose an actual D>0 such that
h(x)=0 whenever |x|>D, and set

\[
 N_0(f)=\lceil e^D\rceil,\qquad L_0=\log(N_0+2)>D.
\]

This cutoff depends only on f. For every annulus a,d>0,

\[
 h(x)=H(x)=V(x)=0\qquad(x\ge L_0). \tag{11}
\]

In particular, for every K∈ℕ and N=N₀+K,

\[
 D_\infty(h)=D_{\log(N+2)}(h),\qquad
 D_\infty(H)=D_{\log(N+2)}(H),\qquad
 W_\infty=W_{\log(N+2)}.
\]

Let Q_N be the actual finite signed packet energy from
`SignedPrimePolarPacketGram.md`, including both prime–polar cross terms.
Then for every η>0 and every K∈ℕ,

\[
 \boxed{
 |D_\infty(h)-W_\infty(f;a,d)|
 \le \eta\int_a^{a+d}(R-h(y))w_{\rm arch}(y)dy
 +\frac{Q_{N_0+K}}{2\eta d^2}
       \int_a^{a+d}e^{-y/2}\sinh y\,dy.
 } \tag{12}
\]

The stronger square-root cost also holds:

\[
 |D_\infty(h)-W_\infty|
 \le d^{-1}\int_a^{a+d}\sqrt{2Q_{N_0+K}(R-h(y))}\,dy.
\]

Thus local Krein–Kantorovich transport now couples the literal global prime and
polar pairings to actual global Chebyshev work. No unresolved convergence or
boundary interface remains in this scalar theorem.

## Dependency-closed proof

**Common support.** Compact autocorrelation support supplies D. Since
exp D≤ceil(exp D)<ceil(exp D)+2, the logarithmic endpoint L₀ is strictly beyond D.
For x≥L₀ and y∈[a,a+d], positivity of a implies x+y≥L₀, so h(x+y)=0. Its annular
integral H(x) vanishes. Both source values defining V(x) vanish as well. This
proves (11) uniformly over all annular parameters. Larger integer cutoffs preserve
all three zero tails by monotonicity of log(N+2).

**Absolute atom admission.** If n>N+2 and N≥N₀, then log n≥log(N+2)≥L₀. Therefore
h(log n)=H(log n)=0. Only the finitely many atoms 2≤n≤N+2 can contribute. The
series and their absolute-value series are finite sums, with the actual von
Mangoldt weights retained at every surviving node.

**Polar admission.** Both polar integrands are continuous on [0,L₀] and vanish
on the remaining positive half-line. Compact-window integrability plus the zero
tail proves half-line integrability and equality of the full and truncated
integrals. No argument relies solely on the convention for a totalized integral.

**Work admission.** The kernels q(x)=exp(−x/2)(V−H/2) and s(x)=exp(−x/2)H are
continuous and vanish for x≥L₀. On [0,L₀], the actual Chebyshev function is a finite
step sum: ψ(exp x)=Σ_{n≤N₀+2}Λ(n)1_{log n≤x}. Hence qE is integrable on this
compact interval, using the previously proved finite-step admission theorem.
The zero tail extends integrability to the half-line. The same argument applies
to s directly by continuity. Both full work integrals equal their truncations.

**Exact arithmetic identity.** Apply the verified finite-window Stieltjes identity
to H at N₀. Its upper boundary exp(−L₀/2)H(L₀)E(L₀) is zero by (11). Replace the
finite atom sum and all truncated integrals by their admitted full values to get
(10). This argument uses no asymptotic estimate for E.

**Signed transport.** For any N=N₀+K, replace the scalar pairing and work in the
verified finite-window signed packet bounds by their stabilized full values.
Their right sides still use the actual finite packet Q_N. This gives (12) and
its square-root version. The inverse weight remains exactly exp(−y/2)sinh y;
it is bounded by y exp(y/2), as established in Pillar XV. Every annular integral
is finite since a>0. The zero source is included without a separate hypothesis.

## Scope and significance

This is one domain-closure contribution: the infinite scalar pairing, all admission
proofs, a common source cutoff, the global Stieltjes identity, and its transport
corollaries count together. It discharges the global convergence and endpoint
obligations left by the two finite-window packages.

The global scalar pairing stabilizes. **The packet norm is not claimed to
stabilize.** Distant translates can still contribute to Q_N even when h(log n)=0.
Each K gives a legitimate bound, without monotonicity or a uniform estimate for
Q_N. No infinite signed source packet or arithmetic cancellation asymptotic is
assumed or proved here.

Formal leaves: `SignedPrimePolarHalfLineDomain.lean` and
`SignedPrimePolarHalfLineTransport.lean`. Both pass direct
`lake --old env lean <leaf> -o <leaf.olean>` without diagnostics. Seven endpoint
axiom audits use only propext, Classical.choice, and Quot.sound; printed main
signatures contain no additional hypotheses. Both leaves are wired into the
field umbrella. Current repository lint status is recorded in the facts ledger.
