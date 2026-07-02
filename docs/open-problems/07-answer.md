The universal statement is **false**. I will give a refutation in the allowed W3 form: for the basilica parameter
[
c=-1\in M\setminus{0,-2},
]
one has
[
\mu_{-1}(S_{-1})=0,
]
not (1). This directly refutes the proposed assertion, whose target was (\mu_c(S_c)=1) for every (c\in M\setminus{0,-2}), with (S_c) defined by strict ball-connectivity of (B(p,\rho)\setminus K_c).  This is exactly the kind of refutation allowed under W3.

## Theorem

Let
[
f(z)=z^2-1,\qquad K=K_{-1},\qquad J=J_{-1},\qquad \Omega=\widehat{\mathbb C}\setminus K.
]
Then
[
\mu_{-1}(S_{-1})=0.
]

Hence the problem’s full statement is false.

## Standard facts used

For the basilica (f(z)=z^2-1):

1. The critical orbit is
   [
   0\mapsto -1\mapsto 0,
   ]
   so (f) is hyperbolic. In particular, (J) is locally connected and (f) is uniformly expanding on (J).

2. The repelling fixed point
   [
   \alpha=\frac{1-\sqrt5}{2}
   ]
   is the common landing point of the two external rays of angles (1/3) and (2/3). These are distinct local accesses to (\alpha). This is the standard basilica ray portrait.

3. The Brolin/harmonic measure (\mu_{-1}) is invariant and ergodic, with support (J), as in the uploaded problem statement.

The dynamical facts above are classical; see Douady–Hubbard’s Orsay notes or Milnor, *Dynamics in One Complex Variable*, sections on the basilica and hyperbolic Julia sets.

---

## Proof

Write (\mu=\mu_{-1}). We prove that (S_{-1}) is contained in a Borel set of (\mu)-measure (0).

### 1. A fixed two-sided local obstruction near the basilica root

Let
[
\alpha=\frac{1-\sqrt5}{2}.
]
The two external rays (R_{1/3}) and (R_{2/3}) land at (\alpha), and they represent two distinct local accesses to (\Omega). Therefore there exists a sufficiently small (\rho>0) such that
[
B(\alpha,\rho)\cap \Omega
]
has at least two connected components whose closures contain (\alpha).

Choose two such components and call them (U_1,U_2). Since (\alpha\in\overline{U_i}), we may choose points
[
x_i\in U_i,\qquad i=1,2,
]
arbitrarily close to (\alpha).

We also choose (\rho>0) so small that
[
\overline{B(\alpha,\rho)}\cap{0,-1}=\varnothing.
]
This is possible because (\alpha\notin{0,-1}).

Fix a small constant (\tau>0), say (\tau=10^{-3}). Now choose numbers (R,\eta>0) with
[
0<\eta\ll R<\rho
]
so that

[
B(q,R)\subset B(\alpha,\rho)
]
whenever (q\in B(\alpha,\eta)), and so that the already chosen points (x_1,x_2) satisfy
[
|x_i-q|<\tau R
]
for every (q\in B(\alpha,\eta)).

Define the target set
[
Y:=J\cap B(\alpha,\eta).
]
Since (\alpha\in J) and (\operatorname{supp}\mu=J), we have
[
\mu(Y)>0.
]

Now fix (q\in Y). The points (x_1,x_2) lie in (B(q,R)\cap\Omega). If they could be joined by a curve inside (B(q,R)\cap\Omega), then, because
[
B(q,R)\subset B(\alpha,\rho),
]
they would also be joined inside (B(\alpha,\rho)\cap\Omega), contradicting that (x_1,x_2) lie in different components (U_1,U_2). Hence

[
B(q,R)\cap\Omega
]
is disconnected for every (q\in Y). Thus every point of (Y) has a uniform one-scale obstruction to strict one-sidedness.

### 2. Pulling the obstruction back along inverse branches

Let (p\in J), and suppose that for some (n\ge 0),
[
q=f^n(p)\in Y.
]
Because (B(q,R)\subset B(\alpha,\rho)) and (B(\alpha,\rho)) avoids the postcritical set ({0,-1}), the inverse branch of (f^n) sending (q) back to (p) is well-defined and univalent on (B(q,R)). Denote it by
[
g_n:B(q,R)\to\mathbb C,\qquad g_n(q)=p.
]

By Koebe’s one-quarter theorem,
[
B!\left(p,\frac14 |g_n'(q)|R\right)\subset g_n(B(q,R)).
]
Also, by the Koebe distortion theorem, because (x_i\in B(q,\tau R)) and (\tau) was chosen small, we have
[
|g_n(x_i)-p|<\frac18 |g_n'(q)|R,\qquad i=1,2.
]
Set
[
s_n:=\frac14 |g_n'(q)|R.
]
Then
[
g_n(x_1),g_n(x_2)\in B(p,s_n)\cap\Omega,
]
and
[
B(p,s_n)\subset g_n(B(q,R)).
]

Suppose, for contradiction, that
[
B(p,s_n)\cap\Omega
]
were connected. Then (g_n(x_1)) and (g_n(x_2)) could be joined by a curve inside (B(p,s_n)\cap\Omega). Applying (f^n), which is conformal and injective on (g_n(B(q,R))), would give a curve joining (x_1) to (x_2) inside
[
B(q,R)\cap\Omega.
]
But we proved above that (x_1,x_2) lie in different components of (B(q,R)\cap\Omega). Contradiction.

Therefore, whenever (f^n(p)\in Y), there is a radius
[
s_n=\frac14 |g_n'(f^n(p))|R
]
such that
[
B(p,s_n)\cap\Omega
]
is disconnected.

Since (f) is hyperbolic on (J), there exist constants (C>0) and (\lambda>1) such that
[
|(f^n)'(z)|\ge C\lambda^n
]
for all (z\in J). Hence
[
|g_n'(f^n(p))|
==============

\frac1{|(f^n)'(p)|}
\le C^{-1}\lambda^{-n}.
]
Thus
[
s_n\le \frac{R}{4C}\lambda^{-n}\to 0.
]

So every sufficiently late visit of the orbit of (p) to (Y) produces a disconnected ball (B(p,s_n)\cap\Omega) at an arbitrarily small scale.

### 3. Ergodicity gives infinitely many visits for almost every point

Because (\mu(Y)>0) and (\mu) is ergodic and (f)-invariant, Birkhoff’s ergodic theorem gives
[
\frac1N\sum_{n=0}^{N-1}\mathbf 1_Y(f^n(p))\to \mu(Y)>0
]
for (\mu)-almost every (p\in J).

Therefore, for (\mu)-almost every (p\in J), the orbit ({f^n(p)}_{n\ge0}) visits (Y) infinitely often.

For such a point (p), the preceding pullback argument gives a sequence (s_{n_j}\to0) such that
[
B(p,s_{n_j})\cap\Omega
]
is disconnected for every (j). Equivalently,
[
B(p,s_{n_j})\setminus K
]
is disconnected for arbitrarily small radii.

Thus (p\notin S_{-1}).

Let
[
T:={p\in J:\ f^n(p)\in Y\ \text{for infinitely many }n}.
]
Then (T) is Borel, (\mu(T)=1), and
[
T\cap S_{-1}=\varnothing.
]
Hence
[
S_{-1}\subset J\setminus T,
]
and therefore
[
\mu^*(S_{-1})=0.
]
In particular, if (S_{-1}) is measurable, then
[
\mu(S_{-1})=0.
]

This proves the claimed refutation.

[
\boxed{\mu_{-1}(S_{-1})=0.}
]

So the proposed full-measure statement is false.

---

# Verification report (2026-07-02)

**Verdict: VERIFIED — the refutation is correct and is accepted in the (W3) form.**
`μ_{−1}(S_{−1}) = 0` at the basilica `c = −1 ∈ M ∖ {0,−2}`; the universal full-measure
statement of Problem 7 is FALSE. Checked point by point:

1. **Step 1.** `α = (1−√5)/2` satisfies `α² − 1 = α`, multiplier `2α ≈ −1.236` repelling;
   the period-2 doubling cycle `{1/3, 2/3}` of rays lands at `α` (classical basilica
   portrait), and "number of accesses = number of rays at a repelling landing point" is
   Known Fact 3 of the parent Problem 6 file. Distinct accesses do force separation at a
   single scale `ρ`: choosing `x_i` on the *final* tails of the rays inside `B(α,ρ)`,
   joins at every scale would merge the accesses. `dist(α, {0,−1}) = 0.382…`, so `ρ`
   avoiding the closure of the postcritical set exists. The quantifier order is
   consistent: fix `x_i` within `τR/2` of `α`, then `η < τR/2` with `R < ρ − η`.
2. **Step 2.** The critical values of `fⁿ` lie in `{0,−1}`, avoided by `B(q,R)`, so the
   inverse branch `g_n` is univalent there. Koebe ¼ gives `B(p, s_n) ⊆ g_n(B(q,R))`
   with `s_n = ¼|g_n′(q)|R`; the growth theorem at `t = 10⁻³` gives distortion
   `≈ 0.001 < ⅛`, placing both pulled points in `B(p, s_n)`. The push-forward
   contradiction is sound: an open connected subset of `ℂ` is path-connected, `fⁿ` is
   conformal on the pulled ball, and full invariance of `K` keeps the curve in `Ω`.
3. **Steps 2–3.** The basilica is hyperbolic (superattracting cycle `0 ↔ −1`), so
   uniform expansion on `J` gives `s_n ≤ (R/4C)λ^{−n} → 0` along visit times — the
   expansion is genuinely used here. `μ(Y) > 0` since `Y` is a relatively open
   neighborhood of `α` in `supp μ = J`; Birkhoff gives infinitely many visits a.e.;
   `T` is Borel; the conclusion is correctly stated in outer measure (the Borel-hull
   phrasing the problem requested).

**Sharper than a counterexample.** `c = −1` is hyperbolic with locally connected `J` —
so the uniaccessible-vs-strictly-one-sided gap is not a comb pathology: at the
basilica, `μ`-a.e. point is uniaccessible (Zdunik-type a.e. accessibility) yet NOT
strictly one-sided. The mechanism: a.e. orbit shadows the pinch point `α` infinitely
often, and each visit imprints a disconnection scale by univalent pullback. This also
refutes the calibration conjecture in the problem file: Zdunik's smooth/singular
dichotomy does NOT govern `μ_c(S_c) = 1` — pinching governs. `[CONJECTURE]` The same
mechanism gives `μ_c(S_c) = 0` for every hyperbolic `c` outside the main cardioid
(some repelling (pre)periodic point carries ≥ 2 rays); for `c` in the main cardioid
`J_c` is a Jordan quasicircle with no cut points and the question `μ_c(S_c) = 1`
remains open (form (W2)) — as does the special-set form (W1).

**Programme consequences.**
- Every *measure-based* route to a strictly one-sided point is now permanently closed
  (positive measure cannot meet a possibly-null `S_{c₁}`); combined with the
  β-preimage no-go, `ExposedOneSided` must come from set-specific geometry.
- The measure-quantified rigidity variant (support-piece engine consuming
  `μ₁(∂W∖K₂) > 0` directly, never mentioning `S_c`) is promoted from hedge to the
  primary route for general pairs.
- For REAL pairs a direct pointwise route opens: with `β₂ < β₁`, the point `β₁` lies
  off `K_{c₂}` (since `K_{c₂} ∩ ℝ = [−β₂, β₂]`, already formalized) and is visible
  along the real ray `(β₁, ∞)`; the sole unproven clause is one-sidedness of the
  single point `β₁` — formalized as the conditional Lean brick
  `realPair_exposedOneSided_of_oneSidedAt_beta` (see the formal tree).
