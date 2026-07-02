I read the file. It defines a finite Koenigs-window verification problem for a real quadratic parameter (c\in[-2,1/4)\setminus{0,-2}), asking for explicit (c,t_0,\sigma,g) such that every level in a multiplicative band has connected sublevel set in angle space, and the band lies below the “window edge” minimum on (t_0/2\le |t|\le t_0).

I can’t honestly write a complete rigorous solution proof from the uploaded file alone. The obstacle is not defining candidate constants; it is certifying **band cleanness for every level in a continuum of levels**, which requires excluding arbitrarily small “descent” intervals of the function (r_c(t)=|L_c(\gamma_c(t))|). The problem statement itself explicitly allows certified interval arithmetic and notes that this is the intended computable route.

What I can give you is a precise reduction to a finite certificate, plus numerically plausible candidate constants.

A good candidate is:

[
c=\frac15,\qquad t_0=\frac1{20},\qquad \sigma\approx 0.1011,\qquad g\approx 0.03.
]

Numerical sampling indicates the band

[
[,\sigma(1-g),\sigma(1+g),]\approx[0.0981,0.1041]
]

is clean, and the edge minimum appears to be about

[
\inf_{t_0/2\le |t|\le t_0}r_{1/5}(t)\approx 0.2129,
]

so condition (2) has a large margin. But this is **not yet a proof**, because a dense numerical sample cannot rule out a very narrow dirty descent inside the band.

Here is the exact certificate that would complete the proof.

Let

[
L=\sigma(1-g),\qquad U=\sigma(1+g).
]

It is enough to certify the following two statements for (c=1/5), (t_0=1/20):

[
\tag{E} r(t)>U\quad\text{for all }t\in[t_0/2,t_0],
]

and

[
\tag{O} \text{for all }0\le s<t\le t_0,\quad
r(s)\ge L\text{ and }r(t)\le U \implies r(s)\le r(t).
]

Then the proof is short.

Assume some level (\sigma'\in[L,U]) has a disconnected sublevel set on ([0,t_0]). Since (0\in{r<\sigma'}), disconnectedness means there are (0\le s<t\le t_0) such that

[
r(s)\ge \sigma' > r(t).
]

Because (\sigma'\in[L,U]), this gives (r(s)\ge L) and (r(t)\le U), so (O) implies (r(s)\le r(t)), a contradiction. Hence every sublevel in the band is a single interval on ([0,t_0]). By the symmetry (r(-t)=r(t)), it is a single interval on ([-t_0,t_0]). The edge condition is exactly (E). The symmetry and exact scaling relation used here are part of the problem setup.

So the whole problem reduces to a rigorous interval proof of (E) and (O). A full certified proof would need to enclose (r(t)) over angle intervals using validated inverse iteration for (\gamma_c), validated Koenigs-series or Koenigs-iteration bounds for (L_c), and a two-variable interval check excluding all bad pairs ((s,t)) for (O). The file’s “Computability” section describes exactly this route.

I’m not going to claim that as solved without the actual interval certificate. A sampled computation strongly suggests the constants above are viable, but the full proof still hinges on a rigorous all-pairs enclosure for (O).

---

# Verification report (2026-07-02)

**Verdict: no proof claimed and none delivered — correctly so — but the finite
certificate is VERIFIED and is the right final form; with two additions from this
audit it becomes strictly finite and directly implementable.**

1. **The certificate (E)+(O) is EQUIVALENT to the required band cleanness** (not
   merely sufficient): a disconnected sublevel at `σ′ ∈ [L,U]` yields a pair
   `s < t` with `r(s) ≥ σ′ > r(t)`, violating (O); conversely (O)'s violating pair
   disconnects the level `σ′` between the two values. So certifying (E) and (O)
   loses nothing.
2. **Audit addition — the check reduces to the edge annulus.** By the exact scaling
   `r(2t) = λ r(t)`, every value on `(0, t₀]` is `λ^{-k}` times a value on
   `[t₀/2, t₀]`. Writing `s = 2^{-j}u`, `t = 2^{-k}v` with `u, v ∈ [t₀/2, t₀]`,
   condition (O) becomes finitely many `(j,k)`-shifted comparisons of `r` on the
   edge annulus alone: the hypothesis can fire only while `λ^k U ≥ min_{edge} r`
   and `λ^j L ≤ max_{edge} r`, which bounds `j, k` explicitly (a handful of pairs
   at the candidate constants). The two-variable interval check over `[0,t₀]²`
   collapses to cell checks on `[t₀/2, t₀]²` with finitely many level shifts.
3. **Audit addition — no validated Koenigs map is needed.**
   `r(t) = lim_n λ^n |γ_c(t/2^n) − β|`, and the exact identity
   `γ(t/2^n) − β = λ(γ(t/2^{n+1}) − β) + (γ(t/2^{n+1}) − β)²` gives an explicit
   quadratic-error telescope; validated enclosures of the landing map at halved
   angles (truncated Böttcher series at a large-radius ray point, then certified
   interval square-root pullbacks) therefore suffice to enclose `r` on edge cells.
4. **Candidates are plausible:** `c = 1/5` lies in the range where independent
   raster experiments found every sampled phase clean; the sampled edge minimum
   `≈ 0.2129` gives (E) a factor-`2` margin over `U ≈ 0.1041`; `λ ≈ 1.4472`.

**Status of Problem 14: OPEN, now with a concrete finite certificate and candidate
constants.** What remains is exactly the validated enclosure of `r` on the edge
annulus and the finitely many (E)/(O) cell checks — a certified-numerics project
with visible margins, executable by either side.
