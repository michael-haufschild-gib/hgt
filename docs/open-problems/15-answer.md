I read the repaired file. The earlier vacuous solution is no longer valid: the repaired statement explicitly adds the cap (b\le 1/4) to prevent choosing a scale band far outside the Julia set . The actual deliverable is now an explicit non-vacuous clean window with (0<a<b\le 1/4), (\delta>0), and (\eta\le 1/10), such that **every** nearby center, scale, and nearly-round curve has at most three intersections with (J_c) .

I should not pretend to have a complete proof of this repaired statement. The repaired version is exactly the substantive finite certification problem described in the file: one may solve it by interval arithmetic or another certified enclosure method, but the proof must include explicit constants and a verified crossing count . I do not have that missing certified enclosure in hand, so giving a numerical-looking “solution” would not be rigorous.

What I can give is the clean reduction that any successful proof would need. It is short, rigorous, and isolates the finite certificate required.

## Certified clean-window criterion

Fix a main-cardioid parameter (c), a point (q\in J_c), constants

[
0<a<b\le \frac14,\qquad \delta>0,\qquad 0<\eta\le \frac1{10}.
]

For (x\in J_c\cap B(q,\delta)), write polar coordinates around (x):

[
z=x+\rho e^{i\theta}.
]

Suppose the following three properties have been certified.

### Certificate hypotheses

There is a closed annular neighborhood

[
A_x={z: a(1-\eta)\le |z-x|\le b(1+\eta)}
]

such that, for every (x\in J_c\cap B(q,\delta)),

[
J_c\cap A_x
]

is contained in the union of two compact arcs

[
P_x^+,\ P_x^-.
]

On each arc (P_x^\pm), the polar angle (\theta) is injective, so the arc can be written as a radial graph

[
\rho=\rho_x^\pm(\theta).
]

Finally, assume the following uniform radial monotonicity estimate holds: for some (m>0),

[
|\rho_x^\pm(\theta_2)-\rho_x^\pm(\theta_1)|
\ge m|\theta_2-\theta_1|
]

whenever (\theta_1,\theta_2) lie in the same angular interval of the same arc, and assume

[
\eta b<m.
]

Then the required clean-window conclusion follows.

## Proof of the criterion

Let

[
x\in J_c\cap B(q,\delta),\qquad s\in[a,b],
]

and let (\Gamma) be an ((x,s,\eta))-round curve. By definition,

[
\Gamma={x+R(\theta)e^{i\theta}:\theta\in[0,2\pi)},
]

where

[
|R(\theta)-s|\le \eta s,\qquad |R'(\theta)|\le \eta s.
]

Therefore every point of (\Gamma) lies in the annulus

[
s(1-\eta)\le |z-x|\le s(1+\eta).
]

Since (s\in[a,b]), this annulus is contained in

[
a(1-\eta)\le |z-x|\le b(1+\eta).
]

Hence

[
J_c\cap \Gamma
\subset
(J_c\cap A_x)
\subset
P_x^+\cup P_x^-.
]

It remains to show that (\Gamma) meets each of (P_x^+) and (P_x^-) at most once.

Assume, for contradiction, that (\Gamma) meets one of the two arcs, say (P_x^+), in two distinct points. Since (P_x^+) is a polar graph, these points have distinct angles (\theta_1\ne\theta_2), and

[
\rho_x^+(\theta_i)=R(\theta_i),\qquad i=1,2.
]

Using the radial monotonicity certificate,

[
|\rho_x^+(\theta_2)-\rho_x^+(\theta_1)|
\ge m|\theta_2-\theta_1|.
]

But using the Lipschitz bound on (R),

[
|\rho_x^+(\theta_2)-\rho_x^+(\theta_1)|
=======================================

|R(\theta_2)-R(\theta_1)|
\le
\eta s|\theta_2-\theta_1|
\le
\eta b|\theta_2-\theta_1|.
]

Combining these inequalities gives

[
m|\theta_2-\theta_1|
\le
\eta b|\theta_2-\theta_1|.
]

Since (\theta_1\ne\theta_2), this implies

[
m\le \eta b,
]

contradicting the certificate assumption (\eta b<m).

Thus (\Gamma) meets (P_x^+) at most once. The same argument applies to (P_x^-). Therefore

[
#(J_c\cap \Gamma)
\le
#(\Gamma\cap P_x^+)+#(\Gamma\cap P_x^-)
\le 2.
]

In particular,

[
#(J_c\cap \Gamma)\le 3.
]

That proves the clean-window conclusion from the certificate.

## What remains to solve the repaired problem

A complete solution must now provide explicit

[
c,\ q,\ a,\ b,\ \delta,\ \eta
]

and prove the certificate hypotheses above. The file explicitly permits a certified computer-assisted proof, such as interval arithmetic with explicit constants , and the formal deliverable is either such explicit constants with proof or a proof that no such window exists for some main-cardioid (c) .

A plausible numerical target is

[
c=-\frac14,\qquad
q=\beta=\frac{1+\sqrt2}{2},
]

with a small band such as

[
a=\frac15,\qquad b=\frac{21}{100},
]

and very small (\delta,\eta). But without a certified enclosure proving the two-arc decomposition and the lower radial-slope bound, this is only a candidate, not a proof.

---

# Verification report (2026-07-02)

**Verdict: the criterion's proof is VERIFIED; its hypotheses are empirically
unsatisfiable; and fresh computations show the repaired problem's STATEMENT is
itself very likely false — the crossing-count formulation must be replaced.**

1. **The criterion is valid.** Reverse-Lipschitz radial graphs (`|Δρ| ≥ m|Δθ|`, two
   arcs) against the `ηs`-Lipschitz polar graphs of the curve family give at most
   one intersection per arc whenever `ηb < m`; the clash of the two Lipschitz bounds
   is correct, and the conclusion `≤ 2` is even stronger than asked.
2. **The hypotheses are empirically unsatisfiable.** Reverse-Lipschitz forces the
   arm's radius to be strictly monotone in polar angle at ALL scales inside the
   window. Direct computation (c = 1/5, Euclidean landing profile, error floor
   1e−14; `computations/op14_certificate/results.md`) finds real, saturating radial
   micro-dips at EVERY probed crossing of the arm (depths 5e−9 … 2.6e−5, stable to
   33M sample points). A dip breaks either monotonicity or the radial-graph
   property. The candidate `c = −1/4` was not computed, but the mechanism
   (decorations of the arm at all scales) is parameter-generic.
3. **The repaired statement itself appears FALSE, not merely uncertified.** A radial
   dip straddling radius `s` adds two crossings to every centered curve of that
   size, so `#(J_c ∩ Γ) ≥ 4` at dip-straddled sizes — and the computations indicate
   dips straddle essentially every size (every probed crossing carries one). This
   kills the crossing-count formulation as such, for every window. [Empirical:
   four sites probed at one parameter; stated as strong evidence, not proof.]
4. **What survives (new, from the same computations).** Whether a dip creates a
   PLANAR pocket depends on its chirality — the lens between dip and sphere lies on
   the Ω-side (pocket) or the K-side (harmless) — and chirality is coherent per
   decoration site, with both types occurring. Planar connectivity of `B(p,ρ) ∖ K`
   tolerates arbitrarily many K-side crossings; only Ω-side dips matter. The
   two-crossings⟹connected lemma was sufficient but far from necessary. The
   successor problems (for the pointwise β-gate and for the a.e. quasicircle gate)
   will be posed on the chirality invariant: a radius is clean iff no Ω-side dip
   straddles it; K-side verdicts are rigorously certifiable by interval escape,
   and the open mathematics becomes the coherence/classification of site chirality
   under the dynamics.
