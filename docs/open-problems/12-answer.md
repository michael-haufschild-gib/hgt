I read the file. The requested statement is the a.e. “arbitrarily small low-crossing radius” claim for harmonic measure on a quasicircle, with the dynamical quadratic main-cardioid case allowed as a complete solution. The file defines the crossing count (N_p(t)=#(J\cap \partial B(p,t))) and asks to prove that for (\mu)-a.e. (p\in J), every (\varepsilon>0) contains some (0<t<\varepsilon) with (N_p(t)\le 3).  It also notes that the dynamical case has expansion, Gibbs/Brolin measure, and bounded distortion of inverse branches.

I cannot honestly give a complete proof of that statement from the material in the file. The natural symbolic/ergodic strategy reduces the problem to one finite “clean block” lemma, but that lemma is not supplied by the hypotheses and is exactly the nontrivial missing point. Below is the rigorous reduction; it shows precisely what would finish the proof, and where the proof attempt currently stops.

## Conditional theorem for the dynamical subclass

Let (f=f_c(z)=z^2+c), with (c\ne 0) in the open main cardioid. Let (J=J_c), (K=K_c), and let (\mu) be the Brolin/harmonic measure. Suppose the following clean-block hypothesis holds.

**Clean-block hypothesis.** There are constants
[
0<a<b<\infty,\qquad \eta>0,
]
and a cylinder set (C\subset J) of positive (\mu)-measure such that for every (q\in C) there is some radius
[
a\le r(q)\le b
]
with the following robust property: every sufficiently small (C^1)-perturbation of the normalized local picture around (q) still has a radius in ([a-\eta,b+\eta]) whose centered circle meets the perturbed boundary in at most three points.

Then the desired conclusion follows: for (\mu)-a.e. (p\in J), and for every (\varepsilon>0), there is (0<t<\varepsilon) with
[
N_p(t)\le 3.
]

### Proof under the clean-block hypothesis

The map (f|_J) is topologically conjugate to the doubling map on the circle. In the main-cardioid case, (f) is uniformly expanding on (J), and (\mu) is the invariant ergodic Brolin measure. Therefore every positive-(\mu) cylinder (C) is visited infinitely often by (f^n(p)) for (\mu)-a.e. (p), by Poincaré recurrence and ergodicity.

Fix such a typical point (p). Then there are infinitely many integers (n_k\to\infty) with
[
q_k:=f^{n_k}(p)\in C.
]

Because (f) is hyperbolic on (J), there is a neighborhood (U\supset J) on which inverse branches of (f^n) along admissible itineraries are defined and uniformly contracting. Let
[
g_k
]
be the inverse branch of (f^{n_k}) sending (q_k) back to (p). Koebe distortion gives uniform bounded distortion for the maps (g_k), and after rescaling by (|g_k'(q_k)|^{-1}), the maps are uniformly close to affine on a fixed small disk, provided the target clean block is chosen inside a sufficiently small dynamical chart.

For each (q_k\in C), the clean-block hypothesis gives a radius (r_k\in[a,b]) such that
[
#\bigl(J\cap \partial B(q_k,r_k)\bigr)\le 3
]
in the normalized picture, robustly under the inverse-branch distortion. Pulling the picture back by (g_k), the radius becomes
[
t_k \asymp |g_k'(q_k)|, r_k.
]
Uniform expansion implies (|g_k'(q_k)|\to 0), hence
[
t_k\to 0.
]
By the robustness clause, for each large (k) there is an actual Euclidean radius (\tilde t_k) centered at (p), comparable to (t_k), such that
[
N_p(\tilde t_k)\le 3.
]
Since (\tilde t_k\to 0), for every (\varepsilon>0) one can choose (k) with (0<\tilde t_k<\varepsilon). This proves the desired conclusion under the clean-block hypothesis. (\square)

## Why this is not yet a full proof

The reduction above is standard in expanding one-dimensional dynamics: a positive-probability finite block recurs infinitely often along almost every symbolic itinerary, and bounded distortion transfers the corresponding Euclidean picture to arbitrarily small scales.

The missing step is exactly the one flagged in the file’s suggested route: one must exhibit “one clean block with positive Gibbs probability.” The file explicitly identifies this as the work to be done: bounded-distortion dictionary plus a clean block, for example near the (\beta)-fixed point.

I do not see a rigorous way to prove that clean block from the stated assumptions alone. The difficulty is that a quasicircle, even a dynamically generated one, may have local radial oscillations: for a point (p), the two one-sided local arcs of (J) can in principle leave and re-enter centered circles many times. Bounded turning prevents arbitrarily thin detours, but it does not by itself force a radius with only two or three crossings. This is exactly why the rectifiable coarea proof in the file does not extend to the nonrectifiable main-cardioid Julia curves.

So the honest status is:

[
\boxed{\text{The dynamical proof is complete once the finite clean-block lemma is proved.}}
]

But I cannot supply that lemma rigorously from the file’s hypotheses, and without it the requested full proof would have a real gap.

---

# Verification report (2026-07-02)

**Verdict: the conditional reduction is VERIFIED; the problem now hangs, certified
from two independent derivations, on a single finite statement — the clean-block
(clean-window) lemma.**

1. **Recurrence step** — sound: a positive-`μ` cylinder is visited infinitely often by
   `μ`-a.e. orbit (ergodicity/Birkhoff), and hyperbolicity gives well-defined inverse
   branches with Koebe-bounded distortion along the returns.
2. **Transport step** — sound, with one bookkeeping point that the write-up glosses
   but which does work: the circles `∂B(p,t)` in the transported band must have ALL
   their `J`-crossings inside the inverse-branch chart (arranged by taking the band
   small relative to the chart via Koebe ¼); then `f^{n_k}` bijects the crossing set
   onto the crossings of a NEAR-ROUND curve at `q_k`. This is exactly why the
   hypothesis must be robust for nearly-round curves, not just round circles — the
   "C¹-perturbation" clause is the right shape, and since Koebe distortion tends to
   `1` as the chart shrinks, the required roundness tolerance can be made arbitrarily
   small before the lemma is invoked.
3. **The admitted gap is genuine and well-diagnosed**: bounded turning does not force
   a low-crossing radius, which is precisely why the rectifiable-case proof does not
   extend.

**Two additions from the audit.**

- At the β fixed point the linearized local picture is two logarithmic-spiral arms
  (multiplier `2β`, non-real for non-real cardioid `c`); along a logarithmic spiral
  the modulus is strictly monotone, so each arm crosses every centered circle exactly
  once: `N_β(t) = 2` in the linear model, at every scale. The clean-block lemma is
  thus plausibly available in cylinders shadowing `β` (long `0`-blocks), and its
  entire content is that the fractal decoration of the arms adds no crossings in SOME
  band — which is what the numerical clean bands show.
- The clean-block statement is a FINITE verification: a compact family of pictures in
  one fixed scale window. A certified computer-assisted proof (interval arithmetic
  through the Böttcher parametrization, with the distortion constants made explicit)
  is a fully legitimate route.

The residual is restated as a new self-contained problem document
(`13-clean-window-lemma.md`), per the series' convention that answered/reduced
problem files stay frozen.
