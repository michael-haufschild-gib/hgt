# THIM: complete absorption and compensated horizon estimates

- **ID:** thim-review1910-complete-absorption
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** docs/reports/review-1910/astra.md, §5 (T1–T4)
- **Statement:** Determine the feasible region of literal cosh/sinh absorption and the exact compensated replacement, on a source class preserved through finite-horizon localization.

## Scope and completion requirements

1. **T1 — source class:** Choose the actual odd theta-profile branch; prove its closure under the localizations consumed by the argument. Track its origin, parity, support and mass. Restricted Fermi inverses are not used without a source-class theorem.
2. **T2 — complete horizon estimate:** Retain archimedean, same-side prime, reflected crossing, collar and cosh-mass terms in one finite-horizon estimate. Identify every loss before taking a limit. No Nyman approximation claim without bulk and origin convergence.
3. **T3 — feasibility:** Audit `coshSinhPolarRatio` with its literal derivative bound. Determine whether replacing the endpoint bound by integration permits uniform unit absorption.
4. **T4 — compensation:** Preserve the reflected-prime compensation and identify a quantitative replacement for any failed absorption mechanism.

## Research plan

- [x] Read review, program interfaces and relevant prior research.
- [ ] Audit external parent theories and exact internal statements.
- [ ] State and attack exact conjectures; distinguish new obstruction from standard localization machinery.
- [ ] Complete dependency-closed paper proofs for surviving claims.
- [ ] Formalize exact statements without unproved analytic premises or added axioms.
- [ ] Audit each leaf with `lake --old env lean`, audit axioms from `/tmp`, wire umbrella, regenerate index, run lint.
- [ ] Check T1–T4 against current evidence; keep unfinished requirements explicit.

## Candidate mechanism

For `m_a(x) = oddProfile a x`, the literal quotient is

\[
q_a(x)=\frac{m_a(x)\cosh(x/2)}{\Theta(x)\sinh(x/2)},\qquad x>0.
\]

The mass-to-potential ratio for a nonzero even compact profile is the weighted average of `q_a`. The endpoint derivative bound is only a sufficient majorant. Candidate: localization forces the optimal universal integrated constant to retain the large-radius growth of `q_a`; hence an integrated estimate alone cannot repair unit absorption. The survivor must retain the exact excess potential alongside the positive compensated crossing energy.

## Exact conjecture and preliminary attack

Write `b = log(2)/2`. For `0 < a ≤ b` and `x ≥ log(2)`, conjecture

\[
q_a(x)\ge \pi\exp(2x-5\log(2)/4)>1.
\]

Consequently no legitimate derivative bound can make `coshSinhPolarRatio a M R ≤ 1` once `R ≥ log(2)`, even if `a` and `M` vary with `R`. Every nonzero even smooth test supported in `|x| ≥ L ≥ log(2)` has mass-to-sinh-potential ratio at least the same exponential bound at `L`. Integration does not repair the obstruction on this source class.

**Verdict: SURVIVES PRELIMINARY ATTACK.** The kernel slope estimate is prior corpus work; localization and multiplication-operator norm principles are classical. The proposed contribution is their explicit uniform consequence for the literal THIM absorption problem, not a new ground-state theory. No scientific-priority claim is established by missing search hits.

## Paper proof: quantitative obstruction [PROVED HERE]

The corpus proves `Θ(u)-Θ(v) ≥ π exp(2u) Θ(v)(v-u)` for `b ≤ u ≤ v`, and `Θ` is positive and decreasing on the positive half-line. Apply this with `u=x-a`, `v=x`; discard only the nonnegative difference `Θ(x)-Θ(x+a)`. Then

\[
 m_a(x)\ge \frac{\pi a\exp(2(x-a))}{2\sinh(a/2)}\Theta(x).
\]

The elementary inequality `exp(-a) ≥ 1-a`, multiplied by `exp(a/2)`, gives `2 sinh(a/2) ≤ a exp(a/2)`. All divisors are positive, hence

\[
 \frac{m_a(x)}{\Theta(x)}\ge \pi\exp(2x-5a/2).
\]

For positive `x`, `cosh(x/2) > sinh(x/2) > 0`, giving the same lower bound for `q_a(x)`. If `a ≤ b` and `x ≥ 2b`, the tail hypothesis holds and `2x-5a/2 ≥ 2x-5log(2)/4 ≥ 0`; therefore the bound is at least `π > 1`. The existing pointwise majorization at `x=R` implies the identical lower bound for the derivative-based coefficient.

For an even compact continuous profile `w`, let `P_a(w)=2∫_{x>0}m_a(x)sinh(x/2)w(x)^2 dx` and `C_a(w)=phiDoobCoshMass((oddPolarWeight a w)^2)`. The existing half-line mass identity gives `C_a(w)=2∫_{x>0}m_a(x)oddPolarFunction(a,x)cosh(x/2)w(x)^2 dx`. If `w` vanishes for `0<x<L`, multiply the pointwise lower bound by the nonnegative weight and integrate. This proves `C_a(w) ≥ π exp(2L-5log(2)/4) P_a(w)`. For a nonzero even continuous `w` supported outside positive `L`, continuity gives an interval of positive integrand and thus `P_a(w)>0`. Nonzero smooth paired bumps in any outer annulus exist independently of any zeta-zero information.

## External parent-theory audit

- Frank–Seiringer, *Non-linear ground state representations and sharp Hardy inequalities*, [arXiv:0803.0503](https://arxiv.org/abs/0803.0503): nonlocal ground-state substitution and remainder terms are established mathematics, not novelty here.
- Frank–Lenz–Wingert, *Intrinsic metrics for non-local symmetric Dirichlet forms and applications to spectral theory*, [arXiv:1012.5050](https://arxiv.org/abs/1012.5050): general Dirichlet-form machinery does not discharge the literal signed reflected-prime estimate.
- Csordas, *Fourier transforms of positive definite kernels and the Riemann ξ-function*, [DOI:10.1007/s40315-014-0105-8](https://doi.org/10.1007/s40315-014-0105-8), and Coffey–Csordas, *On the log-concavity of a Jacobi theta function*, [DOI:10.1090/S0025-5718-2013-02681-6](https://doi.org/10.1090/S0025-5718-2013-02681-6): kernel shape theory is prior work. The recent [second-level concavity preprint](https://arxiv.org/abs/2608.19160) concerns a different Laguerre expression; it is not an input to this proof.

## Positive survivor: concentration and the minimal local repair [PROVED HERE]

Define `K(L)=π exp(2L-5log(2)/4)` and
`P_tail(L,w)=2∫_{x>L}m_a(x)sinh(x/2)w(x)^2 dx`.
The preceding pointwise proof, with the nonnegative cosh-mass integral on `(0,L]` retained, gives the unconditional quantitative confinement law

\[
K(L)P_{\rm tail}(L,w)\le C_a(w),\qquad L\ge\log 2.
\]

Thus any family whose cosh mass is bounded has uniformly exponentially small sinh-potential tails. If an absorption inequality `C_a(w)≤θP_a(w)` is independently true for a restricted family, its normalized tail satisfies `P_tail/P ≤ θ/K(L)`. This is a necessary localization law, not an assertion that an arithmetic family satisfies absorption.

For the complete replacement set

\[
d_{a,\theta}(x)=\Theta(x)\psi_a(x)^2\cosh(x/2)
 -\theta m_a(x)\sinh(x/2),\quad \psi_a=m_a/\Theta,
\qquad D_\pm(w)=\int_{\mathbb R}(\pm d_{a,\theta})_+w^2.
\]

These are continuous even densities; compact support of `w` makes every integral finite. The pointwise identity `d=d_+-(-d)_+` yields `C_a(w)-θP_a(w)=D_+(w)-D_-(w)`. Insert it into the existing complete Doob identity:

\[
E(m_aw)+\theta P_a(w)+D_+(w)
=A(\psi_aw)+2S(\psi_aw)+\mathcal C(\psi_aw)+D_-(w).
\]

`A` is the original archimedean jump energy, `S` the same-side prime term, and `𝒞` the complete compensated reflected-prime series, equivalently the divisor-chain sum. All four right-side terms are nonnegative. No mean, collar, prime tail, endpoint or cosh subtraction is discarded. This supplies a complete finite-horizon lower estimate with a finite explicit local correction; it does not prove that correction is paid by the original energy.

The correction is minimal among continuous nonnegative multiplication densities: if `h≥0` and `C_a(w)≤θP_a(w)+∫h w²` for every even smooth compact profile, localize a paired bump near any positive `x`; negativity of `h-d` there contradicts the inequality. Hence `h≥d_+` (for even `h`; otherwise its even part is the observable density). Conversely `h≥d_+` gives the inequality by pointwise integration. This classification identifies the exact cost a replacement nonlocal coercivity argument must pay.

**[OPEN CORE]:** Formalize the obstruction, confinement law and minimal local repair. Full uncompensated odd positivity remains outside the proved result.

## Canonical growing-horizon family: paper proof [PROVED HERE]

The local repair alone leaves its cost unpaid. For a concrete positive survivor use the
existing full-graph theta translates, rather than asserting absorption. Let `χ_n` be the
corpus smooth even cutoff, equal to one on `|x|≤n+1`, zero on `|x|≥2(n+1)`, and with
Lipschitz constant `C/(n+1)`. Put `h_n=Θχ_n` and

\[
f_{a,n}(x)=\frac{h_n(x-a)-h_n(x+a)}{2\sinh(a/2)}.
\]

For `0<|a|<log(2)/2`, these are actual smooth compact odd tests, hence have mean zero.
Their support lies within `|x|<2(n+1)+|a|`; they equal `m_a` wherever
`|x|+|a|≤n+1`. Thus both moving endpoints are explicit. They converge to the
already-constructed odd polar vector `q_a` in the complete arithmetic graph.
No Nyman or unrestricted primitive approximation statement is claimed.

Write `c=(2sinh(a/2))⁻¹`, `D₂=∫t² dκ(t,x)` for the **entire** archimedean-plus-prime
edge measure, and

\[
J_n=\frac{C^2D_2}{(n+1)^2},\qquad
U_{a,n}=\int \Theta(x)\cosh(x/2)
 \left[\frac{\Theta(x-a)}{\Theta(x)}(\chi_n(x-a)-1)\right]^2 dx.
\]

`D₂` is finite by the corpus full displacement theorem. `U_{a,n}` is finite by
the actual translated-theta mass admission; its integrand vanishes on
`|x-a|≤n+1`. The cutoff slope bounds the complete edge error by `J_n`.
Translation invariance preserves **signed** difference energies. Passing one
index to the existing strong graph limit gives

\[
E(A_{a,n}-A_a)=E(\chi_n-1),\qquad
\|A_{a,n}-A_a\|_G^2
=E(\chi_n-1)+2U_{a,n}\le J_n+2U_{a,n}.
\]

Here `A` denotes the literal inverse-Doob translated source in the graph, not a
replacement norm. For `p_{a,n}=c(A_{a,n}-A_{-a,n})`, the parallelogram inequality gives

\[
\|p_{a,n}-q_a\|_G^2\le H_{a,n}
:=4c^2(J_n+U_{a,n}+U_{-a,n}).
\]

The signed pairing is `B(p,q)=〈Dp,Dq〉−〈p,q〉`, so Cauchy–Schwarz in the two
graph coordinates gives `|B(p,q)|≤‖p‖_G‖q‖_G`. Since the previously proved exact
identity is `E(q_a)=1/2`, polarization yields the complete finite-horizon estimate

\[
\left|E(f_{a,n})-\tfrac12\right|
\le \sqrt{H_{a,n}}\bigl(2\|q_a\|_G+\sqrt{H_{a,n}}\bigr).
\]

Both `U` terms tend to zero by admitted source convergence, and `J_n→0`.
Consequently the right side tends to zero and `E(f_{a,n})>1/4` eventually.
The complete compensated chain identity applies to each `f_{a,n}/Θ`, retaining
its cosh mass and reflected collar. This is a bound on one explicit growing-support
source family, not coercivity on all odd tests. Its cutoff error accounting is the
new specialization; graph density and the exact polar energy are prior corpus work.

### Primitive paired shifts and a stronger error order [PROVED HERE]

Ordinary mean zero does **not** mean both polar moments vanish. In fact
`coshHalfMoment(f_{a,n})=0`, while
`sinhHalfMoment(f_{a,n})=coshHalfMoment(h_n)` for every nonzero `a`.
The translation formulas prove this exactly, without a limit. Therefore the
shared-cutoff difference `g_{a,b,n}=f_{a,n}-f_{b,n}` is primitive at every horizon:
both hyperbolic moments vanish. Independent cutoffs would lose this cancellation.

Its graph limit is `r_{a,b}=q_a-q_b`, already proved to lie in the signed radical.
This removes the linear error term, not just the limiting energy. For the
graph error `e_n=g_{a,b,n}-r_{a,b}`, polarization gives `E(g_{a,b,n})=E(e_n)`.
Consequently

\[
|E(g_{a,b,n})|\le \|e_n\|_G^2
\le 2(H_{a,n}+H_{b,n})\longrightarrow0.
\]

**Conjecture audit:** SURVIVES. This stronger statement is forced by the existing
exact radical pairing, not by positivity or a new analytic premise. The source is
the same four translated theta cutoffs on both sides of the estimate. The corpus
already proves infinite linear independence of the corresponding limiting odd
critical sequence; this family is not merely the zero test. The contribution is
the complete finite-horizon error and exact moment-preserving cutoff prescription.
No density claim for the full primitive sector follows.

## Verification constraints

No numerical experiments, full builds, umbrella builds, heartbeat increases, commits or changes to other agents' work. One owned foreground Lean process at a time. Standard domain/range conditions are stated explicitly; no desired analytic bound is assumed. `update_plan` is unavailable in this session, so this card tracks the plan. Serena supports only Python here; Lean symbol calls fail, requiring source reads and patches.
