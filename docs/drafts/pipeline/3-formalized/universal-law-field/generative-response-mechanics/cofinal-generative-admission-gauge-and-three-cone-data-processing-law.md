# Cofinal generative admission gauge and three-cone data-processing law

- **ID:** `ulf-grm-cofinal-generative-admission-gauge`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / ROUTE-INDEPENDENT MECHANISM
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [ROUTE-INDEPENDENT] [INFINITE/COFINAL]`
  `[LEAN-CLOSED] [TARGETED BUILD PASSED] [AXIOM AUDIT PASSED] [NOT RH]`
- **Active claim:** Finite positive-null response detects only the norm-closed contingent tangent
  cone. Actual one-sided source admission is controlled by a stricter negative-density gauge whose
  reciprocal is the exact perturbation radius and which contracts under every positive comparison.

## 1. Why the finite fusion theorem is insufficient

The finite generative-response theorem identifies legal source birth with nonnegative response on
every positive Gram null face. In a finite simplex this also produces a uniform positive parameter
`epsilon` for the straight perturbation `w+epsilon h`.

That implication fails cofinally. If every coordinate of an infinite positive carrier is nonzero,
all pointwise null tests are vacuous, yet negative relative velocities can diverge along the tail.
Every finite aperture then has a positive perturbation radius while the full carrier has none.

The missing structure is therefore not another null functional. It is the distinction among:

1. bounded-score hereditary tangents;
2. genuinely admitted radial tangents;
3. norm-limit/contingent tangents seen by continuous first-order observers.

## 2. Coordinate-free admission gauge

Let `V` be a real vector space with a convex cone `K`, let `w in K`, and let `h in V`. Define the
one-sided negative-density gauge

\[
\kappa_w(h)=\inf\{c\ge0:h+cw\in K\}\in[0,+\infty].
\tag{CAG.1}
\]

Define the straight-line admission radius by

\[
\rho_w(h)=\sup\{\epsilon\ge0:w+\epsilon h\in K\}.
\tag{CAG.2}
\]

Use the conventions `1/0=+infinity` and `1/(+infinity)=0`.
Infima and suprema are taken in the extended nonnegative reals. The empty feasible set in
`(CAG.1)` has infimum `+infinity`; `(CAG.2)` is never empty because `epsilon=0` is feasible.

### Theorem A — exact admission and data processing

For every cone as above:

\[
\boxed{\rho_w(h)=\kappa_w(h)^{-1}.}
\tag{CAG.3}
\]

If `A:V->W` is positive, meaning `A(K) subset L`, then

\[
\boxed{\kappa_{Aw}(Ah)\le\kappa_w(h),\qquad
       \rho_{Aw}(Ah)\ge\rho_w(h).}
\tag{CAG.4}
\]

For composable positive comparisons the inequalities compose. A positive observer may erase an
admission obstruction but cannot create one.

## 3. Exact `ell^1` model and three cones

Let `w,h in ell^1(N;R)`, assume `w_n>=0`, `sum w_n=1`, and `sum h_n=0`. Put

\[
\kappa_w(h)
=\sup_n\begin{cases}
(-h_n/w_n)_+,&w_n>0,\\
0,&w_n=0\text{ and }h_n\ge0,\\
+\infty,&w_n=0\text{ and }h_n<0.
\end{cases}
\tag{CAG.5}
\]

Define inside the mass-zero hyperplane:

\[
\begin{aligned}
\mathsf H_w&=\{wr:r\in\ell^\infty,\ \sum_nw_nr_n=0\},\\
\mathsf R_w&=\{h:\kappa_w(h)<\infty\},\\
\mathsf T_w&=\overline{\mathsf R_w}^{\ell^1}.
\end{aligned}
\tag{CAG.6}
\]

### Theorem B — three-cone classification

One has

\[
\boxed{\mathsf H_w\subseteq\mathsf R_w\subseteq\mathsf T_w
=\{h:\sum h_n=0,\ w_n=0\Rightarrow h_n\ge0\}.}
\tag{CAG.7}
\]

Moreover:

1. `h` is admitted in both directions iff `h=wr` for a bounded score `r`; equivalently
   `max(kappa_w(h),kappa_w(-h))<infinity`.
2. `h in R_w` iff one common positive `epsilon` makes `w+epsilon h>=0`.
3. `h in T_w` iff every positive finite-dimensional Gram null observer has nonnegative first
   response.
4. The inclusions can both be strict.

This claims that positive null geometry sees `T_w`, whereas actual source execution lives in
`R_w`. The gap `T_w\R_w` is the cofinal admission defect.

## 4. Reporter law

Let `phi_n in R^d` be bounded and let `a in R^d`. Define

\[
E_w(a)=\sum_nw_n\langle a,\phi_n\rangle^2,
\qquad
\dot E_h(a)=\sum_nh_n\langle a,\phi_n\rangle^2.
\tag{CAG.8}
\]

### Theorem C — observer/contingent equivalence

For mass-zero `h`, the following are equivalent:

1. `h in T_w`;
2. for every bounded finite-dimensional feature packet and every `a`,
   \[
   E_w(a)=0\Longrightarrow\dot E_h(a)\ge0.
   \tag{CAG.9}
   \]

The complete oscillatory reporter remains coefficient-faithful. If `lambda_n` are distinct and

\[
\widehat h(t)=\sum_nh_ne^{-it\lambda_n},
\tag{CAG.10}
\]

then `widehat h=0` on `R` implies `h=0`. Thus phase history reconstructs the tangent but does not
by itself bound `kappa_w(h)`.

## 5. Cofinal finite-aperture law

For an increasing exhaustion `F_N` of `N`, define

\[
\kappa_N=\max_{n\in F_N}(-h_n/w_n)_+,
\qquad \rho_N=\kappa_N^{-1},
\tag{CAG.11}
\]

with the zero-coordinate conventions of `(CAG.5)`.

### Theorem D — cofinal conservation

\[
\boxed{\kappa_N\uparrow\kappa_w(h),\qquad
       \rho_N\downarrow\rho_w(h).}
\tag{CAG.12}
\]

Consequently, finite positivity has global content exactly when the finite admission radii have a
strict positive lower bound.

## 6. Fourth-organ prediction: positive finite matrices with no global positive path

Take

\[
w_n=2^{-n-1},\qquad
h_0=1,\qquad h_n=-n2^{-n-1}\quad(n\ge1).
\tag{CAG.13}
\]

Then `w,h in ell^1`, `sum w=1`, `sum h=0`, and `w_n>0` for all `n`. Hence `h in T_w`. But

\[
\kappa_w(h)=\sup_{n\ge1}n=+\infty,
\qquad \rho_w(h)=0.
\tag{CAG.14}
\]

For the diagonal spectral/Gram aperture, with `N>=1`,

\[
G_N(\epsilon)=\operatorname{diag}_{0\le n\le N}(w_n+\epsilon h_n),
\tag{CAG.15}
\]

every finite matrix is positive definite for `0<=epsilon<1/N`, while no `epsilon>0` makes the
cofinal diagonal operator coordinatewise positive. Thus every finite positive-null test passes,
but the actual infinite straight history is not admitted.

This is the predicted theorem in the cofinal spectral/coercivity organ. It is not a restatement of
the finite Gram theorem: the new invariant is the lower envelope of perturbation radii.

## 7. Proof

### A. Coordinate-free gauge

For `epsilon>0`, conicity gives

\[
w+\epsilon h\in K
\Longleftrightarrow
h+\epsilon^{-1}w\in K.
\]

Taking the supremum on the left and the infimum on the right proves `(CAG.3)`. If
`h+cw in K` and `A` is positive, then `Ah+cAw in L`; taking infima proves `(CAG.4)`.
More explicitly, the feasible `c`-set is an upper ray because adding a nonnegative multiple of
`w` preserves `K`. Its reciprocal is exactly the positive feasible `epsilon`-set, with either
endpoint allowed or omitted simultaneously. This proves the extended-real endpoint cases as well.

### B. `ell^1` formula

The inequality `h+cw>=0` is coordinatewise. At `w_n>0` it is equivalent to
`c>=-h_n/w_n` whenever `h_n<0`. At `w_n=0` it is possible exactly when `h_n>=0`.
This proves `(CAG.5)`, the radial classification, and the two-sided bounded-score claim.
Indeed, two-sided finite gauge forces `h_n=0` wherever `w_n=0` and bounds both signs of
`h_n/w_n`; conversely a bounded score bounds both gauges.

### C. Closure of the radial cone

Necessity in `(CAG.7)` follows from continuity of each coordinate evaluation. For sufficiency,
assume `h_n>=0` on the zero set of `w` and define

\[
h_n^{(N)}=\max(h_n,-Nw_n).
\tag{CAG.16}
\]

Then `kappa_w(h^(N))<=N`. Also `h^(N)->h` in `ell^1`: the difference is dominated by the summable
negative part of `h` and converges coordinatewise to zero. Since truncating the negative part can
raise total mass, choose one index `j` with `w_j>0`, put `c_N=sum h^(N)`, and replace
`h^(N)` by `h^(N)-c_N e_j`. Here `c_N>=0` and `c_N->0`; the correction preserves finite gauge,
restores mass zero, and does not affect convergence. This proves `(CAG.7)`.

Both inclusions can be strict even when every `w_n` is positive. Take `w_n=2^{-n-1}`. The
mass-zero vector

\[
g_0=-1,\qquad g_n=n2^{-n-1}\quad(n\ge1)
\tag{CAG.17}
\]

has `kappa_w(g)=2`, hence lies in `R_w`, but `g_n/w_n=n` is unbounded, so it does not lie in
`H_w`. The vector `(CAG.13)` lies in `T_w` but not `R_w`, proving strictness of the second
inclusion.

### D. Null observers

If `E_w(a)=0`, every summand is nonnegative, so
`<a,phi_n>=0` whenever `w_n>0`. Therefore only zero-support coordinates remain in
`dot E_h(a)`, proving nonnegativity for `h in T_w`. Conversely, for any `n` with `w_n=0`, take the
one-dimensional coordinate feature `phi_m=1_(m=n)` and `a=1`. Then `(CAG.9)` says `h_n>=0`.
This proves Conjecture C except for the standard Fourier uniqueness sentence.

### E. Fourier uniqueness

The series `(CAG.10)` is the Fourier transform of the finite signed measure
`mu=sum h_n delta_(lambda_n)`. If its transform vanishes, convolving with every Gaussian has zero
Fourier transform and hence zero continuous density by Fourier inversion. Gaussian approximate
identities converge weakly to `mu`, so `mu=0`; distinct atoms imply every `h_n=0`.

### F. Cofinal radii and example

The finite maxima in `(CAG.11)` increase to the supremum in `(CAG.5)`, proving `(CAG.12)`.
The claim includes zero and infinite limits: reciprocal reverses monotone order continuously in
the extended nonnegative reals. Every exhaustion is assumed nested and to contain each index
eventually.
For `(CAG.13)`, the geometric-series identities give `sum w=1` and
`sum_(n>=1)n2^(-n-1)=1`, so `sum h=0`. The negative ratio is exactly `n`; equations
`(CAG.14)`--`(CAG.15)` follow.

## 8. Hostile conjecture loops

### Loop 1 — null observers characterize actual admission

**FALSIFIED by `(CAG.13)`.** They characterize only the closure `T_w`.

**Stronger survivor:** retain the radial gauge `kappa` in addition to the null-observer cone.

### Loop 2 — finite-aperture positivity is cofinally conservative

**FALSIFIED by `(CAG.15)`.** Every finite aperture has positive radius, but the radii collapse.

**Stronger survivor:** the inverse radii form the monotone exhaustion `(CAG.12)`.

### Loop 3 — phase reconstruction supplies positivity

**FALSIFIED.** Fourier uniqueness recovers `h` but gives no bound on `(-h_n/w_n)_+`.

**Stronger survivor:** reporter faithfulness plus one weighted relative-density estimate computes a
positive admission radius exactly.

### Loop 4 — positive comparison preserves the gauge exactly

**FALSIFIED.** Averaging can strictly reduce the largest negative density.

**Stronger survivor:** positive maps contract `kappa` and enlarge `rho`, the data-processing law
`(CAG.4)`.

### Loop 5 — arbitrary comparison maps obey data processing

**FALSIFIED.** `A=-id` reverses the cone.

**Stronger survivor:** positivity of the source-to-receiver comparison is the load-bearing selector
hypothesis and must be constructed, not inferred from coefficient faithfulness.

### Loop 6 — the theorem proves RH

**FALSIFIED.** It proves a selector mechanism. RH requires the literal pre-zero arithmetic
comparison to be positive and the source intervention to have finite gauge uniformly through the
adaptive/cofinal completion.

## 9. Internal and external frontier

- `[CORPUS]` `HTGeometry.GenerativeResponseFusion` proves the finite contingent/null-observer law,
  but has no infinite radial gauge.
- `[CORPUS]` `ConstraintFrameRelativity.ValuatedPluckerGram` and
  `HilbertMetric.GradedPartition` already close the finite contact/Pluecker alternative; this killed
  the preceding higher-contact conjecture.
- `[LOCAL-RESEARCH]` `prime-coframe-completion-port-uncertainty-law.md` and the weighted-port cards
  show completion-dependent port loss, but do not classify straight-line intervention radius.
- `[LITERATURE]` Bednarczuk--Lesniewski--Rutkowski study tangent/linearized cones in Banach
  constraint systems, <https://arxiv.org/abs/1905.05581>.
- `[LITERATURE]` Glueck--Weber study almost and quasi-interior points in ordered Banach spaces and
  positive semigroups, <https://arxiv.org/abs/1901.03306>.
- `[LITERATURE]` Ligonniere proves projective nonexpansiveness and characterizes strict contraction
  by uniform positivity for positive operators, <https://arxiv.org/abs/2312.11147>.

The cone gauge, tangent-cone closure, and positive-map contraction are classical ordered/convex
mechanisms. No novelty claim is load-bearing. The exact residue is their fusion with coefficient-
faithful history reconstruction and positive-null generation into a cofinal admission law for the
HGT source/observer problem.

## 10. Promotion gate

- [x] exact coordinate-free gauge stated;
- [x] exact `ell^1` three-cone theorem stated;
- [x] positive-map data processing stated;
- [x] cofinal exhaustion and fourth-organ prediction stated;
- [x] explicit countermodel closes finite-to-cofinal failure;
- [x] hostile audit every proof step and edge case;
- [x] close paper proof without Fourier/topology gaps;
- [x] promote to Stage 2;
- [x] formalize reciprocal feasibility, positive-map data processing, exact finite/contingent
  equivalence, conserved probability countermodel, and cofinal spectral collapse;
- [x] formalize the full `ell^1` closure identity and Fourier uniqueness clause;
- [ ] only after Lean, test literal arithmetic source gauge and comparison positivity.

## Log

- 2026-08-11 — higher-order Pluecker/contact conjecture killed by existing Stage-3
  `ValuatedPluckerGram` and `GradedPartition`. The failure forced the finite-versus-cofinal admission
  pivot.
- 2026-08-11 — three-cone admission-gauge conjecture stated with proposed proof and six hostile
  fail/survivor loops. Paper proof and external-priority audit remain open.
- 2026-08-11 — hostile audit closed the paper proof. Lean module
  `HTGeometry.CofinalGenerativeAdmission` certifies the algebraic/cofinal core and an actual
  mass-one, mass-zero-tangent probability countermodel. Full `ell^1` closure and Fourier uniqueness
  remain explicit formal boundaries rather than silently certified claims.
- 2026-08-28 — `HTGeometry.CofinalGenerativeAdmissionClosure` closes both formal boundaries in the
  actual normed `ell^1` space: corrected finite-support radial directions prove the exact closure
  identity, while finite positive/negative atomic measures plus characteristic-function uniqueness
  prove coefficient faithfulness for every injective real frequency family. Direct Lean check and
  targeted module build passed; all 36 new declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`.
