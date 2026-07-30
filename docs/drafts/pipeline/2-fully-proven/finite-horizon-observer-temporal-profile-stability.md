# Finite-horizon observer temporal-profile stability

- **ID:** `finite-horizon-observer-temporal-profile-stability`
- **Stage:** 2-fully-proven
- **Type:** PAPER-PROVED INFRASTRUCTURE / OPERATIONAL TEMPORAL DIMENSION /
  PERTURBATION CROSSOVER
- **Source:** hostile objection 2--3 against
  `../1-in-progress/temporal-codimension-interaction-law.md`
- **Scientific status:** `[PAPER-PROVED] [NOVELTY NOT CLAIMED]`
  `[CSTAR OPERATOR-NORM CORE LEAN-PROVED]`
  `[COVERING-PROFILE FORMALIZATION OPEN]`

## Result

Exact rational gap rank is an infinite-time invariant and is discontinuous
under arbitrarily small Hamiltonian perturbations. The physically robust
replacement at finite time is the covering profile of the reporter orbit.

For every finite reporter family:

1. its finite-horizon profile is Lipschitz stable under Hamiltonian
   perturbations;
2. its long-horizon orbit closure has metric dimension equal to the rational
   rank of the visible gap module;
3. the order of limits is essential:
   \[
   \text{watch for arbitrarily long time first, then increase resolution};
   \]
4. a perturbation of operator norm \(\delta\) cannot produce a
   resolution-\(\varepsilon\) temporal-profile change before a time of order
   \(\varepsilon/\delta\).

This is the rigorous lower half of the interaction crossover law. It does not
prove when the new directions have fully activated.

## Setting

Let \(\mathcal H\) be a finite-dimensional complex Hilbert space. Let \(H\)
and \(K\) be self-adjoint operators and
\[
 U_H(t)=e^{-itH},\qquad U_K(t)=e^{-itK}.
\]
Fix a finite family of Hilbert--Schmidt reporters \(B_1,\ldots,B_N\) and
positive weights \(\lambda_1,\ldots,\lambda_N\). Put
\[
 \mathcal B_{\mathcal O}
 =
 \left(\sum_{a=1}^{N}\lambda_a
   \|B_a\|_{\mathrm{HS}}^2\right)^{1/2}.             \tag{1}
\]

Use the weighted direct-sum Hilbert space
\[
 \mathscr X_{\mathcal O}
 =
 \bigoplus_{a=1}^{N}\mathrm{HS}(\mathcal H),
 \qquad
 \|(X_a)_a\|_{\mathcal O}^2
 =
 \sum_a\lambda_a\|X_a\|_{\mathrm{HS}}^2.             \tag{2}
\]
Define the observed orbit
\[
 \Phi_H(t)
 =
 \bigl(U_H(t)B_aU_H(t)^\dagger\bigr)_{a=1}^{N},      \tag{3}
\]
its finite-horizon image and its compact closure
\[
 X_H(T)=\{\Phi_H(t):|t|\leq T\},\qquad
 X_H(\infty)=\overline{\Phi_H(\mathbb R)}.            \tag{4}
\]

For a totally bounded metric set \(X\), let \(N_\varepsilon(X)\) be its least
open-ball covering number at radius \(\varepsilon>0\), and define
\[
 S_{H,\mathcal O}(T,\varepsilon)
 =\log N_\varepsilon(X_H(T)).                         \tag{5}
\]
This is the finite-horizon temporal information profile. It counts the
number of reporter configurations distinguishable up to resolution
\(\varepsilon\) during the observed time window.

## Theorem A — exact perturbation stability

Let
\[
 \delta=\|H-K\|_{\mathrm{op}}.
\]
For every \(T\geq0\),
\[
 \boxed{
 d_{\mathrm H}\bigl(X_H(T),X_K(T)\bigr)
 \leq 2T\delta\,\mathcal B_{\mathcal O},
 }                                                     \tag{6}
\]
where \(d_{\mathrm H}\) is Hausdorff distance in
\(\mathscr X_{\mathcal O}\).

Consequently, with
\[
 r_T=2T\delta\,\mathcal B_{\mathcal O},
\]
for every \(\varepsilon>r_T\),
\[
 \boxed{
 N_{\varepsilon+r_T}(X_K(T))
 \leq N_\varepsilon(X_H(T))
 \leq N_{\varepsilon-r_T}(X_K(T)),
 }                                                     \tag{7}
\]
and the same inequalities hold with \(H,K\) interchanged.

In particular, if
\[
 T\leq\frac{\varepsilon}
 {4\delta\mathcal B_{\mathcal O}},                    \tag{8}
\]
then
\[
 \boxed{
 N_{3\varepsilon/2}(X_K(T))
 \leq N_\varepsilon(X_H(T))
 \leq N_{\varepsilon/2}(X_K(T)).
 }                                                     \tag{9}
\]
Thus an exact asymptotic rank jump has no order-one operational consequence
at resolution \(\varepsilon\) before the lower crossover scale in `(8)`.

### Proof

Duhamel's identity gives, for every real \(t\),
\[
 U_H(t)-U_K(t)
 =
 -i\int_0^t U_H(t-s)(H-K)U_K(s)\,ds
\]
with the orientation reversed when \(t<0\). Unitarity therefore gives
\[
 \|U_H(t)-U_K(t)\|_{\mathrm{op}}\leq |t|\delta.        \tag{10}
\]
For each reporter,
\[
\begin{aligned}
 &\|U_H(t)B_aU_H(t)^\dagger
      -U_K(t)B_aU_K(t)^\dagger\|_{\mathrm{HS}}\\
 &\quad\leq
 \|(U_H(t)-U_K(t))B_aU_H(t)^\dagger\|_{\mathrm{HS}}
 +\|U_K(t)B_a(U_H(t)^\dagger-U_K(t)^\dagger)\|_{\mathrm{HS}}\\
 &\quad\leq 2|t|\delta\|B_a\|_{\mathrm{HS}}.
\end{aligned}                                         \tag{11}
\]
Squaring, weighting and summing proves
\[
 \|\Phi_H(t)-\Phi_K(t)\|_{\mathcal O}
 \leq2|t|\delta\mathcal B_{\mathcal O}.               \tag{12}
\]
Matching equal times in the two orbit segments proves `(6)`.

If two sets have Hausdorff distance at most \(r\), every
\((\varepsilon-r)\)-cover of one is an \(\varepsilon\)-cover of the other,
and every \(\varepsilon\)-cover of one becomes an
\((\varepsilon+r)\)-cover of the other. This proves `(7)`.
Substitution of \(r_T\leq\varepsilon/2\) proves `(9)`. ∎

## Corollary A — return-record stability

Define the root displacement
\[
 D_{H,\mathcal O}(t)
 =\|\Phi_H(t)-\Phi_H(0)\|_{\mathcal O}.               \tag{13}
\]
The common initial reporter tuple cancels, so `(12)` and the reverse triangle
inequality give
\[
 \boxed{
 |D_{H,\mathcal O}(t)-D_{K,\mathcal O}(t)|
 \leq2|t|\delta\mathcal B_{\mathcal O}.
 }                                                     \tag{14}
\]
For
\[
 R_H(T,\varepsilon)
 =
 \{t\in[-T,T]:D_{H,\mathcal O}(t)<\varepsilon\},
\]
one obtains the exact finite-window sandwich
\[
 \boxed{
 R_K(T,\varepsilon-r_T)
 \subseteq R_H(T,\varepsilon)
 \subseteq R_K(T,\varepsilon+r_T).
 }                                                     \tag{15}
\]
The left set is empty by convention when its radius is nonpositive.

Equation `(15)` transfers immediately to upper and lower finite-window return
fractions. It is the required correction to any claim that an arbitrarily
small interaction has an instantaneous recurrence effect.

## Theorem B — asymptotic temporal dimension from the operational orbit

Diagonalize \(H\) into its distinct energy sectors:
\[
 H=\sum_{j=1}^{D}E_jP_j.
\]
Let \(M_{H,\mathcal O}\subset\mathbb R\) be the rational vector space
generated by all gaps \(E_i-E_j\) for which
\[
 \sum_a\lambda_a\|P_iB_aP_j\|_{\mathrm{HS}}^2>0,
\]
and set
\[
 d_{H,\mathcal O}=\dim_{\mathbb Q}M_{H,\mathcal O}.   \tag{16}
\]
Then
\[
 \boxed{
 \dim_{\mathrm M}X_H(\infty)=d_{H,\mathcal O},
 }                                                     \tag{17}
\]
where \(\dim_{\mathrm M}\) is the common upper and lower Minkowski dimension.
Equivalently,
\[
 \boxed{
 d_{H,\mathcal O}
 =
 \lim_{\varepsilon\downarrow0}
 \frac{\log N_\varepsilon(X_H(\infty))}
      {\log(1/\varepsilon)}.
 }                                                     \tag{18}
\]

The finite-horizon sets approach the compact orbit closure with resolution
slack. For every \(\eta>0\), some \(T_\eta<\infty\) satisfies
\[
 d_{\mathrm H}(X_H(T),X_H(\infty))<\eta
 \qquad(T\geq T_\eta),                                \tag{19}
\]
and therefore
\[
 \boxed{
 N_{\varepsilon+\eta}(X_H(\infty))
 \leq N_\varepsilon(X_H(T))
 \leq N_\varepsilon(X_H(\infty)).
 }                                                     \tag{20}
\]
Thus the operational ordered-limit formula is
\[
 \boxed{
 d_{H,\mathcal O}
 =
 \lim_{\varepsilon\downarrow0}
 \lim_{\eta\downarrow0}
 \liminf_{T\to\infty}
 \frac{\log N_{\varepsilon+\eta}(X_H(T))}
      {\log(1/\varepsilon)}.
 }                                                     \tag{21}
\]

### Proof

Choose a rational basis \(\omega_1,\ldots,\omega_d\) of the visible gap
module. Every visible gap is an integer multiple of a common rational
rescaling of this basis, so the observed orbit factors through a linear flow
with dense image on a \(d\)-torus. Quotient that torus by the common kernel of
all reporter characters. Minimality removes the kernel.

The resulting map
\[
 F:\mathbb T^d\longrightarrow\mathscr X_{\mathcal O}
\]
is real analytic and injective. Its differential at the identity has squared
norm
\[
 \|dF_0(y)\|_{\mathcal O}^2
 =
 \sum_{i,j}
 \left(\sum_a\lambda_a\|P_iB_aP_j\|_{\mathrm{HS}}^2\right)
 (m_{ij}\cdot y)^2,                                   \tag{22}
\]
where \(m_{ij}\in\mathbb Z^d\) is the character vector of the visible gap.
The visible characters span the dual real space, so `(22)` is positive
definite. Translation on the torus conjugates the differential by unitary
phase multipliers, preserving its singular values. Compactness therefore
makes \(F\) a locally bi-Lipschitz embedding with uniform constants.
A finite cover promotes this to the small-scale covering comparison needed
to preserve Minkowski dimension. Hence the image has Minkowski dimension
\(d\), proving `(17)`--`(18)`.

The sets \(X_H(T)\) increase with \(T\) and have dense union in their compact
closure. Compactness supplies a finite \(\eta\)-net from orbit points, all of
which occur in one sufficiently large time window. This proves `(19)`.
The right inequality in `(20)` follows from \(X_H(T)\subseteq X_H(\infty)\);
the left follows because an \(\varepsilon\)-cover of an \(\eta\)-dense subset
is an \((\varepsilon+\eta)\)-cover of the closure. Formula `(21)` follows from
`(18)` and `(20)`. ∎

## Interpretation

The exact projective spectral rank is not discarded. It is recovered as the
metric dimension of the completed operational orbit. The finite profile
\(S_{H,\mathcal O}(T,\varepsilon)\) is what a bounded-duration,
finite-resolution observer can access.

The noncommuting limits explain the apparent singularity:

```text
fixed T, fixed resolution, perturbation -> 0:
  observed histories remain close;

fixed nonzero generic perturbation, T -> infinity, resolution -> 0:
  the completed temporal rank can jump.
```

The missing upper crossover theorem must determine how quickly a generic
local perturbation fills the newly enlarged hull.

## Stronger dimension-free operator theorem

The finite-dimensional Hilbert--Schmidt argument above has now been
strengthened to arbitrary unital \(C^*\)-algebras and operator-normalized
observables.  For self-adjoint \(H,K\), every \(O\) in the algebra, and every
real \(t\),
\[
 \left\|
 e^{-itH}Oe^{itH}-e^{-itK}Oe^{itK}
 \right\|
 \leq
 2|t|\,\|H-K\|\,\|O\|.                              \tag{23}
\]
No matrix dimension, discrete spectrum, Hilbert--Schmidt normalization or
finite reporter assumption enters `(23)`.  If the left side is at least
\(\varepsilon\), with \(H\ne K\) and \(O\ne0\), then necessarily
\[
 |t|
 \geq
 \frac{\varepsilon}
 {2\|H-K\|\,\|O\|}.                                 \tag{24}
\]

This closes the universal lower observability scale in the natural
operator norm.  It does not formalize the Hausdorff and covering-number
consequences `(6)`--`(9)`, nor the finite-dimensional completed-orbit
dimension theorem `(17)`.

### Formal audit

Source:
`formal/GaloisForLFunctions/HTGeometry/FiniteHorizonCStarPerturbationLaw.lean`

Unconditional theorem chain:

1. `exp_skewAdjoint_sub_exp_skewAdjoint_norm_le`;
2. `selfAdjoint_unitaryEvolution_norm_sub_le`;
3. `unitary_conjugation_norm_sub_le`;
4. `selfAdjoint_heisenbergEvolution_norm_sub_le`;
5. `selfAdjoint_distinguishability_time_lowerBound`.

Direct source check passed with:

```text
lake env lean GaloisForLFunctions/HTGeometry/FiniteHorizonCStarPerturbationLaw.lean
```

The axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Hostile boundary

1. `(6)`--`(15)` are standard perturbation geometry applied to a new target;
   no stand-alone novelty is claimed.
2. `(23)`--`(24)` are dimension-free, but `(17)` is finite-dimensional.
   Infinite pure-point hulls require a
   scale-dependent information profile and need not have a finite rank
   exponent.
3. This result supplies only a lower activation timescale. It does not prove
   that new directions become equidistributed at that scale.
4. Exact rank remains experimentally uncertifiable from any single finite
   profile; only finite-resolution lower bounds are operational.
5. The master paper still requires generic bounded-degree local maximality
   and a metric-Diophantine upper crossover.

## Gates

- [x] finite-horizon profile defined
- [x] perturbation stability proved
- [x] return-set sandwich proved
- [x] asymptotic rank recovered from operational orbit
- [x] lower crossover obstruction proved
- [x] arbitrary unital C⋆-algebra operator-norm stability formalized
- [x] operator-normalized distinguishability-time lower bound formalized
- [ ] primary-source collision audit
- [ ] upper crossover theorem
- [ ] bounded-degree local maximality
- [ ] Hausdorff/covering-profile formalization
- [ ] completed-orbit dimension formalization
