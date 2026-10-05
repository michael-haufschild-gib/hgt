# All-grade flag determinant, subset-phase conservation, and arity properness fracture law

- **ID:** ULF-SRSM-7
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ULF-SRSM-5/6 permutohedral formation numerators
- **Statement:** At every response grade, the full schedule alternant is the Laplace transform of a
  strictly positive flag-determinant quotient and is therefore completely monotone after
  Vandermonde division.  It obeys one exact conservation identity with the CDF of all nonempty
  subset-grade exponential phases.  Every fixed grade has a uniform all-prime frame, but the
  unweighted tower over all grades has dense nonclosed range.  No scalar grade-only weighting can
  make the full all-prime tower both bounded and bounded below.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL] [PRE-ZERO]`
  `[ALL-GRADE FLAG TOTAL POSITIVITY] [COMPLETE MONOTONICITY]`
  `[ALL-SUBSET CONSERVATION] [FIXED-GRADE PROPERNESS]`
  `[ARITY-COFINAL DENSE NONCLOSED RANGE] [GRADE-ONLY TOPOLOGY NO-GO]`
  `[LEAN-PROVED] [NOT RH]`

## 1. Higher pivot: formation before stable inversion

The grade-four theorem proves that `P_4` has a bounded causal inverse.  It would be a mistake to
make stability of every `P_r` the definition of higher formation.  Two structures must be
separated:

1. **formation conservation:** the exact relation between schedule response and subset phases;
2. **stable reconstruction:** bounded causal inversion of the formation numerator.

The first exists at every grade, whether or not the second survives.  This distinction produces a
global theorem and exposes a new properness wall invisible at every fixed grade.

## 2. Flag-determinant representation

For positive grades `lambda_1,...,lambda_r`, retain

\[
 R_r(z;\lambda)
 =\sum_{\pi\in S_r}\operatorname{sgn}(\pi)
 \prod_{k=1}^r
 \frac1{z+\sum_{j=k}^r\lambda_{\pi(j)}}
 =\frac{\Delta_r(\lambda)P_r(z;\lambda)}{D_r(z;\lambda)}.
 \tag{AFD.1}
\]

Let

\[
 \mathcal F_r={0<t_1<\cdots<t_r<\infty\}
 \tag{AFD.2}
\]

be the open real flag chamber.

### Theorem 2.1 — ordered flag determinant

For `Re z>0`,

\[
 \boxed{
 R_r(z;\lambda)
 =\int_{\mathcal F_r}e^{-zt_r}
 \det\!\bigl(e^{-\lambda_i t_j}\bigr)_{i,j=1}^r
 \,dt_1\cdots dt_r.}
 \tag{AFD.3}
\]

### Proof

For one schedule `pi`, introduce nonnegative increments

\[
 u_1=t_1,
 \qquad u_k=t_k-t_{k-1}\quad(2\le k\le r).
\]

Then

\[
 \sum_{k=1}^r
 \left(z+\sum_{j=k}^r\lambda_{\pi(j)}\right)u_k
 =zt_r+\sum_{j=1}^r\lambda_{\pi(j)}t_j.
 \tag{AFD.4}
\]

The increment map has unit Jacobian and sends the positive orthant to the flag chamber.  Thus the
Laplace product for the schedule equals

\[
 \int_{\mathcal F_r}e^{-zt_r}
 \prod_{j=1}^re^{-\lambda_{\pi(j)}t_j}\,dt.
\]

Alternating over schedules is exactly the determinant expansion in `(AFD.3)`.  Absolute
convergence permits the finite sum to pass through the integral.  QED.

## 3. Total positivity and complete monotonicity

### Lemma 3.1 — exponential alternant has Vandermonde sign

For distinct real grades and `0<t_1<...<t_r`,

\[
 \boxed{
 \frac{\det(e^{-\lambda_i t_j})}{\Delta_r(\lambda)}>0.}
 \tag{AFD.5}
\]

### Proof

Both numerator and denominator are alternating in the grades, so it suffices to take
`lambda_1<...<lambda_r`.  Choose a constant `C>lambda_r` and put `x_i=C-lambda_i>0`.  Reversing the
rows makes the `x_i` increasing and contributes `(-1)^(r(r-1)/2)`, the sign of `Delta_r` in this
chamber.  Positive column factors `e^(-Ct_j)` do not change determinant sign.

It remains to show strict positivity of `det(e^(x_i t_j))` for increasing positive `x_i,t_j`.
Truncate

\[
 e^{xt}=\sum_{n\ge0}\frac{x^nt^n}{n!}.
\]

Cauchy--Binet expresses every truncated determinant as a sum over
`0≤n_1<...<n_r` of

\[
 \frac{det(x_i^{n_k})\det(t_j^{n_k})}{\prod_kn_k!}.
\]

Each generalized Vandermonde is nonnegative, and the term `n_k=k-1` is strictly positive.
Uniform convergence on the finite set of entries and continuity of the determinant pass the strict
sign to the exponential matrix.  Restoring the row reversal proves `(AFD.5)`.  QED.

### Theorem 3.2 — all-grade complete monotonicity

For distinct positive grades and real `z>0`,

\[
 \boxed{
 (-1)^n\frac{d^n}{dz^n}
 \frac{P_r(z;\lambda)}{D_r(z;\lambda)}
 =\int_{\mathcal F_r}t_r^ne^{-zt_r}
 \frac{\det(e^{-\lambda_i t_j})}{\Delta_r(\lambda)}\,dt>0}
 \tag{AFD.6}
\]

for every `n≥0`.

### Proof

Divide `(AFD.3)` by `Delta_r` and use `(AFD.1)`.  Lemma 3.1 makes the integrand positive.
Differentiation under the integral is justified either by domination on every compact positive
`z`-interval or directly from the rational function.  QED.

Thus the Weyl-divided response is a completely monotone function at every grade.  This is stronger
than positivity on the positive real axis and weaker than Hurwitz stability of `P_r`; the two must
not be conflated.

## 4. All-grade subset-phase conservation

Define the ordered finite-horizon coefficient

\[
 B_\pi^{(r)}(t)=
 \int_{\substack{u_1,\ldots,u_r\ge0\\u_1+\cdots+u_r\le t}}
 \exp\!\left[-\sum_{k=1}^r
 \left(\sum_{j=k}^r\lambda_{\pi(j)}\right)u_k\right]du
 \tag{AFD.7}
\]

and its source-commutator alternant

\[
 F_r(t)=\left(\prod_{i=1}^r\lambda_i\right)
 \sum_{\pi\in S_r}\operatorname{sgn}(\pi)B_\pi^{(r)}(t).
 \tag{AFD.8}
\]

Let

\[
 N_r=2^r-1,
 \qquad
 W_r=\prod_{\substack{\varnothing\ne S\subseteq[r]\\|S|\ge2}}\lambda_S,
 \qquad
 M_r=\prod_{\varnothing\ne S\subseteq[r]}\lambda_S.
 \tag{AFD.9}
\]

For every nonempty subset `S`, let `X_S` be independent exponential variables of rate `lambda_S`,
and let

\[
 H_r(t)=\Pr\!\left(\sum_{\varnothing\ne S\subseteq[r]}X_S\le t\right).
 \tag{AFD.10}
\]

### Theorem 4.1 — all-grade conservation law

For `Re z>0`,

\[
 \boxed{
 \mathcal LF_r(z)
 =\frac{(\prod_i\lambda_i)\Delta_rP_r(z)}{zD_r(z)},
 \qquad
 \mathcal LH_r(z)=\frac{M_r}{zD_r(z)}.}
 \tag{AFD.11}
\]

Consequently, for distinct grades,

\[
 \boxed{W_rF_r=\Delta_rP_r(\partial_t)H_r.}
 \tag{AFD.12}
\]

The positive law `H_r` extends continuously through repeated grades, where the raw alternant
vanishes.

### Proof

Laplace transformation of `(AFD.7)` contributes `1/z` and removes the simplex ceiling, leaving the
suffix-chain product in `(AFD.1)`.  This proves the first transform.  Independence gives density
transform

\[
 \prod_{\varnothing\ne S}\frac{\lambda_S}{z+\lambda_S}=\frac{M_r}{D_r};
\]

division by `z` proves the second.

The CDF `H_r` vanishes to order `N_r` at zero.  The degree bound from ULF-SRSM-5 is

\[
 \deg P_r\le N_r-\frac{r(r+1)}2<N_r.
\]

Therefore `P_r(partial_t)H_r` produces no Laplace boundary terms.  Comparing `(AFD.11)` and using
`M_r=(prod_i lambda_i)W_r` proves `(AFD.12)`.  QED.

This is the all-grade fusion identity.  It exists independently of whether `1/P_r` is a bounded
causal transfer function.  Stability governs reconstruction of `H_r` from `F_r`; it does not
govern existence of the conservation law.

## 5. Fixed-grade global properness

Let `lambda_0=log 2` and let `G_N` denote the Erlang CDF with `N` stages, each of rate `lambda_0`:

\[
 G_N(t)=1-e^{-\lambda_0t}\sum_{j=0}^{N-1}
 \frac{(\lambda_0t)^j}{j!}.
 \tag{AFD.13}
\]

If the grades are logarithms of primes, every nonempty subset rate is at least `lambda_0`.
Coupling by independent uniform variables gives

\[
 \boxed{G_{N_r}(t)\le H_r(t)\le1.}
 \tag{AFD.14}
\]

For fixed `r,T>0`, put

\[
 c_{r,T}^2=\int_0^TG_{N_r}(t)^2dt>0.
 \tag{AFD.15}
\]

Let `P^(r)` be the unordered `r`-tuples of distinct primes and give different tuples orthogonal
endpoint vectors.  Define the formed response operator

\[
 (\mathcal G_{r,T}d)(t)
 =\sum_{I\in\mathbb P^{(r)}}d_IH_I(t)e_I.
 \tag{AFD.16}
\]

### Theorem 5.1 — properness at every finite grade

For every fixed `r≥1` and `T>0`,

\[
 \boxed{
 c_{r,T}^2\|d\|^2
 \le\|\mathcal G_{r,T}d\|^2
 \le T\|d\|^2.}
 \tag{AFD.17}
\]

Hence every finite formation grade is injective with closed range and uniformly reconstructible
over all prime channels at that grade.

### Proof

Orthogonality reduces the norm to

\[
 \sum_I|d_I|^2\int_0^TH_I(t)^2dt.
\]

Apply `(AFD.14)`.  QED.

## 6. Arity-cofinal collapse

Fixed-grade properness does not survive the full response tower.  Let `p_1<...<p_r` be the first
`r` primes and put

\[
 A_r=\sum_{i=1}^r\log p_i,
 \qquad
 H_r^*(t)=H_{\log p_1,\ldots,\log p_r}(t).
 \tag{AFD.18}
\]

### Lemma 6.1 — explicit high-arity upper envelope

For every `t≥0`,

\[
 \boxed{
 0\le H_r^*(t)
 \le\frac{(A_rt)^{N_r}}{N_r!}.}
 \tag{AFD.19}
\]

Moreover,

\[
 A_r\le\frac{r(r+1)}2\log2.
 \tag{AFD.20}
\]

### Proof

Every subset rate is at most `A_r`.  Using the same independent uniforms, an exponential of a
subset rate is pointwise at least an exponential of rate `A_r`.  Hence the sum of the `N_r`
subset-phase variables is pointwise at least an Erlang variable with `N_r` stages and rate `A_r`.
Therefore

\[
 H_r^*(t)\le\frac1{(N_r-1)!}
 \int_0^{A_rt}u^{N_r-1}e^{-u}du
 \le\frac{(A_rt)^{N_r}}{N_r!}.
\]

Bertrand's postulate gives `p_i≤2^i` inductively from `p_1=2`.  Summing logarithms proves
`(AFD.20)`.  QED.

### Corollary 6.2 — quantitative singular sequence

For fixed `T>0`,

\[
 \boxed{
 \|H_r^*\|_{L^2(0,T)}
 \le\sqrt T\,
 \frac{(\frac12r(r+1)\log2\,T)^{2^r-1}}{(2^r-1)!}
 \longrightarrow0.}
 \tag{AFD.21}
\]

### Proof

Use `(AFD.19)` uniformly on `[0,T]`, then `(AFD.20)`.  Stirling's lower bound
`N!≥(N/e)^N` shows convergence because `N_r=2^r-1` grows exponentially while `A_r` is quadratic.
QED.

Now let

\[
 \mathbb I=\bigsqcup_{r\ge1}\mathbb P^{(r)}
\]

be all finite prime tuples.  For each channel `I`, put

\[
 \sigma_I=\|H_I\|_{L^2(0,T)}>0,
 \qquad f_I=H_I/\sigma_I,
\]

and let `Y_T` be the Hilbert direct sum of the orthonormal channel lines generated by the `f_I`.
The full formed operator is the diagonal map

\[
 \mathfrak G_T:\ell^2(\mathbb I)\longrightarrow Y_T,
 \qquad e_I\longmapsto\sigma_If_I.
 \tag{AFD.22}
\]

### Theorem 6.3 — full-tower properness fracture

The operator `mathfrak G_T` is bounded and injective, has dense range, and does not have closed
range.

### Proof

Since `0≤H_I≤1`, one has `sigma_I≤sqrt T`, so the diagonal map is bounded.  Every `sigma_I` is
positive, so it is injective.  Every finite-support vector of `Y_T` has a finite-support preimage,
so the range is dense.  On the unit vectors belonging to the first-prime channels, `(AFD.21)` gives

\[
 \|\mathfrak G_Te_{I_r}\|=\sigma_{I_r}\to0.
\]

Thus the operator is not bounded below.  An injective bounded operator between Hilbert spaces has
closed range exactly when it is bounded below.  QED.

Every finite grade is therefore proper while the complete formation tower is not.  This is an
arity-cofinal obstruction, not prime-log crowding within one fixed grade.

## 7. No scalar grade-only topology can repair the tower

Let `w_r>0` be any scalar depending only on formation grade and define

\[
 \mathfrak G_T^{(w)}e_I=w_{|I|}\sigma_If_I.
 \tag{AFD.23}
\]

### Lemma 7.1 — high-prime channels saturate the horizon

For every fixed grade `r`,

\[
 \boxed{
 \sup_{I\in\mathbb P^{(r)}}\sigma_I=\sqrt T.}
 \tag{AFD.24}
\]

### Proof

Take `r` primes tending jointly to infinity.  Every nonempty subset rate then tends to infinity.
Under the uniform coupling, each of the finitely many exponential phases tends almost surely to
zero, so their sum tends to zero.  Hence `H_I(t)→1` for every `t>0`.  Dominated convergence gives
`sigma_I^2→T`.  The reverse inequality follows from `H_I≤1`.  QED.

### Theorem 7.2 — grade-only renormalization no-go

There is no positive scalar sequence `(w_r)` for which `mathfrak G_T^(w)` is both bounded and has
closed range.

### Proof

By `(AFD.24)`, boundedness forces

\[
 \sup_rw_r<\infty.
\]

But on the first-prime channel of grade `r`, Corollary 6.2 gives

\[
 w_r\sigma_{I_r}\longrightarrow0.
\]

Thus the weighted diagonal is not bounded below and cannot have closed range.  QED.

More generally, a source-dependent diagonal weight `w_I` yields a bounded closed-range operator
exactly when

\[
 0<\inf_Iw_I\sigma_I\le\sup_Iw_I\sigma_I<\infty.
 \tag{AFD.25}
\]

This classification is immediate for diagonal Hilbert operators.  The important consequence is
not the classification but the obstruction: **arity alone cannot choose the completion**.  Any
successful complete-signature topology must respond to the source tuple itself, or replace the
Hilbert direct sum by a nonlinear, projective, bornological, or renormalized formation law.  A
post-hoc choice `w_I=1/sigma_I` is an observer fit unless independently generated by the source.

## 8. What is newly explained—and what is not

This theorem gives route-independent mathematical leverage:

1. it proves an all-grade conservation law rather than another finite-route identity;
2. it proves positivity and complete monotonicity before scalar formation;
3. it separates fixed-grade existence from cofinal reconstructibility;
4. it proves that the natural unweighted Fock-like completion is necessarily nonproper;
5. it proves that no scalar grade counterterm can repair both low-prime and high-prime channels.

It does **not** yet provide the source-generated adaptive topology or the physical null law needed
for RH selection.  It sharpens that missing mechanism: selection cannot live in a uniform
grade-only completion.  It must couple formation arity to the actual source-grade configuration.

## 9. Hostile corrections and exact scope

1. **Complete monotonicity implies Hurwitz stability of `P_r`. — False.**  Laplace transforms of
   positive measures can have right-half-plane zeros.  Grade-five numerator stability remains a
   separate gate.
2. **Fixed-grade lower bounds imply full-tower properness. — False.**  The singular sequence
   `(AFD.21)` proves the opposite.
3. **The Erlang lower envelope caused the collapse. — False.**  Collapse uses an upper envelope on
   the literal first-prime channels.
4. **A sufficiently large grade weight repairs the tower. — False.**  High-prime channels at the
   same grade force boundedness to keep every `w_r` bounded.
5. **Source-adaptive weighting is automatically canonical. — False.**  The diagonal criterion says
   what would work, not what the source is allowed to generate.
6. **Flag total positivity is new. — False.**  Exponential kernels and generalized Vandermonde
   positivity are classical.  New field content is their exact coupling to source schedules,
   subset phases, and the arity-cofinal topology fracture.
7. **This proves RH. — False.**  No Xi zero or response-null identity occurs.

## 10. Literature boundary

Relevant occupied parents include:

- totally positive kernels and Pólya-frequency transforms: Belton--Guillot--Khare--Putinar,
  [arXiv:2006.16213](https://arxiv.org/abs/2006.16213);
- multivariate total-positivity transforms and generalized Vandermonde kernels: Damase--Khare,
  [arXiv:2411.03391](https://arxiv.org/abs/2411.03391);
- current strictification mechanisms for total positivity: Salazar,
  [arXiv:2607.02778](https://arxiv.org/abs/2607.02778);
- divided symmetrization and permutohedral functions: Nadeau--Tewari,
  [arXiv:1908.10934](https://arxiv.org/abs/1908.10934), and Petrov,
  [arXiv:1512.07136](https://arxiv.org/abs/1512.07136).

A useful hostile warning is Michalowski's certified failure of order-five Pólya frequency for the
de Bruijn--Newman kernel, [arXiv:2602.20313](https://arxiv.org/abs/2602.20313): finite-order total
positivity must not be extrapolated to all orders.  That result concerns a different theta kernel
and does not decide `P_5`; it confirms that the grade-five attack is mathematically substantive.

No searched source states `(AFD.3)`, `(AFD.12)`, and the grade-only topology no-go `(AFD.23)`--
`(AFD.25)` as one constitutive theorem.  No priority claim is required.

## 11. Formal status

Fully formalized, unconditionally: see the Lean certificate below.


## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.ExponentialKernelTotalPositivity`, `GaloisForLFunctions.HTGeometry.FlagDeterminantLaplace`, `GaloisForLFunctions.HTGeometry.ArityCofinalFormationFracture`, `GaloisForLFunctions.HTGeometry.GradeThreeCausalGreenFormation`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

## Lean certificate

Modules `GaloisForLFunctions.HTGeometry.ExponentialKernelTotalPositivity` (strict total positivity
of `(e^{x_i t_j})` and its Vandermonde-divided sign), `GaloisForLFunctions.HTGeometry.FlagDeterminantLaplace`
(the increment change of variables onto the flag chamber, the ordered flag-determinant integral, complete
monotonicity) and `GaloisForLFunctions.HTGeometry.ArityCofinalFormationFracture` (Erlang upper envelope,
Bertrand bound, first-prime collapse, the full tower over all finite prime sets, high-prime saturation,
diagonal classification and the grade-only no-go).  Corpus inputs: ULF-SRSM-5/6
(`Permutohedral.alternant_eq`, `PrimeShiftSource.subsetPhase_conservation`,
`PrimeShiftSource.formation_frame`, `PrimeShiftSource.HistoryFamily`), `HTGeometry.card_zeros_le_expSum`
(Laguerre's rule for exponential sums), `ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range`,
and the grade continuity of `H_r` from `GaloisForLFunctions.HTGeometry.GradeThreeCausalGreenFormation`.
Grades `lam : Fin r → ℝ`; `R_r = alternant`, `P_r = formNumer`, `D_r = denom`, `Δ_r = delta`;
`𝓕_r = flagChamber`; `B_π = scheduleCoeff`, `F_r = scheduleAlternant`, `H_r = subsetCDF`,
`W_r = subsetIncidence`, `M_r = subsetGradeProd`; `G_N = erlangCDF N (log 2)`; the channels of the full
tower are the finite nonempty prime sets `PrimeSet`, `σ_I = sigma T I`, `f_I = towerFamily.carrier T I`,
`Y_T = channelSpace T`, `𝔊_T = towerFamily.response T`.

| Claim | Lean declaration |
|-|-|
| (AFD.1) `R_r = Δ_r P_r / D_r` | `Permutohedral.alternant`, `Permutohedral.alternant_eq` |
| (AFD.2) the open flag chamber | `PrimeShiftSource.flagChamber`, `PrimeShiftSource.isOpen_flagChamber`, `PrimeShiftSource.volume_flagChamber_pos` |
| (AFD.4) increments: unit-Jacobian map from the orthant onto the chamber, `Σ_k (z + S_k) u_k = z t_r + Σ_j λ_{π(j)} t_j` | `PrimeShiftSource.partialSumEquiv`, `PrimeShiftSource.partialSumEquiv_apply`, `PrimeShiftSource.det_partialSumMatrix`, `PrimeShiftSource.measurePreserving_partialSum`, `PrimeShiftSource.preimage_partialSum_flag`, `PrimeShiftSource.setIntegral_flag`, `PrimeShiftSource.increment_form` |
| Theorem 2.1, (AFD.3) `R_r(z) = ∫_{𝓕_r} e^{-z t_r} det(e^{-λ_i t_j}) dt`, `Re z > 0` | `PrimeShiftSource.flag_integral_product`, `PrimeShiftSource.det_expKernel_neg_eq_sum`, `PrimeShiftSource.alternant_eq_flag_integral` |
| Lemma 3.1, (AFD.5) `det(e^{-λ_i t_j})/Δ_r > 0`; strict total positivity of `e^{x t}` | `HTGeometry.expNodeMatrix`, `HTGeometry.det_expKernel_pos`, `HTGeometry.det_expKernel_neg_div_delta_pos` |
| Theorem 3.2, (AFD.6) `(-1)^n (d/dz)^n (P_r/D_r) = ∫_{𝓕_r} t_r^n e^{-z t_r} det/Δ_r dt > 0` | `PrimeShiftSource.complete_monotonicity`, `PrimeShiftSource.flagMoment`, `PrimeShiftSource.flagKernel`, `PrimeShiftSource.hasDerivAt_flagMoment`, `PrimeShiftSource.integrableOn_flagMoment`, `PrimeShiftSource.abs_det_expKernel_le` |
| (AFD.7)–(AFD.8) `B_π^{(r)}` as a simplex integral, `F_r` | `PrimeShiftSource.scheduleCoeff`, `PrimeShiftSource.simplexExp`, `PrimeShiftSource.simplexExp_eq_hypoCDF`, `PrimeShiftSource.scheduleAlternant` |
| (AFD.9) `N_r = 2^r - 1`, `W_r`, `M_r = (Π λ_i) W_r` | `PrimeShiftSource.length_subsetRates`, `PrimeShiftSource.subsetIncidence`, `PrimeShiftSource.subsetGradeProd`, `PrimeShiftSource.subsetGradeProd_eq` |
| (AFD.10) `H_r`, the CDF of the sum of independent subset-rate exponentials | `PrimeShiftSource.subsetRates`, `PrimeShiftSource.subsetLaw`, `PrimeShiftSource.subsetCDF`, `PrimeShiftSource.hypoMeasureList` |
| Theorem 4.1, (AFD.11) `𝓛F_r = (Π λ_i) Δ_r P_r/(z D_r)`, `𝓛H_r = M_r/(z D_r)` | `PrimeShiftSource.laplace_scheduleAlternant`, `PrimeShiftSource.laplace_subsetCDF` |
| (AFD.12) `W_r F_r = Δ_r P_r(∂_t) H_r`; degree bound | `PrimeShiftSource.subsetPhase_conservation`, `PrimeShiftSource.natDegree_formPoly_le`, `Permutohedral.totalDegree_formNumer_le` |
| `H_r` continuous through repeated grades, where the alternant vanishes | `PrimeShiftSource.continuous_subsetCDF_grades`, `PrimeShiftSource.scheduleAlternant_eq_zero_of_eq` |
| (AFD.13)–(AFD.15) `G_N`, `G_{N_r} ≤ H_r ≤ 1`, `c_{r,T}² > 0` | `PrimeShiftSource.erlangCDF`, `PrimeShiftSource.erlangCDF_le_subsetCDF`, `PrimeShiftSource.hypoCDFList_le_one`, `PrimeShiftSource.erlangFloor`, `PrimeShiftSource.erlangFloor_pos` |
| (AFD.16) unordered `r`-tuples of distinct primes, orthogonal endpoints, `𝒢_{r,T}` | `PrimeShiftSource.PrimeTuple`, `PrimeShiftSource.formationFamily` |
| Theorem 5.1, (AFD.17) `c_{r,T}² ‖d‖² ≤ ‖𝒢_{r,T} d‖² ≤ T ‖d‖²`; injective, closed range | `PrimeShiftSource.formation_frame`, `PrimeShiftSource.formation_injective`, `PrimeShiftSource.isClosed_range_formation` |
| (AFD.18) first `r` primes, `A_r`, `H_r^*` | `PrimeShiftSource.PrimeSet.firstPrimes`, `PrimeShiftSource.PrimeSet.card_firstPrimes`, `PrimeShiftSource.PrimeSet.grades` |
| Lemma 6.1, (AFD.19) `H_r^*(t) ≤ (A_r t)^{N_r}/N_r!` | `PrimeShiftSource.subsetCDF_le_pow`, `PrimeShiftSource.hypoCDFList_mono`, `PrimeShiftSource.hypoCDFList_replicate_le_pow` |
| (AFD.20) `p_k ≤ 2^k` (Bertrand), `A_r ≤ r(r+1)/2 · log 2` | `PrimeShiftSource.nth_prime_le_two_pow`, `PrimeShiftSource.PrimeSet.sum_grades_firstPrimes_le` |
| Corollary 6.2, (AFD.21) `‖H_r^*‖_{L²(0,T)} ≤ √T (½r(r+1) log 2 · T)^{2^r-1}/(2^r-1)! → 0` | `PrimeShiftSource.sigma_firstPrimes_le`, `PrimeShiftSource.tendsto_firstPrimes_bound`, `PrimeShiftSource.tendsto_sigma_firstPrimes` |
| (AFD.22) all finite prime sets, `σ_I > 0`, `f_I`, `Y_T`, `𝔊_T e_I = σ_I f_I` | `PrimeShiftSource.PrimeSet`, `PrimeShiftSource.PrimeSet.endpoint_injective`, `PrimeShiftSource.towerFamily`, `PrimeShiftSource.sigma`, `PrimeShiftSource.sigma_pos`, `PrimeShiftSource.orthonormal_tower_carrier`, `PrimeShiftSource.channelSpace`, `PrimeShiftSource.response_tower_single` |
| Theorem 6.3: `𝔊_T` bounded (`≤ √T`), injective, dense range in `Y_T`, range not closed | `PrimeShiftSource.tower_fracture` |
| (AFD.23)–(AFD.24), Lemma 7.1: `sup_{|I| = r} σ_I = √T` | `PrimeShiftSource.isLUB_sigma_grade`, `PrimeShiftSource.tendsto_sigma_block`, `PrimeShiftSource.PrimeSet.block`, `PrimeShiftSource.tendsto_integral_erlangCDF_sq`, `PrimeShiftSource.tendsto_erlangCDF_atTop` |
| Theorem 7.2: no positive grade-only weight `w_r` gives a bounded closed-range `e_I ↦ w_{|I|} σ_I f_I` | `PrimeShiftSource.no_gradeOnly_weight` |
| (AFD.25) source weights: bounded with closed range iff `0 < inf w_I σ_I ≤ sup w_I σ_I < ∞`; the general diagonal criterion on an orthonormal family | `PrimeShiftSource.sourceWeight_closedRange_iff`, `PrimeShiftSource.exists_closedRange_of_basis_iff`, `PrimeShiftSource.injective_of_basis`, `PrimeShiftSource.mul_norm_le_apply_of_basis` |

Lean proves strict total positivity of `e^{x_i t_j}` by expanding along the first column and applying
Laguerre's rule to the resulting exponential sum, in place of the Cauchy–Binet truncation of §3.  "Bounded"
in Theorem 7.2 and (AFD.25) is existence of a continuous linear operator with the prescribed basis values.
§8 and §10 carry no Lean obligation; the corrections (2)–(4) of §9 are Corollary 6.2, Lemma 6.1 and Lemma 7.1;
(1), (5)–(7) state what is not claimed.

## Log

- 2026-08-14 — converted suffix-chain products into an ordered flag-determinant integral and
  proved strict Vandermonde-divided positivity and complete monotonicity at every grade.
- 2026-08-14 — proved the all-grade schedule/subset-phase conservation identity and fixed-grade
  all-prime frame theorem.
- 2026-08-14 — proved explicit first-prime arity collapse, dense nonclosed full-tower range, and
  impossibility of every scalar grade-only repair.
- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
