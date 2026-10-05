# Formation-grade properness inversion, prime-log crowding, and finite-prolongation no-go

- **ID:** ULF-SRSM-3
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ULF-SRSM-2 arithmetic prime-shift response
- **Statement:** Source commutator normalization makes the complete one-letter prime response
  uniformly proper, but ordered two-letter fusion creates an injective compact orientation response.
  Source-certified prime-log crowding defeats every finite diagonal logarithmic/time-differential
  prolongation.  Restoring depth-two properness therefore requires a singular relative-scale
  operation, an infinite prolongation, or non-diagonal cross-scale coupling.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL]`
  `[FORMATION-GRADE PROPERNESS SPECTRUM] [FINITE-PROLONGATION NO-GO]`
  `[LEAN-PROVED] [PRE-ZERO] [NOT RH]`

## 1. Question

ULF-SRSM-2 proved two facts from one literal arithmetic source:

1. the commutator-normalized one-letter prime response has a uniform lower bound;
2. two ordered prime shifts have a nonzero signed schedule defect.

Nonzero response at every finite pair does not imply uniform reconstruction over all pairs.  The
missing question is whether the first-order properness theorem survives ordered word formation.

It does not.  The failure is not caused by an arbitrary completion: it is forced by prime-log
crowding and persists through every finite logarithmic differential calculus.

## 2. Ordered source response

Retain the source of ULF-SRSM-2:

\[
 Le_n=(\log n)e_n,\qquad S_te_n=n^{-t}e_n,\qquad V_me_n=e_{mn},
\]

and the source-normalized intervention letters

\[
 A_m=[L,V_m]=(\log m)V_m.
\]

For `m,n>=2`, put

\[
 a=\log m,\qquad b=\log n
\]

and let the normalized ordered defect on the vacuum be

\[
 \widetilde\Omega_{m,n}(t)e_1
 =ab\,\omega_t(a,b)e_{mn},
 \tag{FGP.1}
\]

where

\[
 \omega_t(a,b)=
 \int_{\substack{u,v\ge0\\u+v\le t}}
 e^{-(a+b)u}\bigl(e^{-bv}-e^{-av}\bigr)\,du\,dv.
 \tag{FGP.2}
\]

For `t>0`, its sign is `sgn(a-b)` and it vanishes exactly when `a=b`.

### Lemma 2.1 — universal relative-scale bound

If `0<a<b`, then for every `t>=0`,

\[
 \boxed{
 0< -ab\,\omega_t(a,b)
 \le \frac{b-a}{a}}
 \qquad(t>0\text{ for the strict inequality}).
 \tag{FGP.3}
\]

### Proof

For `v>=0`, the mean-value theorem gives

\[
 0<e^{-av}-e^{-bv}
 \le (b-a)v e^{-av}
 \qquad(v>0).
\]

Enlarge the integration triangle in `(FGP.2)` to the positive quadrant.  Then

\[
\begin{aligned}
 ab|\omega_t(a,b)|
 &\le ab(b-a)
   \int_0^\infty e^{-(a+b)u}\,du
   \int_0^\infty v e^{-av}\,dv\\
 &=\frac{b(b-a)}{a(a+b)}
 \le\frac{b-a}{a}.
\end{aligned}
\]

The sign statement from ULF-SRSM-2 gives strict positivity for `t>0`.  QED.

The infinite-horizon value makes the geometry visible:

\[
 \boxed{
 \lim_{t\to\infty}ab\,\omega_t(a,b)=\frac{a-b}{a+b}.}
 \tag{FGP.4}
\]

Indeed the two variables separate after replacing the triangle by the quadrant.  Thus ordered
memory measures **relative logarithmic separation**, not total logarithmic grade.

There is a stronger exact factorization.  For `Re z>0`, the Laplace transform in formation time is

\[
 \boxed{
 \int_0^\infty e^{-zt}\,ab\omega_t(a,b)\,dt
 =\frac{ab(a-b)}{z(z+a)(z+b)(z+a+b)}.}
 \tag{FGP.4a}
\]

To prove it, interchange the positive absolutely convergent integrals.  Integration over
`t>=u+v` contributes `z^(-1)e^(-z(u+v))`; the remaining two integrals are geometric and give

\[
 \frac{ab}{z(z+a+b)}
 \left(\frac1{z+b}-\frac1{z+a}\right).
\]

Thus the relative-scale factor `a-b` is present before every observer contraction.

Finite time differentiation does not remove it.  For every `k>=0` there is `C_k>0` such that
whenever `1<=b/a<=2`,

\[
 \boxed{
 \sup_{t\ge0}\left|
 \frac{d^k}{dt^k}\bigl(ab\omega_t(a,b)\bigr)
 \right|
 \le C_k a^{k-1}(b-a).}
 \tag{FGP.4b}
\]

For a direct proof set `r=b/a`, `U=au`, `V=av`, and `tau=at`.  Then

\[
 ab\omega_t(a,b)=rG_r(\tau),
\]

where

\[
 G_r(\tau)=\int_{U,V\ge0,\ U+V\le\tau}
 e^{-(1+r)U}(e^{-rV}-e^{-V})\,dU\,dV.
\]

On `1<=r<=2`, every `tau` derivative of `G_r` and its `r` derivative is uniformly bounded on
`tau>=0`: differentiation produces finite sums of polynomial--exponential boundary terms with
decay at least `e^(-tau)`.  Since `G_1=0`, the mean-value theorem gives
`|partial_tau^k G_r|<=C_k|r-1|`.  Rescaling contributes `a^k`, proving `(FGP.4b)`.

## 3. Source-certified crowded prime pairs

The already formalized corpus theorem

`RHTower.exists_prime_log_in_shrinking_window`

supplies constants `c,K,y_0>0` such that every sufficiently large logarithmic window

\[
 [R,R+\eta_R],\qquad
 \eta_R=K\exp(-cR^{1/10}),
 \tag{FGP.5}
\]

contains a prime logarithm.  Applying the same theorem at `R+2eta_R`, with the same window width,
is legal because the lower admissible width decreases with the base point.  Consequently, for all
sufficiently large `R` there are distinct primes `p_R,q_R` with

\[
 R\le a_R:=\log p_R\le R+\eta_R,
 \]

\[
 R+2\eta_R\le b_R:=\log q_R\le R+3\eta_R.
 \tag{FGP.6}
\]

In particular,

\[
 0<b_R-a_R\le3\eta_R,
 \qquad
 \boxed{
 \sup_{t\ge0}|a_Rb_R\omega_t(a_R,b_R)|
 \le \frac{3K}{R}e^{-cR^{1/10}}.}
 \tag{FGP.7}
\]

Choose an increasing sequence `R_j` with disjoint intervals `[R_j,R_j+3]`.  The resulting prime
pairs are disjoint, so the products `p_jq_j` are distinct.

No unproved prime-gap conjecture enters `(FGP.6)`.  The input is the corpus's unconditional
power-log prime-number theorem and its certified shrinking-window consequence.

## 4. Finite diagonal differential prolongations still fail

Let

\[
 \mathcal D=\{(P_1,k_1),\ldots,(P_M,k_M)\},
 \qquad P_\ell\in\mathbb C[X,Y],\quad k_\ell\in\mathbb N,
\]

be any finite differential family containing `(P_1,k_1)=(1,0)`.  It represents the finite
diagonal logarithmic differential calculus generated by polynomial functions of the two source
grades and finitely many formation-time derivatives.

Fix `T>0`.  Define the joint depth-two response on the standard basis `(f_j)` of `ell^2(N)` by

\[
 \mathcal R^{(2)}_{T,\mathcal D}f_j
 =\Bigl(
  P_\ell(a_j,b_j)
  \frac{d^{k_\ell}}{dt^{k_\ell}}
  \bigl(a_jb_j\omega_t(a_j,b_j)\bigr)e_{p_jq_j}
 \Bigr)_{\ell=1}^M
 \tag{FGP.8}
\]

in

\[
 \bigoplus_{\ell=1}^M
 L^2([0,T];\ell^2(\mathbb N_{\ge1})).
\]

Let `s_j` denote the norm of `(FGP.8)`.

### Theorem 4.1 — formation-grade properness inversion

For every `T>0` and every finite `mathcal D` containing `(1,0)`:

1. `s_j>0` for every `j`;
2. `s_j->0`;
3. `mathcal R^(2)_(T,mathcal D)` extends to an injective compact operator;
4. its range is dense and nonclosed in the closed span of its normalized response channels;
5. its inverse cost on the `j`-th unit response is `s_j^(-2)->infinity`.

Hence no finite diagonal logarithmic/time-differential prolongation family gives a positive lower
response bound at formation grade two.

### Proof

Since `P_1=1` and `omega_t(a_j,b_j)` is nonzero for every `t>0`, one has `s_j>0`.

For a polynomial `P` of degree `d`, there is a constant `C_P` such that for `R>=1` and
`a,b in [R,R+3]`,

\[
 |P(a,b)|\le C_P R^d.
\]

Let `D=max deg P_l`, `kappa=max k_l`, and absorb the finite coefficient sum and the constants from
`(FGP.4b)` into one constant `C_D`.  Equations `(FGP.4b)` and `(FGP.6)` give

\[
 \boxed{
 s_j\le
 3\sqrt T\,C_DK
 R_j^{D+\kappa-1}e^{-cR_j^{1/10}}
 \longrightarrow0.}
 \tag{FGP.9}
\]

Stretched-exponential decay dominates every polynomial.  The output subspaces belonging to
different `j` are orthogonal because the integers `p_jq_j` are distinct.  Therefore

\[
 \|\mathcal R^{(2)}_{T,\mathcal D}x\|^2
 =\sum_j|x_j|^2s_j^2.
 \tag{FGP.10}
\]

The positive diagonal entries prove injectivity.  Their convergence to zero proves compactness and
failure of every lower bound.  Finite-support response vectors are in the range and dense in the
declared response carrier.  Closed range would force a lower bound on the kernel complement, so
the range is nonclosed.  The inverse formula from `(FGP.10)` gives cost `s_j^(-2)`.  QED.

### Corollary 4.2 — bounded processing cannot repair the wall

If `B` is any bounded post-processing of the joint depth-two response and `C` any boundedly
invertible change of control coordinates, set

\[
 x_j=\frac{C^{-1}f_j}{\|C^{-1}f_j\|}.
\]

Then `norm(x_j)=1` and

\[
 \|B\mathcal R^{(2)}_{T,\mathcal D}Cx_j\|
 \le \|B\|\,\|C\|\,s_j\longrightarrow0.
\]

In particular, no bounded endpoint reporter or
finite-dimensional augmentation that factors through this response restores depth-two
properness.  The same conclusion applies to any common recovery whose induced map on this Hilbert
response carrier is bounded.  A positive Gram records the same collapse through the squared
singular values.

This is the ideal property of compact operators; the displayed estimate also proves it directly.

### Corollary 4.3 — every successful diagonal repair is singular

Suppose diagonal weights `w_j` make the constant channel `P_1=1` bounded below by `alpha>0`.
Then `(FGP.7)` forces

\[
 \boxed{
 |w_j|\ge
 \frac{\alpha R_j}{3\sqrt T K}
 e^{cR_j^{1/10}}.}
 \tag{FGP.11}
\]

For a finite differential family of maximal polynomial degree `D` and derivative order `kappa`,
the analogous necessary growth is a positive
constant times

\[
 R_j^{1-D-\kappa}e^{cR_j^{1/10}}.
\]

Thus the missing operation cannot be another finite logarithmic derivative.  It must be singular
in relative scale, infinite-order, or non-diagonal across crowded scales.

## 5. The properness spectrum is a field invariant

For a generated response grade `r`, define

\[
 \alpha_r(T)=inf\{\|\mathcal R_T^{(r)}x\|:
  \|x\|=1,\ x\perp\ker\mathcal R_T^{(r)}\}.
 \tag{FGP.12}
\]

The arithmetic source satisfies

\[
 \boxed{
 \alpha_1(T)\ge b_2(T)>0,
 \qquad
 \alpha_2(T)=0}
 \tag{FGP.13}
\]

for every positive horizon, where grade two includes any prescribed finite diagonal logarithmic
differential family `mathcal D` above.

This is the first exact **formation-grade properness inversion** in the programme.  Properness is
not a property of a source object or completion alone.  It is a spectrum indexed by generated word
grade, and closed range is not stable under response fusion.

## 6. Fusion of the five frontier walls

One literal theorem now exhibits all five frontier mechanisms without identifying them as one
scalar:

| frontier wall | depth-two response manifestation |
|---|---|
| singular source descent | every inverse frame needs the stretched-exponential weight `(FGP.11)` |
| all-prime oscillatory transport | relative prime-log gaps are small divisors |
| adaptive spectral orientation | minimizing channels move through crowded pairs `(p_j,q_j)` |
| whole-space coercivity | response is injective but compact with dense nonclosed range |
| positive carrier existence | the Gram exists, but its eigenvalues `s_j^2` tend to zero |

The theorem therefore adds unconditional leverage across the obstruction matrix: a successful
selection law must control the complete properness spectrum, not only the one-letter response or
any finite collection of its logarithmic jets.

## 7. Hypertranscendence and selection consequence

The result does **not** identify hypertranscendence with noncompactness.  It proves a narrower
statement that makes such a connection testable:

> no finite diagonal logarithmic/time-differential prolongation of the arithmetic response stably reconstructs ordered
> two-letter formation.

An infinite prolongation or singular source operation is therefore forced before a finite-response
null law could propagate to the complete word signature.  Any proposed RH selection mechanism
that factors only through finitely many polynomial logarithmic/time derivatives and bounded
recovered observers is structurally incapable of closing this grade-two wall.  A finite but
singular/non-polynomial source operation is not excluded.

The positive survivor is the graded properness spectrum `(FGP.12)`, together with the exact growth
law `(FGP.11)` for every possible diagonal repair.

## 8. Hostile conjecture loops

1. **One-letter source normalization makes the full signature proper. — False.**  Equation
   `(FGP.13)` gives the exact counterexample.
2. **Every finite ordered pair remains nonzero, so the pair atlas is globally reconstructible. —
   False.**  Algebraic injectivity coexists with compact nonclosed range.
3. **Enough logarithmic or time derivatives repair pair crowding. — False for every finite
   diagonal differential family.**
   Stretched-exponential prime-log crowding beats every polynomial multiplier.
4. **A positive Gram removes the issue. — False.**  It records the collapsing singular values
   `s_j^2` and erases the orientation sign.
5. **A bounded common recovery or endpoint enlargement restores information. — False.**  Compactness
   survives bounded processing.
6. **No positive theorem survives. — False.**  The properness spectrum, exact compact phase, and
   necessary singular repair rate are unconditional invariants.

## 9. Literature and corpus boundary

- Chen--Fliess and Volterra word expansions are established response machinery.
- Kernel regularization for Volterra identification commonly chooses a prior kernel adapted to a
  system class; Xu--Mu--Chen, arXiv:2505.20747, is a current example.  Here no identification kernel
  is chosen: the arithmetic semigroup generates the response and the source's prime supply forces
  its singular spectrum.
- Gafni--Tao, arXiv:2505.24017, records current unconditional prime-number theorems in short
  intervals.  The present proof uses the stronger source-local interface already certified in the
  corpus, `exists_prime_log_in_shrinking_window`, rather than a conjectural prime-gap estimate.
- Compact injective operators with nonclosed range and polynomial-versus-stretched-exponential
  comparison are classical ingredients.

Corpus search found prime-gap energies, finite second-order spectral response, logarithmic
commutators, and the separate shrinking-window prime theorem.  It did not contain their exact
coupling into formation-grade properness inversion or the finite-prolongation no-go `(FGP.9)`.

## 10. Formal status and next gate

The prime-supply input is already Lean-certified in

`formal/GaloisForLFunctions/RHTower/ShrinkingWindowPrimeSupply.lean`.

Fully formalized, unconditionally: see the Lean certificate below.

The next gate is no longer “find another normalization.”  It is:

\[
 \boxed{
 \text{construct a source-native infinite or non-diagonal formation law whose response controls}
 \ \inf_r\alpha_r(T),}
 \tag{FGP.14}
\]

or prove that the singular growth forced by `(FGP.11)` is itself the selector.


## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.RelativeScaleDefectKernel`, `GaloisForLFunctions.HTGeometry.CrowdedPrimeLogPairs`, `GaloisForLFunctions.HTGeometry.FormationGradeChannels`, `GaloisForLFunctions.HTGeometry.FormationGradeProperness`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.RelativeScaleDefectKernel` (closed form of `ab ω_t(a,b)`, bounds, limit,
Laplace transform, time derivatives), `GaloisForLFunctions.HTGeometry.CrowdedPrimeLogPairs` (crowded prime pairs from
the certified shrinking-window supply), `GaloisForLFunctions.HTGeometry.FormationGradeChannels` (finite differential
families, depth-two channels, `(FGP.9)`) and `GaloisForLFunctions.HTGeometry.FormationGradeProperness` (the depth-two
response operator, Theorem 4.1, Corollaries 4.2–4.3, the properness spectrum).  Corpus inputs:
`RHTower.exists_prime_log_in_shrinking_window`, ULF-SRSM-2 (`PrimeShiftSource.defectKernel`,
`PrimeShiftSource.sign_defectKernel`, `PrimeShiftSource.orderedDefect_letter`,
`PrimeShiftSource.norm_normalizedDefect_vacuum_sq`, `PrimeShiftSource.comResponse`,
`PrimeShiftSource.profile_two_mul_le`), ULF-SRSM-1 (`globalProperness_tfae`, `invisibleKernel`),
`LpDiagonal.isCompactOperator_lpDiag`.

| Claim | Lean declaration |
|-|-|
| (FGP.1)–(FGP.2) normalized vacuum defect `ab ω_t(a,b) e_{mn}`, sign `sgn(a-b)`, zero iff `a = b` | `PrimeShiftSource.orderedDefect_letter`, `PrimeShiftSource.norm_normalizedDefect_vacuum_sq`, `PrimeShiftSource.sign_defectKernel`, `PrimeShiftSource.defectKernel_eq_zero_iff`, `PrimeShiftSource.defectKernel_eq` |
| closed form `ab ω_t = (a-b)/(a+b)(1-e^{-(a+b)t}) + e^{-at} - e^{-bt}` | `PrimeShiftSource.defectKernel_closed`, `PrimeShiftSource.simplexKernel_eq` |
| Lemma 2.1, (FGP.3) `0 < -ab ω_t(a,b) ≤ (b-a)/a` | `PrimeShiftSource.neg_defect_le`, `PrimeShiftSource.neg_defect_pos` |
| (FGP.4) `ab ω_t(a,b) → (a-b)/(a+b)` | `PrimeShiftSource.tendsto_defect_atTop` |
| (FGP.4a) Laplace transform `ab(a-b)/(z(z+a)(z+b)(z+a+b))`, `Re z > 0` | `PrimeShiftSource.laplace_defect` |
| (FGP.4b) `sup_t ∣∂_t^k(ab ω_t)∣ ≤ C_k a^{k-1}(b-a)` for `a ≤ b ≤ 2a` | `PrimeShiftSource.abs_iteratedDeriv_defect_le`, `PrimeShiftSource.iteratedDeriv_defect`, `PrimeShiftSource.scale_difference_le`, `PrimeShiftSource.derivConst` |
| (FGP.5)–(FGP.6) crowded prime pairs in `[R, R+η_R]`, `[R+2η_R, R+3η_R]` | `PrimeShiftSource.exists_crowded_prime_pair`, `PrimeShiftSource.crowdWidth`, `PrimeShiftSource.crowdWidth_antitone` |
| (FGP.7) `sup_t ∣a b ω_t(a,b)∣ ≤ 3η_R/R`; separated sequence with distinct `p_j q_j` | `PrimeShiftSource.CrowdedPairs`, `PrimeShiftSource.CrowdedPairs.nonempty`, `PrimeShiftSource.CrowdedPairs.abs_defect_le`, `PrimeShiftSource.CrowdedPairs.b_sub_a_le`, `PrimeShiftSource.CrowdedPairs.mul_injective` |
| §4 finite diagonal differential families containing `(1,0)`; (FGP.8) joint depth-two response | `PrimeShiftSource.DiffFamily`, `PrimeShiftSource.CrowdedPairs.channelCoeff`, `PrimeShiftSource.CrowdedPairs.responseVec`, `PrimeShiftSource.CrowdedPairs.depthTwoResponse`, `PrimeShiftSource.CrowdedPairs.depthTwoResponse_single` |
| Theorem 4.1(1) `s_j > 0` | `PrimeShiftSource.CrowdedPairs.singular_pos`, `PrimeShiftSource.CrowdedPairs.singular` |
| Theorem 4.1(2), (FGP.9) `s_j ≤ √T C_𝒟 R_j^{D+κ-1} η_{R_j} → 0` | `PrimeShiftSource.CrowdedPairs.singular_le`, `PrimeShiftSource.CrowdedPairs.tendsto_singular`, `PrimeShiftSource.norm_eval_le`, `PrimeShiftSource.tendsto_zpow_mul_crowdWidth` |
| (FGP.10) orthogonal outputs, `‖𝓡^{(2)} x‖² = ∑ ∣x_j∣² s_j²` | `PrimeShiftSource.CrowdedPairs.inner_responseVec_of_ne`, `PrimeShiftSource.CrowdedPairs.orthonormal_normalizedChannel`, `PrimeShiftSource.CrowdedPairs.norm_sq_depthTwoResponse` |
| Theorem 4.1(3) injective compact | `PrimeShiftSource.CrowdedPairs.depthTwoResponse_injective`, `PrimeShiftSource.CrowdedPairs.isCompactOperator_depthTwoResponse` |
| Theorem 4.1(4) dense nonclosed range in the channel carrier | `PrimeShiftSource.CrowdedPairs.closure_range_depthTwoResponse`, `PrimeShiftSource.CrowdedPairs.not_isClosed_range_depthTwoResponse` |
| Theorem 4.1(5) inverse cost `s_j^{-2} → ∞` | `PrimeShiftSource.CrowdedPairs.inverseCost_normalizedChannel`, `PrimeShiftSource.CrowdedPairs.tendsto_inverseCost` |
| Corollary 4.2 bounded processing: `‖B 𝓡^{(2)} C x_j‖ ≤ ‖B‖‖C‖ s_j` | `PrimeShiftSource.CrowdedPairs.bounded_processing_collapse` |
| Corollary 4.3, (FGP.11) constant-channel repair `∣w_j∣ ≥ α R_j e^{cR_j^{1/10}}/(3√T K)`; general family `R_j^{1-D-κ} e^{cR_j^{1/10}}` | `PrimeShiftSource.CrowdedPairs.diagonal_repair_const`, `PrimeShiftSource.CrowdedPairs.constChannelNorm_le`, `PrimeShiftSource.CrowdedPairs.diagonal_repair_family` |
| (FGP.12)–(FGP.13) properness spectrum `α_1(T) ≥ b_2(T) > 0`, `α_2(T) = 0` | `PrimeShiftSource.propernessConst`, `PrimeShiftSource.propernessConst_comResponse`, `PrimeShiftSource.propernessConst_depthTwoResponse`, `PrimeShiftSource.profile_pos` |

The time semigroup and kernels are as in ULF-SRSM-2.  §6 (frontier-wall table), §7 (consequences),
§8 (hostile loops, each answered by the theorems above), §9 (literature) and §10 (next gate
`(FGP.14)`) carry no further Lean obligation.

## Log

- 2026-08-14 — hostile attack on ULF-SRSM-2 found that one-letter properness is destroyed by
  ordered fusion.
- 2026-08-14 — combined exact Duhamel pair kernel with the corpus's certified shrinking prime-log
  windows; proved compact/nonclosed depth-two response and failure of every finite diagonal
  logarithmic/time-differential prolongation.
- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
