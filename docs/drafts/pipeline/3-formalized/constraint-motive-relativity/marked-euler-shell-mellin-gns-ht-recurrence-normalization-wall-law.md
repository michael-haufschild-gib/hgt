# Marked Euler-shell Mellin--GNS, HT, recurrence, and normalization-wall law

- **ID:** `cmr-marked-euler-shell-mellin-gns-ht-recurrence-wall`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / CROSS-DOCTRINE SOURCE COMPARISON
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LITERAL PRE-ZERO SOURCE]`
  `[HT/POSITIVE/SPECTRAL/RECURRENCE/MASS-WEIL WELD] [NORMALIZATION WALL]`
  `[NOT RH] [LEAN-FORMALIZED UNCONDITIONALLY]`
- **Formalized companion:**
  `marked-euler-shell-mellin-gns-ht-recurrence-normalization-wall-law-formalized.md` (same
  directory).
- **Statement:** One marked exponent-shell coefficient source has Mass/Weil/phase shadows that are
  coefficient-faithful on the marked pure-prime skeleton, positive Mellin--GNS and genuine HT
  realizations, compact-resolvent
  recurrent observed dynamics, and divergent lifted history; no single finite positive Hilbert
  normalization reaches its physical half-density prime fibre.

## 1. Source and scope

Let `E(n)=1`, let `M(n)=mu(n)`, and let

\[
 (\delta f)(n)=(\log n)f(n),
 \qquad \Theta_E=M*\delta E=\Lambda.
\tag{ESG.1}
\]

Fix an integer `m>=12`. For `n>=2`, put

\[
 M_{\max}(n)=\max_pv_p(n),
 \qquad a_m(n)=\mathbf1_{\{M_{\max}(n)=m\}},
 \qquad L=-\delta,
\tag{ESG.2}
\]

and set `a_m(1)=0`. Its Dirichlet source is

\[
 S_m(s)=\sum_{n\ge1}a_m(n)n^{-s}.
\tag{ESG.3}
\]

All data precede a Xi zero or divisor specialization. The mark `a_m` and the free commutative
prime-monoid grading are load-bearing. An unmarked list of pure-prime values does not determine
arbitrary mixed-shell coefficients.

## 2. Pure-power recovery and finite naturality

For every prime `p` and `k>=0`,

\[
 (L^ka_m)(p^m)=(-m\log p)^k.
\tag{ESG.4}
\]

Hence

\[
 \Theta_E(p)=\log p=-\frac1m(La_m)(p^m).
\tag{ESG.5}
\]

For a finite prime set `F`, let `H_F=C^F` with basis `(e_p)`, and define

\[
 D_Fe_p=(\log p)e_p,
 \qquad v_F(p)=\frac{\log p}{\sqrt p},
 \qquad U_F(t)=e^{-itD_F},
 \qquad h_F(t)=(-t\log p)_{p\in F}.
\tag{ESG.6}
\]

Then

\[
 v_F(p)=-\frac{(La_m)(p^m)}{m\sqrt p},
\tag{ESG.7}
\]

\[
 (-D_Fv_F)(p)
 =-\frac{(\log p)^2}{\sqrt p}
 =-\frac{(L^2a_m)(p^m)}{m^2\sqrt p},
\tag{ESG.8}
\]

and

\[
 p^{-it}=\exp\!\left(\frac{it}{m}(La_m)(p^m)\right).
\tag{ESG.9}
\]

The three right sides are respectively the primitive-prime Mass half-density coefficient, the
positive-location coefficient of the reflection-odd Weil tangent, and the prime phase.

If `E subset F`, coordinate restriction `r_(E,F):H_F->H_E` commutes with `D`, `v`, `U`, `h`, and
the marking `p->p^m`, and restrictions compose. Thus `(ESG.7)`--`(ESG.9)` form a genuine
coefficient-faithful pro-natural comparison on the marked pure-prime skeleton. Equation `(ESG.5)`
recovers each prime logarithm. The definition `(ESG.2)`, together with unique factorization, then
reconstructs the full marked shell source.

### Proof

Since `a_m(p^m)=1`, applying the diagonal operator `L=-delta` repeatedly gives `(ESG.4)`.
Equations `(ESG.5)`--`(ESG.9)` follow by substitution. Coordinate projections commute with every
diagonal formula, and their composition is ordinary coordinate restriction. Unique factorization
computes `M_max(n)` from the marked prime exponents, so `(ESG.2)` determines every mixed-shell
coefficient. QED.

## 3. Mass/Weil moment object and affine successor

For `r>=0`, define

\[
 \mu_r(F)=\langle v_F,D_F^rv_F\rangle
 =\sum_{p\in F}\frac{(\log p)^{r+2}}p.
\tag{ESG.10}
\]

Then the source comparison is

\[
 \mu_r(F)=\frac{(-1)^r}{m^{r+2}}
 \sum_{p\in F}\frac{(L^{r+2}a_m)(p^m)}p.
\tag{ESG.11}
\]

For `R>=0`, let `H_R(F)=(mu_(i+j)(F))_(0<=i,j<=R)`. Then

\[
 \operatorname{rank}H_R(F)=\min(R+1,|F|).
\tag{ESG.12}
\]

The full marked source fixes every successor moment, but a truncated face through `mu_(2R)` does
not determine `mu_(2R+1)` among positive atomic sources.

### Proof

Equation `(ESG.11)` follows from `(ESG.4)`. For `c=(c_0,...,c_R)`,

\[
 c^*H_R(F)c
 =\sum_{p\in F}\frac{(\log p)^2}{p}
   \left|\sum_{i=0}^Rc_i(\log p)^i\right|^2.
\tag{ESG.13}
\]

The nodes `log p` are distinct, so the weighted Vandermonde matrix has rank
`min(R+1,|F|)`, proving `(ESG.12)`.

For nonuniqueness, choose `2R+2` distinct prime-log nodes `x_j`. The Vandermonde rows
`0,...,2R` have a nonzero real kernel vector `c`, while the next row does not kill `c`, because
the full square Vandermonde matrix is invertible. For positive weights `w_j`, choose `epsilon>0`
small enough that `w_j+epsilon c_j` and `w_j-epsilon c_j` stay positive. The two positive atomic
measures have identical moments through order `2R` and distinct moment `2R+1`. QED.

## 4. Full positive shell and Mellin--GNS realization

Fix real `sigma>1` and define the finite positive measure

\[
 \mu_{m,\sigma}
 =\sum_{n\ge1}a_m(n)n^{-\sigma}\delta_{\log n},
 \qquad Z_{m,\sigma}=S_m(\sigma),
 \qquad P_{m,\sigma}=Z_{m,\sigma}^{-1}\mu_{m,\sigma}.
\tag{ESG.14}
\]

Let

\[
 \mathcal H_{m,\sigma}=L^2(P_{m,\sigma}),
 \qquad \Omega=1,
 \qquad (Df)(x)=xf(x),
 \qquad U_t=e^{-itD}.
\tag{ESG.15}
\]

The marked pair `(Z,P)`, equivalently the unnormalized measure `mu`, is coefficient-faithful:

\[
 a_m(n)=n^\sigma\mu_{m,\sigma}(\{\log n\})
       =Z_{m,\sigma}n^\sigma P_{m,\sigma}(\{\log n\}).
\tag{ESG.16}
\]

Its exact observer comparisons are

\[
 \int x^r\,d\mu_{m,\sigma}(x)=(-1)^rS_m^{(r)}(\sigma),
\tag{ESG.17}
\]

\[
 \langle D^i\Omega,D^j\Omega\rangle
 =\frac{(-1)^{i+j}S_m^{(i+j)}(\sigma)}{S_m(\sigma)},
\tag{ESG.18}
\]

and

\[
 \langle\Omega,U_t\Omega\rangle
 =\frac{S_m(\sigma+it)}{S_m(\sigma)}.
\tag{ESG.19}
\]

Every finite Hankel block in `(ESG.18)` is positive definite.

### Proof

Absolute convergence follows from `0<=a_m(n)<=1` and `sigma>1`. The logarithm is injective on
positive integers, proving `(ESG.16)`. Termwise differentiation in the absolute-convergence
half-plane gives `(ESG.17)`; `(ESG.18)` and `(ESG.19)` are direct GNS integrals. A nonzero
polynomial has finitely many real zeros, while the support contains `log(p^m)` for every prime.
Its squared norm against `P` is therefore positive, proving strict Hankel positivity. QED.

## 5. Compact-resolvent recurrence with open lifted history

The multiplication operator `D` in `(ESG.15)` has compact resolvent. Every `D^kOmega` lies in
`H_(m,sigma)`. The orbit `{U_tOmega:t in R}` has compact norm closure and returns arbitrarily close
to `Omega` at arbitrarily large positive times. Nevertheless the unwrapped logarithmic history

\[
 \widetilde h_t=-tD\Omega
\tag{ESG.20}
\]

satisfies

\[
 \|\widetilde h_t\|^2
 =t^2\frac{\int x^2\,d\mu_{m,\sigma}(x)}{Z_{m,\sigma}}
 \longrightarrow\infty.
\tag{ESG.21}
\]

### Proof

The atoms `log n` have finite multiplicity and escape to infinity, so the diagonal resolvent has
entries tending to zero and is compact. Exponential summability implies
`sum a_m(n)n^(-sigma)(log n)^(2k)<infinity`, so `D^kOmega` is admitted.

Write `P_n=P({log n})`. The orbit lies in the image of the product torus under

\[
 (z_n)_n\longmapsto(\sqrt{P_n}z_n)_n.
\]

This map is norm-continuous: a finite head is continuous and the squared norm of every tail is
bounded uniformly by its probability mass. The product torus is compact, so the orbit closure is
compact. Simultaneous approximation on a finite head gives arbitrarily large return times; the
uniformly small tail upgrades them to norm returns. Equation `(ESG.21)` is immediate from
`(ESG.20)` and the strictly positive finite second moment. QED.

## 6. Genuine HT realization

The publication-ready shell theorem proves

\[
 S_m(s)=\zeta(s)H_m(s),
 \qquad
 H_m(s)=\zeta((m+1)s)^{-1}-\zeta(ms)^{-1},
\tag{ESG.22}
\]

initially on `Re s>1`. For `m>=12`, `H_m` extends holomorphically and without zeros to
`Re s>1/2`. Moreover `(H_m)_(m>=2)` is jointly differentially algebraically independent over the
differential field generated by `zeta` and all of its derivatives. In particular the marked
source `(ESG.2)` has a genuine analytic HT realization as well as the positive, spectral,
recurrent, and lifted-history realizations above.

This is a comparison theorem: it does not say recurrence, positivity, or compact resolvent causes
HT.

## 7. Normalization wall

No single finite positive normalization of `(ESG.14)` reaches the physical Mass half-density
prime fibre.

First,

\[
 H_m(1)=\zeta(m+1)^{-1}-\zeta(m)^{-1}>0,
\tag{ESG.23}
\]

so `S_m(sigma)=infinity` for real `sigma<=1`. Second, on the pure-power atom `p^m`, the
unnormalized shell mass is `p^(-m sigma)`, while the normalized GNS weight is
`Z_(m,sigma)^(-1)p^(-m sigma)`. Under the canonical coordinate realization of
`L^2(P_(m,sigma))`, the vector `m^(-1)D Omega` has pure-power coordinate

\[
 Z_{m,\sigma}^{-1/2}(\log p)p^{-m\sigma/2}
\tag{ESG.23a}
\]

at `p^m`. Matching the Mass vector `(log p)p^(-1/2)` up to one finite global normalization forces

\[
 m\sigma=1,
 \qquad \sigma=1/m\le1/12,
\tag{ESG.24}
\]

where the shell measure is infinite. Equivalently,

\[
 \sum_p\left|\frac{\log p}{\sqrt p}\right|^2
 =\sum_p\frac{(\log p)^2}{p}=\infty.
\tag{ESG.25}
\]

so the target Mass vector itself has divergent squared norm.

Thus the full positive shell lives in normalization fibres `sigma>1`, while physical Mass/Weil
half-density lives only as finite cutoff, pro/Tate, distributional, or otherwise renormalized
data. A transition between them must change normalization/completion doctrine; it cannot be an
ordinary bounded Hilbert gauge.

### Proof

For real `r>1`, `zeta(r)` is strictly decreasing, so `(ESG.23)` holds. Since `zeta` has its pole
at `1`, `(ESG.22)` and positivity show divergence at `sigma=1`; termwise comparison gives
divergence below it. Formula `(ESG.24)` compares the pure-power radial weights. Euler divergence
of `sum_p1/p`, or direct comparison on a tail, implies `(ESG.25)`. QED.

## 8. Sharp reporter nonfaithfulness

The pure-power prime reporter is faithful on the marked prime skeleton but not on an ambient
coefficient algebra. Changing a coefficient at a mixed shell atom such as `2^m3` while fixing all
`p^m` leaves `(ESG.7)`--`(ESG.9)` unchanged but changes the unnormalized measure and some higher
normalized moments/correlations; the normalized zeroth moment and the `t=0` correlation remain
`1`. This perturbation lies in the ambient positive coefficient cone, not in the singleton source
class determined by `(ESG.2)`.

A sufficient unrestricted datum is the full unnormalized measure, equivalently the weighted
coefficient monoid at known `sigma`. On the ambient positive coefficient cone, normalization
forgets global scale and disrupts additive restriction unless `Z` is retained. For the fixed
binary shell law, `P` together with the shell prior can recover `Z`; no minimality claim is made.

## 9. Higher-field consequences

1. **Normalization is a field coordinate.** Positive Mellin--GNS, physical half-density, and
   distributional/pro realizations occupy different normalization/completion fibres.
2. **HT is not observed noncompactness.** This genuinely HT source has compact-resolvent `D` and a
   norm-precompact recurrent orbit. Its unbounded directions are differential prolongation,
   universal lifted history, and singular degeneration toward `sigma=1`.
3. **Source comparison is parallel, not serial.** Prime Mass/Weil/phase and full-shell GNS/HT
   reporters are parallel shadows of one marked source. Prime-reporter data alone cannot
   reconstruct an ambient coefficient source. For the fixed shell `a_m`, mixed coefficients are
   recovered only after adjoining the global shell law
   `a_m(n)=1_(M_max(n)=m)`.
4. **Density and coercivity remain separate.** The full marked measure is coefficient-faithful in
   `sigma>1`; transport to half-density loses finite norm.
5. **No RH selector appears.** Nothing here forces a Xi zero to a line or nulls a source class.

This supplies a literal PCDG/CMR source chart combining genuine analytic HT, positivity,
compact-resolvent spectral geometry, recurrence, Mass/Weil prime data, and open lifted history,
with an exact comparison and a proved transition wall. It does not show that other route organs
factor through this shell source or establish a universal CMR constitution.

## 10. Conjecture/proof/failure loops

### Loop A — use one positive Hilbert fibre for every shadow

**Failed by `(ESG.23)`--`(ESG.25)`.** The positive shell needs `sigma>1`; physical half-density
forces `sigma=1/m` on pure powers.

**Survivor.** Fibre the geometry over normalization and completion; any crossing needs explicit
renormalized/Tate/distributional transition data.

### Loop B — HT should make the observed orbit noncompact

**Failed by Section 5.** The HT shell has compact resolvent and norm-precompact recurrent orbit.

**Survivor.** Locate HT in persistent differential rank. Noncompactness of another shadow must be
proved through a comparison; here it appears in lifted history and the singular normalization
wall.

### Loop C — prime reporters reconstruct the full source

**Failed on the ambient coefficient cone by Section 8.** Mixed shell atoms are invisible to
pure-power reporters. For the fixed binary shell, its global law supplies the missing mixed data.

**Survivor.** Prime-reporter data alone cannot reconstruct an ambient coefficient source. For the
fixed shell, adjoin the global shell law; for unrestricted coefficients, retain a sufficient full
weighted monoid/measure datum.

### Loop D — the common source should select the RH mechanism

**Failed as a research inference.** The theorem constructs comparisons and a wall, not an
annihilation, sign, or zero-location law.

**Survivor.** Use the source to constrain field transitions before asking for a later constitutive
equation.

## 11. Corpus and literature boundary

Exact corpus parents:

- `docs/drafts/pipeline/2-fully-proven/nomological-geometry-and-dynamics/dirichlet-maurer-cartan-mellin-orbit-law.md`;
- `docs/drafts/pipeline/2-fully-proven/nomological-geometry-and-dynamics/critical-euler-mass-weil-stokes-shadow-law.md`;
- `docs/drafts/pipeline/2-fully-proven/nomological-geometry-and-dynamics/euler-prime-orbit-prolongation-recurrence-polar-cofinal-law.md`;
- `docs/drafts/pipeline/4-publication-ready/positive-hypertranscendental-riemann-divisor-frame/main.tex`.

GNS, compact diagonal resolvents, simultaneous approximation, and moment Hankel/Vandermonde
factorization are classical. The content here is their exact marked-source comparison and the
normalization obstruction inside the HGT corpus. No external novelty claim is needed.

## 12. Lean-return note

Formalized unconditionally in Lean 4; see the companion certificate.  Formal parents reused:

- `formal/GaloisForLFunctions/RHTower/HighExponentShellClockMeasure.lean`;
- `formal/GaloisForLFunctions/RHTower/HighExponentShellClockMoments.lean`;
- `formal/GaloisForLFunctions/RHTower/HighExponentShellHypertranscendence.lean`;
- `formal/GaloisForLFunctions/HTGeometry/HankelBoundaryExtension.lean`;
- `formal/GaloisForLFunctions/HTGeometry/FiniteHankelBoundaryExtensionClass.lean`.

## Log

- 2026-08-09 — exact paper comparison and normalization wall closed; no Lean written or built.
- 2026-08-12 — formalized unconditionally in Lean 4 and promoted to stage 3.
