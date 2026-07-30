# Wold--shell Euler activation square and the divisor blow-up

- **ID:** `wold-shell-euler-activation-square`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[PROVED HERE] [EXACT SOURCE BRIDGE] [NOT RH]`
- **Parents:**
  - `new_scientific_knowledge/wold-sieve-normal-cone-von-mangoldt-current.md`;
  - `mobius-fixed-current-von-mangoldt-critical-transport-weld.md`;
  - `bounded-exponent-poisson-strictness-emergence.md`;
  - `../4-publication-ready/riemann-divisor-prime-transfer-spectrum/main.tex`;
  - `../1-in-progress/polarized-critical-rees-corona-transgression-rh.md`;
  - `not_new_scientific_knowledge/shifted-euler-quotient-finite-tangent-prime-support-filtration.md`.
- **Statement:** One literal Euler deformation has the Wold/von-Mangoldt normal current as its
  zero-activation tangent, the positive bounded-exponent frame as its full-activation boundary,
  and zeta as its infinite-depth/full-activation corner.  Its local continuation at a zeta zero
  is a genuine blow-up chart.  Prime-transfer tomography is already visible in the first tangent,
  so the unresolved RH input is the polarized Gamma/co-Poisson transport to the exceptional
  divisor, not recovery of the transfer spectrum.

## Goal

Identify one source object which contains the recent Wold normal-cone theorem and the
high-exponent prime-transfer paper as different faces.  Use it to decide whether two-prime
tomography contributes a zero-exclusion mechanism or only reports a source character already
present before the Riemann divisor is formed.

The theorem below is unconditional on its half-plane of absolute convergence.  The local
divisor statement uses only ordinary meromorphic continuation and local factorization of zeta.
No RH-equivalent sign, boundedness, positivity, or fibre landing is assumed.

## 1. Source deformation

For \(n>1\), write
\[
 \omega(n)=\#\{p:p\mid n\},
 \qquad
 M(n)=\max_{p\mid n}v_p(n),
\]
and put \(\omega(1)=M(1)=0\).  For real \(h\geq0\), define
\[
 a_h(n)=\prod_{p\mid n}(1-p^{-h}),
 \qquad a_h(1)=1.
 \tag{1}
\]
The parameter \(h\) activates prime support: \(a_0(n)=0\) for every \(n>1\), while
\[
 \lim_{h\to\infty}a_h(n)=1.
 \tag{2}
\]

For an integer \(m\geq0\) and \(\operatorname{Re}s>1\), define
\[
 {\cal Z}_m(h,s)
 =
 \sum_{\substack{n\geq1\\M(n)\leq m}}
 a_h(n)n^{-s}.
 \tag{3}
\]
Absolute convergence follows from \(0\leq a_h(n)\leq1\).

## 2. Euler activation square

`[PAPER-PROVED] [WOLD_SHELL_EULER_ACTIVATION_SQUARE]`

For \(h\geq0\), \(m\geq0\), and \(\operatorname{Re}s>1\),
\[
 {\cal Z}_m(h,s)
 =
 \prod_p
 \left(
  1+(1-p^{-h})\sum_{k=1}^{m}p^{-ks}
 \right).
 \tag{4}
\]
Its four boundary faces are
\[
 \begin{aligned}
 {\cal Z}_m(0,s)&=1,\\
 {\cal Z}_\infty(h,s)
 :=\lim_{m\to\infty}{\cal Z}_m(h,s)
 &=\frac{\zeta(s)}{\zeta(s+h)},\\
 {\cal Z}_m(\infty,s)
 :=\lim_{h\to\infty}{\cal Z}_m(h,s)
 &=\frac{\zeta(s)}{\zeta((m+1)s)},\\
 {\cal Z}_\infty(\infty,s)&=\zeta(s).
 \end{aligned}
 \tag{5}
\]
Both iterated limits at the final corner agree on \(\operatorname{Re}s>1\).

### Proof

Unique factorization and multiplicativity of \(a_h\) give `(4)`.  At \(h=0\), every nonconstant
local term vanishes.  As \(m\to\infty\),
\[
 \begin{aligned}
 1+(1-p^{-h})\sum_{k\geq1}p^{-ks}
 &=
 1+(1-p^{-h})\frac{p^{-s}}{1-p^{-s}}\\
 &=\frac{1-p^{-(s+h)}}{1-p^{-s}},
 \end{aligned}
 \]
and the Euler product is \(\zeta(s)/\zeta(s+h)\).

For fixed \(m\), dominated convergence in `(3)` gives
\[
 {\cal Z}_m(\infty,s)
 =
 \sum_{M(n)\leq m}n^{-s}.
 \]
The local factor is
\[
 1+p^{-s}+\cdots+p^{-ms}
 =
 \frac{1-p^{-(m+1)s}}{1-p^{-s}},
 \]
so the product is \(\zeta(s)/\zeta((m+1)s)\).  Sending the remaining parameter to infinity gives
\(\zeta(s)\) in either order.  `QED`

The infinite-depth face has an exact cocycle and connection:
\[
 {\cal Z}_\infty(h+k,s)
 =
 {\cal Z}_\infty(h,s)\,
 {\cal Z}_\infty(k,s+h),
 \tag{6}
\]
\[
 \partial_h{\cal Z}_\infty(h,s)
 =
 A(s+h){\cal Z}_\infty(h,s),
 \qquad
 A(w)=-\frac{\zeta'(w)}{\zeta(w)}.
 \tag{7}
\]
Consequently,
\[
 \zeta(s)
 =
 \exp\!\left(\int_0^\infty A(s+u)\,du\right)
 \qquad(\operatorname{Re}s>1).
 \tag{8}
\]
Thus zeta is the infinite activation holonomy of the von Mangoldt connection.

## 3. Normal strata

Let \(r=\omega(n)\).  Each factor in `(1)` has expansion
\[
 1-p^{-h}=h\log p+O(h^2).
 \]
Therefore
\[
 \partial_h^j a_h(n)\big|_{h=0}=0\quad(j<r),
 \qquad
 \partial_h^r a_h(n)\big|_{h=0}
 =
 r!\prod_{p\mid n}\log p.
 \tag{9}
\]
The first normal stratum is exactly the prime-power stratum:
\[
 \partial_h a_h(n)\big|_{h=0}=\Lambda(n).
 \tag{10}
\]
After summation on the infinite-depth face,
\[
 \partial_h{\cal Z}_\infty(0,s)
 =
 \sum_{n\geq1}\frac{\Lambda(n)}{n^s}
 =
 -\frac{\zeta'(s)}{\zeta(s)}.
 \tag{11}
\]
Equation `(11)` is simultaneously the derivative of `(5)` and the trace of the all-prime Wold
normal jet already formalized in
`RHTower/WoldSieveNormalConeVonMangoldt.lean`.

This identifies the full finite-\(h\) germ as the nonperturbative completion of the
distinct-prime-support filtration.  Every fixed Taylor order sees only bounded \(\omega(n)\);
the full-activation boundary retains all support orders at once.

## 4. Depth shells and their tangent

Put
\[
 {\cal B}_m(h,s)={\cal Z}_m(h,s)-{\cal Z}_{m-1}(h,s)
 \qquad(m\geq1).
 \tag{12}
\]
At full activation,
\[
 \begin{aligned}
 {\cal B}_m(\infty,s)
 &=
 \frac{\zeta(s)}{\zeta((m+1)s)}
 -
 \frac{\zeta(s)}{\zeta(ms)}\\
 &=\zeta(s)H_m(s)
 =S_m(s).
 \end{aligned}
 \tag{13}
\]
This is exactly the positive high-exponent shell of the divisor-frame and transfer-spectrum
papers.

At zero activation, \({\cal B}_m(0,s)=0\), but its first normal derivative is
\[
 D_m(s)
 :=
 \partial_h{\cal B}_m(0,s)
 =
 \sum_p(\log p)p^{-ms}.
 \tag{14}
\]
Indeed, the first derivative permits one prime support only, and the depth difference retains
only exponent \(m\).

For every fixed \(s\) with \(\operatorname{Re}s>0\),
\[
 \frac{2^{ms}}{\log2}D_m(s)\longrightarrow1,
 \tag{15}
\]
and, after removing the prime-two atom,
\[
 \frac{3^{ms}}{\log3}
 \left(D_m(s)-(\log2)2^{-ms}\right)
 \longrightarrow1.
 \tag{16}
\]
For `(15)`, write the normalized remainder as
\[
 \sum_{p\geq3}\frac{\log p}{\log2}\left(\frac2p\right)^{ms}.
 \]
Once \(m\operatorname{Re}s\geq2\), its norm is dominated by the convergent series
\[
 \sum_{n\geq3}\frac{\log n}{\log2}\left(\frac2n\right)^2,
 \]
and every term tends to zero.  Dominated convergence proves `(15)`.  The same argument after
removing \(p=2\), with \(3/n\) and \(n\geq5\), proves `(16)`.

Hence
\[
 \frac{D_{m+1}(s)}{D_m(s)}\longrightarrow2^{-s},
 \tag{17}
\]
and the residual adjacent transfer tends to \(3^{-s}\).  After the same half-density
normalization used by the shell paper, the tangent characters are
\[
 2^{1/2-s},\qquad3^{1/2-s}.
 \tag{18}
\]

`[HOSTILE CONSEQUENCE]` Exact minimal-rank-two transfer tomography is already present in the
first Wold normal tangent `(14)`, before the shell acquires its common zeta divisor in `(13)`.
The transfer spectrum recovers \(s\), but it does not explain why a divisor point must satisfy
\(\operatorname{Re}s=1/2\).  It is a faithful reporter, not the missing producer.

## 5. The divisor is an exceptional blow-up boundary

The infinite-depth identity in `(5)` continues meromorphically as
\[
 {\cal Z}_\infty(h,s)=\frac{\zeta(s)}{\zeta(s+h)}.
 \tag{19}
\]
Let \(\rho\) be a nontrivial zeta zero of multiplicity \(d\).  On a sufficiently small
neighbourhood,
\[
 \zeta(s)=(s-\rho)^d u(s),
 \tag{20}
\]
where \(u\) is holomorphic and nonzero.  Therefore
\[
 {\cal Z}_\infty(h,s)
 =
 \left(\frac{s-\rho}{s+h-\rho}\right)^d
 \frac{u(s)}{u(s+h)}.
 \tag{21}
\]

`[PAPER-PROVED] [WOLD_ACTIVATION_DIVISOR_BLOWUP]`

The point \((h,s)=(0,\rho)\) has no ordinary continuous activation value compatible with both
faces:
\[
 {\cal Z}_\infty(0,s)=1\quad(s\ne\rho),
 \qquad
 {\cal Z}_\infty(h,\rho)=0\quad(h\ne0\text{ small}).
 \tag{22}
\]
On the blow-up chart \(h=\lambda(s-\rho)\),
\[
 {\cal Z}_\infty(\lambda(s-\rho),s)
 \longrightarrow(1+\lambda)^{-d}
 \qquad(s\to\rho),
 \tag{23}
\]
for \(\lambda\ne-1\).  Thus the missing divisor point fibre is not recovered by another ordinary
Hilbert completion.  It is the exceptional projective normal direction \([s-\rho:h]\) of the
activation/divisor corner.  This is a literal source realization of the Rees boundary predicted
by the completion-fracture corpus.

### Proof

Equations `(21)` and `(22)` are immediate from `(20)`.  Substitute
\(h=\lambda(s-\rho)\) into `(21)`.  The rational factor tends to
\((1+\lambda)^{-d}\), and \(u(s)/u(s+h)\to1\).  `QED`

## 6. What the transfer-spectrum paper changes

The paper
`riemann-divisor-prime-transfer-spectrum/main.tex` proves four valuable facts:

1. actual source masses \(h_m=H_m(1)\) supply the canonical half-density normalization;
2. prime two and prime three give the minimal faithful spectral coordinate;
3. local Julia residue and cofinal shell Lyapunov rate are the same signed charge; and
4. diagonal source--shell conservation is compatible with every off-line zero.

The activation square adds the missing placement of those facts:

```text
h=0 tangent:
  von Mangoldt current and the complete two-prime transfer spectrum;

finite h germ:
  all bounded prime-support interaction orders;

h=infinity boundary:
  positive exponent shells carrying the common zeta divisor;

(h,s)=(0,rho):
  non-Hausdorff corner repaired by the exceptional Rees/blow-up fibre;

Gamma/co-Poisson completion:
  must supply the positive dagger transport on that exceptional fibre.
```

Therefore the paper does not move the RH frontier by adding another detector.  Its source
normalization becomes useful because it fixes the positive metric on one boundary face of the
activation square.  What remains is a comparison theorem between independently fixed faces.

## 7. Sharpened RH-bearing conjecture

`[BOLD CONJECTURE] [XI_WOLD_ACTIVATION_BLOWUP_DAGGER_TRANSPORT]`

> Gamma completion, literal co-Poisson/Sonin boundary comparison, and Riemann reflection extend
> the ordinary-prime activation family `(3)` to a Hausdorff polarized correspondence on the
> blow-up of the reduced Xi divisor at \(h=0\).  The extension:
>
> 1. agrees with the Wold/von-Mangoldt connection `(7)` in the Euler chamber;
> 2. agrees with the source-normalized positive shell boundary `(13)` as \(h\to\infty\);
> 3. retains every reduced exceptional conormal fibre `(23)`;
> 4. identifies reflected backward activation with the positive adjoint of forward activation;
>    and
> 5. is contractive in both oriented activation directions for the independently fixed source
>    and Hardy polarizations.

On a retained one-dimensional Xi conormal at \(\rho\), prime activation has character
\[
 \chi_\rho(p)=p^{1/2-\rho}.
 \tag{24}
\]
Clause 4 gives inverse equal to adjoint, or equivalently the two inequalities
\[
 |\chi_\rho(p)|\leq1,\qquad|\chi_\rho(p)^{-1}|\leq1.
 \tag{25}
\]
Hence \(|\chi_\rho(p)|=1\), so \(\operatorname{Re}\rho=1/2\).  The conjecture therefore implies
RH.  The implication is elementary; construction of the source comparison is the entire
RH-bearing content.

`[OPEN CORE] [XI_GAMMA_COPOISSON_ACTIVATION_EXCEPTIONAL_TRANSPORT]`

Construct the completed two-variable source family off the divisor and prove that its
Gamma/co-Poisson continuation acts adjointably and two-sided contractively on the exceptional
normal module `(23)`.  The topology and polarization must be fixed from the Wold weights,
Gamma determinant, and Sonin/Hardy source maps before any zero is chosen.

This is more concrete than “find a third completion”: the underlying point-retaining completion
is the activation/divisor blow-up, and the sole missing theorem is its source-derived polarized
transport.

## 8. Hostile audit

1. Equations `(4)`--`(18)` are Euler-product and dominated-convergence mathematics.  Novelty, if
   any, lies in the exact corpus conjunction and blow-up placement, not the parent identities.
2. The blow-up retains off-line conormals as well as critical-line conormals.  It solves the point
   loss, not the line selection.
3. Reflection pairs exceptional fibres; it does not identify inverse with positive adjoint.
4. Any norm defined by pulling back along `(19)` makes the conjecture circular.
5. Contractivity after choosing \(\rho\) is exactly the independent-quadrant detector and proves
   nothing source-side.
6. Every finite \(h\)-jet remains a bounded \(\omega(n)\)-layer.  Grinding higher jets cannot
   prove the endpoint theorem.
7. The limits commute only in the Euler half-plane.  Passing the source polarization through
   meromorphic continuation and the exceptional boundary is the unresolved operation.
8. Generalized-prime off-line systems may possess analogous activation squares.  The conjecture
   requires the literal ordinary-prime Gamma/co-Poisson comparison, not positivity of `(3)` alone.
9. The arXiv identifier `1707.06610` is the physics paper *Quark matter may not be strange*; it
   supplies no theorem about this activation square or its exceptional transport.

## Literature boundary

A targeted exact-formula search found the classical parents separately: Euler products,
\(-\zeta'/\zeta\), bounded-exponent Euler quotients, support-count generating functions, and
zeta-ratio cocycles.  It did not locate the joint square `(4)`--`(18)`, its use as a literal
activation/divisor blow-up `(21)`--`(23)`, or the identification of the transfer spectrum as an
already-tangent invariant.  This is a preliminary noncollision report, not a priority claim.

## Gates

- [x] 0 → 1: source-pure object, exact formulas, falsifiers, and RH consumer isolated.
- [x] 1 → 2: activation square, normal strata, tangent spectrum, and local blow-up proved on paper.
- [ ] 2 → 3: formalize the finite Euler activation square and connect its first normal derivative
  to `hasDerivAt_woldIncidenceNormalFactor`; the infinite analytic faces remain the load-bearing
  Lean target.
- [ ] 3 → 4: no publication claim before broader literature audit and a nontrivial part of the
  exceptional Gamma/co-Poisson transport is constructed.

## Log

- 2026-07-30 — Audited the prime-transfer-spectrum paper against the Wold normal-cone and
  two-clock no-go corpus.  Constructed one Euler activation square containing both as boundary
  charts, proved that two-prime tomography already occurs in the first Wold tangent, identified
  the zeta divisor as a nonperturbative activation boundary, and proved its literal local
  blow-up normal form.  Replaced “find a third completion” by the typed
  `XI_GAMMA_COPOISSON_ACTIVATION_EXCEPTIONAL_TRANSPORT` open core.
