# Suzuki coherent causal fusion and Gamma weld

- **ID:** `suzuki-coherent-fusion-gamma-weld`
- **Stage:** 1 — in progress
- **Type:** CONJECTURE / GLOBAL SOURCE ASSEMBLY / CROSS-PRIME SCHUR COMPLETION
- **Scientific status:** `[CONJECTURE] [RH-BEARING] [SOURCE-SPECIFIC]`
- **Source:**
  `../2-fully-proven/new_scientific_knowledge/suzuki-causal-depth-frostman-transfer.md`,
  `../2-fully-proven/new_scientific_knowledge/suzuki-causal-depth-rectangular-caratheodory-growth.md`,
  `../2-fully-proven/new_scientific_knowledge/suzuki-rectangular-wall-gram-gate.md`,
  `../2-fully-proven/new_scientific_knowledge/suzuki-critical-entry-wall-quarter-shift-green-law.md`,
  Gamma cyclic measure, and rectangular Ward connector
- **Statement:** Start from compactly gated observer-free wall Grams carrying exact sharp prime
  cells, transport them through actual restricted-Weil boundary response into the coherently fused
  causal field, then identify centered Gamma projected covariance as division-free Robin--Gamma
  rectangular trace.

## Goal

Replace unspecified cross-prime correction in
`SUZUKI-RESOLVENT-RECTANGULAR-LIGHT-INTERTWINER` by one source-forced response to already identified
sharp wall source.  Proving source-to-response intertwining, trace identity, and uniformly
lower-semibounded residual feeds
`riemannHypothesis_of_suzukiRectangularHilbertWardDefect_eventually_bddBelow` and proves RH.

No Xi zero, Weil positivity, RH premise, fitted covariance, or numerical computation may enter.

## Forced coherent field

Fix `h,a>0`, put `alpha=ha/2`, and for every prime `p` define

```text
d_p=p^(-alpha),
r_p=p^(-(1/4+2 alpha)),
z_p(t)=exp(i t log(p)/2),
A_p=(h sqrt(h))^(-1) sqrt(log(p)) p^(-1/4)
      (p+1)^(-1) (1-d_p)^2.
```

The formalized causal-depth law gives the exact ray

```text
R_p(t)=sum_(e>=0) psi_t(p,e)=A_p z_p(t)/(1-r_p z_p(t)).       (1)
```

This ray is stronger than an `ell^2` wall coordinate.  Since `r_p<=2^(-1/4)<1`,

```text
|R_p(t)| <= C_h sqrt(log(p)) p^(-5/4)
          <= (C_h/2)(1+log(p))p^(-5/4).                      (2)
```

Both majorants in the last expression are zeta-Dirichlet summable.  Hence

```text
R(t)=sum_p R_p(t)                                             (3)
```

converges absolutely and uniformly in real height.  This is the first legal all-prime operation
which fuses both valuation depths and distinct primes before taking a square.

For every finite prime set `F`, and therefore in the absolutely convergent cofinal limit,

```text
|sum_(p in F) R_p(t)|^2
 =sum_(p,q in F) R_p(t) conjugate(R_q(t)).                    (4)
```

The `p!=q` entries in `(4)` are an actual source-derived cross-prime correction; they are neither
inserted nor obtained after FE light splitting.

The individual Frostman cap law gives `|R_p(t)|<=R_p(0)`.  Equality in the global triangle bound
forces equality for every ray.  Applying the already formalized two-prime phase-clock injection
to primes `2` and `3` yields

```text
|R(t)| <= R(0),
|R(t)| = R(0)  <->  t=0.                                    (5)
```

Thus `R(0)^2-|R(t-u)|^2` is a faithful, translation-invariant, nonnegative global height
separator.  Unlike the S63 pair profile, its square contains the cofinal cross-prime terms required
by the Xi trace.

Exact sharp-support audit imposes a source-type correction.  `R_p` is an observer-dressed response
and has nonzero tails at every prime; it cannot itself be the compact sharp prime cell.  The
arithmetic input is instead

```text
G_(L,a,e)(t,u)=R_(L,a)(log(p^(e+1)))
                 omega_e(t) conjugate(omega_e(u)),           (5a)
```

whose diagonal is exact von Mangoldt cell, FE anti-diagonal retains full delayed phase, and which
vanishes for `2a<log(p^(e+1))`.  Coherent field `(3)` remains candidate boundary-response carrier,
but actual restricted-Weil/Robin operator must be proved to transport `(5a)` into that response.

## Gamma sewing

Let `mu_Gamma` be the existing normalized Gamma cyclic measure and let
`c(t)=t^2-int t^2 dmu_Gamma` be its centered conductor coordinate.  Regard the bounded functions
`R_p` as vectors in `L2(mu_Gamma)`, center them, and set

```text
f_p=R_p-int R_p dmu_Gamma,
f_p^perp=f_p-<c,f_p>/||c||^2 c.                              (6)
```

Then, for every finite prime packet,

```text
K_Gamma(p,q)=<f_p^perp,f_q^perp>                             (7)
```

is positive semidefinite and is exactly the Schur complement of the centered conductor channel.
This is the positive architecture demanded by `GammaConductorSchurCapacity`: diagonal damping no
longer tries to pay a divergent scalar cost independently.  Cross-prime covariance is carried by
one common Gamma spectral variable before projection.  Formula `(7)` is a direct Hilbert
projection identity, not a positivity conjecture.

## `SUZUKI-COHERENT-FUSION-GAMMA-WELD` `[CONJECTURE]`

For one fixed rectangular width `L>0`, the actual division-free causal Weil--Robin boundary
observation takes compact gated wall Grams `(5a)` as arithmetic input and factors their response
through coherently fused field `(3)` before FE/Xi-real light splitting.  After centered Gamma
projection `(6)`, finite-aperture quadratic trace is `(7)` plus explicit sharp prime diagonal,
marked-halfgap, and holonomy blocks, with no duplicate source count.  On arithmetic aperture mesh
`a=log(n)/2`, remaining difference from Xi screw curvature is uniformly lower bounded.

This is not a disguised target-positivity premise: the carrier, fusion order, Gamma projection,
and allowed residual are fixed by `(1)`, the causal Green law, and the existing rectangular trace.
It is false if any one of the following occurs:

1. actual Robin observation fails to intertwine compact gated wall source with coherent causal
   response, or keeps distinct primes orthogonal after causal depth fusion;
2. coherent fusion is available only after projective division or FE light splitting;
3. centered Gamma projection does not reproduce the concrete polar--Gamma boundary term;
4. marked-halfgap or holonomy debt is not uniformly controlled on the projected graph domain;
5. the resulting Ward residual tends to `-infinity` on any admissible aperture sequence.

## Gates

- [x] 0 -> 1: source-pure coherent carrier and falsifiers isolated
- [x] exact prime-ray formula and Frostman cap already formalized
- [x] exact compact sharp prime source identified as gated wall-Gram diagonal
- [x] direct identification of infinite-tail fused ray with sharp trace cell ruled out
- [x] all-prime `ell^1` majorant proved on paper
- [x] cofinal cross-prime Gram expansion and faithful global cap proved on paper
- [x] Gamma conductor Schur payment identified as an actual covariance projection
- [x] formalize all-prime coherent fusion and global cap
- [ ] identify `(7)` with concrete Robin--Gamma rectangular trace
- [ ] pay marked-halfgap and holonomy graph debts
- [ ] prove Ward residual uniformly lower bounded
- [ ] RH

## Log

- 2026-07-22 — created after S63 collision audit; replaces unspecified cross-prime correction by
  coherent all-prime causal fusion followed by source Gamma projection.
- 2026-07-22 — all-prime `ell^1`, cofinal cross-prime Gram, FE reflection, and faithful global cap
  proved in `SuzukiCoherentCausalDepthFusion.lean`.  Open core reduced to concrete Gamma/Robin trace
  weld and rectangular Ward lower bound.
- 2026-07-22 — primewise fixed-width real-part sign proved after source demodulation; demodulator
  is exactly actual unstarred depth-zero Gamma--Euler boundary coordinate.  Trace weld must preserve
  this pairing before coherent cross-prime square; arbitrary scalar phase rotation is excluded.
- 2026-07-22 — sharp-support/source-degree audit corrected architecture: gated observer-free wall
  Gram is arithmetic source; coherent fused ray is boundary response.  Open core now includes exact
  restricted-Weil source-to-response intertwiner before Gamma covariance projection.
