# Deninger prime-holonomy groupoid

- **ID:** `deninger-prime-holonomy-groupoid`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/Deninger program.md` · `deninger-arithmetic-cohomology-construction`
- **Statement:** The rational-Witt/absolute-\(\mathbb F_1\) source contains a non-homogeneous
  three-dimensional Riemann-surface lamination whose prime holonomy is locally the rectangular
  weight-one isogeny law and whose twisted leafwise complex realizes arithmetic cohomology.

## Goal

Construct the geometric source that simultaneously supplies prime orbits, Gamma fixed-point data,
cup/Poincaré duality, positive quaternionic Hodge theory, and the comparison with the already
formalized source quotient.  No Xi zero or divisor coordinate may enter the construction.

## Gates

- [x] 0 → 1  in-progress: exact frontier, source purity, and first hostile attacks recorded
- [ ] 1 → 2  fully-proven: complete construction and proof
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Exact frontier

- `[LITERATURE]` Deninger's rational-Witt suspension supplies compact packets of prime-period
  orbits but is infinite-dimensional; existence of a \(3\)-dimensional Riemann-surface
  sub-dynamical system meeting every packet is explicitly open.
- `[LITERATURE]` Generalized solenoids permit conformal exponent \(1\) and leafwise Hodge purity.
  Compact smooth manifolds do not.
- `[LITERATURE]` The rational-Witt/Kucharczyk--Scholze space retains multiplicative information but
  misses Steinberg relations; the true coefficient complex must restore additive descent.
- `[LITERATURE]` Deninger's 2025 finite-flat/\(h\)/\(qfh\) sheafification identifies the
  sheafified reduced monoid algebra with \(W_{\mathrm{rat}}\) on the relevant normal/Dedekind
  sources.  It therefore does not by itself repair the missing Steinberg relations.  Deninger
  explicitly asks for descent stronger than Galois descent to recover more additive structure.
- `[LITERATURE]` Arithmetic degree-one cohomology cannot have a functorial real structure.  It must
  use twisted complex leafwise cohomology valued in Deninger's \(K_{\mathbb R}\) category.
- `[LOCAL-RESEARCH]` `DAC_POISSON_ZETA_THREE_TERM_COHOMOLOGY`
  constructs the exact source-defined analytic target
  \(C^\bullet_{\mathrm{PZ}}\), with middle quotient
  \(M_\zeta=H_-/Z(H_\cap)\).  The remaining factors are the
  rational-Witt relevant-complex comparison and source-positive Hodge
  identification.
- `[LOCAL-RESEARCH]` `deninger-rectangular-quaternionic-hodge` proves that every moving rectangular
  prime germ already has a positive anti-linear \(\star^2=-1\) Hodge atom, and its
  half-density-centered action is unitary.  Global twisted descent, not local positivity, is now
  the obstruction.

## Failed conjecture chain

1. `[FALSIFIED]` An ordinary compact \(FDS^3\) realizes all prime lengths.
   Closed-orbit lengths lie in the finitely generated period group, whereas
   \(\{\log p\}\) has infinite integral rank.
2. `[FALSIFIED]` A local absolute-\(\mathbb F_1\) Tate curve is itself the prime flow model.
   Its time-\(\log p\) radial return is the identity, so it is a periodic packet with degenerate
   return, not a simple isolated orbit.
3. `[FALSIFIED]` One fixed rectangular elliptic curve supplies every prime Frobenius.
   Its multiplication-by-\(p\) map has degree \(p^2\); a fixed elliptic endomorphism algebra cannot
   contain norm-\(p\) elements for every prime.
4. `[PAPER-PROVED] [BRIDGE]` Moving the rectangular modulus \(r\mapsto pr\) repairs the local
   degree and weight simultaneously; see `deninger-rectangular-isogeny-half-density`.
5. `[FALSIFIED]` The compact adelic two-solenoid
   \(S=(\mathbb A_\mathbb Q/\mathbb Q)^2\), with
   \(A_q=\operatorname{diag}(q,1)\), globalizes every rectangular
   tangent map.  It does not give the required suspension.  For
   \(K=S\times[1,2]\), every rational
   \(q\in[1/2,2]\) has \(Kq\cap K\ne\varnothing\); there are infinitely
   many such \(q\).  Hence the diagonal \(\mathbb Q_{>0}\)-action is not
   proper and the quotient is not the required Hausdorff lamination.
   The invariant second coordinate also leaves a clean, degenerate
   return direction.  The noncompact rational-Witt transversal is
   therefore load-bearing.

## Conjecture

`[CONJECTURE] [DAC_PRIME_HOLONOMY_GROUPOID]`:
there is a proper arithmetic holonomy groupoid \(\mathcal G_{\mathbb Z}\) internal to the corrected
rational-Witt/absolute-\(\mathbb F_1\) source with a compact \(C^{\infty,0}\)
three-dimensional laminated realization \(Y_{\mathbb Z}\) such that:

1. its two-dimensional leaves are oriented Riemann surfaces and its flow is transverse;
2. primitive closed orbits are indexed by primes, have length \(\log p\), and all positive iterates
   have Lefschetz sign \(+1\);
3. a prime holonomy germ moves rectangular modulus \(r\mapsto pr\) and is locally conjugate to
   \(F_p:E_r\to E_{pr}\), so the canonical leafwise metric has conformal weight \(p\);
4. the archimedean compactification has the single real fixed-point germ producing the
   \(\Gamma_{\mathbb R}\) distribution;
5. a canonical complex coefficient complex \(\mathscr K_{\mathrm{arith}}\), obtained from descent
   strictly stronger than the finite-flat/\(h\)/\(qfh\) sheafification of
   \(W_{\mathrm{rat}}\), restores the Steinberg relation and has no functorial real form; its odd
   cohomology carries the descended local rectangular anti-linear Hodge operator squaring to
   \(-1\);
6. reduced twisted leafwise cohomology admits a strict cup-isometric,
   flow-equivariant comparison with the source-defined Poisson--zeta
   complex \(C^\bullet_{\mathrm{PZ}}\), inducing
   \(H^1\simeq M_\zeta\), constructed before Mellin spectral
   decomposition or divisor evaluation.

## Hostile verdict

`SURVIVES PRELIMINARY ATTACK`, but only as a Stage-1 conjecture.  Conditions 1--4 are geometric and
prime-side.  Condition 5 is forced by Deninger's real-coefficient obstruction.  Condition 6 is the
first point at which circularity can enter: merely declaring the comparison cup-isometric is
equivalent to importing the missing Hodge theorem.  A valid proof must construct
\(\mathscr K_{\mathrm{arith}}\), its chain pairing, and the comparison
map to \(C^\bullet_{\mathrm{PZ}}\) from rational-Witt correspondences;
divisor coordinates are forbidden.

`[OPEN CORE]`: construct the additive/Steinberg descent complex
\(\mathscr K_{\mathrm{arith}}\) on the prime-holonomy groupoid and prove that the already
paper-proved local rectangular quaternionic Hodge atoms descend to it.  Positivity and
flow-unitarity are closed locally; remaining problem is global descent plus the cup-isometric
comparison.  This is stronger than selecting a finite-dimensional subsystem and cannot be
ordinary finite-flat/\(h\)/\(qfh\) sheafification, which returns \(W_{\mathrm{rat}}\).
The primary candidate mechanism is now
`deninger-milnor-witt-hodge-realization`: refine Deninger's ordinary finite correspondences to
arithmetic finite Milnor--Witt correspondences before real/analytic realization.  This places the
Steinberg relation and quadratic transfer in the source category.  The earlier
`deninger-metaplectic-steinberg-descent` remains only a possible later real-representation
pushout; it is not the arithmetic-cohomology construction.

## No-go closure

- **Exact killing mechanism:** finite-type periods, trivial local Tate return, and fixed quadratic
  endomorphism algebra each kill a homogeneous carrier.
- **Strongest positive survivor:** prime-dependent moving-modulus holonomy has the exact degree and
  conformal weight; its coefficient \(1/r\) and centered exponent \(1/2\) are forced, and its
  complexified tangent plane carries the required positive local quaternionic Hodge operator.
- **New insight:** finite-dimensionality must be local leaf dimension, not a homogeneous global
  endomorphism algebra.  Arithmetic complexity belongs in the totally disconnected holonomy
  transversal and twisted coefficient complex.  Compactifying that
  transversal before taking the dense rational suspension destroys
  properness.
- **Status:** local atom paper-proved; global groupoid and coefficient complex conjectural.

## Log

- 2026-07-26 — created after compact-period and fixed-fiber hostile audits.
- 2026-07-26 — finite-flat/\(h\)/\(qfh\) sheafification audited: it recovers
  \(W_{\mathrm{rat}}\), so it cannot be the missing additive correction.  Local rectangular
  quaternionic Hodge and centered-unitary laws paper-proved.
- 2026-07-26 — Deninger 2024's explicit \(R\alpha_*\mathscr G\) prescription and 2025
  finite-correspondence theorem isolate the coefficient problem.  Primary active conjecture
  switched from a metaplectic extension to arithmetic finite Milnor--Witt realization, which
  retains Steinberg and quadratic data before analytic completion.
- 2026-07-27 — Replaced the stale divisor-indexed comparison target by
  the source-defined Poisson--zeta complex and Meyer quotient.
- 2026-07-27 — Retired the compact adelic two-solenoid globalization:
  dense rational suspension is nonproper on any compact transversal.
