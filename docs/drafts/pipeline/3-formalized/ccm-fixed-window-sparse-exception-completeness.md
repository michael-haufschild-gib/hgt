# Exact fixed-window exceptional-carrier decomposition

- **ID:** ccm-fixed-window-sparse-exception-completeness
- **Stage:** 3-formalized
- **Type:** `[PROVED] [NOVELTY-PENDING]`
- **Source:** fixed-window logarithmic Weil tomography
- **Statement:** For every exceptional aperture set, RH is equivalent to finite Dirichlet energy of the actual negative Weil mass on that set together with one-sided subpower lower control on its complement.

## Goal

Replace the exact all-aperture lower-floor obligation in the Connes--CCM route by an exact positive
carrier decomposition.  A successful semilocal construction may allocate its negative defect to
an arbitrary exceptional set, provided the actual negative mass on that set has finite Dirichlet
energy and the complementary values have subpower one-sided loss.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, exact module build green, axiom audit PASS
- [x] 3 → 4  publication-ready: integrated into the standalone tomography paper

## Approach

For every (E\subset\mathbb N), let (q_{L,N}^-) be the negative part of the completed
fixed-window tail.  The exact theorem is
\[
 \mathrm{RH}\iff
 \left(\forall\varepsilon>0,\
   \sum_{n\in E}\frac{q_{L,N}(n)^-}{n^{1+\varepsilon}}<\infty\right)
 \land
 \left(\forall\delta>0,\ q_L(n)\ge-C_\delta n^\delta
   \text{ off }E\right).
\]
The reverse direction dominates the full negative part by the exact exceptional contribution
plus a subpower complement and invokes the negative-energy Landau gate.  Under RH both channels
vanish or are nonnegative.  Therefore false RH forces a universal dichotomy for every (E):
either the complementary subpower law fails, or the carried negative energy diverges on some line
to the right of one.

The earlier explicit corollary first proves the unconditional universal bound
\[
 |q_L(n)|\le M_L n^{1/2}
\]
on every admissible logarithmic sample, using the right-divisor fold and bounded observable remainder.  If \(E\subset\mathbb N\) has
\[
 \sum_{n\in E}n^{-1/2-\varepsilon}<\infty
 \qquad(\varepsilon>0),
\]
and \(q_L(n)\ge-C_\delta n^\delta\) off \(E\) for every \(\delta>0\), then the negative part of \(q_L\) is dominated by a subpower term plus the half-power exceptional majorant.  Its Dirichlet energy is finite on every line \(\Re s=1+\varepsilon\), so the existing negative-part energy gate yields RH.

The budget-matched corollary replaces the square-root exponent by any global exponent
\(\beta\): if \(|q_L(n)|=O(n^\beta)\), then it is enough that
\[
 \sum_{n\in E}n^{\beta-1-\varepsilon}<\infty
 \qquad(\varepsilon>0).
\]
Taking \(\beta=\delta_*\), the exact sharp transverse exponent of the same observable, gives a
self-calibrating theorem.  Under false RH every set carrying all non-subpower negative excursions
must have divergent \(\delta_*\)-weighted Dirichlet energy at some positive exponent.  The
half-power law is the unconditional divisor-independent corollary of \(\delta_*\le1/2\).

## Formal artifact

`formal/GaloisForLFunctions/RHTower/CCM/CCMRectangularSparseExceptionCompleteness.lean`

The exact module build and repository lint pass.  The checked capstones depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

## Remaining RH-bearing theorem

This theorem does not prove the prime/semilocal source estimate.  The Connes route must still
construct the completed fixed-window observable and prove the exact pair: off-exception subpower
lower control and finite Dirichlet energy of the actual negative mass carried by the exceptional
set.  The matched power-thickness law is a convenient sufficient envelope.  Alternatively it may
prove holomorphy of the cutoff-free Mellin continuation on \(\Re s>1\).

## Log

- 2026-07-13 — Candidate isolated after the exact one-sided exponent theorem showed that a uniform finite lower floor is stronger than necessary.
- 2026-07-13 — Strengthened to the arbitrary budget-matched and exact self-calibrating transverse-exponent forms; formal build, axiom audit, lint, and paper integration completed.
- 2026-07-13 — Strengthened again to the exact exceptional-carrier equivalence and universal false-RH carrier dichotomy.  The power and transverse thickness statements are now explicit outer envelopes of the actual negative-energy theorem.
