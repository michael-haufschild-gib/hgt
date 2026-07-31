# Absolute-Euler Squared-Seam Sign Violation

- **ID:** `absolute-euler-squared-seam-sign-violation`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / RH-disproof source target
- **Scientific status:** `[CONJECTURE] [OPEN CORE] [NOVELTY UNVERIFIED]`
- **Source:** `../2-fully-proven/not_new_scientific_knowledge/seam-log-derivative-weld-identity.md`;
  `../2-fully-proven/not_new_scientific_knowledge/seam-log-markov-pick-rh-equivalence.md`;
  `../3-formalized/not_new_scientific_knowledge/completed-prime-gamma-moment-far-right-asymptotic.md`
- **Statement:** For `w > 1/2`, set
  `F(w)=xiLogDeriv(1/2+w)/w`. There exist `n >= 1` and `w > 1/2` for which
  `(-1)^n ((1/(2w)) d/dw)^n F(w) < 0`.

## Goal

Prove an unconditional violation using only the absolutely convergent Euler source, the
completed rational--Gamma source, and exact analytic inequalities. Such a violation implies
`not RiemannHypothesis`: under RH the centered canonical product gives

`F(w)=2 sum_gamma m_gamma/(w^2+gamma^2)`,

so every displayed alternating squared-coordinate derivative is nonnegative.

The proposed sign violation is stronger than `not RiemannHypothesis`; the converse is not
assumed. The research content is the source-derived negative sign, not the conditional endpoint.

## Protected Low-Order Gates

The theorem
`../3-formalized/squared-xi-low-order-complete-monotonicity-protected.md`
is now formalized unconditionally, and it protects the *derivatives themselves*, not only the
reciprocal-square atoms.  `RHTower.alternating_iteratedDeriv_squaredXiRadialField_pos` gives

`(-1)^n g^(n)(y) > 0` for every `y > 0` and every `0 <= n <= 18`,

where `g(y) = xi'(1/2+sqrt y)/(2 sqrt y xi(1/2+sqrt y))`, identified with the field by
`RHTower.squaredXiRadialField_eq`.  The bridge that was missing before is the analytic one:
termwise differentiation of the reflection-paired Hadamard trace, with a uniform
reciprocal-square majorant on the whole positive base ray
(`RHTower.hasDerivAt_xiShiftedReciprocalMoment`,
`RHTower.iteratedDeriv_squaredXiRadialField`).

In particular the former first-gate candidate is formally impossible
(`RHTower.xiRealLogDeriv_radial_gap_neg`, for every `w > 0`):

`w * deriv xiLogDeriv (1/2+w) - xiLogDeriv(1/2+w) < 0`.

The first order not protected by the original uniform orbit chamber was `n=14`; that order is now
closed on all of `y>0` rather than only far right
(`RHTower.alternating_iteratedDeriv_squaredXiRadialField_pos_orderFourteen`).  Any scalar
violation must have `n>=19`.

## Competing Moves and Discriminator

1. **Compact fixed-order gate.** Closed positively through order eighteen: the completed source
   excludes the only possible edge corner at orders fourteen through eighteen.
2. **Compact growing-order gate.** Retain a fixed safe base point and let `n>=14` grow. The source
   proof must control the cancellation between the pole leg and the von-Mangoldt leg before
   taking the high jet.
3. **Cofinal coupled gate.** Let both `n` and `w` grow, with a proved coupling selected by a
   saddle inequality for the completed source. This move survives only if low critical-line atoms
   are not automatically dominant in that scaling.

The discriminator is a rigorous source-side asymptotic or one-sided bound for the completed
expression. A move is killed if its proposed main term has the RH-compatible sign or if it merely
renames an existing Stieltjes/Hankel equivalence.

## Current Attack

Orders through eighteen are now closed globally, not merely far right. At order fourteen the
only atomwise failure chamber was
`1/5<(Re rho-1/2)^2<1/4`, `85<(Im rho)^2<100`; the formalized theta-source fourth-moment floor and
quartet trace comparison exclude that chamber unconditionally.  A sharpened exact theta floor
and endpoint-curvature certificate bound the complete fourth reciprocal trace by `9/25000`;
this also excludes the order-fifteen failure chamber
`1/5<(Re rho-1/2)^2<1/4`, `85<(Im rho)^2<104`.

A six-interval rational theta certificate further proves
`thetaCuspNormalizedEvenMoment 2>3/625`, improving the complete fourth reciprocal trace bound to
`7/25000`. The order-sixteen sector coefficient `118` necessarily shrinks the protected central
band from `u<=1/5` to `u<=9/50`; the completed source excludes the remaining corner
`9/50<u<1/4`, `85<v<118`. Hence every seventeenth reciprocal-power atom is positive.

A seven-interval rational theta certificate with fifth-order endpoint propagation now proves
`thetaCuspNormalizedEvenMoment 2>263/50000`, improving the complete fourth reciprocal trace bound
to `1/5000`. The order-seventeen sector coefficient `132` protects `u<=4/25` and `v>=132`; the
completed source excludes the residual corner `4/25<u<1/4`, `85<v<132`. Hence every eighteenth
reciprocal-power atom is positive.

The exact symbolic boundary floor `3/70<exp(-pi)` strengthens the same seven-interval certificate
to `thetaCuspNormalizedEvenMoment 2>269/50000` and the complete fourth reciprocal trace bound to
`9/50000`. The order-eighteen sector coefficient `147` protects `u<=7/50` and `v>=147`; the
completed source excludes the residual corner `7/50<u<1/4`, `85<v<147`. Hence every nineteenth
reciprocal-power atom is positive and the live scalar target starts at order `n>=19`.

The former compact order-fourteen search is retired.  Its far-right sector theorem and the
formalized compact-corner source exclusion together prove the compatible strict sign for every
`w>1/2`.

The paper theorem
`../2-fully-proven/needs-audit/squared-xi-radial-jet-reverse-bessel-source-alignment.md`
now gives the exact source operator at every order.  After positive rescaling, the order-`n`
target is

`Q_n(w)=sum_(j=0)^n (-1)^j*b_(n,j)*w^j*xiLogDeriv^(j)(1/2+w)`,

with positive reverse-Bessel coefficients `b_(n,j)`.  Every von Mangoldt jet then has the same
negative sign.  The pole and Euler terms must be regrouped first as the logarithmic derivative of
the already formalized pole-filled function `(s-1)*zeta(s)`.  For later orders the exact operator
remains a finite cancellation-preserving jet expression in `regularizedRiemannZeta`, the elementary
`1/s` term, and the digamma term.

No numerical search is part of this card. The next discriminator must be a symbolic
rational--digamma--von-Mangoldt inequality or an exact integral representation for an order at
least nineteen that preserves pole/Euler cancellation.

Two further source coordinates now constrain that discriminator.  The paper theorem
`../3-formalized/squared-xi-bose-log-cumulant-coordinate.md` rewrites every completed
jet as a half-Gamma polygamma term minus/plus cumulants of one strictly log-concave Bose-log law,
with the zeta pole retained inside its Mellin normalization.  This is the live compact-order
coordinate.

For growing order, the paper theorem
`../2-fully-proven/needs-audit/reverse-bessel-fixed-frequency-blindness.md` proves
`exp(-x)B_n(x)/b_(n,0)->1` at each fixed frequency.  Hence large order does not isolate `m=2` or
any finite Euler prefix: after normalization every fixed atom tends to weight
`Lambda(m)/sqrt(m)`, and the source mass escapes through a prime window growing with `n`.  Any
cofinal attack must control that moving window uniformly against the completed archimedean source.

The moving window is now explicit.  The paper theorem
`../2-fully-proven/needs-audit/squared-xi-radial-jet-chebyshev-window.md` identifies the polar jet
and the prime jet as the Lebesgue and Chebyshev--Stieltjes integrals of the same positive kernel.
At fixed `s=1/2+w>1`, its polar mass concentrates at
`log x=n/(s(s-1))+o(n)`.  Thus the growing-order core is a signed completed Chebyshev discrepancy
on one exponential prime window, including the trivial-zero/archimedean correction.

## Anti-Theatre Gate

- The seam-log Markov/Pick and Hankel criteria are already RH-equivalent; restating them is not
  progress.
- Complete monotonicity is only a necessary RH shadow, not an equivalent characterization. A
  source-derived negative derivative is useful because it is a one-way disproof certificate.
- Fixed coefficient prefixes, fixed-rank Hankel tests, isolated positive Euler frequencies,
  finite local repairs, and finite half-turn-repaired packets are already excluded by the source
  boundary cards attached to `seam-log-markov-pick-rh-equivalence.md`.
- The rational pole at `s=1` and the zeta logarithmic derivative cancel in the completed object.
  Termwise high-jet estimates that split this cancellation are invalid as an RH argument.

## Open Core

`[OPEN CORE]` Prove a strict negative order-`n` squared-coordinate derivative for some `n>=19`, or
a negative completed square test, directly from the absolute Euler plus rational--Gamma source.
The proof must preserve the completed cancellation and cannot use a zero off the critical line as
an input.

## Gates

- [x] 0 -> 1 in-progress: source-pure coordinate, unconditional disproof endpoint, competing moves,
  and a falsifying asymptotic discriminator are explicit.
- [x] Orders `0<=n<=13` excluded unconditionally by exact orbit geometry and the formal sector.
- [x] Order-fourteen far-right boundary proved on paper (`w^2>=8`).
- [x] Order-fourteen compact corner excluded and global atomwise strict positivity formalized.
- [x] Order-fifteen compact corner excluded and global atomwise strict positivity formalized.
- [x] Order-sixteen corrected compact corner excluded and global atomwise strict positivity
  formalized.
- [x] Order-seventeen compact corner excluded and global atomwise strict positivity formalized.
- [x] Order-eighteen compact corner excluded and global atomwise strict positivity formalized.
- [ ] Fixed-order far-right boundary formalized in Lean.
- [ ] Strict source-side sign violation proved on paper with no open dependency.
- [ ] Violation formalized and wired to `not RiemannHypothesis` in Lean.

## Log

- 2026-07-17 -- Created under the RH-false goal. The first move is to prove the far-right boundary,
  then attack only compact or growing-order completed-source regimes.
- 2026-07-17 -- The formal endpoint sector and exact squared-orbit derivative powers protect
  every order through thirteen on the entire ray. The first live scalar order is fourteen.
- 2026-07-17 -- The off-line quartet height floor protects order fourteen for `w^2>=8`; only the
  compact source window `1/4<w^2<8` remains.
- 2026-07-17 -- Derived the exact reverse-Bessel radial-jet operator.  All prime jets align with
  one negative sign, while the existing pole-filled zeta logarithmic derivative preserves the
  mandatory pole/Euler cancellation.  The live order-fourteen problem is now one finite regularized
  source-jet inequality.
- 2026-07-17 -- Recast the compact jet as a Bose-log cumulant difference and proved the Bose-log
  law strictly log-concave.  Proved separately that normalized reverse-Bessel weights are blind to
  every fixed Euler frequency, killing finite-prime localization in the growing-order move.
- 2026-07-17 -- Identified the exact pole--prime cancellation as one reverse-Bessel
  Chebyshev--Stieltjes discrepancy.  Its normalized polar kernel has a Gamma-mixture index with
  exact mode `j=n/s` and concentrates at the prime scale `log x=n/(s(s-1))`.
- 2026-07-17 -- Closed order fourteen globally: a source-side fourth-moment bound excludes the
  only possible edge corner.  The first live scalar order is now at least fifteen.
- 2026-07-17 -- Sharpened the exact first-theta-atom floor and Euler--Mascheroni endpoint budget.
  The resulting fourth-trace bound excludes the order-fifteen corner `85<v<104`, so every
  order-sixteen reciprocal-power atom is positive and the first live scalar order is at least
  sixteen.
- 2026-07-17 -- Extended the rational theta certificate to six intervals, obtaining normalized
  fourth moment `>3/625` and complete fourth trace `<7/25000`. Corrected the order-sixteen sector
  split to `u<=9/50`, excluded the residual corner `9/50<u<1/4`, `85<v<118`, and formalized strict
  positivity of every order-seventeen reciprocal-power atom. The first live scalar order is now
  at least seventeen.
- 2026-07-17 -- Strengthened endpoint propagation to fifth order across seven rational intervals,
  obtaining normalized fourth moment `>263/50000` and complete fourth trace `<1/5000`. Excluded
  the order-seventeen residual corner `4/25<u<1/4`, `85<v<132`, and formalized strict positivity
  of every order-eighteen reciprocal-power atom. The first live scalar order is now at least
  eighteen.
- 2026-07-17 -- Replaced the coarse `1/24<exp(-pi)` boundary floor by the exact symbolic bound
  `3/70<exp(-pi)`, obtaining normalized fourth moment `>269/50000` and complete fourth trace
  `<9/50000`. Excluded the order-eighteen residual corner `7/50<u<1/4`, `85<v<147`, and formalized
  strict positivity of every order-nineteen reciprocal-power atom. The first live scalar order is
  now at least nineteen.
- 2026-07-31 -- The protected range is now formalized at the level of the derivatives, not only of
  the reciprocal-square atoms (`RHTower.SquaredXiCompleteMonotonicity`, axioms clean).  The
  analytic bridge is the shift monotonicity `A = y + t > t`: every sector ratio the corpus proves
  for the unshifted atoms transfers verbatim to the shifted kernel at every `y > 0`, so orders
  fourteen through eighteen are closed on the whole positive ray with no far-right cutoff, and the
  order-fourteen compact window `1/4<y<8` is empty.  The remaining live scalar order is nineteen,
  which needs the order-twenty residual annulus
  (`XiCenteredOrderTwentyResidualAnnulusEmpty`) to be excluded unconditionally.
