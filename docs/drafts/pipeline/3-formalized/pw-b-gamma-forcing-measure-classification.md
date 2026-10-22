# PW-B actual forcing: complete mass and measure classification

- **ID:** PW-B-GAMMA-FORCING-MEASURE-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** Both actual Gamma differential forcings are integrable in ray measure `dx`, with explicit affine masses and different zero-defect shifts. Both forcings and both potential terms are nonintegrable separately in log measure `dt`. Their complete connection responses are admitted derivatives of the original source, with zero `dt` mass at every shift. The same complete derivative has ray mass `-Gamma(3/2)`, so its ray-mass defect from the actual arithmetic current is `2*Gamma(3/2)`.

## Source, measure and exact moments

Keep `q(t)=exp(t/2-exp(t))`, `Q(x)=q(log x)` for `x>0`, the original
arithmetic current `E(x)`, and the two previously defined forcings

`rminus_z(t)=(-sinh(t)-z)*q(t)`,
`rplus_z(t)=(1-exp(t)-cosh(t)-z)*q(t)`.

The previous [current audit](pw-b-gamma-logarithmic-current.md) proves
`E in L1(dx)` and `integral E dx=Gamma(3/2)`.
All statements here distinguish ordinary Lebesgue `dx` on the positive
ray from ordinary Lebesgue `dt` on the full log line.

The actual source has three admitted complex moments:

`integral Q(x)/x dx=Gamma(1/2)`,
`integral Q(x) dx=Gamma(3/2)`,
`integral x*Q(x) dx=Gamma(5/2)`.

The inverse moment is proved directly from the convergent Gamma integral
at `1/2`, using the exact real-power identity, not continued across its
convergence boundary. The other moments come from the already-admitted
Gamma source. The Gamma recurrence gives
`Gamma(1/2)=2*Gamma(3/2)` and `Gamma(5/2)=3/2*Gamma(3/2)`.

## Ray masses and exact weak balance shifts

The existing forcings, pulled to the positive ray, decompose exactly as

`rminus_z(log x)=1/2*(Q(x)/x-x*Q(x))-z*Q(x)`,
`rplus_z(log x)=(1-z)*Q(x)-3/2*x*Q(x)-1/2*Q(x)/x`.

Each finite term is integrable in `dx`, so linearity is justified.
Their complete integrals are

`integral rminus_z(log x) dx=(1/4-z)*Gamma(3/2)`,
`integral rplus_z(log x) dx=(-9/4-z)*Gamma(3/2)`.

The exact defects from the arithmetic current are therefore

`integral (E-rminus_z o log) dx=(z+3/4)*Gamma(3/2)`,
`integral (E-rplus_z o log) dx=(z+13/4)*Gamma(3/2)`.

Since `Gamma(3/2)>0`, zero mass is equivalent to `z=-3/4` for the inverse
forcing and `z=-13/4` for the positive forcing. These are classifications
of this particular scalar test, not identifications with a spectral
coordinate. The [leading-forcing audit](pw-b-gamma-leading-forcing.md)
already proves that neither forcing equals the actual arithmetic current
pointwise at any complex shift, including these two shifts.

## Log-domain obstruction and complete positive survivor

There is no transfer of the preceding separate admissions to `dt`.
Direct exponential factorization gives

`exp(t/2)*rminus_z(t) -> 1/2`,
`exp(t/2)*rplus_z(t) -> -1/2`, as `t -> -infinity`, for every complex `z`.

The normalized expressions are quadratic polynomials in `exp(t)` times
`exp(-exp(t))`, so all limits are explicit. Since `exp(t/2)->0`, the
nonzero limits force a positive constant lower bound on each forcing's
norm over an infinite negative half-line. The corpus's half-line
nonintegrability theorem then excludes both raw forcings from `L1(dt)`.

Let `p(t)=cosh(t)-1/2`. The complete identities are still exact:

`(p(t)+z)*q(t)+rplus_z(t)=q'(t)`,
`(-p(t)+z)*q(t)+rminus_z(t)=q'(t)`.

The actual Gamma profile and its derivative are integrable on the log
line, by the corpus's positive-parameter Gamma derivative family. The
whole-line fundamental theorem for an integrable function and derivative
therefore gives `integral q'(t) dt=0`. Both complete connection sums are
integrable and have zero mass for every shift. Their potential terms
cannot be separately integrable: subtracting such an admitted term from
the admitted complete sum would contradict nonintegrability of the forcing.
Thus this complete cancellation cannot be expanded into integrals of its
pieces or interpreted as a condition selecting `z`.

The same complete derivative satisfies

`q'(log x)=1/2*Q(x)-x*Q(x)`.

It is integrable in `dx` with integral `-Gamma(3/2)`. The actual arithmetic
current consequently has exact complete-response defect

`integral (E(x)-q'(log x)) dx=2*Gamma(3/2)`.

The measure and complete source response both matter. Neither the raw
zero-defect shift nor the all-shift log-domain cancellation supplies the
missing arithmetic-to-spectral Ward identification.

## Route scope and next attack

Literal PW response -> FE imbalance -> positive Deninger Ward transmutation
-> independently source-forced fixed-grade balance -> RH remains the chain.
RH is unproved and PW-B remains active. This theorem closes a direct test
of the proposed complete source match: exact global masses, both admission
domains, the retained nonintegrable pieces, and the admitted positive survivor.

The next source-specific candidate must use the actual Möbius family and
its coefficient generator, or derive an independent compensating source
and physical pairing. Defining a forcing separately for each shift makes
the complete derivative identity true at every shift and supplies no
independent orientation law.

## Search and novelty audit

Three deep method searches and their candidate/source-argument/premise-group
metadata are saved in [search artifact](../1-in-progress/pw-b-gamma-forcing-measure-searches.json).
All reported partial coverage. The usable corpus methods were convergent
Gamma moments, finite source decomposition, exact exponential tail limits,
half-line nonintegrability, and the whole-line fundamental theorem.
Abstract signed-measure transfer requires finite measure and did not solve
this unbounded-domain problem. Generic tail upper estimates supply no
lower bound without the actual nonzero normalized forcing limit.

Broad torsion/interface searches led to the primary abstracts of
[September6 p-torsion barriers](https://arxiv.org/abs/2609.06534) and
[September2 equivariant holomorphic torsion](https://arxiv.org/abs/2609.02192).
The first distinguishes uniform function convergence from its gradient
estimates; the second derives asymptotic terms from positive-line-bundle
and fixed-point geometry. No admitted transfer to the literal arithmetic
current or its Ward parameter was found. Neither is a Lean premise.

The new content is the exact classification for these literal forcings
and the current's full mass mismatch, using already-proved Gamma and
calculus methods. No new general integration theorem or RH proof is claimed.

## Lean audit

Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekGammaForcingMeasureClassification.lean`.
The leaf has 422 lines and 31 public theorems. Its closed capstone is
`pwGammaForcingMeasureClassification_closed`; the complete arithmetic
mass defect is `pwGammaMobius_complete_response_mass_defect`.

Scratch and direct `lake env lean` checks passed without warnings.
The targeted `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaForcingMeasureClassification`
passed. All 31 theorems were audited by scratch `#print axioms`: only
`propext`, `Classical.choice`, and `Quot.sound` occur. Formal lint, index
regeneration, all-name uniqueness and task-scoped file checks passed.
Umbrella wired; no full/umbrella build or numerical experiment ran.
All owned Lean and research processes finished. RH remains unproved.
