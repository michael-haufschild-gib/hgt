# The Poisson vertical-line criterion for RH

- **ID:** poisson-vertical-line-rh
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/drafts/pipeline/1-in-progress/harmonic-invisibility-and-the-one-over-delta-law.md §§26–70
- **Statement:** RH holds iff the Poisson zero trace `sum_rho exp(-t alpha^_rho)` is bounded on some
  vertical line of the open right half-plane; the same criterion holds for every admissible spectral
  family, in particular for the prime-accessible mass-shifted family.

## Goal
Converts RH from a statement about zero locations into a single explicit analytic inequality about a
zero-free, prime-computable object, with every step from that inequality to `RiemannHypothesis`
machine-checked.  The residual open core is the inequality itself.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper): §29 corrected at §37/§38/§53
- [x] 2 → 3  formalized: theorems below, `lake build` green, axioms exactly
      `propext, Classical.choice, Quot.sound`, `scripts/formal_tools.py lint` passes
- [ ] 3 → 4  publication-ready

## Lean surface

```text
RHTower.riemannHypothesis_iff_exists_xiPoissonTrace_line_bound
  RH  <->  ∃ sigma > 0, ∃ C, ∀ x, ‖xiPoissonTraceC (sigma + i x)‖ <= C
RHTower.SpectralFamily.im_eq_zero_iff_exists_line_bound
  the same criterion for any admissible family
RHTower.riemannHypothesis_of_xiMassTrace_line_bound
  the prime-accessible instance beta_a = sqrt(alpha^^2 + a^2), a > 1/2
RHTower.re_xiPoissonMomentTraceC_nonneg_of_rh
  RH -> every moment trace is nonnegative (complete monotonicity)
RHTower.xiPoissonPoint_im_eq_zero_of_forall_moment_nonneg
  its converse at the bottom shell, by a real-variable argument
RHTower.SpectralFamily.abs_im_le_of_line_growth_all
  the graded form: ‖trace(sigma + i x)‖ <= C exp(lam|x|)  ->  |Im (F.pt q)| <= lam for every copy
RHTower.SpectralFamily.abs_im_le_iff_exists_line_growth
  the graded equivalence, both directions, for every lam >= 0
```

Modules: `XiPoissonVerticalType`, `XiPoissonShell`, `XiPoissonBottomShellRigidity`,
`XiPoissonBottomExtraction`, `XiPoissonTraceAnalytic`, `XiPoissonHalfPlaneDecay`,
`XiPoissonVerticalSplit`, `XiPoissonBottomOnLine`, `XiPoissonCutTrace`,
`XiPoissonCutHalfPlaneDecay`, `XiPoissonCutSplit`, `XiPoissonCutBottomShell`,
`XiPoissonCutOnLine`, `XiPoissonLineBoundRH`, `XiSpectralFamily*`, `XiMassShiftedFamily`,
`XiPoissonMoment*`, `XiPoissonShell*`; abstract support in
`HTGeometry/{RealExponentialSumRigidity, GeometricAmplitudeDominance,
TrigPolynomialPhaseSelection, PrincipalSquareRoot}`.

## Approach
Square-root the heat parameter.  In the Poisson coordinate the vertical growth rates are the
displacements themselves, bounded by `1/2`, so the trace has exponential type at most one half —
order one, which is what Phragmén–Lindelöf on a quadrant admits and what the Gaussian coordinate
(order exactly two) does not.  Boundedness on one line then upgrades to decay at the bottom-shell
rate; shell homogeneity turns the bottom shell into a finite real-exponential sum; phase-robust
dominance forces its displacements to vanish; and a minimal counterexample over the discrete height
set removes the need for any induction.

## Graded channel
The criterion is not all-or-nothing.  `abs_im_le_of_line_growth_all` turns an explicit growth
exponent `lam` for the trace on one vertical line into the zero-free region `|delta| <= lam`:

```text
lam = 1/2       the unconditional envelope; vacuous
0 < lam < 1/2   an explicit zero-free region (open; weaker than RH)
lam = 0         RH
```

The hypothesis mentions no zeros.  The grading is free because the quadrant theorem's `∃ c < 2`
condition has slack in the Poisson coordinate (order one) and none in the Gaussian one (order two).

## Open core
`∃ sigma > 0, ∃ C, ∀ x, ‖Theta(sigma + i x)‖ <= C`.  Equivalent to RH (§70: the criterion is faithful
in every admissible coordinate), to complete monotonicity of `Theta` on `(0, infinity)` (§44), and on
the prime side to square-root cancellation in the `K_1`-smoothed explicit formula (§§32–33).

## Corrections recorded during the work
- §37 retracts §29's step 3 (the claimed limit does not exist; the phases spin).
- §38 retracts §37's proposed Parseval repair (phase-robust dominance suffices).
- §53 retracts the usability of §52 on a conjugation-stable divisor (the mirror class cancels the
  gain; the pair lemma restores it).
- §58 records that moment positivity does not peel, so the full converse must run through Bernstein
  and boundedness.

## Log
- 2026-07-25 — created in 3-formalized; criterion proved in both directions and transferred to the
  admissible-family interface and the mass-shifted instance.
- 2026-07-25 — graded channel added: growth exponent on one line implies zero-free region
  (`XiSpectralFamilyGraded`, `XiSpectralFamilyGradedOnLine`).

## Index-free form (§90)

The criterion no longer mentions zeta. `HTGeometry.AbstractSpectralFamily ι` packages the six
admissibility conditions over an arbitrary index type, and

- `HTGeometry.AbstractSpectralFamily.im_eq_zero_iff_exists_line_bound`
- `HTGeometry.AbstractSpectralFamily.abs_im_le_iff_exists_line_growth`

state, for any such family: the exponential type of `t ↦ ∑ᵢ exp(-t αᵢ)` along any vertical line of
the open right half-plane equals `supᵢ |Im αᵢ|`; in particular one bounded line certifies that the
whole spectrum is real.

Files: `HTGeometry/AbstractSpectralFamily.lean`, `AbstractSpectralDecay.lean`,
`AbstractSpectralShell.lean`, `AbstractSpectralRigidity.lean`, `AbstractSpectralGraded.lean`.
Axioms: `propext, Classical.choice, Quot.sound`.

The zeta statement is recovered as a corollary in `RHTower/XiAbstractInstance.lean`:
`riemannHypothesis_of_abstract_line_bound` and `abs_re_sub_half_le_of_abstract_line_growth`
(a growth exponent `lam` on one line is the zero-free strip `|Re ρ - 1/2| ≤ lam`).
