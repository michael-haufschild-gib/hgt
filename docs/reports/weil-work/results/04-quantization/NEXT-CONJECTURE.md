# After J: test whether source positivity can stay uniformly strict

Tenth-cycle update: H remains open after the exact near-null and critical
Gamma/pole audits below. Candidate J, excluding arbitrarily late sublinear
residual scales, now has a closed paper proof in [QUIET-SCALES.md](QUIET-SCALES.md).
Its formalization and all nineteen declaration audits are complete. J improves the obstruction from a limsup statement
to an eventual bound; it supplies no source upper bound and does not solve H
or WP04. Return to source degeneration after this survivor is audited.

G is now proved in `WeilWorkQuantizationPowerRigidity.lean`: for every specified hW, either R (λ=Λ on n≥2 and RH) holds, or the actual integer-floor remainder exceeds every sublinear power bound. The paper proof and compiled dependency map are in SUBLINEAR-REMAINDER.md. No source bound eliminates that alternative.

## Big-picture decision

Do not spend the next cycle merely replacing a power by a slower envelope. That improves a receiver while leaving the source question untouched. The decisive structure is exact integer arithmetic support: the corpus already constructs coercive positive systems on real support, and even jittered discrete support. It also rules out generic random integer constructions and regular perturbations. Positivity, discreteness and small fluctuations separately are insufficient.

Given that internal frontier, what stronger conjecture survives? Test strict positivity itself before returning to full singularity or integer multiplicities.

**Conjecture H (source degeneration):** for every `hW : WeilPositiveFull lam` and every real c>0, there exists s∈ℂ such that

`1/2 < s.re ∧ (weilContinuation hW s).re < c`.

Thus the actual source Herglotz function has infimum zero on the open critical half-plane. This is a source theorem, with no residual-growth, phase, support or continuation premise beyond hW. Its measure interpretation would exclude a positive constant Lebesgue-density floor. That interpretation must be proved using the canonical Poisson representation, with its π normalization retained.

H is weaker than WP04. It does not imply singularity, atomicity, a residual-growth bound, or quantization. Its significance would be ruling out uniform coercivity from exact arithmetic support even for entirely uncontrolled infinite remainder. Falsity would expose a sharply incompatible world: a full-positive integer-supported source whose spectral measure retains a positive density floor, contradicting the eventual counting target once the canonical measure implication is proved.

## Preliminary attack

- `WeilLinearTwistQuantization.mixed_spectrum_no_uniform_density` assumes integer/real atomic representations, a continuous-edge diffuse part, and sublinear residual growth after removing the constant. These are precisely missing for H. Its stronger-looking title does not prove H.
- `WeilPositivityConductorObstruction` rules out a specified χ₈ mixture through a known double radical. It does not provide a radical for arbitrary λ or rule out every density floor.
- `LebesgueAtomArchimedeanWeilDensity` and `JitteredDiscreteWeilPositive` show why discarding exact integer support destroys H's intended mechanism. The jittered source has noninteger positions and a separate negative atom; it is not a counterexample satisfying hW.
- STATUS MUST-573 rules out broad independent random integer constructions; MUST-522 explains why number-field-specific arithmetic support matters. These do not establish H.
- The external Samaris positive-real Dirichlet-series theorem concerns a normalized absolutely convergent pure exponential series. Our positive-real function includes the Gamma datum and the polar term. Removing those terms does not preserve positivity. Booker/Oliver L-datum results retain discrete spectral support and multiplicity assumptions, which are unpaid here.
- Two deep searches found no applicable source degeneration theorem. The first completed; the second returned partial results with text/source stages interrupted. Every returned candidate and source row was inspected. Suggested ξ-divisor estimates concern the already-defined ξ divisor, not the arbitrary canonical measure. The proposed implication from ordinary Dirichlet convergence to a strict spectral lower bound is also unpaid.

Verdict: **SURVIVES PRELIMINARY ATTACK; UNPROVED**. Scientific novelty is unconfirmed. No Lean declaration for H has been written.

## First open core and next experiment

`[OPEN CORE]`: use the exact integer-frequency source identity to contradict a uniform lower bound `(weilContinuation hW s).re ≥ c>0` throughout the half-plane. Generic Herglotz theory cannot do this.

1. Audit the general source form and near-null/prime-blind results for an actual source-dependent sequence with normalized spectral energy tending to zero. A ζ radical cannot be substituted without showing it is near-null for λ.
2. Track subtraction of c in the exact archimedean/arithmetic identity. A conductor argument must preserve the specified source and pay any needed reflected continuation; citing a degree-one converse with those hypotheses omitted is circular.
3. Let the competing possibility remain live: construct a uniformly strict integer-supported source, or derive the exact obstruction that prevents the real-support positive constructions from being transferred to integers. No numerical experiment is authorized.
4. Finish a dependency-closed paper proof before writing Lean. If H fails, audit its strongest positive survivor and continue conjecturing; if H succeeds, return to local density/singularity and the full residual obstruction.

## Variational refinement prepared during J's audit

The exact normalized null-mixture theorem currently requires a<b. At the
critical boundary a=b=1 it gives no conclusion: its witnesses can have
unbounded Gamma energy per unit mass as a approaches b. Passing to equality
without uniform control would be a gap.

Existing open conjecture H2 (rediscovered formulation of CANNOT-496): for every ε>0 there exists
`c : SmoothTest →₀ ℝ` with all coefficients nonnegative,
`linearCombination ℝ (fun f => logVector f.1) c = 0`,
`smoothMixtureMass c = 1`, and
`linearCombination ℝ (fun f => criticalDatum 1 1 0 f.1.1) c < ε`.
These are literal source symbols from CriticalDatum and CriticalBoundary.
This is a variational upper bound, not positivity or existence of a producer.
Under a given hW, null-mixture energies are nonnegative; H2 would then show
that exact integer support forbids a uniform positive spectral-energy gap.
The passage to H's Poisson real-part statement still needs its canonical
normalization proved. H2 has no paper proof or Lean declaration.

First attack: check whether critical constant slack is already classified;
then inspect whether the a<b witnesses have any uniform mass/Gamma control.
A generic boundary-of-cone argument cannot supply that control. The opposite
possibility is a positive infimum at a=b despite collapse for every a<b.

Eleventh-cycle correction: STATUS CANNOT-496 already identifies this critical
constant slack as the prime-blind LP value and requires approximate C-PIN
witnesses. Verdict: **REDISCOVERED; OPEN**. Earlier searches did not justify
calling the formulation new. The a<b normalized theorem does not pass to
equality without controlling Gamma energy per unit mass. The September 2026
compact-window upper bound treats Λ and assumes RH asymptotically; its tests
are not integer-null mixtures. Automorphic conductor bounds assume an
automorphic/Rankin–Selberg realization. `[OPEN CORE]`: produce normalized
integer-null mixtures at a=b=1 with arbitrarily small archimedean energy, or
show their infimum is positive and understand that obstruction.

If H2 fails with a positive energy gap δ, the exact polar-completion theorem
would supply weights satisfying the smooth-test inequalities for
`criticalDatum 1 1 (-δ)`. Turning those into a full-positive source with a
Lebesgue density floor would still require the smooth-to-full-test extension
and canonical measure normalization. This is the competing structural world
to attack, not a contradiction that can be dismissed by generic positivity.

## K is formalized; L attacks resonant analytic phases

K now excludes arbitrarily late sublinear scales of the actual circle-phase
variation, not only of the positive floor remainder. Its paper argument and
complete Lean status are in PHASE-VARIATION.md. This does not exclude linear
variation. Further generic bounded-variation prerequisites are not the next
research objective.

**Conjecture L (unproved):** for every specified hW, writing
`W = quantizationCirclePhase hW`, if there exist sequences `p : ℕ → ℂ` and
`ω : ℕ → ℝ` such that

`Summable (fun j => ‖p j‖ * Real.exp (|ω j| / 2))`

and for every x>0,

`W(x) = ∑' j, p(j) * exp(i*ω(j)*x)`,

then λ=Λ on n≥2 and RH holds. Equivalently, the proposed final source-only
alternative says R or no such representation exists. No claim is made that
an arbitrary source supplies this representation.

What is new in the candidate: retain all rational resonances
`m*exp(-ω(j)/2) ∈ ℕ`; do not discard them. Existing `ap_lock_rigidity` and
settled-AP receivers explicitly exclude every nonzero rational resonance.
The actual radial trace also lacks their supplied continuous-edge premise.
L concerns the canonical phase itself, including its values at trace zeros.

Why it might fail: an infinite, analytically summable, unit-modulus AP factor
could have genuine rational dilation couplings compatible with the normalized
integer source. Finite exponential sums and single linear phases are not
adequate tests of that possibility. A counterexample must supply the actual
hW and phase identity; an arbitrary circle-valued AP function is insufficient.

Parent audit so far: the smooth lock-phase theorem needs a subpower phase;
the linear-plus-variation theorem needs subpower variation of the perturbation;
boundary/infinite dilation rigidity needs a convergent dilation representation
of λ. None of those premises has been derived here from L's representation.
The deep query returned partial results (unfinished filter_and_judge), so the
failure to find a stronger theorem is not a claim of corpus absence. Broad
external searches did not identify an applicable theorem or establish novelty.

Preliminary verdict: **SURVIVES PRELIMINARY ATTACK; OPEN**. Scientific novelty
unconfirmed. `[OPEN CORE]`: derive the exact coupled resonant coefficient
identities from the actual radial source, retaining their scaling constants,
then decide whether positivity and normalization force the AP factor to be
constant. Do not replace this system by the nonresonant mean-only formula.
No dependency-closed paper proof or Lean declaration for L exists yet.

Next actions: audit the full resonant radial formulas and primary converse
theory; attack an infinite rational-frequency factor as well as a possible
rigidity proof. Preserve H/H2 as the wider source-degeneration problem.

### L: normalization and failed shortcuts

The exact shifted right-edge calculation in
`WeilLinearTwistQuantization.norm_twEdgeTerm_le` retains

`n^(-s) * exp(-(ω/2)*(s-1/2)) = exp(ω/4) * exp(-(log n+ω/2)*s)`.

Consequently a resonance `n = m*exp(-ω/2)` has coefficient
`exp(ω/4)*a(n)`, where `a = dirichletExp (lamLog lam)`. The candidate
coupled coefficient at positive integer m is therefore

`B(m) = Σ_j p(j)*exp(ω(j)/4)*a(m*exp(-ω(j)/2))`,

with a term included only when its argument is a positive natural number.
Omitting the exponential factor changes the arithmetic system. This series
is absolutely convergent: convergence of `Σ |a(n)| n^(-3/2)` gives
`|a(n)| ≤ A*n^(3/2)`, so each included coefficient has absolute value at
most `A*m^(3/2)*|p(j)|*exp(|ω(j)|/2)`.

This is a paper-level normalization and summability audit, **not** a proof
of the coupled radial identities. Their source contour passage, dominated
limit and common main-term normalization remain to be proved. In particular,
the earlier nonresonant mean-only identity cannot substitute for B(m).

Further attacks that do not close L:

- The classical mean-motion theorem for nonvanishing uniformly almost-periodic
  functions gives a linear phase plus a bounded almost-periodic remainder.
  Bounded amplitude does not bound total variation; K and the existing
  sublinear-variation theorem therefore do not settle this case.
- A finite unimodular exponential sum does not test the infinite case.
  Infinite analytic unimodular periodic factors can have many harmonics.
  Such a factor alone is not a full-positive arithmetic source.
- The boundary and infinite dilation theorems assume a decomposition of λ
  involving Λ. No such decomposition has been derived from L.
- The bounded ζ-quotient route needs an actual quotient bound. An AP
  reflection multiplier is not already that quotient.
- STATUS MUST-692's shorthand that analytic AP phases are covered must be
  read with MUST-690's explicit resonance restriction, confirmed in the
  Lean statement of `ap_lock_rigidity`.

L remains **SURVIVES PRELIMINARY ATTACK; OPEN**. No new Lean declaration has
been written for L. Next decisive step: derive the full B(m) system from
the actual radial traces, then attack its rigidity using source positivity;
do not replace that step by generic AP regularity or another growth wrapper.
