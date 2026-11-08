# Frankenstein routes of review-0811 §2.3: assemblies, bridges, conjectures

- **ID:** FR-0811
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per route; CONJECTURE loop
- **Source:** docs/reports/review-0811/obstacles-summary.md §2.3 (F1–F25)
- **Statement:** assemble each Frankenstein route as one Lean theorem; build the missing bridges;
  conjecture on what the assembly exposes.

Lean modules go into the owning programme folders.
Order: F22, F21, F18, F15, F2, then the rest.

## F22 — curve-proof template over ℤ

**Parts in the corpus.** `RH ⇔ ZAL ∧ AAL` (`riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw`);
weak recurrence ⇒ AAL; curve data with zeros `ρ_{i,k}` periodic in height (`CurveDatum.zetaZero`,
`curveConfig_periodic`); vertical recurrence of periodic and exponential-polynomial configurations
(`verticallyRecurrent_of_periodic`, `verticallyRecurrent_of_expPoly`); RH for odd hyperelliptic
curves (`riemannHypothesis_oddHyperelliptic`, `hyperellipticDatum_unitary`); JAS shell criterion.

**Missing bridge.** The matching curve step ↔ ℤ step was a reading [D]: ZAL and AAL were defined
only for ζ. Bridge: define both laws on every `ZeroConfig` and evaluate them on curves and on ζ.

**Results (Lean, `ZeroConfigurationGeometry/AbscissaLaws/TheAbscissaLawsOfAZeroConfiguration`).**
- For every configuration: pure ⇔ ZAL ∧ AAL (the FE of the configuration gives the left side).
- AAL ⇔ zero transport: every right zero has, for every `ε` and `T`, a zero of real part
  `> Re ρ − ε` at height `|Im| > T`. This is exactly the zero-level conclusion of weak recurrence;
  AAL carries no more and no less.
- Vertical recurrence ⇒ AAL. Curves (periodic, Kronecker rank one) and zero sets of exponential
  polynomials (finite rank) satisfy AAL unconditionally.
- For a curve datum in the strip: AAL holds; ZAL ⇔ pure ⇔ unitary. Odd hyperelliptic curves: all
  three hold.
- ζ: the configuration laws are `AsymptoticAbscissaLaw` and `ZerosApproachLine`.
- The configuration FE does not give B13: for every `½ < Re ρ < 1` the two-point configuration
  `{ρ, 1 − ρ̄}` approaches the line, is reflection-symmetric, and violates AAL at `h = 0`.

**Correction of the [D] matching.** In the coordinates where both laws are stated (the `s`-plane),
the curve proof's split is the opposite of the reading `Stepanov ↔ ZAL, power sums ↔ AAL`: AAL is
supplied for free by the Frobenius (periodicity of the zeros in height), and ZAL is the whole
content, proved by Stepanov plus power sums plus FE. Over ℤ, AAL is the trace of the missing
Frobenius periodicity; weak recurrence is its function-level shadow, and AAL equals its zero-level
shadow. The JAS shell criterion reads the same proof in the Frobenius-eigenvalue coordinate:
ZAL ↔ finite rank (free on curves), shell-sum growth ↔ Stepanov's count, Turán ↔ power sums.

**Follow-up (Lean, `ZeroConfigurationGeometry/AbscissaLaws/TheCurveProofSplitsAtTheAbscissaLaw`).**
`curve_template_split`: for every curve datum in the strip, AAL holds, and crude count at every
level ⇔ ZAL ⇔ purity ⇔ unitarity. Stepanov and the power sums both live inside ZAL.

## F21 — critical-line firewall

**Bridge (Lean, `ArithmeticPositiveDuality/TheCriticalLineFirewall`).** One function-level law
`HalfPlaneAbscissaLaw F σ₀`; for ζ at `½` it is `AsymptoticAbscissaLaw`. `criticalLineFirewall`:
the law fails with a finite nonempty top layer for the continuous positive system (count error → 0,
continued across `½`), the integer-norm Euler product with linear counting, the rational-prime Euler
product with multiplicative coefficients and linear counting, and the zero set of one reflection
pair; ζ's law is invariant under every symmetric shift.

**Learning.** The reflection `ρ ↦ 1 − ρ̄` keeps heights; AAL is vertical transport. A functional-
equation input must turn the FE into transport in height — the zero-set symmetry gives nothing.

**Follow-up (Lean, `ZeroConfigurationGeometry/AbscissaLaws/TheAbscissaLawIsNotAsymptotic`).**
`exists_not_abscissaLawAt_zero_of_isAsymptotic`: any property of zero configurations that depends
only on the zeros above some height and holds for one pure configuration also holds for a
configuration with ZAL that violates the finite case of AAL (add one reflection pair). No large-height
zero statistic decides B13 or AAL; the input must see zeros at bounded height.

## F18 — AAL tail form

**Bridge (Lean, `TailArithmeticOfThePrimeOrbit/TheAbscissaLawIsATailTransport`).**
`asymptoticAbscissaLaw_iff_tailTransport`: AAL ⇔ near every right zero, above every height, a point
where at every cut the tail vanishes and `|ζ − E_y| = |E_y| ≥ Π_{p≤y}(1+p^{−σ})^{−1}`. The heights
are tail-bad at every cut (`tailTransport_height_mem_tailBad`).

**Correction of the [D] reading.** No head alignment ("Kronecker scale") is part of AAL: the law asks
for full-amplitude tail events, not returns of the phases. Alignment enters only through the
return-based producers, which ask for more than AAL.

## F15 — count skeleton

**Bridge (Lean, `CountingHolography/TheCountDoorOfACurveAndOfZ`).** The Tate principle in both
directions (`exists_count_tateLimit_iff`): a degree-two homogeneous function is the Tate limit of an
`ℕ`-valued count iff it is nonnegative. Curves (`curve_countDoor`): the integral Castelnuovo–Severi
defect is a Tate limit of a count iff the datum is unitary (Hodge index on integral classes forces RH,
by rational scaling and continuity). True curves (`hyperelliptic_spanDefect_is_count`): the defect of
an integral class is an integer polynomial in `q` and the point counts, a natural number, exactly
homogeneous — the count is the intersection number itself. Over ℤ the same door is
`riemannHypothesis_iff_tateLimit_of_count` with a real-valued form.

**Learning.** On curves the form is itself integral before any sign is known (it is a polynomial in
point counts); over ℤ the Krein square of the integer probes is a real Toeplitz form in `log(m/n)`.
Conjecture (open, not attempted in Lean): the integer-probe form takes non-integer values (would
follow from continuity and non-constancy of the spline correlation, since `log(m/n)` is dense).

## F2 — critical curve = window

**Bridge (Lean, `ArithmeticHodgeTheoryOfDegenerations/TheCriticalMatrixIsDecidedByThePoleChannel`).**
`posDef_iff_primitive_and_poleChannel` (positivity splits along any subspace);
`eventuallyCriticalPosDef_iff_poleChannel_of_lt_iInf_windowThreshold` (below `W = ⨅ windowThreshold`
the whole-space matrix at ratio `R` is positive iff its pole channel is, using `R_pole = W`);
`criticalPositivityThreshold_eq_iInf_windowThreshold_iff_poleChannel`: B104 (`R_c = W`) ⇔ the pole
channel pays at every ratio below `W`. Uses the committed, previously unwired module
`PrimitiveCriticalThresholdEqualsWindowThreshold` (`R_pole = W`).

## F8 / F23 — the critical partial sum

**Bridge (Lean, `ArithmeticHodgeTheoryOfDegenerations/TheCriticalPartialSumOfHalfTheHeightIsZeta`).**
The [C] item "a partial sum of length half the height approximates `ζ(½+ib)` to `O(|b|^{−½})`" is
proved from the corpus' Titchmarsh 4.11 (`norm_zetaStripError_le_grid`):
`‖S_M(b) − ζ(½+ib)‖ ≤ 9M^{−½} + M^{½}/|b|` for `|b| ≤ πM`; for `M(b) = ⌈|b|/2⌉ + B` the error is
`(9√2 + √(3 + 2B))|b|^{−½}`, and the squares differ by that error times `2|ζ| + error`.

## F5 — typical-height layer

**Bridge (Lean, `ArithmeticProduction/AnEulerMollifierNeedsThePrimesUpToLogSquared`).** The [D] step
"any mollifier reaching it has Euler length of the primes `≤ c log²T`" is proved for Euler mollifiers:
`M_y = Π_{p≤y}(1 − p^{−s})` is the Dirichlet polynomial `μ·[d | y#]` of length `y# ≤ 4^y`
(`edPoly_eulerMollifierCoeff`), and a mollified second moment `≤ (1 + K₀/log T)T` forces
`y ≥ min(1/24, 1/(14K₀)) log²T / log 4` (`eulerMollifier_needs_primes`).

## F12 — the rigid ¬AAL world (zero-set level)

**Bridge (Lean, `ZeroConfigurationGeometry/AbscissaLaws/TheFailureOfTheAbscissaLawIsAFiniteLayer`).**
`not_abscissaLaw_iff_finite_layer`: AAL fails iff some top layer `{Re > ½ + h}` is finite and nonempty;
`finite_layer_structure`: its reflection is a finite bottom layer at the same heights, and above them
every zero lies in `|Re z − ½| ≤ h`. The [D] row "the FE maps the top layer to a bottom layer" is now
[L] at the level of zero sets.

## Rest of §2.3
F1, F3, F4, F6, F9, F10, F11, F13, F14, F16, F17, F20, F25 are single [L] assemblies in the corpus; no
bridge was missing. F7 is a meta-statement (one theorem with many proofs); equivalences of proved
statements carry no content in Lean. F19: with Euler head coordinates the tail coordinate of `S` is
`S·M_y`, Schur iff `|S| ≤ |E_y|` (`norm_tailCoordinate_le_one_iff`); this holds at the zeros of `S`, so
"certificates exist exactly at tail-good heights" (tail-good = `|ζ − E_y|` small) is not the same
condition — not bridged. F24: open (B106).

## Conjecture loop
- C15.1 (open): the Krein square of the integer probes is not integer-valued. Reduction: integral
  values force `2 Re C(log(m/n)) ∈ ℤ`; `C` is continuous (`continuous_splineCorr`) and `log ℚ₊` is
  dense, so `2 Re C` would be constant. Missing: non-constancy of the spline correlation, which needs
  the explicit formula for `C`. Not attempted further.
- C22.1 (refuted as stated, kept as a reading): "power sums ↔ AAL" — on curves AAL is free; the
  power-sum step is inside ZAL (`curve_template_split`).
- C21.1 (proved): asymptotic zero statistics cannot decide B13 (`TheAbscissaLawIsNotAsymptotic`).
- C21.2 (proved): no verification up to a fixed height decides B13
  (`exists_not_abscissaLawAt_zero_of_isLocalBelow`). AAL/B13 is two-scale: configuration-level
  producers must relate bounded and large heights, as recurrence and transport do.
- C18.1 (proved): AAL needs no head alignment; it is the transport of full-amplitude tail events.
- C22.2 (proved, `ZeroConfigurationGeometry/AbscissaLaws/AlmostPeriodicZerosRecurWithBoundedGaps`): zeros of a
  uniformly strip-almost-periodic holomorphic function recur with bounded gaps (Bohr), hence obey the
  law; every Dirichlet series does so where its partial sums converge uniformly. The rational one-off
  tends to `1` vertically (almost periodic at large height) and violates the law: almost periodicity
  must hold uniformly in height. ζ is the Frobenius-periodic analogue only on `Re s > 1`.

## Log
- 2026-11-08 — created; F22, F21, F18, F15, F2, F8/F23, F5 bridges and two F21/F22 follow-ups compiled and wired.
