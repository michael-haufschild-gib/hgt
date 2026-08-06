# Two-clock locality law

- **ID:** `two-clock-locality-law`
- **Stage:** 3-formalized
- **Type:** UNIVERSAL NULL TEST / CONTINUUM GRAVITY / CLOCKS / HYPERTRANSCENDENCE
- **Parent:** `two-mass-self-calibrating-clock-metric-law.md`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/ClockPropagatorSelfCalibration.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockPrincipalSymbolCalibration.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockLocalityDistributionKernel.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockLocalityNullTest.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockResponseIdentifiability.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockResponseStability.lean`
- **Status:** complete mathematical locality law and differential-algebraic residual obstruction
  formalized unconditionally in Lean, together with the reconstruction bridge — identifiability and
  quantified stability of the measured response from probe data. What remains open is physical: that
  a finite compact intervention set is norming and that laboratory noise stays inside the
  tolerance.

## Headline

> **If spacetime is one continuum, two kinds of clocks can disagree only where they meet.**

Equivalent experimental line:

> **Two clocks can test whether gravity is governed by one local spacetime.**

The law concerns inverse responses. Individual forward clock responses may contain arbitrarily
long tails and may be hypertranscendental.

## The locality law

Let two minimally coupled scalar clock species propagate through one metric with operators

\[
  P_{\mu_i}=P_0+\mu_iI,\qquad \mu_1\neq\mu_2.
\]

Let the same unknown local receiver and source gains dress their complete Green responses:

\[
  \widehat G_{\mu_i}=A\,G_{\mu_i}\,B.
\]

Then the measured inverse operators obey

\[
  \boxed{
  \widehat G_{\mu_1}^{-1}
  -
  \widehat G_{\mu_2}^{-1}
  =
  (\mu_1-\mu_2)B^{-1}A^{-1}.}                                           \tag{1}
\]

Because \(A\) and \(B\) are multiplication operators, the right side is multiplication by a
function. Its distribution kernel is

\[
  (\mu_1-\mu_2)\kappa(x)\delta(x-y).                                     \tag{2}
\]

Therefore the cross-species inverse residual has:

1. no off-diagonal support;
2. no derivative of \(\delta(x-y)\);
3. no species-dependent principal or subprincipal propagation term;
4. no memory tail.

## Proof

The inverse of the dressed response is

\[
  Q_{\mu_i}=B^{-1}(P_0+\mu_iI)A^{-1}.
\]

Subtracting cancels \(P_0\) before it is commuted through either endpoint gain:

\[
\begin{aligned}
  Q_{\mu_1}-Q_{\mu_2}
  &=
  B^{-1}\bigl[(P_0+\mu_1I)-(P_0+\mu_2I)\bigr]A^{-1}\\
  &=
  (\mu_1-\mu_2)B^{-1}A^{-1}.
\end{aligned}
\]

This is exact in a noncommutative operator algebra. \(\square\)

## Converse null test

Within the stated two-species model class, any measured residual containing an order-one or
order-two derivative term, or any kernel support away from \(x=y\), contradicts `(1)`.

This converse is now formalized rather than asserted:

- `ScalarSecondOrderOperator.ne_twoMassDifference_of_first_ne_zero` and
  `ne_twoMassDifference_of_second_ne_zero` — a residual carrying a nonzero first- or second-order
  coefficient is not a two-mass inverse difference of the model class;
- `notMem_dsupport_twoMassClockLocalityKernel_of_ne` — no point off the diagonal lies in the
  support of a two-mass residual kernel fiber.

At least one premise must then fail:

- no common local metric principal part;
- nonminimal or species-dependent curvature coupling;
- species-dependent endpoint gain;
- unresolved field mixing;
- nonlocal effective dynamics;
- incorrect mass calibration;
- incomplete inversion/support reconstruction.

Thus a nonlocal residual is not by itself proof of quantum gravity. It is a sharp falsification of
the complete single-metric, minimal-coupling, common-calibration hypothesis.

## No memory tail

Claim 4 of the kernel list is the only one that is not a restatement of the operator identity, and
it is where the physical content lives. Call a response operator *memoryless* when its output at
each instant depends only on the input at that instant. Then:

- a residual acting by pointwise multiplication is memoryless;
- there are response operators that both carry genuine memory whose difference is nevertheless a
  pointwise multiplication, hence memoryless.

So locality of the residual is not inherited from locality of the responses. It is **created by the
cancellation**. This is the exact sense of the public translation below.

`formal/GaloisForLFunctions/HTGeometry/ClockLocalityNullTest.lean`: `Memoryless`,
`memoryless_pointwiseMul`, `memoryless_residual_of_pointwiseMul`, `not_memoryless_delay`,
`exists_memoryful_responses_with_memoryless_residual`. All depend only on `propext`,
`Classical.choice`, `Quot.sound`.

## Hypertranscendental strengthening

Let experimental control frequency be the differential variable. Suppose the common calibration
\(\kappa\) is nonzero and differentially algebraic over the calibrated control field, as it is for
every finite rational/exponential-algebraic instrument model in the admitted class. Then `(1)`
implies

\[
  Q_{\mu_1}-Q_{\mu_2}
  =
  (\mu_1-\mu_2)\kappa
\]

is differentially algebraic.

Therefore

\[
  \boxed{
  \text{HT inverse residual}
  \quad\Longrightarrow\quad
  \text{failure of the local single-metric clock model}.}                \tag{3}
\]

This implication does **not** say an HT forward propagator violates locality. The corpus proves
exact black-hole clock responses that are hypertranscendental even though their underlying wave
operators are local. Locality is revealed only after inversion and cross-species subtraction.

Public translation:

> **A black hole may make each clock infinitely complicated. If both clocks inhabit one local
> spacetime, all that complexity must cancel from their inverse disagreement.**

## Falsifiable protocol

1. Use two scalar clock transitions or modes with distinct calibrated pole masses and common
   source/readout hardware.
2. Measure their complete complex impulse-response matrices over a laboratory network.
3. Reconstruct regularized inverse response operators on the resolved band.
4. Subtract them after the known mass normalization.
5. Test whether residual is diagonal/local and derivative-free at increasing resolution.

An analogue-gravity or distributed quantum-sensor experiment is the first realistic venue.
Astrophysical use would require phase-coherent multi-species response reconstruction, which is not
presently available.

### Lean status of the reconstruction step

Step 3 of the protocol — "reconstruct regularized inverse response operators on the resolved band" —
is supported by
`formal/GaloisForLFunctions/HTGeometry/ClockResponseIdentifiability.lean` and
`formal/GaloisForLFunctions/HTGeometry/ClockResponseStability.lean`:

- `responseOperator_eq_of_data`, `hiddenResponse_eq_of_data`, `hiddenResponse_eq_of_family_data` —
  complete drives and separating readouts determine the measured response, and behind unknown gains
  the hidden one, with a separating *family* of couplings in place of invertibility;
- `responseOperator_norm_sub_le_of_data`, `hiddenResponse_norm_sub_le_of_data` — with norming drives
  and readouts the reconstruction is Lipschitz in the data, with an explicit constant built from the
  apparatus; `normingReadouts_dualBall` and `normingDrives_unitBall` show the canonical families are
  norming with constant `1`.

Axioms: `[propext, Classical.choice, Quot.sound]`.

## Hostile novelty audit

The bare statement that inverse free propagators differ by their mass terms is standard QFT
algebra and receives no novelty credit. Ward identities routinely use differences of inverse
propagators. The potentially new content is narrower:

1. source/receiver dressing is retained rather than assumed calibrated;
2. the cross-mass difference self-calibrates the endpoint product;
3. the same recovered product divides the principal symbol to reconstruct the full metric;
4. the residual is proposed as an all-wavelength equivalence-principle/null-locality test;
5. DA calibration makes an HT inverse residual a formal obstruction.

Ordinary interacting QFT can produce species-dependent nonlocal self-energies even on one
spacetime. Therefore the test applies to controlled probe sectors whose non-gravitational
self-energies have been removed or shown common. Without that control, a residual detects
model failure but is not evidence against continuum spacetime.

## Nature boundary

Nature's editorial gate requires results that are novel, arresting, and have immediate and
far-reaching implications. Equation `(1)` is arresting and falsifiable, but the current package
still lacks a physical experiment, stability theorem under finite bandwidth/noise, and complete
priority audit across multichannel inverse scattering and equivalence-principle null tests.

## Gates

- [x] 0 → 1: inverse-residual null test and exact failure modes stated
- [x] 1 → 2: noncommutative cancellation, local-kernel consequences, and HT obstruction proved
- [x] 2 → 3: literal local second-order cancellation, zeroth-order operator identity,
  diagonal-supported Dirac kernel fibers, and DA/HT obstruction formalized unconditionally,
  umbrella-reachable, and axiom-audited
- [ ] 3 → 4: physical stability and external priority audit

## Log

- 2026-08-06 — moved to `3-formalized`: every theorem stated and proved on this card is unconditional in Lean, all named modules build under the `GaloisForLFunctions.HTGeometry` umbrella, and every declaration is axiom-audited to `[propext, Classical.choice, Quot.sound]`.

- 2026-08-01 — closed derivative/support abstraction gap: formalized exact two-mass coefficient
  cancellation and honest classical-distribution kernel fibers
  `(μ₁-μ₂)κ(x)δ_x`, including singleton support and nonzero-support equality.
