# CCM-FU completed Riesz graph energy

Status: in progress

## Exact frontier

The corpus identifies one universal RH-bearing scalar:
`completedPrimePolarGammaUnitApertureWindow`. Its uniform bound is equivalent to RH. Existing
local, coherent, HG, Suzuki, and G-CE energies only re-encode this scalar.

## Conjecture loop

### C1 — absolute variation

Conjecture: normalized completed Riesz windows have summable absolute increments.

Hostile audit: this would force convergence and boundedness, hence RH. No source-independent
absolute estimate can prove it. Rejected as an equivalent reformulation.

### C2 — square graph energy

Conjecture: if `A_M` is the literal completed `Lambda - 1 + Gamma@1` square-root Riesz moment,
then

```text
sum_{M >= 1} |(A_{M+1} - A_M) / M|^2 < infinity.
```

Exact increment law expected:

```text
A_{M+1} - A_M = (sqrt(M+1) - sqrt(M)) * (psi(M) - M + 2*gamma).
```

Paper proof route: rationalize square-root increment; use the unconditional PNT error summability
already formalized as `summable_psi_error_weight`, the crude linear remainder bound to reduce a
square to one power, and summability of `M^-3` for the Gamma atom.

This is strictly weaker than RH: `ell^2` increments do not bound their partial sums. Positive
survivor is a source-faithful singular graph norm for the actual completed source, potentially the
missing compactness input in Suzuki boundary transport.

## Novelty audit

Internal corpus search found no successor law or square-summability theorem for the completed
Riesz window. Primary-literature search across Suzuki/CCM, Nyman--Beurling, and Riesz-criterion
work found no matching finite graph-energy theorem. Novelty remains unverified until broader
expert audit.

## Lean target

New `RHTower` module proving exact increment, source-prefix identity, unconditional summability,
and its unit-aperture graph-coordinate form. No hypotheses, axioms, or computations.

## Closed results

Lean module:
`GaloisForLFunctions/RHTower/CCMFUSuzukiCompletedRieszGraphEnergy.lean`.

- Exact prefix flux:
  `A_M = sum_{k<M-1} (psi(k+1)-(k+1)+2*gamma) * (sqrt(k+2)-sqrt(k+1))`.
- Unconditional singular graph energy:
  `sum_k |(A_{k+2}-A_{k+1})/(k+1)|^2 < infinity`.
- Exact completed harmonic charge is absolutely summable and has total charge zero. The Mertens
  Abel tail `-2*gamma` cancels the Gamma clock `+2*gamma` before any absolute value.
- Exact clock transmutation and signed Abel law:
  the Riesz producer is harmonic-prefix boundary readout plus signed clock acceleration.
- Suzuki critical-jet landing: for every finite aperture, right derivative at `omega=0+` of the
  shifted-Euler coupled error, Gamma-completed before scalarization, converges to the literal
  completed Riesz moment and normalized unit-aperture window.
- Unconditional joint critical/cofinal selection: there is `omega_N>0`, `omega_N -> 0`, for which
  the finite Suzuki critical jets track actual completed Riesz moments with error `o(1)`; the same
  schedule tracks normalized FU/Suzuki windows.

All listed results are closed Lean theorems. No RH premise, divisor premise, new axiom, `sorry`, or
computation occurs.

## Conjecture loop continuation

### C3 — zero harmonic charge bounds square-root clock

Conjecture: absolute convergence and total zero of completed harmonic charge force bounded
normalized square-root-clock readout.

Hostile audit: rejected. Harmonic clock is multiplied by

```text
(sqrt(k+2)-sqrt(k+1)) / (1/(k+1)-1/(k+2)) ~ (1/2) k^(3/2).
```

Qualitative tail convergence therefore has no rate adequate for the moving boundary or its clock
acceleration. The exact Abel law identifies needed datum as signed interaction of actual harmonic
prefixes with this unbounded clock, not total charge or local graph energy.

### C4 — Suzuki convergence closes source selection

Conjecture: fixed-aperture critical-jet convergence, diagonalized cofinally, supplies RH-bearing
uniformity.

Hostile audit: rejected and replaced by an unconditional positive theorem. A source-selected
cofinal diagonal with vanishing tracking error always exists, independently of RH. Hence
subsequence convergence, Montel compactness, and finite characteristic identification alone cannot
bound the arithmetic scalar. They solve identification, not uniformity.

### C5 — surviving hard estimate

The common hard core is now a genuinely joint estimate: bound the normalized finite Suzuki
critical jets uniformly along a coefficient-faithful critical/cofinal schedule, while retaining
shifted-Euler atomic/main-term cancellation through the `omega -> 0+` derivative. Because tracked
jets differ from `completedPrimePolarGammaUnitApertureWindow` by `o(1)`, such a bound is
RH-equivalent. Any proposed proof must produce new uniform arithmetic cancellation; positivity of
the shifted coefficients, fixed-`omega` summatory estimates, square graph energy, harmonic total
charge, or compactness cannot supply it.

## Updated novelty audit

Corpus search found the coefficient derivative
`hasDerivAt_suzukiShiftedCoefficient` and coupled-error derivative
`suzukiCoupledError_critical_derivative_base_one`, but no transport of that jet through the literal
completed square-root clock and no critical/cofinal tracking theorem. Suzuki's canonical-system
paper treats fixed positive shift and does not state this finite completed-Riesz jet landing. Recent
Suzuki/CCM searches found no matching theorem. These results remain `[NOVELTY UNVERIFIED]` pending
expert review.

### C6 — positive critical chord and local Möbius pole cancellation

Conjecture: Suzuki's finite right critical secant admits a source-faithful decomposition before
scalarization, without the apparent `1 / omega` loss.

Outcome: proved unconditionally in
`GaloisForLFunctions/RHTower/CCMFUSuzukiCriticalChordMeasure.lean`.

- The atomic chord coefficient and matching polar prefix mass are nonnegative.
- The completed finite Riesz jet is exactly positive atomic Riesz mass minus positive polar Riesz
  mass plus the Gamma boundary.
- Suzuki's Euler-product coefficient is exactly the pre-existing signed Möbius synthesis
  coefficient.
- For every non-unit label, `sum_{d|n} mu(d)=0` cancels the entire exterior `1 / omega` debt.
  The remaining kernel
  `(1-d^(-2 omega))/(2 omega)` lies in `[0, log d]`.
- The resulting signed Möbius-log divisor fibre, and therefore its finite Riesz producer, is
  nonnegative after exact local cancellation.

This closes a real convergence/renormalization gap but does not estimate the atomic--polar
imbalance.

### C7 — distinct-prime grading and positive-carrier cofinal convergence

The renormalized coefficient has exact grade law

```text
c_omega(n)/(2 omega)
  = n^omega (2 omega)^(card(primeFactors(n))-1)
      product_{p|n} ((1-p^(-2 omega))/(2 omega)).
```

Thus prime powers are the only nonzero zero-clock grade; every additional distinct prime carries
one explicit positive `2 omega` factor. Lean also proves one common positive schedule
`omega_N -> 0+` on which atomic and polar Riesz carriers converge separately, each with vanishing
error, at moving aperture `N+1`. Cancellation is preserved during diagonal passage.

Hostile audit: this settles joint convergence, not cofinal boundedness. Higher-grade mass can grow
with aperture while each fixed label vanishes. Exact remaining datum is uniform cancellation
between aggregate positive higher-grade atomic mass and matching polar continuum. Route-O actual
heads, G-CE singular graph positivity, Suzuki Ward positivity, and FU graph energy all lack this
joint quantitative comparison.

Novelty status: `[NOVELTY UNVERIFIED]`. Corpus contains Möbius synthesis and fixed-aperture Suzuki
derivatives, but search found no fibrewise critical-pole cancellation theorem, distinct-prime
critical grade factorization, or separate positive-carrier cofinal convergence theorem.

### C8 — exact higher-grade defect and cofinal clock rigidity

The positive-chord decomposition now lands literally on the completed Möbius-divisor source:

```text
SuzukiCriticalJet(omega,M) - MobiusCompletedRieszMoment(M)
  = AtomicHigherGradeExcess(omega,M) - PolarSecantExcess(omega,M).
```

All terms and equalities are finite and unconditional in Lean. Further coefficient laws expose
what the polar side must cancel:

- shifted Suzuki coefficients are multiplicative on coprime labels;
- critical chords satisfy
  `Chord_omega(mn) = 2 omega Chord_omega(m) Chord_omega(n)` for nontrivial coprime labels;
- every chord dominates its von Mangoldt atom;
- on `p^(k+1)`, chord exceeds `log p` by at least
  `omega k (log p)^2`;
- every coprime pair contributes at least
  `2 omega Lambda(m) Lambda(n)` at the product label.

Consequently the atomic excess is pointwise nonnegative and the fixed label `4=2^2` forces

```text
AtomicHigherGradeExcess(omega,M)
  >= omega (log 2)^2 (sqrt M - 2),   M >= 5.
```

This yields a new cofinal rigidity theorem: any positive schedule with separately vanishing atomic
excess must satisfy `omega_N sqrt(N) -> 0`. The canonical common atomic--polar convergence schedule
obeys this rate. Hence separate-carrier convergence necessarily collapses every nonzero
square-root-scale Suzuki clock jet; it cannot itself supply the missing Route-O/G-CE source sign or
the FU uniform completed prime--polar bound. Surviving avenue must compare atomic and polar excesses
before taking separate limits, at a rate stronger than graph-energy or compactness control.

Novelty status: `[NOVELTY UNVERIFIED]`. Corpus search found no exact literal-source excess law,
critical-chord coprime multiplication theorem, prime-power second-grade lower bound, or induced
`omega_N sqrt(N) -> 0` rigidity theorem.

### C9 — exact second and third Suzuki transverse layers

The second-grade global arithmetic asymptotic is now closed unconditionally in
`GaloisForLFunctions/RHTower/CCMFUSuzukiSecondGradeAsymptotic.lean`:

```text
sum_{n<=N} (Lambda*Lambda)(n)
  = N (log N - 1 - 2 gamma) + o(N).
```

The proof retains both Mertens constants and the symmetric hyperbola overlap, then transports the
sublinear discrepancy through the exact positive square-root Toeplitz mesh.  This yields normalized
cofinal cancellation of the literal signed second-grade Suzuki arithmetic-minus-polar Riesz mass.

The next coefficient layer is now exact in
`GaloisForLFunctions/HTGeometry/ShiftedEulerThirdTangent.lean`:

```text
d^3/domega^3 c_omega(n)|_0
  = 8 (Lambda*Lambda*Lambda)(n) + 2 Lambda(n) log(n)^2.
```

The prime-power curvature term is forced.  Therefore the third shifted-Euler tangent is not a pure
triple convolution.  The theorem is proved through the literal reflected Möbius--zeta Mellin
convolution, including `n=0`; no coefficient pattern or support surrogate is assumed.

### C10 — connected pre-scalar producer and exact CCM landing

Conjecture: form the third Dirichlet cumulant before scalarization.  The disconnected cubic Euler
mass should cancel, leaving precisely the prime-power curvature required by the CCM prime-entry
third jet.

Outcome: proved unconditionally.  With `T_j` the arithmetic-function-valued `j`th Suzuki tangent,

```text
T_3 - 3 T_2*T_1 + 2 T_1*T_1*T_1
  = 2 D_log^2 Lambda,
```

so coefficientwise the connected producer is exactly `2 Lambda(n) log(n)^2`.  The cancellation is
inside the Dirichlet-convolution algebra before any scalar readout; all disconnected two- and
three-prime Euler grades disappear identically.

`GaloisForLFunctions/RHTower/CCMFUSuzukiConnectedThirdTangentBridge.lean` proves the exact dressed
landing on every canonical non-unit label:

```text
CCMPrimeEntryThirdJetScale(n)
  = 16 Re(ConnectedSuzukiThirdTangent(n)) /
      (sqrt(n) log(n)^5).
```

It also identifies the complete finite CCM prime rate, completed prime--polar--Gamma rate, and the
literal RH-bearing moving triangular prime--polar window with the corresponding connected Suzuki
producer.  Thus Suzuki-to-CCM source faithfulness is no longer missing at third grade.

Hostile audit: this does not prove uniform cofinal boundedness.  After connected-cumulant
cancellation, the surviving coefficient is exactly the literal CCM prime source, and its coupled
triangular polar cancellation is still the RH-bearing datum.  Any next argument must control that
signed connected-producer-minus-polar window; positivity of the connected coefficients alone would
separate the two regions and lose the required cancellation.

Novelty status: `[NOVELTY UNVERIFIED]`. Corpus search found source-form and Suzuki wall-field welds,
but no arithmetic-function third cumulant of the shifted Euler family, no proof that its disconnected
triple convolution cancels, and no coefficient-faithful connected-cumulant landing onto the CCM
prime-entry third jet.

### C11 — exact positive-window barycentre and source-adaptive cofinal landing

The finite connected Suzuki log-chord multiplier is now bounded sharply enough for moving walls:

```text
1 <= Phi_omega(h) <= cosh(omega h),
|Phi_omega(h) - 1| <= (omega h)^2 exp(omega h) / 2.
```

More importantly, its third connected multiplier has the exact probability-mixture representation

```text
Phi_omega(h)
  = integral_{t in [0,1]} 3(1-t)^2 cosh(t omega h) dt.
```

After finite Fubini interchange, the actual completed positive connected Suzuki producer is therefore
an exact barycentre of literal *signed* prime-minus-polar triangular windows under symmetric Mellin
shifts:

```text
A_{omega,b,H}
  = integral_{t in [0,1]} 3(1-t)^2 W^sym_{b,H}(t omega) dt.
```

Prime and polar terms remain coupled inside every shifted window. No separate absolute-value or
positive/negative-region estimate enters this identity.

The moving-wall convergence problem is also closed constructively. Let `V(b,H)` be the exact finite
total variation of the triangular prime--polar source and choose

```text
omega(b,H) = 1 / (H^2 (V(b,H) + 1)).
```

For `0 < b <= H` and `1 <= H`, Lean proves unconditionally

```text
|A_{omega(b,H),b,H} - W_{b,H}| <= exp(1) / (2 H^2).
```

On canonical cofinal walls `H_N = max(b,1) + N + 1`, the clock is positive, tends to zero, the walls
tend to infinity, and the signed Suzuki-minus-literal error tends to zero. This is an explicit
source-faithful schedule, not compactness or nonconstructive subsequence selection.

Hostile audit: convergence does not provide uniformity. The corpus now contains the exact equivalence

```text
(exists C, forall H >= max(b,1), |A_{omega(b,H),b,H}| <= C)
  <->
(exists C, forall H >= max(b,1), |W_{b,H}| <= C).
```

At `b=1`, the left side implies the Riemann hypothesis through the existing third-grade Cesaro
completeness theorem. Thus cofinal convergence is no longer an open datum, while uniform boundedness
of the source-adaptive finite Suzuki barycentre is exactly the original signed triangular
prime-minus-polar cancellation problem. Positivity alone cannot contract it: `Phi_omega(h) >= 1`.
Remaining new-science target is source-specific cancellation in the finite coupled barycentre (or an
equivalent matched-coverage/quantile-current law), not another convergence, compactness, local
energy, or separate-region positivity theorem.

Lean status: proved and wired in
`GaloisForLFunctions/RHTower/CCMFUSuzukiPositiveConnectedLogChord.lean`,
`GaloisForLFunctions/RHTower/CCMFUSuzukiSignedWindowMixture.lean`, and
`GaloisForLFunctions/RHTower/CCMFUSuzukiAdaptiveCofinalLanding.lean`. Targeted source checks and
`lake build GaloisForLFunctions.RHTower.CCMFUSuzukiAdaptiveCofinalLanding` pass. Capstones have no
axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.

Novelty status: `[NOVELTY UNVERIFIED]`. Corpus search found fixed-window Suzuki convergence and
reporter-level positive mixtures, but not this exact signed-window barycentre, explicit
variation-adaptive cofinal clock, quantitative `O(H^-2)` landing, or exact uniformity equivalence for
the actual finite connected producer.

### C12 — quantitative Suzuki landing on matched coverage and completed transport

The explicit adaptive Suzuki producer is now connected directly to both source-level hard
coordinates isolated elsewhere in the Lean corpus. For `0 < b <= H` and `1 <= H`, Lean proves

```text
|A_adaptive(b,H) - (MatchedBlock(b,H) + CoverageSeam(b,H) - IncomingPolar(b,H))|
  <= exp(1) / (2 H^2),
```

and

```text
|A_adaptive(b,H) - (CompletedQuantileTransport(b,H)
    - LowerOutgoingCorrection(b,H) - IncomingPolar(b,H))|
  <= exp(1) / (2 H^2).
```

Every displayed core keeps prime, polar, internal transport, and terminal transport contributions
coupled before the absolute value. At canonical lower wall `b=1`, two exact frontier equivalences
follow:

```text
UniformBound(A_adaptive) <-> UniformBound(CoverageSeam),
UniformBound(A_adaptive) <-> UniformBound(CompletedQuantileTransport).
```

This closes the formerly implicit Suzuki-to-hard-current landing. It also kills a possible false
pivot: a new finite-characteristic convergence or positivity theorem cannot bypass the arithmetic
obstruction, because the actual adaptive finite Suzuki family is quantitatively asymptotic to, and
uniformly equivalent to, the outgoing matched-coverage seam and completed oriented quantile current.

Lean status: proved and wired in
`GaloisForLFunctions/RHTower/CCMFUSuzukiHardCoreLanding.lean`. Direct source check and targeted
`lake build GaloisForLFunctions.RHTower.CCMFUSuzukiHardCoreLanding` pass. Missing transitive oleans
were built individually as encountered. Capstones have no axioms beyond `propext`,
`Classical.choice`, and `Quot.sound`.

Novelty status: `[NOVELTY UNVERIFIED]`. Corpus search found separate equivalences from literal
triangular windows to coverage/quantile currents and the new adaptive Suzuki-to-literal convergence,
but no direct quantitative Suzuki-to-current landing or direct uniformity equivalences.
