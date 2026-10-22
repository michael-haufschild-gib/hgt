# Fixed Suzuki clocks and the actual critical divisor

- **ID:** ccm-fu-fixed-clock-pole-obstruction
- **Stage:** 1-in-progress
- **Type:** [JUMP] clock-orbit interpretation under hostile test; fixed one-sided source no-go closed in Lean, fixed connected source no-go has paper proof but open Lean analytic bridge
- **Route:** CCM-FU / SV2

## Closed kernel component

`CCMFUSuzukiClockEndpointKernel.lean` proves unconditionally in Lean that, for every
`ω > 0`, the exact cubic mixing-density endpoint kernel

```text
∫₀¹ 3v² / (δ + ωv)⁴ dv
```

is at least `1/(16ω³δ)` for `0 < δ ≤ ω`, and tends to `+∞` as `δ ↓ 0`.
This is the sharp derivative-order obstruction used below. It does **not** identify this
kernel with a derivative of the actual arithmetic window; that is still open.

## Literal statement under test

For `b > 0` and every fixed `ξ > 0`, the literal completed triangular window

```text
Wξ(H) = ccmFUSuzukiSymmetricMellinShiftedTriangularWindow b H ξ
```

is unbounded as `H > b` varies. This is about the actual prime-minus-polar source, not a
positive model or a separate bound on either channel. It does **not** assert the RH-bearing
zero-clock window is bounded.

The stronger, route-relevant test is that for every fixed `ω ≠ 0`, the **actual connected
Suzuki completed window**

```text
ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H ω
```

is unbounded over `H > b`. The Lean barycentre theorem in
`CCMFUSuzukiSignedWindowMixture.lean` identifies it with the positive mixture
`∫₀¹ 3(1-t)² W_(tω)(H) dt`. Unboundedness of each `W_(tω)` alone does not prove
this stronger assertion: cancellation between different shifts must be excluded.

## Pole test

Write `μ` for the literal critical-Mellin prime-minus-polar signed measure on `(b,∞)`.
The definition of the triangular weight gives

```text
H Wξ(H) = ∫_(b,H] 32 (H-h) h^(-3) cosh(ξh) μ(dh).
```

If `Wξ` were uniformly bounded, its left side would have linear growth. Its Laplace transform
would then be analytic for `Re u > 0`. In a sufficiently far right half-plane
(the existing Euler comparison uses `Re u > 2+ξ`), Fubini gives

```text
u² Laplace[H Wξ(H)](u)
  = ∫_(b,∞) 32 h^(-3) e^(-uh) cosh(ξh) μ(dh).
```

Three complex derivatives remove `h^(-3)`. The already formalized unshifted third-grade Abel
identity should identify the result, up to an entire finite-head correction and a nonzero
constant, with

```text
regularizedCriticalMellinDefect(u-1/2-ξ)
  + regularizedCriticalMellinDefect(u-1/2+ξ).
```

Hardy's theorem supplies `ρ = 1/2+iγ` in the actual Xi divisor. At `u = ξ+iγ`, the first
summand has a simple pole. If the second summand is regular there, the sum has that pole. If
the second also has a pole, both residues are positive analytic multiplicities, so the pole
survives. Therefore the displayed sum cannot be analytic throughout `Re u > 0`.

For the connected mixture, the proposed replacement is an **endpoint divisor-transport law**.
The meromorphic defect is `1/(s+1) + logDeriv regularizedRiemannZeta(s+1)`; every pole of this
function has positive integer residue. Mixing its two real translates by the positive density
`3(1-t)²` pushes each zero's positive divisor mass along a horizontal segment. Fix a nonzero
Hardy-zero height and choose the zero with maximal real part at that height. Its rightmost
transported endpoint has real part `βmax - 1/2 + |ω| > 0`; no other zero at the same height
can transport mass beyond it. A positive compactly supported Cauchy transform cannot extend
holomorphically through its rightmost support point. The quadratic vanishing of the mixing
density at `t=1` weakens the endpoint to a `(z-z₀)² log(z-z₀)`-type branch, but does not remove
it. More directly, on the ray `z = z₀ + δ`, `δ > 0`, three derivatives of a translated pole
`1/(z-x)` equal `-6/(z-x)^4`. All zero contributions at that height and left of `z₀` have the
same negative real sign; the maximal-zero endpoint contributes at least a positive constant
times `δ⁻¹` in magnitude by integrating `t ∈ [1-δ/|ω|,1]`. Terms from other zero heights
and the holomorphic remainder have bounded third derivatives locally. A holomorphic extension
through `z₀` would have a bounded third derivative, contradiction. This is a paper mechanism
under test, not a formalized theorem. A pointwise pole argument
is insufficient for the continuum mixture; its singularity may be a cut rather than a pole.

### Finite-jet reinterpretation: continuum mixture is not needed

The exact connected test itself has an exponential-polynomial form. New Lean theorem
`CCMFUSuzukiConnectedSixthJet.lean` proves, for all real `ω,h` (with Lean's totalized
division at zero),

```text
h^6 * (32/h^3) * 6*(sinh(ωh)/(ωh)-1)/(ωh)^2
  = (96/ω^3) * (exp(ωh)-exp(-ωh)-2ωh).
```

It also proves the equality **inside the literal finite prime-minus-polar window**, with the
same test on both channels. Consequently the expected sixth derivative of the completed
connected Abel transform, on its safe Euler half-plane, is

```text
Aω⁽⁶⁾(u) = -(96/ω³) * [T(u-ω)-T(u+ω)+2ω T'(u)],
```

where `T` is the existing polar-minus-prime tail Mellin defect. This analytic identity is
**not yet a Lean theorem**. Source-faithful first Abel integration is now closed on the
safe Euler half-plane. `CCMFUSuzukiConnectedPrimeSixthJet.lean` now proves the
sixth derivative of the literal connected prime Dirichlet series equals its exact
endpoint exponential jet. The polar sixth derivative and completed continuation
remain open. The finite-window identity alone does not establish them.

`CCMHardyHorizontalEndpointZero.lean` now proves unconditionally in Lean that there is a
Hardy-height Xi zero with no Xi zero anywhere on its rightward horizontal ray. The companion
`CCMFUSuzukiConnectedJetPoleNoGo.lean` proves, for every fixed positive `ω`, that the
actual regularized-zeta finite-difference jet `D(u-ω)-D(u+ω)+2ωD'(u)` fails analyticity at
some `Re u>0`, where `D(u)=regularizedCriticalMellinDefect(u-1/2)`. It uses the actual Xi pole
order and proves the other two terms analytic there. Both modules passed scratch and
target-only Lake `--old` builds and are wired into the `RHTower` umbrella. The local
noncancellation is thus **Lean-closed**. `CCMFUSuzukiConnectedPrimeAbel.lean`,
`CCMFUSuzukiConnectedPolarAbel.lean`, and
`CCMFUSuzukiConnectedCompletedAbel.lean` now prove the first-Abel identity for the
same literal completed connected source on `Re u > 1+ω`, retaining prime-minus-polar
cancellation. The prime-channel sixfold differentiation is also closed; polar-channel
differentiation and uniqueness of continuation remain open.

On `Re u>1+ω`, the first-Abel identity is Lean-closed by an actual finite-prime
Dirichlet series and actual clocked-polar Laplace integral. The remaining paper
argument differentiates this identity six times on a slightly smaller half-plane.
The sixth power of `h` is absorbed by any positive margin in `Re u-(1+ω)`; the
finite-window sixth-jet theorem then reduces the result to two shifts and one
derivative of the existing tail defect. The tail-defect/wall equality gives a
meromorphic continuation to `Re u>0`. These last steps are not formalized.

With that identity, the fixed connected-clock no-go reduces to finitely many
ordinary poles. At a nonzero Hardy-zero height, choose the rightmost Xi zero at that height
(finiteness in a compact horizontal strip is already formalized in
`WeilLagFunctionCriterion.lean`). At its pole coordinate `p`, the term `T(u-ω)` has a simple
pole at `u=p+ω` in `Re u>0`. The terms `T(u+ω)` and `T'(u)` are analytic there because their
arguments lie strictly to the right of that selected zero. Thus no clock-mixture branch-cut
analysis is needed. A bounded literal connected cumulative source would make `Aω` analytic
on `Re u>0`, contradicting the endpoint pole. More importantly, boundedness of the **triangular
connected window** would make its exact Volterra primitive `H Wω(H)` grow only linearly; the
second-Abel transform `u² Laplace[H Wω(H)]` gives the same analytic extension. This is an
unconditional paper proof that every fixed `ω>0` connected triangular window is unbounded;
Lean currently closes the finite sixth-jet identity, literal first-Abel identity,
prime-channel sixth derivative and spectral pole noncancellation, but **not** the
polar sixth derivative, second-Abel continuation or final pole contradiction.
Priority against external literature has not been established.
It would retire **fixed** `ω>0` clocks, not moving
source-adaptive clocks or the RH-bearing zero-clock window.

### Stronger clock-support reinterpretation

The cubic density is not essential. Let `ν` be any nonzero finite positive clock measure of compact
support on `[0,a]`, with `a>0` in its support. Its Cauchy transform
`Cν(z)=∫(z-t)⁻¹dν(t)` cannot extend holomorphically through `a` from the right. At `z=a+δ`,
the absolute value of its normalized `n`th derivative is
`∫(a+δ-t)⁻ⁿ⁻¹dν(t)`. For every `ε>0`, positivity and `a∈supp ν` give a lower bound
`ν((a-ε,a])/(δ+ε)^(n+1)`, while total mass gives an upper bound
`ν([0,a])/δ^(n+1)`. Taking `n`th roots and then `ε↓0` shows the Taylor radius at `a+δ`
is exactly `δ`. An extension across `a` would give a larger radius for small `δ`, contradiction.
This is a paper proof of the abstract endpoint lemma, not yet a Lean theorem.

The proposed **universal positive-clock classification** is: any fixed positive symmetric
Mellin-clock measure with nonzero support endpoint makes its literal completed Cesàro window
unbounded. Choose a nonzero Hardy-zero height and the maximal-real-part zero at that height.
Its translated positive divisor measure has a right endpoint at
`βmax-1/2+a > 0`; all other same-height zero masses are positive and end no farther right.
The abstract endpoint lemma then forbids the holomorphic second-Abel continuation that a
bounded window would provide. The only positive compact clock not excluded by this mechanism
is the zero-clock point mass. This is a conjectural *source application*: its shifted
source-to-Laplace identity and analytic decomposition at the actual divisor still need Lean
proofs for general clocks. The first-Abel identity above covers the connected Suzuki
clock only. No claim is made that the abstract Cauchy-transform fact itself is new to
literature.

### Signed-clock extension under test

Positivity of the clock measure appears unnecessary for the **endpoint obstruction**. For any
finite complex measure `ν` supported in `[0,a]` with `a>0` in its support, its Cauchy transform
`Cν(z)=∫(z-t)⁻¹dν(t)` cannot extend holomorphically through `a` from the right. Indeed, if an
extension existed on a disc about `a`, the identity theorem would make it agree with `Cν` on
the disc minus the real support (this complement is connected around the right endpoint).
The distributional identity `∂̄Cν=πν` would then make `ν` vanish on that disc, contradicting
`a∈supp ν`. Unlike the derivative lower bound above, this argument permits arbitrary signed
or complex cancellation. This is an abstract paper argument, not a Lean theorem or a novelty
claim about Cauchy transforms.

Applied to the actual source, the proposed stronger classification is that **every fixed
nonzero signed compact symmetric Mellin clock with positive right support endpoint** has an
unbounded literal completed triangular window. At a Hardy-zero height, choose the zero with
maximal real part. Near its rightmost shifted endpoint, its positive multiplicity times `ν`
is the sole singular measure; other zero transports end strictly to the left or lie at
different heights. Thus signed mass cannot cancel this endpoint unless the clock itself has
no support there. The source-specific Abel identity, local analytic decomposition of the
full Xi divisor, and uniqueness of continuation remain unproved for this general clock.
This extends the proposed positive-clock no-go, not the RH-bearing zero-clock bound.

**Failed first argument:** Nonzero positive `∂̄`-current on an *interior* segment does not by
itself preclude analytic continuation of the far-right germ to another sheet across that cut.
The rightmost endpoint, or a precise maximal-support theorem, is essential.

## Closed finite source bridge and next analytic landing

Let `mω(h) = ∫₀¹ 3(1-t)² cosh(tωh) dt` and let `qω(H)` be the literal cumulative
prime-minus-polar source with weight `32mω(h)/h³`. The generic finite weighted Volterra identity
is proved in `CCMGuinandWeilWeightedVolterraIdentity.lean`; its specialization to the actual
connected Suzuki weight is proved in `CCMFUSuzukiClockVolterraBridge.lean`. For `0 < b ≤ H`
and `ω ≠ 0`, Lean proves exactly

```text
∫_(b,H) qω(t) dt = H * connectedWindow(b,H,ω).
```

This retains both literal prime and polar terms. It does not prove boundedness or the no-go.
A hypothetical uniform bound on the window would make this primitive `O(H)` and give a
second-Abel continuation analytic on `Re u > 0` once measurability and the existing generic
analytic lemma are connected to this source.

An independent exact clock-transport law is now closed in Lean. The generic theorem in
`CCMGuinandWeilClockCommutator.lean` says, for a smooth clock `m` and literal completed
prime-minus-polar cumulative source `q_F`, that

```text
q_(mF)(H) = m(H) q_F(H) - ∫_b^H m'(t) q_F(t) dt.
```

`CCMFUSuzukiClockCommutator.lean` specializes it to the actual connected Suzuki multiplier
and the actual zero-clock third-grade cumulative source. This is a source-faithful gauge/Volterra
identity, not an estimate. `CCMGuinandWeilExponentialClockAbelTransport.lean` proves an abstract
Abel-shift law; `CCMGuinandWeilActualDampedEnvelope.lean` supplies its unconditional growth
hypothesis for the literal source; `CCMGuinandWeilActualExponentialClock.lean` identifies its
Volterra clock with the literal one-sided prime-minus-polar weight; and
`CCMGuinandWeilActualExponentialAbelShift.lean` proves, for `a ≥ 0` and `Re u > 1+a`,

```text
Abel(q_a,b,u) = Abel(q_0,b,u-a),
q_a(H) = primePolarWindow(b,H,exp(a h)*32/h^3).
```

All four modules are scratch-checked, target-built with Lake `--old`, and wired into the
`RHTower` umbrella. This is an exact *actual-source* spectral translation, not a bound or a
continuation across any zeta zero. It preserves prime-minus-polar cancellation at finite cutoff.
In particular, a fixed clock does not create an independent arithmetic channel.

`CCMHardyCriticalMellinNonextension.lean` now closes the analytic obstruction in Lean:
Hardy's actual critical-line Xi zero and the corpus's exact positive pole residue forbid any
holomorphic extension of the regularized completed defect to a half-plane crossing
`Re s = -1/2` that agrees with the Euler-side defect. Its proof clears the logarithmic
derivative denominator, applies analytic identity on the connected half-plane, and contradicts
the known simple pole at Hardy's point. No RH premise enters.

`CCMGuinandWeilFixedExponentialClockNoGo.lean` then applies this obstruction to the *literal*
prime-minus-polar source. For every `b>0` and `a>0`, Lean proves

```text
¬ ∃ C ≥ 0, ∀ H>b, |primePolarWindow(b,H,exp(a h)*32/h^3)| ≤ C.
```

The proof constructs a measurable clamped representative identical above the physical base
wall, uses a hypothetical bound only to obtain Laplace holomorphy, translates the actual Abel
transform by `a`, differentiates three times to recover the completed defect plus its entire
wall head, and invokes the Hardy nonextension theorem. Both modules passed scratch checks and
target-only Lake `--old` builds, and are imported by `RHTower.lean`. This is an unconditional
fixed **one-sided** clock no-go, not a connected Suzuki no-go and not RH.

### Clock-orbit reinterpretation under test

**Public sentence:** a positive scalar clock does not improve the arithmetic source; it moves
the source's singularity boundary. The primitive object may be the completed source's orbit
under clock changes, not an individual positive window. The finite commutator is its physical
transport law; the proved Abel shift is its spectral transport law; divisor tomography says
what is transported. A fixed positive spectral displacement should move at least one Hardy-zero
obstruction into the half-plane where a bounded-window producer would require holomorphy.

**Risky consequence:** every fixed nonzero positive compact symmetric clock has an unbounded
literal completed triangular window, even if RH holds. The one-sided exponential case is now
proved; continuum positive mixtures may cancel between branches, so the general assertion does
not follow and has not been proved. Existing `CCMFUSuzukiAdaptiveCofinalLanding`
already proves an adaptive-clock boundedness equivalence with the literal zero-clock window;
`CCMEvenShiftExponentialTypeRigidity` proves a different rigidity for decaying fixed-shift
polynomial multipliers. Neither establishes this growing-clock consequence.

**Falsifiers:** a bounded fixed positive connected clock for the literal source; a lawful
negative/divisor-wall cancellation at the rightmost transported endpoint; failure of the
source-to-divisor continuation identity for the same cutoff and normalization. A positive
interior jump is insufficient, because continuation to another sheet may cross that cut;
the endpoint is the load-bearing object.

The paper-level endpoint argument remains conjectural. Priority against classical omega
results and spectral-flow formulations remains unaudited. No literature-new theorem is claimed
for the abstract Cauchy endpoint lemma or Abel translation alone.

The hard next test is to take the connected positive mixture of this exact identity and
prove its derivative/wall law with no illicit exchange of signed source and positive clock.
On a far-right Euler half-plane, the existing cubic differentiation and wall-head identities
should yield

```text
(1/32) * (secondAbel qω)'''(u) + entireWallω(u)
  = (1/2) ∫₀¹ 3(1-t)² *
      [D(u-1/2-tω) + D(u-1/2+tω)] dt,
D = regularizedCriticalMellinDefect.
```

This formula has not yet been proved in Lean. Its exact factor, signs, and hypotheses must be
checked against the literal source; the endpoint argument is not a substitute for it.

## Audit obligations

1. Check the exact `32`, Laplace translation, wall-head and sign conventions in the literal
   existing Lean source. A wrong shift would invalidate the argument.
2. **Closed for the connected sixth jet:** residue noncancellation uses the actual Xi
   divisor in `CCMFUSuzukiConnectedJetPoleNoGo.lean`.
3. **Partially closed:** first-Abel source-to-Laplace identity holds for the literal
   completed connected source on `Re u > 1+ω`, and the prime-channel sixth derivative
   has the predicted exponential jet. Still prove polar-channel differentiation,
   bounded-window second-Abel continuation, and analytic uniqueness for that *same*
   source before promoting the window no-go.
4. Search priority: classify this against existing Suzuki fixed-shift results and literature.
5. For the connected assertion, prove the maximal-support non-extension lemma for a compact
   positive shift measure, then the literal shifted-source Laplace identity. Verify that no
   signed wall or rational correction contributes at the selected nonzero-height endpoint.

## Meaning for the route

If true, no fixed positive symmetric Mellin displacement can supply a bounded FU producer.
The clock must collapse toward zero with aperture, consistent with the existing adaptive
landing. The surviving RH-bearing problem remains the zero-clock prime-minus-polar
cancellation, so this result alone does not close CCM-FU or SV2. It is not a primary
reframing conjecture; priority against classical prime-error omega results remains open.
The stronger connected result would retire **fixed nonzero connected clocks themselves**, not
only their point-shift components. It would reinterpret positive clocking as transport of divisor
mass, rather than harmless smoothing, while leaving the moving-clock RH producer open.
