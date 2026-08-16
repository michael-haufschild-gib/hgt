# Route U bandlimited literal compact source

- **ID:** `route-u-bandlimited-literal-compact-source`
- **Stage:** 3-formalized
- **Type:** THEOREM / source-selection and exact factor transport
- **Routes:** U primary
- **Source:** hard-edge Paley--Wiener strong limit, L² Fourier reflection, classical Fourier bridge

## Status labels

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`

## Theorem U-BANDSOURCE

Let `F` be a complex `L²(R)` class whose unitary Fourier transform vanishes almost everywhere
outside `[-a,a]`. Define the literal representative

```text
q(x) = 1_{(-a,a)}(x) (FourierUnitary F)(x).
```

Then `q` is pointwise zero for `x<=-a` and `a<=x`, and `q` lies in `L¹ cap L²`. If `F` has a
continuous representative `f`, then for every real `w`, not merely almost every `w`,

```text
routeURealFourier(q)(w) = f(w/(2 pi)).                    (1)
```

For the actual Route-U hard-edge strong limit with degree bound `N_k<=C a_k`, corpus support
theorem gives `a=C/pi`, including open-band support after removing only two null endpoints.
Consequently every continuous representative of that actual limit has a literal compact source
supported in `[-C/pi,C/pi]` satisfying `(1)`.

If additionally

```text
f(x) = (x^2-r^2)^m K(x^2)
```

for continuous complex `K`, then exact multiplicity survives source selection:

```text
routeURealFourier(q)(w)
  = (w^2-(2 pi r)^2)^m G(w^2),
G(u) = (2 pi)^(-2m) K(u/(2 pi)^2),                       (2)
```

and `G` is continuous. Thus actual hard-edge bandlimit plus a continuous exact squared-variable
factorization supplies every compact-support, integrability, continuity, and pointwise Fourier
hypothesis required by recursive Route-U root division.

All statements are unconditional closed Lean theorems. They do not assume RH. Actual-limit
capstones take a continuous representative and its exact squared-variable factorization as local
hypotheses; corpus still must derive those properties and incoming form strictness from selected
first-contact packets.

## Theorem U-LOCAL-L2

Let the actual rational hard-edge packets converge strongly in real `L²` to `L`, and suppose their
angular polynomials converge locally uniformly in squared variable to `F(u)` along the same
subsequence. The Cayley half-density tends pointwise to one, so packets converge pointwise to

```text
f(x)=F(x^2).
```

An almost-everywhere convergent subsequence of strong `L²` convergence then forces both limits to
coincide. Lean derives, rather than assumes,

```text
f in L²,    toLp(f)=ofRealLp(L),    Im(F(x^2))=0 for every real x.   (3)
```

Thus the locally uniform squared-variable limit is automatically the real-even physical
representative of the strong hard-edge limit. If `F` is continuous, U-BANDSOURCE now constructs
its literal compact source with no separate representative-equality or `L²` hypothesis. If
globally `F(u)=(u-r^2)^m H(u)` for continuous `H`, the exact compact factorization `(2)` follows
directly.

## Heavy conjecture loop

### U-B1 — abstract L² bandlimit cannot select a literal compact source

**Conjecture.** Paley--Wiener support of an equivalence class is too weak for pointwise compact
root division, so a new source-construction theorem is needed.

**Attack.** Multiply the canonical unitary-Fourier representative by the open-band indicator.
Finite-measure Hölder gives `L¹`, class equality gives `L²`, and the indicator enforces literal
endpoint vanishing.

**Verdict:** false. The literal compact source is available directly from existing bandlimit.

### U-B2 — double Fourier recovery remains only almost everywhere

**Conjecture.** L² Fourier squaring recovers reflection only as a class, insufficient for exact
root identities at exceptional frequencies.

**Attack.** Use corpus L²-to-classical Fourier bridge for the integrable source, identify its
second unitary Fourier transform with L² reflection, and compare with the continuous
representative. Both classical Fourier transform and reflected representative are continuous, so
almost-everywhere equality upgrades to pointwise equality.

**Verdict:** false. Lean proves `(1)` for every real frequency.

### U-B3 — hard-edge support leaves uncontrolled boundary values

**Conjecture.** Existing support theorem only kills frequencies with strict inequality
`2C<2 pi |xi|`, while root division requires literal zero at support endpoints.

**Attack.** The open-band indicator forces endpoint values to zero. The two endpoints form a null
set, so replacing the original L² representative there preserves its class and all Fourier laws.

**Verdict:** false. Existing hard-edge support yields exact literal support at `C/pi`.

### U-B4 — Route U normalization may destroy root multiplicity

**Conjecture.** Passing from `f(x)` to source transform `f(w/(2 pi))` may leave only zero locations,
not exact squared-variable multiplicity and continuous quotient.

**Attack.** Rescale squared variable and factor `(2 pi)^(-2m)` explicitly. Lean normalizes the
polynomial identity without derivatives or computation.

**Verdict:** false. Formula `(2)` preserves full multiplicity and continuity exactly.

### U-B5 — locally uniform limit and strong L² limit may be unrelated representatives

**Conjecture.** Normal-family extraction gives an entire limit, while precompactness gives an L²
limit, but an additional identification theorem is needed and may fail on exceptional sets.

**Attack.** Strong L² convergence has an almost-everywhere convergent subsequence. Local uniform
convergence gives pointwise convergence of every subsequence. Uniqueness of pointwise limits makes
the entire candidate equal to the L² limit almost everywhere, which simultaneously proves its
square-integrability and exact `toLp` identity.

**Verdict:** false. Formula `(3)` closes representative identification on the same subsequence.

### U-B6 — complex normal-family limit may lose physical reality

**Conjecture.** Even after representative identification, the entire limit may take complex values
on real squared arguments, obstructing real hard-edge factor profiles.

**Attack.** Every finite rational hard-edge packet is real. Continuity of imaginary part transports
their pointwise limit, so `Im(F(x²))=0` for every real `x`.

**Verdict:** false. Physical real-even symmetry is automatic. Subsequent
`XiShiftedHardEdgeEntireRootFactorization.lean` closes global root quotient; incoming form sign
remains.

## Higher universal principle

**For continuous bandlimited states, source selection is Fourier involution plus null-set gauge,
not an additional compactness theorem.** Earlier obstruction conflated three layers: an L² class,
a continuous physical representative, and a literal compact source. Fourier reflection connects
first two, while open-band indicator fixes pointwise support without changing class. Exact root
multiplicity then transports functorially under normalization.

This removes compact-source existence, integrability, endpoint support, scaling, locally-uniform/
L² representative identification, and physical reality from Route U's open core. Subsequent
escaping-pole entireness plus unit-norm noncollapse removes global squared-variable root
quotient/factorization as well. Remaining hard problem is incoming PSD/strictness before prime
wall.

## External novelty audit

Corpus search found separate Paley--Wiener support, L² Fourier reflection, L²/classical Fourier
agreement, compact root division, and hard-edge limit modules, but no theorem composing them into
an actual Route-U literal source with pointwise recovery and multiplicity-preserving factor
transport. No external priority claim is made; novelty remains unverified.

## Gates

- [x] 0 -> 1: literal representative, pointwise inversion, endpoint, and scaling conjectures attacked
- [x] 1 -> 2: dependency-closed proof and corpus collision audit
- [x] 2 -> 3: unconditional Lean proof, direct check, exact leaf build, axiom audit, umbrella wire
- [ ] 3 -> 4: independent significance audit and standalone exposition

## Lean closure

Module:
`formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeBandlimitedCompactSource.lean`.

Companion module:
`formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeLocallyUniformL2Source.lean`.

Capstones:

- `routeUOpenBandSupport_of_ae_abs_support`;
- `routeUHardEdge_limit_open_band_support`;
- `fourier_routeUBandlimitedCompactSource_eq_reflection`;
- `routeURealFourier_routeUBandlimitedCompactSource`;
- `routeURealFourier_routeUBandlimitedCompactSource_factor_pow`;
- `routeUHardEdge_limit_has_literal_compact_source`;
- `routeUHardEdge_limit_has_literal_compact_factorization`;
- `exists_memLp_toLp_eq_of_tendsto_pointwise_of_tendsto_L2`;
- `routeUHardEdge_angularLocallyUniformLimit_sq_im_eq_zero`;
- `exists_memLp_routeUHardEdge_angularLocallyUniformLimit_toLp_eq`;
- `routeUHardEdge_angularLocallyUniformLimit_has_literal_compact_source`;
- `routeUHardEdge_angularLocallyUniformLimit_has_literal_compact_factorization`.

Module passed direct `lake env lean` and exact leaf `lake build`. Finished module is imported by
`RHTower.lean`; no umbrella or full-project build was run.

## Log

- 2026-08-16 — Open-band literal `L¹ cap L²` source constructed from abstract L² bandlimit.
- 2026-08-16 — L² Fourier reflection upgraded to exact pointwise classical recovery.
- 2026-08-16 — Actual hard-edge support connected at aperture `C/pi`.
- 2026-08-16 — Exact squared-root multiplicity transport through Route U normalization proved.
- 2026-08-16 — Locally uniform squared-variable limit identified with strong L² limit.
- 2026-08-16 — Square-integrability and real-even physical symmetry derived automatically.
