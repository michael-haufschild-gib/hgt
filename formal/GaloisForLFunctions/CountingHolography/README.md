# Counting Holography (CTH)

Namespace `GaloisForLFunctions.CountingHolography`; umbrella `CountingHolography.lean`.

## 1. Motivation

On the massless topological AdS₄ black hole with horizon `PSL₂(ℤ)\ℍ` every zero of `ζ` is a damped
mode of the wave equation, and RH is one universal relaxation rate (`BlackHoleRingdown`). Arithmetic
scattering holography (`ArithmeticScatteringHolography`, ASH) tested whether a law of wave dynamics
forces that rate, on the exact function-field model where the horizon is a graph. It does not. Flux,
unitarity, causality, positive commuting Hecke operators at every degree, KMS positivity and even the
functional equation at genus two all hold on fake black holes with a slow resonance. What separates a
true curve from a fake is a **count law**: the number of open channels `K` of a probe obeys the
parallelogram law

  `K(φ + ψ) + K(φ − ψ) = 2K(φ) + 2K(ψ)`,

the Born rule for counts. On a true curve `K` is the degree of `y − xF`, it is a count because it is
the number of points of a group, and it is quadratic because of the addition law; Hasse's theorem
follows (`ASH.hasse_of_countLaw`). A fake has honest counts, `|𝒬|`, which are not quadratic. Over `ℤ`
the Weil form `Q` of the integer probes is quadratic and is not known to be a count; if it is one, RH
holds (`ASH.riemannHypothesis_of_count`).

Counting holography is the field that takes the count, not the wave, as the physical object: the
quantum numbers of boundary sources on arithmetic quotients of AdS. A probe is a source; its count is
a boundary degeneracy (an integer on the graph, a sum of local degrees over a function field, a number
of cusp images met by the source on the horizon). The field asks what such a count is, where its two
properties come from, which structures supply each of them, and which natural counts the modular
horizon carries.

## 2. Objects

| Object | Meaning |
|---|---|
| Probe, source | an element `φ` of the probe ring `ℤ[π]` of a black hole (delayed echo combinations), or an integer vector `a` of translates `B(· − log n)` over `ℤ` |
| Delay `π` | one double tick of the ringdown; on the state space of echoes it is the companion (Lax–Phillips) matrix of the mode polynomial |
| Count | a function `K` on probes with values in `ℕ` |
| Count law | `K` obeys the parallelogram law and is normalized on `1, π, 1 − π` by the channel numbers |
| Genus-`g` count of level `n` | `K_n(x, y) = g y² − a_n x y + g qⁿ x²` on `y − xπⁿ`, with `a_n` the trace of `πⁿ`; `K_n(1,1) = N_n + (g − 1)(qⁿ + 1)` |
| Tower count law | the count law at every level `n ≥ 1` of the base-change tower |
| Delay-covariant form | a quadratic form `S` on probes with `S(πφ) = q S(φ)`: the similitude of the delay |
| Tate limit of a count | `lim K(m a)/m²` along integer rays |
| Shell count | the number of cusp images `γ∞` of `SL₂(ℤ)` whose horoball shell at depths `[a, b)` contains a point: a pseudo-Eisenstein series of an indicator |
| Farey reading | the mean of a shell count along a closed horocycle as a sum over denominators `c`, weighted by `ϕ(c)` |
| Calibration models | true elliptic curves (Manin), fakes `(q, G, D)`, throats, the 11-vertex genus-two graph, the modular horizon |

## 3. Language

- **Open channel**: a cusp of the graph black hole, a point of a curve, a cusp image met by a source.
- **Count of a probe**: the number of points of `ℤ[π]/(φ)` or the value of a count law at `φ`.
- **Born rule for counts**: the parallelogram law.
- **Quadratic half, count half**: the two properties of a count law; the first is a statement about
  the probe ring and its involution, the second is a sign.
- **Delay covariance**: `K(πφ) = q K(φ)`: a probe delayed by one double tick has `q` times the channels.
- **Partner law**: the modes come in pairs `α`, `q/α`: the functional equation of the mode polynomial.
- **Level**: the base change `𝔽_{qⁿ}`; the count of level `n` probes `y − xπⁿ`.
- **Oscillating mode**: a mode with `t² < 4q`; **overdamped**: `t² > 4q`.
- **CM lattice**: the probe ring of an oscillating mode embedded in `ℂ`.
- **Shell, depth**: horoball regions of the cusp between heights `a` and `b`.
- **Thermalization rate**: the rate at which the horocycle mean of a source reaches its volume value.

## 4. Mechanisms

1. **A count law is determined by three numbers.** The parallelogram law on `ℤ²` determines `K` from
   `K(0,1)`, `K(1,0)`, `K(1,1)`; the channel numbers fix them, and then `K` is the genus form.
2. **The quadratic half is the partner law.** A nondegenerate quadratic form on the probe space for
   which the delay is a similitude forces the spectrum of the delay to be closed under `α ↦ q/α`.
3. **The count half is universal damping.** If such a form is positive, every mode has `|α|² = q`.
4. **Tensor power.** A count law at every level of the tower bounds every power sum by the genus, and
   power-sum elimination puts every mode on the circle.
5. **Tate.** A nonnegative function whose quadratic growth along rays is `Q` forces `Q ≥ 0`; no law
   is needed at finite size.
6. **Unfolding.** The horocycle mean of a pseudo-Eisenstein series is a sum over cusp images; the
   images with denominator `c` contribute `ϕ(c)` copies of one kernel in `c²y`.

## 5. Questions the programme answers

1. What is `K` on an integer source of the modular horizon?
2. What is the physical origin of the parallelogram law on a branched graph?
3. Does integrality of the mode data, which bounds the genus by the trivial modes, force a count when
   the trivial modes are infinite in number, as over `ℤ`?
4. Why is the form a boundary square exactly when the modes oscillate?
5. Does Hecke at a second place constrain a count, given that it does not constrain flux?
6. Why do long horocycles thermalize at rate `y^{3/4}`, and is that rate a consequence of a count?

First rung: on the genus-two graph, decide whether a parallelogram channel count exists exactly for
`q ≤ 3`, where the modes are damped, and fails for `q ≥ 4`.

## 6. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| The count law at every genus | | to prove |
| The genus-two rung | | to prove |
| The two halves of the count law | | to prove |
| The Tate limit of a count over `ℤ` | | to prove |
| The Farey reading of the horocycle | | to prove |
| Hecke supplies conservation, not the law | | to prove |

## 7. Tools

To build: a bulk construction of `K` on integer probes; a dictionary between heights on Jacobians and
solutions on branched graphs; a boundary operator algebra whose GNS form on sources is Krein;
Lyapunov functionals from counts; horoball lattice-point counts attached to sources.

## 8. Traps

| Trap | Truth |
|---|---|
| A count law is a law of wave dynamics | It is a statement about the probe ring; fakes have all the dynamics |
| Positive counts at every level exclude fakes | Fakes have groups of order `qⁿ + 1 − V_n` at every level |
| The parallelogram law needs positivity | Every norm form is quadratic; the fake fails because its count is `|𝒬|` |

## 9. Where it sits

| Neighbour | Interface |
|---|---|
| ArithmeticScatteringHolography | black holes, probes, `CountLaw`, Krein square, fakes, throats, genus-two graph |
| BlackHoleRingdown | modular horizon, pseudo-Eisenstein series, horocycle means, Zagier |
| ArithmeticCastelnuovoSeveri | curve data, Toeplitz form of traces, Hodge index on the span |
| ArithmeticEffectivityTheory | Tate limits, naive heights |
| RHTower (Farey) | Farey counts, Franel–Landau |

## 10. Success criteria, and what a contribution must be

Criteria from the review: recover Hasse from channels at all probes and Hasse–Weil at every genus;
fail on fakes through the count, not through dynamics; supply the partner law globally; fail for
non-arithmetic groups; explain the blindness of KMS, Schur, `C*` and Hecke-algebra positivity;
explain the two RH rates `e^{−t/4}` and `y^{3/4}`; be consistent with raw echo spikes and GUE.

A contribution must be a theorem about counts, state what it does on the fakes, and over `ℤ` say
where it stops.

## 11. Open research topics

A count over `ℤ` equal to the Krein square of the integer probes (this is RH); Manin's count at genus
two through a Jacobian; non-congruence and non-arithmetic groups.
