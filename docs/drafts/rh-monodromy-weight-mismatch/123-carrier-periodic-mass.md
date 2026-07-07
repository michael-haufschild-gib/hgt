# 123 — The carrier's periodic mass: all-or-nothing, sign-readable, seam-emptied

Formal home: `formal/GaloisForLFunctions/RHTower/CarrierPeriodicMass.lean` (all
endpoints axiom-clean: `[propext, Classical.choice, Quot.sound]`). Builds the
object doc 122 §5 named: the periodic mass of the finite carrier's own root
trace — as a complete theory, not an estimate.

## 1. The mass is modulus-determined and quantized [PROVED HERE]

- `trace_normSq_eq_norm`: the pointwise L² density of ANY root trace is `‖f‖`
  on the circle — trace-independent, branch-independent.
- `doubledTrace_self_pairing_value`: at even holonomy the self-pairing attains
  exactly `2∮‖f‖`.
- With the banked vanishing theorem: **the periodic mass takes exactly two
  values, `0` or `2∮‖f‖`**, according to the holonomy. No intermediate values,
  no choice-dependence: a mass gap of width the full circle modulus mass
  (`circle_modulus_mass_pos`: strictly positive for annulus-nonvanishing
  members).

## 2. Traces exist unconditionally on nonvanishing annuli

`exists_chartLA_sqrt` + `exists_circle_trace`: analytic + nonvanishing on the
annulus produces a continuous square-root trace along every interior circle
(both slit charts are simply connected; the two-chart `rootTrace` assembles
them).

## 3. Line symmetry reads the mass on two real numbers

`trace_holonomy_of_sign`: for a line-symmetric member on a line-centered
annulus, EVERY trace closes up when the (real) port values have positive
product and flips when negative — the canonical pair of doc 120 supplies the
chart data, and doc 122's rigidity makes the answer trace-independent. The
periodic mass of the carrier at radius `r` is decided by the sign of
`Re f(a+ri) · Re f(a−ri)`.

## 4. A sign change vanishes ON the line inside the hole

`exists_online_zero_of_port_sign_change`: negative port product forces
`f(a + ti) = 0` for some `|t| ≤ r₀` — the member is real along the vertical
segment (reflection-fixed points), continuous through the hole, nonvanishing on
the annulus; the intermediate value theorem places the zero in the closed hole.
Zero periodic mass is not an abstract parity: it is an on-line zero of the
member at distance `≤ r₀` from the center.

## 5. The carrier instantiation [PROVED HERE]

At critical-line-centered annuli (`a.re = 1/2`, `R ≤ 1/2`) with the carrier
nonvanishing on the annulus:

- `exists_carrier_trace`: the carrier's root trace exists.
- `carrier_periodic_mass_of_sign_pos`: positive port product ⟹ every trace
  closes up, the self-pairing equals `2∮‖completedSEM N‖ > 0`.
- `carrier_periodic_mass_of_sign_neg`: negative product ⟹ every trace flips,
  every finitely-periodic probe is annihilated, and **the carrier vanishes on
  the critical line inside the closed hole**.

The carrier's periodic mass is now a two-point observable of the finite real
function `t ↦ Re completedSEM N (a + ti)` — a Hardy-Z-type object at finite
level — with the all-or-nothing value `{0, 2∮‖completedSEM N‖}`.

## 6. The seam: odd zeros empty the carrier's mass [PROVED HERE]

- `carrier_mass_zero_of_odd_isolated_zero`: an isolated odd-order zero of ANY
  member `g`, with a carrier nonvanishing on the annulus and dominating
  `‖g − F‖ < ‖F‖` on one interior circle, flips every carrier trace — the
  carrier's periodic mass at that circle is ZERO.
- `carrier_mass_zero_of_odd_xi_zero`: the ξ-instantiation. A hypothetical
  odd-order off-line ξ-zero, dominated by the finite carrier on one circle,
  forces a zero-periodic-mass circle for the explicit finite object
  `completedSEM N` at an off-line center.

## 7. Where the question now stands

The mass object is complete: quantized values, sign-readability on the line,
existence, and the seam transfer are theorems. RH₂'s negation now produces a
concrete finite-object event: a circle on which the finite carrier's root trace
is orthogonal to every periodic voice — equivalently (off-line center version
of §4 unavailable: no line symmetry there) a circle where the carrier's own
enclosed zero count is odd.

Two constraint-typed forward moves:

[CONJECTURE] **Domination is purchasable at isolating annuli.** The banked
domination arcs (`ZetaDominationTransfer`, `completedSEM_domination_iff`,
Selberg-transfer constants) supply `‖ξ − completedSEM N‖ < ‖completedSEM N‖`
on circles for suitable `N` at bounded heights; welding one such certificate to
`carrier_mass_zero_of_odd_xi_zero` makes the zero-mass event unconditional at
the certificate's window.

[OPEN CORE] **The carrier's own mass positivity off the line.** The finite
carrier at an off-line center: its enclosed count is a finite question about an
explicit function's zeros in a disc. The line-symmetric pairing of the
carrier's zeros (its zeros come in reflection pairs, `completedSEM_orderAt`
identities) means an odd off-line count forces an on-line carrier zero in the
REFLECTED geometry — transporting §4's on-line zero conclusion to off-line
centers via the mirror annulus is the next construction: one reflection, two
annuli, one shared on-line segment.
