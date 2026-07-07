# 125 — The certificate, activated: unconditional zero-mass mirror pairs

Formal home: `formal/GaloisForLFunctions/RHTower/CertificateActivation.lean`
(all endpoints axiom-clean: `[propext, Classical.choice, Quot.sound]`).
Discharges doc 124 §5's open core — and it was a supply-line discovery, not a
new estimate: the certificate already existed in the tree.

## 1. The find

`EMAnnulusSupply.lean` (banked in a parallel arc) proves the unconditional
supply for the **plain completed EM carrier** `completedEM N = archFactor ·
emCarrier N`: at every point of the open strip there exist an isolating
annulus and a truncation length with
`‖ξ − completedEM N‖ < ‖completedEM N‖` on the two slit charts
(`exists_isolating_em_domination` — EM remainder decay `N^{−σ₀}` against a
compactness floor for ζ; no analytic interface).

Docs 122–124's seam capstones were deliberately stated for a GENERIC carrier
`F`, so the weld is direct. The symmetrized carrier `completedSEM` is not
needed here: the mirror pair comes from ξ's own order pairings, not from
carrier symmetry.

## 2. The activation [PROVED HERE]

`carrier_mass_zero_at_odd_xi_order`: at any strip point of odd ξ-order there
exist — unconditionally — an isolating annulus `(r₀, R)`, the interior circle
`r = (r₀+R)/2`, and a truncation length `N ≥ 1` such that:

- the completed EM carrier is nonvanishing on the annulus (domination forces
  it),
- its continuous square-root trace along the circle EXISTS,
- EVERY such trace flips (`V(3π/2) = −V(−π/2)`), and
- every finitely-periodic probe is annihilated: the carrier's periodic mass at
  that circle is ZERO.

`xi_orderAt_lineReflection`: the ξ-order at the reflection across the critical
line agrees with the order at the point (functional-equation pairing composed
with the reality pairing).

`carrier_mass_zero_mirror_pair_at_odd_xi_order`: both events at once — the
zero-mass circle at `ρ` AND at `1 − conj ρ`, each with its own unconditional
certificate.

## 3. What the stack now says, end to end

The chain from docs 117–125, every link machine-checked and axiom-clean: if
the base rung fails — an off-line ξ-zero of odd order exists — then an
EXPLICIT finite object misbehaves in an explicit quantized way: some
truncation `completedEM N` of the Euler–Maclaurin carrier has a circle, in a
mirror pair across the critical line, on which its square-root trace is
orthogonal to every periodic voice — periodic mass exactly `0` where the
all-or-nothing law otherwise pins it to the full modulus mass `2∮‖completedEM
N‖ > 0`. Contrapositive, RH₂ reads: **every circle of every truncation of the
finite carrier at every strip annulus dominated onto ξ carries full periodic
mass.**

No hypothesis of the 122–125 stack remains open. The parity question is now a
question about finite Dirichlet-type sums and their square-root traces on
explicit circles.

## 4. Forward

[CONJECTURE] **Finite-object mass positivity.** For the finite carrier
`completedEM N` — an explicit entire-on-strip function built from `N` terms —
the zero-mass event at a circle is equivalent (by the count identity) to an
odd zero count of `emCarrier N` in the hole. The zeros of the FINITE carrier
are algebraically accessible objects (zeros of generalized Dirichlet
polynomials); their off-line/on-line disposition at dominated annuli is now
the entire content of the base rung. The lane's next object: the zero
geometry of `emCarrier N` as `N` grows — as a CONSTRAINT system (which
configurations are compatible with domination onto ξ at the same annulus),
not as a flow in `N`.

[OPEN CORE] Carry the count identity (`trace_holonomy_online_count`) onto
`completedEM N` at the dominated annulus: the carrier's enclosed count is odd
there iff ξ's order is odd (holonomy transfer already forces the traces to
agree) — formalizing the count-level statement makes the finite-carrier zero
disposition the literal negation surface of RH₂.
