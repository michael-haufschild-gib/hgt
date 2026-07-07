# 124 — The mirror-annulus transport: holonomy travels intact, mirror pairs drop out

Formal home: `formal/GaloisForLFunctions/RHTower/MirrorTransport.lean` (all
endpoints axiom-clean: `[propext, Classical.choice, Quot.sound]`). Builds doc 123
§7's named construction. Self-attack recorded up front: `f = (z−ρ)(z−ρ′)` is
line-symmetric with an odd mirror pair and NO on-line zero, so "off-line odd ⟹
on-line zero" is FALSE for general symmetric members; the honest transport
package is what follows.

## 1. The geometry [PROVED HERE]

The reflection is an isometry (`norm_lineReflection_sub`), maps annuli to mirror
annuli, and conjugates the circle parametrization
(`lineReflection_circleMap`): the circle at `ρ` maps to the circle at the mirror
center with the parameter reversed through `π`.

## 2. Holonomy travels intact [PROVED HERE]

`mirrorTrace U := θ ↦ conj (U (π − θ))` is a continuous root trace of the
line-symmetric member at the MIRROR circle (`mirrorTrace_sq`,
`mirrorTrace_continuousOn`) with the SAME `±1` holonomy
(`mirrorTrace_holonomy`): the antiholomorphic reflection reverses both the
traversal direction and the sheet phase, and the two reversals cancel. The
entire root-trace theory of docs 122–123 transports across the critical line
with no loss.

## 3. Zero-mass events come in mirror pairs [PROVED HERE]

`carrier_mass_zero_mirror_of_odd_isolated_zero` and the ξ-instantiation
`carrier_mass_zero_mirror_of_odd_xi_zero`: an isolated odd-order (ξ-)zero whose
annulus the carrier dominates on ONE circle empties the carrier's periodic mass
at the MIRROR circle as well — with an explicit flipping trace exhibited. One
domination certificate now yields two zero-mass circles, symmetric across the
critical line.

## 4. Mirror pairs drop out: the on-line count identity [PROVED HERE]

- `neg_one_pow_sum_reflection_equivariant`: for a configuration carried by a
  multiplicity-preserving reflection involution, the total-order parity equals
  the parity of the on-line part — free orbits pair off (`ZMod 2` involution
  cancellation; no counting machinery).
- `trace_holonomy_online_count`: every continuous root trace's holonomy at an
  annulus enclosing a reflection-equivariant configuration reads exactly the
  ON-line enclosed count mod 2. The center need not lie on the line.
- `trace_closes_of_offline_mirror_pairs`: purely off-line mirror-paired
  configurations close every trace up — the blindness of docs 120/122 as a
  positive statement: the periodic mass is the FULL modulus mass `2∮‖f‖`
  whatever the off-line pairs do.

## 5. The shape of the ledger after this pass

For a line-symmetric member, the trace/mass formalism now has a complete
transport calculus: holonomy is reflection-invariant, zero-mass events are
mirror-symmetric, and line-centered observables are exactly on-line counters.
The fork's verdict stands sharpened: within the symmetric world no boundary
observable at symmetric positions sees an off-line pair mod 2 — the
counterexample `(z−ρ)(z−ρ′)` realizes the blind spot.

What distinguishes ξ's carrier from the counterexample is therefore not
symmetry, not topology, not boundary modulus at symmetric positions — it is the
arithmetic supply: the domination certificates that pin the carrier to ξ at
specific annuli. The constraint-typed residue is unchanged from doc 123 §7 and
now maximally located:

[OPEN CORE] **One certificate.** Produce a single machine-checked domination
certificate `‖ξ − completedSEM N‖ < ‖completedSEM N‖` on one interior circle of
one isolating annulus inside the banked certificate arcs' window
(`ZetaDominationTransfer`, `completedSEM_domination_iff`, Selberg constants).
Every theorem of docs 122–124 activates on it: the zero-mass mirror pair, the
flipping traces, the on-line zero forcing at line-centered geometry. The open
core is no longer a theory question but a certificate-supply question — the
seam between the arithmetic carrier and the archimedean member, on one pinned
circle.
