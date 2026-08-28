# PW-B/FZZ-P/Deninger recoil--information--Ward transmutation

- **ID:** PW-B-HC40
- **Stage:** 3-formalized
- **Type:** THEOREM / three-route exact positive transmutation
- **Sources:** `ThetaCuspHawkingParikhWilczekBorelPartnerEndpoint` +
  `FZZCigarParityDeningerInformationWardTransmutation`
- **Frontier map:** read-only; no edit permitted

## Frozen conjecture

At Borel grade `k`, let

`I_k(s) = Re R_k(s) - Re R_k(1-s)`

be the first-winding Parikh--Wilczek partner-growth imbalance and define

`P_k = 2(2k+1)/(k+1)^2 > 0`.

For every Xi divisor copy `q`, with HC38 Deninger Ward charge `D(q)` and nonlinear FZZ
information force `F(Re q)`, conjecture:

1. `I_k(q) = -P_k Re D(q)` exactly;
2. `I_k(q) = (P_k/C(Re q)) F(Re q)` exactly, where HC38 proves `C>0`;
3. at every grade, PW partner balance, FZZ information equilibrium, and Deninger reflect-gauge
   equivariance are pointwise equivalent;
4. universal balance at any one fixed grade is equivalent to RH.

This tests whether recoil activation supplies a genuinely new charge or only a positive
renormalization of the shared HC38 open core.

## Paper proof

Existing PW-B source algebra gives

`I_k(s) = 4(2k+1)(Re s-1/2)/(k+1)^2`.

HC38 gives `Re D(q)=1-2 Re q` and `F=(2 Re q-1)C=-C Re D`. Substitution yields both
transmutation identities; positivity of `P_k` and `C` preserves signs and zeros. The three
pointwise equilibrium statements are therefore equivalent. Universality over divisor copies is
equivalent to RH by the existing divisor endpoint.

## Corpus audit

Mandatory searches on 2026-08-28 included:

- `scripts/formal_tools.py research "Parikh Wilczek Mellin jet reflection ratio zero critical line real part"`
- `scripts/formal_tools.py research "schwarzschildParikhWilczekMellinJet nontrivial zero formula reflection"`
- `scripts/formal_tools.py research "FZZ parity dark mode Parikh Wilczek backreaction activation Ward charge"`
- `scripts/formal_tools.py research "PW recoil Mellin response reflected norm equality iff critical line"`
- `scripts/formal_tools.py research "Hawking backreaction jet zeta zero activation conjugate reflection"`
- `scripts/formal_tools.py research "Parikh Wilczek Mellin jet all positive orders nonzero divisor"`

Corpus proves PW activation, PW Borel partner imbalance, and HC38 FZZ/Deninger transmutation
separately. It has no exact positive three-route conversion theorem.

## Literature boundary

Primary sources checked on 2026-08-28:

- Parikh--Wilczek, *Hawking Radiation as Tunneling*, arXiv:hep-th/9907001;
- Hatsuda, *Quasinormal modes of black holes and Borel summation*, arXiv:1906.07232;
- Hikida--Schomerus, *The FZZ-Duality Conjecture -- A Proof*, arXiv:0805.3931;
- Deninger, *A dynamical systems analogue of Lichtenbaum's conjectures on special values of
  Hasse--Weil zeta functions*, arXiv:math/0605724;
- Connes--Consani, *The Scaling Hamiltonian*, arXiv:1910.14368.

Search found no Parikh--Wilczek/FZZ/Deninger information--Ward identity. Component physical and
cohomological frameworks are prior art; novelty claim is bounded to exact three-route conversion
and burden unification.

## Formal theorem

Module:
`GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekFZZDeningerWardTransmutation`

The formalization proves unconditionally:

1. PW-to-Deninger grade multiplier `P_k` is strictly positive;
2. PW partner-growth imbalance is exactly `-P_k` times real Deninger Ward charge;
3. it is exactly the positive ratio `P_k/C(Re q)` times nonlinear FZZ information force;
4. PW imbalance and FZZ force have strictly positive product at every off-line divisor copy;
5. zero PW imbalance, zero FZZ force, and Deninger reflect-gauge equivariance are pointwise
   equivalent;
6. universal balance at any one fixed Borel grade is equivalent to RH.

## New route knowledge and remaining burden

HC40 shows positive recoil activation does not add an independent RH charge: the actual selector is
reflected Hawking/CPT partner imbalance, and that imbalance is the same oriented charge as HC38's
FZZ information gradient and Deninger commutator. The conversion is sign-faithful at every Borel
grade.

This does **not** derive physical partner balance. Remaining shared producer is now more precise:
prove from coefficient-faithful evaporation/CTP dynamics that forward and reflected first-winding
growth rates balance on every divisor mode. Switching among PW-B, FZZ-P, and Deninger languages or
using brightness alone cannot discharge it.

## Verification

- direct check:
  `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekFZZDeningerWardTransmutation.lean`;
- targeted build:
  `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekFZZDeningerWardTransmutation`
  passed (`8834` jobs);
- `#print axioms` on all eight public theorems reported only `propext`, `Classical.choice`, and
  `Quot.sound`;
- formal lint reported no HC40 finding; repository-wide lint still reports unrelated pre-existing
  unreachable modules;
- module is wired into `GaloisForLFunctions.RHTower`; full umbrella build intentionally not run;
- frontier map remained read-only and untouched.

## Expected burden separation

If proved, recoil activation alone is not a producer: every positive jet is bright even on the
critical line. Only reflected partner balance carries the Ward zero, and that balance is the same
charge already isolated by FZZ information flow and Deninger equivariance. Remaining physical
core becomes derivation of Hawking/CPT partner balance from coefficient-faithful evaporation
dynamics.

## Status

- [x] corpus-led conjecture frozen
- [x] dependency-closed paper proof
- [x] Lean formalization
- [x] direct check, targeted build, axiom/lint audit, umbrella wiring
- [x] bounded literature audit
- [x] move to `3-formalized`
