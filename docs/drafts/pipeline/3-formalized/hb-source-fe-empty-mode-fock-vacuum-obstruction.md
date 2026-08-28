# HB source-FE empty-mode Fock-vacuum obstruction

- **ID:** HC82
- **Stage:** 3-formalized
- **Type:** THEOREM / DIAGONAL SHALE NECESSITY + REGULAR-FOCK NO-GO + RH ENDPOINT
- **Source:** read-only `rh-current-frontier-map.md` · HC79--HC81 source-FE Bogoliubov endpoint

## Goal

Remove HC80's dependence on an external Shale--Stinespring theorem at the hardest surviving point:
existence of an actual normalizable transformed vacuum in the corpus occupation Hilbert space.

For a Xi copy `q`, define the normalized source-FE pair recurrence ratio

`r(q) = -beta(q) / (sqrt(2) alpha(q))`,

where `alpha(q)>0` and `beta(q)` are HC79's exact bosonic coefficients. A transformed vacuum must,
at minimum, satisfy the empty-mode two-particle coefficient recurrence

`psi(mu + 2 e_n) = r(q) psi(mu)` whenever `mu(n)=0`.

Prove that a nonzero `ell^2` occupation vector satisfying this necessary recurrence exists exactly
when `r(q)=0`, hence exactly when `beta(q)=0`, partner occupation vanishes, and `Re(q)=1/2`.
Universally over all Xi copies, existence is equivalent to RH.

## Gates

- [x] 0 → 1 in-progress: corpus audit; exact conjecture frozen
- [x] 1 → 2 fully-proven: dependency-closed paper proof and bounded primary-literature audit
- [x] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom and lint audit
- [ ] 3 → 4 publication-ready: independent mathematical/physical review and broader novelty search

## Corpus audit

- `[CORPUS]` `HTGeometry.BosonicFockOperatorRealization` defines the concrete occupation Hilbert
  space `BosonicFock Nat = ell^2 (Nat →₀ Nat)` and its occupation basis.
- `[CORPUS]` `summable_sq_lp` proves square summability of every `ell^2` coordinate family.
- `[CORPUS]` `Finsupp.support` supplies the decisive finiteness: every occupation `mu` leaves
  infinitely many modes empty.
- `[CORPUS]` HC79 proves `alpha(q)^2 - ‖beta(q)‖^2 = 1`, positivity of the expanding sheet, and
  `‖beta(q)‖^2 = N(q)`.
- `[CORPUS]` HC80 proves the repeated beta block is Hilbert--Schmidt exactly on the wall, but only
  invokes the external Fock interpretation in prose.
- `[CORPUS]` HC81 kills ordinary self-adjoint QNM eigenmodes and every bounded Riesz realization,
  leaving regular Fock existence versus genuinely extended representations as the live fork.
- `[CORPUS NEGATIVE]` mandatory searches for bosonic Fock creation/annihilation, squeezed-vacuum
  recurrences, and infinite occupation coefficients found no theorem proving this exact
  coefficient-level necessity or its source-FE/RH specialization.

## Theorem HC82-A: diagonal empty-mode Shale necessity

Let `r : Nat → Complex`. If a nonzero `psi : ell^2 (Nat →₀ Nat)` satisfies

`psi(mu + single n 2) = r(n) * psi(mu)`

for every occupation `mu` and every empty mode `n`, then `∑ ‖r(n)‖² < ∞`.

In particular, if `r(n)=r` is constant, such a nonzero vector exists only if `r=0`.

### Dependency-closed paper proof

Assume `psi` is nonzero and choose an occupation `mu` with `psi(mu) ≠ 0`. Because `mu` has finite
support, choose an injective sequence `j(k)` strictly above the supremum of that support. Then
`mu(j(k))=0`, and the occupations `mu + 2 e_{j(k)}` are pairwise distinct. Restricting the square
summable coefficient family along this injection proves summability of
`‖r(j(k)) psi(mu)‖²`. Divide by the fixed positive number `‖psi(mu)‖²` to obtain square summability
of the full tail of `r`; adding its finite prefix proves `∑ ‖r(n)‖² < ∞`. For a constant family,
summability forces the constant to vanish.

The proof deliberately does not assume the vacuum coefficient `psi(0)` is nonzero; it starts from
an arbitrary nonzero coefficient. Thus no hidden cyclicity or Gaussian-product hypothesis enters.

## Theorem HC82-B: exact source-FE regular-vacuum classification

Define `HBXiPeierlsUnitSourceFEHasRegularFockVacuum q` as existence of a nonzero vector in
`HTGeometry.BosonicFock Nat` satisfying the normalized empty-mode pair recurrence with `r(q)`.
Then

`HasRegularFockVacuum(q) ↔ r(q)=0 ↔ beta(q)=0 ↔ N(q)=0 ↔ Re(q)=1/2`.

The reverse implication uses the ordinary occupation vacuum: when `r(q)=0`, it is supported only at
the zero occupation, while `mu + 2e_n` is never zero for an empty mode.

## Theorem HC82-C: global RH and receiver endpoints

Prove

`(∀ q, HasRegularFockVacuum(q)) ↔ RiemannHypothesis`,

plus exact local equivalences with HB optical darkness, Deninger Ward cancellation, FZZ-P
information equilibrium, every-grade PW-B balance, and canonical-copy RBH leading balance.

## Hostile checks

- Predicate is a necessary coefficient slice of the transformed annihilation equation, not a
  definition of the full unbounded creation/annihilation operators or their domains.
- Nonexistence of a vector satisfying this slice is enough to exclude a regular transformed vacuum;
  existence on wall is represented by the standard occupation vacuum.
- Do not claim the theorem excludes Lill-style extended Fock spaces, rigged states, or non-`ell^2`
  infinite products. Those are exactly the surviving escape.
- Do not assume a nonzero vacuum overlap. Start from an arbitrary nonzero coefficient.
- Do not use finite truncations, numerical spectra, optimized bounds, RH, Shale--Stinespring, or any
  new axiom.

## Expected route impact

HC82 upgrades HC80 from a coefficient-level Hilbert--Schmidt obstruction to a direct
regular-Fock vector nonexistence theorem. Off wall, even the weakest empty-mode pair slice of the
Bogoliubov vacuum equation has no nonzero normalizable solution. The ordinary-Fock escape is dead
without importing Shale--Stinespring. The only survivor is an extended/nonregular representation;
the next producer must explain why physical HB/QNM states select ordinary Fock normalizability or
derive a route receiver inside the extended representation.

## Bounded primary-literature audit (2026-08-28)

- `[LITERATURE]` Shale,
  [*Linear Symmetries of Free Boson Fields*](https://doi.org/10.1090/S0002-9947-1962-0137504-6),
  gives the general unitary-implementability criterion, not this source-specific occupation-slice
  proof or an iff-RH endpoint.
- `[LITERATURE]` Lill,
  [*Bogoliubov Transformations Beyond Shale--Stinespring: Generic v* v for bosons*](https://arxiv.org/abs/2208.03487),
  states regular Fock implementability only under the trace-class condition and constructs an
  extended implementation without it. This confirms both the regular obstruction and the precise
  extended-representation survivor.
- `[LITERATURE]` Lill,
  [*Implementing Bogoliubov Transformations Beyond the Shale--Stinespring Condition*](https://arxiv.org/abs/2204.13407),
  constructs extensions of a dense Fock subspace when the ordinary condition fails; it does not
  prove the arbitrary-nonzero-coefficient empty-mode replication lemma used here.
- `[LITERATURE]` Qin--Wang--Li,
  [*General Multimode Squeezed States*](https://arxiv.org/abs/quant-ph/0109020), develops finite- or
  general-multimode squeezed states and Bogoliubov decompositions, but no literal Xi source-FE
  coefficient, infinite repeated-ratio `ell^2` no-go, or RH equivalence.
- `[NOVELTY CLAIM, BOUNDED]` Targeted primary-source and exact corpus searches found no Lean theorem
  deriving square summability of an arbitrary diagonal pair-ratio family directly from this
  empty-mode coefficient recurrence and an arbitrary nonzero occupation coefficient, nor any result
  coupling that necessity theorem to the literal Xi source-FE ratio and deriving the route receiver
  and iff-RH endpoints. This is a bounded audit, not an exhaustive literature claim.

## Formalization result

Module:
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFERegularFockVacuumObstruction`

Lean proves unconditionally:

- every nonzero occupation-Hilbert vector satisfying an arbitrary diagonal empty-mode pair
  recurrence forces square summability of the complete ratio family;
- a constant nonzero ratio admits no nonzero normalizable recurrence vector;
- a nonzero constant-ratio recurrence vector exists iff the ratio is zero, with the ordinary
  occupation vacuum providing the reverse implication;
- the literal source-FE normalized ratio has a nonzero denominator and vanishes iff the HC79 pair
  amplitude and partner occupation vanish iff the Xi copy lies on the critical wall;
- universal existence over all Xi copies is equivalent to RH;
- exact local equivalences with HB optical darkness, Deninger Ward cancellation, FZZ-P information
  equilibrium, every-grade PW-B balance, and canonical-copy RBH leading balance.

Audit:

- direct `lake env lean` check: passed;
- targeted `lake build
  GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFERegularFockVacuumObstruction`: passed
  `12186/12186`;
- `#print axioms` on diagonal necessity, constant existence classification, global iff-RH, and RBH
  bridge: only standard `[propext, Classical.choice, Quot.sound]`;
- formal lint: no finding in HC82 or its umbrella wiring; global failure remains only unrelated
  pre-existing/shared unreachable modules.

## Open core after HC82

Ordinary occupation-Hilbert vacuum existence is dead off wall without importing
Shale--Stinespring, and the result survives arbitrary diagonal ratios as an internal necessity
theorem. The live escape is now genuinely nonregular: Lill-style extended Fock space, rigged states,
or an unbounded/non-Riesz QNM synthesis. Hardest next producer is to formalize the extended-state
quotient or renormalized coefficient law and decide whether the HB/FZZ-P/PW-B/RBH receiver remains
defined there. If it does, prove whether receiver equilibrium still forces square summability; if it
does not, retire the Fock endpoint and extract the exact representation-selection hypothesis needed
for the physical route.
