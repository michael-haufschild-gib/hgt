# FZZ replica levels 3 and 4 select the critical wall

- **ID:** FZZ-P-REPLICA-3-4-SELECTOR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** FZZ-P
- **Statement:** Passive Krein sign at cigar levels `k=3,4` is equivalent to imaginary-axis frequency.

## RH proof chain

`common FZZ mode at k=3,4` → `two level chambers` → `Re ω = 0` → centered Mellin
`Re ρ = 1/2` → reflected FZZ-P crossing/incidence → RH.

This theorem closes the selection arrow. Remaining FZZ-P burden is only source-faithful transport
of each Mellin divisor to one common mode at these two explicit CFT levels, plus the already-ledgered
crossing/incidence weld. It removes the prior full-continuum level-family premise.

## Exact statement

Let

`K_β(ω) :⇔ Im(sinh(βω/2)^2)=0 ∧ Re(sinh(βω/2)^2)≤0`.

The stronger minimal statement is

`Im(sinh(ω/2)^2)=0 ∧ Re(sinh(ω)^2)≤0 ↔ Re(ω)=0`.

Consequently, for every `ω : ℂ`,

`K_2(ω) ∧ K_1(ω) ↔ Re(ω)=0`.

Since the replica response scale is `β(a)=2a/(1-2a)`, `a=1/3` (`k=3`) gives `β=2` and
`a=1/4` (`k=4`) gives `β=1`.

## Proof `[PROVED HERE]`

Write `ω=x+iy`. If `x=0`, both squares are negatives of real squares.

Conversely assume scale-1 reality and scale-2 nonpositivity. The reality equation is

`0 = Im(sinh(ω/2)^2) = sinh(x) sin(y)/2`.

If `x≠0`, then `sinh(x)≠0`, hence `sin(y)=0`. Therefore

`sinh(ω)=sinh(x)cos(y)` and
`Re(sinh(ω)^2)=sinh(x)^2 cos(y)^2=sinh(x)^2>0`,

using `sin(y)=0 → cos(y)^2=1`. This contradicts the scale-2 nonpositive chamber. Hence `x=0`.

No continuity, all-level limit, zero classification, or numerical input is used.

## Sharpness and conjecture loop

- Full physical level continuum: sufficient in corpus, but overstrong.
- One arbitrary level: false; corpus gives an explicit off-axis strict-chamber point at every level.
- Arbitrary two levels: not claimed; coincident levels already reduce to the one-level no-go.
- Levels `k=3,4`: sufficient by the proof above, and cardinality-minimal by the one-level no-go.

Positive survivor: scale-doubling makes first-scale reality force the second-scale response real;
second-scale passivity then excludes every off-axis branch. Only two source observables are needed:
scale-1 reality and scale-2 nonpositivity.

## Novelty audit (through 2026-08)

Internal corpus search found the all-level selector and fixed-level no-go, but no finite two-level
selector. External primary-source audit covered the FZZ proof, finite-level/off-shell replica
construction, winding/oscillator level duality, and black-hole spectral-duality law. None states
this `k=3,4` selector or the continuum-to-two-level reduction. Elementary hyperbolic identities
are classical; claimed new content is their exact finite-level FZZ-P reduction and minimality.

## Gates

- [x] 0 → 1: source-pure statement and explicit FZZ-P chain
- [x] 1 → 2: complete dependency-closed paper proof above
- [x] 2 → 3: Lean theorem, targeted build, axiom audit, umbrella wire
- [ ] 3 → 4: standalone publication artifact

## Lean certificate

- Module: `GaloisForLFunctions.HTGeometry.FZZCigarReplicaTwoLevelKreinSelector`
- Strong theorem: `fzzReplicaLevelFourRealityLevelThreeNonpositive_iff_re_eq_zero`
- Full-chamber corollary: `fzzReplicaLevelsThreeFourKreinSign_iff_re_eq_zero`
- Direct Lean and targeted module build: PASS
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Umbrella: `GaloisForLFunctions.HTGeometry` wired; not built
- Lint: new module reachable and forbidden-declaration clean; global lint still fails on pre-existing
  unreachable modules outside this change.
