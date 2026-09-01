# FZZ higher-genus cycles 1 and 2 realize the dyadic Mellin wall selector

- **ID:** FZZ-P-HIGHER-GENUS-MELLIN-CYCLE-SELECTOR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** FZZ-P
- **Statement:** Reciprocal FZZ holonomies at cycles `1,2` of one fixed cigar CFT realize the
  dyadic Mellin character and select `Re rho = 1/2` by one reality and one passivity test.

## RH proof chain

`literal parity-Mellin Gamma-zeta divisor mode rho`
→ `canonical torus twist tau(rho)`
→ `same-CFT reciprocal holonomies at cycles 1,2`
→ `cycle-1 odd-square reality + cycle-2 odd-square nonpositivity`
→ `Re rho = 1/2`
→ `reflected FZZ-P divisor incidence`
→ `RH`.

This theorem closes the common-mode/scale-transport arrow: changing cigar level is unnecessary.
Remaining FZZ-P burden is the source-specific torus replica-area Ward theorem placing every literal
divisor mode in the two stated holonomy chambers, followed by the already-ledgered incidence weld.

## Exact statement

For integer cycle number `n` and twist `tau`, put

`B_n(tau)=exp(2 pi n i tau)`, `G_n(tau)=exp(-2 pi n i tau)`, and
`O_n(tau)=(B_n(tau)-G_n(tau))/2`.

For `n != 0`,

`Im(O_n(tau)^2)=0 and Re(O_(2n)(tau)^2)<=0  iff  Im(tau)=0`.

At positive dilaton slope `b`, this is also equivalent to zero radial monodromy and
`norm(B_n(tau))=1`.

Define the universal centered Mellin twist

`tau(rho) = -i ((rho-1/2) log 2)/(2 pi)`.

Then

`B_1(tau(rho)) = exp((rho-1/2) log 2)`,
`B_2(tau(rho)) = B_1(tau(rho))^2`, and

`Im(O_1(tau(rho))^2)=0 and Re(O_2(tau(rho))^2)<=0  iff  Re(rho)=1/2`.

## Proof `[PROVED HERE]`

Let `z=2 pi n i tau`. Reciprocal exponentials give
`O_n(tau)=(exp z-exp(-z))/2=sinh z`; quantized cycle doubling gives
`O_(2n)(tau)=sinh(2z)`.

The already proved sharp two-scale identity is

`Im(sinh(z)^2)=0 and Re(sinh(2z)^2)<=0  iff  Re(z)=0`.

It follows directly by applying the levels-3/4 selector to `omega=2z`. Since
`Re(z)=-2 pi n Im(tau)`, positivity of `pi` and `n!=0` give
`Re(z)=0 iff Im(tau)=0`. Existing higher-genus redshift identities then give the radial-monodromy
and unit-holonomy equivalences for `b>0`.

For the Mellin twist, cancellation of `2 pi` and `i(-i)=1` gives

`2 pi i tau(rho)=(rho-1/2) log 2`.

Exponentiating proves the dyadic-character identity; doubling the cycle squares it. Moreover

`Im(tau(rho))=-(log 2)/(2 pi) (Re(rho)-1/2)`.

Since `log 2>0` and `pi>0`, `Im(tau(rho))=0 iff Re(rho)=1/2`. Substitution into the general
cycle selector proves the final equivalence. No zero classification, computation, level variation,
or dynamical assumption occurs.

## Conjecture loop and hostile audit

- **C1:** transport one spectral mode between levels `k=3,4`. Rejected: changing `k` changes CFT;
  corpus supplies no canonical cross-level state identification.
- **C2:** cycle number scales the black-hole spectral response. Rejected: corpus proves cycle scaling
  only for higher-genus holonomy; extending it to a scattering response is unsupported.
- **C3:** use the odd part of the actual reciprocal beta/gamma holonomies at cycles `n,2n`. Proved:
  it is exactly the needed two-scale hyperbolic response inside one fixed CFT.

Strongest positive survivor: the physical scale pair is homological, not cross-level. One twist mode
in one CFT supplies both scales, and its cycle-1 holonomy is exactly the corpus's centered dyadic
Mellin character under a universal, zero-independent coordinate map.

## Novelty audit (through 2026-08)

Internal corpus search found higher-genus reciprocal holonomies, the dyadic Mellin character, and the
`k=3,4` algebraic selector, but no theorem identifying them or removing cross-level transport.
Primary-source audit covered arbitrary-closed-surface FZZ duality, higher winding perturbations,
twisted cigar spectral asymmetry, and 2025 off-shell winding-replica entropy. None states this
same-CFT cycle-1/2 Mellin selector or supplies the still-open torus Ward sign. Novelty claim is scoped
to the exact representation theorem and proof-burden reduction, not the classical exponential or
hyperbolic identities.

## Gates

- [x] 0 → 1: source-pure statement and explicit FZZ-P chain
- [x] 1 → 2: complete dependency-closed proof above
- [x] 2 → 3: Lean theorem, targeted build, axiom audit, umbrella wire
- [ ] 3 → 4: standalone publication artifact

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.FZZCigarParityHigherGenusMellinCycleSelector`
- General selector: `fzzHigherGenusCyclePairKreinSign_iff_im_eq_zero`
- Radial/unitary forms: `fzzHigherGenusCyclePairKreinSign_iff_radialMonodromy_eq_zero`,
  `fzzHigherGenusCyclePairKreinSign_iff_norm_beta_eq_one`
- Mellin embedding: `higherGenusBetaTwistMultiplier_mellinTorusTwist_eq_dyadicCharacter`,
  `higherGenusBetaTwistMultiplier_two_mellinTorusTwist_eq_dyadicCharacter_sq`
- Critical-line endpoint: `fzzCigarParityMellinCyclePairKreinSign_iff_re_eq_half`
- Direct Lean and targeted module build: PASS
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Umbrella: `GaloisForLFunctions.RHTower` wired; not built
- Lint: new module reachable and forbidden-declaration clean; global lint fails only on pre-existing
  unreachable modules outside this change.
