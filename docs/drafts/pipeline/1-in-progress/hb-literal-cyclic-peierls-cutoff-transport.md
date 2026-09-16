# HB literal cyclic Peierls cutoff transport

- **ID:** HB-B2-cutoff-transport
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md`, HB; `ThetaCuspHawkingBMStreamFrequencyDefectCochain.lean`; own facts F361, F363, F365--F371
- **Statement:** The literal retarded/left-QNM two-leg action is a relative transport on the joint frequency--cutoff boundary whose source-pole holonomy is exactly the retained `contactField`; hence its completed boundary is `mixedField`.

## Goal

Close or kill the only shared HB/FZZ-P/PW-B B2 producer:

`unit onset residue → complete original and reduced source residues → frequency-defect cochain → finite two-leg Green/action balance → cap holonomy = contact → mixedField Peierls boundary → extinction/RH receiver`.

This is non-circular: neither RH, Peierls extinction, a global propagator, nor a cap cancellation is assumed.

## Frozen physical hunch

The cap is not an error term.  It is parallel transport in the cutoff coordinate.  Frequency-defect and cap are the two components of one relative transgression; their boundary holonomy has no free normalization and equals the ingoing contact retained in `mixedField`.

In a joint frequency/cutoff chart, the unproved law is `dA = Φdefect·dw + Φcap·dR`, with source-pole residue of `Φdefect` fixed by F370--F371 and `lim R→∞ Φcap = contactField`.  Its completed boundary must be `mixedField`.

## Why this is a new primary conjecture

- **Compression:** F361 makes contact absent from the local cochain; F363 fixes finite action plus contact; F365 forbids chamber relabelling; F366 supplies all eight finite faces; F367 and F370--F371 fix the pole coefficients.  One relative-transport law explains all five facts.
- **Ontological reversal:** cutoff is a coordinate/connection, not a regulator to remove.
- **Risky prediction/falsifier:** exact finite-face specialization has one forced source-pole cap coefficient.  If it differs from the fixed contact coefficient, the nonzero holonomy kills this literal realization; no renormalization is available.
- **Unoccupied residue:** existing causal pairing is frequency-free and existing meromorphic Green/source objects do not exchange through the improper causal pairing.  No corpus theorem constructs this joint transport.

## Gates

- [x] 0 → 1: source-pure target, chain, falsifier, and source residues fixed.
- [ ] 1 → 2: dependency-closed paper proof of finite-face specialization, polar noncompact limit, and cap/contact identification—or a no-go with positive survivor.
- [ ] 2 → 3: closed Lean theorem(s), targeted `lake env lean` checks, final needed-module audit, standard axioms only.
- [ ] 3 → 4: standalone proof and RH receiver audit.

## Attack sequence

1. Define the literal finite two-leg action from the actual off-frequency polarized metric/source fields; specialize the eight-face rectangle identity with every face explicit.
2. Prove its frequency increment is the existing defect cochain and its finite cutoff increment is the retained contact-renormalized action from F363.
3. Construct the noncompact polar/left-QNM limit without passing through the forbidden physical chamber.
4. Compare the limiting cap trace coefficient to `contactField`. Equality closes B2; inequality yields the required no-go and its exact surviving holonomy invariant.

## No-go closure (if falsified)

- **Exact killing mechanism:** nonzero source-pole cutoff holonomy after all eight faces and cap terms are retained.
- **Strongest positive survivor:** the explicit holonomy/contact mismatch coefficient and its parameter regime.
- **Status:** not yet tested; no cancellation is presumed.
