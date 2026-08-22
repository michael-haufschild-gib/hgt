# Nonreciprocal Wilson source firewall and EWQ orientation lift

- **ID:** NW-EWQ
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** arXiv:2607.18215 · whole-corpus route audit
- **Statement:** Passive reverse-adjoint link systems have zero real directional Wilson contrast, while an active Pauli link word gives a coefficient-faithful linear orientation lift whose square is the EWQ--Hedenmalm reflected crossing.

## Goal

Determine whether directional non-Hermitian Wilson transport supplies the missing source-native
orientation law for any live RH route.  Separate an unconditional active-link source theorem from a
receiver that merely reports the centered Xi grade after divisor selection.

## Gates

- [x] 0 → 1  in-progress: paper mechanism is well-posed; passive-source obstruction and active Pauli attack are explicit
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, exact leaf build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

1. Prove reverse-adjoint Wilson reciprocity: reverse trace is the conjugate of forward trace, so
   real and absolute directional contrasts vanish for every passive Hermitian/Gram carrier.
2. Build the minimal active non-Hermitian Pauli word modeled on the paper's ordered plaquette and
   prove its signed contrast is linear in the source amplitude while magnitude contrast is blind.
3. Weld that contrast to the exact EWQ--Hedenmalm crossing and test whether the completed EWQ jet
   supplies a pre-divisor, independent source law or only a nowhere-zero auxiliary carrier.
4. Audit implications for every route family using the source/receiver firewall.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** pending
- **Strongest positive survivor:** pending
- **New insight:** pending
- **Status:** active heavy-conjecturing loop

## Log

- 2026-08-22 — created directly in 1-in-progress after paper extraction and whole-corpus novelty search
