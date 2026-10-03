# Route PM: literal finite-band Mellin transform

- **ID:** pm-ramanujan-band-mellin
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean:** `PMRamanujanBandMellin.lean`, seven public declarations.
- **Active continuation:** `../1-in-progress/pm-ramanujan-band-spectral-escape.md`.

## Exact result and proof

For q>1, the literal primitive P_q(floor(1/t)) equals the finite signed sum

    -sum_(d*m=q) d*mu(m)*fract(1/(d*t)),     t>0.

The linear terms cancel because sum_(d*m=q) mu(m)=0. Every divisor is positive, so the existing Nyman Mellin theorem applies termwise on 0<Re(s)<1. Finite integrability and the complex-power law give

    Mellin(P_q(floor(1/t)),s)=zeta(s)/s * J_s(q),
    J_s(q)=sum_(d*m=q) mu(m)*d^(1-s).

For every finite natural band X<q<=Y, X>=1, its complete transform is zeta(s)/s times the sum of every actual a_epsilon(q)*J_s(q). For prime p, J_s(p)=p^(1-s)-1. No infinite sum is interchanged and no coefficient or endpoint is removed.

## Frontier contribution

This supplies the exact finite-source input for the proposed two-variable moving-band transform. The infinite Euler identity, Hilbert continuation, nonzero moving component and complete small-damping energy ceiling remain open. These results neither prove nor refute RH.

## Audit — 2026-10-02

- Scratch proof passed.
- `lake --old build GaloisForLFunctions.RHTower.PMRamanujanBandMellin`: exit 0; only the new leaf built.
- Final actual-file `lake env lean GaloisForLFunctions/RHTower/PMRamanujanBandMellin.lean`: exit 0, no diagnostics.
- All seven exports checked by `/tmp` axiom queries: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella wired once; no umbrella build. Global lint reported ten unrelated unreachable modules, no own-module finding.
- No added axiom, sorry, RH premise, heartbeat increase, numerical experiment or subagent.

Corpus searches129–131 informed the proof. 129/130 were complete; 131 returned partial text retrieval. Candidate statements, source arguments and suggested ingredients were inspected; no retrieval suggestion was treated as an audited theorem.
