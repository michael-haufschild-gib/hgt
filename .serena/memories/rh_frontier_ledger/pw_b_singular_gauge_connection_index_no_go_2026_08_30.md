# PW-B singular-gauge connection-index route kill (2026-08-30)

Formalized exact PW logarithmic singular gauge:
- Module: formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekSingularGaugeConnectionIndexNoGo.lean
- Capstone: RHTower.pwSingularGauge_connectionIndex_noGo
- Card: docs/drafts/pipeline/3-formalized/pw-b-singular-gauge-connection-index-no-go.md
- Umbrella: imported by formal/GaloisForLFunctions/RHTower.lean

Mathematics:
- In t=log x, exact gain is a(t)=exp(2 phi(t)), phi(t)=sinh(t)-t/2, and phi'(t)=cosh(t)-1/2>0.
- Horizontal sections of d/dt-phi' are exactly c exp(phi); of d/dt+phi' are exactly c exp(-phi).
- Finite square energy forces c=0 for both orientations, so natural kernel-imbalance/Witten index is zero.
- Positive reflection-unitarizing densities for T f(t)=a(t)f(-t) are exactly w(t)=a(t)^(-1)h(t) with arbitrary positive even h.
- T preserves maximal weighted-energy domain and exact total energy for every such density.
- Consequence: singular PW carrier alone cannot provide intrinsic edge index or source-independent Hilbert calibration. Surviving PW-B chain needs external source-normalized domain/measure or direct source-dynamical partner balance.

Verification:
- lake env lean on module: pass
- targeted lake build module: pass
- #print axioms: only propext, Classical.choice, Quot.sound
- global formal lint remains red only on unrelated pre-existing umbrella reachability failures; no new module failure
- no full umbrella build; no stale Lean process from this task.