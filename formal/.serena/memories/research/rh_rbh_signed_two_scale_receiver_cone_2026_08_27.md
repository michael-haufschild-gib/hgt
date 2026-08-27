# RBH signed two-scale receiver cone (2026-08-27)

Formalized `GaloisForLFunctions.RHTower.ReflectedBiHeatSignedTwoScaleReceiverCone` and wired it into `RHTower.lean`.

Exact abstract classification for `F_{a,b}(t)=a sinh(t)+b sinh(2t)`:

`∀t, F(t)=0 ↔ t=0` iff `(b=0 ∧ a≠0) ∨ (b≠0 ∧ 0≤b(a+2b))`.

Proof factors `F=sinh(t)(a+2b cosh t)`. Inside cone, the second factor cannot vanish off wall. Outside cone, `c=-a/(2b)>1` and `t=arcosh c>0` is an explicit false-balance zero.

Bridged to physical RBH multiplicity-leading diagonal gaps at apertures `x` and `x²`:

`Gap = 2 |C(rho)|² F_{a,b}(log x (Re rho - 1/2))`.

Thus every coefficient pair in the exact cone gives an RH-equivalent receiver. In particular `(-2,1)` is genuinely signed and lies outside the prior entrywise-nonnegative matrix cone, while `sinh(2t)-2sinh(t)=2sinh(t)(cosh(t)-1)` is wall-selective.

Direct check and targeted build passed. Five principal theorems audited with only `propext`, `Classical.choice`, `Quot.sound`. Card: `docs/drafts/pipeline/3-formalized/reflected-bi-heat-signed-two-scale-receiver-cone.md`. Frontier map remained read-only.