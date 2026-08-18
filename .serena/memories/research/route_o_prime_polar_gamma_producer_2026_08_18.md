# Route O actual-head prime–polar–Gamma producer (2026-08-18)

Created `formal/GaloisForLFunctions/RHTower/CCMActualHeadGammaAutocorrelationEnergy.lean` and `formal/GaloisForLFunctions/RHTower/CCMRestrictedWeilActualHeadPrimePolarGammaProducer.lean`; wired both into `RHTower.lean`.

New exact infrastructure and science:
- `kΓ(h)=exp(-h/2)/(1-exp(-2h))` and scalar Binet law `∫₀∞(2-2cos(2πξh))kΓ(h)dh=2(γ(2πξ)-γ(0))`.
- Tonelli/Plancherel theorem on every actual complex `L²` head: weighted physical squared translation loss equals spectral Γ excess.
- Full CCM form-domain theorem: `GammaDefect(A_a u)=||u||²-||A_a u||²`.
- Producer `P=2γ(0)||f||²+GammaDefect(f)+CompletedErrorQuadrature(a,f)` equals literal restricted-Weil source quadratic.
- On canonical finite Γ-Slepian heads: producer = ground energy times head mass + certified tail defect; producer nonnegativity iff literal reverse-prime bound.

Hostile kill: universal pointwise Γ–polar autocorrelation positivity is false/unlawful because projected finite heads may have negative autocorrelations. Squared increments are the lawful positive carrier.

Validation: `lake env lean` on both leaves passed; targeted `lake build GaloisForLFunctions.RHTower.CCMRestrictedWeilActualHeadPrimePolarGammaProducer` passed; `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`. `scripts/formal_tools.py lint` still fails only on six unrelated pre-existing unreachable HTGeometry modules. Route map was not edited. Remaining RH core: prove nonnegativity of this explicit same-head producer cofinally/on canonical finite heads.