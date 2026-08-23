# Theta-cusp Hawking modular-boost endpoint (2026-08-23)

File: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingModularBoostEndpoint.lean`
Umbrella: imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Result
- [LITERATURE] Wedge modular evolution is a Lorentz boost (Bisognano-Wichmann); horizon restriction of a doubled pure state produces Hawking thermality (Israel); reduced Hawking modes are quantum amplifier/Gaussian channels.
- [PROVED] At source coordinate x, aperture a is exactly `lorentzBoost (-(a*x))` on the even source datum `[k(x),0]`.
- [PROVED] Light-cone rays are `[exp(-a*x)k(x), exp(a*x)k(x)]`, exactly the tilted theta source at x and reflected partner at -x for |a|<1.
- [PROVED] Apertures compose as a reversible boost group; ray product and even/odd Krein norm equal `k(x)^2`.
- [PROVED] Reduced gain `cosh(r)^2` and partner number `sinh(r)^2` satisfy the CCR difference 1.
- [PROVED] Persistent-partner coherent gain differs from a fresh-vacuum Markov reset:
  `cosh(r+s)^2 - cosh(r)^2 cosh(s)^2
   = 2 cosh r cosh s sinh r sinh s + sinh(r)^2 sinh(s)^2 > 0`
  for r,s>0.
- [FALSIFIED] Aperture itself cannot be identified with serial reduced Hawking amplifiers having a reset environment. This misses a strictly positive partner-memory term.
- [PROVED] Fourier observation of one physical ray equals `xi(1/2+a+ib)` and the existing Hawking strip pair amplitude.
- [REDUCTION] No observed power backflow under the exact modular source flow is equivalent to amplifier CP divisibility and hence RH.
- [OPEN CORE] Derive observed passivity from persistent-partner dynamics (likely a source-specific QEI/natural-cone/Weil parity coherence theorem). Generic boost/KMS algebra is insufficient because Fourier observation does not preserve pointwise future-cone order.
- [NOVELTY UNVERIFIED] Exact theta-cusp boost plus strict partner-memory obstruction was absent from targeted corpus and primary-literature searches; no exhaustive novelty claim.

## Verification
- `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingModularBoostEndpoint.lean` passed.
- Target olean built.
- `#print axioms` for source-ray, boost, purity, memory, observation, and RH endpoint theorems: only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint` passed.
