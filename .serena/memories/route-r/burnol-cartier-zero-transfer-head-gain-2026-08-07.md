# Route R Burnol Cartier zero-transfer head gain (2026-08-07)

Formalized module: `formal/GaloisForLFunctions/RHTower/BurnolCartierZeroTransferHeadGain.lean`; umbrella import present.

Conjecture loop:
1. Total-space functional-equation sewing falsified: cosine swaps rho and 1-rho fibres and does not identify them.
2. Finite-head determination of global physical port falsified: zero-head Sonin directions can retain positive Herglotz energy.
3. Canonical zero-transfer survives and is formalized.

New unconditional facts:
- `burnolCartierZeroTransfer h = I - 2(Re rho-1/2) M_rho` is a complex linear isometry for every Re rho>1/2.
- At a right-half Xi divisor and fixed [1/2,1] co-Poisson atom, its value lies in literal extended Sonin space.
- Exact heads are `-conj(rho)/(1-rho)` and `-log(2)*(1-conj(rho))/rho`.
- Gains alpha=conj(rho)/(1-rho), beta=(1-conj(rho))/rho satisfy beta=1/conj(alpha).
- `|alpha|=1 iff Re rho=1/2`; in open right half of critical strip, `1<|alpha|`.
- `BurnolXiCartierZeroTransferForwardHeadNormConservation` is equivalent to prior `BurnolXiForwardReflectedCartierStokesSewing` and implies existing RH endpoint.

Open core: derive separate preservation of this one explicit fixed forward-head norm from pre-divisor rational-adelic/Euler-Gamma-Stokes structure. Total L2 isometry and Sonin landing do not imply it; amplitude is redistributed reciprocally between heads.

Verification: direct `lake env lean` green; targeted `lake build GaloisForLFunctions.RHTower.BurnolCartierZeroTransferHeadGain` green; lint green; key axiom prints only `[propext, Classical.choice, Quot.sound]`.

Card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/burnol/burnol-cartier-zero-transfer-head-gain.md`.

Related prior memory: `mem:route-r/burnol-reflected-coshift-cartier-continuation-2026-08-07`.