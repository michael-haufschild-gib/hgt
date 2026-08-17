# Source-horizontal Gamma-six Meyer modular untwisting (2026-08-16)

Created `formal/GaloisForLFunctions/RHTower/SourceHorizontalGammaSixMeyerModularUntwisting.lean`, wired into `RHTower.lean`.

Exact unconditional identity for every retained Xi divisor support `rho` and prime `p`:
[
GammaGhost(rho,p)=-multiplicity(rho)(||chi_p(rho)||-||chi_p(rho)||^{-1})^2.
]
Here `chi_p` is the existing genuine `deningerMeyerXiPrimeGammaCharacter`. Consequences formalized:
- full ghost nonnegative iff Meyer norm imbalance is zero;
- norm imbalance zero iff `||chi_p||=1`;
- Meyer character unitary iff physical Gamma-six covariant boundary equals fixed/untwisted boundary;
- full ghost nonnegative directly implies untwisting.

Canonical Abelian-zeta gas/GNS pivot failed and obstruction was formalized: gas generator/co-generator satisfy only one-sided Toeplitz inverse, with `gasV * gasW != 1`; Gibbs state detects range projection; no Laurent ring hom can map `T` and `T^-1` to these.

Verification:
- scratch Lean passed;
- direct `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalGammaSixMeyerModularUntwisting.lean` passed;
- exact leaf `lake build GaloisForLFunctions.RHTower.SourceHorizontalGammaSixMeyerModularUntwisting` passed;
- axiom audit: only propext, Classical.choice, Quot.sound;
- no umbrella/full build.

Open core remains RH-strength: construct an unconditional Xi-selected bilateral positive source receiver proving `||deningerMeyerXiPrimeGammaCharacter rho p||=1` (equivalently ghost nonnegativity) for each retained Xi divisor. Toeplitz gas cannot do it.