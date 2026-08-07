# Route R: Burnol Cartier head-energy Stokes flux (2026-08-07)

Module `formal/GaloisForLFunctions/RHTower/BurnolCartierHeadEnergyStokesFlux.lean`, wired into `RHTower.lean`.

Scientific delta: define oriented head current
`J_a(f)=|h_a(f)|^2-|h_a(Cf)|^2`. For fixed co-Poisson atom and divided shift `T_rho`, Lean proves
`J_(1/2)(T_rho f0)=|(1-rho)^(-1)|^2-(log 2)^2|rho^(-1)|^2` and exact transgression
`E_(1/2)(U_rho f0)-E_(1/2)(f0)=2(Re rho-1/2) J_(1/2)(T_rho f0)`.

At every hypothetical right-half Xi divisor, `J` is strictly positive and exceeds explicit floor `(1-(log 2)^2)|rho|^(-2)`. Pointwise two-head nonamplification is exactly equivalent to `J<=0`. New producer `BurnolXiCartierDividedShiftHeadFluxDissipativity`; capstone derives RH from it unconditionally.

This moves producer before Cartier transfer and removes full metric/head conservation, but does not derive remaining sign. Open core: derive `J_(1/2)(T_rho f0)<=0` independently from pre-divisor Euler--Gamma--Stokes structure. Do not retry Douglas factorization (circular), Fourier-invariant reader (parity erases signal), or compact-window source presentation (unproved globalization).

Card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/burnol/burnol-cartier-head-energy-stokes-flux.md`.

Verification: targeted `lake env lean` passed; `lake build GaloisForLFunctions.RHTower.BurnolCartierHeadEnergyStokesFlux` passed (8927 jobs); capstone axioms `[propext, Classical.choice, Quot.sound]`; `git diff --check` and source forbidden-token scan pass. Whole-tree formal lint was blocked only by unrelated concurrent un-wired modules; this new module is wired.