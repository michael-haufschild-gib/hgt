# MSC fixed-power rigging route kill (2026-09-01)

Formal module: `formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnSquarefreeFisherPowerRiggingNoGo.lean`.

For spectral point `rho` and fixed Dirichlet power `n^{-r}`, physical coordinate shifts to `(rho-sigma+r)/(sigma-1)`. Exact `ell^2` admission is `sigma < b`, `b=2 Re rho+2r-1`. Hence:
- `r <= 1-Re rho`: no physical source column is admitted for any `sigma>1`.
- `r > 1-Re rho`: canonical admitted `sigma_N=1+(b-1)/(N+2)` has exact norm square `Z_sq(b+1-sigma_N)/Z_sq(sigma_N) -> 0`.

Existing MSC regular germ on same physical divisor tends to `2`; every closed linear relation retaining these cofinal pairs contains vertical `(0,2)`, so no single-valued graph exists. Capstone `strictRightXiZero_exists_mscPowerRiggedGraphNoGo` attaches actual strict-right Xi residue-split germ.

Positive survivor: genuinely multivalued or non-power distributional completion retaining vertical value `2` (energy `4`). Ordinary and every fixed-power Hilbert graph are killed.

Audit: targeted `lake build` passed; axiom print only `propext`, `Classical.choice`, `Quot.sound`. Literature through Aug 2026: no collision found; Hedenmalm arXiv:2606.17494 asks for Hilbert inner-product structure but contains no squarefree-Mobius power-rigging/closed-relation law.