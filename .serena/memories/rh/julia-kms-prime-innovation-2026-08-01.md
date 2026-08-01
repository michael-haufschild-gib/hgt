JKPIT-1 formalized whole-HT source coupling.

New module: formal/GaloisForLFunctions/HTGeometry/JuliaKMSScaleFourInnovation.lean
Card: docs/drafts/pipeline/3-formalized/needs-audit/julia-kms-prime-innovation-tower.md
Working log appended: docs/drafts/pipeline/1-in-progress/rh-whole-formal-corpus-frontier-audit.md
HT umbrella imports new module.

Math:
For x=β(Ea-Eb)/2>0, D(x)=1/(2sinh x), C=finite KMS commutator, W=Wightman:
D(x) C = W.
Combining D(x)=Σ_{j<n}4^j J(4^j x)+4^nD(4^n x) yields exact finite Julia innovation resolution of every positive-gap KMS transition.
Prime-log Hermitian realization has W_p=primeDyadicWeight(u,p)>0 and C_p=2sinh(βlog p/2)W_p, so every prime carrier weight decomposes into strictly positive Julia layers plus strictly positive tail.
Formal no-go: multiplying any positive prime Julia layer by a negative external phase stays negative. This bridge does not sign RHT first clock; primeDyadicWeight is not literal Λ(p^e)/sqrt(p^e), and diagonal inverse FDT does not mix/change sine phases.
Positive survivor: Julia equilibrium is a canonical multiscale inverse-FDT response resolution, instantiated exactly on arithmetic prime-log carrier.
Open core: non-diagonal phase-sensitive KMS realization of literal prime-power Mellin source, or cross-frequency quadratic inequality before sine evaluation.

Capstones:
criticalDirichletLevyRadialDensity_mul_finiteKMSCommutator_eq_wightman
finiteKMSWightmanTransitionIntensity_eq_juliaScaleFourInnovationTelescope
juliaScaleFourKMSInnovationLayer_nonneg
primeDyadicWeight_eq_criticalDirichletFDT
primeDyadicWeight_eq_juliaScaleFourInnovationTelescope
primeJuliaScaleFourInnovationLayer_pos
primeJuliaScaleFourInnovationTail_pos
primeJuliaScaleFourInnovationLayer_mul_neg

Verification:
direct lake env lean green;
lake build GaloisForLFunctions.HTGeometry.JuliaKMSScaleFourInnovation green 8768/8768;
8 axiom sets exactly [propext, Classical.choice, Quot.sound];
lint new work clean, global lint fails only unrelated umbrella gaps RHTower.SuzukiClarkSeriesReconstruction, RHTower.ZetaGammaProjectiveHorizonSchwarzianDiamond, HTGeometry.ProjectiveHorizonActualSchwarzianDiamond;
no stale Lean/lake.
Not RH.