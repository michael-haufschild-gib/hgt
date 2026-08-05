# Mass-shifted spectral trace §9.3 audit (2026-08-04)

- Formalized exact Euler source identity, archimedean contour shift/uniform bound, and prime-only RH reduction.
- New modules: `RHTower/RectangleLocalCauchyFormula`, `RectangleLocalWeightedCauchyResidue`, `XiGuinandWeilVerticalCauchyScaled`, `XiMassFiniteContour`, `XiMassSymmetricContour`, `XiMassVerticalResolvent`, `XiMassBottomEdge`, `XiMassEulerContourSourceIdentity`, `XiMassArchimedeanUniformBound`, `XiMassPrimeOpenCore`, `XiMassPrimeGradedOpenCore`.
- Exact open core: `XiMassBottomPrimeLineBound a c sigma`. For every legal fixed `(a,c,sigma)`, it is equivalent to RH. Complete prime integral is independent of legal depth, and all legal line-bound propositions are equivalent.
- Graded source law: for `lambda >= 0`, `XiMassBottomPrimeLineGrowth a c sigma lambda` iff every mass-shifted Xi displacement is at most `lambda`. Any larger displacement defeats every `C exp(lambda |u|)` envelope. At zero exponent, `not RH` iff prime integral is cofinally unbounded.
- Source identity and Gamma seams are fully unconditional. Remaining obstruction is genuinely cofinal von-Mangoldt cancellation; no pole, contour, integrability, or archimedean hypothesis remains.
- PNTPlus magnitude route fails: `x exp(-c(log x)^(1/10))` becomes a critical-weight envelope `exp(u/2-c u^(1/10)-O(sqrt u))`, still divergent. Absolute/Stieltjes use of the existing PNT remainder cannot close the bound.
- Final target build `lake build GaloisForLFunctions.RHTower.XiMassPrimeGradedOpenCore` succeeded. Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`. Direct checks of all new route modules were warning-free.
- Repository-wide lint is red only on pre-existing unrelated umbrella issue: `RHTower.MobiusMertensFiniteSectionEnergy` unreachable from `GaloisForLFunctions.RHTower`.
- Goal remains active/unmet: do not claim RH or mark complete until source-side prime bound is proved unconditionally.