# TG C9.11k — actual finite Euler boundary quotient

- **Stage:** 3-formalized
- **Type:** PROVED finite annular realization, Banach quotient and actual current return
- **Route:** TG, source-defined graded admission after the moving-carrier obstruction.

## Exact result

For every finite genuine prime set S and b,c>0, let P=P_S and
`B_(S,b,c)=R_c A_S|K_b`, using the original physical Euler polynomial.
Its range is exactly

`H_(S,b,c)={u : R_(b/P)u=0 and R_cu=u}`,

and its kernel is `K_b ∩ ker R_(P*c)`. The source map induces an actual
bounded linear equivalence from its Banach quotient onto this closed annulus.
For b/P≤c, the annulus is the range of the literal operator `R_c−R_(b/P)`.
The cutoff-condition description also handles the zero range when the edges
cross; the difference-of-cutoffs description must not be used in that chamber.

At c=1 and b≥1, the actual adjoint return reconstructs the full cleared current:

`J_S f=−A_S* (boundaryQuotientEquiv [f])=−A_S* R₁ A_S f`.

The quotient therefore retains a genuine source and return pair. Its norm or
positive Gram alone would not retain this current identity.

## Dependency-closed paper proof

1. **Ambient time-band inverse.** A_b R_c is compact. A fixed vector f obeys
   `‖f‖≤‖R_cf‖≤‖f‖`; equality in orthogonal projection implies R_cf=f and
   A_bf=f. The corpus's bounded-support Fourier uncertainty gives f=0.
   The compact Fredholm alternative therefore inverts I−A_bR_c on the whole
   even Hilbert space. Put G=(I−A_bR_c)⁻¹, H=G A_b and T=I−(I−R_c)H.
   The resolvent equation and its left A_b multiple give A_bH=H, hence
   `A_bT=0` and `R_cT=R_c`. For b≤c and annular u, Tu∈K_b and R_cTu=u.
   This actual bounded Sonin section proves surjectivity, not only density.
2. **Exact triangular inverse.** For r≥1 put W_r=R_cD_r(I−R_b).
   Covariance gives R_cD_rR_c=R_cD_r and R_bD_r(I−R_b)=0, so
   W_rW_s=W_(rs). For b≤c it is the compression by R_c−R_b.
   It vanishes when c≤rb. Thus W_p is nilpotent for every p>1 and
   I−zW_p is a unit for every complex z, including sqrt(p).
3. **Original local Euler equation.** For u in the annulus (b/p,c), set
   v=D_pu and W=R_(pc)D_p(I−R_b). Solve
   `(I−sqrt(p)W)w=−sqrt(p)v`. Applying the lower cutoff and upper-cutoff
   complement forces w into (b,pc). Applying D_(1/p) to the equation gives
   `R_c A_p w=u`. Also `R_c A_p R_(pc)=R_c A_p`.
4. **Full finite source.** Induct on actual prime insertion. Lift through p,
   then through the remaining original denominator at upper aperture pc.
   Upper-cutoff absorption composes these lifts without deleting any mixed
   term. At the empty stage use the Sonin section, or the zero vector if the
   annulus is empty. The sharp Fourier-gap theorem proves the reverse range
   inclusion and the exact kernel.
5. **Banach quotient and return.** The annulus is the intersection of two
   closed cutoff kernels. Descend the original continuous linear boundary map
   through its closed kernel, use the proved surjectivity and Banach inverse
   theorem, and identify its value on every source class. The previously
   proved exact current formula supplies the actual adjoint return.

## Corpus and working log

Fresh deep searches inspected candidates, source arguments and partial compiler
coverage. They did not return the required annular surjectivity or nilpotent
Euler boundary inverse. Exact source inspection supplied time-band compactness,
Fourier uncertainty, cutoff covariance, genuine prime insertion and sharp gaps.
New-source search hits were not treated as verification.

The initial compressed-Fredholm approach was simplified to the stronger ambient
asymmetric resolvent above. All mathematical conjectures in this finite chain
survived. Lean fixes concerned projection rewriting, scalar multiplication and
explicit inherited structures for the Banach quotient; no heartbeat limits
were raised. The actual physical factors and adjoint return remain throughout.

## Lean artifacts and remaining frontier

- `SoninAnnularExtension`
- `SoninAnnularDilationNilpotent`
- `CCMEulerAnnularLocalRange`
- `CCMEulerAnnularRange`
- `CCMEulerBoundaryQuotient`

All five final leaf checks use `lake --old env lean <leaf> -o <leaf.olean>` and
pass; all five leaves are wired into RHTower without an umbrella build.
There are 26 public theorems, six definitions and two carrier instances.
All 34 public axiom queries pass and report only `propext`, `Classical.choice`
and `Quot.sound`. Queries live in /tmp; no audit commands, additional axioms,
holes, numerical experiments or increased heartbeat limits were added to Lean
source. One owned foreground Lean process ran at a time.

The final formal lint gate exits 1 solely for ten other unwired modules:
CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.
None of these five new leaves has a lint failure. Full output:
`/tmp/tg-c911k-final-lint.log`.

C9.11l, `tg-euler-cofinal-boundary-transitions`, attacks actual source-preserving
transitions and their kernel shells. No cofinal relative class, uniform inverse
estimate, mixed prime–Gamma operator continuation, degree-three Hardy-index
comparison, strict sub-unit law, or unconditional RH conclusion follows merely
from this finite realization. Those remain the hard route-TG obligations.
