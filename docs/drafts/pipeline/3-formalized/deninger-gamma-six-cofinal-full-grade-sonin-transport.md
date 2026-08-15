# Gamma-six cofinal full-grade Gamma--Sonin transport

- **Stage:** 3 — formalized in Lean 4
- **Route:** L
- **Date:** 2026-08-15
- **Status:** `[NEW BRIDGE] [PAPER PROVED] [LEAN FORMALIZED]`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/DeningerGammaSixCofinalFullGradeSoninTransport.lean`
- **RH used:** no
- **Xi-zero location used:** no
- **Computation used:** no

## Frontier diagnosis

Existing Gamma-six reflection rigidity holds the local horizontal parameter `delta` fixed while
the Wold clock raises shell depth.  Its reflection multiplier then acquires holonomy

\[
 (1/6)^{2\delta},
\]

which is stationary only at `delta=0`.  Reusing that fixed-local-grade family is therefore an
RH-equivalent endpoint, not a source construction.

The source modular character on depth `m` depends on the **total grade** `g=m a`.  A cofinal
section of fixed total grade must consequently use the depth-dependent local parameter

\[
 a_m=\frac g m.
\tag{FG1}
\]

This is forced by the actual Gamma modular rate, not chosen to fit the Sonin target.

## Theorem: full-grade Wold-flat reflection

Let `lambda_n=6^{-m}` on the Gamma-six shell of honest depth `m>=3`.  Evaluate the two reflected
shell branches at the half-local parameters `+-g/(2m)`.  Their multiplier is

\[
 \lambda_n^{g/m}=6^{-g},
\tag{FG2}
\]

independent of `m`.  Therefore the transported reflection multiplier is exactly Wold-stationary:

\[
 \lambda_{Wn}^{g/(m+1)}=\lambda_n^{g/m}=6^{-g}.
\tag{FG3}
\]

This does not contradict fixed-`delta` rigidity: local parameter changes from `g/m` to
`g/(m+1)` while total grade remains `g`.

The corresponding logarithmic branches are

\[
 J_g^+(n)=m\log 6\,\lambda_n^{1-g/(2m)}
          =6^{g/2}J_0(n),
\qquad
 J_g^-(n)=m\log 6\,\lambda_n^{1+g/(2m)}
          =6^{-g/2}J_0(n).
\tag{FG4}
\]

Hence each branch has an exact Wold coface in the same non-trace-class principal source class:

\[
 J_g^\pm(Wn)-\frac16J_g^\pm(n)
 =6^{\pm g/2}\frac{\log6}{6}\lambda_n.
\tag{FG5}
\]

The signed cross-normalized relation is exact before any scalar target is introduced:

\[
 6^{-g/2}J_g^+(n)-6^{g/2}J_g^-(n)=0,
\tag{FG6}
\]

and the same identity holds for their Wold cofaces.  This is a same-full-grade relation rather
than constant-local-grade stationarity.

## Actual Gamma boundary and fixed Sonin frequency

Let `E_m(alpha)` be the genuine common-test Gamma/co-Poisson modular exterior on the ordered cells
`(2,m-1),(3,m-1)`.  Existing critical comparison gives

\[
 E_m(0)=-mV_{23}6^{-m/2},\qquad
 V_{23}=\frac{\log2\log3(\log3-\log2)}2>0.
\]

The sum of the two source modular rates is `-m log 6`, so

\[
 E_m(\alpha)=E_m(0)e^{-\alpha m\log6}.
\tag{FG7}
\]

At the forced half-local grade `alpha=g/(2m)`, the reflection-odd exterior is therefore

\[
 E_m^{\mathrm{odd}}(g)
 =mV_{23}6^{-m/2}\sinh(g\log6/2).
\tag{FG8}
\]

All depths carry the same frequency.  Only the source calibration

\[
 K_m=\frac{mV_{23}6^{-m/2}}2>0
\tag{FG9}
\]

varies.  For Route R's fixed `(2,3)` Sonin/Stokes odd curvature

\[
 O(g)=-2\sinh(g\log6/2)G(g),\qquad G(g)>0,
\]

one obtains the division-free comparison

\[
 \boxed{\quad G(g)E_m^{\mathrm{odd}}(g)=-K_m O(g).\quad}
\tag{FG10}
\]

Thus every labelled depth represents one and the same fixed Sonin orientation class after its
source-defined positive calibration.  No `1/Xi`, zero-fitted quotient, compactness premise, or
target-defined normalization occurs.

For the genuine two-sheet Gamma packet

\[
 \Gamma_{g,m}=(E_m(g/(2m)),E_m(-g/(2m)))
\]

and the fixed Stokes packet `S_g=(C(g),C(-g))`, (FG10) upgrades by linearity of the literal Euler
orientation Gram to

\[
 G(g)\,\operatorname{Gram}(\Gamma_{g,m})
   =2K_m\,[C_g,P],
\tag{FG11}
\]

where `[C_g,P]` is the already constructed fixed noncompact Sonin commutator.  This is the desired
actual Gamma-to-fixed-Sonin comparison; compactness is not asserted.

## Proof status

- `(FG1)`--`(FG8)`: dependency-closed from actual modular-current formula, equal-depth Gamma
  boundary comparison, shell-depth Wold law, and real-power identities.
- `(FG9)`--`(FG10)`: dependency-closed from positivity of `V_23`, half-density, and Route R polar
  normal form.
- `(FG11)`: dependency-closed by literal finite two-sheet orientation-matrix linearity.
- All claims are formalized in the leaf module named above.

## Anti-theatre audit

This is not the already formalized fixed-local-grade shell transport.  That transport has
nontrivial Wold holonomy and detects RH.  New section changes local parameter covariantly with
depth because actual source character fixes `m a`, producing a Wold-flat reflection multiplier at
arbitrary total grade.

This also is not the trivial observation that two scalar formulas contain `sinh`.  Equations
`(FG1)`--`(FG8)` construct one cofinal, depth-labelled, actual Gamma source section whose frequency
lands in the *fixed* Sonin receiver at every depth.  Division-free operator comparison `(FG11)` is
the scientific bridge.  Remaining hard problem is independent source annihilation of this
constant target class; it is not claimed here.

## Novelty audit

Meyer supplies the nuclear spectral quotient, Burnol supplies Gamma-completed co-Poisson/Sonine
evaluation, and Connes--Consani supply fixed Sonin compression.  None constructs the inverse-depth
full-grade connection `(FG1)`, its Wold-flat reflection law `(FG3)`, or the labelled actual-Gamma
to fixed-Sonin comparison `(FG10)`--`(FG11)`.  Corpus contains fixed-local-grade rigidity and the
critical logarithmic tangent separately, but targeted symbol/co-occurrence search found no
inverse-depth total-grade section or depth-uniform fixed-Sonin comparison.

## Remaining frontier after this card

Use the cofinal section `(FG11)` to construct the source-selected logarithmic graph completion and
prove that its independently defined Meyer/Rost--Schmid boundary annihilates the constant Sonin
class.  The comparison itself must remain singular: `K_m -> 0`, so division by `K_m` cannot extend
boundedly to the ambient Calderon `ell^2` completion.

## Lean certificates

- `deningerGammaSixCofinalFullGradeReflectionMultiplier_eq`;
- `deningerGammaSixCofinalFullGradeReflectionMultiplier_wold`;
- `deningerGammaSixCofinalFullGradeForwardLogWeight_eq`;
- `deningerGammaSixCofinalFullGradeReflectedLogWeight_eq`;
- `deningerGammaSixCofinalFullGradeForwardLogWeight_wold`;
- `deningerGammaSixCofinalFullGradeReflectedLogWeight_wold`;
- `deningerGammaSixCofinalFullGradeLogWeight_signed_relation`;
- `deningerGammaSixTwoThreeEqualDepthModularExterior_eq`;
- `deningerGammaSixCofinalActualForwardLogWeight_eq`;
- `deningerGammaSixCofinalActualReflectedLogWeight_eq`;
- `deningerGammaSixCofinalFullGradeOddExterior_sonin`;
- `deningerGammaSixCofinalFullGradeGamma_orientationMatrix`;
- `deningerGammaSixCofinalFullGradeGamma_orientationGram_eq_soninCommutator`.
