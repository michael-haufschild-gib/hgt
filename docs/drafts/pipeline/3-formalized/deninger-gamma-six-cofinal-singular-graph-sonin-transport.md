# Deninger Gamma-six cofinal singular graph transport

**Stage:** 3 — formalized  
**Route:** L  
**Status:** `[NEW BRIDGE] [PAPER PROVED] [LEAN FORMALIZED]`

## Frontier

The cofinal full-grade comparison gives, at every honest depth `m`,

\[
 G(g)\,\Gamma_{g,m}=2K_m T_g,\qquad K_m>0,
\]

where `Gamma_{g,m}` is the literal actual-Gamma two-sheet orientation Gram and `T_g` is Route R's
fixed `(2,3)` Sonin commutator.  Since `K_m -> 0`, normalizing by `2K_m` cannot extend as a bounded
map on ambient cofinal `ell^2`.  Missing object is the source-selected completion on which this
normalization is continuous without pretending it is bounded on ambient carrier.

## Construction

Let `A=c_00(N,C)`, let `i:A -> ell^2(N)` be finite-packet admission, and let

\[
 \tau(c)=\sum_m c_m.
\]

Define graph admission

\[
 j(c)=(i(c),\tau(c))\in \ell^2\oplus_2\mathbf C.
\tag{SG1}
\]

The source graph completion is the Hilbert carrier

\[
 \mathcal G_6:=\ell^2\oplus_2\mathbf C
\tag{SG2}
\]

together with dense source map `j`, ambient projection `pi_0`, and singular trace projection
`pi_s`.  Density is exact.  If a vector is orthogonal to every `j(e_m)=(e_m,1)`, its `ell^2`
coordinates are all one fixed constant.  The only square-summable constant sequence is zero, so
the scalar coordinate also vanishes.  Hence `range(j)^perp=0` and `range(j)` is dense.

The vector

\[
 \omega_6=(0,1)
\tag{SG3}
\]

is therefore a genuine completion point with `pi_0(omega_6)=0` and `pi_s(omega_6)=1`.  It is not a
new ambient vector: it is the vertical sector forced by nonclosability of ordinary summation.

## Actual Gamma transport

For every depth define the source-normalized *actual* packet

\[
 \widehat\Gamma_{g,m}:=(2K_m)^{-1}G(g)\Gamma_{g,m}.
\tag{SG4}
\]

Positivity of `K_m` and the division-free cofinal comparison prove

\[
 \widehat\Gamma_{g,m}=T_g.
\tag{SG5}
\]

Thus finite transport is

\[
 \Gamma_g^{\mathrm{fin}}(c)
   =\sum_m c_m\widehat\Gamma_{g,m}
   =\tau(c)T_g.
\tag{SG6}
\]

It has the unique continuous graph extension

\[
 \widehat\Gamma_g(x,z)=zT_g,
\qquad
 \widehat\Gamma_g(\omega_6)=T_g.
\tag{SG7}
\]

This is a strict source-to-physical singular transport: every finite value is reconstructed from
actual equal-depth Gamma/co-Poisson packets, while extension uses only the source trace coordinate.

## Sharp descent law

Let ambient descent mean existence of a bounded `F:ell^2 -> physical` with

\[
 \widehat\Gamma_g=F\circ\pi_0.
\tag{SG8}
\]

Evaluating at `omega_6` forces `T_g=0`.  Conversely `T_g=0` gives zero descent.  For aperture one,
Route R's compactness classification and the explicit neutral-grade zero give

\[
 \boxed{\quad \widehat\Gamma_g\text{ descends through ambient }\ell^2
        \iff T_g=0\iff g=0.\quad}
\tag{SG9}
\]

Equation (SG9) is a classifier, not the missing producer.  It identifies the exact singular
one-dimensional source sector on which independent Meyer/Rost--Schmid annihilation must act.

## Anti-theatre audit

- Not a declared target quotient: carrier, dense finite source map, ambient projection, and
  singular coordinate are explicit.
- Not generic graph-closure rediscovery: existing corpus already proves saturation laws for
  nonclosable first-trace clocks.  New content is the coefficient-faithful identification of the
  resulting vertical sector with source-normalized *actual Gamma/co-Poisson packets* and Route R's
  fixed Sonin commutator.
- Not an RH premise: (SG9) does not assert ambient descent or `g=0`.
- No `1/Xi`, zero-fitted norm, target-defined normalization, compactness assumption, or numerical
  evidence occurs.

## Literature audit

Burnol relates co-Poisson distributions and Sonine spaces; Meyer supplies the nuclear quotient;
Connes--Consani supply the fixed scaling/Sonin compression.  Targeted arXiv search found no
cofinal total-grade actual-Gamma packet normalization whose nonclosable graph vertical is
identified with the fixed Sonin commutator.  General graph closure of a nonclosable functional is
standard and is not claimed as novelty.

## Subsequent frontier movement

`DeningerGammaSixCofinalMeyerTateXiGreenBoundary.lean` now constructs a literal cofinal Tate
naturality differential, tensors it with actual rational-adelic trace-one prime cycles, and proves
that its completed Green-weighted boundaries converge to `omega_6`.  Singular trace recovers the
existing multiplicity-aware completed Xi Green fibre exactly.  Thus source production and Green
landing requested here are closed.

The remaining theorem is narrower: a distinguished arithmetic Stokes identity must annihilate the
specific Green-weighted chain.  It cannot annihilate all completed boundaries continuously, since
the new module proves their range is dense.

## Lean certificates

Module: `GaloisForLFunctions/RHTower/DeningerGammaSixCofinalSingularGraphSoninTransport.lean`.

- `deningerGammaSixCofinalFiniteGraph_closure_eq_top`;
- `tendsto_deningerGammaSixCofinalFiniteGraphAdmission_averagingPacket`;
- `deningerGammaSixCofinalNormalizedActualGammaPacket_eq`;
- `deningerGammaSixCofinalFiniteActualGammaTransport_eq`;
- `deningerGammaSixCofinalGraphPhysicalTransport_finiteGraph`;
- `deningerGammaSixCofinalGraphPhysicalTransport_unique`;
- `deningerGammaSixCofinalGraphPhysicalTransport_singularVector`;
- `deningerGammaSixCofinalGraphAmbientDescent_iff`.

Verification: direct `lake env lean` passed; leaf-only `lake build` passed; key declarations depend
only on `propext`, `Classical.choice`, and `Quot.sound`.
