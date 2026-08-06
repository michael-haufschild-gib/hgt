# Route E Gibbs parity--energy defect law

- **ID:** `ROUTE-E-GIBBS-PARITY-ENERGY-DEFECT-001`
- **Stage:** 3-formalized
- **Type:** THEOREM / SOURCE-MECHANISM NO-GO / POSITIVE SURVIVOR
- **Parent:** `../../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **External priority claim:** none; external search intentionally omitted under current research
  instruction. Internal corpus audit found no parity--energy covariance formula for the Gibbs
  dilation defect.

## Statement

For a finite aperture (S), put

\[
 E(T)=\prod_{q\in T}q,\qquad
 Z_S(x)=\sum_{T\subseteq S}e^{-xE(T)},\qquad
 J_S(x)=\sum_{T\subseteq S}(-1)^{|T|}e^{-xE(T)},
\]

and define the normalized parity current (psi_S=J_S/Z_S).  The unnormalized
parity--energy covariance is

\[
 C_S(x)=
 \left(\sum_T(-1)^{|T|}E(T)e^{-xE(T)}\right)Z_S(x)
 -J_S(x)\left(\sum_TE(T)e^{-xE(T)}\right).                 \tag{1}
\]

All sums are finite and (Z_S(x)>0).  Direct differentiation gives

\[
 \psi_S'(x)=-\frac{C_S(x)}{Z_S(x)^2}.                     \tag{2}
\]

For the exact scale defect isolated by the Gibbs programme,

\[
 \Delta_{S,p}(x)=J_S(px)Z_S(x)-J_S(x)Z_S(px),             \tag{3}
\]

one therefore has the finite-volume source formula

\[
 \boxed{
 \Delta_{S,p}(x)
 =Z_S(x)Z_S(px)\int_x^{px}-\frac{C_S(t)}{Z_S(t)^2}\,dt.}  \tag{4}
\]

Thus the formerly opaque remainder is exactly accumulated parity--energy covariance across the
prime dilation interval.  Equation `(4)` is an identity, not a sufficient hypothesis or an RH
reformulation.

At the free-gas boundary, for every nonempty (S),

\[
 J_S(0)=0,\quad Z_S(0)=2^{|S|},\quad
 J_S'(0)=(-1)^{|S|+1}\prod_{q\in S}(q-1).                 \tag{5}
\]

Consequently

\[
 C_S(0)=-2^{|S|}(-1)^{|S|+1}\prod_{q\in S}(q-1),         \tag{6}
\]

and the first defect jet is

\[
 \boxed{
 \Delta_{S,p}'(0)
 =(p-1)2^{|S|}(-1)^{|S|+1}\prod_{q\in S}(q-1).}          \tag{7}
\]

For (p\ge2) and (q\ge2) on (S), `(7)` is strictly positive when (|S|) is odd and
strictly negative when (|S|) is even.

## Proof

Differentiating one Boltzmann factor inserts (-E(T)).  Finite summation gives

\[
 J_S'=-\sum_T(-1)^{|T|}E(T)e^{-xE(T)},\qquad
 Z_S'=-\sum_TE(T)e^{-xE(T)}.
\]

The quotient rule is exactly `(2)`.  Positivity of (Z_S) makes the quotient regular for every
real coupling.  The fundamental theorem of calculus on ([x,px]) gives

\[
 \psi_S(px)-\psi_S(x)=\int_x^{px}-C_S(t)/Z_S(t)^2\,dt.
\]

Clearing the two positive partition denominators gives `(4)`.

At (x=0), the gas is ((1+z)^{|S|}), proving the first two identities in `(5)`.  The existing
parity-jet theorem supplies the third.  Substitution into `(1)` gives `(6)`.  Differentiating
`(3)` at zero kills both terms containing (J_S(0)), leaving

\[
 pJ_S'(0)Z_S(0)-J_S'(0)Z_S(0)=(p-1)J_S'(0)2^{|S|},
\]

which is `(7)`.  The sign corollaries are immediate.

## Frontier consequence

This moves the hard source from “bound an unexplained defect (Delta)” to one explicit statistic:
weighted, signed parity--energy covariance across every moving prime-dilation interval.

It also kills a real proof strategy.  No theorem asserting one fixed covariance sign, monotonicity
of (psi_S) under dilation, or termwise-positive defect production can hold uniformly over natural
prime apertures: the infinitesimal sign reverses whenever aperture cardinality changes.  Taking
absolute values discards exactly the cancellation needed by Route E.

The surviving route must be cofinal and signed.  It must control the weighted accumulation of the
integrals in `(4)` while (S=S(x)) grows at the physical aperture.  Fixed-(S) Taylor control is
nonuniform: `(7)` contains the rapidly growing factor
(2^{|S|}\prod_{q\in S}(q-1)).  This explains, rather than assumes, why fixed-volume contraction
cannot pass to the RH scale.

The theorem does **not** prove the needed cofinal covariance estimate.  Route E remains open.

## Lean implementation

`formal/GaloisForLFunctions/RHTower/GibbsParityEnergyCovariance.lean`, wired into
`GaloisForLFunctions.RHTower`, proves unconditionally:

- `hasDerivAt_gibbsDiag_energy`;
- `hasDerivAt_normalized_gibbs_current`;
- `continuous_gibbsParityEnergyCovariance`;
- `integral_neg_covariance_eq_normalized_current_sub`;
- `gibbsScaleDefect_eq_normalized_current_difference`;
- `gibbsScaleDefect_eq_integral_neg_covariance`;
- `hasDerivAt_gibbsScaleDefect_zero`;
- `gibbsParityEnergyCovarianceNumerator_zero`;
- `deriv_gibbsScaleDefect_zero_eq_covariance`;
- the odd/even strict-sign corollaries.

Direct `lake env lean` verification passes.  Final targeted module build and axiom audit are recorded
after umbrella wiring.

## Verification log

- `lake env lean GaloisForLFunctions/RHTower/GibbsParityEnergyCovariance.lean` — pass, no warnings.
- `lake build GaloisForLFunctions.RHTower.GibbsParityEnergyCovariance` — pass
  (`8658/8658`); no umbrella or full build run.
- Scratch-file axiom audit of the integrated defect capstone, defect jet, and both sign corollaries:
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden-token scan: clean.
