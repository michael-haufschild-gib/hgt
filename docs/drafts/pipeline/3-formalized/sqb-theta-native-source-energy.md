# SQB: native theta source and exact weighted energy

The original theta zero mode now has an unconditional native modular L2
realization, an exact mean, and a quantitative weighted energy comparison.
The complete source, its primitive rows and all native cross terms are retained.
RH and full-Xi occurrence remain unproved.

## Closed Lean statements

For an actual Xi divisor copy q, write z=b+ic=xiSpectralPoint(q),
u=SelbergThetaSourcePhase.mode(q), Phi=thetaCuspFullSource, and x=log(y)/2.
The native seeds and their complete primitive-row periodizations are

    p(y)=sqrt(y)Phi(x), w(y)=sqrt(y)u(x),
    P=periodize(p), W=periodize(w).

`SelbergThetaNativeSource.lean` proves

    P>0, |P+bW|<P, |W|<2P/|b|, W!=0,
    P and W are measurable, modular invariant and native L2,
    integral_fd P=m>0, integral_fd W=-m/(z-i),
    m=2 integral exp(-x)Phi(x).

Every real height power bounds each seed with a proved positive constant:
for every r, p(y)<=C_r y^r and |w(y)|<=D_r y^r for all y>0.
These constants are obtained analytically from the original theta envelope.

`SelbergThetaNativeEnergy.lean` proves, with h=z-i,

    m/|h|^2 <= E=integral_fd |W|^2/P < 2m/|h|^2,
    V=W+P/h belongs to native L2, integral_fd V=0,
    integral_fd |V|^2/P=E-m/|h|^2,
    0 <= integral_fd |V|^2/P < m/|h|^2.

No spectral-occurrence premise or auxiliary unproved source hypothesis is
used. Each statement takes only its actual divisor copy and spatial/height
arguments where required. The comparison is weighted by P; P has not been
identified with a constant or silently replaced by one.

## Proof mechanism

The actual double exponential envelope gives p(y)<=C and p(y)<=C y^2.
The bounded source ratio u/Phi gives the same two bounds for w. Positive
Eisenstein quadratic row majorants prove absolute convergence of both full
row sums. The native nonparabolic quadratic bound and the identity row
then prove boundedness on the modular cell. Measurability, invariance and
native L2 membership follow for the literal periodizations.

Multiplying the previously proved disk |1+b u/Phi|<1 by each positive
profile, summing absolutely and keeping strictness in the identity row
proves |P+bW|<P. Thus W is nowhere zero and its norm is bounded by 2P/|b|.

Absolute strip unfolding and the exact change of variables y=exp(2x)
give the means. The required source tilt is -1, outside the earlier
open-strip variance theorem. Its integrability and both vanishing
endpoints are proved directly from the actual all-rate envelope.
Integration of the first-order mode equation then gives the denominator
z-i with its correct sign and native half-density normalization.

Squaring the native disk shows

    0 < -2 Re(W)/b-|W|^2/P.

This integrable defect has positive integral. Inserting the exact real
mean of W proves the strict upper bound. Expanding |W+P/h|^2/P and
integrating all three terms gives the exact centered energy identity;
its nonnegativity proves the lower bound. No row cross terms are omitted.

For the all-power tail bounds, exp(2x)>=x^2 and the square
(6x-(a+9/2))^2 control exp(a x)Phi(x) on x>=0. Evenness handles x<0.
Substituting x=log(y)/2 supplies every positive and negative height power.

## Audit

- NativeSource: 21 public declarations, 626 lines.
- NativeEnergy: 11 public declarations, 223 lines.
- Both wired once into `formal/GaloisForLFunctions/RHTower.lean`.
- Complete scratch and canonical checks passed with `lake env lean FILE`,
  without diagnostics. Logs: `/tmp/sqb32_tail_check.log`,
  `/tmp/sqb32_source_check.log`, `/tmp/sqb32_energy_check.log`,
  `/tmp/sqb32_energy_source_check.log`.
- Final named leaf builds passed with
  `lake --old build GaloisForLFunctions.RHTower.SelbergThetaNativeSource`
  and `lake --old build GaloisForLFunctions.RHTower.SelbergThetaNativeEnergy`.
  Their preflights and actual Built lines identify only the respective leaf,
  taking 42 and 23 seconds. Existing dependencies were replayed; this is
  not a fresh whole-dependency audit. Logs: `/tmp/sqb32_preflight.log`,
  `/tmp/sqb32_leaf_build.log`, `/tmp/sqb32_energy_preflight.log`,
  `/tmp/sqb32_energy_leaf_build.log`.
- All 21 NativeSource public declarations passed scratch `#print axioms`,
  reporting only `propext`, `Classical.choice`, `Quot.sound`.
  Log: `/tmp/sqb32_axioms.log`.
- All 11 NativeEnergy public declarations passed scratch `#print axioms`,
  reporting only `propext`, `Classical.choice`, `Quot.sound`.
  Log: `/tmp/sqb32_energy_axioms.log`.
- Repository formal lint passed, including proof-debt and umbrella wiring.
  Log: `/tmp/sqb32_lint.log`. Scoped whitespace checks passed.
- Declaration indexing passed. Log: `/tmp/sqb32_index.log`.

No numerical computations, full builds, umbrella builds or frontier-map
edits were used. Lean and Lake checks were foreground and serial. Every owned Lean/Lake
process exited and its terminal result was collected.

## Mathematical continuation

The [positive occurrence card](../1-in-progress/sqb-positive-occurrence-conjecturing-loop.md)
contains the complete proof that the centered source is not zero almost
everywhere. Its pairing with the actual positive Eisenstein row sum is
nonzero by two-Weyl algebra and all-power absolute unfolding. That pairing,
the strict lower bound and actual native unit normalization are now
formalized; see the [complete pairing audit](sqb-theta-native-pairing.md).

Full operator graph admission and vanishing normalized residual at the
unchanged full-Xi target remain unresolved. The actual forcing is

    (A-e)V=-periodize[sqrt(y)(D-1)(D-iz)Phi]/(4(z-i)),
    e=5/4+z^2/4.

This operator equation is currently a paper calculation. Native source
admission and nonzero source mass are not assertions of spectral occurrence.
