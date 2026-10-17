# Odd single-logarithmic-zero multiplier inheritance

- **ID:** BSU-HML-SINGLE-ZERO
- **Stage:** 5-failed
- **Type:** FALSIFIED, positive survivor THEOREM (Lean)
- **Scope:** Independent BiScale Uncertainty; one logarithmic source zero.
- **Rejected statements:** Oddness and h_f(log 2)=0 imply h_(S_(1/2)f)(log 2)=0;
  or a finite universal constant A bounds that multiplier correlation by A h_f(0).

## Exact obstruction and dependency-closed proof

Let d=log(2)>0. Reuse the existing even smooth packet phi from
`formal/GaloisForLFunctions/RHTower/EvenSectorSmoothBlindInterpolationObstruction.lean`.
Its support diameter is below d/10 and m=integral phi^2>0. For t=|T| put
a_j=t+jd, j=1,2,3, and define

f_T(u)=-phi(u-a_1)+phi(u-a_2)+phi(u-a_3)
       +phi(u+a_1)-phi(u+a_2)-phi(u+a_3).

This constructs a smooth compact odd function. Separation gives h_fT(0)=6m.
At lag d, only edges a_1->a_2, a_2->a_3, -a_2->-a_1 and -a_3->-a_2
survive, with products -1,+1,-1,+1, so h_fT(d)=0.

Set M=integral cosh(u)phi(u)^2 du>=m>0. Evenness of phi gives
integral sinh(u)phi(u)^2 du=0. Hyperbolic product decomposition yields

integral sinh((u+a)/2)sinh((u+b)/2)phi(u)^2 du
 =[cosh((a+b)/2)M-cosh((a-b)/2)m]/2.

Summing the same four overlaps proves the exact positive law

h_(S_(1/2)fT)(d)=2 sinh(|T|+2d)sinh(d/2)M>0.

Write c=2 sinh(d/2)M>0. Given any real A choose
T=(|A(6m)|+1)/c>0. Since sinh(T+2d)>=T+2d, the multiplier correlation
exceeds A(6m). Original energy and its logarithmic zero remain fixed.
Every integral is integrable by smoothness and compact support. [PROVED HERE]

## No-go closure

- **Exact killing theorem:** `OddMultiplierLeakage.exists_odd_logZero_large_sinhCorrelation`
  constructs the source for each real A; `source_sinh_autocorr_lag_pos` directly
  disproves inherited multiplier vanishing.
- **Strongest positive survivor:** `source_sinh_autocorr_lag` gives the entire
  quantitative growth law; `source_autocorr_zero`, `source_autocorr_lag`,
  and `packetMass_le_packetCoshMass` identify its fixed energy, exact cancellation,
  and positive weighted packet invariant. The survivor is a positive exact identity,
  not a restatement of the rejected bound.
- **New insight:** A single source clique edge and fixed source energy leave
  multiplier leakage unbounded through absolute packet position. A valid lifting
  bound must retain actual multiplier Gram data or additional weighted/position
  information. The support-sensitive receiver has not been invalidated.
- **Status:** Dependency-closed paper proof above; exact family, smoothness,
  support, zero, energy, leakage and unboundedness verified in
  `formal/GaloisForLFunctions/BiScaleUncertainty/OddMultiplierLeakageFamily.lean`.
  Actual-source compile exited 0 without warnings. All 12 public theorem axiom
  audits returned only `propext`, `Classical.choice`, `Quot.sound`.
  SHA256: `fd8f41743e0b8a24bb2a4ebd43594b172a93ffef3c3066c9a631afedaa500ef0`.
- **Boundary:** This imposes h_f(log 2)=0 only. It neither supplies a source blind
  on the full infinite prime grid nor closes the odd secant/plastic lifting program.
  No source moment cancellation or external novelty is claimed.
- **Accounting:** Fourth contribution in BSU-HML, counted once with its survivor.
  Repository-wide lint outcome is on the parent in-progress card.
