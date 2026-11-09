# The mass obstruction to smoothed torsion locking

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** former B129, scalar locking of the raw torsion lift; B135 is the coupled successor.
- **Statement:** A fixed compact C² profile prevents every scalar radius from giving finite limits on both its one-orbit and two-orbit packets. For the exponential locking, finite convergence is equivalent to equality of discrete and continuum mass; separated packets have an exact discriminant defect.

## Construction and scope

For `f(u)=Σ_{1≤n≤N}x_n g(u−log n)`, set `M=∫g²`, `D=MΣx_n²`, `H=∫f²`, and `a₀=gammaHardyPhaseRate 0`. The actual channels are

`L_r = pole(f) − ∫archDamped(r,u)autocorr(f,u)du + M·torsionForm(ρ(r),Icc 1 N,x)`.

This is a precise lift of the existing torsion form to labelled smooth packets. It agrees with the exact prime bridge below the atom spacing. The theorem does not identify every possible continuum extension of torsion damping with this lift; coupled smoothing is the remaining B135 problem.

## Proof

The autocorrelation identity `∫(f(v)−f(v+u))²dv=2(autocorr(f,0)−autocorr(f,u))` identifies the archimedean finite part as `−levyEnergy(f)`. The existing torsion limit gives

`L_r + log|1−ρ(r)|D + H Z(r) → pole(f)+levyEnergy(f)+M·renormalizedTorsionForm(Icc 1 N,x)`.

For `ρ_c(r)=1−exp(−Z(r)−c)`, the radius tends to one and eventually lies in `(0,1)`. Hence

`L_r−(D−H)Z(r) → pole(f)+levyEnergy(f)+M·renormalizedTorsionForm(Icc 1 N,x)+cD`.

The finite part is `weilQuad(f)+smoothPacketWeilDefect`, where

`smoothPacketWeilDefect = primeSum(f)−M·atomicWeilForm(N,x)+cD−2a₀H−MΣx_n² selfIntersection(n)`.

Since `Z(r)→∞`, a finite limit exists exactly when `D=H`. Below the atom spacing, the exact mass and prime bridges give `D=H` and the limit becomes

`weilQuad(f)+(c−2a₀)H−MΣx_n² selfIntersection(n)`.

For failure under **every** radius, take a nonnegative nonzero compact smooth bump `b` and `g(u)=b(u)+b(u−log 2)`. Then `autocorr(g,log 2)≥∫b²>0`. Its one-orbit packet has mass `M`; its two-orbit packet has mass `2M+2autocorr(g,log 2)`. Their discrete masses are `M` and `2M`. Subtracting twice the first renormalized identity from the second cancels the torsion logarithm for any `ρ(r)→1`. Finite limits for both energies would force the positive multiple `2autocorr(g,log 2)Z(r)` to converge finitely, a contradiction.

## No-go closure

- **Killing mechanism:** overlapping copies alter the continuum Gram form but not the torsion divergence's discrete diagonal. Even a radius chosen for this single profile cannot fix both packets.
- **Positive survivor:** exact asymptotic for every packet; finite convergence iff total overlap vanishes; exact finite discriminant defect in the separated regime.
- **Forced correction:** in the separated regime, adding `MΣx_n² selfIntersection(n)+(2a₀−c)H` restores the Weil limit. The spacing regulator supplies continuum self-energy, but scalar mass calibration cannot supply the degree-dependent discriminant correction.
- **New constraint:** an alternative torsion smoothing must reproduce the continuum Gram form, including overlaps. Matching only the diagonal mass on isolated packets is insufficient. The obstruction already uses orders 1 and 2, whose torsion self-intersections vanish; it precedes the discriminant anomaly.
- **Status:** paper proof and Lean formalization complete. Both source files pass `lake --old env lean`; the principal theorems audit to `propext`, `Classical.choice`, and `Quot.sound` only. Both modules are imported by the HyperbolicArakelovTheory umbrella. B135 remains open.

## Lean declarations

- `HyperbolicArakelovTheory/TheGreenDampingOnSmoothProbes.lean`.
- `HyperbolicArakelovTheory/TheMassObstructionToSmoothedTorsionLocking.lean`: `exists_smooth_profile_without_scalar_locking`, `finite_smoothLockedPacket_iff_mass_balance`, `tendsto_smoothLockedPacket_sub_mass_defect`, `tendsto_smoothLockedPacket_weil_normalization`.
