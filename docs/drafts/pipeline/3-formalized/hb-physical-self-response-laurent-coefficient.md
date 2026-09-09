# HB: complete physical Laurent coefficient and pole-survival criterion

Status: formalized. RH remains unproved.

At both original fundamental QNMs of every actual Xi copy, the complete
same-copy physical response has an explicitly derived simple-pole term
and an analytic remainder. The coefficient retains the actual residual
angular period, all three cutoff corrections, both original radial source
moments, and the original connection normalization. No source-nonvanishing
or spectral-noncollision premise is supplied.

## Complete angular reduction

Use the original notation from the
[same-copy continuation](hb-physical-self-response-continuation.md):
residual period A, cutoff periods C_i, principal amplitudes A_i, and
nonzero same-copy angular gaps delta_i. Scalar linearity of both native
Green integrals, including the finite-part endpoint subtraction, gives
U(J)=J U(1). Therefore the actual continued response is exactly

```text
A_eff = A - sum_(i=0..2) C_i A_i / delta_i
P(w,t) = A_eff U(1)(w,t) + sum_(i=0..2) (C_i/delta_i) V_i(w,t).
```

This identity holds before taking a frequency limit. No cutoff period is
discarded and A_eff is not an assigned coupling.

## Original fundamental denominators

The two actual Laplace frequencies are

```text
w_plus  = -3/2 - i chi = -1-rho/2
w_minus = -3/2 + i chi = -2+rho/2.
```

The original Xi zero is nonreal. Both frequencies are nonreal and satisfy
|Re w|<2. Direct algebra proves w_star-2s is nonzero for either original
source branch. For every one of the three principal angular frequencies,
both denominator Gamma arguments at either w_star have nonzero imaginary
part. Their original principal connections are therefore nonzero.

The actual cleared principal numerators are analytic in the continued
strip. Dividing by these nonzero denominators proves the entire retained
principal sum analytic at w_star. This is a radial noncollision proof;
the previously proved nonzero angular gaps alone did not establish it.

For the target connection

```text
c(w) = Gamma(C) Gamma(1/2) / [Gamma(C-A) Gamma(C-B)],
```

one reciprocal-Gamma argument vanishes at the fundamental resonance.
Its derivative in w is 1/2. The other argument equals 3/2+w_star and is
nonreal. Differentiating the original factorization, using the corpus's
reciprocal-Gamma derivative at zero, gives

```text
d = c'(w_star)
  = Gamma(1+w_star) Gamma(1/2) / [2 Gamma(3/2+w_star)] != 0.
```

Thus the target connection has a derived simple zero with its actual
normalization. No derivative or simplicity premise is introduced.

## Native radial numerator

At fixed original t<0, put b=horizonCoordinate(t), J=1, and
K=reducedGreenGradient(chi,s,1). Define

```text
Q(w,t) = Normalizable(w,b) firstEndpointMellin(horizonMellinCore(s,chi,a,1,K),b,w)
       + Horizon(w,b) integral_(b..1, Normalizable(w,r) sourceProfile(s,w,a,1,K,1,r))
T_c(w) = 1+(w-2s) onsetCorrection(2s,w)
N_c(w,t) = Q(w,t) T_c(w) + c(w) radialLift(s,w,a,T_c(w),t)
E(w) = -(w-2s)c(w).
```

The exact identity N_c=E U(1) holds wherever the original two
denominators are nonzero. N_c is analytic through both target resonances.
At w_star the lift term vanishes, leaving both source moments multiplied
by the complete smooth-onset numerator. In particular this is an
analytic numerator, not the totalized value of U(1) at a pole.

The cleared denominator has

```text
E(w_star)=0,
E'(w_star)=-(w_star-2s)d != 0.
```

The derivative's slope limit gives the actual Laurent coefficient

```text
R(q,branch,side,a,t) = A_eff(q) N_c(w_star,t) / E'(w_star)
lim_(w -> w_star, w != w_star) (w-w_star) P(w,t) = R.
```

## Exact pole classification

Meromorphy and the proved limit give an analytic extension of
(w-w_star)P with value R at w_star. Its analytic divided difference
produces an analytic function G on a neighborhood of w_star such that

```text
P(w,t) = R/(w-w_star) + G(w),  for w near but unequal to w_star.
```

Consequently P has a finite punctured limit if and only if R=0. Since
E'(w_star) is nonzero, the exact nonremovability criterion is

```text
P has no finite punctured limit
    iff A_eff(q) != 0 and N_c(w_star,t) != 0.
```

This is a proved classification of the original source, not a proof that
either factor is nonzero. The capstones are
`continuedPhysicalSelfResponse_residue_tendsto`,
`continuedPhysicalSelfResponse_laurent_remainder`, and
`continuedPhysicalSelfResponse_nonremovable_iff`.

## Scope and remaining problem

These are scalar germs at every fixed original t<0, for the same source
and target Xi copy. Equality to the original physical Hilbert response
holds on the previously proved overlap. No operator-valued or radial-L2
continuation at the resonances is asserted.

For strict-right Xi copies, the [complete angular-source evaluation](hb-effective-angular-source.md)
now combines the source-identified physical period with every cutoff
correction. The angular factor is the explicit four-Lambda product;
its nonvanishing and that of the radial source moment remain to be proved.
Identification with a full retarded/advanced adjoint pairing, its
multiplicity-matched spin-two/AIME reconstruction, and independent
source-level extinction remain open. RH is not proved.

## Corpus comparisons

Separate broad searches for Fokas and Higgs found respectively 2,254
declarations in 163 modules and 285 in 26 modules in the cached index.
The inspected Fokas--Lenells results identify a nonlinear compatibility
moment with an actual reciprocal-pole coefficient
(`FokasLenellsRegularOrigin`) and make its vanishing equivalent to
operator-norm time differentiability (`FokasLenellsCauchyNormGate`).
Strong differentiability on every vector does not imply that operator
condition. This supplies a concrete model for relating source residues
to regularity; no transfer of that model's compatibility law to HB has
been proved.

`AdjointClockHiggsMechanism` identifies an unbroken stabilizer with the
centralizer of a selected clock holonomy. Its group adjoint action does
not identify the left state of this radial boundary problem.
`CausalRayPolarityNonselection` proves that positive null outer squares
and equal scalar weight can still give distinct causal rays. Neither
result supplies the missing physical source orientation.

## Lean audit

Ten new RHTower leaves, prefixed `ThetaCuspHawkingBM`:

- `SourceAmplitudeLinearity`
- `PhysicalSourceCoefficient`
- `PhysicalFundamentalFrequencies`
- `PhysicalPrincipalNoncollision`
- `PhysicalPrincipalRegularity`
- `ConnectionSimpleZero`
- `ReducedGreenNumerator`
- `PhysicalFundamentalSlope`
- `PhysicalSelfResidue`
- `PhysicalSelfLaurent`

The leaves contain 37 public theorems and 10 definitions in 677 lines;
the largest has 93 lines. All scratch checks used `lake env lean`.
All ten individual final `lake build <exact-module>` checks passed
without warnings in an isolated project using cached dependencies.
Only the 47 new public declarations were axiom-audited; each uses exactly
`propext`, `Classical.choice`, and `Quot.sound`. No added axiom or
computational certificate is used. All 30 installed source/olean/ilean
artifacts match the audited files by SHA-256. Ten unique umbrella imports
are wired; no umbrella or full build was run.

The generated index and `scripts/formal_tools.py lint --check-generated`
pass, retaining 141 existing large-file warnings. `git diff --check`
passes. The frontier map's SHA-256 is unchanged.
