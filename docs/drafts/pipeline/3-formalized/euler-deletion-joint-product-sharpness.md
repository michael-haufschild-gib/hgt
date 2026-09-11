# Sharp convergence boundary of the actual joint deletion product

**Stage:** 3-formalized. **RH implication:** none. **Novelty:** not certified.

For the fixed six-coordinate generators `X=E_01+E_12` and `Y=E_23+E_34+E_45`, the
literal moduli-two-and-three product with weights `n^(-s)` converges on the positive real
axis exactly when `s>1/5`. In particular it does not converge at `s=1/5`.

This is a theorem about the actual weighted source. Each six-factor frozen block equals
`1-q_k Z`, where `Z=E_05` and `q_k=(6k+1)^(-5s)/60`. For the actual block `B_k`, set
`E_k=B_k+q_k Z`. Lean proves `sum ||E_k-1||<infinity` for every `Re(s)>0` and the exact identity

`B_0...B_(N-1)=E_0...E_(N-1)-(sum_{k<N}q_k)Z`.

The corrected products converge. Their `(0,5)` coordinate isolates the scalar series, which
is nonsummable for real `s<=1/5` by comparison with the harmonic series. A convergent actual
source product would give bounded partial sums of this nonnegative series, a contradiction.

Module: `formal/GaloisForLFunctions/RHTower/EulerDeletionJointProductSharpness.lean`.
Namespace: `RHTower.DeletionJointSharpness`.
Capstones: `sourceProduct_not_convergent`, `positive_real_convergence_iff`,
`oneFifth_sourceProduct_not_convergent`. The last theorem has no supplied premise.

`lake env lean /tmp/hgt-joint-polygon-17TZsg/SharpnessAudit.lean` passed. Seven axiom
audits, including the decomposition, correction convergence, scalar obstruction, and capstones,
report only `propext`, `Classical.choice`, and `Quot.sound`. Production matches the audited
scratch body. The narrow final
`lake build GaloisForLFunctions.RHTower.EulerDeletionJointProductSharpness` passed.
The umbrella import is wired; no umbrella build ran. Repository-wide
`scripts/formal_tools.py lint` passed. No computation or external certificate was used.

This closes the fixed-target sharpness claim in the
[paper theorem](euler-deletion-joint-product-one-fifth.md).
The general coprime-modulus extension remains paper-only. No relation forced by a zeta zero,
off-line contradiction, or qualifying RH proof architecture is established by this result.


The [full complex successor](edq-joint-fifth-phase-asymptotic.md) now proves convergence exactly
for `Re(s)>1/5` throughout the positive half-plane, retaining the explicit power/logarithmic
asymptotic and the full summable correction. The two-prime phase clock closes every oscillatory
boundary point. This extends the fixed-target classification without supplying an RH implication.
