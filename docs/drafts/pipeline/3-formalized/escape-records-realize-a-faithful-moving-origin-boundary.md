# Escape records realize a faithful moving-origin boundary

- **ID:** escape-records-realize-a-faithful-moving-origin-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Q-III](../1-in-progress/q-iii-escape-state-classification.md)
- **Dependency:** [Resetting the moving origin](resetting-the-moving-origin-adds-a-faithful-step-module.md)

## Construction

For the actual prefix `A`, let `a=1-epsilon<1`. Escape means its pronic
energy `E(T)` tends to infinity. If `A(n)^2/n^a` were bounded, comparison with
the convergent power sum `sum n^(a-2)` would pay the receiver. Thus that ratio
is unbounded on escape.

Choose a sequence of prefix record locations `k_m` with record heights
`M_m=|A(k_m)|` and `M_m^2/k_m^a -> infinity`. Such records can be selected
from large values of the ratio: replace an index `n` by a location of the
maximum absolute prefix on `[0,n]`. Its height increases and its location
is at most `n`, so the ratio does not decrease. The resulting heights and
locations tend to infinity after extraction.

At records, `E(k_m)/M_m^2 -> 0`: all earlier prefix values have modulus at
most `M_m`; each fixed coordinate divided by `M_m` tends to zero; the
summable pronic weights dominate the normalized cells. This is a direct
head/tail argument.

Fix any positive `c`. Choose the first horizon `T_m` with
`E(T_m) >= M_m^2/c`. Eventually `T_m>=k_m`. The actual source has
`|A(n)|<=n`, hence each energy jump is at most one. Therefore
`E(T_m)/M_m^2 -> 1/c`, so `A(k_m)^2/E(T_m) -> c` and
`k_m^a/E(T_m) -> 0`.

Take a common cofactor Gram subsequence along these horizons. The already
proved source-power bound kills the recentered translation, and the fixed
step mixed terms vanish weakly. Thus the origin-reset translated rows have
own-normalized Gram

`[K(j,l) + c/max(j,l)]/(1+c)`.

For every `c>0` this is a faithful critical Wiener module with full Bohr
hull. It is a construction conditional only on the actual escape branch,
so the final statement must be admission-or-existence with no added analytic
premise. It does not assert this mixed kernel is an unshifted Möbius
`ActualCofactorLimit` and does not settle that classification.

## Closed construction and horizon convention

To avoid a zero initial record height, cross the positive level
`M_m^2/c+1`. The first crossing `T_m` has overshoot below one, and the energy
used by `cofactorGram epsilon T_m` is `E(T_m+1)`, which differs by at most
one more unit. Hence

`M_m^2/c+1 <= E(T_m+1) < M_m^2/c+3`.

Dividing by `M_m^2 -> infinity` gives `E(T_m+1)/M_m^2 -> 1/c` and therefore
`M_m^2/E(T_m+1) -> c`. Multiplying by the already obtained
`k_m^a/M_m^2 -> 0` gives `k_m^a/E(T_m+1) -> 0`. Monotonicity of finite energy
and divergence of these levels imply `T_m -> infinity`. The record-energy
limit gives `E(k_m)<E(T_m)` eventually, so `k_m<T_m`; thus origins can be
chosen inside their observation horizons.

No sign extraction is needed: `A(k_m)/sqrt(E(T_m+1))` stays bounded in
absolute value, while its square tends to `c`. Each mixed step/receiver
pairing tends to zero, so the signed cross terms vanish even if record signs
alternate. Extract the actual cofactor Gram along the cofinal `T_m` family.
The recentered error and its fixed dilates vanish by the verified uniform
source-power budget with `a=1-epsilon`. This closes the paper construction
of the stated mixed kernel for every `c>0` on the escape branch.

## Lean coverage

All thirteen boundary modules passed direct canonical source checks and
transitive axiom audits containing only `propext`, `Classical.choice`,
`Quot.sound`; sessions and dependency checks are in
[the completion ledger](q-iii-existing-findings-lean-completion.md).

- `admits_or_exists_record_horizons` in `EscapeRecordsControlMovingOriginMass`
  supplies cofinal observation horizons, interior origins, prescribed trace
  mass and vanishing source-power ratio (declaration namespace:
  `GaloisForLFunctions.ArithmeticDefectRigidity`).
- `CommonCofactorLimitsExistAlongPrescribedHorizons` extracts the actual
  common Gram along those horizons.
- `ResettingTheMovingOriginAddsTheMaxKernel` identifies the mixed Gram.
- `TheOriginStepModuleHasTheFullBohrHull` and
  `PositiveOriginMixturesAreFaithful` prove injective cyclic maps, zero
  annihilators and full Bohr hulls using the complete Wiener action.
- `EscapeRealizesEveryPositiveOriginBoundary` proves
  `admits_or_every_positive_faithful_boundary_is_realized` and the zero-mass
  recovery `mixedOrigin_kernel_zero`. Its final check was `60215`.

The general record/first-crossing device is not claimed as a new general
analysis theorem; its target is the exact actual Möbius moving-origin
boundary. No numerical experiment, actual escape instance or zero
configuration is used or claimed. The unshifted classification remains open.
