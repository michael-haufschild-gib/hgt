# PTR fixed linear commuting-target intertwiner — no-go

- **ID:** ptr-fixed-linear-commuting-intertwiner
- **Stage:** 5-failed
- **Type:** FALSIFIED (temporal-slab port class, not PTR)
- **Statement:** No nonzero fixed linear state port intertwines two distinct literal temporal-Maxwell prime two-cycles with any finite-dimensional commuting arithmetic target action.

## Route and exact obstruction

The tested chain is `literal prime Maxwell cells on one (D,B) state → fixed linear arithmetic-occupation port → Euler/conormal landing → confinement → RH`. Write `S_p=T_p²=1+A_p`, `S_q=T_q²=1+A_q`. The source-proved identity is `C²=t²·1`, where `C=S_pS_q−S_qS_p`, `t=tr(A_pA_q)≠0`. Let `U,V` be arbitrary commuting target matrices of any finite size and `J` a possibly noninjective rectangular linear port with `JS_p=UJ`, `JS_q=VJ`. Then `JC=(UV−VU)J=0`; multiplying by `C` gives `t²J=0`, so `J=0`. No positive metric, spectral premise, Xi zero, or target dimension choice enters.

## Positive survivor and consequence

The invertible source commutator, with exact inverse `C/t²`, is the obstruction and an ordered physical invariant; its normalization `C/t` is the existing source-derived chirality involution. Thus a surviving temporal-slab landing must retain noncommutative order or use a source-derived nonlinear, nonlocal, or prime-dependent inter-fibre transport. A separate rotating-cylinder Maxwell boundary map remains open. The algebraic Euler dilation cannot be interpreted as a *fixed linear* descent of these literal shared-state cells.

The paper proof above is dependency-closed. [Lean theorem](../../../../formal/GaloisForLFunctions/RHTower/PhotonicPrimeNoLinearCommutingIntertwiner.lean): `ptr_no_nonzero_fixed_linear_commuting_target_intertwiner`. The positive commutator-square and chirality-involution laws are in [source algebra](../../../../formal/GaloisForLFunctions/RHTower/PhotonicPrimeSourceAlgebraAbelianizationNoGo.lean). Direct Lean and targeted `lake --old build ...:olean` passed; umbrella import is wired without an umbrella build. No full build or numerical computation was used.
