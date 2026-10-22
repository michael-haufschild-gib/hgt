# HB: rapid complete cusp tails and retained physical endpoint flux

- **ID:** HB-QCFD
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Predecessor:** [physical response Mellin transport](hb-radial-response-mellin-transport.md)
- **Active attack:** [source-contact/current balance](../1-in-progress/hb-source-contact-spin-two-balance.md)

Proof chain: literal theta cusp → Xi occurrence → retained spin two → physical
causal radial/left-QNM action → fixed common Hawking-clock extinction → RH.

## Source-derived tail bound

For either actual angular-response branch and either indicial root r, let F_r
be the original flux source. Above height three its exact formula is

```
F_r(y) = (alpha/2) y^(r-2) mean(tail(theta,y)^2).
```

The square here is the complete signed complex Fourier square. No positivity
is assumed. Every complex-power-weighted scalar tail is uniformly bounded.
Apply that theorem twice, to weights w+r and zero, and bound the width-one
horizontal integral of their product. This gives, for every complex w,

```
||y^w F_r(y)|| <= C_w/y^2,       y>3.
```

To estimate the unweighted source integral with an external power y^w, choose
v=max(Re(w),0). For t>=y>3, y^Re(w)<=y^v<=t^v. The preceding theorem at real
weight v bounds ||y^w F_r(t)|| by C_v/t^2. The original source is integrable on
this ray, and integration of the majorant gives the exact estimate

```
||y^w integral_(y,infinity) F_r(t)dt|| <= C_v/y.
```

Consequently every such weighted source tail tends to zero. The original
Wronskian satisfies J_r(y)=L_r-integral_(y,infinity)F_r, so its remainder from
its actual limiting coefficient also has arbitrary power decay. The coefficient
L_r still contains the original height-four jet and the full source moment.

## Exact physical endpoint law

Write r_-=root false, r_+=root true, d=r_+-r_-, and C_-=limitingCoefficient false.
Let M be the full response mean, m its native residual mean, K its explicit
particular cusp response, and v one of the three original physical test weights.
Define J_v(f)=y^v f'-v y^(v-1)f. Above height three M-m=K, and local equality
plus the established differentiability of M and m gives the same derivative
splitting. No additional particular-response smoothness assumption is needed.

Multiplication of the native Wronskian definitions by y^(v-r_±) gives

```
J_v(m) = (v-r_-)/d y^(v-r_+) J_(r_+)(m)
         +(r_+-v)/d y^(v-r_-) J_(r_-)(m).
```

The native-L2 theorem supplies L_(r_-)=0; the other limiting flux is
L_(r_+)=-d C_-. Inserting both original source-tail identities yields

```
J_v(M) = J_v(K)+(r_--v)C_- y^(v-r_+)
         -(v-r_-)/d y^(v-r_+) integral_(y,infinity)F_(r_+)
         -(r_+-v)/d y^(v-r_-) integral_(y,infinity)F_(r_-).
```

The last two terms tend to zero by the proved source estimate. Thus the full
physical flux minus its explicit particular contribution and actual native
coefficient contribution tends to zero. This holds on both response branches
at all three original physical weights. No physical clock is adjusted.

## Surviving obstruction

The particular contribution and C_- term are retained, not proved zero.
Re(v-r_+) need not be negative throughout the critical strip. Tail decay alone
therefore does not justify discarding the full endpoint or its native moment.
A finite-part prescription and cancellation with the other action faces must
still be derived from the complete physical action if they are to be used.

The exact finite-height Mellin transport can now send its source-tail endpoint
remainders to zero. Its remaining particular/native endpoint terms, the full
admitted scalar-test remainder, angular divergences, independent SS/SV/VV
channels, solved ++/+- corrections, changing metric weights, and horizon,
characteristic and source-contact contributions still require one complete
left-QNM identity. Neither extinction nor RH is claimed.

## Search assessment

Corpus deep search indexed 57,056 files but reported partial text/source
retrieval. Candidate power-tail identities and source-argument matches
suggested the inverse-square majorant method. Discrete tail theorems were not
used for this continuous original source. The actual proof uses the existing
complete scalar-tail bound, original flux reconstruction and current-toolchain
Bochner integral and complex-power lemmas.

A broad September recurrence search found Farhangi and Rodríguez Martín,
[Solutions to 6 problems in recurrence and Van der Corput sets](https://arxiv.org/html/2609.07506v1)
(7 September 2026). Operatorial recurrence there requires unitary representations
or measure-preserving systems; neither is thereby established for this source
and physical action. That method does not close the missing invariance producer.


## Lean validation

Module:
[ThetaCuspHawkingBMQuarticCuspFluxDecay.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMQuarticCuspFluxDecay.lean),
namespace `RHTower.D4BMQuarticCuspFluxDecay`.
Six public theorems and two definitions are wired into the RHTower umbrella once.
`lake env lean /tmp/hb-cusp-flux-decay-next.lean` passed without diagnostics.
The final exact leaf
`lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticCuspFluxDecay`
passed in 25 seconds without warnings, using cached imports. No dependency or
umbrella build ran. The audited source SHA256 is
`2f8ac5abed0198f4a8539d30032f9cc2323293c08023976e9b7ef7b3dfd121dc`.

Proofs factor the weighted scalar bound, inverse-square integration, Wronskian
algebra and local derivative splitting into explicit steps. No heartbeat,
recursion-depth or transparency override was introduced. No numerical experiment
or axiom-printing check was used. All owned Lean/Lake processes completed.


Index regeneration registered all eight public declarations. Final
`scripts/formal_tools.py lint --check-generated` returned exit 1 for one other
unreachable worktree module,
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMTemporalCurrentFundamentalFactor`.
It reported no error for this leaf and no stale generated-document error.
That unrelated module was not modified. All owned search, Lean, Lake and lint
processes completed; the isolated leaf-audit directory was removed.
