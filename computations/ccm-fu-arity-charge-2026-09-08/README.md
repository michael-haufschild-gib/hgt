# CCM-FU arity charge: frozen trajectory replay

Status: numerical diagnostic completed; exact algebraic accounting separately
formalized. Neither accumulated-charge control nor RH is proved by these data.
The [protocol and mathematical scope](../../../1-in-progress/ccm-fu-arity-charge.md)
were fixed before execution. No policy, cutoff or audit-selection rule changed.

## Question and method

For each complete divisor-source state, let `D=sum_R |R| F_R^2`. At a
selected prime `q`, let `W=sum_R F_(R+q)^2` and
`J=2 sum_R |R| F_R F_(R+q)`, over all labels avoiding `q`.
Replay eight previously saved complete greedy trajectories, retaining all
incidences, to distinguish stepwise decrease of `D` from a bound on
accumulated signed charge. Check each raw energy against its saved value
and check `D_n=D_0+sum J-sum W` at each prefix.

Input paths are the unchanged
[fixed-late-greedy summary](../ccm-fu-fixed-late-greedy-2026-09-08/summary.json).
The two policies allow every unused middle prime and the next isolated late
prime in a fixed increasing or decreasing order, selecting least raw next
energy among permitted actions. This run only replays those saved paths.

## Observed outcomes

Every path has `max D/D_0=1` and no positive accumulated-charge prefix in
the double-precision screen. Every path also has positive individual `D`
increments. Indices start at zero. Maximum charge below excludes the empty
prefix, whose charge is zero.

| M | Late order | First positive D index | Positive D steps | Max accumulated J / D_0 | Final sum W / D_0 |
|---:|:---|---:|---:|---:|---:|
| 512 | increasing | 16 | 3 | -0.636010 | 0.363412 |
| 512 | decreasing | 17 | 6 | -0.632998 | 0.367002 |
| 2048 | increasing | 67 | 5 | -0.659302 | 0.327501 |
| 2048 | decreasing | 63 | 9 | -0.659302 | 0.326449 |
| 8192 | increasing | 127 | 13 | -0.675538 | 0.302792 |
| 8192 | decreasing | 131 | 14 | -0.675538 | 0.302150 |
| 32768 | increasing | 265 | 17 | -0.685001 | 0.285935 |
| 32768 | decreasing | 278 | 6 | -0.685001 | 0.285472 |

The independent 80-digit audit selected `M=512`, increasing order, index
16, prime 71 by the frozen first-positive-D rule. It reconstructed the
original time-sum coefficients with independent trial factorization.

| Quantity | Audited value, rounded |
|:---|---:|
| D before | 50.97622581748012078 |
| D after | 51.07259060491095206 |
| D increment | 0.09636478743083128 |
| J | 1.08374353935308260 |
| W | 0.98737875192225132 |
| Raw Q before | 35.86162828179455247 |
| Raw Q after | 35.82952133717677123 |

The complete nonzero copied packet has cofactors `r=1,5,7`. Their charge
contributions are respectively `0`, `1.09115412755617016`, and
`-0.00741058820308756`; every child square is retained in `W`.
Thus the audited raw-energy descent has a positive arity increment.
This rules out transferring stepwise contraction between the two energies
on numerical evidence, while leaving their global ceilings open.

No accumulated-charge crossing occurred, so the protocol did not trigger
an 80-digit replay of an entire prefix. Only the selected state and its
successor have that independent high-precision audit. Floating values are
not interval certificates. No result is used as a Lean premise.

## Execution and provenance

All mathematical computation ran on the supplied RunPod through
`ssh root@157.157.221.29 -p 27094 -i ~/.ssh/id_ed25519`.
Four independent workers; BLAS/OpenMP/MKL each limited to one thread.
Internal deadline 90 seconds; outer timeout 100 seconds.
Screen wall time: 0.5802904814 seconds. Audit wall time: 0.1037576571
seconds. Both completed normally. Downloaded files were compared against
remote SHA-256 values; owned remote directory and processes were cleaned up.

- `source_screen.py`: unchanged source generator copied from the prior
  diagnostic; imported by the screen, not executed through its old main.
- `screen.py`: complete incidence replay and prefix accounting.
- `cutoff_*.json`: complete per-cutoff trajectories and charges.
- `summary.json`: aggregate records, runtimes and input/script hashes.
- `audit.py`: independent original-source reconstruction and selected audit.
- `audit.json`: audited state, every cofactor, and exact selection provenance.

| Artifact | SHA-256 |
|:---|:---|
| Input paths summary | `0d94afe4d3695afc431cc07c3b11b5d45b4dd8cf47834b0e17e585718782d2bd` |
| source_screen.py | `77bcc9058e05d01f20fdbe49536ab800b5a046512324cb2e5e2605cde2313427` |
| screen.py | `368b89889e1afa2777b119941f037e2c37150a7f8732fb5a284bf56c14d991a8` |
| audit.py | `6d02700c70a006d24652637abeadca10e863479c9e6b2ee30b94bb90c6fd1160` |
| summary.json | `4e0f0fbfcc57942244d252825e0e36edf527a22db56ed473a4d0182d33edd6ed` |
| audit.json | `36497afac84a556b17bd0d01d6353e6420adec52f68c214e4862a7c79ac225a5` |

## What survives analytically

The separately checked Lean module `RHTower.MobiusDivisorArityCharge`
proves the exact one-step and accumulated identities for every prime
history, the initial bound `D_0 <= 722 M^2 floor(log_2 M)`, and zero arity
energy after complete processing. For generic signed fields it proves a
nonincreasing arity move with two coordinates and sharp factor `4/3`
with three. These algebraic theorems use no numerical observations.

The remaining arithmetic problem is a useful uniform accumulated-charge
bound through all interacting primes. The head has zero arity weight, so
even such a bound needs a further head estimate and scale control before
it could close CCM-FU.
