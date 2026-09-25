# Exhaustive CCM-FU order feasibility with accumulated-charge control

Numerical diagnostic only. All integer cutoffs 2 through 48 pass the frozen
test. No all-cutoff inequality or RH proof follows. See the
[protocol and mathematical scope](../../../1-in-progress/ccm-fu-charge-safe-order.md).

## Test and result

The test asks whether some complete prime order keeps both the actual raw
energy below its initial value and accumulated arity charge nonpositive
at every prefix. The exact existing balance converts the latter to
`D(P)+sum W<=D_0`, where W is the full copied-child square cost.

A dynamic program retains the minimum accumulated W among admissible
histories ending at each processed subset. Every continuation from that
subset has identical subsequent edge costs; discarding larger costs loses
no feasible order. Complete ordered source-pair kernels and subset zeta
transforms generate Q and W. Independent direct fibre regrouping checks Q,
D and every unused-prime W at **every** subset of **every** cutoff.

All 47 cutoffs pass. At every tested cutoff, every subset whose Q lies
below the initial ceiling is reachable under the additional charge
constraint. This stronger pattern was observed, not assumed in the
protocol; its all-cutoff version remains unproved.

At M=48, 666 of 32,768 subsets exceed the raw-energy ceiling; all remaining
32,102 are reachable. The frozen 80-digit independent audit checked this
saved complete order:

`47,43,41,31,7,37,5,29,3,2,23,19,17,13,11`.

| Quantity | Independently audited value, rounded |
|:---|---:|
| Initial Q | 3.37779279505674529 |
| Initial D | 3.94716608692011278 |
| Final accumulated W | 1.27400862737379798 |
| Final accumulated J | -2.67315745954631479 |
| Final signed head | -0.91397916303658708 |
| Final head square | 0.83535791046506023 |

The audit reconstructs coefficients from the original time sum with
independent trial factorization, not the screen's quotient-block routine.
It checks every saved prefix, each complete signed cofactor charge, and
the final head. Because no cutoff failed, the protocol selected a witness
audit, not an 80-digit exhaustive rerun. The all-subset results remain
double-precision observations. Neither precision is an interval certificate.

## Files and execution

- `source_screen.py`: unchanged earlier source generator, imported only.
- `screen.py`: full pair transforms, direct checks and exhaustive recurrence.
- `cutoff_M.json`: cutoff metadata and complete successful witness.
- `cutoff_M.npz`: all Q, D, W, minimum costs, predecessors and prime labels.
  Array indices are processed-set bitmasks, using the saved prime order;
  W row j is used only when prime j is unprocessed. Infinite cost marks an
  unreachable state; predecessor -1 marks no accepted predecessor.
- `summary.json`: all cutoff records, runtimes and script/source hashes.
- `audit.py`, `audit.json`: independent selected witness audit.
- `SHA256SUMS`: all 99 downloaded script/result/array hashes, verified
  against their remote copies before cleanup.

All mathematical execution used the supplied RunPod:
`ssh root@157.157.221.29 -p 27094 -i ~/.ssh/id_ed25519`.
Four workers; one BLAS/OpenMP/MKL thread each. Internal limit 90 seconds,
outer timeout 100 seconds. Screen: 0.2180628404 seconds. Successful audit:
0.0148053989 seconds. A first audit invocation failed immediately because
Python 3.8 lacks `int.bit_count`; the identical population count was
replaced by `bin(r).count('1')`. No cutoff, witness, tolerance or mathematical
test changed. Screen acceptance tolerance is `1e-10 max(1,Q_0,D_0)`;
audit comparison tolerance is `1e-65 max(1,Q_0,D_0)`.

The download command reported the generated `__pycache__` directory was
not a regular file; all 99 intended files nevertheless downloaded and
matched the remote hash manifest. Cache bytecode is not a result artifact.
The owned remote directory and processes were cleaned up.

## Remaining gap

Finite feasibility does not give a uniform source bound. Even global
reachability of every below-ceiling state would leave the complete head's
ceiling to prove. Accumulated arity charge only sees a distinct source pair
through common primes surviving after its differing primes are processed;
coprime pairs contribute zero. The complete head square also contains
those coprime pairs. Their arithmetic compensation remains unproved.
No numerical value is used in Lean, and no new Lean checks were needed.
