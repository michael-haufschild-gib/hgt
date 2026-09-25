# Final-overlap attack on reserve extension

Numerical guidance only; no value enters Lean. The frozen hypothesis is
the same local extension property in the
[direct induction card](../../../1-in-progress/ccm-fu-reserve-extension-induction.md).

At every integer M=65..1024, retain every subset of two through five primes
with p*p<M and process every other prime below M. The complete actual
source is grouped by these remaining prime labels, with every Möbius sign
and clipped dilation retained. These are full states near completion,
not selected packets with their complement omitted.

[screen.py](screen.py) tests all306999 states in this family and every
outgoing prime. All54466 states satisfying
`Q+2sqrt(GD)<=Q_empty` have a certified successor. There is no reported
failure. [summary.json](summary.json) contains per-cutoff counts and the
state with least successor reserve at each cutoff. This finite pass leaves
the all-cutoff inequality and RH open.

The existing defect/unit-clock table and greedy original diagonals were
reused. Original diagonals agree at tolerance `1e-12*max(1,Q_empty)`.
For a last oriented pair x,y, the exact algebraic identity
`Phi=max(x*x+y*y,(x-y)^2)` checks the terminal implementation; it is a
predictable validation identity, not a new experimental finding. Every
failure and all its successors would be independently regrouped directly
from signed source coefficients; none occurs. Floating-point arithmetic
and the original input-table uncertainty are retained.

RunPod: `ssh root@157.157.221.29 -p27094 -i~/.ssh/id_ed25519`.
Owned directory: `/root/ccm_fu_final_overlap_20260907_01a077d3`.
Foreground command `timeout 60s python3 screen.py` completed in about
0.820 seconds, using eight workers and one-thread BLAS/OpenMP. No
background job or timeout occurred. The exact input hashes are recorded
in the output. Both downloaded/local artifact hashes match the remote
originals:

| File | SHA-256 |
| --- | --- |
| screen.py | 2ee8e5b5ad5d6b34f26a9168f3190b529a912cb0e42fcb12606ced49f5ed609f |
| summary.json | 33cec69b6f79dc4d444f6cb9d85d9dbdaa2e84b6bccb6e1f2adf842c98684b80 |

Remote inputs, script, output and the owned directory were removed after
download verification. No owned computation process remains.
