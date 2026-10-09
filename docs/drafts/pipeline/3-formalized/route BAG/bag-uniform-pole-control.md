# BAG uniform finite Euler pole geometry

- **Stage:** 3-formalized

01at. Exact paper consequence of the fully audited all-frequency U1
comparison and the corpus's global polynomial residue-factor bounds.
Scratch84975 and production74521 emptyPASS; axiom58622 standard3 only.

For each real A there is C>0 such that, eventually in the ORIGINAL cutoff N,
for every real |a|<=|A| and EVERY real t, write
Q_N=product_(p<=N)(1-p^(-1-a/logN-it)), d=1/logN+it. Then

  |d| <= C*(1+|t|)^9*|Q_N|,
  |Q_N| <= C*(1+|t|)^9*|d|.

Both signs of the logarithmic real shift are allowed. The lower estimate
controls inverses, including the pole-scale region. On each fixed compact
frequency interval, |Q_N| is therefore comparable to 1/logN+|t|.

Proof: U1 supplies B>0 with exp(-B)<=|Q_N|*|zeta(1+d)|<=exp(B).
For N>=3, Re(1+d) belongs to[1,2]. Existing
ChiRamanujanGlobalResidueControl.exists_residue_global_polynomial_disks,
applied at each disk's center, gives M>0 with |R|,|1/R|<=M*(1+|t|)^9,
where R=zetaResidueFactor(1+d)=d*zeta(1+d). Both d and zeta(1+d) are nonzero.
Multiply the lower U1 inequality by exp(B)*|d| and use the upper R bound;
this proves the first claim with C=exp(B)*M. Multiply the upper U1 inequality
by |1/R|*|d| and use the inverse R bound to prove the second.
Every factor and domain condition is supplied unconditionally by the corpus.
No zero-free region, residue estimate, convergence or RH premise is assumed.

Corpus: exact global-disk theorem and ZetaResidueFactorDerivative definition
read from source. Lexical research query exists_residue_global_polynomial_disks
retrieved the global and high-frequency disk declarations; lexical output
has no coverage/compiler-freshness metadata. Scratch verifies applicability.
This is pole control, not full labelled or actual physical cancellation.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiRamanujanGlobalResidueControl` | `exists_zeta_polynomial_zeroFree_region`, `exists_residue_polynomial_disks`, `exists_residue_global_polynomial_disks`, `exists_residue_derivative_polynomial_bounds` |
| `GaloisForLFunctions.RHTower.ChiRamanujanUniformPoleControl` | `criticalFiniteEulerProduct_pole_comparison` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
