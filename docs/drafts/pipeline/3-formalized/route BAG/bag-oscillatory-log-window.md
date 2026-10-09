# BAG off-pole prime logarithmic-window transport

- **Stage:** 3-formalized

For every nonzero real tau the literal prime-ordered boundary sums
S_tau(x)=sum_(p<=x) p^(-1-i*tau) converge to some A_tau, by the corpus
PrimeZetaOneLineConvergence theorem. For every fixed complex w,
 sum_(p<=N) p^(-1-i*tau)*exp(w*logp/logN) -> A_tau,
 sum_(p<=N) p^(-1-i*tau)*(logp/logN)*exp(w*logp/logN) -> 0.
The same A_tau serves every w. No numerical or unproved prime bound enters.

More generally, for C^1 H on [0,1], finite integration of each atom gives
 sum_(p<=N) H(logp/logN)*p^(-1-i*tau)
 = H(1)*S_tau(N)-int_0^1 H'(t)*S_tau(N^t)dt.
The equality p<=N^t iff logp/logN<=t keeps the actual cutoff. Endpoint atoms
are included; changing a singleton in the real integral contributes zero.
S_tau is globally bounded because its integer partial sums converge and its
real partial sums are their floor extension. For t>0, N^t tends to infinity.
Dominated convergence applies on (0,1] with norm(H'(t))*C as majorant.
The limit is H(1)A_tau-(H(1)-H(0))A_tau=H(0)A_tau. Choose H=exp(wt) and
H=t exp(wt). The derivative is computed from the actual entire exponential.

This pays the oscillating prime-window input exposed by the BAG mixed source,
including a moving O(1/logN) complex exponent, rather than invoking the old
fixed-profile Mertens law at a diverging frequency. Euler-product boundary
identification, exact rational response/collision transfer, and uniform
physical tails remain open. Scratch11875 and production93239 passed with empty output.
Production ChiRamanujanOscillatoryLogWindow has243lines; final foreground
`lake --old env lean ... -o ...olean` audit complete. Axiom25259 PASS (standard three axioms only); index95668 PASS/API6; wired once.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiRamanujanOscillatoryLogWindow` | `criticalPrimeBoundarySum_tendsto`, `criticalOscillatoryLogWindow_tendsto`, `criticalOscillatoryLogWindow_difference_tendsto` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
