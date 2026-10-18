# Canonical squarefree state and finite defect certificate

2026-10-18. Second contribution in an ACTIVE open-ended THIM research goal. Do not mark the whole goal complete. User forbids hgtl7, RH focus, numerical experiments, proof holes/new axioms, heartbeat changes, and README edits. One foreground Lean process; other agents build concurrently.

Source: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/HorizonRadicalStateAndDefectNormalForm.lean`.

- `horizonRadicalState N k = gcd(k,primorial N)` is positive, squarefree, divides k and the primorial, and has range exactly the divisors of the primorial. Valid at N=0 and k=0.
- State equality iff equality of every squarefree-supported sieve response. Converse uses prime-indicator weights. State is the least positive representative of its class.
- `R_N(kl)=lcm(R_N(k),R_N(l))`; positive powers preserve state. Both active sawtooth endpoints factor through state for positive k.
- For squarefree-supported c and k>=1, r=R_N(k):
  `2(D_N(k-1;c)-D_N(r-1;c))=-sum_{j=r}^{k-1}(s_N(j+1;c)-s_N(j;c))^2`.
  Includes r=1 by extending polarization to empty prefixes. Canonical representative maximizes defect among POSITIVE observations in its fibre. Equality iff every intermediate additive step is flat.
- CENTRAL: `sieveRenormalizedPrefixDefect_global_upper_bound_iff_radical_states`:
  for every real B, `(forall M, D_N(M;c)<=B) iff (forall r, r|primorial N -> D_N(r-1;c)<=B)`.
  Exact finite certificate for an infinite prefix upper-bound problem, not merely a cofinal bound.
- Damped sign theorem: epsilon>=0, k>=1, R_N(k)<=2N implies D_N(k-1;c_epsilon)<=0. Mobius at epsilon=0. Allows independent visible-prime exponents and arbitrary factors with primes above N; no bound on k. Uses previous package at r and exponent1, with r1 handled separately.

Boundary: no additive successor closure claimed; energy records path information. Residual canonical representatives r|primorial N with r>2N remain unclassified for damped global sign. Period drift is assigned to another README track; avoid duplicate work. No global novelty claim; corpus research found constituents and previous full lcm-state but no equivalent squarefree state/finite defect certificate.

Verification: actual source `lake --old env lean -o <leaf.olean> <leaf.lean>` exit0, no warnings. Separate scratch import #print axioms for all20 public theorems +1definition exit0: every closure exactly propext/Classical.choice/Quot.sound. SHA256 06d29cef6c6307b1b4785bcedca16e672a84e6decddeb04eb46c0dfc9e56d654. All API entries and MainTheorems-to-umbrella-to-leaf reachability verified. Index exit0. Global lint --check-generated exit1: eight unrelated-area unreachable modules plus existing field-umbrella registration; no own-leaf finding or stale generated file in that run. Do not claim globally clean lint.

Artifacts: card `docs/drafts/pipeline/3-formalized/thim-horizon-radical-state-defect-normal-form.md`; continuing ledger `logs/thim-radical-sawtooth-knowledge.md`; `logs/thim-radical-state-{lean,axioms,index,lint}.txt`; `logs/thim-radical-state-audit.json`. Nine owned scratch files removed after all jobs exited. Source imported once by field umbrella; README untouched. Previous contribution: `mem:trans-horizon/all-horizon-radical-sawtooth-defect`.
