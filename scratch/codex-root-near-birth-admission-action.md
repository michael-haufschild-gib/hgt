# CCM-FU near-birth admission action — paper proof, Lean open

This is an own research note, not an edit to the read-only frontier map. It gives a necessary condition for a uniformly quadratic literal terminal-core history. It does not establish such a history, RH, or literature priority.

## Theorem

For each prime `p`, choose an integer admission time `a(p)` with `p ≤ a(p) ≤ 2p`. At integer cutoff `M`, process exactly the active primes with `a(p) ≤ M`, giving `P_a(M)`. Suppose a constant `B` satisfies

`mobiusDivisorSelectionEnergy M P_a(M) ≤ B M²`

at every sufficiently large integer `M`. Then the *prime-harmonic quadratic admission action* is finite:

`Σ_{p prime} (a(p)-p)²/p³ < ∞`, equivalently `Σ_p ((a(p)/p)-1)²/p < ∞`.

Consequently, for every fixed `η>0`, primes admitted at or after `(1+η)p` must have finite harmonic prime mass. In particular, no history with a fixed positive proportional delay on a set of primes of divergent `Σ 1/p` can have a uniform quadratic energy budget. The statement only covers schedules `a(p)≤2p`; later admissions can enter quotient cells where the critical source changes sign.

## Proof

Put `C(x)=criticalContinuousAbel x` and `d_p=a(p)-p`. Every active prime with `p²≤M` belongs to `P_a(M)`: for `p≥2`, `a(p)≤2p≤p²≤M`. Thus the corpus's arbitrary-terminal-core source identity applies at every cutoff. Its processed head is

`H_a(M)=C(M)+Σ_{p<M<a(p)} √p C(M/p)`.                                      (1)

Every quotient in the sum lies in `(1,2)`. The exact first-cell identity, already checked in scratch Lean, is `C(y)=(√y−1)(2γ−1)` for `1≤y≤2`, and the corpus proves `2γ−1>0`. Hence `T_a(M):=H_a(M)−C(M)≥0`.

The energy contains `H_a(M)²`, so the assumed budget yields `|H_a(M)|≤√B M`. The corpus's strong `ψ` prime number theorem inserted into the literal Abel primitive gives, for some `b>0`, `|C(M)|≪M^(3/2) exp(-b√log M)`. Therefore both series `Σ_{M≥2}|H_a(M)|/M^(5/2)` and `Σ_{M≥2}|C(M)|/M^(5/2)` converge; the latter follows on substituting `u=√log M` in the comparison integral. Thus

`Σ_{M≥2} T_a(M)/M^(5/2) < ∞`.                                              (2)

All terms in (1) are now nonnegative. Tonelli for countable nonnegative sums rewrites (2) as the sum over primes of their window costs. For `M=p+j` with `1≤j≤d_p−1`, we have `M≤2p`, and on the first cell

`C(M/p) = (2γ−1)(√(M/p)−1) ≥ (2γ−1)j/(3p)`.

Consequently, with `κ=(2γ−1)/(3·2^(5/2))>0`,

`√p C(M/p)/M^(5/2) ≥ κ j/p³`.

Summing `j` gives prime cost at least `κ d_p(d_p−1)/(2p³)`. Since `d²≤2d(d−1)+1` for every natural `d`,

`d_p²/p³ ≤ (4/κ)·(prime window cost) + 1/p³`.

Sum over primes. The window costs have finite total by (2), and `Σ_p1/p³<∞`. This proves the theorem. Finitely many cutoffs excluded by the assumed eventual budget contribute only finitely many terms.

## Meaning for the whole route

The first quotient cell carries a positive, quadratic **time-of-admission cost** under prime-harmonic measure. For near-birth schedules, this cost cannot be canceled by changing the order of prime insertions; it is an invariant of the admission times. This upgrades the fixed-ratio no-go to variable, nonmonotone delays and identifies a necessary feature of any paid near-birth history: relative delays must be square-summable in prime-harmonic measure.

This does **not** prove that square-summable delay suffices. It is an integrated-in-cutoff necessary condition; the open CCM-FU theorem is a pointwise all-cutoff payment and signed growing-core covariance law. For admissions beyond `2p`, later quotient cells are signed, so the theorem does not exclude a history that compensates positive first-cell cost with genuinely source-selected negative later-cell action. That compensation, rather than an unweighted energy estimate, is the next falsifiable target.

## Falsification of sufficiency: sparse delayed blocks

The converse to the theorem is false unconditionally, even for a deterministic near-birth schedule. Choose integer cutoffs `M_j` growing sufficiently fast that the intervals below are disjoint and `Σ_j (log M_j)^(-6)<∞`. Put `w_j=⌊M_j/(log M_j)^2⌋`. For each prime `p` in `[M_j-w_j,M_j-w_j/2]`, set `a(p)=M_j+1`; for every other prime set `a(p)=p`. All these admission times obey `p≤a(p)≤2p` once the first cutoff is large.

Each block contributes at most `O(w_j³/M_j³)=O((log M_j)^(-6))` to `Σ_p(a(p)-p)²/p³`, even bounding prime count by number of integers. Thus total action is finite. At cutoff `M_j`, all earlier blocks have been admitted and exactly the current block is missing. The strong `θ` prime number theorem counts `≫w_j/log M_j` primes in `[M_j-w_j,M_j-w_j/2]`: its error `O(M_j exp(-b√log M_j))` is `o(w_j)`. Each missing child lies in the positive first quotient cell and has size `√p C(M_j/p) ≫ w_j/√M_j`. Hence its total is

`T_j ≫ w_j²/(√M_j log M_j) ≍ M_j^(3/2)/(log M_j)^5`.

The same strong PNT bounds `C(M_j)=O(M_j^(3/2)exp(-b'√log M_j))=o(T_j)`. The exact terminal-head identity therefore gives `H_a(M_j)≥T_j/2` eventually. Its squared contribution alone yields

`mobiusDivisorSelectionEnergy M_j P_a(M_j)/M_j² ≫ M_j/(log M_j)^10 → ∞`.

This counterexample is a genuine pivot: global prime-harmonic action detects persistent lag but misses arbitrarily sparse concentration. A viable invariant must simultaneously encode signed Mellin boundary jets **and** a local-in-cutoff maximal or packing bound. Merely renaming the latter as a Carleson norm would be theatre unless it can be derived from the literal arithmetic source.

Lean status: exact terminal-head identity is already formal in `MobiusDivisorAdaptiveTerminalCriticalSource`; first-cell formula and positivity pass `lake env lean` in `scratch/codex-root-proportional-delay.lean`. The infinite weighted-series/Tonelli theorem above is not Lean-closed. No full build was run.
