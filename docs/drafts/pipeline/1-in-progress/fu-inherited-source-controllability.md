# FU: inherited source controllability

Status: investigation; no claimed theorem yet.

Objective: remove a structural obstruction beyond prescribed-prime finite-cube sign preparation. No numerical experiments, external search, new hypotheses, or estimate-only deliverable.

Plan:
1. Recover the exact remaining obstruction from current Lean statements and corpus search.
2. Conjecture and attack structural mechanisms; record failures and positive survivors.
3. Complete a dependency-closed proof before formalization.
4. Audit each leaf with `lake --old env lean`, audit axioms, wire imports, run formal lint, remove scratch artifacts.

Corpus findings:
- `exists_mobiusDivisorPreparedPrimeCube` repairs every prescribed finite Boolean sign but does not repay helper energy.
- `exists_mobiusDivisorQuantitativePrescribedDebtPayment` gives simultaneous positive absolute and relative payments. Its iteration has no nonsummability mechanism.
- `exists_mobiusDivisorUniformReserveHistory` changes cores with an all-cutoff budget but need not exhaust primes.
- `exists_mobiusDivisorCoupledTwo_positive_circuit` controls one particular two-coordinate source. Higher inherited residual fields need a source-generated controllability argument.
- `criticalAbelLogProfile_mass_zero` supplies an exact signed cancellation, and causal dilation supplies distinct source onsets.

Conjecture ledger:
1. Iterating distant bounded-mass helpers repays arbitrary fixed debt. Rejected: the current delayed-repayment obstruction retains the fixed initial head and rules this out. Positive lesson: distinguish marginal sign preparation from net repayment.
2. Every finite retained-prime source field has full positive span after a finite complementary completion. Already solved more strongly in `RetainedPrimeLandauSeparation`, `RetainedPrimeFiniteSourceMargin`, and `RetainedPrimeBoundedBatches`; do not repackage this as new work. `MobiusDivisorFiniteDepthPrimeCancellation` also treats finite delayed fields over inherited cores.
3. Neutralizing all retained receiving coordinates pays insertion of the prescribed retained field. Rejected: insertion also merges residual fibres outside that field. Their inherited covariance is not controlled by the receiving vector. The existing two-coordinate positive-debt circuit addresses exactly this extra quadratic quantity.
4. Iterated fixed-core spectral payment might produce cofinal energy control. Still unresolved: `MobiusDivisorPrimeBlockEnergyEscape` proves exponential limiting energy for natural exhaustive cores, so limit-first arguments cannot be promoted to moving-cutoff control without controlling escaping spectral mass.
5. Admit primes at a common nontrivial zero of the continuous child source. Rejected as the deliverable: zero insertion work on a real clock does not pay original integer-clock drift; treating it as a solution would merely move the debt.
6. Paid least-missing-prime exhaustion at a fixed proportional clock. Paper mechanism below; checking the existing source lemmas and formal dependencies before implementation.

## Candidate 6: paper proof

Write `H(K)` for the complete signed child source. Existing PNT cancellation gives `H(K)/K^(3/2) -> 0`. Existing source windows give fixed positive and negative singleton intervals, each with amplitude at least a fixed positive multiple of `sqrt(M)` and prime count asymptotic to its interval width times `M/log(M)`.

Choose one sufficiently large integer clock factor `A`, divisible by the source-window clock modulus. At `M=A*r`, the mandatory prime's singleton is `-sqrt(r)*H(A)`. Thus a bounded number `K(A)` of opposite-sign singleton helpers covers its magnitude, with `K(A)/A -> 0`. Choose `A` so both witness windows have asymptotic prime counts strictly larger than `(K(A)+2)*pi(r)`.

Start with every prime below a sufficiently large fixed seed bound. At each stage let `r` be the least missing prime. All primes below `r` have already been processed, and `r>A`, so the state is terminal at `A*r`. Every remaining prime is a scalar singleton. The small child core is complete, hence its coefficient is independent of the inherited history.

Maintain `card(P) <= D*pi(r)` with fixed `D=K(A)+1` (enlarge harmlessly if required). Each source window has more than `card(P)+K(A)` primes, so at least `K(A)` remain fresh. If the mandatory singleton has favorable sign against the receiving head, insert it directly. Otherwise select opposite-sign helpers until their mass crosses its magnitude. The final total singleton mass has sign opposite the receiving head; its overshoot square is paid by selected singleton squares. Consequently the complete raw energy is no larger than the pre-block energy. The logarithmic clock weights only add nonnegative removed-square credit. Scalar endpoint ordering pays every prefix of the whole block, with the mandatory prime included.

Each block uses at most `D` primes. The next least missing prime has prime count at least one larger, preserving the counting invariant. Mandatory primes strictly increase; every prime is eventually processed. All bounds and source supplies are fixed before constructing this infinite inherited history.

The intended theorem is an actual prime-exhaustive schedule whose complete logarithmic insertion work is paid at every block's own original integer cutoff. It does not assert a bound for cutoff drift or for completed action at earlier cutoffs.

Significance gate: a generic cone receiver is insufficient. Any survivor must discharge its source hypotheses on the actual arithmetic profiles and explicitly identify the finite inherited obstruction removed.

Formal construction choice: scan consecutive primes `r_k = Nat.nth Nat.Prime (B+k)`.
If a scanned prime already occurs among previous helpers, take an empty block;
otherwise use the paid mandatory block. Initial core contains all primes below
`r_0`. Then every smaller prime remains processed, and `pi(r_k)=B+k+1`
makes the consumption invariant immediate. This is the same exhaustion proof
with explicit skipped stages, avoiding a separate least-missing-prime recursion.
All nonempty blocks still pay their mandatory prime and helpers against the
inherited pre-block state. Strictly increasing proportional clocks remain.

Exact constants: choose the corpus positive window `b >= 8`, amplitude
`c > 0`, and put `a = min(c,1/40)`, `C = 448*(b+1)`. Choose `n >= 1`
with `abs(H(C*n)) <= n*a*sqrt(n)` and set `A=C*n`, `D=2*n`.
Positive helpers lie in `(64*b*n*r,64*(b+1)*n*r]`; negative helpers lie
in `(224*(b+1)*n*r,336*(b+1)*n*r]`. Each has the required sign and
magnitude at least `a*sqrt(n*r)`. Both windows eventually contain at least
`4*n*pi(r)` primes. The inherited core has at most `2*n*pi(r)` elements,
leaving at least `n` fresh helpers of each sign. At most `n+1 <= D` primes
enter each nonempty block.

The mandatory singleton identity is exact:
`singleton(A*r,r) = -sqrt(r)*H(A)`. Helper child cores are fully processed
because their primes exceed `r > A+1`. Signed supply is consequently
independent of every preceding helper choice and of the receiving head.

Formalization: scalar paid block and fixed source/count capacity compiled.
Signed supply, inherited extension, and exhaustive history are being checked
leaf by leaf. No capstone verification claimed yet.
