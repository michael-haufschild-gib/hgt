# Coprime chronological words vanish over complete arithmetic periods

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); complete-period nonzero-invariant realization excluded
- **Source:** `EulerDeletionCoprimeCrossCompletion.lean`, full-index corpus research, and `rg` inspection of its Chinese remainder proof.
- **Result:** All nonempty unweighted chronological words with positive pairwise-coprime labels vanish at complete periods, including independently shifted labels. Every prefix has an exact finite residue description.

## Exact source and theorem

Write `a_p(n)=1-p[p divides n]`. Use reverse chronological lists:

`S_empty(N)=1`,

`S_(p::w)(N)=sum_(0<=n<N) a_p(n+1) S_w(n)`.

Thus the first stored letter is the latest in time, and all earlier factors occur at strictly earlier integers. If all labels in `w` are positive and pairwise coprime, set `P=prod(w)`. Lean proves

`S_w(N+P)=S_w(N)` and `S_w(N)=S_w(N mod P)`.

For every nonempty such word and every natural `k`, `S_w(kP)=0`. Each letter may independently be replaced by `a_p(n+r_p+1)` for an arbitrary natural phase `r_p`; periodicity and complete-period vanishing still hold. The modulus-one zero channel is allowed.

## Stronger generic theorem and paper proof

The induction works over every commutative ring, for arbitrary zero-mean periodic source functions `x_i`, with positive pairwise-coprime periods `d_i` along the word. It is therefore a residue-independence mechanism, not an extra property supplied by a zeta zero.

1. For positive coprime `p,q`, Chinese remaindering identifies the integers in `[0,pq)` with the pairs of residues modulo `p` and `q`. Therefore any `p`-periodic `f` and `q`-periodic `g` satisfy
   `sum_(n<pq) f(n)g(n) = (sum_(n<p) f(n))(sum_(n<q) g(n))`.
   This is proved by an explicit finite equivalence in Lean.
2. If an increment `h` is `d`-periodic and sums to zero over `[0,d)`, its primitive `H(N)=sum_(n<N)h(n)` is `d`-periodic: split the first `d` terms from `H(N+d)` and use periodicity on the rest.
3. The empty chronological word is constant one, with period one. Suppose the earlier word has period `Q`, the product of its labels' periods. The new letter has period `p`, coprime to `Q`. Step 1 makes its product with the earlier prefix have zero mean over `pQ`, regardless of the mean of that prefix. Step 2 makes the new prefix periodic. This proves the all-depth generic theorem by induction.
4. Every nonempty prefix equals zero at cutoff zero. Periodicity consequently gives zero at every multiple of the period and recovers every other cutoff from its residue.
5. A deletion coefficient has zero mean: among the residues modulo `p`, exactly one contributes `1-p` and the other `p-1` contribute one. Shifting a periodic zero-mean source preserves its complete-period sum, by splitting its periodic primitive at the shift. Apply step 3 to the separately shifted deletion letters.

Every dependency here is finite algebra or integer divisibility. No numerical experiment, Dirichlet weight, zero assumption, analytic continuation, or open mathematical input enters.

## Boundary and positive survivor

- **Excluded realization:** a nonzero observable obtained solely from complete-period unweighted chronological words whose labels are pairwise coprime. More word depth and separate changes of phase do not rescue it.
- **Positive survivor:** exact all-depth reconstruction of each chronological prefix from one finite period; the stronger theorem classifies arbitrary zero-mean periodic sources with independent residue periods.
- **Limits:** the theorem does not assert that Dirichlet-weighted words vanish. It does not cover labels sharing a prime factor, repeated nontrivial labels, or cylinder letters whose prime supports overlap. It does not retire all factorization-graded descent proposals. A common multiple, not necessarily the minimal period, is sufficient for the result.
- **Consequence for the current candidate:** unweighted complete-period observations on disjoint prime supports cannot supply its desired nonzero class. Weighted within-period variation or overlapping supports would need a separate construction and proof. No such producer is supplied here.

The generic strict iterated-sum object is already published in Diehl–Ebrahimi-Fard–Tapia, [*Iterated-sums signature, quasi-symmetric functions and time series analysis*](https://diehlj.github.io/FPSAC2020.pdf), equation (1.4). The present proof specializes finite Chinese remainder factorization. The bounded search found no exact matching theorem; that does not establish novelty or absence from literature.

The bounded corpus queries for this and the reconstruction audit are preserved in [the search manifest](euler-deletion-reconstruction-periodicity-searches.tsv). Its limits are requested retrieval caps, not audited declaration counts. Exact `rg` checks supplied the source proof inspection.

## Lean evidence

Module: `formal/GaloisForLFunctions/RHTower/EulerDeletionCoprimeWordPeriodicity.lean`, namespace `RHTower.DeletionCoprimeWords`.

- `coprime_period_sum_mul`: complete-period factorization for arbitrary periodic functions.
- `sourceWordPrefix_periodic`: generic all-depth periodic-source induction.
- `wordPrefix_periodic`, `wordPrefix_eq_residue`: actual deletion prefix classification.
- `wordPrefix_complete_period_zero`: all nonempty complete-period words vanish.
- `shiftedWordPrefix_complete_period_zero`: vanishing survives independent phase choices.

Scratch compilation, the targeted leaf build, and an imported audit of all six listed capstones passed. The leaf is wired into `RHTower.lean`; no umbrella or full build ran. Every audited capstone reports only `propext`, `Classical.choice`, and `Quot.sound`. Repository-wide `scripts/formal_tools.py lint` passed with existing large-file warnings. All owned Lean/Lake processes terminated. RH and a qualifying novel architecture remain unproved.
