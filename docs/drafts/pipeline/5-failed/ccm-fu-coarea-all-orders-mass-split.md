# CCM-FU: the coarea envelope fails along every complete prime order

- Type: derived obstruction and exact replacement comparison.
- Status: dependency-closed paper proof below; Lean verification in progress.
- Chain: actual divisor source → exhaustive prime processing with an O(M²)
  retained-energy ceiling → O(M) Abel bound → CCM-FU → RH.
- This obstruction concerns the coarea majorant, not raw retained energy or RH.
- Frontier map remains read only.

## Exact obstruction [PROVED HERE]

Write F_R for actual signed fibre mass, A_R for original absolute fibre
mass, f=F_empty, a=A_empty, and K=Σ_nonempty F_R²/A_R, with zero-mass
terms zero. The head action is H=f²+aK. The proposed envelope
B=(max_R A_R) Σ_R F_R²/A_R satisfies B≥H.

Let L be active primes p with M/2<p<M, b_p=|C_p|, T=Σ_L b_p. At state
P, let t=Σ_(L∩P)b_p and r=Σ_(L\P)b_p. Then t+r=T. Every processed
late prime contributes its original absolute mass to the empty fibre,
so a≥t. Every unprocessed late prime is an isolated singleton with
conditional energy C_p²/|C_p|=b_p, so K≥r. Consequently

    H(P) ≥ t(P) r(P) = t(P) (T-t(P)).

Along a chain that inserts one index at a time, starting with no late
prime processed and ending with all of them processed, t starts at zero
and ends at T. Each increment is between zero and D=(3/5)sqrt(M), by
the actual uniform channel ceiling. At the first crossing of T/2, the
two adjacent values bracket T/2 and differ by at most D. One is within
D/2 of T/2. Hence some prefix satisfies

    H(P) ≥ (T²-D²)/4.

The existing unconditional source theorem T(4N)/(4N)→∞ implies that
for every fixed C, every complete order at all sufficiently large N
has a prefix H>C(4N)². This permits arbitrary small/middle-prime
interleaving and an arbitrary number of late blocks. Since B≥H,
no selection rule can give the proposed O(M²) coarea-envelope ceiling.
No numerical experiment is needed: the result follows from exact mass
accounting and the corpus source-growth theorem.

## Positive survivor: preserve the late diagonal [PROVED HERE]

Let E_late=Σ_(L\P)b_p² and K_mixed=K-r. The latter is exactly the
conditional energy of nonempty cells other than active late singleton
cells, hence nonnegative. Replace H by

    H_corrected = H-a r+E_late
                = f²+a K_mixed+E_late.

If every mixed cell has absolute mass at most a, then raw Q≤H_corrected.
The comparison no longer requires head dominance over late singleton
cells. It removes precisely the artificial common-mass cost on those
cells while preserving their exact squared energy. The original
diagonal bounds E_late at O(M²).

For a fresh late prime of mass b, f'=f-b, a'=a+b, K_mixed'=K_mixed,
and E_late'=E_late-b². Therefore

    H_corrected'-H_corrected = b (K_mixed-2f).

For a fresh late block of total mass u and square reserve R=Σ b²,

    H_corrected(P union block)-H_corrected(P)
      = u (K_mixed(P)-2f(P)) + u²-R.

This retains the receiving-head square and diagonal credit. It does
not assert a uniform bound for the corrected action. That bound still
requires quantitative control of the mixed-prime fibres and head.

## No-go closure

- Killing mechanism: unavoidable product of consumed and remaining late
  absolute mass, even with arbitrary interleaving.
- Strongest positive survivor: exact late-diagonal correction, a raw
  energy majorant under mixed-cell dominance, and its exact block law.
- New insight: the old envelope creates a superquadratic comparison
  cost independently of actual signed cancellation. A viable proof must
  retain cell-specific late energy rather than multiply it by head mass.
- Lean status: in progress. No unproved selection premise is discharged.

## Corpus audit

Broad OR searches used the repository research tool with explicit
`--any`: coarea barrier, mass split, consumed mass, late prime,
comparison loss; bounded jump, prefix mass, half mass, threshold
crossing, split mass. Existing late-prime interleaving capacity rules
out a fixed number of raw-energy late blocks. The present obstruction
allows arbitrarily many blocks and concerns the different coarea
majorant. Existing raw-energy block laws retain the receiving square;
the corrected conditional-energy comparison above must do the same.
