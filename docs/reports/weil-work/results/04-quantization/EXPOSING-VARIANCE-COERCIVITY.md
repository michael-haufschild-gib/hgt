# C31 — variance controls the exposing deficit (OPEN)

Cycle31, 2026-10-08. Verdict: **SURVIVES PRELIMINARY ATTACK**.
New conjecture; no paper proof or Lean assertion.
Independent scientific novelty is not established.

Given the exact internal and external frontier, what would a Fields
Medal-winning mathematician conjecture? Replace the failed coefficient
reconstruction from finite marginal residues by a quantitative comparison
of two actual source invariants.

Fix the corpus normalization F=riemannKernelAutocorr. For every specified
hW : WeilPositiveFull lambda, let beta=sourceCompletion hW 1 and let V be
the unique nonnegative centered logarithmic coefficient variance. Define

    L(lambda) = -atomPairing (lambda-Lambda) F.

The existing exposed-point theorem gives L>=0 and L=0 only for lambda=Lambda
on n>=2. The source producer gives beta!=0 and finite V. No new hypothesis
is needed for these definitions or facts.

**C31.** There is a real constant C>0, depending only on the fixed kernel F,
such that for every lambda and every specified hW,

    |beta|^2 L(lambda)^2 <= C V.

The quantifier order is essential: one C must work for all sources. A
source-dependent C would add no quantitative content to C30 when V>0.
The conjecture imposes no multiplicativity, coefficient sign, sparse
support, finite mean on the physical boundary, or source tail premise.

If true, it gives C30 immediately and a quantitative lower variance cost
for nonzero exposing deficit. With T29 it would force a physical T log T
energy cost proportional to |beta|^2 L^2. It still would not establish
V=0 or exact interval quantization. If false, a counterexample must be an
actual full-positive source; a sequence with |beta|^2 L^2/V unbounded
would refute uniform C31 without necessarily refuting C30.

## Initial attack

The corpus's quantitative exposedness theorem
`sq_atomPairing_riemannKernel_le` bounds mixed kernel moments by L times a
Weil test energy. It does not bound L by coefficient variance. Reversing
that implication would be an error. The exact statement and its cutoff
argument were inspected.

The source Toeplitz test gives a log-moment inequality for the actual
forward coefficients. Substituting centered coefficients brings back the
forcing term beta*(lambda-Lambda) in the logarithmic convolution. The
existing proof does not make that term zero. Moreover V=0 provides no
decay rate for the normalized truncation error; a form estimate growing
with the truncation cannot be passed to zero merely from this limit.

[OPEN CORE] Construct a uniformly bounded comparison between the actual
exposing deficit and the centered coefficient variance, paying the
forcing term and the cutoff error from hW itself. This is the proposed
new structural estimate, not a premise of a formal receiver.

The current primary operator-theoretic parents were rechecked.
[Suzuki's 2026 screw-function paper](https://arxiv.org/html/2606.09096v1)
constructs localized operators for the fixed von Mangoldt Weil form and
keeps its proposed global spectral limit conjectural. Its initial source
is not an arbitrary full-positive lambda with the variance above.
[Connes--Consani--Moscovici](https://arxiv.org/html/2310.18423v2), section4.7,
proves semilocal Sonin-space stability using specified Euler factors.
That structure has not been produced for arbitrary hW. Neither result
supplies the missing source comparison. Exact web queries also returned
unverified numerical/reformulation claims, which were not used as lemmas.

The exact deep corpus attack completed (`partial=false`, 68,902 inventoried
files; mixed compiler freshness, semantic coverage unmeasured). Every
candidate and source-argument row was inspected. The proposed ingredients
do not establish C31: `abs_atomPairing_le` requires both Lambda+w and
Lambda-w to be full-positive, while `eq_zero_of_perturbedKernel_bound`
requires the very absolute kernel estimate that needs production. The
critical-zero-carried alternative has an additional spectral-support
premise. None may be silently supplied by V=0. Full metadata and rows
are retained in cycle31-search-evidence.json. Survival of these checks
is not a proof or an originality claim.
