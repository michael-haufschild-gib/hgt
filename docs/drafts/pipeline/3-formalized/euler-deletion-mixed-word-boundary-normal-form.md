# Mixed arithmetic words: absolute boundary normal form

Status: formalized; no RH-producing annihilation law.

## Frozen question

Can passing from two chronological indices to three create a new conditional
regrouping anomaly at a hypothetical right-half zeta zero? Test the actual
mixed-modulus source at every finite depth, not just one modulus's word history.

Corpus inputs: `EulerDeletionCoprimeWordPeriodicity.sourceWordPrefix` gives the
generic strict-word convention; `EulerDeletionQuasiShuffleSecondConvergence`
gives literal zero-endpoint Abel decay; `EulerDeletionChronologicalScheduleBoundary`
gives the doubled-abscissa row majorant. Search checked mixed/joint development,
word convergence, tail boundaries, and conditional triple grouping before conjecturing.
The existing operator word history handles one modulus; no inspected theorem gives
the following mixed-word normal form.

## Conjecture and paper proof

Write `H_w(N)` for strict chronological words, latest letter first, and
`S_j(N)=sum_(n<N) x_j(n)`. Finite summation by parts gives

`H_(j,i,w)(N) = S_j(N) H_(i,w)(N)
              - sum_(n<N) S_j(n+1) x_i(n) H_w(n)`.

If all single-letter prefixes tend to zero with bound `A_j(N+1)^(-sigma)`
and jumps have bound `B_i(n+1)^(-sigma)`, `sigma>1/2`, induction on word length
shows every `H_w` converges. Indeed the shorter prefixes are bounded; the displayed
carry is absolutely summable by `(n+1)^(-2sigma)`, while the boundary product tends
to zero. Thus every word of length at least two has an exact absolutely summable
last-letter formula. At depth three this is precisely a middle-index grouping
using the closed last-letter tail.

Apply to any labelled collection of literal deletion moduli and independently
conjugated letters at one hypothetical right-half zeta zero. No pointwise repeated-
generator cancellation, coprimality, unweighting, fitted quotient, or uniform-in-word
bound is assumed. Coefficients and chronological ordering remain literal.

## Proved consequence and limits

The natural depth-three middle regrouping cannot supply an anomaly if the exact
boundary term is retained. This does not classify arbitrary factorization-tree
regions or prove vanishing of higher words. It does not prove RH or supply the
missing independent arithmetic annihilation law. Summation by parts is classical;
the source normal form is not being claimed as a new convergence principle.

The statement covers arbitrary mixed labels, arbitrary finite lengths, and independent
complex conjugations. It does not provide a bound uniform over word length or growing
moduli. Repeated letters occur at distinct strict times; no pointwise repeated-generator
zero law is used. The empty word remains one, and only single-letter limits are forced
to zero. In particular, this theorem does not identify chronological composition with
the different multiplicative-label operation in `EulerDeletionFactorizationCurvature`.

The general ordered-series family is classical (Kelliher–Masri,
[equation (1.4)](https://math.ucr.edu/~kelliher/papers/LFunctionsFull.pdf)); no priority
claim is made for the integration-by-parts mechanism.

## Verification

Leaf: `formal/GaloisForLFunctions/RHTower/EulerDeletionMixedWordBoundary.lean`.
Namespace: `RHTower.DeletionMixedWords`.

- `word_boundary_identity`: exact finite endpoint/carry decomposition.
- `every_word_converges`: induction over the complete finite-word hierarchy.
- `source_every_word_converges`, `source_word_normal_form`: literal arithmetic instance.
- `source_triple_middle_form`: natural depth-three middle regrouping.

Scratch and published leaf passed without warnings. Seven imported capstone axiom audits
use only `propext`, `Classical.choice`, `Quot.sound`. A scratch compatibility proof checks
that the two-letter conjugated word is the existing Hermitian second prefix, fixing the
order convention. Global lint passed with existing large-file warnings. Olean built;
umbrella wired without a build. All owned processes finished before the interruption.
No numerical computation or RunPod job. RH remains unproved.
