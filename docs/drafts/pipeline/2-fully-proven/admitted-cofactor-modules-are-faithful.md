# Admitted cofactor modules are faithful

- **ID:** admitted-cofactor-modules-are-faithful
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Parent:** [Q-III](../1-in-progress/q-iii-escape-state-classification.md)
- **Statement:** Every actual common cofactor limit at an admitted damping has faithful Wiener action and full annihilator hull. Consequently a nonfaithful actual limit forces receiver escape.

## Dependency-closed proof

Let A be the actual centered receiver, E_T its pronic energy, and pi the
representation of any actual common cofactor limit. Its first cell A(1) is
nonzero, already forced by the proved positivity E_1>0.

For a complex critical Wiener coefficient row a, set
`P_a(n)=sum_(j<=n) a_j A(floor(n/j))`. This is a finite sum at every cell.
Two applications of dominated convergence, with majorant
`|a_j| |a_k| /sqrt(j*k)`, give along the chosen common subsequence

`sum_(n<=T) |P_a(n)|²/[n(n+1)E_T] -> ||pi(a)v_1||²`.

No escape assumption enters this limit. If a annihilates the module, its
right side is zero. On admission E_T<=C uniformly, so the unnormalized
nonnegative sum also tends to zero. Every fixed nonnegative cell lies below
this sum at all sufficiently large horizons. Therefore P_a(n)=0 for every n.

Induction now recovers a=0. Its coefficient at zero is zero by the arithmetic
function convention. If coefficients below n vanish, the finite expression
P_a(n) contains only the term a_n A(1). Since A(1)!=0, a_n=0. Thus ker(pi)=0.
The Bohr hull of the zero ideal is the full polydisk. Contraposition, combined
with the proved admission-or-divergence dichotomy, gives the escape conclusion
for every actual nonfaithful module.

## Consequences and scope

The common normalized Gram construction exists on both admitted and escaping
branches. Its nonzero Hilbert module alone cannot certify escape. On admission
the paid ideal is the whole Wiener algebra, whereas the module annihilator is
zero; this explains why paid-ideal annihilation is expressly an
admission-or-annihilation theorem.

Faithfulness also makes the admitted Hilbert module infinite-dimensional:
otherwise its operator algebra would be finite-dimensional, while the Wiener
algebra contains arbitrarily many independent point masses. The closed
annihilator quotient is then the Wiener algebra itself, of continuum Hamel
rank. This does not assert admission at any particular subcritical damping.
Conversely, any finite-dimensional actual cofactor module forces source escape:
the admitted branch is already infinite-dimensional, and the existing energy
dichotomy supplies divergence when admission fails. This implication does not
assert that a finite-dimensional actual module exists.

Uniqueness of the admitted Gram kernel is a separate positive consequence:
global source-square summability and Cauchy–Schwarz make every fixed covariance
absolutely convergent; E_T has a positive finite limit. Thus every common
subsequence has the same normalized global kernel. This argument does not
identify the kernel with an escape state or with a zero-counting module.

## Lean status

Universal actual Hilbert/Wiener realization, first-horizon positivity, and
admission-or-escape are checked inputs. Double Wiener covariance convergence
and its exact finite-cell pairing identity passed with standard axioms and
are in `CompleteWienerPairingsFollowTheCommonCofactorLimit.lean`.
Faithfulness, full hull, and the contrapositive escape theorem passed with
standard axioms and are in `AdmittedCofactorModulesAreFaithful.lean`.
Both final source checks passed. The further dimension and uniqueness
drafts are queued for their first check; those consequences remain unverified.

## Gates

- [x] Dependency-closed paper argument.
- [x] Full source pairing identity and convergence.
- [x] Actual faithfulness and full-hull dichotomy.
- [ ] Dimension, uniqueness, source checks, and axiom audits.

### Full-horizon uniqueness and source-cell promotion

The draft proof of `kernel_eq_of_admits` passed with standard axioms in the
unit/finite batch. It is now promoted to
`ADR/TheAdmittedCofactorKernelIsUnique.lean`; leaf source check remains queued.
The separately verified coefficient evaluation and exact full-source floor
reindexing are promoted to `AOT/WienerCoefficientEvaluation.lean` and
`ADR/CompleteWienerSourceRowsRespectDilation.lean`. Their final leaf checks and
required oleans remain queued. Umbrella imports are added without building
umbrellas. The new finite-module-implies-escape corollary still awaits the
corrected draft check.
