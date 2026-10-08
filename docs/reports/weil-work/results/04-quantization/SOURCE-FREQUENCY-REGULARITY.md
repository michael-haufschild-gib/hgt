# P23: frequency regularity of the actual phase

Status: CONJECTURE, SURVIVES PRELIMINARY ATTACK. No paper proof or Lean theorem.
P22, this stronger source assertion, and full WP04 remain OPEN. No independent
novelty claim is made.

## Exact conjecture

Given the exact internal and external frontier, what would a Fields
Medal-winning mathematician conjecture? The source resonance row loses a
square root of logarithmic bandwidth. Test whether the actual phase has
frequency regularity that pays this loss, rather than postulating a bounded
operator on unweighted B².

For every `hW : WeilPositiveFull lam`, let W(t)=quantizationCirclePhase hW t.
There exist a real s>1/2, an injective sequence ω:ℕ→ℝ and p:ℕ→ℂ such that

    Σ_j |p_j|² (1+|ω_j|)^(2s) < ∞,

and, writing P_N(t)=Σ_{j<N}p_j exp(iω_jt),

    ∀δ>0 ∃N₀ ∀N≥N₀ ∃T₀≥1 ∀T≥T₀,
        (1/T)∫₀ᵀ |W(t)−P_N(t)|² dt < δ.

Zero coefficients allow finite spectra. All integral and limit conventions are
literal positive-time Lebesgue averages. This states membership in the
frequency-weighted B² completion; it asserts neither uniform convergence nor
pointwise boundary equality. No periodicity or representation is a premise.

The incompatible world is an actual hW whose phase either has a continuous
translation-spectral component or has a pure-point spectrum with divergent
displayed moment for every s>1/2. P23 would isolate arithmetic regularity that
generic positive measures do not have. Its failure would say that smoothing
the physical boundary requires more than a fixed Fourier Hilbert topology.

## Immediate attacks and remaining obligations

1. T23 defeats s=0 bounded resonance duality, not P23. Its test polynomials are
   not asserted to be approximation errors of an actual source phase. They must
   not be substituted for W itself.
2. The chirp diagnostic in SOURCE-MEAN-COMPACTNESS.md fails even P22; it is not a
   full-positive integer-arithmetic source. Positivity and local variation alone
   therefore cannot prove P23.
3. Existing exponentially weighted representation receivers are stronger
   premises than this mean-square assertion. They do not produce p,ω from hW.
4. The source-only regularization theorem
   `exists_integral_regularizedPhase_sub_le_inv` bounds the dyadic L¹ error of
   the actual canonical phase by C/Y at width Y⁻⁸. Its source proof and
   definitions were inspected. The smoothing width varies with the averaging
   interval; it supplies no fixed global Fourier approximants or uniform
   frequency moment. Even a finite-interval approximation theorem would not
   exchange these quantifiers. The canonical phase also includes central mass,
   so any transfer to W must retain its exact normalization and argument scaling.
5. The [Defant–Schoolmann survey](https://www.impan.pl/shop/en/publication/transaction/download/product/113364),
   Sections 1 and 4.8, distinguishes coefficient spaces on compact Dirichlet
   groups and their almost-everywhere Fourier convergence. Membership of this
   physical source phase in the stated weighted completion remains unpaid.
   It cannot be supplied by changing the boundary orbit to a Haar-generic one.
6. Even P23 would not by itself identify the weighted Hilbert residue pairing
   with the actual radial contour limit. That identification is a second
   obligation. T23 concerns the normalized residue row, and no universal
   nonzero main-kernel limit is silently assumed.
7. L4 closes periodic frequency lattices. It does not close every countable
   spectrum; general L remains open. Even successful contour identification
   would still require a general residue-rigidity argument or a source-produced
   restriction of the spectrum. P23 is a structural source conjecture, not an
   already-complete alternative proof of WP04.
8. The inspected source theorem `source_rigidity_or_canonical_phase_disorder`
   forces nonrigid phases to have arbitrarily late dyadic deviation at least
   aY exp(−K log Y/log log Y) from every fixed phase. That lower bound divided
   by Y tends to zero. Thus even a constant B² class could hide a source
   remainder too large for the available rigidity receiver. Weighted Fourier
   moments alone do not control that B²-null remainder. Its actual contour
   contribution must be retained rather than discarded by the quotient.

[OPEN CORE] Derive p,ω and a finite moment of order greater than one from the
original hW arithmetic identity, with the displayed order of quantifiers.
First attack the actual regularization identity's frequency tail. A proposed
bound must survive η↓0 and T→∞ jointly. No P23 Lean should be written before a
dependency-closed paper proof.

An exact necessary test avoids guessing a representation. For h>0 set

    D(h) = limsup_{T→∞} (1/T)∫₀ᵀ |W(t+h)−W(t)|² dt.

P23 would imply D(h)=O(h^(2 min(s,1))) as h↓0, hence D(h)/h→0.
Indeed translations are isometries in the positive-time B² seminorm for these
bounded functions; finite-frequency orthogonality and approximation give
D(h)=Σ_j |p_j|²|exp(iω_jh)−1|². The bound
|exp(iu)−1|≤min(2,|u|) and the stated frequency moment give the claim.
On the actual source, the integrand is exactly

    2 − 2 cos(2π(C(t+h)−C(t))),  C=quantizationResidualCumulative hW.

Thus the first source attack can target this literal interval-phase observable.
The displayed implication is classical Fourier analysis, not a new theorem or
a proved estimate for hW. P22 alone supplies no rate in h, and the dyadic
regularization theorem supplies no uniform bound for D(h)/h.

## Search evidence

Cycle23's exact source-weighted search was complete as a retrieval request
(partial=false, no unfinished stages), with 68,767 inventoried files. Compiler
coverage was predominantly pending/source-only and refresh used the background
indexer. Candidates, source arguments, proof ideas and ingredient sets were
inspected and saved in cycle23-search-evidence.json. The suggested inertia-kernel
and matched-moment pairing concerns different objects and has no verified bridge
to W; it is not evidence for P23. Retrieval does not establish exhaustive absence.

The follow-up interval-phase search also completed (68,772 files). It returned
the actual source disorder theorem and the same regularization estimate, not a
small-shift bound for W. Its proposed lattice-phase/cosine ingredients concern
linear test characters, not this nonlinear cumulative measure phase. Results
also contain the newly written T23 source file; that self-hit is not independent
support or prior art. All four query records are retained.
