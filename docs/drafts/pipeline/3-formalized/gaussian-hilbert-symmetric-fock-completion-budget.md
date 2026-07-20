# Symmetric-Fock completion-budget phase law

- **ID:** gaussian-hilbert-symmetric-fock-completion-budget
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / CANDIDATE NEW COMBINED LAW
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Source:** `gaussian-hilbert-ambient-completion-budget.md`
- **Statement:** canonical bosonic lowering charge and transverse variance obey a sharp universal
  rank budget, with exact phase threshold `4e < (e - 3)M`.

## Goal

Separate two costs that had previously been conflated in the Gaussian Hilbert counterexample:

1. the lowering charge forced by an actual symmetric-Fock subspace on `e` active modes;
2. the ambient Hilbert dimension needed to supply independent transverse variance channels.

The resulting theorem must apply to every real top subspace and every transverse rank, not only
to monomial tops, the full symmetric power, or equal singular values.

## The universal law

Let `U_n subset Sym^n(E)` be finite-dimensional real subspaces for `0 <= n <= M`, with

\[
 \partial U_{n+1}\subseteq U_n,
\]

where `partial` is the span of all canonical bosonic annihilations.  Put

\[
 e=\dim E,\qquad k=\dim U_M,\qquad
 B=\sum_{n<M}n\dim U_n.
\]

Let `r<=k` be the rank of a transverse completion and let `p_1,...,p_r` be its singular-channel
parameters.  The associated determinant-line mean-minus-variance margin is

\[
 F=B+(k-r)M+\sum_{j=1}^r
 \left(-\frac{M(M-4)}4+
 \left((M-1)p_j-\frac{M-2}{2}\right)^2\right).
\]

Then

\[
 \boxed{\quad
 k\left(M(M-1)-(e+1)\frac{M(M-4)}4\right)
 \le (e+1)F.\quad}                                      \tag{U}
\]

The rank-sensitive form is stronger:

\[
 M(M-1)k+(e+1)\left((k-r)M-r\frac{M(M-4)}4\right)
 \le(e+1)F.                                               \tag{R}
\]

Consequently, if `M>0` and `F<0`, then

\[
 \boxed{\quad4k(M+e)<(e+1)rM.\quad}                      \tag{C}
\]

Thus every negative phase pays an explicit ambient-completion budget.  Combining `r<=k` with
(C) forces

\[
 \boxed{\quad4e<(e-3)M.\quad}                            \tag{P}
\]

The full symmetric top with full-rank balanced completion attains (U), and its margin is negative
exactly under (P).  Hence (P) is the sharp stability/instability threshold for the entire
single-top transverse class.

## Dependency-closed proof

For the normalized annihilators

\[
 a_i:\operatorname{Sym}^{n+1}(E)\longrightarrow\operatorname{Sym}^{n}(E),
\]

the canonical commutation relations give

\[
 \sum_i\lVert a_i x\rVert^2=(n+1)\lVert x\rVert^2,
 \qquad
 \sum_i\lVert a_i^*y\rVert^2=(n+e)\lVert y\rVert^2.      \tag{1}
\]

For any `V subset Sym^{n+1}(E)`, Parseval in `partial V`, adjointness, and Bessel in `V` imply

\[
 (n+1)\dim V\le(n+e)\dim(\partial V).                    \tag{2}
\]

Apply (2) to `U_{n+1}` and use `partial U_{n+1} subset U_n`.  Multiplying the degree-`n`
inequality by `n` and summing gives the exact telescoping identity

\[
 \sum_{n<M}n\bigl((n+e)h_n-(n+1)h_{n+1}\bigr)
 =(e+1)B-M(M-1)k,                                        \tag{3}
\]

so

\[
 M(M-1)k\le(e+1)B.                                      \tag{4}
\]

Completing the square independently in every transverse channel yields (R).  Since

\[
 (k-r)M+(k-r)\frac{M(M-4)}4=(k-r)\frac{M^2}{4}\ge0,
\]

(R) implies (U).  If `F<0`, multiplying the left side of (R) by four factors it as

\[
 M\bigl(4k(M+e)-(e+1)rM\bigr),
\]

which proves (C).  Finally `r<=k` gives (P).  Every dependency is explicit; there is no
Macaulay, generic-position, numerical, or spectral-asymptotic assumption.

## Lean declarations

In `GaloisForLFunctions.HilbertMetric.SymmetricFockShadow`:

- `symmetricFockAnnihilation_energy`
- `symmetricFockAnnihilation_adjoint_energy`
- `tightOperatorFamily_subspace_finrank`
- `symmetricFockLoweringShadow_finrank`
- `weightedFockShadow_telescope`
- `weightedFockShadowCharge_lower_bound`
- `gradedFockLoweringCharge_lower_bound`

In `GaloisForLFunctions.HilbertMetric.SymmetricFockPhase`:

- `gradedFockTransverseFanoMargin_rank_bound`
- `gradedFockTransverseFanoMargin_universal_bound`
- `gradedFockTransverse_negative_forces_rank_budget`
- `gradedFockTransverse_negative_forces_phase`
- `gradedFockTransverseFanoMargin_nonnegative_of_phase`
- `threeMode_gradedFockTransverseFanoMargin_nonnegative`
- `fullTopTransverse_phase_at_balance_lt_zero_iff`
- `singleTopFock_phase_threshold_rewrite`

## Novelty and anti-theatre boundary

The bosonic number/creation identities, Parseval, Bessel, Hilbert functions, and Bernoulli square
completion are parent mathematics.  No novelty is claimed for (1), the derivative-shadow
inequality (2), or their standard commutative-algebra interpretations.

There is also an operator-scaling parent for (2).  The Kraus map
`X |-> sum_i a_i X a_i*`, after rescaling its two scalar marginals, is a rectangular analogue of
a doubly stochastic completely positive map.  Gurvits's rank-nondecreasing criterion and its
specified-marginal extensions place the dimension-expansion phenomenon inside established
operator scaling.  The direct Parseval/Bessel proof is retained because it is exact over the real
Fock levels used here, but it is not presented as a new operator theorem.

The candidate new contribution is the exact organization of those parents into the sharp
curvature law (U), the rank-sensitive law (R), and the ambient completion obstruction (C), tied to
the Gaussian determinant-line curvature mechanism.  Searches across symmetric-Fock operators,
partial-derivative spaces, Hilbert functions, Fano-factor inequalities, Gaussian RBF flat limits,
and bandwidth log-determinant curvature found no matching combined theorem.  Search noncollision
is not priority evidence, so the novelty label remains unverified pending expert review.

Additional parent source: C. Franks, *Operator scaling with specified marginals*,
arXiv:1801.01412, especially the completely positive marginal setup and the rank-nondecreasing
criterion inherited from Gurvits.

This theorem alone does **not** prove concavity for every Gaussian configuration in ambient
dimension three: `e` counts active base modes, while the `r` transverse directions live in an
additional completion space.  Nor does it classify arbitrary multilevel annihilation-invariant
subspaces.  Claiming either would fail the anti-theatre test.

## Publication gate

The theorem is mathematically paper-worthy as a sharp finite-Hilbert/Fock extremal law.  It does
not yet clear the stated general-scientific-journal bar.  That bar requires at least one of:

1. a theorem converting (C) into a sharp ambient-dimension law for all finite Gaussian distance
   matrices;
2. a classification of arbitrary multilevel annihilation-invariant spaces that preserves the
   same phase boundary;
3. a broadly useful consequence in kernel learning, determinantal geometry, or bosonic quantum
   statistics that is not confined to the single-top normal form.

## Verification log

- 2026-07-20 -- both new modules passed direct `lake env lean` checks.
- 2026-07-20 -- `#print axioms` for every headline theorem reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- 2026-07-20 -- final `lake build GaloisForLFunctions.HilbertMetric` completed all 2541 targets;
  the only message was a pre-existing tactic suggestion in `DegreeFiveGaussianCurvature.lean`.
