# Prime Sonin quadratic corners are matrix-injective modulo compacts

- **ID:** sonin-prime-quadratic-calkin-matrix-injectivity
- **Stage:** 1-in-progress
- **Type:** THEOREM / QUADRATIC OBSTRUCTION
- **Date:** 2026-07-10
- **Status banner:** `[CONJECTURE]` The shell proof below survives the paper attack. Lean realization
  and an independent operator-theory/Sonin literature audit remain open.
- **Parents:**
  `../2-fully-proven/new_scientific_knowledge/sonin-two-scale-quadratic-corner-noncompact.md`;
  `../2-fully-proven/new_scientific_knowledge/sonin-finite-calkin-l2-lower-bound.md`

## Claim

Fix `a>0` and distinct primes `p_1,...,p_n`. On the even Sonin carrier let

`L_i=(1-Q_a)(U_(p_i)+U_(p_i)^(-1))Q_a`.

For `A in M_n(C)` define

`G_A=sum_(i,j) A_(ij)L_i^*L_j`.

Then

`G_A compact  iff  A=0`.                                  (1)

More quantitatively, for every compact `K`:

- if `i!=j`, then `|A_(ij)|<=||G_A-K||`;
- for every `k`,

  `|sum_(i:p_i>=p_k) A_(ii)|<=||G_A-K||`.                 (2)

The functionals in (2) separate every matrix: the off-diagonal entries are read directly, and a
maximal-prime nonzero diagonal entry is its own tail sum.

## Constraint-side mechanism

Choose one narrow interior shell `J={c<|x|<d}` with `0<c<d<a`. It is chosen close enough to the
physical boundary and narrow enough that:

1. every inverse prime dilate `U_(1/p_k)J` lies outside `[-a,a]`;
2. if `p_j<p_k`, then the ratio shell `U_(p_j/p_k)J` also lies outside `[-a,a]`;
3. all distinct inward ratio shells

   `U_(p_j/p_k)J`, with `p_j>=p_k`,

   are pairwise disjoint.

Such a shell exists because only finitely many strict inequalities are imposed. Let `v_m` be an
orthonormal even sequence in `J`, put

`g_(k,m)=U_(1/p_k)v_m`, `f_(k,m)=Q_ag_(k,m)`.

The bounded-shell Sonin correction gives `||f_(k,m)-g_(k,m)||->0`; hence every `f_(k,m)` is bounded
and weakly null. For each pair `(j,k)`, the outward branch

`U_(1/(p_jp_k))v_m`

is asymptotically killed by `1-Q_a`. The remaining branch gives

`L_jf_(k,m) -> 0` if `p_j<p_k`,

`L_jf_(k,m) -> U_(p_j/p_k)v_m` if `p_j>=p_k`.              (3)

## Prime-ratio rigidity

Pair `G_A f_(k,m)` against `f_(l,m)`. By (3) and shell orthogonality, a coefficient `A_(ij)` survives
exactly when

`p_j/p_k=p_i/p_l`, equivalently `p_jp_l=p_ip_k`,

and both ratios are at least one. Unique factorization gives:

- for `k!=l`, the only surviving pair is `(i,j)=(l,k)`, so

  `<G_A f_(k,m),f_(l,m)> -> A_(lk)`;

- for `k=l`, the surviving pairs are `i=j` with `p_i>=p_k`, so

  `<G_A f_(k,m),f_(k,m)> -> sum_(i:p_i>=p_k) A_(ii)`.

Every compact `K` sends each fixed `f_(k,m)` sequence to zero in norm. Since `||f_(k,m)||<=1`, the
operator-norm inequality and the two limits give (2), hence (1).

## Attack

- `[SURVIVES]` Pairwise noncompactness alone would not prove (1). The new ingredient is the full
  asymptotic compression table (3) plus prime-ratio rigidity.
- `[SURVIVES]` Equal scale ratios would create contaminating matrix coefficients. Distinct primes
  remove every off-diagonal collision by unique factorization; the remaining diagonal collisions
  form an invertible tail transform.
- `[SURVIVES]` The theorem covers arbitrary complex matrices, including trace-zero, skew-adjoint,
  and indefinite combinations. Positivity is not used.
- `[SURVIVES]` The proof uses the fixed physical/Fourier constraint. Dilation only labels which
  pieces cross it; no carrier is propagated by a flow.
- `[PARENT-THEORY WARNING]` Once (3) is known, the finite-dimensional matrix argument is elementary.
  Scientific content, if any, is the actual-Sonin realization of the ratio-poset compression and
  the arithmetic removal of all nontrivial ratio collisions.
- `[OPEN CORE]` Build the shell selector and (3) in Lean, then discharge the ratio-rigidity interface
  for literal prime families rather than leaving it as a hypothesis.

## Novelty and significance

- **Novelty:** `[NOVELTY UNVERIFIED]` Preliminary searches found the Connes--Consani quasi-inner
  and semilocal Sonin constructions and general Toeplitz/Hankel product theory, but no theorem that
  finite prime-indexed actual-Sonin Gram corners are matrix-injective in the Calkin quotient.
- **Significance:** The result closes the matrix-level quadratic cancellation left open by the
  two-scale theorem. No finite signed quadratic counterterm built from canonical prime Sonin corners
  can enter the compact ideal. Any viable repair must be genuinely infinite, nonlinear, smoothed,
  or use a different polarization.

## Gates

- [x] 0 -> 1: exact matrix theorem and ratio-poset mechanism isolated
- [ ] 1 -> 2: complete paper proof with every shell inequality written explicitly
- [ ] 2 -> 3: Lean formalization and concrete positive-Euler/source transport
- [ ] 3 -> 4: independent primary-literature and expert priority audit
