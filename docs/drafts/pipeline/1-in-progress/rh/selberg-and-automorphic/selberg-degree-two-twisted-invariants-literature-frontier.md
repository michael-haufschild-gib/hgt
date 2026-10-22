# Degree-two Dirichlet twists: published invariant frontier

- **ID:** `selberg-degree-two-twisted-invariants-literature-frontier`
- **Status:** Stage 1 — published proof dependency extraction in progress
- **Novelty:** `[LITERATURE]`
- **Primary source:** J. Kaczorowski and A. Perelli, *On the invariants of L-functions of degree 2,
  I: twisted degree and internal shift*, arXiv:2405.03186 (2024)
- **Role:** exact literature frontier to formalize before resuming novel attacks on Selberg
  Conjecture 3

## Exact published theorem

Let `F ∈ S♯` have degree `d_F=2`, integer conductor `q_F`, and internal shift `θ_F`. Let `D` be a
positive squarefree integer such that `D ≡ 1 (mod q_F)`. Assume:

1. `F` splits polynomially at every prime dividing `D`;
2. `F` is saturated modulo `D`;
3. for every Dirichlet character `χ` modulo `D`, the coefficient twist by the primitive character
   `χ*` inducing `χ` belongs to `S♯` and has degree `d_{χ*}` and internal shift `θ_{χ*}`.

Then, for every `χ` modulo `D`,

`d_{χ*}=2` and `θ_{χ*}=θ_F`.

This is the exact theorem at arXiv:2405.03186, lines 61–62 of the HTML edition. No assumption may be
discarded or hidden in an abstract proposition.

## Exact definitions consumed

- `S♯`: nonzero Dirichlet series, absolutely convergent on `Re(s)>1`, with meromorphic
  continuation of finite order and a Selberg-type functional equation.
- `degree`: `2 ∑_j λ_j`.
- `conductor`: `(2π)^{d_F} Q² ∏_j λ_j^(2λ_j)`.
- `internal shift`: `(2/d_F) Im(∑_j μ_j)`.
- `F` saturated modulo `D`: for every integer `M` and every reduced residue class `a mod D`, some
  positive integer `ν` satisfies `ν ≡ a mod D`, `(ν,M)=1`, and `a_F(ν) ≠ 0`.
- polynomial splitting at `p`: the inverse local factor is a nonzero polynomial in `p^{-s}`.
- primitive character `χ*`: the unique primitive character inducing `χ`, with conductor `f_χ`.

## Published dependency DAG

1. Exact `S♯` carrier, gamma data, degree, conductor, internal shift.
2. Dirichlet-series absolute convergence and uniqueness; coefficientwise Dirichlet twist.
3. Primitive-character conductor/induction and Gauss sums.
4. Finite Fourier expansion for a principal-character additive phase (paper Lemma 1;
   Montgomery–Vaughan, Theorem 9.12).
5. Polynomial local-factor deletion and coefficient identity (paper Lemma 2).
6. Inductive additive/nonlinear-twist decomposition into primitive character twists (paper
   Lemma 3).
7. Kaczorowski–Perelli degree classifications: degree zero is a Dirichlet polynomial; no degrees
   in `(0,1)` or `(1,2)`; exact degree-one classification in `S♯`.
8. Lindelöf `μ`-function law for `S♯` and invariance under finite-prime depletion.
9. Standard/nonlinear twist theory from *Twists and resonance of L-functions I–II*, including
   continuation, polar locus, residue formula, dual-twist transformation, and growth bounds.
10. Saturation plus linear independence of Dirichlet characters.
11. Main contradiction proving degree and internal-shift invariance.

Every item must be implemented as concrete definitions and kernel-checked theorems. Quoting an item
as a field, axiom, opaque declaration, `Prop` interface, `sorry`, or hypothesis does not count.

## Current verified foundation

`RHTower.DirichletCharacterTwist` proves, for Mathlib arithmetic functions and Dirichlet
characters:

- exact twist composition;
- exact compatibility with Dirichlet convolution;
- inverse twist equals principal-character level depletion;
- coprime coefficients survive and non-coprime coefficients vanish.

This closes one algebraic prerequisite only. It does not yet formalize the published theorem.

`RHTower.SelbergClass.TwistFrontierData` now gives concrete Lean predicates for polynomial local
splitting, saturation modulo `D`, exact coefficient twisting, and integer conductor of the current
gamma presentation.  The polynomial-splitting predicate is the analytic identity
`F_|p(s) = (\sum_j A_j p^{-js}) F(s)` on `Re(s)>1`, with nonzero leading coefficient; it does not
replace this identity by an abstract closure hypothesis.

## Completion gates

- [x] Exact theorem frozen against primary source
- [x] Published proof read end-to-end
- [x] Dependency DAG extracted
- [x] First coefficient-twist algebra layer paper-proved
- [x] First coefficient-twist algebra layer Lean-audited and promoted
- [x] Exact polynomial-splitting, saturation, coefficient-twist, and integer-conductor predicates
- [ ] Exact `S♯` carrier and invariants (carrier exists; gamma-presentation invariance remains)
- [ ] Lemma 1 (Fourier inversion and primitive Gauss case formalized; imprimitive
  conductor/Möbius factor remains)
- [ ] Lemma 2
- [ ] Lemma 3
- [ ] Degree-gap/classification dependencies
- [ ] Lindelöf-function dependencies
- [ ] Nonlinear-twist I–II dependencies
- [ ] Main theorem paper dependency closure independently audited
- [ ] Exact main theorem in Lean
