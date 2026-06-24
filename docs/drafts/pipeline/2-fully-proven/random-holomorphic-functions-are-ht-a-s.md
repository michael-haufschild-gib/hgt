# Random holomorphic functions with nondegenerate finite jets are HT almost surely

- **ID:** random-holomorphic-functions-are-ht-a-s
- **Stage:** 2-fully-proven
- **Type:** THEOREM / MEASURE-THEORETIC HT LARGENESS
- **Source:** C24, C22 support-count proof, Haiku 2026-06-24
- **Priority:** HIGH as a nature-of-HT theorem; novelty still needs external audit

## Statement

Let `Omega subset C` be a connected domain. Let `F` be an `O(Omega)`-valued random holomorphic function such
that for every finite list of distinct points `z_1,...,z_r in Omega` and every jet order `m >= 0`, the joint
finite-jet vector

```text
J_{z,m}(F) = (F^(j)(z_i))_{1 <= i <= r, 0 <= j <= m}
```

has an absolutely continuous law with respect to Lebesgue measure on `C^{r(m+1)}`.

Then

```text
Pr(F is hypertranscendental over C(z)) = 1.
```

In particular, the standard planar Gaussian entire function

```text
F(z)=sum_{n>=0} xi_n z^n / sqrt(n!)
```

with independent standard complex Gaussian coefficients is hypertranscendental over `C(z)` almost surely.

## Promptability audit

No computation is involved. A random sample path cannot certify HT, because every finite observation vector has
DA and HT realizers. The proof uses a structural bit outside any finite transcript:

1. every ADE over `C(z)` has a finite expanded differential-monomial support;
2. there are only countably many such finite supports;
3. for each support, algebraic dependence forces one nonzero finite-jet determinant to vanish;
4. the finite-jet law has a density, so that determinant vanishes with probability zero.

This theorem is therefore not numerical evidence. It is a probability-one exclusion of all finite ADE supports.

## Proof

After clearing denominators, any algebraic differential equation over `C(z)` has the form

```text
sum_{alpha,k} c_{alpha,k} z^k prod_{j=0}^m (Y_j)^{alpha_j} = 0,
```

with finitely many terms and complex coefficients. Thus the possible equations are indexed by countably many
finite supports of expanded differential monomials

```text
M(z,Y_0,...,Y_m)=z^k prod_{j=0}^m Y_j^{alpha_j}.
```

Fix one finite support `S={M_1,...,M_s}`. Let `E_S` be the event that the analytic functions

```text
M_l(z, F(z), F'(z), ..., F^(m)(z)),    1 <= l <= s,
```

are linearly dependent over `C`.

The monomials `M_1,...,M_s` are linearly independent as holomorphic functions on
`Omega x C^{m+1}`. Hence there exist distinct points `a_1,...,a_s in Omega` such that the determinant

```text
Delta((v_{i,j})) =
det( M_l(a_i, v_{i,0}, ..., v_{i,m}) )_{1 <= i,l <= s}
```

is not the zero polynomial in the finite jet variables `v_{i,j}`. This is the standard evaluation lemma for
linearly independent holomorphic functions: choose evaluation points inductively so the evaluation matrix gains
rank at each step; distinct base points may be kept by avoiding the finite set already chosen.

If `E_S` occurs, then all such evaluation determinants vanish, so in particular

```text
Delta(J_{a,m}(F))=0.
```

By hypothesis `J_{a,m}(F)` has an absolutely continuous law, and the zero set of a nonzero polynomial has
Lebesgue measure zero. Therefore

```text
Pr(E_S)=0.
```

There are only countably many finite supports `S`, so the probability that any nonzero ADE over `C(z)` holds is
zero. Therefore `F` satisfies no ADE over `C(z)` almost surely, i.e. it is HT over `C(z)` almost surely. ∎

## Gaussian entire example

For the planar Gaussian entire function

```text
F(z)=sum_{n>=0} xi_n z^n / sqrt(n!),
```

every finite jet vector is a nondegenerate complex Gaussian vector. Indeed, a linear relation among finitely many
derivative evaluations would have variance zero only if the corresponding finite linear combination of kernel
derivatives

```text
partial_{\bar w}^j exp(z bar(w)) |_{w=a_i}
```

were the zero entire function. These are exponential-polynomial functions attached to distinct exponents
`bar(a_i)` and are linearly independent. Thus every finite jet covariance matrix is nonsingular, so the theorem
applies.

## Consequences

1. **Measure-one HT.** HT is not merely Baire-generic in holomorphic function spaces; it is probability-one for
   any random holomorphic law with nondegenerate finite jets.
2. **Finite handles are null events.** Each fixed differential-monomial support defines a finite-jet determinant
   obstruction, hence a probability-zero event.
3. **Randomness does not certify a sample path.** A sampled finite transcript still cannot prove HT. The theorem
   proves HT by quantifying over all finite ADE supports before sampling.
4. **Constraint-not-flow interpretation.** A random analytic function almost surely has no finite
   algebraic-differential rule; finite generative handles are exceptional constraints, not typical structure.

## Source and novelty boundary

Known ingredients:

- Gaussian analytic functions and their finite-jet nondegeneracy are standard; see the Hough--Krishnapur--Peres--
  Virag Gaussian analytic functions text for the general GAF setup.
- The support-count and Baire analogue are already recorded in `ht-c22-topological-largeness.md`.
- Van den Dries 1995 proves a nearby meagreness theorem for traces of differentially algebraic entire functions,
  so broad genericity of DA failure is source-adjacent.

Targeted searches for exact phrases such as `"Gaussian analytic function" "differentially algebraic"`,
`"Gaussian analytic functions" hypertranscendental`, `"random entire function" "differentially algebraic"
almost surely`, and `"random analytic function" "differentially algebraic"` did not surface this almost-sure
HT theorem. This is weak negative evidence only.

Verdict: proof is complete; novelty/significance is plausible but not yet certified. Treat as **PROVED /
AUDIT-NEEDED** until another agent checks whether the random-holomorphic almost-sure statement is already in the
Rubel, Malgrange, van den Dries, or Gaussian-analytic-function literature.

## Gates

- [x] 0 -> 1 in-progress: theorem stated with exact finite-jet nondegeneracy hypothesis.
- [x] 1 -> 2 fully-proven: finite-support proof written; Gaussian entire example verified.
- [ ] 2 -> 3 formalized: possible as an abstract probability/linear-algebra theorem, with DA support-count
  imported.
- [ ] 3 -> 4 publication-ready: requires source audit and examples beyond the planar GEF.

## Log

- 2026-06-24 - Promoted from `ht-c24-random-series-as-escape` by Haiku as a standalone theorem. The proof is not
  computational; it converts the finite-support nature of ADEs plus nondegenerate finite-jet laws into
  probability-one HT.

## 2026-06-24 additional source-search note

Additional targeted searches for van den Dries/Rubel/Malgrange variants found van den Dries,
*Parametrizing the solutions of an analytic differential equation*, Illinois J. Math. 39 (1995), 450--462, via
Project Euclid and bibliographic listings. Search snippets mention differentially algebraic entire functions and
interpolation traces, matching the already-recorded source-adjacent risk from C22.

The same search pass did not find an exact random-holomorphic or Gaussian-analytic-function theorem stating
almost-sure hypertranscendence/differential transcendence over `C(z)`. This remains weak negative evidence only:
the source risk is still the Rubel/Malgrange parametrization tradition, and a proper audit must inspect the van den
Dries paper and adjacent citations rather than relying on search snippets.

## 2026-06-24 coefficient-series examples

The finite-jet absolute-continuity hypothesis is not special to Gaussian laws.

Let

```text
F(z)=sum_{n>=0} xi_n c_n z^n
```

be a random power series on a disk of positive radius, with every `c_n != 0`, and suppose the coefficients
`xi_n` are independent complex random variables with absolutely continuous laws. Assume the series converges
almost surely and defines a holomorphic function on the disk. Then every finite jet vector of `F` has an
absolutely continuous law.

Proof. Fix distinct points and a maximum jet order. Let `N` be the number of requested jet coordinates, counted
with multiplicity. The map from polynomials of degree `<N` to those finite jets is an isomorphism by Hermite
interpolation. Since `c_0,...,c_{N-1}` are nonzero, the contribution of `(xi_0,...,xi_{N-1})` to the jet vector is
an invertible linear image of an absolutely continuous random vector. The remaining tail is independent; adding
an independent random vector preserves absolute continuity by convolution. ∎

Thus the theorem applies to any such nondegenerate random Taylor series on its disk of convergence, not only to
Gaussian analytic functions.

## 2026-06-24 source-risk distinction: meagre trace is not null event

The van den Dries/Malgrange/Rubel source risk remains serious, but the theorem here is not a formal consequence
of a meagreness statement alone. A meagre subset of a sequence or function space can have probability one under a
singular probability law. The present theorem uses a different hypothesis: absolute continuity of every finite-jet
law, which turns each finite differential-monomial support into a null event through a nonzero polynomial
determinant.

Thus the delta, if any, is the finite-dimensional absolute-continuity mechanism:

```text
finite ADE support -> nonzero finite-jet determinant -> null event -> countable union.
```

If a source already proves this for random Taylor series or Gaussian analytic functions, this card should be
regraded as source-known. If the available sources prove only Baire/meagreness or interpolation-trace statements,
then this card remains a measure-theoretic companion theorem rather than a direct duplicate.

## 2026-06-24 team audit downgrade -- correct but folklore/bridge

Turing audited the theorem after a cold prior-art probe and agreed with proof correctness under the joint
finite-jet absolute-continuity hypothesis. The novelty grade is downgraded to **FOLKLORE / BRIDGE**, not new
project-completing knowledge. The reason is mathematical, not just bibliographic: once the finite-support
normal form for ADEs is exposed, the proof is the standard countable-union-of-null-sets argument.

Citation hygiene correction: the suggested source `math/0412354`, *Differentially Transcendental Functions*, was
opened and searched for `meager`, `Baire`, `random`, and `generic`; no matches were found. It should be cited for
DA-field background and examples, not as evidence for a Baire/meagreness theorem. The actual topological twin
source remains `van den Dries 1995` / Rubel-Malgrange-adjacent until inspected more fully.

Disposition: keep this file in `2-fully-proven` as a correct measure-theoretic largeness lemma. Do not use it to
claim the active goal is complete. It belongs with finite-observation and genericity guardrails unless a later
source audit finds a sharper, consequence-bearing delta.
