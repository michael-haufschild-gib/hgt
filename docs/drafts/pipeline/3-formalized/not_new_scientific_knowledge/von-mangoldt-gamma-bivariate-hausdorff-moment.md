# Von Mangoldt--Gamma bivariate Hausdorff moment reconstruction

- **ID:** `von-mangoldt-gamma-bivariate-hausdorff-moment`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (Lean), SOURCE-SIDE MOMENT/GRAM PRODUCER
- **Scientific status:** `[PROVED] [LEAN-VERIFIED] [BRIDGE] [NOT AN RH PROOF]`
- **Parent:** `finite-von-mangoldt-gamma-full-jet-orientation.md`
- **Child:** `von-mangoldt-gamma-pointed-ward-bianchi-gram.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/VonMangoldtGammaBivariateMoment.lean`,
  `formal/GaloisForLFunctions/RHTower/VonMangoldtGammaBivariateGram.lean`

## Theorem

For a finite positive exponential source with weights `q_p`, rates `lambda_p>0`, and real base
coordinate `x`, define one source-determined positive kernel on the finite source set times the
unit interval:

```text
d nu_x(p,u)
  =q_p exp(-x lambda_p) exp(-lambda_p(1-u)) du,
  0<u<=1.                                                   (1)
```

Its bivariate moments are

```text
B_x(a,b)
  =sum_p integral_[0,1]
      lambda_p^a u^b d nu_x(p,u).                          (2)
```

Let `A_N(i)` be coordinate `i` of the depth-`N` finite Gamma-descent anomaly.  Reversing the jet
index by `i=N-1-r`, Taylor's integral remainder gives the exact identity

```text
r! (-1)^(N+1) Re A_N(N-1-r)=B_x(N,r),
0<=r<N.                                                     (3)
```

Thus every finite Gamma-anomaly jet is a triangular observable slice of one fixed bivariate
moment array.  The depth does not select an unrelated measure: increasing `N` only takes the next
moment in the same source-rate variable `lambda`.

For every fixed rate degree `a`, the row `b |-> B_x(a,b)` has the canonical positive Hausdorff
representing measure

```text
d mu_(x,a)(u)
  =sum_p q_p exp(-x lambda_p) lambda_p^a
      exp(-lambda_p(1-u)) du.                              (4)
```

Consequently every finite Hankel matrix

```text
(B_x(a,i+j))_(0<=i,j<n)                                   (5)
```

is positive semidefinite, for every `a` and every finite size `n`.  Equations `(1)--(5)` are
formalized for arbitrary finite positive exponential sources and specialized to the actual finite
von Mangoldt source `q_p=Lambda(p+2)/(p+2)`, `lambda_p=log(p+2)`.

More strongly, choose arbitrary rate and remainder exponents `a_i,b_i`.  The full mixed matrix

```text
G_ij=B_x(a_i+a_j,b_i+b_j)                                 (6)
```

is positive semidefinite.  It is the Gram matrix of the bivariate monomials
`(lambda,u) |-> lambda^(a_i)u^(b_i)` in `L^2(nu_x)`.  If
`b_i+b_j<a_i+a_j`, then `(3)` identifies every entry of `(6)` with a factorially normalized,
reverse-indexed Gamma-anomaly coordinate, even when the entries come from different anomaly
depths.  Thus the formal theorem is one all-depth bivariate Gram, not a family of unrelated
one-depth positivity statements.

## What this closes

The former source theorem placed the finite anomaly jet in one open orthant.  The present theorem
upgrades that coordinatewise statement to a canonical moment geometry:

1. exact integral reconstruction of every oriented Taylor remainder;
2. one fixed bivariate source kernel across all Gamma depths;
3. exact reconstruction of every reversed finite anomaly coordinate from mixed moments;
4. canonical positive representing measures for all rows;
5. unconditional Hankel positive semidefiniteness at every row and every finite size;
6. unconditional mixed Gram positivity across arbitrary Gamma depths and remainder degrees.

The positivity is source-effective: it is built directly from the von Mangoldt weights and Gamma
clock, without assuming RH, Weil positivity, a zero distribution, or target Hankel positivity.

## Novelty gate

The two ingredients are classical.  Taylor's integral remainder supplies `(3)`, and the Hausdorff
moment theorem makes a positive measure on `[0,1]` produce a completely monotone sequence and
positive Hankel forms.  Liu--Pego describe the standard equivalence between Hausdorff moment
sequences and positive measures on `[0,1]`:

- https://arxiv.org/abs/1401.8052

The literature on exponential Taylor remainders also treats their integral representations and
inequalities:

- https://arxiv.org/abs/1608.08784

No exact occurrence of `(3)` for the finite von Mangoldt--Gamma clock anomaly was found in the
targeted literature search.  That exact source dictionary is useful to this corpus, but it is not
claimed as new scientific knowledge: the proof is a project-specific composition of classical
Taylor-remainder and moment facts.  Significance can only arise from a non-circular completed
source/Xi comparison.

## RH boundary

The theorem proves positivity before the critical completion.  This distinction is decisive.
Every positive exponential source has `(1)--(6)`, regardless of any analogue of a zero-locus
statement, so the moment cone alone cannot distinguish the Riemann source.

The repository already proves exact analytic identities from the completed moving source and the
inverse-tilted prime--Gamma source to the normalized prime--Gamma moment germ, and from that germ to
the Xi central reciprocal moments.  Therefore the missing theorem is not another source/Xi value
identity.  It is a positivity-preserving comparison between the positive bivariate anomaly Gram
and that already reconstructed completed moment germ.  Inverse de-Poissonization is expansive, and
polar subtraction is sign-sensitive; neither operation is a positive pushforward of `(1)` merely
because the pre-completion measure is positive.

The exact remaining chain is

```text
fixed bivariate von Mangoldt--Gamma moment measure
  -> all finite anomaly coordinates + all mixed bivariate Gram cones
  -> pointed Ward reconstruction + positive mixed Bianchi environment
  -> order-growing two-boundary positive source packet
  -> existing completed source/Xi analytic value identities
  -> [OPEN] positive compression/Schur-complement identity through inverse tilt and polar completion
  -> completed Xi/Weil positivity
  -> RH.                                                    (7)
```

A valid next theorem must exhibit the completed moment functional as a positive compression or
shorted operator of the same source measure.  Merely defining a target measure from the desired
completed moments is circular, and merely observing another source Gram does not advance `(7)`.

## Lean certificate

Principal declarations:

- `expNegOrientedRemainder_eq_unitIntervalIntegral`
- `finiteExponentialGammaAnomaly_reverse_eq_bivariateMoment`
- `finiteVonMangoldtGammaAnomaly_reverse_eq_bivariateMoment`
- `finiteExponentialGammaBivariateMoment_eq_integral`
- `finiteExponentialGammaBivariateMoment_hankel_posSemidef`
- `finiteVonMangoldtGammaBivariateMoment_hankel_posSemidef`
- `exponentialRemainderBivariateGramAtom_posSemidef`
- `finiteExponentialGammaBivariateGram_posSemidef`
- `finiteVonMangoldtGammaBivariateGram_posSemidef`
- `finiteVonMangoldtGammaAnomalyMixedGram_eq_bivariateGram`
- `finiteVonMangoldtGammaAnomalyMixedGram_posSemidef`

Verification:

- exact module build passed;
- theorem-file direct check passed;
- axiom audit: `propext`, `Classical.choice`, `Quot.sound` only;
- no numerical computation;
- repository lint still reports unrelated concurrently unimported modules, but reports no
  reachability or forbidden-declaration defect for this module.

## Gates

- [x] exact Taylor integral remainder
- [x] fixed bivariate source kernel
- [x] exact anomaly/mixed-moment reconstruction
- [x] canonical Hausdorff representing measure
- [x] all-size row Hankel positive semidefiniteness
- [x] arbitrary mixed bivariate Gram positive semidefiniteness
- [x] exact all-depth normalized anomaly Gram reconstruction
- [x] actual finite von Mangoldt specialization
- [x] unconditional Lean formalization
- [x] exact module build and axiom audit
- [x] anti-theatre and literature novelty gate
- [x] completed source/Xi analytic value identities (existing modules)
- [ ] positive compression/Schur-complement identity from the bivariate source Gram
- [ ] positive critical completion
- [ ] Xi/Weil positivity
- [ ] RH
