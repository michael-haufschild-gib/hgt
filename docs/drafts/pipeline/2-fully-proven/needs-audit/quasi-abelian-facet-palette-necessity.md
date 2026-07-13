# Every full HT relation geometry carries a faithful quasi-Abelian facet palette

- **ID:** `quasi-abelian-facet-palette-necessity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / NECESSARY HT PERIOD GEOMETRY
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Statement:** Every meromorphic realization of a finite full Stanley--Reisner HT differential
  matroid canonically assigns to each facet a noncompact quasi-Abelian period quotient satisfying
  the generalized Riemann relations, with exact complement incidence and an injective integral
  facet translation lattice. Consequently `qaDim(Delta)<=htDim(Delta)`.

## Setup

Let `Delta` be a finite simplicial complex on an essential finite vertex set `V`. Let

```text
a_v in C^d,  v in V,                                       (1)
```

be linearly independent over `Q`, and let `T_v` translate meromorphic functions on `C^d` by
`a_v`. Fix a constant directional derivation `delta`. Put

```text
D=C(z_1,...,z_d),
S=C[delta],
R=S[t_v^(+-1):v in V],
x_v=t_v-1,
I_Delta=(x_N:N is a minimal nonface of Delta).              (2)
```

Assume a scalar meromorphic function `F` realizes the exact full localized Stanley--Reisner
differential matroid:

```text
Ann_R(F)=I_Delta,                                           (3)
```

and for every finite family `P_1,...,P_m in R`,

```text
dtrdeg_D D<P_1(T)F,...,P_m(T)F>_delta
 =dim_(C(delta)) span{Pbar_1,...,Pbar_m}                    (4)
```

in `C(delta) tensor_S(R/I_Delta)`.

## Quasi-Abelian facet-palette theorem `[PROVED HERE]`

For every facet `A` there is a closed additive subgroup `P_A subset C^d` with the following
properties.

1. `E_A=P_A^0` is a complex-linear subspace.
2. `Gamma_A=P_A/E_A` is discrete in `W_A=C^d/E_A`.
3. The quotient `X_A=W_A/Gamma_A` is noncompact.
4. Vertex incidence is exact: `a_v in P_A` if and only if `v notin A`.
5. The integral facet lattice map

   ```text
   Z^A -> X_A,
   n   |-> sum_(v in A)n_v a_v mod P_A                      (5)
   ```

   is injective.
6. There is a positive-definite Hermitian form `H_A` on `W_A` such that

   ```text
   Im H_A(Gamma_A,Gamma_A) subset Z.                        (6)
   ```

Thus every facet quotient is a noncompact quasi-Abelian group satisfying the generalized Riemann
relations, and its surviving structural translation group is a faithful free Abelian subgroup.

## Proof

### 1. Isolate one facet

For every other facet `B!=A`, choose a vertex `b_B in A\B` and set

```text
q_A=product_(B!=A)x_(b_B).                                 (7)
```

The localized facet-prime decomposition is

```text
I_Delta=intersection_(B in Fac(Delta))(x_v:v notin B).      (8)
```

Every factor of `q_A` lies in `A`, so `q_A` is outside the `A`-prime. For every `B!=A`, its
selected factor lies outside `B`, so `q_A` belongs to the `B`-prime. Therefore

```text
q_A notin I_Delta,
x_v q_A in I_Delta  iff  v notin A.                         (9)
```

Define the facet carrier

```text
G_A=q_A(T)F.                                               (10)
```

Equation (4) for the singleton `q_A` makes `G_A` differentially transcendental. Equations
(3) and (9) give

```text
T_vG_A=G_A iff v notin A.                                 (11)
```

### 2. The complete integral facet orbit is free

For `n in Z^A`, let `t^n` be the corresponding Laurent monomial. If `n_1,...,n_r` are distinct,
the quotient classes

```text
t^(n_i) q_A mod I_Delta                                   (12)
```

are linearly independent over `S`. Indeed, restrict to the `A`-facet quotient. The image of
`q_A` is nonzero, the facet Laurent polynomial ring is a domain, and the distinct Laurent
monomials `t^(n_i)` are linearly independent over `S`. Hence a relation among (12) has all
coefficients zero.

After tensoring with `C(delta)`, the classes remain independent. Equation (4) therefore proves
that every finite distinct family

```text
T^(n_1)G_A,...,T^(n_r)G_A                                 (13)
```

is differentially algebraically independent over `D`.

### 3. Take the full period quotient

Set

```text
P_A=Per(G_A)={h in C^d:G_A(z+h)=G_A(z)}.                  (14)
```

This is closed. Its identity component is complex-linear: tangent period directions annihilate
`G_A`, and holomorphy makes the annihilating tangent space stable under multiplication by `i`.
Thus `E_A=P_A^0` is complex-linear and `Gamma_A=P_A/E_A` is discrete in `W_A=C^d/E_A`, proving
properties 1--2.

Because `G_A` is differentially transcendental, the noncompact period-quotient theorem applies and
proves property 3. Equation (11) proves property 4.

If a nonzero `n in Z^A` mapped to zero in (5), then its translation vector would belong to `P_A`
and `T^nG_A=G_A`. But (13) applied to `0,n` says these two functions are differentially
algebraically independent, impossible for equal functions. Therefore (5) is injective and
property 5 holds.

### 4. Generalized Riemann relations are forced

The function `G_A` descends through `E_A` to a `Gamma_A`-periodic meromorphic function `g_A` on
`W_A`. Since `P_A` was the full period group, `g_A` has no period outside `Gamma_A`; it is
nondegenerate in periodic meromorphic-function theory.

The main theorem of Capocasa--Catanese states that a discrete subgroup `Gamma subset W` is the
period group of a nondegenerate meromorphic function exactly when it satisfies the generalized
Riemann relations. Applying its necessary direction to `g_A` gives a positive-definite Hermitian
form `H_A` with integral imaginary part on `Gamma_A`, which is property 6. `QED`

## Dimension consequence `[PROVED HERE]`

Define `qaDim(Delta)` as the least `d` admitting globally `Q`-independent translation vectors and
facet groups satisfying properties 1--6. The theorem extracts exactly such data from every
`d`-dimensional full HT realization. Therefore

```text
qaDim(Delta)<=htDim(Delta).                                (15)
```

Every quasi-Abelian palette is a period-escape separation after forgetting properties 5--6, and
every periodic pencil is the quasi-Abelian cylinder `C/Z`. Together with the existing realization
theorems,

```text
peDim(Delta)<=qaDim(Delta)<=htDim(Delta)
                              <=ppDim(Delta)<=ffsDim(Delta).               (16)
```

The unresolved converse `htDim<=qaDim` is exactly the quasi-Abelian full-orbit theorem on the
companion in-progress card. It is not assumed here.

## Positive law and RH-facing consequence

The former statement "noncompactness is not enough" becomes:

> **Quasi-Abelian facet law.** Every facet of a finite full HT relation geometry carries a
> noncompact quasi-Abelian period quotient satisfying a positive Hermitian integrality law, and the
> whole integral structural lattice of that facet embeds in the quotient.

Thus a finite RH-facing HT carrier must supply more than escape directions. Its facet periods must
admit compatible positive Hermitian forms with integral imaginary parts, while the prime/Euler
translation lattice remains faithful. Any functional-equation sewing must act on these
quasi-Abelian palettes and preserve their arithmetic Hermitian data. This is a necessary carrier
law, not an assertion that zeta already supplies such a finite relation complex.

## Parent-theory and novelty boundary

The generalized Riemann relation is `[SEARCH]`: F. Capocasa and F. Catanese, *Periodic meromorphic
functions*, Acta Math. **166** (1991), 27--68, DOI `10.1007/BF02398883`. The paper proves the
existence criterion for one nondegenerate periodic meromorphic function. Closed period groups,
Remmert--Morimoto decomposition, and the facet-prime decomposition are also parent inputs.

The theorem proved here attaches those quotient geometries simultaneously and canonically to the
facet separators of a full nonlinear HT differential matroid, proves exact vertex incidence and
faithfulness of every integral facet lattice, and derives the dimension inequality (15).
Scientific novelty remains unverified pending searches in periodic meromorphic functions,
quasi-Abelian varieties, difference algebra, toric arrangements, and differential algebraic
matroids.

## Exact Lean boundary

The finite Stanley--Reisner facet separator, Laurent-monomial independence, and transfer from row
independence to differential independence are supported by the existing formal HTGeometry modules.
`HTGeometry.jetPoleFingerprint_injective` also formalizes the finite valuation fingerprint proposed
for the converse full-orbit construction.
The analytic theorem surface is not formalized: closed complex period groups, quotient complex Lie
groups, noncompactness of the quotient, Hermitian forms, and the Capocasa--Catanese generalized
Riemann relation are absent. This card cannot move to Stage 3 until those inputs and the assembled
theorem are formalized unconditionally.

Formalization audit (needs-audit pass): the combinatorial framework is confirmed present
(`HTGeometry.jetPoleFingerprint_injective`, plus the finite Stanley--Reisner / Laurent-monomial
support cited above). No bounded self-contained kernel survives removal of the analytic surface: the
load-bearing steps (properties 3, 6 and the dimension bound) all route through the Capocasa--Catanese
generalized-Riemann-relation criterion and complex-Lie period quotients, neither of which mathlib
provides. Building that criterion is a research-scale development; no partial file is added.

## Gates

- [x] facet carrier isolated without an atomic decomposition
- [x] exact complement-period incidence proved
- [x] complete integral facet orbit proved differentially free
- [x] faithful lattice injection into the full period quotient proved
- [x] noncompactness inherited from differential transcendence
- [x] generalized Riemann relations forced by the nondegenerate quotient carrier
- [x] dimension hierarchy sharpened by `qaDim`
- [x] positive RH-facing carrier law stated
- [x] complete paper proof
- [ ] independent specialist proof and novelty audit
- [ ] complete unconditional Lean formalization before Stage 3
