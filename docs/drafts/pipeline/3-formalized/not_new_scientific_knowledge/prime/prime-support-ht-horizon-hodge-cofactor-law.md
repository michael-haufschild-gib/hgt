# Prime-support boundary jets are rooted HT-horizon Hodge cofactors

- **ID:** `prime-support-ht-horizon-hodge-cofactor-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / HT HORIZON HODGE BRIDGE
- **Scientific status:** `[PROVED HERE] [CLASSICAL MATRIX-TREE PARENT] [NOT AN RH PROOF]`
- **Parents:**
  - `../../1-in-progress/prime-support-boundary-jet-stability-rh.md`;
  - `../new_scientific_knowledge/projective-horizon-tits-building.md`;
  - `../new_scientific_knowledge/projective-horizon-solomon-tits-topological-charge.md`.
- **Successor:** `../squarefree-euler-modular-corona-curvature-colligation.md`.
- **Statement:** The positive prime-support deformation
  `M_n(t)=n(1-t)^(n-1)` is exactly the sum of the rooted Hodge cofactors of the weighted flag path
  obtained by coning a chamber of the projective HT horizon building.  This supplies a canonical
  source-positive metric for the full boundary-jet selector.  The same theorem proves that this
  chamber metric is phase-blind: every rank-one twist on the flag tree is gauge trivial.  The
  smallest phase-bearing positive successor is a twisted apartment cycle, whose holomorphic
  torsion is `1-Hol` and whose Hodge determinant is `|1-Hol|^2`.

## The source-marked flag path

Let `S={p_1<...<p_n}` be a nonempty prime support and let `V_S` have the ordered coordinate basis
`e_(p_1),...,e_(p_n)`.  The prefix flag

```text
<e_(p_1)> < <e_(p_1),e_(p_2)> < ... < V_S                 (1)
```

is the source ordering of one projective-horizon chamber, augmented by the full-source cone point
`V_S`.  Its incidence graph is the path `P_n` on `n` vertices.  Put the common edge conductance

```text
a=1-t                                                         (2)
```

and let

```text
L_n(t)=a d^*d                                                 (3)
```

be the weighted graph Laplacian of this path.  For `1<=r<=n`, write `L_n(t)^(r)` for the matrix
obtained by deleting the row and column of the root `r`.

## Rooted Hodge-cofactor theorem `[PROVED HERE]`

For every `n>=1`, every root `r`, and every scalar `t`,

```text
det L_n(t)^(r)=(1-t)^(n-1).                                 (4)
```

Consequently

```text
sum_(r=1)^n det L_n(t)^(r)
 =n(1-t)^(n-1)
 =M_n(t).                                                   (5)
```

For real `t<1`, `L_n(t)` is positive semidefinite, has radical exactly the constant line, and
every reduced rooted form is positive definite.  Thus `(5)` is a source-fixed positive Hodge
realization of the complete marked support deformation.

### Proof

The path `P_n` is already a tree.  The weighted matrix-tree theorem says that every principal
cofactor of its Laplacian is the sum of the weights of spanning trees rooted at the deleted
vertex.  There is one spanning tree, namely `P_n` itself, and it has `n-1` edges, all of weight
`1-t`.  This gives `(4)`.  Summing over the `n` roots gives `(5)`.  Positivity and the constant
radical are the standard identity

```text
<f,L_n(t)f>=(1-t) sum_(j=1)^(n-1)|f_(j+1)-f_j|^2.          (6)
```

`QED`

The boundary derivatives now have a geometric meaning.  The first nonzero normal derivative at
`t=1` occurs in order `n-1`, the number of chamber edges, and equals

```text
M_n^(n-1)(1)=n(-1)^(n-1)(n-1)!.                           (7)
```

Thus support-cardinality tomography is the rooted determinant of the complete flag path, not an
unstructured scalar cancellation.

## Exact phase-blindness theorem `[PROVED HERE]`

Give the oriented path edges arbitrary nonzero complex transports `u_1,...,u_(n-1)`.  The twisted
differential is

```text
(d_u f)_j=f_(j+1)-u_j f_j.                                (8)
```

Choose vertex gauges recursively by `g_1=1`, `g_(j+1)=u_j g_j`.  Then `(8)` is conjugate by the
diagonal gauge `g` to the untwisted path differential.  Hence every twisted rooted Hodge cofactor
depends only on the conductances and is independent of all `u_j`.

**No-go.**  A positive determinant pencil built only from one horizon chamber or its rooted flag
path cannot retain the prime Bohr phases, the continued divisor, or the anti-causal Ward column.
The phases are gauge on a tree.

**Positive HT statement.**  The marked prime-support jet has a canonical positive Hodge metric,
but phase and metric live in different topological layers.  The chamber carries the metric; a
nontrivial cycle is required to carry phase holonomy.

## The minimal phase-bearing successor `[PROVED HERE]`

Let `C_m` be an oriented cycle with positive edge conductances `c_j` and nonzero transports `u_j`.
Define

```text
(d_u f)_j=sqrt(c_j)(f_(j+1)-u_j f_j),
Hol(u)=product_j u_j.                                      (9)
```

Using cyclic indices, direct expansion of the two possible permutation terms gives

```text
det d_u = unit * sqrt(product_j c_j) * (1-Hol(u)),          (10)
det(d_u^*d_u)
 =product_j c_j * |1-Hol(u)|^2.                            (11)
```

Thus the holomorphic torsion `det d_u` retains the phase and the positive Hodge determinant is
its squared norm.  Twisted cohomology is nonzero exactly when `Hol(u)=1`.

An apartment in the type-`A_2` projective HT horizon building is a hexagonal cycle and therefore
already supplies such a phase carrier.  More generally, apartment top classes supply the
Steinberg cycles absent from a single chamber.  Equations `(10)`--`(11)` are the precise local
topological mechanism needed by a phase-sensitive Ward construction.

For a centered prime character `u_p(z)=exp(-i z log p)` and any nonempty positive exponent packet
`m_p`,

```text
Hol_m(z)=product_p u_p(z)^(m_p)=exp(-i z log N_m),
N_m=product_p p^(m_p)>1.                                  (12)
```

If `Hol_m(z)=1`, then its modulus gives

```text
exp(Im(z) log N_m)=1,
```

so `Im z=0`.  Every finite positive prime-apartment torsion therefore has its cohomology jumps on
the centered critical line.  This extends the independent prime Lee--Yang baseline from local
factors to arbitrary positive monomial holonomies.  It does not identify a cofinal torsion with
`Xi`.

## RH-facing consequence and exact remaining theorem

The squarefree Euler product on `Re s>1` has the finite torsion realization

```text
Z_(sq,P)(s)=product_(p in P)(1+p^(-s))                   (13)
```

by assigning one source apartment the holonomy `-p^(-s)` for each prime.  Every finite complex is
acyclic in the open critical strip.  Any nontrivial Xi divisor appearing after cofinal completion
must therefore be cohomology at the infinite HT corona, not finite-aperture cohomology.

The general HT capacity theorem supplies the correct metric invariant for such a corona class,
but does not identify its metric with the Hardy metric.  The RH-bearing theorem is now sharply
stated:

> **[CONJECTURE -- PRIME-APARTMENT QUILLEN--WARD DESCENT.]**  The Gamma-completed cofinal
> determinant line of the source apartments has a source Quillen/Hodge metric whose curvature is
> the proved squarefree Fisher-incidence curvature.  Its harmonic corona component is, under the
> Laplace boundary chart, exactly `P_anti Q_sq=ell_E`.  The Hodge energy identity is
>
> ```text
> 4=E_exact+||ell_E||_2^2,       E_exact>=0.              (14)
> ```

Equation `(14)` would prove the anti-causal Ward estimate and RH.  It is not a generic
colligation claim: the finite differential is `(9)`, the holomorphic determinant is `(13)`, the
metric is fixed by the rooted cofactors `(4)`, and the source curvature is the already proved
squarefree Fisher law.  The two remaining checks are the Gamma determinant anomaly and the strong
Hodge-corona-to-Hardy identification.

## Gates

- [x] prime-support deformation identified with rooted flag-path Hodge cofactors
- [x] positivity and radical computed
- [x] tree phase-blindness proved by explicit gauge
- [x] apartment-cycle torsion and Hodge determinant computed
- [x] positive prime monomial holonomy localized to the centered critical line
- [x] finite squarefree Euler product realized as source apartment torsion
- [x] every proved statement of this card formalized unconditionally in Lean 4
- [ ] construct the Gamma-completed cofinal determinant line (open research; not a proved theorem)
- [x] finite determinant-line/Fisher curvature identity proved in the successor card
- [ ] identify its harmonic corona class with `ell_E` in the Hardy metric (open research)
- [ ] prove `(14)` and RH (open research)

## 2026-08-19 — unconditional Lean formalization (stage 3)

Every `[PROVED HERE]` statement of this card is now formalized unconditionally; the trailing
`[CONJECTURE — PRIME-APARTMENT QUILLEN–WARD DESCENT]` and its two gates are open research and are
deliberately not part of the formal content.  All declarations are axiom-clean
(`propext, Classical.choice, Quot.sound`).

**The rooted flag-path Hodge cofactor** —
`formal/GaloisForLFunctions/HTGeometry/PathLaplacianRootedCofactor.lean`

| Card item | Lean declaration |
|---|---|
| the flag-path difference operator `d`, `(d f) j = f_{j+1} - f_j` | `pathDifferential` |
| root-normalized potential (the explicit integrator inverting `d`) | `pathPotential`, `reducedPathIntegrator` |
| the weighted Hodge Laplacian `L_n(t) = a d^* d`, eq. (3) | `pathLaplacian` |
| the rooted (row/column deleted) Laplacian `L_n(t)^{(r)}` | `rootedPathLaplacian` |
| **eq. (4): `det L_n(t)^{(r)} = (1-t)^{n-1}` for every root** | `det_rootedPathLaplacian` |
| **eq. (5): the sum of the rooted cofactors is the marked deformation** | `sum_det_rootedPathLaplacian` |
| eq. (6): the Dirichlet energy identity | `star_dotProduct_pathLaplacian_mulVec` |
| radical of the form is exactly the constant line | `pathLaplacian_form_eq_zero_iff`, `pathDifferential_mulVec_eq_zero_iff` |
| eq. (8): the twisted differential `(d_u f) j = f_{j+1} - u_j f_j` | `twistedPathDifferential` |
| the recursive vertex gauge `g_1 = 1`, `g_{j+1} = u_j g_j` | `pathGauge`, `pathGauge_succ` |
| **the gauge conjugates the twisted differential to the untwisted one** | `twistedPathDifferential_mul_diagonal`, `reducedTwistedPathDifferential_mul_diagonal` |
| the exact gauge factor of a twisted rooted determinant | `det_reducedTwistedPathDifferential` |
| **phase blindness: unimodular transports leave every rooted cofactor unchanged** | `det_rootedTwistedPathLaplacian_of_unimodular` |

The determinant is computed without the matrix-tree theorem: partial-sum potentials give an
explicit integral inverse of the root-reduced incidence matrix, so its determinant is a unit of
`ℤ`, hence its square is `1`, and `L^{(r)} = a · D_rᵀ D_r` gives `a^{n}` directly.

**The minimal phase-bearing successor** —
`formal/GaloisForLFunctions/HTGeometry/CycleTwistedTorsion.lean`

| Card item | Lean declaration |
|---|---|
| eq. (9): the twisted cycle differential and its holonomy | `cycleDifferential`, `cycleHolonomy` |
| only the identity and the cyclic shift contribute | `perm_eq_subRight_of_forall`, `sign_subRight_one_cycleIndex` |
| **eq. (10): `det d_u = unit · ∏ w · (Hol − 1)`** | `det_cycleDifferential` |
| **eq. (11): `det(d_u^* d_u) = ∏ c · |1 − Hol|²`** | `det_conjTranspose_mul_cycleDifferential`, `det_cycleHodge_of_conductances` |
| twisted cohomology is nonzero exactly at holonomy one | `det_cycleDifferential_eq_zero_iff` |

**The prime-support specialization** —
`formal/GaloisForLFunctions/RHTower/PrimeSupportFlagPathHodge.lean`

| Card item | Lean declaration |
|---|---|
| the marked deformation `M_n(t) = n(1-t)^{n-1}` | `primeSupportDeformation`, `primeSupportDeformationPoly` |
| **eqs. (4)–(5) in prime-support form** | `primeSupportDeformation_eq_sum_det_rootedPathLaplacian`, `det_rootedPathLaplacian_flag` |
| **eq. (7): `M_n^{(n-1)}(1) = n(-1)^{n-1}(n-1)!`** | `eval_iterate_derivative_primeSupportDeformationPoly` |
| eq. (12): `Hol_m(z) = exp(-i z log N_m)` for a positive packet | `prod_primeCharacter_pow_eq_primeMonomialHolonomy`, `one_lt_prod_prime_pow` |
| **eq. (12): a positive prime monomial holonomy is trivial only on the centred critical line** | `im_eq_zero_of_primeMonomialHolonomy_eq_one`, `im_eq_zero_of_det_cycleDifferential_eq_zero` |
| **eq. (13): the finite squarefree Euler product is the source-apartment torsion** | `det_cycleDifferential_squarefree_factor`, `prod_det_cycleDifferential_squarefree` |
| finite acyclicity in the open right half plane | `det_cycleDifferential_squarefree_ne_zero` |
