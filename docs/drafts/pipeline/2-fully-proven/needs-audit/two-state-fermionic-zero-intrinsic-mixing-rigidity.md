# A two-state unitary flip-anchored braid family has one fixed product eigenframe

- **ID:** `two-state-fermionic-zero-intrinsic-mixing-rigidity`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM / COMPLETE-CLASSIFICATION COROLLARY / QFT SEARCH NO-GO
- **Scientific status:** `[PROVED ON PAPER] [EXTERNAL CLASSIFICATION DEPENDENCE]`
  `[NOVELTY UNVERIFIED AFTER 1982 PARENT AUDIT]`
- **Scope:** analytic two-state positive-unitary difference-form scattering in the adjacent braid
  convention with `B(0)=-P`; no RH or distinguished special-function input
- **Parents:** `projective-wigner-smith-nonabelian-ht-separation.md`,
  `../not_new_scientific_knowledge/diagonal-projective-ht-local-qft.md`, and
  `fermionic-zero-braid-anchor-commutation-gate.md`
- **Statement:** Let `V=C^2` and let `B(theta)` be analytic on a connected rapidity domain,
  positive-unitary on the real axis, and satisfy the additive adjacent-leg Yang--Baxter equation

  ```text
  B_12(x) B_23(x+y) B_12(y)
    =B_23(y) B_12(x+y) B_23(x).                               (1)
  ```

  If `B(0)=-P`, then one constant unitary one-particle basis `U` makes

  ```text
  (U tensor U) P B(theta) (U tensor U)^*
  ```

  diagonal for every real `theta` in the domain.  Thus this exact two-state locality route allows
  arbitrary projective HT in relative diagonal eigenphases, but no intrinsic channel mixing.

## Convention-correct reduction

Put

```text
R(theta)=-P B(theta).                                         (2)
```

The permutation calculation in the parent theorem sends `(1)` to the standard quantum equation

```text
R_12(y) R_13(x+y) R_23(x)
  =R_23(x) R_13(x+y) R_12(y),                                (3)
```

and gives

```text
R(0)=I.                                                       (4)
```

Positive unitarity is preserved because

```text
R(theta)^* R(theta)=B(theta)^* P P B(theta)=I.                (5)
```

This is the nonregular scalar-identity quantum slice.  It is not the regular quantum slice
`R(0)=P`.  A physical quantum S-matrix with zero `-P` instead has a braid conversion with zero
`-I`; the theorem must not be transferred to that lane by notation.

## Exhaustion of the scalar-identity full-rank slice

De Leeuw--Posch classify all analytic `4 x 4` quantum Yang--Baxter solutions, up to parameter
redefinitions, scalar normalization, transpose/parity, and spectral local similarities

```text
R_ij(u,v) |-> V_i(u) V_j(v) R_ij(u,v) V_i(u)^(-1) V_j(v)^(-1). (6)
```

Because a similarity fixes the identity, a representative of a family meeting `(4)` must itself
have a nonzero scalar-identity equal-parameter value.  Pointwise unitarity also forces full rank and
diagonalizability.  Their complete rank-four list then filters as follows.

| Branch | Scalar-identity test | Positive-unitary consequence |
|---|---|---|
| `R^A` | Four arbitrary diagonal functions may all equal one at coincidence. | Survives. |
| `R^B` | Anti-diagonal at coincidence. | Excluded. |
| `R^C,R^D` | A nonzero combination of the displayed traceless Pauli tensors cannot be a nonzero scalar identity. | Excluded. |
| `R^E` | Scalar identity would require `p=q=k` and also `-pq=k^2`. | No invertible solution. |
| `R^{E'}` | Scalar identity forces `p=q=k`. | Its sole off-diagonal coefficient vanishes identically; the branch is scalar. |
| `R^F` | Coincidence spectrum is `{1,1,1,-1}`. | Excluded. |
| `R^G` | It has the form `f_1 I+N` with `N` strictly upper triangular. | A nonzero `N` gives a Jordan block, so unitarity forces `N=0`. |
| `R^H` | Identity forces `p=q=0`, leaving `I+c(f(u)-f(v))E_14`. | A nonconstant member is unipotent and non-diagonalizable, so it is excluded. |
| `R^I,R^J` | Their coincidence spectra are not scalar. | Excluded. |

All lower-rank families are excluded by `(5)`.  Jordan form, spectrum, and rank are invariant under
the similarities in `(6)`.  Hence every surviving family is in the spectral-local gauge orbit of
the diagonal family `R^A`.

This argument uses the final June 2026 version of the classification.  It includes the arbitrary-
function upper-triangular branch omitted in earlier lists; that branch is precisely `R^G`, and the
Jordan obstruction is why it does not survive positive unitarity.

## The local-gauge loophole closes in dimension two

The classification quotient `(6)` is coarser than physical equivalence.  A rapidity-dependent
`V(u)` is not one fixed one-particle basis and can carry a noncentral logarithmic connection.  The
following lemma closes that loophole for a normal two-state difference family.

### Product-grid gauge-rigidity lemma

Let `T(u-v)` be a normal analytic family on `C^2 tensor C^2`.  Suppose that for every `(u,v)` it is
similar to a diagonal matrix in the product grid

```text
{ V(u)e_i tensor V(v)e_j : i,j in {0,1} }.                   (7)
```

Then one constant basis `U` makes every `T(theta)` diagonal by `U tensor U`.

### Proof

Fix `theta=u-v` and translate both parameters by `t`.  The operator `T(theta)` does not change, so
the product grid in `(7)` remains an eigenbasis of one fixed normal operator.

If `T(theta_0)` has simple spectrum for one `theta_0`, its four eigenlines are unique.  Analyticity
prevents a nonconstant permutation of those lines as `t` varies.  Equality of two nonzero
decomposable tensor lines implies equality of each factor line.  Consequently each of the two
lines `C V(s)e_0` and `C V(s)e_1` is independent of `s`.  Rescaling the columns does not affect a
diagonal conjugation, so a single constant product basis diagonalizes the whole family.

It remains to treat persistent spectral degeneracy.  On an open interval with constant
multiplicity pattern, the diagonal entries form a partition of the `2 x 2` product grid.

1. Patterns `3+1` and `2+1+1` contain a rank-one product spectral projector.  Its invariance under
   simultaneous translation fixes both local factor lines.  Applying the same argument to the
   complementary block fixes the required product axes.
2. A `2+2` partition is, up to row and column exchange, one of three types:
   - a row split, whose spectral projector is `p(u) tensor I`;
   - a column split, whose spectral projector is `I tensor p(v)`;
   - a checkerboard split, whose centered projector is a nonzero decomposable tensor
     `a(u) tensor a(v)` in the two local traceless operator spaces.
   Simultaneous-translation invariance fixes the local rank-one projector in the first two cases.
   In the checkerboard case, uniqueness of a nonzero decomposable tensor up to reciprocal scalars
   fixes the two local projective axes.  Normality makes the resulting two local lines orthogonal.
3. Pattern `4` is scalar and is diagonal in every fixed basis.

These cases exhaust partitions of a four-element product grid.  The fixed basis obtained on a
nonempty open interval extends across isolated eigenvalue collisions by analyticity and across the
connected domain by continuation.  This proves the lemma.

Apply the lemma to the surviving `R^A` gauge orbit.  Pointwise unitarity makes `R(theta)` normal,
so one constant unitary `U` diagonalizes every `R(theta)`.  Equation `(2)` then proves the stated
diagonal-behind-the-flip conclusion for `B`.

## Exact HT consequence

The theorem is not a no-go for physical HT.  In the surviving basis,

```text
R(theta)=diag(r_11(theta),r_12(theta),r_21(theta),r_22(theta)),
B(theta)=-P R(theta).                                         (8)
```

The relative phases `r_ab/r_cd` may be arbitrarily hypertranscendental subject to the remaining
analytic, unitarity, and crossing conditions.  The existing compact-local two-species model has
exactly this form and differential-transcendence degree one.

What is excluded is the conjunction

```text
dim V=2,
positive-metric unitarity,
adjacent difference-form Yang--Baxter equation,
B(0)=-P,
intrinsic mixing after removing P.                            (9)
```

Thus HT survives on this route as relative eigenphase geometry, not as a moving nonabelian channel
frame.

## Parent-theory and novelty audit

Sogo--Uchinami--Akutsu--Wadati already solved the two-component factorization equations in the
generalized eight-vertex sparsity sector in 1982.  They obtained eight `8V`, `6V`, and `7V`
families, with elliptic, trigonometric, hyperbolic, and degenerate formulas and explicit unitarity
conditions.  Vieira--Lima-Santos later gave a systematic differential classification of regular
two-state solutions up to the eight-vertex model.  Therefore any claim that merely reclassifies
the sparse two-component families, or observes that their displayed mixing ratios are DA, is
rediscovery.

The exact possible-new residue here is narrower: the full sixteen-entry scalar-identity,
positive-unitary corollary of the complete 2026 classification together with the fixed-product-
frame closure of its spectral local gauge orbit.  The primary sources do not state this corollary
in these terms.  Focused searches for `R(0)=I unitary diagonal`, `two-component factorization fixed
product basis`, and `nonregular Yang--Baxter positive unitary` found no explicit theorem.  This is
negative search evidence, not an expert novelty certificate.

The significance is real but bounded.  The theorem closes one exact two-state compact-local search
surface.  It is not a new classification of Yang--Baxter solutions, does not exclude projective HT,
and does not establish a minimum of three physical species in the conventional quantum lane.

## Physical bifurcation

The constructive program now separates cleanly:

```text
adjacent B(0)=-P + two states + positive unitarity
  => HT relative diagonal phases are possible, intrinsic mixing is not;

physical quantum R_phys(0)=-P + intrinsic mixing
  --right flip-->
braid B_phys(0)=-I,
```

where compact locality needs the identity-zero braid intertwiner or a direct quantum-convention
reconstruction theorem already isolated elsewhere in the corpus.  No state-dimension jump follows
without solving that separate locality problem.

## Anti-theatre gate

1. The 1982, 2018, and 2026 classifications are parent mathematics and are not claimed as new.
2. Projective HT is not ruled out; the proved diagonal local-QFT control remains a counterexample
   to any such claim.
3. Pointwise product diagonality alone is insufficient.  The product-grid gauge-rigidity lemma is
   the step that supplies one fixed basis.
4. A rapidity-dependent basis is not silently quotiented as physical gauge.
5. The theorem is confined to the adjacent flip-anchor lane and cannot be advertised as a no-go
   for standard physical quantum S-matrices.
6. No lower bound of three species and no intrinsically mixing HT construction is claimed.

## Lean boundary

The braid-to-quantum conversion and pointwise operator-Schmidt commutation theorem are already
proved on paper in the parent card.  The global theorem here relies on an external complete
classification whose many analytic matrix families are not formalized in the project.  Encoding
the classification conclusion as a hypothesis would not be an unconditional formalization of this
theorem.  No Lean wrapper or build is justified before the novelty audit decides whether importing
that classification, or finding a classification-free proof, creates a substantive theorem surface.

## Primary literature

- K. Sogo, M. Uchinami, Y. Akutsu, and M. Wadati, *Classification of Exactly Solvable
  Two-Component Models*, <https://doi.org/10.1143/PTP.68.508>.
- R. S. Vieira and A. Lima-Santos, *Solving and classifying the solutions of the Yang--Baxter
  equation through a differential approach. Two-state systems*,
  <https://arxiv.org/abs/1712.02341>.
- M. de Leeuw and V. Posch, *All `4 x 4` solutions of the quantum Yang--Baxter equation*,
  <https://arxiv.org/abs/2411.18685>.
- S. Alazzawi and G. Lechner, *Inverse Scattering and Locality in Integrable Quantum Field
  Theories*, <https://arxiv.org/abs/1608.02359>.

## Gates

- [x] corpus convention and `O(N)` benchmark audited
- [x] adjacent flip anchor converted to quantum scalar identity
- [x] final June 2026 full-rank list audited branch by branch
- [x] omitted arbitrary-function triangular branch included and killed by Jordan form
- [x] rank-deficient branches excluded by positive unitarity
- [x] spectral local-gauge loophole closed for every `2 x 2` product-grid multiplicity pattern
- [x] one rapidity-independent unitary `U tensor U` obtained
- [x] projective HT survival stated explicitly
- [x] 1982 sparse-sector parent collision identified
- [ ] independent specialist audit of the classification-equivalence closure
- [ ] expert novelty assessment of the full-sixteen-entry corollary
- [ ] classification-free proof
- [ ] unconditional Lean formalization of a substantive proof surface
- [ ] identity-zero braid intertwiner for intrinsically mixing physical quantum scattering
