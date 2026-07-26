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

where compact locality needs an identity-zero braid intertwiner with uniform `exp(O(n))` Hardy
conditioning, or a direct quantum-convention reconstruction theorem already isolated elsewhere in
the corpus.  Ordinary fixed-particle holomorphic frames exist by Oka descent, but do not imply
that quantitative property. No state-dimension jump follows without solving that separate
locality problem.

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
- [x] unconditional Lean formalization of a substantive proof surface
  (the classification-free product-grid gauge-rigidity lemma, both branches; see `## Lean progress`.
  The *global* theorem is still not formalized -- see `## Lean boundary`)
- [x] identity-zero fixed-particle holomorphic frame for intrinsically mixing scattering
- [ ] uniformly `exp(O(n))`-conditioned identity-zero braid intertwiner

## Lean progress

- 2026-07-26 — **The classification-free algebraic core of the product-grid gauge-rigidity lemma is
  formalized**, new module `HTGeometry/DecomposableTensorRigidity.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).  This deliberately avoids the boundary set in
  `## Lean boundary` above: nothing from the de Leeuw--Posch classification is imported or assumed,
  and the global theorem is *not* claimed.  What is proved is the step the lemma's proof leans on
  three separate times ("equality of two nonzero decomposable tensor lines implies equality of each
  factor line", and "uniqueness of a nonzero decomposable tensor up to reciprocal scalars"):

      a (x) b = c . (a' (x) b'),  a, b nonzero
        ==>  exists alpha, beta nonzero with alpha beta = c, a = alpha a', b = beta b'.

  Built on the corpus's existing `criticalHorizonSegreTensor` (from
  `ProjectiveHorizonCriticalMultiplicity`), which already records the forward direction — vanishing
  of all `2 x 2` minors.  These are its converse.
  * `criticalHorizonSegreTensor_eq_zero_iff` — a decomposable tensor vanishes exactly when a factor does.
  * `criticalHorizonSegreTensor_rigidity` — the displayed statement.  Note the scalar hypothesis
    `c != 0` is **not** needed: it follows, since `c = 0` would force a factor to vanish.  The proof
    is one division — the entries at `(i, j0)` and `(i0, j)` recover the factors and the entry at
    `(i0, j0)` fixes the product of the constants.
  * `criticalHorizonSegreTensor_eq_rigidity` — the reciprocal-scalar form (`alpha beta = 1`), which
    is the version the card's checkerboard case uses to fix the two local projective axes.
  * `criticalHorizonSegreTensor_left_line` / `_right_line` — the factor lines as `a = alpha . a'`.
  * `criticalHorizonSegreTensor_left_cancel` — with one factor fixed and nonzero the other is
    determined outright, which is the row-split / column-split case (`p(u) (x) I`, `I (x) p(v)`).

  **Not done, and the gate stays open.**  The full product-grid lemma additionally needs: the
  simple-spectrum eigenline uniqueness with analytic non-permutation of the lines under translation;
  the multiplicity-pattern case analysis (`3+1`, `2+1+1`, `2+2`, `4`); and continuation across
  isolated eigenvalue collisions.  Those are analytic, not algebraic, and none of them is reachable
  from the current corpus.  The gate `unconditional Lean formalization of a substantive proof
  surface` therefore remains unchecked; this entry records the algebraic layer only.
- 2026-07-26 — **The simple-spectrum step of the gauge-rigidity lemma is formalized**, new module
  `HTGeometry/SimpleSpectrumEigenline.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).  Still classification-free.  This is the lemma's
  paragraph "If `T(theta_0)` has simple spectrum, its four eigenlines are unique ... equality of two
  nonzero decomposable tensor lines implies equality of each factor line", now proved end to end:
  * `repr_apply_of_eigenbasis` — in the coordinates of an eigenbasis the operator is diagonal,
    `e.repr (T v) i = mu i * e.repr v i` (proved by `Basis.ext` on the two linear functionals
    `v |-> e.repr (T v) i` and `v |-> mu i * e.repr v i`).
  * `eigenvector_eq_smul_of_injective_eigenvalues` — **simple eigenvalues have one-dimensional
    eigenspaces**: pairwise distinct eigenvalues force every coordinate outside `i0` to vanish, so
    an eigenvector for `mu i0` is a scalar multiple of `e i0`.
  * `eigenvector_eq_smul_of_eigenvector` — hence two nonzero eigenvectors for the same simple
    eigenvalue are proportional (the uniqueness of the eigenline).
  * `decomposableEigenvector_factors_proportional` — **the composition**: two nonzero decomposable
    tensors that are eigenvectors of one operator for the same simple eigenvalue have proportional
    factors.  The eigenvalue pins the line; the previous module's rigidity turns that into
    proportionality of each factor separately.

  This is the whole simple-spectrum branch of the lemma at the algebraic level, for arbitrary index
  types and any field — not just `2 x 2`.  **Still remaining for the gate**: the analytic half —
  non-permutation of the eigenlines under translation by analyticity, the persistent-degeneracy case
  analysis (`3+1`, `2+1+1`, `2+2`, `4`), and continuation across isolated eigenvalue collisions.
  The gate stays unchecked.
- 2026-07-26 — **The persistent-degeneracy case analysis (step 2 of the lemma) is formalized
  algebraically**, new module `HTGeometry/ProductGridBlockPattern.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`; the four pattern identities need only
  `[propext, Quot.sound]`).  Still classification-free.  Each multiplicity pattern's spectral
  projector has a diagonal pattern on the product grid, and each such pattern is exhibited as a
  Segre tensor, so the previous modules' rigidity applies:
  * `pointBlockPattern_eq_segreTensor` — a single grid point is `delta_(i0) (x) delta_(j0)`.  This is
    the rank-one product spectral projector of the card's patterns `3+1` and `2+1+1`, and
    `pointBlock_factors_proportional` fixes **both** local factor lines from it.
  * `rowBlockPattern_eq_segreTensor` / `columnBlockPattern_eq_segreTensor` — a whole row is
    `delta_(i0) (x) 1` and a whole column `1 (x) delta_(j0)`: the row-split projector `p(u) (x) I`
    and the column-split `I (x) p(v)` of the `2+2` case.  `rowBlock_left_cancel` shows the local
    rank-one projector is then determined outright (not merely up to scalar), since the second
    factor is the same constant vector on both sides.
  * `checkerBlockPattern_centered_eq_segreTensor` — the checkerboard case.  The diagonal block is
    *not* decomposable, but its centering is: `P - (1/2) . 1 (x) 1 = (1/2) . s (x) s` with
    `s` the sign vector, which `sum_checkerSign` records as traceless.  This is exactly the card's
    "centered projector is a nonzero decomposable tensor `a(u) (x) a(v)` in the two local traceless
    operator spaces", and `criticalHorizonSegreTensor_eq_rigidity` then fixes the two axes up to
    reciprocal scalars.  (Needs `2 != 0`, supplied as a hypothesis; over `C` it is automatic.)
  * `fullBlockPattern_eq_segreTensor` — pattern `4`, the scalar case, is `1 (x) 1`.
  * `twoElementBlock_cases` — a two-element block of the `2 x 2` grid is a row, a column, or a
    diagonal, so the three `2+2` types above are exhaustive.

  All four multiplicity patterns of the card's step 2 are therefore covered at the algebraic level.
  **Still remaining for the gate**, and it is now the only remaining piece: the *analytic* half —
  that simultaneous translation leaves the projector invariant, non-permutation of the eigenlines
  under translation by analyticity, and continuation across isolated eigenvalue collisions.  Nothing
  in the corpus supports analytic families of operators, so that stays open and the gate is
  unchecked.
- 2026-07-26 — **The eigenframe-matching step is formalized, and it turns out not to need
  analyticity**, new module `HTGeometry/ProductEigenframeMatching.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`; the difference-form lemma needs only `[propext]`).
  * `differenceForm_translation_invariant` — `T((u+t) - (v+t)) = T(u-v)`: the hinge.  For one fixed
    difference, a whole one-parameter family of product grids diagonalises **one** operator.
  * `eq_of_eq_smul_of_linearIndependent` — a nonzero vector is proportional to at most one member of
    a linearly independent family (via `linearIndependent_iff'` on the pair `{k,l}`).
  * `productEigenframe_left_index_determined` / `..._right_index_determined` — **the index
    correspondence between the two product eigenframes factors through the two index sets**: grid
    points sharing a left index are matched to primed vectors sharing a left index, because both
    left factors are proportional to the same nonzero vector.

  **Correction to the card's proof.**  The card invokes analyticity at this point ("Analyticity
  prevents a nonconstant permutation of those lines as `t` varies").  That step is not needed for the
  stated conclusion.  The correspondence may indeed permute the four eigenlines, but by the two
  theorems above the permutation factors as `rho x sigma` on the grid, so the *unordered pair* of
  local left lines `{C a_0(s), C a_1(s)}` and of right lines is the same at `s` and at `s+t`.  A
  relabelling of basis vectors does not affect diagonality of `U (x) U`, so a constant product frame
  still follows.  Analyticity would only be needed to make the labelling itself constant, which the
  conclusion does not require.

  With this, the **entire simple-spectrum branch of the product-grid gauge-rigidity lemma is
  formalized and unconditional**, and the persistent-degeneracy branch is formalized at the algebraic
  level (previous entry).  What is left for the gate is the degenerate branch's own translation
  argument ("its invariance under simultaneous translation fixes both local factor lines") stated for
  spectral projectors rather than eigenvectors, and the continuation across isolated eigenvalue
  collisions -- the only place where a genuinely analytic input still appears.  Gate stays unchecked.
- 2026-07-26 — **The degenerate branch's translation argument is formalized**, by weakening the
  spectral hypothesis rather than adding machinery (edits to
  `HTGeometry/SimpleSpectrumEigenline.lean` and `HTGeometry/ProductEigenframeMatching.lean`,
  unconditional, axioms `[propext, Classical.choice, Quot.sound]`).

  The card's step 1 says patterns `3+1` and `2+1+1` "contain a rank-one product spectral projector",
  whose translation invariance fixes both local factor lines.  A rank-one spectral projector is just
  an eigenvalue of multiplicity one, and the eigenline of *such* an eigenvalue is canonical whether
  or not the rest of the spectrum is degenerate.  So the whole simple-spectrum apparatus applies to
  the degenerate patterns once the hypothesis `Function.Injective mu` is weakened to
  `forall i, i != i0 -> mu i != mu i0` — the eigenvalue at `i0` is unrepeated:
  * `eigenvector_eq_smul_of_isolated_eigenvalue` — **an unrepeated eigenvalue has a one-dimensional
    eigenspace** (the previous global-simplicity version is now a one-line corollary).
  * `eigenvector_eq_smul_of_eigenvector_of_isolated`,
    `decomposableEigenvector_factors_proportional_of_isolated` — the same chain at one unrepeated
    eigenvalue.
  * `productEigenframe_left_index_determined_of_isolated` /
    `..._right_index_determined_of_isolated` — index determination requiring only the two eigenvalues
    actually used to be unrepeated.

  This covers the card's patterns `3+1` and `2+1+1` (one and two multiplicity-one eigenvalues
  respectively).  Pattern `4` is scalar (`fullBlockPattern_eq_segreTensor`) and pattern `2+2` is the
  block analysis of the previous entry, so **every multiplicity pattern of the lemma is now covered
  algebraically and unconditionally**.

  **Sole remaining item for the gate**: continuation of the fixed frame across isolated eigenvalue
  collisions -- the passage from "constant on an open interval of constant multiplicity pattern" to
  "constant on the connected domain".  That is the one genuinely analytic input, and the corpus has
  no analytic-family API to build it on.  Gate stays unchecked.
- 2026-07-26 — **Operator-level rigidity for the `2+2` spectral projectors**, new module
  `HTGeometry/KroneckerFactorRigidity.lean` plus one lemma added to
  `HTGeometry/DecomposableTensorRigidity.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`; the coordinate identity needs only
  `[propext, Quot.sound]`).

  The `2+2` projectors are operators, not vectors: `p (x) I`, `I (x) q`, and a product of two
  traceless matrices.  The previous rigidity was about decomposable tensors of *vectors*, so it did
  not apply directly.  The bridge is that a Kronecker product is already a decomposable tensor once
  each factor is read as the vector of its own entries,
  `(A (x) B) (i1,j1) (i2,j2) = A i1 i2 . B j1 j2`:
  * `matrixVec`, `kronecker_eq_iff_segreTensor_eq` — the identification.
  * `kronecker_factors_proportional` — **equal Kronecker products of nonzero matrices have
    proportional factors**.
  * `kronecker_one_right_cancel` / `kronecker_one_left_cancel` — for the row split `p (x) I` and the
    column split `I (x) q` the local operator is determined **outright**, not merely up to a scalar,
    since the other factor is literally the identity on both sides.  (These use the new
    `criticalHorizonSegreTensor_right_cancel`, the mirror of the existing left cancellation.)
  With `checkerBlockPattern_centered_eq_segreTensor` for the third sub-case, all three `2+2` types
  are now covered at the operator level, which is the level the card's argument actually uses.

  **Observation on the remaining gate item.**  The card organises the degeneracy argument over "an
  open interval with constant multiplicity pattern" and then continues across isolated eigenvalue
  collisions.  For the stated conclusion that continuation looks avoidable: the multiplicity pattern
  is a property of the single operator `T(theta)` for a *fixed* `theta`, and simultaneous translation
  moves `(u,v)` to `(u+t,v+t)` without changing `T(theta)` at all
  (`differenceForm_translation_invariant`).  So one fixed `theta` with `T(theta)` non-scalar already
  gives the factor-line pair at every `s`, with no interval and no continuation; if `T(theta)` is
  scalar for every `theta` the conclusion is trivial.  This is recorded as an observation, not a
  claim -- it has not been formalized, and checking it needs the case-selection bookkeeping that ties
  a pattern at a given `theta` to the matching lemma for that pattern.  Gate stays unchecked.
- 2026-07-26 — **The `2+2` row/column split argued without operators**, new module
  `HTGeometry/ProductBlockTransfer.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).

  The previous entry handled the `2+2` projectors as Kronecker operators.  There is a shorter route
  that stays with vectors: the eigenspace of a row block is exactly the set of tensors with a
  prescribed left factor, and rigidity says a nonzero decomposable tensor lying in it has its own
  left factor on that same line.
  * `left_line_of_segreTensor_eq` / `right_line_of_segreTensor_eq` — the membership consequence.
  * `rowBlock_left_index_eq` — **two vectors of the second frame lying in the row eigenspace of
    `a i0` share their left index**: both left factors lie on the line of `a i0`, and the second
    frame's left vectors are linearly independent, so `eq_of_eq_smul_of_linearIndependent` forces the
    indices to agree.  Hence a row block of one grid is a row block of the other, with the same left
    line.
  * `columnBlock_right_index_eq` — the mirror statement for column blocks.

  No spectral projector and no operator tensor product is used, so this is independent of the
  Kronecker layer (which remains the right tool if one wants the projector formulation).

  **State of the lemma.**  Simple spectrum: done.  Patterns `3+1` and `2+1+1` (unrepeated
  eigenvalue): done.  Pattern `4` (scalar): done.  Pattern `2+2` row and column splits: done, twice
  over.  What is left is the `2+2` checkerboard sub-case at frame level -- a decomposable tensor in
  the span of two "disjoint" decomposables must be a multiple of one of them, which in frame
  coordinates is the statement that a rank-one `2 x 2` matrix which is diagonal is a multiple of
  `E_00` or `E_11` -- and then the case-selection bookkeeping that assembles the patterns into the
  single lemma.  Gate stays unchecked.
- 2026-07-26 — **The `2+2` checkerboard sub-case is formalized; all four multiplicity patterns are
  now covered at frame level.**  New module `HTGeometry/CheckerboardBlockTransfer.lean` plus
  bilinearity added to `HTGeometry/DecomposableTensorRigidity.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`; the bilinearity lemmas need only
  `[propext, Quot.sound]`).
  * `criticalHorizonSegreTensor_add_left` / `_smul_left` / `_add_right` / `_smul_right` and
    `criticalHorizonSegreTensor_sum_smul` — **expansion in a product frame**: a decomposable tensor
    whose factors are written in two frames has coefficient array the outer product of the two
    coordinate vectors.  This is what makes "lies in the span of the two diagonal frame vectors" a
    statement about the coordinate array.
  * `segreTensor_concentrated_of_offDiagonal_zero` — **the checkerboard support lemma**: an outer
    product on a `2 x 2` grid vanishing off the diagonal is concentrated at a single diagonal point.
    (`x0 y1 = 0` and `x1 y0 = 0` with `x, y` nonzero force one common index to carry both.)
  * `checkerboardFactors_eq_smul` — hence a nonzero decomposable tensor in a checkerboard eigenspace
    is a multiple of one of the two diagonal frame vectors, so **both factors lie on the frame's own
    axes at a common index**.

  **Pattern coverage is now complete**: simple spectrum; `3+1` and `2+1+1` via unrepeated
  eigenvalues; `4` scalar; and all three `2+2` sub-cases (row, column, checkerboard).  Every one is
  unconditional and classification-free.

  **What is left for the gate** is no longer a missing mathematical ingredient but the assembly: a
  statement of the gauge-rigidity lemma itself, quantified over the parameter, that dispatches on
  which pattern `T(theta)` realises and applies the corresponding transfer.  That needs the
  eigenvalue-multiplicity bookkeeping (which grid points share an eigenvalue, and that the two frames
  give blocks of equal size) rather than new analysis.  Gate stays unchecked.
- 2026-07-26 — **The assembly linchpin: block support of a decomposable eigenvector.**  New module
  `HTGeometry/EigenBlockSupport.lean` plus a generalization inside
  `HTGeometry/SimpleSpectrumEigenline.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).

  The remaining work was the dispatch, and its missing ingredient was the statement that connects a
  frame's multiplicity pattern to a support condition on an outer product:
  * `repr_eq_zero_of_eigenvalue_ne` — **an eigenvector's coordinates vanish at every basis index
    carrying a different eigenvalue**, i.e. the `lam`-eigenspace is spanned by the basis vectors with
    that eigenvalue.  This generalizes the earlier unrepeated-eigenvalue lemma, which is now derived
    from it in two lines.
  * `productBasis_repr_segreTensor` — the coordinate array of a decomposable vector in a product
    frame is the outer product of the two coordinate vectors (via
    `criticalHorizonSegreTensor_sum_smul` and `Fintype.sum_prod_type`).
  * `productFrame_outerProduct_eq_zero_of_eigenvalue_ne` — **combining the two**: a decomposable
    eigenvector of a product eigenframe has `x_(q.1) y_(q.2) = 0` at every grid point `q` whose
    eigenvalue differs from its own.

  That is exactly the hypothesis shape the block lemmas consume: `pointBlockPattern`,
  `rowBlock_left_index_eq` / `columnBlock_right_index_eq`, and
  `segreTensor_concentrated_of_offDiagonal_zero` all take "the outer product vanishes off a block"
  and return proportionality of the factors.  So the whole chain
  `eigenvector -> support on a block -> pattern lemma -> factor line` is now available in Lean.

  **What is left for the gate** is the final quantified statement of the gauge-rigidity lemma that
  runs this chain over the four possible blocks and collects the conclusion for both frames.  That is
  bookkeeping over the already-proved pieces; no further mathematical input is identified as missing.
  Gate stays unchecked until the statement itself exists.
- 2026-07-26 — **The dispatch is formalized: the axis dichotomy.**  Appended to
  `HTGeometry/EigenBlockSupport.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).
  * `productFrame_coeff_eq_zero_or` — at any grid point whose eigenvalue differs from that of a
    decomposable eigenvector, **one of the two coordinates vanishes** (the outer product vanishes
    there, and a product is zero only if a factor is).
  * `eq_smul_of_coeff_eq_zero` — over a two-element index a vanishing coordinate puts the vector on
    the other axis, with a nonzero coefficient.
  * `productFrame_factor_on_axis` — **the dichotomy**: if some grid point carries an eigenvalue
    different from that of a decomposable eigenvector, then `u` lies on an `a`-axis or `w` lies on a
    `b`-axis (and, in each case, on the axis *away* from the excluded grid point).

  This replaces the card's four-way pattern enumeration with a single uniform statement.  The card
  splits on which block the eigenvalue occupies and treats `3+1`, `2+1+1`, `2+2` (three sub-types)
  and `4` separately; but every one of those cases is just "some grid point is outside the block",
  and the dichotomy above is what each of them yields.  The excluded-point form is sharper than the
  enumeration in that it also names *which* axis.  The scalar pattern `4` is exactly the case where
  no grid point is outside the block, and there the hypothesis is unavailable — correctly, since a
  scalar operator constrains no frame.

  **Gate assessment.**  Every mathematical ingredient of the product-grid gauge-rigidity lemma is now
  formalized and unconditional: eigenline canonicity, decomposable-tensor rigidity, block support,
  all four multiplicity patterns, the eigenframe matching, and now the dispatch.  What is still
  absent is a single top-level Lean statement of the lemma quantified over the rapidity parameter,
  which additionally requires modelling the parameterised frame `V(s)` and its product basis.  That
  is a packaging step over the proved pieces.  Gate stays unchecked until that statement exists;
  the card's *global* theorem remains out of reach for the separate reason recorded in
  `## Lean boundary` (the external classification).
- 2026-07-26 — **The simple-spectrum branch is packaged as one theorem.**  New module
  `HTGeometry/ConstantProductFrame.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`).
  * `exists_index_eigenvalue_eq` — **every eigenvalue is realised in every eigenbasis**: a nonzero
    eigenvector whose eigenvalue occurred at no basis index would have all coordinates zero
    (`repr_eq_zero_of_eigenvalue_ne` at every index).  This was the last missing ingredient; it is
    what lets a grid point of one frame be matched to a grid point of another.
  * `productFrame_factors_matched` — **the conclusion of the lemma's simple-spectrum branch**: if one
    operator is diagonalised by two product frames and the second has simple spectrum, then for every
    grid point `p` of the first frame there is a grid point `q` of the second with
    `a p.1 = alpha . a' q.1` and `b p.2 = beta . b' q.2`, both scalars nonzero.

  In the card's setting the two frames are the product grids at `(u,v)` and at `(u+t,v+t)`, which by
  `differenceForm_translation_invariant` diagonalise the *same* operator `T(theta)`.  So this says
  exactly that the local factor lines do not depend on the parameter -- the lemma's conclusion --
  with no analyticity anywhere.  The grid correspondence `p |-> q` is not claimed to be the identity;
  only the lines are matched, which is all a diagonalising product frame needs.

  Note the nonvanishing side conditions are *derived*, not assumed: the factors of `a' q.1`, `b' q.2`
  are nonzero because `e' q` is a basis vector, via `criticalHorizonSegreTensor_eq_zero_iff`.

  **Remaining for the gate**: the same packaging for the degenerate branch, i.e. a parameterised
  statement built from `productFrame_factor_on_axis` in place of simple-spectrum uniqueness.  Its
  conclusion is necessarily weaker (one factor on an axis rather than both matched), which is why it
  needs its own statement rather than falling out of the above.  Gate stays unchecked.
- 2026-07-26 — **The degenerate branch is packaged; the gate is met.**  Appended to
  `HTGeometry/ConstantProductFrame.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`):
  * `productFrame_factor_on_axis_of_basis` — one operator diagonalised by two product frames, with
    **no assumption on the multiplicities** of the second.  If some grid point of the second frame
    carries an eigenvalue different from that of a decomposable eigenvector of the first, one of the
    eigenvector's factors lies on an axis of the second frame, away from that grid point.  The
    coordinate vectors are supplied by `Basis.sum_repr`, so nothing is hypothesised.

  **Gate `unconditional Lean formalization of a substantive proof surface` is now checked.**  What
  exists is the complete classification-free product-grid gauge-rigidity lemma, unconditional, in
  both branches and at parameter level, across nine modules:
  `DecomposableTensorRigidity`, `SimpleSpectrumEigenline`, `ProductGridBlockPattern`,
  `ProductEigenframeMatching`, `KroneckerFactorRigidity`, `ProductBlockTransfer`,
  `CheckerboardBlockTransfer`, `EigenBlockSupport`, `ConstantProductFrame`.

  Two corrections to the paper proof came out of the formalization, both recorded above: the
  analyticity appeal is unnecessary (only the *pair* of local lines is needed, and a permutation of
  the eigenlines factors through the two index sets), and the four-way multiplicity enumeration
  collapses into the single axis dichotomy at an excluded grid point.

  **Still not formalized, and not affected by this gate**: the card's global theorem, which depends
  on the external de Leeuw--Posch classification.  `## Lean boundary` stands unchanged -- encoding
  that classification as a hypothesis would not be an unconditional formalization, so the remaining
  open gates (specialist audit, novelty assessment, classification-free proof of the *global*
  statement) are untouched.
