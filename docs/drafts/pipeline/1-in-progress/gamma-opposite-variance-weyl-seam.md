# The Gamma opposite-variance Weyl seam

- **ID:** `gamma-opposite-variance-weyl-seam`
- **Stage:** 1-in-progress
- **Type:** SOLVABLE HT COMPARISON MODEL / BOUNDARY-CHARGE CONJECTURE
- **Scientific status:** `[CONJECTURE] [ALGEBRAIC INCOMING CHANNEL LEAN-FORMALIZED] [ANALYTIC OUTGOING CHANNEL LEAN-FORMALIZED] [FINITE WEYL SEAM + MIGRATION LEAN-FORMALIZED] [PARENT COLLISION IDENTIFIED]`
- **Parents:**
  - `source-anomaly-boundary-colligation-field.md`
  - `ht-source-riemann-hilbert-correspondence.md`
  - `dyadic-weld-weyl-multiplicity-route.md`
- **Statement:** Gamma's shift equation identifies two opposite-variance realizations of the Weyl
  algebra: analytic Taylor translation and algebraic coordinate-multiplication prolongation. Their
  finite comparison defect is a rank-one charge supported only on the newest clock boundary.

## 1. One source equation, two realizations

Gamma satisfies

```text
Gamma(z+1)=z Gamma(z).                                    (1)
```

On the infinite raw jet `a=(f,f',f'',...)`, the two sides are represented by

```text
E=exp(D),                                                  (2)
(Z(z)a)_j=z a_j+j a_(j-1).                                (3)
```

Here `E` is analytic translation and `Z(z)` is the algebraic differential prolongation of
multiplication by `z`. Equation `(1)` says that the Gamma jet is an equalizer section

```text
E a=Z(z)a.                                                 (4)
```

The clock index is derivative resolution, not time.

## 2. Opposite variance `[LEAN-FORMALIZED]`

Let `E_N` and `Z_N(z)` be the first-`N` finite raw-jet matrices.

Taylor translation is forward Ind-flat but backward Pro-curved:

```text
E_(N+1)i_N=i_N E_N,                                       (5)
p_N E_(N+1)-E_N p_N=beta_N b_N,                           (6)
beta_N(1)=(1/N!,1/(N-1)!,...,1).                          (7)
```

Coordinate multiplication is backward Pro-flat but forward Ind-curved:

```text
p_N Z_(N+1)(z)=Z_N(z)p_N,                                 (8)
Z_(N+1)(z)i_N-i_N Z_N(z)=gamma_N,                         (9)
gamma_N(a)=N a_(N-1)e_N.                                 (10)
```

Equations `(5)`--`(10)` are Lean-formalized. Thus the two exact realizations expose complementary
boundary channels:

```text
beta_N : new boundary -> retained observables,            (11)
gamma_N: retained observables -> new boundary.            (12)
```

No adjoint was inserted by hand. The source equation itself supplies the outgoing analytic and
incoming algebraic halves.

## 3. Finite Weyl boundary formula `[LEAN-FORMALIZED]`

For `0<=i,j<N`,

```text
(E_N)_(i,j)=1_(i<=j)/(j-i)!,                              (13)
(Z_N(z))_(i,j)=z delta_(i,j)+i delta_(j,i-1).             (14)
```

The infinite Weyl covariance is

```text
E Z(z)=Z(z+1)E.                                            (15)
```

No finite truncation can satisfy `(15)` exactly. Direct coefficient cancellation gives the exact
positive replacement

```text
E_N Z_N(z)-Z_N(z+1)E_N
  =-N v_N tensor ell_N,                                   (16)
v_N(i)=1/(N-i)!,        ell_N(a)=a_(N-1).                 (17)
```

The proof is one boundary calculation. For `j<N-1`,

```text
(j+1)(E_N)_(i,j+1)
  =(E_N)_(i,j)+i(E_N)_(i-1,j),                            (18)
```

so the two matrix products cancel. At `j=N-1`, the absent `j+1` column leaves

```text
-1/(N-1-i)!-i/(N-i)!=-N/(N-i)!,                          (19)
```

which is `(16)`.

This is the additive finite-Weyl trace obstruction concentrated on one boundary line. Truncated
oscillators, finite canonical-commutation anomalies, and the project's existing truncated-Weyl
cards are parent theory; `(16)` is not claimed as new linear algebra.

Lean proves `(16)` pointwise as `gammaClockWeylSeam_apply` for the comparison map
`gammaClockWeylSeam`.

## 4. Boundary-charge migration

The significant exact mechanism is the interaction of the two source-selected channels. The
old-clock block of the level-`N+1` Weyl defect is

```text
R_N+beta_N gamma_N.                                       (20)
```

Equations `(7)`, `(10)`, and `(16)` give

```text
beta_N gamma_N=+N v_N tensor ell_N=-R_N.                  (21)
```

Both halves of `(21)` and their equality are now Lean-formalized. The paired map
`gammaClockPairedBoundaryCurrent` has pointwise formula

```text
(beta_N gamma_N a)_i=N a_(N-1)/(N-i)!,                    (21a)
```

range exactly the factorial boundary line, and finrank one at every positive level. The theorem
`gammaClockWeylSeam_eq_neg_pairedBoundaryCurrent` proves the map identity

```text
R_N=-beta_N gamma_N.                                      (21b)
```

The general conservation identity behind `(20)` is Lean-formalized as
`truncate_comp_clockComparisonSeam_comp_extend`; the explicit Gamma substitution `(21)` is now
closed as well.

Therefore the old defect cancels exactly. The whole Weyl charge is recreated on the newest
boundary as `R_(N+1)`. The anomaly does not accumulate in the observable bulk:

```text
boundary charge at N
  --incoming/outgoing pairing--> cancelled at N
  --next clock--> boundary charge at N+1.                 (22)
```

This is a literal model of infinite capacity concentrated on a moving thin boundary.

## 5. Universal-Weyl no-go and positive source criterion

Every analytic germ carries the jet Weyl pair `(D,Z)`; boundary-charge migration alone cannot
certify hypertranscendence. This kills a universal-Weyl definition of HT.

**Positive replacement.** A nonlocal source constraint selects an equalizer or more general
relation inside a completion of the local differential operator algebra. For Gamma the selected
relation is `(4)`. Source content is the pair

```text
(completed relation E-Z(z), global analytic equalizer section).             (23)
```

The boundary current `(16)` is the finite-clock shadow of `(23)`, not the source by itself.

## 6. Thin-completion conjecture

**[CONJECTURE — THIN COMPLETION IDEAL]** A regular source-minimal constrained HT germ `x` has:

1. no nonzero finite algebraic-differential annihilator;
2. a nonzero finitely generated annihilator or relation object in a canonical nonlocal completion
   of its source operator algebra;
3. a source-canonical anomaly colligation whose boundary width is uniformly finite;
4. a global analytic section of the completed relation with no finite algebraic horizontalization.

This is the proposed foundational gap:

```text
finite differential annihilator = 0,
completed nonlocal constraint ideal != 0.                 (24)
```

The associated boundary current is the graded defect of passing from the completed relation to
finite clocks.

**Falsifier.** A source-minimal constrained HT germ whose minimal nonlocal relation necessarily
has unbounded boundary width, or a differentially algebraic germ satisfying all four clauses.

## 7. Boundary-charge escape conjecture

**[CONJECTURE — SOURCE-SELECTED NONTERMINATION]** Within the class in the thin-completion
conjecture, differential algebraicity is equivalent to absorption of the source anomaly by a
finite algebraic boundary condition. Hypertranscendence is equivalent to nontermination: every
finite clock pushes a nonzero source comparison charge to a higher boundary, while the completed
constraint still has a global analytic section.

This is not the universal statement that the Weyl defect `(16)` never terminates. The charge must
be the image of the minimal source relation `(23)` under the source comparison functor.

**Falsifier.** Gamma's source-specific comparison charge terminates after finite calibrated gauge,
or a differentially algebraic constrained source has an unavoidable nonterminating minimal charge.

## 8. Comparison-correspondence conjecture

Parameterized difference Galois theory constructs the algebraic prolongation tower `(3)`. Analytic
translation constructs `(2)`. These are established parent theories.

**[CONJECTURE — GAMMA WEYL-SEAM COMPARISON]** The Gamma comparison torsor is the moduli of
source-compatible identifications of the algebraic Pro-flat prolongation and analytic Ind-flat
translation across the boundary current `(16)`. Under this identification:

1. parameterized Galois differential dimension becomes clock capacity;
2. the rank-one Weyl current becomes transverse thinness;
3. period-one tangent freedom is the automorphism group of the equalizer section;
4. Gamma normalization makes the global integration fiber contractible.

This would be the first actual theorem of the proposed HT source Riemann--Hilbert correspondence.

### Periodic gauge and canonical reduction

A value normalization does not make the Gamma fiber a point: two nowhere-zero solutions of the
same shift constraint differ by a nonzero period-one multiplier. This torsor law is already
Lean-formalized generically in `CarrierDichotomy.lean`.

The positive calibrated model is also already formalized on the additive digamma side. Two
solutions of the same unit-shift cocycle with one common logarithmic asymptotic coincide on the
right half-plane; the explicit digamma source supplies existence. Therefore:

```text
uncalibrated analytic fiber = periodic gauge torsor,
asymptotically calibrated fiber = one point.               (24a)
```

**[CONJECTURE — TORSOR IDENTIFICATION]** The parameterized difference-Galois automorphism torsor of
the Gamma module analytifies to the periodic gauge torsor in `(24a)`, and the opposite-variance
boundary current is the filtered extension class of this identification. Asymptotic source
selection is a reduction of structure group to the trivial subgroup, not an arbitrary boundary
condition.

## 9. General source conjecture

For a rank-one difference constraint

```text
f(z+1)=a(z)f(z),                                          (25)
```

the algebraic side is the differential prolongation of `M_a`, while the analytic side is Taylor
translation. Their finite seam is no longer the elementary Weyl current `(16)`; derivatives of
`a` create a higher boundary colligation.

**[CONJECTURE — SOURCE SEAM CLASSIFICATION]** The gauge-equivalence class of this opposite-variance
seam is a complete invariant of the minimal rank-one parameterized difference module together with
its analytic source topology. Its boundary width is controlled by the differential complexity of
`a`, while hypertranscendence is maximal capacity of its global equalizer section.

Gamma is the affine Weyl vacuum `a(z)=z`; a non-affine `a` is the first test of genuine higher seam
curvature.

## 10. RH pressure test only

**[CONJECTURE; NOT AN RH RESULT]** The different RH obstruction chains could be representations of
one source-selected nonterminating boundary current: spectral incompleteness, continuation
failure, positivity failure, monodromy, and boundary-condition ambiguity would describe different
ways its completed equalizer section fails to be uniquely self-dual. Critical zeros would be the
common self-dual degeneracy spectrum of that completed seam.

No Weyl pair chosen from a zero space counts. A prime--archimedean source relation must first
produce both variance halves and their comparison current independently of the divisor.

## Gates

- [x] analytic translation Ind-flatness Lean-formalized
- [x] analytic outgoing factorial boundary channel Lean-formalized
- [x] algebraic coordinate multiplication Pro-flatness Lean-formalized
- [x] algebraic incoming top-jet boundary channel Lean-formalized
- [x] universal-Weyl HT criterion killed with source-specific positive replacement
- [x] exact finite Weyl boundary formula proved on paper
- [x] boundary-charge migration identity proved on paper
- [x] exact paired incoming/outgoing current and rank-one range Lean-formalized
- [x] general opposite-variance seam conservation formalized in Lean
- [x] finite Weyl boundary formula formalized in Lean
- [x] migration identity formalized in Lean
- [ ] Gamma equalizer section constructed analytically in the project language
- [x] uncalibrated periodic ambiguity and asymptotic analytic source selection anchored to existing
  Lean theorems
- [ ] Gamma parameterized-Galois/analytic comparison torsor proved
- [ ] one non-affine rank-one source seam constructed
- [ ] independent novelty and significance audit
