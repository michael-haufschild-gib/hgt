# Polarized framed derived source-character principle

- **ID:** `polarized-framed-derived-source-character-principle`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / UNIFIED HT OBSTRUCTION OBJECT / COMPARISON PROGRAM
- **Scientific status:** `[BOLD CONJECTURE] [SUPPORTED BY ONE EXACT HIERARCHY]`
  `[T1 LEAN-VERIFIED] [EXTERNAL NOVELTY GATE OPEN] [NOT AN RH RESULT]`
- **Parents:**
  - `../2-fully-proven/new_scientific_knowledge/multiple-gamma-physical-characteristic-fat-point.md`
  - `../2-fully-proven/new_scientific_knowledge/multiple-gamma-period-excess-closure-phase-transition.md`
  - `hypertranscendental-critical-closure-defect-principle.md`
  - `hypertranscendental-constraint-hodge-duality.md`
- **RH pressure-test input only:**
  - `../../../reports/rh-proof-chains-and-obstructions-2026-07-16.md`

## The level shift

The multiple-Gamma physical pullback proves that a thin reduced degeneracy set can carry an
arbitrarily large constraint multiplicity and derived amplitude.  It does **not** yet identify the
unified HT object.  The same calculation gives a decisive no-go.

Let the pulled-back source cofaces be

```text
g_i(lambda)=lambda^r u_i(lambda),   u_i(0) != 0.          (1)
```

Multiplying the `g_i` independently by arbitrary analytic units changes their source phases and
can reverse source-labelled orientations, but it changes neither

```text
the ideal (lambda^r),
the fat point Spec A/(lambda^r),
the quasi-isomorphism class of the Koszul complex,
nor its homology modules.                                      (2)
```

Indeed, unit rescaling is removed by an invertible diagonal change of the source generator module.
Therefore:

```text
[NO-GO] The unframed derived physical characteristic germ can determine source orientation.
```

This is not merely a warning about reduced support.  Even the complete unframed derived topology
is blind to orientation surgery.

**Positive successor.**  The source presentation, its integral labels, its logarithmic lift, and
its positive real structure are load-bearing data.  The candidate unified object is a framed and
polarized derived source-character germ, not a derived scheme considered up to quasi-isomorphism.

## Candidate object

For a source-minimal constrained HT system `F`, let:

```text
Lambda_F                         integral source group,
rho_F : Lambda_F -> Aut(K_F)    source action on the analytic differential field,
A_F=C[Lambda_F]                 source group algebra,
epsilon : A_F -> C              augmentation,
J_F subset A_F                  DA-relative source constraint ideal/module,
chi_F : Spec O_F -> Spec A_F    physical character germ,
                                  q |-> exp(lambda tau_F(q)).
```

Choose a source presentation `s_F:E_F -> A_F` of `J_F`, where `E_F` retains the ordered integral
source labels rather than only the image ideal.  Define the algebraic core

```text
P_F = L chi_F^* K(s_F),                                      (3)
```

with `K(s_F)` the source-labelled Koszul object.  The proposed complete invariant is

```text
U(F) = (
  Lambda_F -> C,                 embedded integral source group,
  E_F -> A_F,                    integral source framing,
  P_F,                           derived physical character fiber,
  Rees_epsilon(P_F),             augmentation/contact filtration,
  log chi_F,                     chosen logarithmic lift and deck action,
  B_F,                           source-forced bornological realization,
  eta_F,                         positive half-density/polarization,
  c_F                            calibration killing the residual constant gauge
).                                                               (4)
```

The word `physical` means source-character realization; it does not assert that `lambda` is time.
It is an observable coordinate on the character family.

## Main conjecture

> **[CONJECTURE — POLARIZED FRAMED DERIVED SOURCE-CHARACTER PRINCIPLE.]**  Every conservative
> obstruction produced by a source-minimal constrained hypertranscendental system factors through
> `U(F)`.  The algebraic support of `(3)` records exact degeneracy, its nilpotent and derived
> filtrations record constraint depth, the embedded integral source group and bornology record
> cofinal attainability, the logarithmic lift records monodromy and orientation, and the polarized
> pointed framing selects the effective source boundary condition.

This is a universality conjecture about HT source constraints, not an assertion about any zeta
zero.  It is falsified by two source systems with isomorphic data `(4)` and different conservative
obstruction theories.

## Exact multiple-Gamma evidence

For the generic order-`r` multiple-Gamma hierarchy:

```text
A_F = C[t_0^+-1,...,t_r^+-1],
x_j=t_j-1,
J_F=< product_(j!=i) x_j >,
chi_F(t_j)=exp(lambda tau_j).
```

The current exact results give:

```text
chi_F^*J_F=(lambda^r),
length O_F/(lambda^r)=r,
derived amplitude of L chi_F^*K(s_F)=r,
DA transverse depth=r,
source constraint onset=r,
period-rank excess=r.                                      (5)
```

On actual exponential modes, each global source translation defect diagonalizes as

```text
(T_tau_j-1)e^(lambda z)
  =(exp(lambda tau_j)-1)e^(lambda z).                       (6)
```

Hence the source-labelled coface boundary and the DA characteristic coface have the same scalar
physical symbol.  For rationally independent periods their common exact degeneracy spectrum is
the central character `lambda=0`.  This is the first chain-level comparison between two genuinely
different realizations: DA annihilators and global analytic source translations.

This comparison and the unit-scaled fat-point ideal are Lean-verified in
`formal/GaloisForLFunctions/HTGeometry/PhysicalCharacteristicIncidence.lean`.

The bounded integral-period realization sends the augmentation coordinate to

```text
w(q)=q/(1+|q|),
```

and the order-`r` fat-point generator to the powered multiplier `w(q)^r`.  Its positive critical
section is `|w(q)|^(r/2)`.  The formal comparison of this complete Rees filtration, rather than
only its exponent, remains open.

## Why the framing is necessary

The successive forgetful maps lose different obstruction data:

```text
framed polarized germ
  -> unpolarized framed germ       forgets sign/effectivity,
  -> unframed derived germ         forgets source orientation and labelled incidence,
  -> nonreduced classical germ     forgets higher coherence,
  -> reduced support               forgets multiplicity and constraint depth,
  -> underlying point set          forgets all infinitesimal structure.       (7)
```

The multiple-Gamma unit-rescaling theorem proves the second loss is real.  The central-fat-point
theorem proves the fourth loss is real.  The nondiscrete period-incidence theorem proves that even
the framed local algebra does not determine cofinal attainability without its bornological
realization.

## Proposed interpretation of the seven RH-chain obstructions

The following is a pressure test, not evidence for RH and not yet a theorem.

| Terminal class | Proposed forgotten datum in `U(F)` |
|---|---|
| source sign/orientation | polarization and oriented integral source frame |
| critical all-scale estimate | closedness/effectivity in the source-forced bornology |
| spectral/determinant realization | perfect polarized realization and determinant trivialization |
| arithmetic multiplicity structure | nilpotent length, Fitting filtration, and derived amplitude |
| non-circular source-to-divisor comparison | missing source-natural comparison morphism out of `(3)` |
| missing typed bridge | absence of a functor carrying the complete structure `(4)` |
| unsupported algebraicity/rigidity | torsion or periodicity of the lifted physical character arc |

This table is useful only if the same assignments predict obstruction behavior in non-zeta HT
families.  It must be tested there first.

## Anti-theatre and parent-theory gate

The following components are established parent mathematics and do not carry novelty separately:

1. group algebras and augmentation ideals;
2. Koszul complexes and derived base change;
3. exponential diagonalization of translation operators;
4. Mellin transforms, Alexander modules, and cohomology jump loci on complex tori;
5. arc contact orders and Rees filtrations;
6. orientations on derived/d-critical loci and framed derived deformation problems;
7. closed-range criteria and fractional source conditions for diagonal operators.

The candidate-new content is the **forced conservative package** `(4)` for constrained HT systems,
the cross-realization law `(5)`--`(6)`, and a universality theorem explaining why apparently
different obstruction types arise from distinct forgetful functors of one source object.  This
novelty claim remains provisional until a broader literature audit and a second HT family are
complete.

Known adjacent literature presently includes Mellin transforms from `D`-modules to difference
systems, cohomological Alexander modules over affine tori, propagation of cohomology jump loci,
exponential-algebraic intersections, oriented d-critical loci, and framed derived deformation
functors.  These parents substantially weaken any novelty claim based merely on adding the words
`derived`, `oriented`, or `framed`.  None of the located sources states `(4)` for
hypertranscendental source systems, derives its decorations from source minimality, or proposes the
obstruction-factorization principle.  This is negative search evidence, not priority
certification.

Representative adjacent sources checked:

- Garcia Lopez, Mellin transform of a `D`-module to a difference system,
  `https://arxiv.org/abs/1804.09776`;
- Liu--Maxim--Wang, Mellin transformation and cohomology jump-locus propagation,
  `https://arxiv.org/abs/1709.02870`;
- Elduque--Herradón Cueto--Maxim--Wang, Alexander modules and mixed Hodge structures,
  `https://arxiv.org/abs/2104.09729`;
- Joyce, oriented d-critical loci as classical models of derived critical loci,
  `https://arxiv.org/abs/1304.4508`;
- Booth, framed derived deformation theory,
  `https://arxiv.org/abs/2009.01590`.

## Exact next theorems

### T1. Source-symbol comparison `[first]`

Formalize `(6)` for every source-labelled coface and prove

```text
DA physical characteristic boundary
  <-> all source coface translation boundaries kill the exponential mode.      (8)
```

For a rationally independent period frame, prove both sides of `(8)` hold exactly at `lambda=0`.
This theorem is unconditional and does not mention RH.

### T2. Framing no-go

For a commutative local ring, prove componentwise unit rescaling of a source sequence induces an
isomorphism of source Koszul complexes, while the oriented determinant of the labelled
presentation changes by the product of those units.  The unframed derived object is invariant;
the framed determinant line is not.

### T3. Rees-to-powered-incidence comparison

Construct the polynomial functional calculus

```text
C[lambda] -> bounded diagonal source operators,
lambda |-> M_w,
```

and prove `(lambda^k) |-> M_(w^k)` together with the exact fractional phase law for `k=r`.  Then
identify which completion of the Rees algebra is forced by the embedded period group rather than
chosen by hand.

### T4. Positive-tangency falsifier

Construct a natural HT source with physical tangency excess `>0`.  Test whether its DA depth tracks
abstract source height while its analytic closure exponent tracks physical contact order.  If the
closure exponent does not change, the contact filtration in `(4)` is not conservative.

### T5. Second-family comparison

Carry T1--T3 out for Barnes or multiple-sine data.  A comparison only inside one multiple-Gamma
hierarchy is not enough for a universality claim.

## Decision

The immediate search target is T1 followed by T2, not another scalar equality and not an RH
criterion.  The first can establish that two independent analytic/algebraic realizations share the
same source-character fiber.  The second determines the minimum extra structure needed to retain
orientation.  Only after both should the bornological comparison T3 be treated as a candidate
unification theorem.

## Gates

- [x] bold conjecture stated with falsifier
- [x] unframed-derived no-go isolated
- [x] positive framed/polarized successor isolated
- [x] all seven obstruction classes assigned provisionally
- [x] parent components separated from candidate novelty
- [x] RH kept as downstream pressure test
- [x] T1 Lean-verified
- [ ] T2 Lean-verified
- [ ] T3 Lean-verified
- [ ] positive-tangency example constructed
- [ ] second HT family realizes the same package
- [ ] broader external novelty audit complete
