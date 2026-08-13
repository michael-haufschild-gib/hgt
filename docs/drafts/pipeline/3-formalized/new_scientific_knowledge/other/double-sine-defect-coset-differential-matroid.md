# The double-sine translation defects form the coset differential matroid

- **ID:** `double-sine-defect-coset-differential-matroid`
- **Stage:** 3-formalized / needs independent audit
- **Type:** THEOREM (paper) / TRANSLATION-DEFECT CLASSIFICATION
- **Scientific status:** `[NOVELTY UNVERIFIED]` -- the paper proof is complete conditional on the
  several-translation additive telescoping theorem already used by the parent double-sine card.
  Kurokawa--Wakayama prove differential algebraicity for commensurable positive periods, and Kato
  proves hypertranscendence when some period ratio is non-real.  No located theorem treats positive
  real irrational periods, classifies arbitrary translation defects by period-lattice cosets, or
  computes their complete nonlinear differential matroid.
- **Parent:** `double-sine-translation-annihilator`
- **Statement:** Let `omega_1,omega_2>0` with irrational ratio, let `L_2=(log S_2)'`, and put
  `H=Z omega_1+Z omega_2`.  For arbitrary shifts `h_1,...,h_m`, the differential transcendence
  degree of the defects `L_2(z+h_i)-L_2(z)` is the number of distinct nonzero classes among
  `h_i+H`.  Consequently every finite family of translates in distinct `C/H` classes is
  differentially algebraically independent, and every finite constant-coefficient differential
  superposition has the exact group-algebra rank.

## Setup

Write

```text
T_j f(z)=f(z+omega_j),
Delta_h f(z)=f(z+h)-f(z),
a_j(z)=(pi/omega_j) cot(pi z/omega_j).
```

For signs `epsilon_j in {1,-1}` depending only on the standard double-sine convention,

```text
(T_1-1)L_2=epsilon_1 a_2,
(T_2-1)L_2=epsilon_2 a_1.                         (1)
```

The signs play no role below.  Put

```text
E_j=C(exp(2 pi i z/omega_j)),
K=E_1 E_2.
```

The parent card proves that `E_1` and `E_2` are algebraically independent over `C`, that `K` is a
differential field DA over `C(z)`, and that a meromorphic function fixed by both `T_1,T_2` is
constant because `Z omega_1+Z omega_2` is dense in the real line.

## Main theorem

For a finite list `h_1,...,h_m in C`, let

```text
d_i=Delta_(h_i)L_2.
```

Let `c(h_1,...,h_m)` be the number of distinct nonzero elements of `C/H` represented by the
`h_i`.  Then

```text
dtrdeg_(C(z)) C(z)<d_1,...,d_m>_delta=c(h_1,...,h_m).   (2)
```

In particular:

1. `Delta_h L_2` is DA exactly when `h in H`;
2. defects belonging to distinct nonzero `H`-cosets are jointly differentially algebraically
   independent;
3. defects in the same coset differ by a DA function.

The abstract independence content (2) — distinct-coset defects jointly independent, same-coset
rank-neutral, giving `dtrdeg = ` number of distinct nonzero cosets — is the partition-matroid /
star-independence case of the gluing engine formalized axiom-clean in
`GaloisForLFunctions.DifferentialMatroidGluing` (`Rank.freeBlock`, `Rank.crossNeutral_iUnion_indep`).
The rank abstraction is now discharged by `DifferentialMatroidRank.differentialRank`, and
`differentialRank_crossNeutral_of_image_differentialAlgebraic` converts packetwise DA directly to
`CrossNeutral`. In addition, `DifferentialFamilyMatroid.differentialFamilyMatroid_eq_affineCollisionMatroid_iff`
identifies the exact remaining target: the double-sine family represents the coset collision
matroid precisely when every subfamily is differentially independent exactly when its nonzero
coset labels are injective. The unformalized content is therefore the paired analytic telescoping
and pole-orbit proof of that equivalence, not the matroid or rank infrastructure.

## Proof: structural cosets give the upper bound

Equation (1) and finite telescoping show that `Delta_h L_2` is DA for every `h in H`.

If `h_i-h_j in H`, then

```text
d_i-d_j=Delta_(h_i-h_j)L_2(z+h_j),
```

which is a translate of a DA function.  Therefore all defects are DA over one representative from
each distinct nonzero coset, proving the upper bound in (2).

## Proof: simultaneous paired telescoping

Choose representatives `h_1,...,h_s` of distinct nonzero classes of `C/H` and suppose their
defects are differentially algebraically dependent.  Commuting `Delta_(h_i)` with (1) gives

```text
(T_1-1)d_i=epsilon_1 Delta_(h_i)a_2 in E_2,
(T_2-1)d_i=epsilon_2 Delta_(h_i)a_1 in E_1.        (3)
```

Every element of `K<d_1,...,d_s>_delta` is meromorphic.  Its common `T_1,T_2` fixed field is `C` by
the dense-period argument.  Since `K(z)` is differential algebraic over both `K` and `C(z)`, the
hypothetical dependence may be read over `K`.

Apply the several-translation additive telescoping theorem to the compatible unipotent system (3).
There exist operators

```text
A_1,...,A_s in C[delta], not all zero,
```

and one `g in K` satisfying simultaneously

```text
T_1 g-g=sum_i epsilon_1 A_i(Delta_(h_i)a_2),
T_2 g-g=sum_i epsilon_2 A_i(Delta_(h_i)a_1).       (4)
```

The fact that one `g` satisfies both equations is essential; unrelated one-operator primitives
would not descend to a single cylinder.

## Proof: the shifted cotangent pole separates every coset

Specialize the `E_1` factor of `K=Frac(E_1 tensor_C E_2)` outside the numerator and denominator
exceptional loci of `g`.  Translation by `omega_1` acts on

```text
X=exp(2 pi i z/omega_2)
```

as `X |-> qX`, where

```text
q=exp(2 pi i omega_1/omega_2)
```

is not a root of unity.  The first equation of (4) becomes

```text
u(qX)-u(X)=sum_i A_i(b(r_i X)-b(X)),                (5)
```

for a rational `u in C(X)`, where

```text
b(X)=c (X+1)/(X-1),   c!=0,
r_i=exp(2 pi i h_i/omega_2).
```

The term `b(r_iX)-b(X)` has poles at `X=r_i^(-1)` and `X=1`.  Its shifted pole satisfies

```text
r_i^(-1) in q^Z
  iff h_i in Z omega_1+Z omega_2=H,                   (6)
```

and two shifted poles lie in the same `q^Z`-orbit exactly when `h_i-h_j in H`.  Thus the selected
nonzero cosets determine pairwise distinct pole orbits, all distinct from the orbit of `1`.

Let `N` be the largest differential order among the `A_i`, and choose `i_0` whose order-`N`
coefficient is nonzero.  In the coordinate `X`, the derivation is a nonzero scalar multiple of
`X d/dX`.  It is nonvanishing at `r_(i_0)^(-1)`, so the top derivative in `A_(i_0)` produces a
nonzero pole of order `N+1` there.  No lower derivative cancels it, and no other summand in (5) has
a pole anywhere in that `q^Z`-orbit.

For every rational `u`, each fixed-order principal-part coefficient of `u(qX)-u(X)` has zero sum
over every `q^Z`-orbit: the sum is finite and telescopes.  The right side of (5) has one nonzero
order-`N+1` coefficient on the orbit of `r_(i_0)^(-1)`.  This contradicts (5), proves joint
differential independence, and establishes the lower bound in (2).

## Full translate and operator matroid

The abstract theorem `atomic-defect-full-orbit-differential-matroid` now applies with

```text
f=L_2,
G=C/H.
```

The quotient `G` is infinite.  Hence, for any distinct classes `g_1,...,g_n in C/H`, the translates

```text
L_2(z+g_1),...,L_2(z+g_n)
```

are differentially algebraically independent over `C(z)`.

More generally, let

```text
A=C[delta][C/H]
```

be the finite-support differential group algebra.  For every finite `D_1,...,D_m in A`,

```text
dtrdeg_(C(z)) C(z)<D_1L_2,...,D_mL_2>_delta
  =dim_(C(delta)) span{D_1,...,D_m}.                    (7)
```

Thus there are no hidden nonlinear differential relations among arbitrary translation
superpositions beyond their constant-coefficient operator rank.

## Attacks and boundaries

1. **Commensurable periods.** If `omega_1/omega_2 in Q`, the `q`-orbit is finite and the dense common
   fixed-field argument fails.  This matches the differential-algebraicity theorem of
   Kurokawa--Wakayama for rational period vectors.
2. **Complex-period theorem.** Kato proves hypertranscendence when a period ratio is non-real.  That
   theorem does not cover the positive real irrational regime here and does not state the defect
   spectrum or finite-family matroid.
3. **Several-translation dependency.** The proof inherits the independent-audit obligation of the
   simultaneous additive telescoping theorem.  A one-translation criterion is insufficient because
   its periodic constant field is nontrivial.
4. **Meromorphic category.** Dense-period constancy and rational-cylinder specialization use actual
   meromorphic functions, not formal solutions.
5. **Lean closure.** The local tree now constructs the genuine meromorphic double-sine source on
   every positive imaginary-ray frame with irrational ratio, proves exact orbit independence and
   same-coset differential algebraicity, and packages the defects as the pointed period-class
   collision matroid over `ℂ(z)`.  Its rank is the number of distinct nonzero classes.  A separate
   rational-base operator theorem proves the exact `ℂ(δ)` row rank of every finite separated
   differential-translation superposition, closing the group-algebra clause without assuming a
   telescoper or an abstract source.

## Parent-theory and literature gate

- Kurokawa--Wakayama, *Differential Algebraicity of Multiple Sine Functions*, Lett. Math. Phys. 71
  (2005), 75--82, proves DA for rational/commensurable periods.
- Kato, *Hypertranscendence of the Multiple Sine Function for a Complex Period*, Proc. Japan Acad.
  Ser. A 95 (2019), 16--19, proves HT when some period ratio is non-real.
- Kurokawa--Koyama and Onodera supply the standard multiple-sine definition, functional equations,
  and Weierstrass products.
- Hardouin--Singer supplies the several-automorphism parameterized Picard--Vessiot parent.
- Multiplicative orbital residues and rational `q`-summability supply the pole-orbit obstruction.

Searches for the exact DA spectrum, arbitrary translation-defect independence, positive-real
irrational double-sine HT, and a full nonlinear translation matroid located no equivalent or
stronger theorem.  This is a preliminary result only; independent experts must audit both proof and
priority before scientific-novelty promotion.

## Gates

- [x] exact defect-coset statement formulated
- [x] zero-coset and same-coset upper bound proved
- [x] simultaneous paired telescoping reduction proved
- [x] cylinder specialization and coset/pole-orbit equivalence proved
- [x] highest-principal-part obstruction proved for an arbitrary finite family
- [x] full translate and differential group-algebra matroid deduced
- [x] preliminary exact/equivalent/stronger literature search
- [ ] independent audit of the several-translation telescoper in this specialization
- [ ] independent specialist proof and novelty audit
- [x] unconditional analytic formalization in Lean
- [x] 2 -> 3: exact defect matroid, nonzero-coset rank, and finite operator-row rank formalized in
  `GaloisForLFunctions.HTGeometry.DoubleSineDefectCosetMatroid`
