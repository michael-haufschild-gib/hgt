# Periodic-pencil dimension is matrix rank plus one rational-kernel bit

- **ID:** `periodic-pencil-matrix-rank-formula`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / EXACT HT CONSTRAINT-DIMENSION FORMULA
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The periodic-pencil dimension of every finite essential simplicial complex is the
  minimum, over its admissible facet-evaluation matrices, of complex matrix rank plus a correction
  of one exactly when the matrix has a nonzero rational kernel.

## Setup

Let `Delta` be a finite simplicial complex on a nonempty essential vertex set `V`, with finite
facet set `A=Fac(Delta)`. A matrix

```text
M=(m_(A,v)) in C^(A times V)                                (1)
```

is **PP-admissible** when, for every facet `A`,

```text
m_(A,v) in Z                         for v notin A,          (2)
{1} union {m_(A,v):v in A} is Q-linearly independent.      (3)
```

Write

```text
K_Q(M)={q in Q^V:M q=0 in C^A},                             (4)
epsilon_Q(M)=0 if K_Q(M)={0}, and 1 otherwise.              (5)
```

The periodic-pencil dimension `ppDim(Delta)` is defined in
`periodic-pencil-intrinsic-ht-dimension-two.md`: it is the least `d` for which there are globally
`Q`-independent translation vectors `a_v in C^d`, nonzero forms `ell_A`, and nonzero periods
`omega_A` satisfying

```text
ell_A(a_v)/omega_A in Z                    for v notin A,
{1} union {ell_A(a_v)/omega_A:v in A}      Q-linearly independent.       (6)
```

## Exact matrix formula `[PROVED HERE]`

```text
ppDim(Delta)
 =min_(M PP-admissible) (rank_C M+epsilon_Q(M)).             (7)
```

### From a periodic pencil to a matrix

Let pencil data in `C^d` be given. Choose coordinates and form the matrices

```text
B=(a_v)_(v in V) in C^(d times V),
U=(ell_A/omega_A)_(A in Fac(Delta)) in C^(A times d).        (8)
```

Then

```text
M=U B,   m_(A,v)=ell_A(a_v)/omega_A                         (9)
```

is PP-admissible. Put `r=rank_C M`. If `r<d`, then

```text
r+epsilon_Q(M)<=r+1<=d.                                    (10)
```

If `r=d`, the map represented by `U:C^d->C^A` has rank `d` and is injective. For
`q in K_Q(M)`, equation (9) gives `U(Bq)=0`. Injectivity of `U` gives `Bq=0`, and the global
`Q`-independence of the columns `(a_v)` gives `q=0`. Hence `epsilon_Q(M)=0`, so again

```text
rank_C M+epsilon_Q(M)<=d.                                  (11)
```

Taking the minimum over pencil data proves that the right side of (7) is at most
`ppDim(Delta)`.

### From a matrix to a periodic pencil

Let `M` be PP-admissible and put `r=rank_C M`. Choose a rank factorization

```text
M=U B,
U in C^(A times r) injective,
B in C^(r times V).                                        (12)
```

Because `U` is injective,

```text
ker_C B=ker_C M,
ker_Q B=K_Q(M).                                             (13)
```

If `epsilon_Q(M)=0`, the columns `b_v` of `B` are `Q`-linearly independent. Take

```text
a_v=b_v in C^r,
ell_A=the A-th row of U,
omega_A=1.                                                  (14)
```

Each row of `M` is nonzero by (3), so every `ell_A` is nonzero. Equations (2)--(3) become exactly
the periodic-pencil conditions (6). Thus `ppDim(Delta)<=r`.

Suppose `epsilon_Q(M)=1`. Choose an injection `nu:V->N` and one transcendental number `tau`. The
numbers

```text
c_v=tau^(nu(v))                                             (15)
```

are `Q`-linearly independent. Define

```text
a_v=(b_v,c_v) in C^(r+1),
ell_A=(U_A,0),
omega_A=1.                                                  (16)
```

The evaluations remain `ell_A(a_v)=m_(A,v)`, so (2)--(3) remain true. If
`sum_v q_v a_v=0` with rational `q_v`, the last coordinate gives

```text
sum_v q_v tau^(nu(v))=0.
```

Transcendence of `tau` forces every `q_v=0`. Hence the translation vectors in (16) are globally
`Q`-independent and `ppDim(Delta)<=r+1`.

Both cases give

```text
ppDim(Delta)<=rank_C M+epsilon_Q(M).                        (17)
```

Taking the minimum over PP-admissible matrices and combining with (11) proves (7). `QED`

## Existence of the minimum and consequences

PP-admissible matrices exist. Give `C^V` its coordinate basis `(e_v)`. For each facet choose
numbers `(theta_(A,v))_(v in A)` such that

```text
{1} union {theta_(A,v):v in A}
```

is `Q`-linearly independent, and set the other row entries to zero. The resulting matrix is
PP-admissible. Its cost is a natural number at most `|V|`, because the construction itself is a
periodic-pencil realization in `C^|V|`. Thus the minimum in (7) is attained.

The formula reveals that periodic-pencil dimension has exactly two layers:

```text
complex geometric cost = rank_C M,
arithmetic lifting cost = epsilon_Q(M) in {0,1}.             (18)
```

No larger correction can occur. A complex rank factorization already supplies all analytic
directions except possibly the one direction needed to make the translation columns rationally
faithful.

Together with the faithful-separation comparison and the two universal constructions,

```text
ppDim(Delta)<=ffsDim(Delta)
            <=min(|V|,|Fac(Delta)|).                        (19)
```

The dimension-one phase law becomes the rank-one boundary of (7): for a nonempty essential
complex, `ppDim(Delta)=1` exactly when every facet complement has cardinality at most one.

## Scientific meaning

The contributing rank-factorization and transcendental-power arguments are standard. The
candidate-new content is the exact geometric formula (7): a facetwise periodic constraint
geometry is controlled by complex row rank together with one, and only one, rational-kernel bit.
This converts `ppDim` from an existential analytic definition into an explicit matrix invariant.

For an RH-facing prime-translation model, (7) gives a positive design requirement. A proposed
prime-indexed relation geometry must exhibit an admissible facet-evaluation matrix; its analytic
dimension is then forced by the complex rank of that matrix, with one extra coordinate precisely
when the rank factorization loses rational faithfulness. This does not assert that `zeta` realizes
the matrix or the associated full differential matroid.

## Parent-theory and novelty boundary

Rank factorization, rational-kernel lifting, toric arrangements, gain-labelled affine
arrangements, and arithmetic matroids are established parents. De Concini--Procesi describe toric
arrangements as periodic generalizations of hyperplane arrangements, while arithmetic and elliptic
matroids retain lattice or endomorphism-ring multiplicities. No checked source states the
facet-indexed minimum (7), its single-bit correction, or its equality with the analytic
periodic-pencil realization dimension.

Closest primary sources checked:

1. C. De Concini and C. Procesi, *On the geometry of toric arrangements*,
   `https://arxiv.org/abs/math/0505351`.
2. L. Moci, R. Pagaria, M. Pismataro, and A. Vargas, *Elliptic arrangements of complex
   multiplication type*, `https://arxiv.org/abs/2506.19638`.

Novelty remains provisional pending independent comparison with toric-arrangement representation
ranks, arithmetic matroids, gain graphs, and matroids over endomorphism rings.

## Lean certificate

Formalized in `formal/GaloisForLFunctions/HTGeometry/PPMatrixRankFormula.lean` and
`formal/GaloisForLFunctions/HTGeometry/PPMatrixRankFormulaConsequences.lean`:

- `PPAdmissible`, `epsQ`, `matrixCost`, and `ppDim` formalize the admissible matrix, rational-kernel
  bit, matrix minimum, and periodic-pencil realization minimum;
- `config_to_cost` proves the pencil-to-matrix inequality;
- `M_to_config` proves the matrix-to-pencil construction in both rational-kernel cases, using one
  transcendental-power coordinate exactly when required;
- `ppDim_eq_matrixCost` is the exact rank-plus-bit formula;
- `exists_ppAdmissible` and `matrixCost_attained` prove existence and attainment of the minimum;
- `epsQ_le_one`, `ppDim_le_card`, and `matrixCost_le_card` formalize the single-bit correction and
  the universal vertex-count upper bound.

Both modules elaborate directly and their dedicated target passes.  Axiom audits of the exact
formula, both inequalities, existence, and attainment use only `propext`, `Classical.choice`, and
`Quot.sound`.

## Gates

- [x] PP-admissible matrix defined
- [x] pencil-to-matrix inequality proved
- [x] matrix-to-pencil construction proved in both rational-kernel cases
- [x] existence and attainment of the minimum proved
- [x] exact matrix formula proved unconditionally on paper
- [x] geometric, arithmetic, and analytic contributions separated
- [x] preliminary parent-theory audit
- [x] complete unconditional Lean formalization before stage 3
