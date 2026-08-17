# Balanced context-order globality fracture

Status: `[LITERATURE] [PAPER-PROVED] [NOVELTY UNVERIFIED]`

Source: Maciej Nowicki and Artificial Hyperintelligence Eve, *Locally Quantum, Globally
Non-Hilbertizable* (Zenodo 21982163, 2026), Theorem 5.2 and Corollary 5.3.  This card records an
independent dependency-closed proof in the representation already available in the local corpus.

## Exact claim

For every `r : ℕ`, put

```text
N = r + 3,
t = 2 / (2N - 3),
δ = 1 / (2N - 3),
C_N(i,j) = if i = j then 1 else -t.
```

Then:

1. every codimension-one principal restriction of `C_N` is positive semidefinite;
2. `C_N` is not positive semidefinite;
3. the local and global spectral margins on the constant line are exactly `+δ` and `-δ`;
4. the transverse eigenvalue is `1+t` at both levels;
5. therefore increasing the number of contexts produces an unconditional genuine anomaly at every
   order `N ≥ 3`, with equal local and global margins.

The theorem has no source, genericity, probability, physical, or spectral hypotheses.  `r` merely
indexes an explicit finite matrix family.

## Paper proof

For a nonempty finite index set `I` of cardinality `m`, let `J` be the all-ones matrix and
`P = J/m` the orthogonal projection onto the constant line.  The corpus already proves that `P` and
`1-P` are positive semidefinite orthogonal projections.  Direct entrywise algebra gives

```text
C_m(t) = (1+t)(1-P) + (1-(m-1)t)P.                 (1)
```

Indeed, `mP=J`, so the right side is

```text
(1+t)1 + ((1-(m-1)t)-(1+t))P
= (1+t)1 - mt P
= (1+t)1 - tJ,
```

which has diagonal `1` and off-diagonal entry `-t`.

For a codimension-one face, `m=N-1`.  With `t=2/(2N-3)`,

```text
1-(m-1)t = 1-(N-2)t = 1/(2N-3) = δ > 0.
```

Both coefficients in (1) are positive, hence every codimension-one restriction is positive
semidefinite.  Since all such restrictions have the same equality-pattern kernel, reindexing by any
injection gives exactly this matrix.  Every smaller face is a principal restriction of one of these
maximal proper faces and is therefore positive semidefinite as well.

For the full set, `m=N`, and

```text
1-(N-1)t = -1/(2N-3) = -δ.
```

The constant section is killed by `1-P` and fixed by `P`, so its quadratic value under `C_N` is
`-δ` times its positive squared norm.  Thus `C_N` is not positive semidefinite.  On the orthogonal
complement `P` vanishes and `1-P` is the identity, giving transverse eigenvalue `1+t`.  This proves
all five clauses.

## Hostile audit

- No eigenvalue ordering, numerical diagonalization, or unproved spectral lemma is used.
- Denominator `2N-3` is positive because `N=r+3`, so it is at least three.
- Arbitrary codimension-one restrictions are covered because injections preserve equality and the
  kernel depends only on equality of indices.
- Proper lower-dimensional faces inherit positivity by principal compression.
- This is established matrix theory and is not claimed as local novelty.  Its value is as the exact
  quantitative PSD layer missing from the corpus's stronger synchronization and fact-descent laws.

## Lean target

Formalize the balanced family, exact projector decomposition, all codimension-one restrictions,
local positivity, constant/transverse actions, and global non-positivity.  Reuse
`SimplexEffectiveHarmonic`; introduce no axioms or conditional source assumptions.
