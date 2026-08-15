# CCM Guinand--Weil finite atomic prime-entry connection

- **Status:** LEAN-FORMALIZED
- **Lane:** CCM-FU / atomic BV connection
- **Novelty scope:** corpus-new finite aggregate factorization and unconditional visible-cutoff
  negative orientation
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCMGuinandWeilPrimeEntryAtomicConnection.lean`

## Universal matrix direction

For a finite index set `S`, define cumulative scalar rate and event tangent

```text
R_S=sum_(k in S) -4 criticalMellinAtomWeight(k)/log(k),
T_(S,N)=sum_(k in S) T_(k,N).                                  (1)
```

Every single-event tangent already lies on the same constant-boundary projector. Lean proves the
aggregate identity

```text
T_(S,N)=R_S vecMulVec(e,e).                                    (2)
```

Thus arbitrary finite arithmetic complexity changes only one scalar coefficient. The whole atomic
matrix direction is aperture- and prime-independent.

## Unconditional visible-cutoff orientation

For every `k>1`, von-Mangoldt nonnegativity implies its event rate is nonpositive; composite
indices automatically contribute zero. Hence for every finite set above one,

```text
v^T T_(S,N) v=R_S (sum_i v_i)^2 <= 0,
rank(T_(S,N))<=1.                                               (3)
```

Specializing `S` to the literal visible set

```text
{2,...,floor(exp(2a))}                                         (4)
```

gives `(3)` for every real aperture without a prime-power classification premise.

## CCM-FU consequence

Finite atomic part of desired aperture connection is completely classified: one scalar negative
Stieltjes event stream times fixed rank-one constant-boundary projector. Remaining construction is
the continuous pole/Gamma connection and its weld to centered continued Xi Ward transport.

## Lean declarations

- `ccmGuinandWeilPrimeEntryAtomicRate`
- `ccmGuinandWeilPrimeEntryAtomicTangent`
- `ccmGuinandWeilPrimeEntryAtomicTangent_eq_rankOne`
- `ccmGuinandWeilPrimeEntryMatrixRate_nonpos`
- `ccmGuinandWeilPrimeEntryAtomicRate_nonpos`
- `ccmGuinandWeilPrimeEntryAtomicTangent_quadratic`
- `ccmGuinandWeilPrimeEntryAtomicTangent_quadratic_nonpos`
- `ccmGuinandWeilVisiblePrimeEntryAtomicTangent`
- `ccmGuinandWeilVisiblePrimeEntryAtomicTangent_quadratic_nonpos`
- `ccmGuinandWeilPrimeEntryAtomicTangent_rank_le_one`

Targeted direct Lean check and `lake build
GaloisForLFunctions.RHTower.CCMGuinandWeilPrimeEntryAtomicConnection` pass. Principal
`#print axioms` reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
