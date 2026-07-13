# Support-cardinality boundary jets do not determine prime-word Young shape

- **ID:** `prime-word-young-shape-boundary-blindness`
- **Stage:** 3-formalized
- **Type:** `THEOREM (Lean) / [NO-GO] [POSITIVE FULL-WORD REPAIR] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeWordYoungShapeNoGo.lean`
- **Consumer:** `../../1-in-progress/prime-theta-young-thoma-schur-rh.md`

## Theorem

The multiplicities of the letters in a length-`n` prime word form a partition of `n`.  Lean defines
this partition using mathlib's `Nat.Partition.ofSym`.

The words

```text
w_31 = [0,0,0,1],
w_22 = [0,0,1,1]
```

have the same distinct-letter support `{0,1}`.  Their unit singleton ensembles therefore have
identical one-variable marked deformations and identical boundary jets of every order.  Their
multiplicity partitions are nevertheless different:

```text
lambda(w_31) = [3,1],
lambda(w_22) = [2,2].
```

Thus neither the support set nor the complete support-cardinality boundary germ determines the
Young shape required by the Edrei--Thoma route.

## Positive repair

The full word canonically determines its multiplicity partition.  A Young-graph source producer
must therefore preserve the full prime word through

```text
word -> multiplicity counts -> Nat.Partition,
```

and only then aggregate weights by shape.  The scalar boundary germ may grade the number of rows,
but it cannot replace the partition.

Lean also proves the complete exact Young-graph branching rule.  If `x` is a prime label not
occurring in `w`, then

```text
parts(lambda(x::w)) = 1 :: parts(lambda(w)).
```

Thus insertion of a fresh prime letter adds precisely one new one-box row.  The complementary
case is equally exact: if `x` occurs `k` times in `w`, then

```text
parts(lambda(x::w)) = (k+1) :: (parts(lambda(w)).erase(k)).
```

Thus every letter insertion adds one box to exactly one row: a new row for a fresh letter and the
row carried by `x` for a repeated letter.  What remains open is not the combinatorial Young edge,
but the completed positive weight balance after all labelled preimages of an unlabelled shape are
aggregated.

The squarefree boundary is also classified exactly:

```text
parts(lambda(w)) = [1,1,...,1]  <->  w has no repeated label.
```

Consequently the positive squarefree Bernoulli law in `MobiusFiniteSchurTransfer.lean` occupies
precisely the pure-column boundary of the Young graph.  This is both a no-go and a positive source
theorem: squarefree Möbius amplitudes alone cannot generate shapes with a row of length at least
two, while their entire surviving sector already has the correct column positivity.  Repeated
prime powers are exactly the missing row-lengthening data.

## Formal certificate

The module proves:

- `primeWordMultiplicityPartition`;
- `multiplicityWords_support_eq`;
- `multiplicityEnsemble_deformation_eq`;
- `multiplicityWord31_partition_parts`;
- `multiplicityWord22_partition_parts`;
- `multiplicityWords_partition_ne`;
- `boundaryGerm_blind_to_multiplicityPartition`;
- `primeWordMultiplicityPartition_cons_fresh_parts`;
- `primeWordMultiplicityPartition_cons_existing_parts`;
- `primeWordMultiplicityPartition_parts_eq_replicate_one_of_nodup`;
- `primeWordMultiplicityPartition_parts_eq_replicate_one_iff_nodup`.

The exact module build is green.  Axiom audits report only `propext`, `Classical.choice`, and
`Quot.sound`.

## Gates

- [x] full-word multiplicity partition defined
- [x] equal support and complete scalar germ proved
- [x] `[3,1]` versus `[2,2]` partition separation proved
- [x] positive full-word repair formalized
- [x] fresh-letter one-box Young branching formalized
- [x] repeated-letter row-lengthening branch formalized
- [x] squarefree words classified exactly as pure Young columns
- [ ] completed positive weight balance over labelled preimages
- [x] accepted-axiom audit
