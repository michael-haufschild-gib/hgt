# Induced-character degree equals subgroup index times degree

- **ID:** `artin-induced-character-degree-index`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Status:** `[LITERATURE] [PAPER-PROVED] [LEAN-PROVED] [BRIDGE]`

## Exact claim

Let `G` be a finite group, `H <= G`, and let `rho` be a finite-dimensional complex
representation of `H` on `V`. Then

```text
dim_C Ind_H^G(rho) = [G:H] * dim_C V.
```

Equivalently, the character of the actual induced representation satisfies

```text
char(Ind_H^G(rho))(1) = [G:H] * dim_C V.
```

For a complex linear character `chi : H -> C^x`, this specializes to

```text
monomialCharacter(G,H,chi)(1) = [G:H].
```

## Paper proof

The coinduced carrier consists of functions `f : G -> V` satisfying

```text
f(hg) = rho(h) f(g)  for h in H, g in G.
```

Choose one representative `r_q` of each right coset `q in H\G`. Evaluation

```text
f |-> (f(r_q))_q
```

is a complex-linear map from the coinduced carrier to the product of one copy of `V` per right
coset. Its inverse sends a tuple `(v_q)` to the function

```text
hg = h r_q |-> rho(h) v_q.
```

Existence and uniqueness of `h` follow from equality of right cosets; the displayed rule is
therefore well-defined. The two maps are inverse by evaluation at representatives and the
equivariance relation. Hence

```text
Coind_H^G(rho) ~= product_{H\G} V
```

as complex vector spaces. The quotient has `[G:H]` elements, so its dimension is
`[G:H] * dim_C V`.

For finite-index subgroups, induction and coinduction are isomorphic representations. Their
underlying vector spaces therefore have equal dimension, proving the first formula. Character at
the identity equals representation dimension, giving the second. A linear character acts on the
one-dimensional space `C`, so its dimension is one and the monomial specialization follows.

## Hostile audit

- No induced-character sum formula is assumed.
- No choice of representatives affects the dimension or final equality.
- Finiteness of `G` supplies finite quotient and finite-dimensional coinduced carrier.
- The argument uses the actual coinvariant induction and actual equivariant-function coinduction.
- This is a classical theorem, not new scientific knowledge.

## Lean target

Construct the right-coset evaluation linear equivalence for `Representation.coindV`, combine it
with `Rep.indCoindIso`, prove the finrank and identity-character formulas, and specialize to
`monomialGenuineCharacter`. No `sorry`, `admit`, new axiom, `opaque`, `unsafe`, or
target-equivalent proposition interface.

## Lean formalization

Module:

```text
formal/GaloisForLFunctions/RHTower/ArtinInducedDegree.lean
```

Exported results:

- `coinducedRightCosetEquiv`: explicit right-coset evaluation linear equivalence.
- `coinduced_finrank_eq_index_mul`: coinduced dimension formula.
- `induced_finrank_eq_index_mul`: induced dimension formula via `Rep.indCoindIso`.
- `induced_character_one_eq_index_mul`: induced-character degree formula.
- `monomialGenuineCharacter_one_eq_index`: genuine monomial degree equals subgroup index.
- `monomialVirtualCharacter_one_eq_index`: underlying virtual monomial degree equals index.

Verification on 2026-08-14:

- direct source check: `lake env lean GaloisForLFunctions/RHTower/ArtinInducedDegree.lean` passed;
- targeted audit: `lake build GaloisForLFunctions.RHTower.ArtinInducedDegree` passed;
- axiom audit for every exported result: only `propext`, `Classical.choice`, and `Quot.sound`;
- imported by `formal/GaloisForLFunctions/RHTower.lean`; umbrella build intentionally not run.
