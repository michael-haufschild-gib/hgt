# CO6 involution host caveat

- **Stage:** 3-formalized
- **Status:** fully proven on paper; formalized in Lean 4
- **Type:** formula-graph guardrail
- **Formula node:** `CO6`, `g_p=g_p^{-1} => g_p=+-1`
- **Random-node source:** ligand/cofactor-stabilized symmetry in protein folding

## Claim

The implication

```text
g = g^{-1}  =>  g = +-1
```

is a scalar/connected-host statement. It is valid in a field, and more generally in a
commutative ring with no idempotents except `0,1` and with `2` invertible. It is not
stable under product-sector or projector extensions of the coefficient host.

Equivalently, in a commutative ring `R` with `2` invertible, self-inverse units are
the same data as idempotents:

```text
{g in R^x : g^2=1}  <->  {e in R : e^2=e}
g = 2e - 1,         e = (g+1)/2.
```

Therefore `g^2=1` forces only global `+-1` exactly when the coefficient host is
connected in this idempotent sense.

## Proof

If `e^2=e`, then

```text
(2e-1)^2 = 4e^2 - 4e + 1 = 1,
```

so `g=2e-1` is self-inverse.

Conversely, if `g^2=1` and `2` is invertible, set `e=(g+1)/2`. Then

```text
e^2 = (g^2+2g+1)/4 = (1+2g+1)/4 = (g+1)/2 = e.
```

The two constructions are inverse. Hence nontrivial idempotents give nontrivial
self-inverse units.

For example, in `C x C`,

```text
g=(1,-1),       g^2=(1,1),
```

but `g` is neither global `+1` nor global `-1`. In a matrix/projector host, any
nontrivial projector `P` gives an involution

```text
g = 2P - I,
```

which satisfies `g^2=I` but need not equal `+-I`.

## Consequence for CO6

The CO6 guardrail used in prime-side orthogonality must keep the coefficient host
fixed as scalar/connected, or explicitly prohibit hidden product sectors/projectors.

Otherwise one can manufacture a fake self-duality by adding a cofactor-like sector:
the equation `g=g^{-1}` is then solved sectorwise, not globally. This does not
invalidate the existing prime-side orthogonality result over the intended scalar
host, but it forbids using CO6 without stating the host condition.

## Computation

The workflow test used the protein-folding NODE "metal ions/cofactors/ligands can
stabilize symmetry that the apo protein does not maintain." A toy apo/holo energy
showed symmetry restored only after adding a stabilizing cofactor term. The transfer
then tested scalar, matrix-projector, and product-ring coefficient hosts.

Artifact:

```text
computations/2026-06-21-penrose-formula-co6-cofactor-idempotents.py
computations/2026-06-21-penrose-formula-co6-cofactor-idempotents.txt
```

The extreme cases were:

```text
R=C^1: 2 self-inverse units, no non-global signs.
R=C^2: 4 self-inverse units, 2 non-global signs.
R=C^3: 8 self-inverse units, 6 non-global signs.
R=C^4: 16 self-inverse units, 14 non-global signs.
```

This is the exact coefficient-host analogue of cofactor-stabilized symmetry: the
added host component can create symmetry that the original scalar host does not
maintain.

## Lean formalization

Module: `formal/GaloisForLFunctions/HTGeometry/InvolutionIdempotentHost.lean`
(namespace `GaloisForLFunctions.HTGeometry`).

| Paper statement | Lean declaration |
|---|---|
| `e^2=e  =>  (2e-1)^2=1` | `hostInvolutionOfIdempotent_mul_self` |
| `g^2=1, 2 invertible  =>  (g+1)/2` idempotent | `hostIdempotentOfInvolution_isIdempotentElem` |
| the two constructions are mutually inverse | `hostIdempotentOfInvolution_hostInvolutionOfIdempotent`, `hostInvolutionOfIdempotent_hostIdempotentOfInvolution` |
| `{g : g^2=1} <-> {e : e^2=e}` | `involutionEquivIdempotent` |
| `2e-1 = 1 <=> e = 1`, `2e-1 = -1 <=> e = 0` | `hostInvolutionOfIdempotent_eq_one_iff`, `hostInvolutionOfIdempotent_eq_neg_one_iff` |
| connected host: only `0,1` idempotent `=> g = +-1` | `eq_one_or_neg_one_of_mul_self_eq_one` |
| field / no zero divisors case | `isIdempotentElem_eq_zero_or_one`, `eq_one_or_neg_one_of_mul_self_eq_one_of_noZeroDivisors` |
| nontrivial idempotent manufactures a non-global sign | `exists_mul_self_eq_one_ne_one_ne_neg_one_of_idempotent` |
| `C x C` witness `g=(1,-1)` | `prod_sign_mul_self`, `prod_sign_ne_one`, `prod_sign_ne_neg_one`, `isIdempotentElem_prod_left`, `hostInvolutionOfIdempotent_prod_left` |

The matrix/projector host of the card is the special case of
`exists_mul_self_eq_one_ne_one_ne_neg_one_of_idempotent` at a proper projector `P`, whose attached
self-inverse element is `2P - I`.

Audit: direct `lake env lean` check clean, targeted module build clean, umbrella import wired,
`#print axioms` on every declaration above returns only `propext`, `Classical.choice`, `Quot.sound`.
