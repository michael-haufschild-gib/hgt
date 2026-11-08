# A filtered two-prime normal form for weighted chains

- **ID:** esg-two-prime-weighted-normal-form
- **Stage:** 0-backlog
- **Type:** FILTERED CHAIN NORMAL FORM
- **Status:** CONJECTURE; paper and novelty audits required

## Target

Over every commutative ring, the prime-valued exterior boundary should be
filtered-chain-isomorphic to the boundary supported only at vertices two and
three, with coefficients two and three. The isomorphism should commute with
height inclusions and canonical coefficient extension.

For a prime support `S` omitting two and three, of product `m` and cardinality
`k`, the resulting block has generators at heights

| Generator | Exterior degree | Birth |
|---|---:|---:|
| `S` | `k` | `m` |
| `e₂∧S` | `k+1` | `2m` |
| `e₃∧S` | `k+1` | `3m` |
| `e₂∧e₃∧S` | `k+2` | `6m` |

Its nonzero differentials have coefficients `2,3` and `(-3,2)`.
This would classify the actual filtered chain complex, beyond its integral
homology functor.

## Candidate mechanism

Put `u=e₃−e₂`. Let `ψ(e₂)=ψ(e₃)=0` and `ψ(e_p)=p` for primes `p≥5`.
The vertex maps `A=id−uψ` and `A⁻¹=id+uψ` are inverse because `ψ(u)=0`.
They fix the two smallest prime vertices and kill the remaining boundary
coefficients under conjugation.

The proposed exterior formulas are `ΛA=id−u∧ι_ψ` and
`ΛA⁻¹=id+u∧ι_ψ`. Deleting a vertex with nonzero `ψ` lowers product height
by at least five; adjoining `u` costs at most three. These formulas should
therefore preserve every cutoff in both directions. The exterior identity,
filtered comparison, direct-sum blocks and coefficient naturality all require
proof and Lean audits.

## Expected consequences

For arbitrary coefficients `R`, the first homology branch is `R` on `[m,2m)`,
then `R/2R` on `[2m,3m)`, with reduction at the transition. The second branch
is `Ann_R(2)` on `[2m,3m)`, then `R` on `[3m,6m)`, with the annihilator's
inclusion at the transition.

Over `ℤ` this recovers the integral weighted-persistence classification. Over `𝔽₂`
it predicts intervals `[m,3m)` and `[2m,6m)` in consecutive exterior degrees.
The latter joins a universal-coefficient torsion contribution to a later
integral free class, so an objectwise universal-coefficient splitting should
fail to be natural in height. These are conjectural consequences until the
chain normal form and actual comparisons are formalized.

## Scope

No Euler-cancellation estimate or arithmetic height sign follows from a chain
normal form alone. Novelty must be checked against weighted simplicial homology
and filtered Koszul decompositions before claiming an arithmetic contribution.
