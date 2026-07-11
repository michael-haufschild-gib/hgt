# HT as an infinite additive-torsor staircase

- **ID:** `ht-infinite-additive-torsor-staircase`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[STRUCTURAL REFORMULATION] [PROVED HERE] [NOT CLAIMED NEW]`
- **Lane:** general hypertranscendence; derivative-shadow field geometry
- **Statement:** A function is HT exactly when every successive derivative-shadow extension is a nontrivial primitive additive torsor.

## Goal

Give a field-geometric picture of the landscape separating DA and HT functions. This is deliberately not claimed as new scientific knowledge: it is an exact repackaging of differential transcendence that makes the separate autonomous-cap theorem intelligible.

## Derivative-shadow tower

For every meromorphic function `u` and `k>=0`, put

`D_k(u)=C(z)<u^(k)>`

and

`epsilon_k(u)=trdeg_(D_(k+1)(u)) D_k(u).`

Since

`D_k(u)=D_(k+1)(u)(u^(k))`

and the derivative of `u^(k)` already lies in `D_(k+1)(u)`, every `epsilon_k(u)` lies in `{0,1}`.

When `epsilon_k(u)=1`, the maps

`u^(k) |-> u^(k)+c`, `c in C`,

extend to differential automorphisms fixing `D_(k+1)(u)`. Thus the step is a primitive `G_a`-torsor in the function-field sense.

## Characterization

`[STRUCTURAL REFORMULATION] [PROVED HERE]` A meromorphic function `u` is HT over `C(z)` if and only if

`epsilon_k(u)=1`

for every `k>=0`.

If `u` is HT, no derivative `u^(k)` can be algebraic over its higher-derivative field. Any such algebraic relation uses only finitely many higher derivatives and is an ADE for `u`.

Conversely, suppose `u` is DA and put

`r_k(u)=trdeg_(C(z)) D_k(u).`

Every `r_k(u)` is finite and

`r_k(u)=r_(k+1)(u)+epsilon_k(u).`

If every `epsilon_k(u)` were one, the nonnegative integers `r_k(u)` would decrease strictly forever. This is impossible. Hence some derivative-shadow step is algebraic.

Therefore:

- a DA function has a finite binary derivative-shadow staircase and only finitely many strict primitive steps;
- an HT function has the infinite all-ones staircase.

## Use

The separate bridge theorem `2-fully-proven/not_new_scientific_knowledge/autonomous-cap-derivative-shadow-law.md` proves that an autonomous first-order entire cap acts exactly on the first step of this staircase: it adds one outer state and removes the inner primitive defect from the rank count.

The distinction matters because a scalar label such as `ord_DA(u)` records only the total finite height. It cannot distinguish a primitive additive state from a state already algebraically visible in the derivative shadow.

## Anti-theatre gate

- The equivalence with HT is a repackaging, not a new transcendence theorem.
- The `G_a` language adds geometry but no new implication by itself.
- Novelty, if any, belongs to a nontrivial operation law on this staircase, not to renaming the defining algebraic independence.

## Gates

- [x] Complete paper proof.
- [x] Separated from candidate-new-knowledge claims.
- [ ] Formalization deferred with the surrounding derivative-shadow program.
