# Exact arithmetic gap cost

- **ID:** completed-arithmetic-forms-irregular-green
- **Stage:** 3-formalized
- **Type:** THEOREM

## Statement

Let `0=k₀<k₁<…<k_N=Q` be integer nodes, `N≥1`. On the interior define

`K(i,j)=min(k_i,k_j)−k_i k_j/Q`,

`s_i(b)=(b_(i+1)−b_i)/(k_(i+1)−k_i)`,

`(L_k b)_i=s_(i−1)(b)−s_i(b)`.

For zero endpoint values `b₀=b_N=0`, the exact inverse of `K` is `L_k` and the
exact Schur cost is

`D_k(b)=Σ_(0≤i<N) (b_(i+1)−b_i)²/(k_(i+1)−k_i)`.

Writing `F_k(a)=Σ_(1≤i,j<N) a_i a_j K(i,j)`,

`F_k(a)−2Σ_i a_i b_i+D_k(b)=F_k(a−L_k b)≥0`.

The upper bound `2Σ_i a_i b_i−F_k(a)≤D_k(b)` is attained at `a=L_k b`.
It is the actual normalized divisor-conductor Gram restricted to these arithmetic nodes.

## Proof

The slope of `k_i↦min(k_i,k_j)` is one before node `j` and zero after it. The product
term has constant slope. Hence `L_k K(·,j)` is the point mass at `j`. The two endpoint
values of `K` vanish.

If `L_k u=0`, every adjacent slope of `u` agrees. Summing the differences gives
`u_i=u₀+s₀(u)(k_i−k₀)`. Two zero endpoints force the common slope and every value
to vanish. Thus the kernel potential of `L_k b` equals `b`.

Finite summation by parts gives

`Σ_(1≤i<N) b_i(L_k b)_i=D_k(b)−b_N s_(N−1)(b)+b₀s₀(b)`.

The endpoint terms vanish. Symmetry and expansion at `a−L_k b` give the exact
completion. Positivity is the completed arithmetic Gram theorem on the distinct nodes.
At `a=L_k b` the remainder vanishes, proving optimality of the cost.

## Arithmetic consequence

The payment between two prescribed nodes is their squared coupling difference divided
by their arithmetic gap. Both endpoint gaps remain. Restricting to sparse indices therefore
changes the inverse from ordinary second differences to differences of adjacent slopes.
The cost requires no interpolation values at omitted integer indices.

If every arithmetic gap is at least `δ>0`, then

`D_k(b)≤(4/δ)Σ_(1≤i<N)b_i²`,

`(δ/4)Σ_(1≤i<N)a_i²≤F_k(a)`.

For the first bound apply `(u−v)²≤2u²+2v²` on each edge; each interior value occurs
twice and the endpoint values vanish. For the second, use the exact Schur bound with
`b_i=δa_i/4` on the interior and zero at both endpoints. The reciprocal-gap cost gives
the improved coefficient reserve directly.

## Dependencies

- `divisorGramEnergy_packetCoefficient` and positivity of `divisorGramEnergy`.
- Finite summation by parts and the affine uniqueness recurrence.

## Lean declarations

- `CompletedArithmeticForms.meshPotential_inverse`.
- `CompletedArithmeticForms.meshGram_eq_completed`.
- `CompletedArithmeticForms.meshGram_eq_zero_iff`.
- `CompletedArithmeticForms.meshSchur_completion`.
- `CompletedArithmeticForms.meshSchurCost_isGreatest`.
- `CompletedArithmeticForms.meshGram_gap_coercive`.

Module: `GaloisForLFunctions/CompletedArithmeticForms/IrregularGreen.lean`.
The final `lake --old env lean` audit passes without output files. The transitive
axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`.
