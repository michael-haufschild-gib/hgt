# Arithmetic restriction and optimal Dirichlet extension

- **ID:** completed-arithmetic-forms-optimal-interpolation
- **Stage:** 3-formalized
- **Type:** THEOREM

## Statement

For integer nodes `0=k₀<…<k_N=Q` and prescribed values `b₀=b_N=0`,

`min {D_Q(u) : u(k_i)=b_i, 0≤i≤N} = D_k(b)`.

The minimum is attained by the completed arithmetic potential of the node sources
`a_i=(L_k b)_i`:

`u(r)=Q⁻¹ Σ_i B_Q(r,k_i) (L_k b)_i`.

Thus restriction to arithmetic nodes has an exact optimal extension in its dual
Dirichlet norm. The extension uses the same completed conductor kernel as the form.

## Proof

Restriction of the normalized full kernel to the nodes is `K_k`. Therefore the
displayed potential has values `K_k L_k b=b` at every selected node, including
the two endpoints.

For any source `A`, finite Green summation gives

`D_Q(B_Q A/Q)=E_Q(A)/Q`.

Apply this to the zero extension of `L_k b` from the selected nodes. The resulting
energy is `F_k(L_k b)=D_k(b)`, so the candidate extension attains the stated cost.

For any competing extension `v`, the normalized arithmetic Schur inequality on
the node packet `L_k b` gives

`2Σ_i (L_k b)_i v(k_i)−F_k(L_k b)≤D_Q(v)`.

Its left side equals `2D_k(b)−D_k(b)`. Both zero endpoint values are retained,
so this is exactly `D_k(b)≤D_Q(v)`. This proves minimality without a loss in
conductor, number of omitted indices, or gap size.

## Actual prime coupling

Let the mesh contain every prime of a block `S⊂(P,2P]`, with endpoints `0` and
`Q=2P+2`. For zero-mass, zero-log-moment coefficients and prescribed coupling
values `b_i` at the mesh nodes,

`2Σ_(p∈S) a_p b_(index(p))−primePacketBilinear(S,S,a,a)≤D_k(b)`.

Insert the canonical arithmetic extension into the proved full-grid prime Schur
bound. Its values at the primes are the prescribed couplings, and its full-grid
variation is exactly `D_k(b)`. Thus the actual source payment depends on the
reciprocal arithmetic gaps. Attainment and optimality concern its completed
conductor comparison; the actual prime form may have additional positive energy.

Lean: `CompletedArithmeticForms/OptimalInterpolation.lean`, particularly
`meshInterpolation_values`, `dirichletEnergy_meshInterpolation`,
`meshDirichletEnergy_isLeast_extension`, and `primePacket_mesh_schur_bound`.
Kernel dependencies: `propext`, `Classical.choice`, `Quot.sound`.
