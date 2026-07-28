# Perfect-return connected-path rigidity

- **ID:** perfect-return-connected-path-rigidity
- **Stage:** 3-formalized
- **Type:** CANDIDATE
- **Source:** positive survivor of the disconnected \(p=1\) locality objection

## Exact frontier

- `[CORPUS]` `one_fixed_nearestNeighbor_chain_every_future_probability`
  constructs a tridiagonal representative for every terminal probability
  in \([0,1]\). At \(p=1\), it is an active Krylov block plus a diagonal
  spectator block.
- `[LITERATURE]` For a finite irreducible Jacobi matrix, every eigenvector
  has nonzero first and last coordinate; equivalently, an endpoint basis
  vector is cyclic. This follows directly from the three-term recurrence
  and is classical; see Leite--Saldanha--Tomei,
  [*Reconstruction of tridiagonal matrices from spectral
  data*](https://arxiv.org/abs/math/0508099).
- `[BRIDGE]` Applying endpoint cyclicity to the parity-supported perfect
  return state has not yet been made explicit in the local recurrence law.
  The classical Jacobi fact alone is not new scientific knowledge.

## Conjecture and hostile attack

`[CONJECTURE]` Let \(D_T\) have the simple spectrum
\(\{\pi j/T:0\leq j\leq 2q+1\}\), let \(e_0\) be the fixed endpoint state,
and let \(Ue_0\) be the odd-parity clock state. For
\(K=U^*D_TU\), every tridiagonal realization has at least one zero
off-diagonal path coupling.

Potential failures:

1. Perfect return alone need not omit any spectral phase when all energies
   acquire the same phase. Here the fixed spectrum contains both phase
   parities and the specified endpoint state has exactly zero weight on
   every even spectral level.
2. A tridiagonal matrix may be connected with complex or signed
   off-diagonal entries. Endpoint cyclicity needs only nonzero forward
   entries, not positivity or reality.
3. Degenerate spectra can carry endpoint-orthogonal eigenvectors even for
   less rigid graph structures. Here the proof uses an explicit
   endpoint-orthogonal eigenvector, not simplicity as an unproved shortcut.

Verdict: `SURVIVES PRELIMINARY ATTACK` as a sharp application and
classification boundary; `REDISCOVERED` if presented as a new standalone
Jacobi theorem.

## Dependency-closed paper proof

Let \(A\) be any tridiagonal operator on the path basis
\(e_0,\ldots,e_n\), with every forward matrix element
\(\langle e_k,Ae_{k+1}\rangle\neq0\). Suppose \(Av=\lambda v\) and
\(\langle e_0,v\rangle=0\). Inductively assume the first \(k+1\)
coordinates of \(v\) vanish. In row \(k\), tridiagonality eliminates every
coordinate above \(k+1\), while the induction hypothesis eliminates all
coordinates at or below \(k\). The eigenvalue equation therefore reduces to
\[
  \langle e_k,Ae_{k+1}\rangle\langle e_{k+1},v\rangle=0.
\]
The forward matrix element is nonzero, so the next coordinate vanishes.
Thus every coordinate of \(v\) is zero. Contrapositively, a nonzero
endpoint-orthogonal eigenvector forces at least one zero path coupling.

Now take any unitary \(U\) sending the fixed state \(e_0\) to the
odd-parity endpoint clock. For any even spectral basis vector \(f_{2a}\),
\[
  v=U^*f_{2a}
\]
is nonzero and is an eigenvector of \(K=U^*D_TU\). Moreover,
\[
  \langle e_0,v\rangle
  =\langle Ue_0,f_{2a}\rangle=0
\]
because the parity endpoint clock has zero weight on all even spectral
levels. The contraposition therefore forces a zero path coupling in every
tridiagonal fixed-protocol realization.

`[PAPER-PROVED]` Proof uses no positivity, real-coupling or unproved
spectral theorem. It is stronger than needed because the endpoint
propagation lemma applies to arbitrary complex tridiagonal operators.

## Formal target

1. Define nonzero-forward-coupling path connectedness.
2. Prove endpoint propagation for an arbitrary tridiagonal eigenvector.
3. Prove its zero-coupling contraposition.
4. Instantiate it with an even spectral eigenvector transported through an
   arbitrary endpoint unitary.
5. Audit axioms and add the exact boundary to manuscript and hostile review.

## Formal result

Module:
`formal/GaloisForLFunctions/RHTower/PerfectReturnPathRigidity.lean`

- `ForwardConnectedHamiltonian`
- `connected_nearestNeighbor_eigenvector_endpoint_ne_zero`
- `nearestNeighbor_endpointOrthogonal_eigenvector_forces_disconnection`
- `endpointTransportedSpectator_eigen`
- `endpointTransportedSpectator_orthogonal_fixedClock`
- `endpoint_paritySupport_forces_path_disconnection`
- `finiteKrylovBasis_forward_entry_ne_zero`
- `finiteKrylov_conjugate_forwardConnected`
- `endpoint_return_connectedness_dichotomy`

`[LEAN-PROVED]` Targeted foreground compilation passes. The capstone's axiom
audit reports only `propext`, `Classical.choice` and `Quot.sound`. Manuscript
and claim trace state the exact theorem. Final project lint and umbrella
build remain part of the parent paper audit.
