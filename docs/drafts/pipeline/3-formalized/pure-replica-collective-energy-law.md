# Pure-replica collective energy law

- **ID:** `pure-replica-collective-energy-law`
- **Stage:** 3 -- formalised in Lean 4
- **Type:** exact replica law / Brown-front normalization correction
- **Status:** `[LEAN-PROVED] [AXIOM-AUDITED] [FRONTIER ADVANCE] [NOVELTY UNAUDITED]`
- **Date:** 2026-08-20

## Result

Let `A` act on one finite Hilbert space and let

\[
  A^{(r)}=\sum_{j=1}^r I^{\otimes(j-1)}\otimes A\otimes I^{\otimes(r-j)}.
\]

For every normalized vector `v` satisfying `\langle v,Av\rangle=0`,

\[
 \boxed{\|A^{(r)}v^{\otimes r}\|^2=r\|Av\|^2.}
\]

The proof is exact: diagonal replica pairs contribute the one-copy energy and every off-diagonal
pair factors through `\langle v,Av\rangle` and vanishes.

Normalization is unnecessary.  Writing `q=\langle v,v\rangle`, the exact law is

\[
 \boxed{\|(A^{(r)})v^{\otimes r}\|^2
 =r\|Av\|^2q^{r-1}.}
\]

For every finite matrix `G` and every Hermitian `X`, trace cyclicity gives

\[
 \langle\operatorname{vec}X,\operatorname{ad}_G\operatorname{vec}X\rangle
 =\operatorname{Tr}(X[G,X])=0.
\]

Therefore, for every normalized pure state `psi`, every finite generator `G`, and every replica
number `r`, the collective commutator representation on
`vec(|psi><psi|)^{tensor r}` has exactly replica-linear energy.  No randomness, spectral gap,
asymptotic limit, or ensemble premise enters.

The unnormalized law applies to every Hermitian matrix `X`, hence also to Hermitian mixed or cavity
boundaries: the only extra factor is their Hilbert--Schmidt mass to power `r-1`.

## Brown-front consequence

Worst-case collective-operator bounds cost `r^2`.  That loss is false on physical pure-projector
boundaries: the exact cost is `r`.  This removes one obstruction from the `r=O(n)` complete
Brown-grid threshold schedule.  It does **not** prove fixed-time static-local graph mixing.  Next
open step is to retain this centered sector through the quenched fixed-time incidence transfer,
rather than reverting to a worst-case operator norm after conditioning or cavity expansion.

## Lean certificate

Module: `GaloisForLFunctions.HTGeometry.PureReplicaCollectiveEnergyLaw`

| Statement | Declaration |
|---|---|
| slot Gram orthogonality | `quadForm_replicaSlot_gram_centered` |
| exact replica-linear centered energy | `collectiveReplicaSlotOp_centered_energy` |
| unnormalized centered energy | `collectiveReplicaSlotOp_centered_energy_unnormalized` |
| vectorized commutator trace identity | `quadForm_matrixCommutatorRepresentation_vec` |
| Hermitian commutator centering | `quadForm_matrixCommutatorRepresentation_vec_centered` |
| Hermitian cavity-boundary law | `hermitian_collectiveReplicaCommutator_energy_unnormalized` |
| pure-projector physical law | `pureProjector_collectiveReplicaCommutator_energy` |

Targeted `lake env lean` and module build pass.  Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.
