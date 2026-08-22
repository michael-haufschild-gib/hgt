# Static Choi centralizer-carrier replica law

- **Stage:** 3 — formalized in Lean 4
- **Status:** `[LEAN-PROVED] [AXIOM-AUDITED] [FRONTIER ADVANCE] [NOVELTY UNAUDITED]`
- **Date:** 2026-08-22

## Result

For a unitary target `W` in a `d`-level Hamiltonian eigenbasis, define

\[
  S(W)=d^{-1}\sum_i |W_{ii}|.
\]

The direct-target growing-replica near-action mass obeys

\[
  A_{r,\delta}(E,W)\le S(W)^{2r}.
\]

For every finite unitary circuit dictionary with probability design `w`, every `β ≥ 0` therefore
satisfies the geometric decomposition

\[
 \sum_c w_c A_{r,\delta}(E,W_c)
 \le \beta^{2r}+
 \sum_{c:\,d_{\rm Choi}(Z_c,W_c)<\sqrt{1-\beta^2}}w_c,
\]

where `Z_c` is the explicit radial diagonal unitary obtained from the phases of `(W_c)_{ii}`.
It commutes exactly with the diagonal Hamiltonian. The identity

\[
 d_{\rm Choi}(Z_c,W_c)=\sqrt{1-S(W_c)^2}
\]

is exact. Substitution into the canonical determinant-design theorem replaces its opaque weighted
near-action premise by an exponentially small transverse term plus literal optimal-design weight
inside the spectral-centralizer tube.

The companion commutator bridge proves

\[
 d^{-1}\|[\operatorname{diag}E,W]\|_{HS}^{2}
 \le (2v_E)^2 d_{\rm Choi}(Z,W)^2,
\]

with the corpus speed `v_E`. Thus the unsuppressed carrier is a small normalized observer-
commutator event, not generic spectral crowding. No minimum spectral gap enters.

## Exact remaining frontier

For an ordinary fixed-`q` static local Gaussian draw, prove a quenched, circuit-uniform lower-tail
bound for the shared-draw Pauli commutator incidence map after removing the return and exact
centralizer strata. The bound must retain determinant-design weight and survive the complete
polynomial-depth circuit net. Existing Pauli Casimir/Hall laws prove rank and leakage expansion but
do not yet give the required pseudodeterminant conditioning on every occupied circuit stratum.

## Lean certificate

- `GaloisForLFunctions.RHTower.StaticChoiCentralizerCarrierReplicaLaw`
- `GaloisForLFunctions.RHTower.StaticChoiCentralizerCommutatorBridge`

Targeted source checks and targeted module builds pass. `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`.
