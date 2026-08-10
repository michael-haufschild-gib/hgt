# One-replica local-Pauli planar cavity decay

- **ID:** `one-replica-local-pauli-planar-cavity-decay`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper proof + unconditional Lean 4 proof)
- **Source:** `../1-in-progress/static-local-complexity-law.md` · O4 planar replica route
- **Formalized companion:** `one-replica-local-pauli-planar-cavity-decay-formalized.md`
- **Statement:** Positive isotropic weight-one Pauli variance makes the one-replica planar commutator pencil full; its vacuum-compressed real-time propagator decays to zero in operator norm on traceless operators.

## Status

- `[PAPER-PROVED] [LEAN-FORMALIZED] [KERNEL-AUDITED]`
- `[BRIDGE] [NOVELTY UNVERIFIED]`
- Lean closes the finite Dyson--Hall atomlessness, algebraic coordinate-law absolute continuity,
  exact vacuum compression, Fourier decay, and finite-dimensional operator-norm upgrade without
  assuming an external operator-valued semicircle theorem.

## Theorem

Let `H=(C^2)^(tensor n)` and let `V=End(H)_0` be its traceless
Hilbert--Schmidt operator space.  For every nonidentity Pauli word `p` of
weight at most a fixed `q>=1`, put

\[
 A_p=\operatorname{ad}_{P_p}:V\to V,
 \qquad A_p(X)=P_pX-XP_p.
\]

Let `v_p>=0`, and assume every weight-one word has one common variance
`v_p=v_1>0`.  With free standard semicircular variables `s_p`, define

\[
 S=\sum_p\sqrt{v_p}\,A_p\otimes s_p,
 \qquad
 U_0(t)=E_\Omega(e^{-itS}).
\]

Then:

1. the Hermitian pencil `(sqrt(v_p) A_p)_p` is full;
2. the scalar spectral law of `S` is purely absolutely continuous;
3. every matrix coefficient of `U_0(t)` tends to zero as `|t|->infinity`;
4. because `V` is finite-dimensional,

\[
                    \|U_0(t)\|_{op}\longrightarrow0.
\]

## Proof

### 1. Exact support-block Casimir

Index the normalized nonidentity Pauli basis by words `z`.  For a nonempty
site set `T`, let `V_T` be the span of the Pauli words having support exactly
`T`.  Then

\[
                  V=\bigoplus_{\varnothing\ne T\subseteq[n]}V_T.
\]

A one-site commutator preserves every `V_T`.  If `z` is supported on `T`,
then at each `i in T` exactly two of the three one-site Pauli letters
anticommute with `z_i`.  Each nonzero commutator has squared amplitude four.
Consequently

\[
 \sum_{\substack{p:\,\operatorname{wt}(p)=1}}A_p^2\big|_{V_T}
 =8|T|I_{V_T}.                                             \tag{1}
\]

Every `A_p` is self-adjoint for the Hilbert--Schmidt inner product.

### 2. Explicit symmetric doubly-stochastic scaling

Let

\[
 \eta_1(X)=v_1\sum_{\operatorname{wt}(p)=1}A_pXA_p
\]

and define the positive definite block-scalar operator

\[
 C\big|_{V_T}=(8v_1|T|)^{-1/2}I_{V_T}.                \tag{2}
\]

Because every one-site `A_p` preserves support, `(1)` gives exactly

\[
                         \eta_1(C)=C^{-1}.             \tag{3}
\]

Thus the symmetric scaling

\[
 \Phi(X)=C^{1/2}\eta_1(C^{1/2}XC^{1/2})C^{1/2}
\]

is unital.  It is also trace-preserving because its Kraus operators are
self-adjoint.  For every positive semidefinite `B`, unital positivity gives
`0<=Phi(supp B)<=I`, while trace preservation gives
`Tr Phi(supp B)=rank(B)`.  Hence

\[
                  \operatorname{rank}\Phi(B)
                  \ge\operatorname{rank}B.            \tag{4}
\]

Indeed, on `P=supp B` the positive matrix `B` has a strictly positive least
eigenvalue `c`, so `B>=cP`.  Therefore `Phi(B)>=c Phi(P)` and the support of
`Phi(B)` contains that of `Phi(P)`.

Invertible left--right scaling preserves this rank-nondecreasing property,
so `eta_1` is rank non-decreasing and its pencil is full.

Let

\[
 \eta(X)=\sum_pv_pA_pXA_p=\eta_1(X)+\eta_{>1}(X).
\]

For `B>=0`, both summands are positive and therefore
`supp eta_1(B) <= supp eta(B)`.  Equation `(4)` yields

\[
                  \operatorname{rank}\eta(B)
                  \ge\operatorname{rank}B.            \tag{5}
\]

The full bounded-weight pencil is therefore full.

### 3. Absolute continuity and Fourier decay

Kargin's matrix-semicircle structure theorem states that the scalar Cauchy
transform of a finite matrix semicircle is algebraic and that a full pencil
has purely absolutely continuous scalar spectral law, real-analytic away
from finitely many algebraic singularities.  Apply it using `(5)`.

The matrix trace tensored with the free semicircular trace is faithful.
Therefore a spectral projection of `S` over a Lebesgue-null set has zero
faithful trace and hence is the zero projection.  Every vector spectral
measure of `S`, including every measure associated with vectors
`Omega tensor v`, is consequently absolutely continuous.  Since `S` is
bounded, those densities lie in `L^1` on a compact interval.

For `v,w in V`, the Riemann--Lebesgue lemma gives

\[
 \langle v,U_0(t)w\rangle
 =\langle\Omega\otimes v,e^{-itS}(\Omega\otimes w)\rangle
 \longrightarrow0.                                     \tag{6}
\]

There are only finitely many matrix entries in an orthonormal basis of `V`.
Entrywise convergence in `(6)` therefore implies operator-norm convergence.

## External theorem audit

- `[LITERATURE]` V. Kargin, *An algebraic characterization of non-singular
  matrix semicircles*, arXiv:2604.23089 (2026): fullness is equivalent to
  rank non-decrease; the scalar Cauchy transform is algebraic; a full pencil
  has purely absolutely continuous law.
- `[LITERATURE]` V. Kargin, *Singularities of matrix semicircles*,
  arXiv:2607.26222 (2026): full matrix semicircles have no zero atom and only
  algebraic density singularities; no singular-continuous component occurs.

These sources motivate the paper proof.  Lean does not import their conclusions as hypotheses:
the finite Dyson equation, Hall obstruction, algebraic branch, absolute-continuity transfer, and
Fourier-decay chain are all proved inside the project.

## Hostile audit

- This is a planar/free Gaussian theorem, not the finite static-Hamiltonian
  evolution theorem.
- It closes only replica order one.  Circuit-union control needs replica
  order growing with circuit budget.
- At replica order at least two, one-site diagonal Pauli action has local
  singlets.  Removing only the global replica-permutation algebra does not
  remove every local singlet; two- and higher-site interactions must be shown
  to synchronize them before the same scaling argument applies.
- No decay rate uniform in `n` is claimed.  Absolute continuity gives
  `o(1)` decay only.
- The Lean capstone quantifies the positive qubit count as `n + 1`.  This is definitionally the
  theorem's `n ≥ 1` domain and avoids inventing a normalized scalar trace on the zero-dimensional
  traceless sector.

## Lean formalization

Primary module:

- `formal/GaloisForLFunctions/HTGeometry/OneReplicaTracelessPauliSpectralDecay.lean`

Capstone declaration:

- `oneReplicaLocalPauliPlanarCavityDecay`

Its closed conjunction contains the exact Hermitian pencil law, rank-nondecreasing fullness,
absolute continuity of the normalized scalar spectral law, decay of every matrix entry, decay of
every vector matrix coefficient, and operator-norm decay.  Principal supporting declarations are:

- `oneReplicaWeightedTracelessPauliAdjointMatrix_conjTranspose`;
- `oneReplicaWeightedPauliPencil_full`;
- `oneReplicaWeightedScalarSpectralLaw_hasMoments`;
- `oneReplicaWeightedScalarSpectralLaw_absolutelyContinuous`;
- `oneReplicaWeightedVacuumCompressedPropagator_matrixCoefficient_tendsto_zero`;
- `oneReplicaWeightedVacuumCompressedPropagator_operatorNorm_tendsto_zero`.

Reusable infrastructure is in
`FiniteDysonHallAtomlessness.lean`, `MatrixSemicircleAnalyticLaw.lean`,
`FreeFockMatrixSemicircleCoordinateLaw.lean`, and
`FreeFockMatrixSemicircleFourierDecay.lean`.  All are imported through
`GaloisForLFunctions/HTGeometry.lean`.

Verification on 2026-08-10:

```text
lake env lean GaloisForLFunctions/HTGeometry/OneReplicaTracelessPauliSpectralDecay.lean  # pass, no warnings
lake build GaloisForLFunctions.HTGeometry.OneReplicaTracelessPauliSpectralDecay          # pass
#print axioms oneReplicaLocalPauliPlanarCavityDecay                                      # propext, Classical.choice, Quot.sound
```

## Mathematical delta

The previous corpus had strict contraction only at the first interaction
timescale.  This theorem proves genuine all-long-time planar decay at replica
order one and identifies the first higher-replica obstruction exactly as the
local-singlet synchronization problem, not a generic failure of free-cavity
decay.

## Log

- 2026-08-04 — Support-block Casimir and explicit symmetric scaling derived; full-pencil and operator-norm decay proof closed using April/July 2026 matrix-semicircle structure theorems.
- 2026-08-10 — Entire theorem closed unconditionally in Lean 4, kernel-audited, wired into the HTGeometry umbrella, and promoted to Stage 3.
