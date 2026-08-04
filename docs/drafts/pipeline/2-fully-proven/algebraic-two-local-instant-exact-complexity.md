# Algebraic two-local instant exact-complexity law

- **ID:** algebraic-two-local-instant-exact-complexity
- **Stage:** 2-fully-proven
- **Type:** THEOREM / boundary theorem for robust autonomous complexity
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/static-local-complexity-law.md`, obligation O4
- **External parent:** Y. Jia and M. M. Wolf, *Hay from the haystack: explicit
  examples of exponential quantum circuit complexity*, arXiv:2205.06977

## Exact statement

Fix `n >= 2` and put `D=2^n`.  There exist

1. a traceless two-local `n`-qubit Hamiltonian `H_n` whose Pauli
   coefficients are rational; and
2. the fixed algebraic product input `Omega=|0>^tensor n`

such that `Omega` has nonzero overlap with every eigenvector of `H_n`, the
only rational linear relation among the `D` eigenvalues is their trace
relation, and the following hold.

### A. Every nonzero algebraic time has exponential exact complexity

For every nonzero real algebraic `t`,

\[
  C_0(e^{-itH_n}\Omega)\ge {D-1\over16}.                 \tag{1}
\]

Here `C_0` is exact pure-state preparation complexity from `Omega` using
arbitrary two-qubit unitary gates on arbitrary pairs.  Allowing a fixed
algebraic product change of input changes the bound only by its linear gate
cost.

### B. Low exact-complexity times are locally finite

For every integer `s<(D-1)/16` and every finite `T`,

\[
 \{t\in[-T,T]:C_0(e^{-itH_n}\Omega)\le s\}              \tag{2}
\]

is finite.  Equivalently, outside a locally finite subset of real time, the
autonomous orbit has exact state complexity at least `(D-1)/16`.

This is an exact-complexity theorem.  It gives no lower bound at one fixed
positive approximation radius and therefore does not close O4.

## Proof

### 1. A rational two-local specialization with full symmetric Galois group

The generic characteristic polynomial of the traceless two-local Pauli
family has geometric monodromy `S_D`; this is paper-proved and Lean-proved in
`generic-two-local-spectral-monodromy`.  Hence its generic Galois group over
the rational-function field of Pauli coefficients is `S_D`.

Hilbert irreducibility gives a Zariski-dense set of rational coefficient
specializations whose characteristic polynomial still has Galois group
`S_D`.  We may simultaneously avoid the discriminant and any prescribed
nonzero polynomial in the coefficients.

The cyclicity determinant

\[
 K_\Omega(H)=\det[\Omega,H\Omega,\ldots,H^{D-1}\Omega]   \tag{3}
\]

is such a nonzero polynomial on the two-local family.  To see it is not
identically zero, take

\[
 H_0=\sum_{j=0}^{n-1}3^jX_j .                           \tag{4}
\]

Its product `X`-basis eigenvalues are distinct by uniqueness of balanced
ternary expansion, while `|0>^tensor n` has the same nonzero overlap with
every `X`-basis vector.  The usual Vandermonde factorization of (3) therefore
gives `K_Omega(H_0) != 0`.

Choose a rational Hilbert specialization outside the discriminant and
`K_Omega=0`.  It has simple spectrum and full spectral support at `Omega`.

### 2. The specialized spectrum has rational rank `D-1`

Let `E=(E_1,...,E_D)` be the roots.  The rational relation space

\[
 R_E=\{a\in\mathbb Q^D:\sum_j a_jE_j=0\}               \tag{5}
\]

is invariant under the Galois group `S_D`.  The rational permutation module
splits as the constant line plus the irreducible standard representation.
Tracelessness puts the constant vector in `R_E`.  If `R_E` contained any
standard component, it would be all of `Q^D`, forcing every `E_j` to vanish,
contrary to simple spectrum.  Thus

\[
 R_E=\mathbb Q(1,\ldots,1),\qquad
 \dim_\mathbb Q\operatorname{span}\{E_j\}=D-1.          \tag{6}
\]

### 3. Lindemann--Weierstrass transfers spectral rank to the state

Fix nonzero algebraic real `t` and put `z_j=exp(-itE_j)`.  Every `E_j` is
algebraic.  Finite Lindemann--Weierstrass, applied to a rational basis of
their span, gives

\[
 \operatorname{trdeg}_\mathbb Q\mathbb Q(z_1,\ldots,z_D)=D-1.      \tag{7}
\]

This exact finite theorem is already in the Lean corpus as
`exp_algebraicIndependent_of_linearIndependent` in
`RHTower/FiniteLindemannWeierstrass.lean`.

Choose an algebraic orthonormal eigenbasis `V` of the rational Hermitian
matrix `H_n`, and put `c=V^*Omega`.  Cyclicity makes every `c_j` nonzero.
In computational coordinates,

\[
 e^{-itH_n}\Omega=V\operatorname{diag}(c)z .             \tag{8}
\]

The matrix `V diag(c)` is algebraic and invertible, so (8) preserves
transcendence degree.  The output state therefore has transcendence degree
`D-1`.

Jia--Wolf Theorem 1 proves for qubits that the coordinate transcendence
degree of a state is at most `16` times its arbitrary two-qubit exact circuit
complexity.  Equation (1) follows.

### 4. O-minimality makes the exceptional real times discrete

For fixed `s`, the set `S_s` of states prepared by at most `s` arbitrary
two-qubit gates is compact semialgebraic.  Indeed, there are finitely many
gate-support patterns; for each pattern the parameter space `U(4)^s` is
compact semialgebraic, the output coordinates are polynomial in the gate
entries, and Tarski--Seidenberg preserves semialgebraicity under projection.

On `[-T,T]`, every coordinate of `t -> exp(-itH_n)Omega` is a finite algebraic
linear combination of restricted sine and cosine functions.  The orbit map
is therefore definable in the restricted-analytic o-minimal structure
`R_an`.  Its preimage of `S_s` is a definable subset of the real line, hence
a finite union of points and intervals.

If that preimage contained a nontrivial interval, the interval would contain
a nonzero algebraic time, contradicting (1).  Only finitely many points
remain, proving (2).

## Hostile boundary audit

1. **No robust conclusion.**  Transcendence degree is destroyed by arbitrary
   small perturbations because algebraic vectors are dense.  Neither (1) nor
   (2) supplies a dimension-independent approximation radius.
2. **No Brown growth.**  Exact complexity jumps from zero to order `D` rather
   than growing linearly.  It is therefore an obstruction to using exact
   complexity as a physical observable, not a solution of the growth law.
3. **No effective first time.**  O-minimality gives local finiteness but no
   usable lower bound on distance from the low-circuit semialgebraic set.
4. **No novelty promotion.**  Jia--Wolf supply the transcendence-degree
   circuit theorem and explicit nonlocal examples.  The fixed-two-local
   Hilbert-specialization and locally-finite-time synthesis was not found in
   the initial exact-concept search, but priority remains unverified.

## Exact surviving O4 question

The theorem converts O4 into a quantitative separation problem:

> Bound, at one fixed positive radius, the distance between the algebraic
> local-Hamiltonian orbit and the semialgebraic `s`-gate state set through
> normalized time `s`, uniformly up to `s=Theta(D/poly(n))`.

Qualitative algebraic independence proves the distance is nonzero at
algebraic times.  Brown growth requires a new quantitative local
Lindemann--circuit separation law whose radius does not collapse with `n`,
`s`, or time.

## Formalization status

- `[CORPUS]` finite Lindemann--Weierstrass and algebraic independence:
  `RHTower/FiniteLindemannWeierstrass.lean`.
- `[CORPUS]` full two-local monodromy and relation rigidity: modules cited by
  `generic-two-local-spectral-monodromy`.
- Missing Lean layers: rational Hilbert specialization, transcendence-degree
  bound for concrete two-qubit circuits, cyclic spectral-coordinate transfer,
  and the o-minimal local-finiteness corollary.
- No new Lean code is authorized until those exact interfaces are designed
  from the existing corpus and this paper proof survives another specialist
  audit.

## Sources

- Y. Jia and M. M. Wolf, *Hay from the haystack: explicit examples of
  exponential quantum circuit complexity*, arXiv:2205.06977, Theorems 1, 3,
  6, and 7.
- D. Hilbert, irreducibility theorem; use the standard Zariski-dense Hilbert
  specialization form over `Q`.
- A. J. Wilkie and L. van den Dries, standard one-dimensional finiteness for
  sets definable in the restricted-analytic o-minimal structure `R_an`.

