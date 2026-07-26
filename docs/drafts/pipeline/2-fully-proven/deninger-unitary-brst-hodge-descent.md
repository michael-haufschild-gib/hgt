# Deninger unitary BRST--Hodge descent

- **ID:** `deninger-unitary-brst-hodge-descent`
- **Stage:** 2-fully-proven
- **Type:** SOURCE HODGE DESCENT THEOREM
- **Parent:** `deninger-mw-gamma-brst-complex`
- **Lean status:** direct check passes in `DeningerArithmeticUnitaryBRSTHodge.lean`

## Statement

Let \(E\) be a real or complex Hilbert space, \(Q:E\to E\) a bounded differential, and
\(U:E\to E\) a unitary operator.  Assume
\[
 UQ=QU.                                                           \tag{1}
\]
Then
\[
 UQ^\dagger=Q^\dagger U,                                         \tag{2}
\]
and therefore \(U\) commutes with the BRST--Hodge Hamiltonian
\[
 \Delta_Q=Q^\dagger Q+QQ^\dagger:                                \tag{3}
\]
\[
 U\Delta_Q=\Delta_QU.                                             \tag{4}
\]
Consequently \(U\) preserves the harmonic sector
\[
 \ker\Delta_Q=\ker Q\cap\ker Q^\dagger.                           \tag{5}
\]

No separate Laplacian-commutation conjecture is needed at a finite Deninger packet.  Once the
centered power transfer is unitary and is a chain map, harmonic cohomology inherits its unitary
action automatically.

## Proof

Taking adjoints in `(1)` gives
\[
 Q^\dagger U^\dagger=U^\dagger Q^\dagger.                        \tag{6}
\]
Multiply `(6)` by \(U\) on the left and by \(U\) on the right.  Using
\[
 UU^\dagger=U^\dagger U=1
\]
gives `(2)`.  Now
\[
\begin{aligned}
 UQ^\dagger Q
   &=(UQ^\dagger)Q
    =(Q^\dagger U)Q
    =Q^\dagger(UQ)
    =Q^\dagger(QU)
    =(Q^\dagger Q)U,\\
 UQQ^\dagger
   &=(UQ)Q^\dagger
    =(QU)Q^\dagger
    =Q(UQ^\dagger)
    =Q(Q^\dagger U)
    =(QQ^\dagger)U.
\end{aligned}
\]
Adding proves `(4)`.  If \(\Delta_Qx=0\), then
\[
 \Delta_QUx=U\Delta_Qx=0,
\]
which proves harmonic preservation.  Equality `(5)` is the already formalized positive
BRST--Hodge identity.

## Deninger consequence

At a finite MW--Gamma packet, combine:

1. hyperbolic localization, which turns \(F_nV_n=n\,\mathrm{id}\);
2. Poincare adjunction and moving-Hodge naturality, which make
   \(U_n=n^{-1/2}V_n\) unitary;
3. framed functoriality, which gives \(U_nQ=QU_n\);
4. the theorem above.

Then every \(U_n\) acts unitarily on harmonic cohomology and commutes with its Hodge Laplacian.
The finite centered-purity gate is therefore reduced to constructing the positive moving Hodge
realization and proving chain-map functoriality.  It is not an additional spectral hypothesis.

## Hostile audit

- Invertibility without unitarity is insufficient: adjoint commutation need not follow.
- Commutation with \(Q\) alone does not imply commutation with \(Q^\dagger\).
- The theorem is finite/bounded.  Passage to the cofinal unbounded limit still requires common
  cores, closability, and strong-resolvent/harmonic-projection convergence.
- Defining \(U\) from Xi spectral coordinates would make the application circular; the theorem
  must consume framed source transfers.
