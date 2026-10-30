# Complete native remainder in Hermite coordinates

**ID:** completed-arithmetic-forms-hermite-native-tail  
**Stage:** Formalized  
**Type:** Complete-source estimate

Let $q=\pi e^{2x}$, $A=27e^{3\pi}/399$, and $T_N$ be the monic Hermite matrix.
The complete native balanced moments and literal first-atom balanced moments satisfy
$$|m_n^{\rm native}-m_n^{(1)}|\le A24^{2L}q^Le^{-3q},
\qquad n\le2L,\quad q\ge2L+6.$$
Odd moments vanish identically on both sides.

The exact transformed head difference is
$T_N(H^{\rm native}-H^{(1)})T_N^{\mathsf T}$.
For $i,j<N$ and $q\ge2N+6$,
$$|(H^{\rm native}_{\rm Hermite}-H^{(1)}_{\rm Hermite})_{ij}|
\le N^2(N!)^2e^8 A24^{2N}q^Ne^{-3q}.$$
On $q\ge16(N+2)^2$,
$$N^2(N!)^2e^8 A24^{2N}q^Ne^{-3q}\le\frac{Ae^8}{q}.$$
The proof uses $N!\le e^{N^2}$, $24^{2N}\le e^{10N}$,
$q^Ne^{-q}\le N!$, and $e^{-q}\le1/q$.
Both coefficient sums and every native theta atom remain in the estimate.

Lean: `CompletedArithmeticForms/HermiteNativeTail.lean`.
Capstones: `firstAtomNormalizedRotatedPair_all_jets`,
`nativeBalancedFullMoment_firstAtom_error_le`,
`nativeHermiteHead_firstAtom_raw_error_le`, `hermiteNativeTail_polynomial_payment`,
and `nativeHermiteHead_firstAtom_error_le`.
Each audited axiom set contains only `propext`, `Classical.choice`, and `Quot.sound`.
