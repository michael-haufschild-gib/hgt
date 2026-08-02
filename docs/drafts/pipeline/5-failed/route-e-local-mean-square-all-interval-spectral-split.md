# Route E local-mean-square/all-interval spectral split

- **ID:** `ROUTE-E-SPECTRAL-SPLIT-SQUARE-ROOT-WALL-001`
- **Stage:** 5-failed
- **Type:** FALSIFIED INPUT SYNTHESIS / EXACT FOURIER COUNTERMODEL
- **Parent:** `../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** exact zero-total Fourier mode and Gibbs transfer function formalized as
  `geometricDefectMode_zeroTotal` and `geometricDefectMode_weighted_transfer` in
  `MobiusBlockDefectEnergy.lean`

## Retired synthesis

Combine:

1. Menon-scale local mean square for width-\(h\) block defects;
2. all-interval Möbius cancellation for intervals of length at least \(U^\theta\);
3. discrete Abel/Cauchy--Schwarz;

and infer the critical \(U^{1/2+o(1)}\) Gibbs current without an additional arithmetic
low-frequency theorem.

## Exact killing mode

Let
\[
h=U^\beta,\qquad N=U/h=U^{1-\beta},\qquad
L(U)=\frac{\log\log U}{\log U},
\]
with \(\beta<\theta<1\).  Choose
\[
K\asymp U^{1-\theta},\qquad
z=e^{2\pi iK/N},\qquad A=hL(U),
\]
with \(K\) an integer and \(z^N=1\), \(z\ne1\).  Define the complex block defect
\[
d_j=Az^j,\qquad 0\le j<N.
\]
Lean proves
\[
\sum_{j<N}d_j=0                                         \tag{1}
\]
and, for every geometric weight \(r\),
\[
\left(\sum_{j<N}A(rz)^j\right)(1-rz)
=A\left(1-(rz)^N\right).                                \tag{2}
\]

A phase-rotated real part gives a real defect sequence with the same bounds and a Gibbs response
within an absolute factor of `(2)`.

## It obeys both published input scales

First,
\[
\sum_{j<N}|d_j|^2=NA^2=Uh\,L(U)^2,                      \tag{3}
\]
which is exactly the block-discretized scale allowed by Menon's mean-square theorem.

Second, every consecutive sum of this mode is a geometric progression, so
\[
\left|\sum_{j=a}^{b}d_j\right|
\le\frac{2A}{|1-z|}
\asymp A\frac NK
\asymp U^\theta L(U).                                   \tag{4}
\]
Every physical interval of length at least \(U^\theta\) therefore has relative defect
\(O(L(U))=o(1)\).  Thus `(4)` satisfies an all-interval \(o(H)\) theorem at exponent \(\theta\).

## Its Gibbs current remains at exponent \(\theta\)

Take \(x\asymp U^{-1}\) and \(r=e^{-xh}\).  Then
\[
1-r\asymp N^{-1},\qquad r^N\asymp e^{-1},
\qquad |1-rz|\asymp K/N.
\]
Equation `(2)` gives
\[
\left|\sum_{j<N}d_jr^j\right|
\asymp A\frac NK
\asymp U^\theta L(U).                                   \tag{5}
\]

Equivalently, the cumulative-defect energy of this mode is
\[
\sum_{j<N}|D_j|^2
\asymp N\left(A\frac NK\right)^2
\asymp U^{1+2\theta-\beta}L(U)^2.                        \tag{6}
\]
Pairing `(6)` with Gibbs gradient energy \(U^{\beta-1}\) again yields current exponent
\[
\frac{1+2\theta-\beta}{2}
+\frac{\beta-1}{2}
=\boxed{\theta}.                                        \tag{7}
\]
The block scale cancels completely.  Critical decay follows from this synthesis only at
\(\theta\le1/2\).

The strongest published all-interval Möbius theorem has every fixed \(\theta>0.55\).  Its
spectral remainder is therefore \(U^{0.55+o(1)}\), not \(U^{1/2+o(1)}\).  Menon's improved
logarithmic mean square cannot change the power in `(7)`.

## Strongest positive survivor

The exact surviving source is not another one-block moment.  It must suppress coherent modes in
the frequency annulus beginning at
\[
K\asymp U^{1-\theta},
\]
or prove the cumulative energy
\[
\sum_{\xi_j\in[U,2U]}M(\xi_j)^2\le U^{2+o(1)}/h.
\]
This is `MOBIUS-CRITICAL-MESH-ENERGY`, already paper- and Lean-reduced on the parent card.

## New insight

The gap from \(0.55\) to \(1/2\) is spectrally rigid: after local mean-square control, a mode whose
physical wavelength is exactly \(U^\theta\) passes the all-interval \(o(H)\) test and transfers
to the Gibbs current with the same exponent \(\theta\).  Changing block width, taking a finer
partition, or improving only logarithmic factors cannot cross the wall.

Any successful combination must use an ordinary-integer-specific estimate on coherent
low-frequency defect modes, not merely stronger exceptional density or fixed-order local
uniformity.

## Status

`[FAILED; EXHAUSTIVE FOR COEFFICIENT-BLIND SYNTHESIS OF THE TWO STATED INPUT NORMS]`.

Actual Möbius defects may exclude this Fourier packet through additional arithmetic structure.
Proving that exclusion is precisely new source work.
