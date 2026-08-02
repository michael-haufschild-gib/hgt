# Route E strict-half \(E_3\)-cofactor capacity ceiling

- **ID:** `ROUTE-E-STRICT-HALF-E3-COFACTOR-CEILING-001`
- **Stage:** 5-failed
- **Type:** FALSIFIED SOURCE ARCHITECTURE / SHARP PHYSICAL CAPACITY CEILING
- **Parent:** `../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** exact two-phase hostile current formalized in
  `MobiusBlockDefectEnergy.lean`; physical-target-versus-representation principle already
  formalized by `sum_conductance_le_neighborUnionCapacity`

## Retired architecture

Cover all ordinary Möbius block imbalance using targets
\[
q=t\,p_1p_2p_3\asymp U,
\]
where
\[
t\le T,\qquad p_1\le P,\qquad
p_2,p_3\asymp\sqrt{\frac{U}{tp_1}},
\]
and \(p_1p_2p_3\) is supplied by a balanced all-interval exact-\(E_3\) theorem.  Permit every
cofactor and every distinguished-prime range consistent with strict-half displacement.

## Exact killing theorem

Assume \(TP=U^{o(1)}\), as forced by
\[
|q-u|\asymp\sqrt{Utp_1}\,U^{o(1)}=U^{1/2+o(1)}.
\]
The number of physical targets in one dyadic scale is at most
\[
\ll
\sum_{t\le T}\sum_{p_1\le P}
\frac{U}{tp_1\log^2 U}
\ll
\frac{U\log T\,\log\log P}{\log^2 U}.                   \tag{1}
\]

Indeed, for fixed \(t,p_1\), both remaining primes lie in fixed comparable square-root ranges.
The prime number theorem upper bound gives
\[
\#\{(p_2,p_3):tp_1p_2p_3\asymp U\}
\ll\frac{U}{tp_1\log^2U}.
\]
Summing uses
\[
\sum_{t\le T}\frac1t\ll\log T,\qquad
\sum_{p\le P}\frac1p\ll\log\log P.
\]
Counting representations only enlarges the physical target count, so collisions cannot invalidate
the upper bound.

Because \(T=U^{o(1)}\),
\[
\log T=o(\log U),
\qquad
\log\log P\le(1+o(1))\log\log U,
\]
and `(1)` yields
\[
\#\{q\}
=o\!\left(\frac{U\log\log U}{\log U}\right).            \tag{2}
\]

Menon's sharp mean-square input permits block defects at the scale
\[
\frac1X\int_X^{2X}
\left|\frac1h\sum_{x<n\le x+h}\mu(n)\right|^2dx
\ll
\left(\frac{\log\log h}{\log h}\right)^2.
\]
Consequently its direct \(L^1\) vertex budget is
\[
U\,\frac{\log\log U}{\log U}.                            \tag{3}
\]
The gap between `(2)` and `(3)` is unbounded.

This is not merely slack in Cauchy--Schwarz.  Put \(N=U/h\), take \(m=N/2\), and assign defects
\(+A\) for the first \(m\) blocks and \(-A\) for the last \(m\), with
\[
A=h\frac{\log\log U}{\log U}.
\]
This sequence has zero total and exactly the permitted quadratic increment scale, but its total
unmatched mass is `(3)`.  For geometric block weight \(r=e^{-xh}\), Lean proves the exact transfer
law
\[
S_m(r)(1-r)=A(1-r^m)^2,
\]
so at \(x\asymp U^{-1}\) its signed Gibbs current also has size `(3)`.

Therefore Menon mean-square input plus any single balanced-\(E_3\) cofactor architecture at
strict-half displacement does not imply ordinary Route E cancellation.  Taking \(T=U^\eta\)
with fixed \(\eta>0\) can restore a full \(\log U\) harmonic cofactor mass, but its displacement is
\(U^{1/2+\eta}\); with an ordinary set of exponent one, the exact fallback threshold requires
\(\eta\le0\).

## Strongest positive survivor

Two useful statements survive.

1. The narrow published \(p_1\)-exponent band contains \(\asymp\log\log U\) disjoint dyadic
   slices.  Summing them improves the proved exceptional token union from
   \(U/(\log U\log\log U)\) to \(U/\log U\).
2. Ordinary blocks must cancel as a signed low-frequency current.  Exact block compression and
   discrete Abel summation identify the critical positive source invariant
   \[
   \sum_{\xi_j\in[U,2U]}M(\xi_j)^2
   \le\frac{U^{2+o(1)}}h,
   \]
   formalized in `MobiusBlockDefectCompression.lean` and
   `MobiusBlockDefectEnergy.lean`.

## New insight

The obstruction is a three-way phase law, not a missing logarithmic optimization:

\[
\text{ordinary defect density}
\times
\text{strict-half displacement}
\times
\text{physical \(E_3\) harmonic capacity}.
\]

Any attempt to gain the missing capacity by a fixed-power cofactor immediately spends the same
power in displacement.  Any subpower cofactor retains critical displacement but has
\(\log T=o(\log U)\), producing the ceiling `(2)`.  Thus exceptional fallback and ordinary
orientation are mathematically different components.

## Status

`[FAILED; EXHAUSTIVE FOR ONE BALANCED-E3 CORE WITH MULTIPLICATIVE PRE-COFACTORS]`.

This does not rule out a denser all-interval core, a genuinely higher-rank target not collapsing
to one total pre-cofactor, or direct proof of cumulative-defect energy.  It does rule out further
label/band/cofactor tuning inside the stated architecture.
