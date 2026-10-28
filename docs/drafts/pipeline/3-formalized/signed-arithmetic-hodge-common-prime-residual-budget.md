# One arithmetic remainder controls every Ramanujan residual

## Statement

Let \(P_N\) be the literal prime matrix on \(1,\ldots,N\), and let
\(v_{m,N}(n)=c_m(n)/\sqrt{\phi(m)n}\). Define

\[
\begin{aligned}
E_m&=\gamma+\log m+\operatorname{tameDifferent}(m),\\
r_{m,N}&=P_Nv_{m,N}-(\log N-E_m)v_{m,N},\\
b(y)&=\left|\sum_{t=1}^y\frac{\Lambda(t)}t-\log y+\gamma\right|+\frac1y,\\
B_N&=\sum_{n=1}^N\frac{b(\lfloor N/n\rfloor)^2}{n},\\
C_m&=\sqrt{\phi(m)}(1+4\log m).
\end{aligned}
\]

Every finite set \(S\) of positive conductors and every real coefficient vector satisfy

\[
\left\|\sum_{m\in S}a_m r_{m,N}\right\|_2^2
\le\left(\sum_{m\in S}a_m^2\right)
\left(\sum_{m\in S}C_m^2\right)B_N.
\]

The same arithmetic function \(B_N\) works for all families, and
\(B_N/\log N\to0\).

## Mathematical proof

The totient bound on the actual Ramanujan sum gives
\(|u_m(n)|\le\sqrt{\phi(m)}\) after normalization. For \(y=\lfloor N/n\rfloor\),
the exact prime-row identity writes the residual as

\[
\frac{(e(y)-r)u_m(n)+\operatorname{corr}_{m,y}(n)
 +(\log m+\operatorname{tameDifferent}(m))u_m(n)}{\sqrt n},
\]

where \(e(y)=\sum_{t\le y}\Lambda(t)/t-\log y+\gamma\) and the proved floor
roundoff satisfies \(0\le r\le1/y\). The explicit conductor-correction theorem
bounds the second bracket by \(4\sqrt{\phi(m)}\log m/y\). Therefore

\[
|r_{m,N}(n)|\le C_m b(y)/\sqrt n.
\]

Apply finite Cauchy–Schwarz to the complete coefficient family at each row,
then sum rows. The coefficient mass and conductor cost factor out, leaving
exactly \(B_N\). This controls all mixed residual interactions together.

The proved Mertens finite part gives \(e(y)\to0\), so \(b(y)^2\to0\) and this
sequence is bounded. The existing complementary-quotient harmonic mean theorem
then yields \(B_N/\log N\to0\). No family-dependent smallness premise is used.

## Formal closure

Module:
`formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/OneArithmeticRemainderControlsEveryRamanujanResidual.lean`

Public declarations include:

- `abs_normalizedRamanujanMode_le_sqrt_totient`
- `abs_ramanujanPrimeResidual_le`
- `ramanujanPrimeResidual_family_sq_le`
- `tendsto_primeMertensRemainderProfile`
- `tendsto_primeMertensSquareBudget_div_log`

The complete module passes its final individual `lake --old env lean` audit.
The three printed capstones cover these dependencies and use only `propext`,
`Classical.choice`, and `Quot.sound`. The programme umbrella imports the module;
no umbrella build is performed.

## Scope

For growing families the explicit normalized residual cost is
\(B_N\sum_{m\in S}C_m^2/\log N\); the Gram cost is supplied separately by
`GrowingRamanujanFamiliesHaveAUniformGramBudget`. An absolute bound on \(B_N\)
would provide a stronger growth schedule. Energy separation, the modal
complement, and continuous Gamma/pole transfer remain separate obligations.
This is a finite prime-matrix approximation budget in \(\ell^2\).
