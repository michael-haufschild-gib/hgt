# Complete native forms on a logarithmic rank horizon

**ID:** completed-arithmetic-forms-hermite-rank-horizon  
**Stage:** Formalized  
**Type:** Complete-source coercivity and successor estimate

Let $q=\pi e^{2x}$, $D=50e\exp(2e)$, $A=27e^{3\pi}/399$, and
$$P_N=N\bigl(De^2(N+1)(N+2)^2+Ae^8\bigr),\qquad
S_N=16(N+2)^2+2P_N.$$
The complete native balanced signed head $H_N$ and its Gaussian comparison $G_N$ satisfy
$$|v^{\mathsf T}(H_N-G_N)v|\le(P_N/q)v^{\mathsf T}G_Nv,
\qquad q\ge16(N+2)^2.$$
The native head retains a strict half-Gaussian reserve when $q>2P_N$.

The monic Hermite kernel is
$K_q(z,w)=e^{-4z^2-4w^2}F_q(z+w)$.
Its source-relative error satisfies
$$|K_q-e^{8zw}|\le DR^4e^{8|z||w|}/q,$$
for $R\ge1$, $|z+w|\le R$, and $q\ge\max(3,4R^2,R^4)$.
Separate radii $r_n=\sqrt{(n+1)/8}$ satisfy
$$\frac{n!}{r_n^n}=\sqrt{\frac{n!}{(n+1)^n}}\sqrt{8^nn!},\qquad
\sqrt{\frac{i!j!}{(i+1)^i(j+1)^j}}e^{8r_ir_j}\le e^2(N+1).$$
They pay the first-atom mixed entries in the exact Gaussian diagonal norm.
The complete native remainder has transformed entry cost at most
$$N^2(N!)^2e^8A24^{2N}q^Ne^{-3q}\le Ae^8/q
\quad\text{on }q\ge16(N+2)^2.$$
The determinant-one Hermite congruence returns the same relative form cost to
every original source direction.

The embedding $i\mapsto2i+s$ places shifted rank $n$ inside full signed dimension
$M=2n+s$. For the exact rank-$n$ successor use $M=2(n+1)+s$:
$$|S_n^{\rm native}-C_{n,s}|\le(P_M/q)C_{n,s},
\qquad q\ge16(M+2)^2,\quad q>P_M.$$
On $q\ge S_M$, the successor lies strictly between $C_{n,s}/2$ and $3C_{n,s}/2$.
All mixed entries, the complete inverse head, and the infinite theta remainder are retained.

The exact physical source rescaling preserves strictness. Both parity blocks of
full signed rank $N$ fit in dimension $N+1$.
For $C=16+2De^2+2Ae^8$, one has $S_M\le C(M+2)^4$; hence
$$x\ge\max(0,\tfrac12\log(C/\pi)+2\log(N+3))$$
makes the literal complete native signed rank-$N$ head positive definite.
This is a rank-dependent source ray. Compact-center integrated compensation is a separate question.

Lean modules in `CompletedArithmeticForms/`:
`GaussianRelativeKernel`, `WickCauchyPayment`, `HermiteRadiusPayment`,
`HermiteJetCongruence`, `HermiteSourceBound`, `HermiteNativeTail`,
`NativeHermiteHorizon`, `PolynomialRankHorizon`, and `NativePhysicalRankHorizon`.
The source, full-form, shifted-successor, and physical-rescaling capstones each
have audited axiom set `propext`, `Classical.choice`, `Quot.sound`.
