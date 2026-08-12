# Route E Deninger vacuum finite-dilation fracture

- **ID:** `ROUTE-E-DENINGER-VACUUM-FINITE-DILATION-FRACTURE-001`
- **Stage:** 2-fully-proven
- **Type:** EXACT DOMAIN CLASSIFICATION / NO-GO WITH POSITIVE COLLAR DECOMPOSITION
- **Parent:** `route-e-cofinal-parity-energy-covariance-accumulation.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** All three exact theorem blocks are formalized. Section 1 and its stronger
  analytic log-pull classification are in
  `RHTower/RouteEDeningerVacuumFiniteDilationFracture.lean`; Section 2's complete finite-aperture
  jet was already formalized; Section 3 is in
  `RHTower/RouteEDeningerVacuumCollarDecomposition.lean`. Claim-complete Stage 3 children certify
  finite-dilation fracture and positive collar decomposition separately; this parent remains the
  Stage 2 synthesis card.

## 1. The finite-dilation theorem

Put
\[
 V(t)=e^{-e^t}.
\]
Let \(a_1,\ldots,a_r>0\) be distinct and let \(c_1,\ldots,c_r\in\mathbb C\).  Then
\[
 F(t)=\sum_{j=1}^r c_jV(t+\log a_j)
     =\sum_{j=1}^r c_je^{-a_je^t}                       \tag{1}
\]
belongs to Deninger's exponentially decreasing Meyer source only when every \(c_j=0\).

Indeed, with \(x=e^t\),
\[
 G(x):=F(\log x)=\sum_{j=1}^r c_je^{-a_jx}
 =\sum_{m\ge0}{(-1)^m\over m!}
      \left(\sum_{j=1}^r c_ja_j^m\right)x^m.           \tag{2}
\]
Meyer decay at the left collar says \(F(t)=O(e^{Mt})\) as \(t\to-\infty\) for every
\(M>0\).  Hence \(G(x)=O(x^M)\) as \(x\downarrow0\) for every \(M\), so every coefficient in
`(2)` vanishes.  In particular
\[
 sum_{j=1}^r c_ja_j^m=0\qquad(0\le m<r).               \tag{3}
\]
The Vandermonde matrix \((a_j^m)_{0\le m<r,1\le j\le r}\) is invertible, proving
\(c_1=\cdots=c_r=0\).

This is stronger than observing that the vacuum itself is not Meyer: no nonzero finite recurrence,
finite prime-dilation mask, or finite difference of vacuum dilates enters the strict adiabatic
domain.

## 2. Exact Route E specialization

For a nonempty finite prime aperture \(S\),
\[
 J_S(x)=\prod_{p\in S}(I-T_p)e^{-x},
 \qquad (T_pf)(x)=f(px).                                \tag{4}
\]
Its Taylor expansion starts at order exactly one:
\[
 J_S(x)=(-1)^{|S|+1}\prod_{p\in S}(p-1)x+O_S(x^2).      \tag{5}
\]
The constant coefficient vanishes, while the coefficient of \(x\) is
\(-\prod_{p\in S}(1-p)\ne0\).  Thus every nonempty finite Route E current has only first-order
left-collar vanishing, independently of aperture size.  Prime insertion amplifies its first jet;
it never moves the vacuum into Meyer space.

Existing Lean theorem
`iteratedDeriv_finitePrimeParityPartition_zero_eq_prod` in
`RHTower/MobiusExponentialGibbsBoundary.lean` certifies the complete finite-aperture jet formula
behind `(5)`. `RHTower/RouteEDeningerVacuumFiniteDilationFracture.lean` proves `(1)` as the exact
iff `exists_deningerExpSchwartz_shiftedVacuum_iff` and proves the stronger survivor: any analytic
log-pull in the strict source has infinite analytic order at zero, while any entire log-pull is
identically zero. The claim-complete formalized child is
`../../3-formalized/new_scientific_knowledge/route-e-deninger-analytic-log-pull-finite-dilation-fracture.md`.
`RHTower/DeningerExpSchwartz.lean` supplies the actual faster-than-every-exponential two-sided
source used by these proofs.

## 3. Exact positive collar decomposition

Choose one smooth cutoff \(\chi\) with \(\chi(x)=1\) on \(0<x\le1\) and \(\chi(x)=0\) on
\(x\ge2\).  Split
\[
 e^{-x}=H_{\rm Mey}(x)+C_{\rm vac}(x),
 \quad
 H_{\rm Mey}(x)=(1-\chi(x))e^{-x},
 \quad
 C_{\rm vac}(x)=\chi(x)e^{-x}.                         \tag{6}
\]
Then \(t\mapsto H_{\rm Mey}(e^t)\) is in `DeningerExpSchwartz`: it vanishes on a complete left
tail and decays superexponentially on the right.  Consequently
\[
 \sum_{n\ge1}\mu(n)e^{-nx}
 =\sum_{n\ge1}\mu(n)H_{\rm Mey}(nx)
  +\sum_{n\le2/x}\mu(n)C_{\rm vac}(nx).                \tag{7}
\]
The tail kernel is a literal strict Deninger-source vector, and its Möbius series is absolutely
summable at every fixed \(x>0\). This statement does **not** assert that the full Möbius tail sum,
as a function of logarithmic radius, is itself a strict-source vector. The second term is a fixed
compact-collar smoothing of Mertens mass through scale \(2/x\). It contains the entire non-Meyer
source and is exactly the Route E hard component.

Thus the adiabatic endpoint gives a canonical easy-tail/hard-collar decomposition, but no estimate
for the hard collar.  Calling `(7)` a Route E closure would merely rename the Möbius source.

## 4. Conjecture--proof--failure loop

1. **Differentiate vacuum once to enter Meyer space.** Failed: \(e^te^{-e^t}\) has only
   first-order exponential decay at the left collar; Meyer requires every exponential order.
2. **Apply finitely many prime-periodization defects.** Failed sharply by `(1)`--`(5)`; every
   nonzero finite mask retains a nonzero finite Taylor grade.
3. **The vacuum is one missing scalar boundary charge.** Failed as an operator-domain statement:
   its complete analytic jet survives and finite dilation acts diagonally on every grade.
4. **Split off one fixed collar vector.** Proved by `(6)`--`(7)`.  This is a useful exact
   classification, but its inverse is the smoothed Mertens source itself.

## 5. Frontier consequence

The new Deninger adiabatic theorems reduce no arithmetic burden in Route E. Their maximal honest
use is `(7)`: strict endpoint control certifies the tail kernel and isolates one fixed vacuum
collar whose Möbius inverse remains `OPEN-SOURCE-001`. Any viable Deninger continuation must add an
independent estimate on that collar; topology, distributional convergence, and the exact
Meyer--Poisson kernel do not supply it.
