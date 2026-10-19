# Sharp cumulative-energy law for the quasi-RH routes

- **ID:** quasi-rh-mean-square-abscissa
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [quasi-rh.md §8.4](../../../report/quasi-rh.md)
- **Statement:** The infimum of polynomial growth exponents at least one for the literal Abel cumulative square energy is \(2\Theta\); the same law holds for completed formation energy.

## Goal

Formalize the sharp mean-square transfer used by the 5/6 and 3/4 routes. A cumulative bound of exponent \(r\geq1\) must give \(\Theta\leq r/2\), rather than the weaker \(1/2+r/2\) obtained by bounding each increment separately. This supplies no numerical arithmetic estimate: growth at \(5/3+\varepsilon\) or \(3/2+\varepsilon\) remains to be proved.

## Closed paper proof

Let \(u(n)=T(n)/n\), where \(T=\operatorname{mobiusDivisorSquareRootAbelMoment}\), and \(E(N)=\sum_{2\leq n\leq N}u(n)^2\).

**Small samples from cumulative energy.** Suppose \(E(N)\leq C N^r\), \(r\geq1\). Fix \(0<\theta<1\). For large N the integer interval \(J_N=[N-\lfloor N^\theta\rfloor,N]\) lies in \([N/2,N]\), and \(|J_N|=\lfloor N^\theta\rfloor+1\geq N^\theta\). At least one \(k\in J_N\) has
\[
|u(k)|\leq(C+1)N^{(r-\theta)/2}
\leq(C+1)2^{(r-\theta)/2}k^{(r-\theta)/2}.
\]
Otherwise summing squares on this interval contradicts the prefix bound. The good level set therefore meets every sufficiently large window with gap \(N^\theta\).

**Arithmetic bootstrap.** The existing one-sided power-gap theorem applies with gap parameter \(1-\theta>0\) and amplitude exponent \((r-\theta)/2\geq0\). It gives
\[
\Theta\leq\tfrac12+\tfrac{r-\theta}{2}.
\]
Let \(\theta\uparrow1\) to obtain \(\Theta\leq r/2\). The input theorem already proves the necessary intrinsic-abscissa contraction. No pointwise bound is inferred by discarding all other energy increments.

**Converse and exact exponent.** The unconditional estimate \(u(n)=O_\varepsilon(n^{\Theta-1/2+\varepsilon})\) gives \(E(N)=O_\varepsilon(N^{2\Theta+\varepsilon})\) by summing squares. Since \(2\Theta\geq1\), the two directions yield
\[
2\Theta=\inf\{r\geq1:E(N)=O(N^r)\}.
\]
Every positive epsilon is required at a claimed endpoint.

**Completed formation energy.** Put \(G_n=\operatorname{suzukiTransitionCoreCompletedAbelSource}(n)\) and \(\mathcal F=\operatorname{suzukiCompletedFormationEnergy}\). Their existing identities give
\[
\mathcal F(n)-\mathcal F(n-1)=\frac n{n+1}G_n^2\quad(n\geq3),
\qquad |u(n)-G_n|\leq D\quad(n\geq2)
\]
for an absolute D. The second bound follows from the explicit gamma boundary of T, the polar-lattice bound \(|L(n)|\leq\sqrt n\), and the uniform polar and archimedean corrections. Thus
\[
E(N)\leq4\mathcal F(N)+2G_2^2+4|\mathcal F(2)|+2D^2N.
\]
For \(r\geq1\), a polynomial upper bound on \(\mathcal F\) implies one on E with the same exponent. Conversely, the established local-production bound \(O_\varepsilon(n^{2\Theta-1+\varepsilon})\) sums to \(\mathcal F(N)=O_\varepsilon(N^{2\Theta+\varepsilon})\). Therefore the exact infimum law also holds for \(\mathcal F\).

## Corpus inputs and scope

- `zetaZeroAbscissa_le_of_powerGaps_mobiusDivisorSquareRootAbel_le_rpow` accepts every fixed positive power-gap saving and a one-sided bound on its sampling set.
- `exists_mobiusDivisorSquareRootAbelMoment_subpower_zetaZeroAbscissa` supplies the unconditional converse.
- `suzukiCompletedFormationEnergy_succ_sub` supplies the exact positive increment.
- `exists_suzukiCompletedFormationEnergy_sub_le_rpow_zetaZeroAbscissa` supplies the unconditional cumulative upper exponent after summation.
- The proof is a new composition of these inspected corpus statements and the finite-window averaging argument. External novelty is unclaimed.

## High-dilation covariance reduction

Let \(a_{M,d}=\operatorname{mobiusDivisorDilationChannel}(M,d)\),
\(D_\varphi(M)=\lfloor M^\varphi\rfloor\), and
\(I_{M,D}=[D+1,M-1]\cap\mathbb N\). Define the ordered off-diagonal sum
\[
V_\varphi(X)=\sum_{M=2}^{X}\frac1{M^2}
 \sum_{d\in I_{M,D_\varphi(M)}}
 \sum_{e\in I_{M,D_\varphi(M)}\setminus\{d\}}a_{M,d}a_{M,e}.
\]
The new channel ceiling \(|a_{M,d}|\leq(3/5)\sqrt M\) proves
\[
0\leq\sum_{M=2}^{X}\frac1{M^2}\sum_{d\in I_{M,D_\varphi(M)}}a_{M,d}^2
\leq\frac9{25}X.
\]
Thus the cumulative tail square energy differs from \(V_\varphi\) by a nonnegative
quantity at most \(9X/25\). This is an arithmetic bound on the literal diagonal,
not an estimate for its cross terms.

For \(\varphi\geq1/2\), the paid head contributes at most
\((9/25)X^{2\varphi}\) to cumulative square energy. Combining the head/tail identity
with \((x+y)^2\leq2x^2+2y^2\), a one-sided upper estimate
\(V_\varphi(X)=O_\varepsilon(X^{2b+\varepsilon})\), \(b\geq\varphi\), suffices for
\(\Theta\leq b\). Conversely that strip supplies the same upper estimate. In particular
\(\varphi=b=5/6\) and \(\varphi=b=3/4\) retain small quotient ranges
\(q\leq M^{1/6}\) and \(q\leq M^{1/4}\), respectively.
At \(\varphi=1/2\), the infimum of upper exponents \(r\geq1\) for
\(V_{1/2}\) is exactly \(2\Theta\). The new arithmetic conjecture is the explicit
off-diagonal estimate at the two target rates; neither the diagonal ceiling nor
complete-rectangle factorization proves it.

## Gates

- [x] Identify literal sources and prove the sharp transfer on paper.
- [x] Formalize finite-window averaging and its application to the actual Abel source.
- [x] Formalize the exact cumulative Abel-energy exponent law.
- [x] Transfer the sharp receiver and exact exponent law to completed formation energy.
- [x] Formalize the paid dilation diagonal and the signed covariance exponent reduction.
- [x] Focused leaf audits, standard-axiom audits, umbrella wiring.
- [x] Run formal lint: no error in either leaf; that audit reported unrelated unreachable module `SquareRootThreshold.OnLineShadowIndistinguishability`.

`QuasiRHMeanSquareAbscissa.lean` and `QuasiRHDilationCovarianceAbscissa.lean` pass focused `lake --old env lean` checks without warnings. All 22 public theorem audits, including the two averaging helpers exposed for power-mesh reuse, report only `propext`, `Classical.choice`, and `Quot.sound`.

Numerical bounds for 5/6 and 3/4 remain separate arithmetic obligations.
