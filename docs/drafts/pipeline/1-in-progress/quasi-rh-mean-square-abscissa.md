# Sharp cumulative-energy law for the quasi-RH routes

- **ID:** quasi-rh-mean-square-abscissa
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
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

## Gates

- [x] Identify literal sources and prove the sharp transfer on paper.
- [ ] Formalize finite-window averaging and its application to the actual Abel source.
- [ ] Formalize the exact cumulative Abel-energy exponent law.
- [ ] Transfer the sharp receiver and exact exponent law to completed formation energy.
- [ ] Focused leaf audit, standard-axiom audit, umbrella wiring, formal lint.

Numerical bounds for 5/6 and 3/4 remain separate arithmetic obligations.
