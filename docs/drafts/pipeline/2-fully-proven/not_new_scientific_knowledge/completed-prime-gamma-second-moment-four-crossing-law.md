# Completed prime--Gamma second-moment four-crossing law

- **ID:** `completed-prime-gamma-second-moment-four-crossing-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [POSITIVE NO-GO SUCCESSOR]`
- **Source:** the falsified parity route
  `docs/drafts/pipeline/5-failed/completed-prime-gamma-polynomial-even-factorization-to-rh.md`
- **Statement:** The second normalized odd completed logarithmic-derivative moment is positive at
  the functional-equation center, negative at `10`, and positive again far to the right; hence it
  has at least four real sign-changing zeros after functional-equation reflection.

## The scalar function

Put

\[
 c_2(x)=\frac1{5!}\left(\frac{\xi'}{\xi}\right)^{(5)}(x)
       =\operatorname{Re}\bigl(\texttt{completedOddLogDerivMoment}(x,2)\bigr).
\]

This is the moving polynomial test `Q_P` for `P=X`, because `P^2=X^2`.  It is real analytic on
the real axis: the completed Xi function has no real zero, and the existing Schwarz law makes the
moment real there.  The functional equation gives

\[
 c_2(1-x)=c_2(x).                                                   \tag{1}
\]

## Strict positivity at the center

For a multiplicity copy `q` of the Xi divisor, let

\[
 \lambda_q=-\left(\rho_q-\frac12\right)^{-2}=a_q+i b_q.
\]

The formal reciprocal-square sector estimates give

\[
 a_q>0,\qquad b_q^2\le \frac1{84}a_q^2.
\]

Consequently

\[
 \operatorname{Re}(\lambda_q^3)
 =a_q(a_q^2-3b_q^2)
 \ge \frac{27}{28}a_q^3>0.                                        \tag{2}
\]

The multiplicity-exact reciprocal moments are absolutely summable, the Xi divisor is nonempty,
and the established center value law identifies their third moment with `c_2(1/2)`.  Summing (2)
therefore gives

\[
 c_2(1/2)=\sum_q\operatorname{Re}(\lambda_q^3)>0.                  \tag{3}
\]

This strengthens the existing termwise nonnegativity theorem at exactly the one scalar needed
below.

## A rigorous negative value at ten

For real `x>1`, logarithmically differentiating the completed Euler product and using the
polygamma series gives the exact identity

\[
 c_2(x)=
 -\frac1{(x-1)^6}
 +\sum_{j\ge1}\frac1{(x+2j)^6}
 +\frac1{120}\sum_{m\ge2}\frac{\Lambda(m)(\log m)^5}{m^x}.        \tag{4}
\]

The `-x^{-6}` rational term cancels the `j=0` term of the Gamma series.  All remaining terms in
(4), except `-(x-1)^{-6}`, are nonnegative.

At `x=10`, the Gamma tail satisfies

\[
 \begin{aligned}
 G&=\sum_{j\ge1}(10+2j)^{-6}
   =\frac1{64}\sum_{m\ge6}m^{-6}\\
 &\le \frac1{64}\left(\sum_{m=6}^{20}m^{-6}
             +\int_{20}^{\infty}t^{-6}\,dt\right)\\
 &=\frac{6077519524707474292238504899835016239219072897}
 {10185786091039001214960337332697685248111017984000000}
 <\frac3{5000000}.                                                 \tag{5}
 \end{aligned}
\]

Only `m=2,3,4,5,7,8,9` contribute to the Euler sum below `11`.  The elementary exponential-series
bounds

\[
 \log2<\frac7{10},\qquad \log3<\frac{11}{10},\qquad
 \log5<\frac{13}{8},\qquad \log7<2
\]

give

\[
 \begin{aligned}
 E_{\le10}
 &\le \frac1{120}\left(
 \frac{(7/10)^6}{2^{10}}+\frac{(11/10)^6}{3^{10}}
 +\frac{32(7/10)^6}{4^{10}}+\frac{(13/8)^6}{5^{10}}
 +\frac{2^6}{7^{10}}+\frac{243(7/10)^6}{8^{10}}
 +\frac{32(11/10)^6}{9^{10}}\right)\\
 &=\frac{99568316000267035965797579044979}
 {79317063608850487394382643200000000000}
 <\frac{63}{50000000}.                                            \tag{6}
 \end{aligned}
\]

For `m>=11`, use `Lambda(m)<=log m` and `log m<=sqrt m`.  The latter follows by differentiating
`sqrt x-log x` on `[11,infty)` and checking its value at `11`.  Hence

\[
 E_{\ge11}
 \le\frac1{120}\sum_{m\ge11}m^{-7}
 \le\frac1{120}\left(11^{-7}+\int_{11}^{\infty}t^{-7}\,dt\right)
 =\frac{17}{14030763120}<\frac1{800000000}.                        \tag{7}
\]

Combining (4)--(7),

\[
 c_2(10)
 <-\frac1{9^6}+\frac3{5000000}+\frac{63}{50000000}
      +\frac1{800000000}
 =-\frac1{9^6}+\frac{1489}{800000000}<0,                          \tag{8}
\]

because

\[
 \frac1{9^6}-\frac{1489}{800000000}
 =\frac{8684351}{425152800000000}>0.
\]

All estimates are rational after the four displayed logarithm bounds; those bounds follow by
truncating the positive Taylor series of `exp` at orders `3`, `5`, `5`, and `5`, respectively.

## Two right crossings and their reflections

The formal far-right asymptotic at `k=2` is

\[
 x^5c_2(x)\longrightarrow\frac1{10}.                              \tag{9}
\]

Thus `c_2(x)>0` for all sufficiently large positive `x`.  Equations (3), (8), and (9), together
with real analyticity, imply the existence of odd-multiplicity real zeros

\[
 \alpha\in(1/2,10),\qquad \beta\in(10,\infty).
\]

Equation (1) supplies the distinct odd-multiplicity zeros `1-alpha` and `1-beta`.  Therefore
`c_2` has at least four real sign-changing zeros, two on each side of the functional-equation
center.

In particular `CompletedOddLogDerivPolynomialRightEvenFactorization` is false already for
`P=X` and `R=10`: an even-root factorization with a continuous nowhere-zero cofactor cannot carry
the strict sign change from (3) to (8).

## Gates

- [x] 0 -> 1 in-progress: explicit `P=X` specialization and rational witness selected
- [x] 1 -> 2 fully-proven: exact source decomposition and strict rational bounds proved
- [x] 2 -> 3 formalized: exact `x=10` Euler/Gamma sign certificate and the resulting parity no-go
  are Lean-proved; the broader crossing package remains paper-level
- [ ] 3 -> 4 publication-ready: not a standalone publication target

## Lean certificate update — 2026-08-15

The exact `x=10` sign certificate is now formalized in
`formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaSecondMomentCenterPositive.lean`:

```text
RHTower.completedEulerMoment_two_ten_lt
RHTower.completedOddLogDerivMoment_two_ten_re_neg
RHTower.not_completedOddLogDerivPolynomialRightEvenFactorization
```

The proof uses the source identity already formalized there, the closed Gamma tail bound, a finite
Euler head bounded with certified logarithm enclosures, and the existing exact p-series tail
theorem. `lake build GaloisForLFunctions.RHTower.CompletedPrimeGammaSecondMomentCenterPositive`
and `#print axioms` of all three declarations pass with only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` axioms.

Thus the exact `P = X`, `R = 10` obstruction is Lean-closed. The broader intermediate-value and
four-crossing packaging remains paper-level in this card, so its stage is not promoted merely from
the terminal sign certificate.
