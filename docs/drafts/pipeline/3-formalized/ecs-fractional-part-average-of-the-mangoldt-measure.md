# A signed fractional-part average of the Mangoldt measure

For every real $x\ge1$,
\[
\lim_{Y\to\infty}\left[\sum_{n\le Y}\Lambda(n)\{x/n\}
-x\bigl(\log(Y/x)+1-\gamma\bigr)\right]
=x(\log x-1)-\log(\lfloor x\rfloor!).
\]
The absolute value of the limit is at most $1+\log x$. The logarithmic density of the test has positive-ray integral $\int_0^\infty e^{-v}\{e^v\}\,dv=1-\gamma$.

For $Y\ge x$, splitting the fractional part leaves $x\sum_{n\le Y}\Lambda(n)/n$ minus $\sum_{n\le x}\Lambda(n)\lfloor x/n\rfloor$. The second sum is $\log(\lfloor x\rfloor!)$ by the divisor identity. The [reciprocal Mangoldt remainder](../../../../formal/GaloisForLFunctions/RHTower/MertensVonMangoldtEulerConstant.lean) tends to $-\gamma$ after subtracting $\log Y$. The [Stirling and floor bounds](../../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheStirlingErrorSplits.lean) give the uniform bound in $x$. On $[\log n,\log(n+1))$, the density is $1-ne^{-v}$. Integrating and summing through $\log N$ gives $1+\log N-H_N$.

**Lean.** [fractionalMangoldtError_eq, tendsto_fractionalMangoldtError, fractional_density_integral](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Analysis/TheFractionalPartAverageOfTheMangoldtMeasure.lean).
