# Positive ordinary-prime windows of bounded width

Let E be the signed ordinary-prime wave after polar subtraction and B=ℒF(0)/2. For some δ>0 the positive windows
$$
W_{n,T}(t)=1_{t>0}(t/n)^n e^{n-t}\operatorname{sinc}^4(\delta(t-T)),\qquad n\le T<n+1,
$$
have bounded centred second moment after normalization, and their E-averages tend to −B uniformly in T.

**Signed integral.** The transform of E+B extends around the closed unit disk centred at −1. Compactness gives η>0, R>1 and a common bound on all disks of radius R centred at −1+iξ for |ξ|≤η. Choose η small enough for the integral to represent the transform near each centre. Cauchy's estimate bounds every modulated gamma average of E+B by C/Rⁿ, uniformly in ξ. Put δ=η/4. Four independent uniform frequencies in [−δ,δ] have a sum supported in [−η,η] with characteristic function sinc⁴(δu). Integrating the modulated estimate against this law with phase exp(−iξT) inserts the positive factor sinc⁴(δ(t−T)) into the physical integral, uniformly in T. Fubini holds because the gamma test times the absolute damped datum is integrable. The change from gamma normalization to the displayed window costs at most e√n by Stirling's upper bound.

**Mass and width.** For t>0 the factor (t/n)ⁿexp(n−t) is at most one by log x≤x−1. For t∈[T,T+d] with n≤T<n+1 and 0<d≤1, it is at least exp(−2). Choose d so that the sinc fourth power is at least one half on [0,d]. Window mass is thus bounded below independently of n,T. Its centred second moment is bounded above by the integral of u²sinc⁴(δu), finite by the fourth-power tail. Dividing the signed integral by the mass gives the asserted limit. The tails of the windows have unbounded support. The unsmoothed one-sided ordinary-prime estimate remains open.

**Lean.** `ordinaryPrimeError_positive_local_windows` bounds the signed integral uniformly for $n≤T≤n+1$. `localizedPrimeWindow_mass_and_width` bounds the mass below and the centred second moment above. [Signed integral](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/PositiveLocalAveragesOfTheOrdinaryPrimeError.lean) · [Window bounds](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Analysis/SincWindowsOnTheLogarithmicAxis.lean)
