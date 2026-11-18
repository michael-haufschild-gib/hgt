# Equal-prime contribution to the variance of the ordinary-prime wave

For the continuous state representative Φ, the equal-prime term in the covariance at fixed lag h satisfies
$$
\frac1t\sum_p\frac{(\log p)^2}{p}\,\Phi(t-\log p)\Phi(t+h-\log p)
\longrightarrow \int_{\mathbb R}\Phi(u)\Phi(u+h)\,du .
$$
At zero lag the physical diagonal is asymptotic to t because the state has unit square mass. The remaining prime-pair terms involve distinct primes and the polar subtraction.

**Proof.** For any continuous ψ supported on the negative ray with |ψ(u)|≤Ce²ᵘ, the prime number theorem on dilates, tested at g(y)=ψ(−log y)/y for y>0 and g=0 elsewhere, gives Σₚ(log p)ψ(t−log p)/p→∫ψ. Indeed g vanishes on (0,1], is O(y⁻³) at infinity, and its integral is ∫ψ by y=exp(−u). The prime sums converge absolutely by comparison with Σ(log p)/p².

Put Ψ(u)=Φ(u)Φ(u+h). Both Ψ and uΨ meet the preceding bounds since |Ψ(u)|≤Cₕe⁴ᵘ and Ψ vanishes for u≥0. At u=t−log p, the extra log p in the covariance equals t−u. Dividing by t leaves the limit ∫Ψ and a bounded prime sum divided by t. Translation preserves almost-everywhere equality of F and Φ, giving the stated correlation.

For increments at lag $h>0$, replace Φ by $D_h(u)=Φ(u)-Φ(u+h)$. This is continuous, vanishes for $u≥0$, and obeys the same exponential bound with constant $C(1+e^{2h})$. Its zero-lag diagonal divided by $t$ therefore tends to $\int (F(u)-F(u+h))^2du$. Multiplication by $\log(1/h)/h$ and passage to $h\downarrow0$ identifies the iterated arithmetic limit with $8a\int F(u)^2e^{-8u}du$ by the wall modulus law. The $t$ limit is taken at fixed $h$.

**Lean.** `criticalState_equalPrimeCovariance` gives every fixed lag. `criticalState_equalPrimeIncrement_wall_energy` proves the unit zero-lag coefficient and the iterated increment limit. [Equal-prime covariance](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheEqualPrimeTermOfTheWaveCovariance.lean)
