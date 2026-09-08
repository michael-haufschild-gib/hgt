# CCM-FU: fixed-core energy coefficient and signed reserve

- **Stage:** 1-in-progress; signed source analysis.
- **Parent:** [fixed-core reserve signs](ccm-fu-fixed-core-reserve-sign.md).
- **Goal:** Actual signed reserve control through changing processed cores, uniform signed Abel bound, RH. Goal remains open.

## Closed source chain

The [fixed-core profile](../3-formalized/ccm-fu-fixed-core-profile.md) gives
F_P(M,R)=mu(r)*sqrt(r)*I_P(M,r), r=product(R), and the exact complete
squarefree energy sum. Every nonempty fixed core also cancels the head's
square-root main term.

The [density and weighted moments](../3-formalized/ccm-fu-fixed-core-density-moments.md)
prove rho_P=(6/pi²)*product_(p in P) p/(p+1), all half-integer source moments,
cutoff rescaling, and every explicit actual quotient-block limit.

The [complete energy limit](../3-formalized/ccm-fu-fixed-core-energy-limit.md)
now assembles all quotient depths for every finite prime core P, including
P=empty. With a_n,b_n the actual square-root-clock slope and intercept, put
Phi_n(c)=a_n²*c+(4/3)*a_n*b_n*c*sqrt(c)+b_n²*c²/2. Then

`Q_P(M)/M² -> kappa_P=sum_(n>=1) rho_P*[Phi_n(1/n)-Phi_n(1/(n+1))]`.

The summands are nonnegative and summable. The complete quotient tail above
T is at most C_P²*M²/T, where C_P=(3/5)*2^(card(P)-1), with natural truncated
subtraction. Thus neither source density nor infinite-block assembly is
an open prerequisite for the fixed-core coefficient. The bound grows with
processed cardinality and does not provide reserve renewal.

## Exact remaining target

The [literal prime correlation](../3-formalized/ccm-fu-fixed-core-prime-correlation.md)
now identifies kappa_P-kappa_(P+p) with an explicit absolutely convergent
signed series. Its finite-prefix error is at most 2*C_P²/T. Prove a usable
sign and size law for this actual series, then control it as P changes. A fixed-core
limit does not produce a full admissible prime selection.

One proposed analytic representation is

`kappa_P=rho_P*integral_1^infinity G_P(x)^2/x^3 dx`,

where G_P is the literal continuous square-root interpolation of H_P,
extended by zero below one. This integral identification is not yet formalised.
The exact prime update should give
G_(P+p)(x)=G_P(x)-sqrt(p)*G_P(x/p). Together with the density factor
p/(p+1), the diagonal terms would cancel to give

`kappa_P-kappa_(P+p)`

`=2*rho_P*p*sqrt(p)/(p+1)*integral_1^infinity G_P(x)*G_P(x/p)/x^3 dx`.

The continuous update and integral passage remain optional representation
work. The direct arithmetic correlation series is already formalised, so
these steps are not prerequisites for its sign problem. The essential
missing arithmetic statement is a supply of signed reserve sufficient for
renewal through changing cores; no positivity is assumed.

No experiment is planned for the density, moments or block assembly: those
steps follow from their displayed proofs. The completed fixed-core reserve
screen must not be repeated or enlarged merely to illustrate convergence.
