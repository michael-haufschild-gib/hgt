# The original prime edges retain a reserve after Gamma coupling

- **ID:** acs-haar-prime-edges-retain-gamma-reserve
- **Stage:** 3-formalized
- **Type:** THEOREM — every claim below formalized and checked in Lean
- **Route:** ACS: full-source effectivity → Hodge index → RH.
- **Parent:** [joint signed graph payment](../1-in-progress/acs-haar-gamma-signed-graph-payment.md)
- **Result:** Every actual prime-power edge remains aligned
  after its full Gamma coupling, with an explicit positive reserve, and
  the payment sums over the original finite source without double counting.

## Exact source theorem

Write n_a=2a+1 and n_b=m*n_a. For a>=1 and m>=3,

`0 <= J_ab <= log(2)*M_b/sqrt(m)`.

If Lambda(m)>0, oddness forces its underlying prime to be at least
three. Thus the original arithmetic coupling exceeds J_ab by at least
`(log(3)-log(2))*M_b/sqrt(m)`. In the already formalized ground coordinates,
the Gamma graph on these arithmetic edges consumes at most
`log(2)/log(3)` of their original divisor-square energy. The combined
contribution of both poles has nonpositive cross entries in the oriented Haar basis;
the actual full-Weil prime-edge sign retains this reserve.

This pays the literal arithmetic-edge subset of the original Gamma graph.
Non-arithmetic Gamma edges and the signed diagonal still
need their joint comparison; full Haar positivity is not claimed.

## Formalized argument

Put n=2a+1. On the original rectangle, exp(y-x) is at least
(mn-1)/(n+1), hence at least 2 and at least m/2. Therefore
1-exp(-2(y-x))>=3/4 and sqrt(m)*exp(-(y-x)/2)<=3/2. The actual Gamma
density k(t)=exp(-t/2)/(1-exp(-2t)) satisfies sqrt(m)*k(y-x)<=2.

For P(x,y)=H_a(x)H_b(y), the original restricted-product volume
integral of P is zero and its absolute integral is 4*M_a*M_b.
The pointwise inequality
`-P*k <= (abs(P)-P)/sqrt(m)` gives
`J_ab <= 4*M_a*M_b/sqrt(m)` after integration. The exact cell mass
obeys `4*M_a<=log(a+1)-log(a)<=log(2)`. All integrations use the original
Gamma rectangle measure through its actual density; no singular
endpoint or interaction is discarded.

For a nonzero original Mangoldt channel, n_b=m*n_a is odd, hence m
and its least prime factor are odd. Thus Lambda(m)=log(minFac(m))
is at least log(3). Write theta=log(2)/log(3), with 0<=theta<1.
Then `sqrt(m)*J_ab<=theta*Lambda(m)*M_b`.

Define G_prime as the sum over the literal nonzero arithmetic channels
of `sqrt(m)*J_ab*(d_a/sqrt(m)-d_b)^2`, and Q_res with coefficient
`Lambda(m)*M_b-sqrt(m)*J_ab`. Exact finite summation gives

`Q_res+G_prime=Q_X`, `Q_res>=(1-theta)*Q_X>=0`,
`G_prime<=theta*Q_X`.

With u_a=sqrt(n_a)*d_a and K_ab=J_ab/(sqrt(n_a)*sqrt(n_b)), each
summand of G_prime is exactly `K_ab*(u_a-u_b)^2`. A fixed ordered
pair has at most one multiplier, and m>=2 forces a<b. Hence the
payment is a subset of the original undirected Gamma graph and
`0<=G_prime<=G_X`.

Writing R_X for the full absent-root charge, the exact source retains

`D_X-G_prime=Q_res+R_X`,
`W(h)+(G_X-G_prime)=Q_res+R_X+P(h)+sum_a V_X(a)*u_a^2`.

This spends no root charge, pole budget, or signed potential. Their
combined payment of the remaining Gamma graph is still open.

Finally let U_a and V_a be the original nonnegative Laplace moments
at rate 1/2. Exact exponential-moment linearity identifies the pole
matrix as `-(U_a*V_b+U_b*V_a)`. With A_ab the original finite prime
matrix, the original Weil interaction matrix is therefore
`J_ab-A_ab-A_ba-(U_a*V_b+U_b*V_a)`, and its complete quadratic
expansion retains the original Gamma/central diagonal. Every actual
prime channel satisfies

`interaction_X(a,b)<=-(log(3)-log(2))*M_b/sqrt(m)<0`.

This is an entry sign and a paid edge subset. It does not imply
positivity of the full signed Haar form.

## Checked Lean declarations

File: [TheHaarPrimeEdgesRetainTheirGammaReserve.lean](../../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHaarPrimeEdgesRetainTheirGammaReserve.lean).

- `haarGammaCoupling_le_prime_scale`
- `haarPrimeGammaShare_nonneg`, `haarPrimeGammaShare_lt_one`
- `haarPrimeGammaConductance_pos`
- `haarPrimeGammaReserve_add_graph`, `haarPrimeGammaReserve_ge`,
  `haarPrimeGammaReserve_nonneg`
- `haarPrimeGammaGraphEnergy_nonneg`,
  `haarPrimeGammaGraphEnergy_le_divisorSquares`
- `haar_prime_gamma_square_eq_graph`,
  `haarPrimeGammaGraphEnergy_eq_ground`, `haarPrimeGammaGraphEnergy_le_graph`
- `haarGammaGraphEnergy_sub_prime_nonneg`
- `haarPrimeLogDefect_sub_primeGamma_eq`,
  `haarSectionProfile_roughWeil_add_remaining_graph_eq`
- `haarPoleCoupling_nonneg`, `haarSectionProfile_poles_eq_matrix`
- `haarSectionProfile_roughWeil_eq_interaction_matrix`
- `haarWeilInteraction_prime_edge_le`, `haarWeilInteraction_prime_edge_neg`

## Validation

The complete source passed this direct check from `formal/`, with exit 0,
no errors, and no warnings:

```sh
lake --old env lean GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHaarPrimeEdgesRetainTheirGammaReserve.lean
```

The module is imported by the ACS umbrella. Its required graph dependency
olean was built only because this source imports it. Existing oleans
were preserved; no umbrella build, axiom check, web search, novelty check,
or numerical experiment was run.

The [positive Gamma graph](acs-haar-gamma-positive-laplace-graph.md)
supplies the already checked moment signs and original full-source identity.
The remaining signed graph payment and full ACS route remain open.
