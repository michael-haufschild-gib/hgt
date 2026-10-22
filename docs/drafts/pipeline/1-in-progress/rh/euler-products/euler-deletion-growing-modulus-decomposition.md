# Growing deletion moduli: the retained arithmetic terms

Status: [BRIDGE] the exact infinite decomposition, ordinary-cutoff convergence, and absolute convergence of its remainder series are proved in Lean. The uniform bound `W_p=O_s(p^(-2 Re(s)))` and its resulting decay are also formalized in `EulerDeletionRemainderRefinementObstruction`; [arithmetic reconstruction](../../euler-deletion-remainder-mobius-inversion.md) records the further exact inverse and nonvanishing consequences. The first scaled limit `p^(2 Re(s))W_p -> -conjugate(s) sum n^(-2 Re(s)-1)/12` is now formalized in `EulerDeletionModulusFirstCoefficient`; [its source proof and global-class consequences](../../../3-formalized/arithmetic-global-minimum-classes.md) retain an explicit ordinary-remainder error. The sharper `O_s(p^(-2 Re(s)-2))` modulus error and the real-part identity for `W_1` below retain paper-proof status. No RH implication or literature novelty is claimed. This is an analysis of the existing mixed-source candidate, not a replacement proof architecture.

## Statement

Let `s` be complex, `1/2 <= sigma=Re(s)<1`, `Z=zeta(s)`, `c_p=p^(1-s)`, `alpha=2-2 sigma`, and `S_N=sum_(n=1..N)n^(-s)`. Define

`F_p(k)=S_k-c_p S_floor(k/p)-(1-c_p)Z`,

`T_p=sum_(k>=0)F_p(k)(k+1)^(-conj(s))`.

For positive integers `n`, retain the exact ordinary power-sum remainder

`R_s(n)=S_n-Z-n^(1-s)/(1-s)-(1/2)n^(-s)`.

Put

`W_p=c_p sum_(n>=1)n^(-s) R_conj(s)(pn)`,

`K=zeta(2 sigma-1)/(1-conj(s))`,

`B_sigma(p)=(1/2)zeta(2 sigma)(p^(1-2 sigma)-1)` if `sigma>1/2`, and `B_(1/2)(p)=-(1/2)log p`.

Then the full arithmetic decomposition is

**`T_p=|Z|²(c_p-1)+K(p^alpha-1)+B_sigma(p)+W_p-W_1`.**

The remainder series is absolutely convergent. Its first asymptotic term is

`W_p= -conj(s) zeta(2 sigma+1)/(12 p^(2 sigma)) + O_s(p^(-2 sigma-2))`.

The real part of the modulus-one remainder satisfies

**`Re W_1=-(1/2)|Z|²-Re K`.**

Consequently

`Re T_p=|Z|²(Re c_p-1/2)+Re K p^alpha+B_sigma(p)+Re W_p`.

This decomposition retains the complete mixed correction. It does not identify replication with Euler dilation.

## Proof

The analytic input is the ordinary Euler–Maclaurin expansion, with fixed exponent and positive integer cutoff:

`S_N=Z+N^(1-s)/(1-s)+(1/2)N^(-s)+R_s(N)`,

`R_s(N)=-(s/12)N^(-s-1)+O_s(N^(-sigma-3))`.

These estimates follow by integrating the bounded periodic Bernoulli remainder sufficiently many times; they are uniform on compact exponent sets avoiding the pole. The underlying formulas are standard, not new research claims: [DLMF 25.11(iii)](https://dlmf.nist.gov/25.11#iii). The displayed estimate gives absolute convergence of `W_p` and its stated asymptotic by comparison with `sum n^(-2 sigma-1)` and `sum n^(-2 sigma-3)`.

For fixed `p`, write `k=pm+r`, `0<=r<p`. The same expansion gives

`F_p(pm+r)=(r-(p-1)/2)(pm)^(-s)+O_(s,p)(m^(-sigma-1))`.

The leading coefficients sum to zero over a complete cell. Multiplication by `(pm+r+1)^(-conj(s))` leaves a complete-cell sum `O_(s,p)(m^(-2 sigma-1))`; the at most `p-1` terms of an incomplete last cell tend to zero. Thus ordinary-cutoff `T_p` exists also at `sigma=1/2`. For `sigma>1/2`, its individual terms are absolutely summable.

Set `U_N=S_N-Z` and

`A_N=sum_(n=1..N)U_(n-1)n^(-conj(s))`.

Finite summation by parts, with every terminal product retained, gives

`T_p(pN)=A_(pN)-c_p U_N conjugate(S_(pN))`

`             +c_p sum_(n=1..N)n^(-s) conjugate(S_(pn))`.  (1)

This finite formula is `mixedPrefix_eq_ordinary_endpoint_pairing` in `EulerDeletionMixedRefinementCarry.lean`. Its block summation-by-parts identity is `centeredBlockSum_eq_endpoint_sub_pairing`. Both hold with arbitrary complex centering, before a zeta zero is chosen.

Write `a=2 sigma`, `Q_N=sum_(n=1..N)n^(1-a)`, and `P_N=sum_(n=1..N)n^(-a)`. There is also the exact identity

`A_N=Q_N/(1-s)-P_N/2+conjugate(W_1(N))`,  (2)

where `W_1(N)` truncates its defining series. Indeed `U_(n-1)=n^(1-s)/(1-s)-(1/2)n^(-s)+R_s(n)` term by term.

First suppose `sigma>1/2`. The same power-sum expansion yields

`Q_N=N^alpha/alpha+zeta(a-1)+o(1)`, `P_N=zeta(a)+o(1)`.

Therefore `A_N-N^alpha/((1-s)alpha)` tends to

`C=zeta(a-1)/(1-s)-(1/2)zeta(a)+conjugate(W_1)`.

In the block sum in (1), insert the exact decomposition of `conjugate(S_(pn))`. Before taking limits the quantity subtracted from `A_(pN)` is

`-c_p |Z|²`

`+ p^alpha/(1-conj(s)) [U_N N^(1-conj(s))-Q_N]`

`+ (1/2)p^(1-a)[U_N N^(-conj(s))-P_N]`

`+ c_p U_N R_conj(s)(pN)-W_p(N)`.

The first bracket equals `(1-conj(s))N^alpha/((1-s)alpha)-zeta(a-1)+o(1)`. The second tends to `-zeta(a)`; the product containing `R_conj(s)(pN)` tends to zero. Subtracting the common `N^alpha` term gives

`T_p=C+c_p |Z|²+Kp^alpha+(1/2)zeta(a)p^(1-a)+W_p`.

The same equality at `p=1`, where `T_1=0`, eliminates `C` and proves the stated decomposition.

At `sigma=1/2`, use `Q_N=N`, `P_N=log N+h0+o(1)` directly in (1)–(2), where `h0=lim_(N->infinity)(P_N-log N)` is the harmonic-sum constant. Here `conj(s)=1-s`. The block expression becomes

`c_p sum_(k<pN)U_floor(k/p)(k+1)^(-conj(s))`

`= -c_p|Z|²+pN/(1-s)+p/(2s)+1/(2(1-s))`

`  -(1/2)log N-h0/2-W_p+o(1)`.

Meanwhile `A_(pN)=pN/(1-s)-(1/2)log(pN)-h0/2+conjugate(W_1)+o(1)`. Subtract, use `K=-1/(2s)`, and again subtract the `p=1` identity. This gives exactly `B_(1/2)(p)=-(1/2)log p`; no interchange of limits in `sigma` and `N` is needed.

Finally the finite quadratic endpoint identity is

`2 Re A_N=|U_N|²-|Z|²-P_N`.  (3)

It is `ordinaryMixedPrefix_quadratic_identity` in the same Lean module. For `sigma>1/2`, subtract `N^alpha/|1-s|²` from (2)–(3) and take limits. The constant terms give `Re W_1=-|Z|²/2-Re K`. At `sigma=1/2`, retain the cross term in `|U_N|²`: its constant contribution is `Re(1/(1-s))=-2 Re K`. The same relation follows. This proves the real-part formula.

## What the conjecture loop established

The leading conjecture `T_p/p^alpha -> K` follows from the decomposition. It holds at zeros and nonzeros. The coefficient of the oscillatory growing term `p^(1-s)` is exactly `|Z|²`; its disappearance reads the zero condition without restricting its location.

The conjecture of a bounded remainder after subtracting only `Kp` at critical-line zeros fails: its real part is `-(1/2)log p+O_s(1/p)`. Adding this logarithm repairs convergence but supplies a universal arithmetic subtraction, not a new zero constraint.

For `1/2<sigma<1`,

`T_p=Kp^alpha+|Z|²c_p+C+o(1)`,

`Re C=-(1/2)(|Z|²+zeta(2 sigma))`.

Thus at a hypothetical strict-right zero the bounded remainder tends to a constant whose real part is **strictly negative**, `-zeta(2 sigma)/2`. Boundedness is not vanishing.

For fixed `p>1`, insert this expansion into the already proved limiting cell law `J_(p,q)=T_(pq)-T_p-p^alpha T_q`. It gives

`J_(p,q)=|Z|²(c_p-p^alpha)q^(1-s)+(1-p^alpha)C-T_p+o(1)`.

Since `|c_p|=p^(1-sigma)` differs from `p^alpha`, boundedness of this `q`-family is equivalent to `Z=0` within the strict-right strip. It is a zero detector, not a proof that the strip contains no zeros. At a zero its limit is the retained constant `(1-p^alpha)C-T_p`, not an automatically zero value.

On the critical line the corresponding zero-specialized correction instead has leading term `(p-1)log q/2`. This is why a bounded-correction conjecture spanning both chambers was wrongly formulated.

The positive survivor is the complete decomposition, including its nonzero boundary terms. The original arithmetic annihilation problem remains open. No route is retired, no result about all possible arithmetic identities is asserted, and no new RH premise has been introduced into Lean.

## Formal proof and scope

The frozen fixed-modulus statement is closed, including `sigma=1/2`. The final theorem is `RHTower.DeletionMixedRefinement.infiniteMixed_eq_decomposition` in `EulerDeletionInfiniteDecomposition.lean`. `infiniteMixed` is the limit of the actual ordered prefixes; `tendsto_mixedPrefix` proves convergence at every ordinary cutoff. `infiniteMixed_eq_strict` and `infiniteMixed_eq_critical` expose the two boundary formulas, and `infiniteMixed_one` checks unit deletion exactly.

The proof uses the source decomposition unchanged. `EulerDeletionPowerSumRemainder.lean` proves

`|R_s(N)| <= |s(s+1)|/(sigma+1) N^(-sigma-1)`

from the actual Bernoulli tail, then weighted remainder decay, conjugation, and `summable_norm_remainder`. It does not assume the sharper `1/12` expansion. `infiniteRemainder_eq_conjugate_exponent` identifies the formal series with the paper's literal `R_conj(s)(pn)` series.

`EulerDeletionMixedDecompositionFinite.lean` subtracts the unit-deletion identity before taking limits. With `a=2 sigma`, `Q_N=S_N(a-1)`, and `P_N=S_N(a)`, it retains

`D_p(N)=p^(2-a)Q_N-Q_(pN)-(1/2)(p^(2-a)-p^(1-a))N^(1-a)`.

The exact identity is

`T_p(pN)=(c_p-1)|Z|²+D_p(N)/(1-conj(s))`

`          +(1/2)[p^(1-a)P_N-P_(pN)]+W_p(N)-W_1(pN)+E_p(N)`.

Here `E_p(N)=F_p(pN)conjugate(S_(pN)-Z)+(p^(2-a)-p^(1-a))N^(1-a)/(2(1-conj(s)))`. Its leading half-endpoint contribution cancels exactly; `endpointError_decomposition` expresses the result using decaying remainder products. The final module proves `E_p(N)->0`, `D_p(N)->(p^(2-a)-1)zeta(a-1)`, and the boundary-difference limit. At `a=1` this is the ordinary harmonic dilation limit, giving `-(1/2)log p`. Finite residue classes then remove the restriction to cutoffs `pN`.

Formalized scope: the displayed complex infinite decomposition, both boundary branches, absolute convergence of `W_p`, the actual power-sum remainder bound, and all endpoint limits needed by that equality. The sharper asymptotic `W_p=-conj(s)zeta(2 sigma+1)/(12p^(2 sigma))+O_s(p^(-2 sigma-2))`, the formula for `Re W_1`, the real-part/growing-modulus consequences, and the bounded-correction characterization remain paper results in this card. No RH implication or arithmetic annihilation law has been formalized.

[Formalized theorem card](../../../3-formalized/euler-deletion-infinite-decomposition.md) records the certificate. [Runpod report and data](../../../2-fully-proven/computations/euler-deletion-growing-modulus/REPORT.md) retain the earlier exploratory computations separately; no numerical result enters the Lean proof, and no new experiment was needed for this formalization.

Euler–Maclaurin remainders and multiple-zeta product identities are established subjects. The [Hurwitz computation paper](https://arxiv.org/abs/1309.2877) and [multiple-zeta expansion paper](https://arxiv.org/abs/1601.05918) document those neighboring methods. This limited audit neither establishes that the exact notation above appears in literature nor supports a claim of radical novelty.
