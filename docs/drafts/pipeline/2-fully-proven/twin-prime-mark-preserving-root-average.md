# Root averages with marks coprime to the modulus

- **ID:** twin-prime-mark-preserving-root-average
- **Stage:** 2-fully-proven (paper deduction from cited analytic theorems; Lean pending)
- **Type:** THEOREM / BRIDGE
- **Source:** [centered root distribution](../1-in-progress/twin-prime-centered-root-distribution.md)
- **Statement:** For each logarithmic precision, a fixed marked
  shifted-Möbius weight has that precision on average over root moduli
  up to `X^(51/100)` coprime to all marking primes.

## Exact paper statement

For an integer `K≥1`, put `a_i=1/10+i/(10(K+1))`, `1≤i≤K`, and
`L=log X`. Let `P_i` be the primes in
`(exp(L^a_i), exp(2L^a_i)]`, let `V_i=Σ_{p∈P_i}1/p`, and let
`ω_i(n)=#{p∈P_i:p|n}`. For sufficiently large `X` these sets are
nonempty and disjoint. Define

`W_X(n)=∏_{i=1}^K [2^(1-ω_i(n)) ω_i(n)/V_i]`,

`P_X=∏_{p∈P_1∪...∪P_K}p`,

`B_W(t)=Σ_{X<p≤t, p prime} log p · μ(p+2)W_X(p+2)`.

For every `A>0`, there are `K≥1`, `C>0` and `X_0`
such that, for all real `X≥X_0`,

`Σ_{q≤X^(51/100), q odd squarefree, gcd(q,P_X)=1}
 sup_{X≤t≤2X} |Σ_{X<p≤t, p prime, p≡-2 mod q} log p μ(p+2)W_X(p+2)
                 - B_W(t)/φ(q)| ≤ C X/(log X)^A`.

`K` is fixed before `X` tends to infinity, but may depend on `A`.
This distinction is essential. The weight and allowed moduli depend
on `K` and `X` exactly as specified.

**Verdict: BRIDGE.** This tests whether a positive cofactor energy can
retain the modulus average. It is not the original unmarked estimate,
and does not imply twin-prime infinitude by itself. For large `X`,
`W_X(n)=0` on primes `n∈(X,2X+2]`. Neither removal of the marks nor
removal of the coprimality condition is included in this statement.

**Status.** The deduction below is complete on paper using the exact
analytic propositions cited below. Their relevant proofs and parameter
interfaces were read and checked; no gap was identified in that audit.
This is not a Lean certificate for those propositions or this deduction.
The unconditional Lean formalization remains an explicit obligation.

## Parent input and preliminary novelty attack

[Lü–Wang–Wu (2026), §§4.1 and 5.3](https://arxiv.org/html/2610.20242v1)
use these weights with general fixed `ρ∈(0,1)`; here `ρ=1/2`.
Their determinant-square argument estimates a positive cofactor energy
`Q_Y≪XY L^(-D)`, after choosing sufficiently many fixed prime groups
for the requested `D`. Their proposition permits fixed positive lower
power bounds on both Type II lengths. The relevant proof in §§4–5
and Appendix A has now been inspected, including its classical
character–Mellin input. These statements are not Lean inputs.

The transfer keeps the extra root condition in the common
cofactor rather than turning it into a polynomial-conductor character.
The corpus query `Mobius shifted primes marked weight distribution
moduli coprime selected primes` returned no lexical hit and timed out
in semantic retrieval; this is not an absence certificate. Current
primary-source searches did not locate this exact root-average
statement. Priority and scientific novelty are unestablished. The
finite energy inequality below is ordinary Cauchy–Schwarz, not new
mathematics.

## Why coprimality changes the transfer

In the marked expansion write `mn+2=ah`, where `a` contains one
selected prime from each group. If `gcd(q,P_X)=1`, then

`q|(mn+2) ⇔ q|h`.

Thus, for these moduli, the root restriction is a projection on the
common cofactor in the positive square. No assertion is made that it
is a separate projection on the two determinant vertices. If `q`
shares selected primes, the correct label is `lcm(a,q)` instead;
the single-cofactor projection argument no longer applies unchanged.

## Exact finite energy inequality and rate accounting

For any complex numbers `A_h,c_h`, `1≤h≤H`, with `|c_h|≤1`, set
`S_q(u)=Σ_{h≤u,q|h}c_h A_h`. Cauchy–Schwarz within each modulus and
then across moduli gives, for any collection of positive moduli,

`(Σ_q sup_{0≤u≤H}|S_q(u)|)²
 ≤ H(1+log H) Σ_{h≤H}τ(h)|A_h|²`.

Indeed, the first factor after the second Cauchy–Schwarz is at most
`Σ_{q≤H}floor(H/q)≤H(1+log H)`. Exchanging the finite sums in the
other factor counts eligible divisors of `h`, at most `τ(h)`.
Individual endpoints do not alter this upper bound.

Put `E_j=Σ_{h≤H}τ(h)^j|A_h|²`. A further Cauchy–Schwarz gives
`E_1≤sqrt(E_0 E_2)`. In the intended Type II block `H≪X/Y`.
If the actual coefficients have

`E_0≪XY L^(-D)` and `E_2≪XY L^C`,

the modulus sum is `≪X L^((C+2-D)/4)`. Consequently precision
`L^(-A)` requires `D≥4A+C+2`. There is no factor `Q^(1/2)` in this
bound. Crucially, `C` must be independent of the subsequently chosen
number `K` of marking groups; otherwise selecting `D` then `K` may
be circular.

This inequality calculates the transfer cost. The absolute weighted
energy is proved below; the small signed energy is the cited analytic
input, with its source audit and application recorded below.

## Absolute weighted energy: paper subclaim

In a Type II block let `MN≍X`, let `a` range over the selected odd
labels in `[Y,4Y]`, and put

`A_h=Σ_{a,m,n:mn+2=ah} η(a/Y)(∏V_i^(-1)) α_m β_n`,

where `|α_m|≤1`, `|β_n|≤L`, and `η` is bounded. Supports are the
prescribed dyadic intervals. Take `H=ceil(CX/Y)` large enough to
contain all possible cofactors. Fixed `K` gives `Y=X^o(1)`, and
`∏V_i^(-1)` is bounded by a constant depending on `K`.

**[PROVED HERE, elementary subclaim]** For sufficiently large `X`,

`Σ_{h≤H}τ(h)^2|A_h|²≪_K XY L^17`.

The exponent `17` is independent of `K`. The same bound holds after
taking `sup_t|A_h(t)|` inside, where `A_h(t)` restricts `mn≤t`.

Proof. Absolute values followed by Cauchy–Schwarz in `a` give

`sup_t |A_h(t)|² ≤ C_K L² Y Σ_{a∈[Y,4Y], a odd} τ(ah-2)²`.

Only positive arguments occur on the original support; extending the
majorant to other positive arguments does not decrease it. For each
odd `a∈[Y,4Y]`, Cauchy–Schwarz in `h` bounds the needed inner sum by

`Σ_{h≤H}τ(h)²τ(ah-2)²
 ≤ sqrt((Σ_{h≤H}τ(h)^4)(Σ_{h≤H,ah>2}τ(ah-2)^4))`.

Both factors inside the square root are `O(H L^15)`. For completeness,
`τ(n)^4≤τ_16(n)`: at a prime power this is
`(e+1)^4≤binom(e+15,15)`. Induction follows from
`(e+16)(e+1)^3-(e+2)^4=e(11e²+27e+17)≥0`; multiply over primes.
The usual ordered-factorization count gives
`Σ_{n≤T}τ_k(n)≤T(1+log T)^(k-1)` and
`Σ_{n≤T}τ_k(n)/n≤(1+log T)^k`.

For the affine argument, delete a largest factor from an ordered
16-factorization of `ah-2`. The product `d` of the other factors is
at most `D=(4aH)^(15/16)`, and there are at most `16τ_15(d)` ways
to choose them and the deleted position. If `d|(ah-2)`, then
`gcd(d,a)|2`; since `a` is odd this gcd is `1`. Consequently `h`
occupies at most one residue class modulo `d`, giving

`Σ_{h≤H,ah>2}τ(ah-2)^4
 ≤16Σ_{d≤D}τ_15(d)(H/d+1)
 ≪H L^15 + X^(15/16)L^14 ≪H L^15`.

The last step uses `aH≪X` and `Y=X^o(1)`. Summing the resulting
`O(H L^15)` bound over `O(Y)` labels proves
`E_2≪_K H Y²L^17≪_K XYL^17`. No joint shifted-divisor asymptotic
or new analytic hypothesis is needed for this subclaim.

## Physical endpoints: a maximal-energy reduction

Here is a precise route from a source energy bound uniform in
polynomial Mellin frequencies to physical endpoints. This is a
reduction to that bound, not an independent proof of it.

On the product range `MN≤mn≤4MN`, put
`z=log(mn/(MN))/(4log 2)∈[0,1/2]`. For an integer endpoint `t`,
use the periodic indicator of the interval from `-1/4` to
`log((t+1/2)/(MN))/(4log 2)`, with trivial constant indicators when
the endpoint lies beyond the product range. Its Fejér polynomial of
degree `T=ceil(X^4)` has coefficients bounded uniformly in `t` by
`C/(1+|k|)`. The distance of each product integer from the moving
jump is at least `c/X`; the fixed jump stays away from the product
range. The Fejér-kernel tail bound gives pointwise error `O(X/T)`.

Each retained term is a product of Mellin phases in `m` and `n`, with
frequency `O(T)`, and the coefficient majorant has total mass `O(L)`.
Cauchy–Schwarz in this majorant therefore yields

`Σ_h sup_t|A_h(t)|²
 ≪L² sup_{|v|≤X^5} Σ_h|A_h^(v)|² + negligible error`.

For the error one may use the crude bounds `τ(mn)≤4MN` and
`O(Y)` labels: its contribution to each `A_h` is
`O_K(YX²L/T)`, whose squared sum is negligible at `T=X^4`.
This also covers arbitrary real endpoints by replacing them with
integer floors. The source's §5.2 permits these polynomial Mellin
twists in exactly the actual Möbius coefficient. Its proof uses the
fixed-power frequency range of the character–Mellin estimate, while
the other coefficient only needs its absolute bound. Both interfaces
were checked in the source audit below.

Combining this reduction with `E_2≪XYL^17`, a source energy precision
`D≥4A+21` gives the required `L^(-A)` modulus saving for this
Type II block. All exponent losses here are independent of `K`.

## Analytic input audit

The input is precisely [Lü–Wang–Wu, Propositions 4.2 and 5.3](https://arxiv.org/html/2610.20242v1).
For fixed lower length exponent and coefficient bound, requesting
`E_0≪XYL^(-D)` fixes the major-arc parameter first and then `K`.
No later step enlarges `K`. The exponent choices are independent
of the fixed marking exponents.

The proof audit covered §§4.2–4.7, §5 and Appendix A. Checks included:
parity conjugacy and its measure; common-prime restrictions;
uniform root counting; the two sources of operator cancellation;
distinctness corrections in growing moments; localized conversion
from moments to pairings; and the final normalization. In §5 the
sparse-frequency estimate controls the second factor. The permitted
twists cover the Fejér frequencies above.

The precise classical character–Mellin input was checked in
[Matomäki–Shao–Tao–Teräväinen, Lemma 3.9(ii), p. 50](https://arxiv.org/pdf/2204.03754).
It allows arbitrary subintervals and polynomial frequency ranges
after a fixed rescaling of its main parameter. Partial summation
differentiates only the real amplitude. This validates the
frequency interface needed here.

This is a source-level mathematical audit, not formal verification.
No source theorem is represented by an analytic hypothesis in Lean.

## Classical Möbius progression input and coprimality

[Murty–Vatwani (2018), Proposition 3, p. 115](https://mrammurty-ai.github.io/chowla.pdf)
states the maximal-endpoint Möbius Bombieri–Vinogradov estimate:
for every `B>0` there is `b>0` such that

`Σ_{m≤H^(1/2)/(log H)^b} max_c max_{u≤H}
 |Σ_{n≤u,n≡c mod m} μ(n)| ≪_B H/(log H)^B`.

The displayed source even allows all residue classes; only reduced
classes are used here. Its cited original is Siebert–Wolke (1971),
Corollary 1, *Math. Z.* 122, 327–341, DOI
`10.1007/BF01110168`. The exact statement was checked in the
author-hosted 2018 paper. The original 1971 proof has not been
independently reproduced here. This is a classical paper-proof input,
not an available Lean theorem or an assumption added to Lean.

One auxiliary reduction is available without assuming distribution
of shifted primes. For a positive integer `R`, let `s_R(d)` indicate
that every prime factor of `d` divides `R`. The exact convolution is

`μ(n)1_{gcd(n,R)=1} = (μ*s_R)(n)`.

If `R≤H^C` for fixed `C`, then for every fixed `σ>0`,

`Σ_d s_R(d)/d^σ=∏_{p|R}(1-p^(-σ))^(-1)=H^o(1)`,

uniformly in `R`, when `0<σ<1`; larger `σ` are easier. To see this,
split the primes at `log H`. The logarithm of the product is
`O_σ((log H)^(1-σ))`, using `Σ_{p|R}log p≤C log H` for the larger
primes. Thus `#{d≤H:s_R(d)=1}≤H^ε` for any fixed `ε>0` and
sufficiently large `H`. Also, for fixed `η>0`,

`Σ_{d>H^η}s_R(d)/d≤H^(-η/2+o(1))`.

For moduli coprime to `R`, expand the convolution and split at
`d=H^η`. At short `d`, an ordinary Möbius Bombieri–Vinogradov
estimate applies to the remaining variable, with a smaller fixed
level margin. At long `d`, summing the trivial progression bound
`H/(dm)+1` costs at most

`H(1+log M)H^(-η/2+o(1)) + M H^ε`.

This is smaller than `H` by a fixed power for
`M≤H^(1/2-δ)` and sufficiently small fixed `ε`. The short-divisor
reciprocal sum is `O_C(log H)`, so it costs only one logarithm.
For this last assertion, the Euler product over primes at most
`log H` is at most the telescoping product over all integers from
`2` to `floor(log H)`, hence at most `log H`; the remaining primes
contribute a bounded factor by the same prime-factor budget. Choose
`0<η<2δ` to preserve a fixed level margin at the short divisors.
Applying the cited theorem at each short divisor therefore proves,
for fixed `C,δ,B>0`, uniformly for `R≤H^C`,

`Σ_{m≤H^(1/2-δ), gcd(m,R)=1} max_{gcd(c,m)=1} max_{u≤H}
 |Σ_{n≤u,n≡c mod m,gcd(n,R)=1} μ(n)| ≪_{B,C,δ} H/(log H)^B`.

Indeed `m≤H^(1/2-δ)` is below
`(H/d)^(1/2)/(log(H/d))^b` for `d≤H^η` and `η<2δ`, once `H`
is large. Since `gcd(m,R)=1`, every retained `d` is invertible
modulo `m`, so all transformed residues remain reduced. The
maximum over the original endpoint is bounded by the source
maximum at length `H/d`. Request one extra logarithmic saving
to absorb `Σ s_R(d)/d≪_C log H`. The long-divisor estimate above
is uniform in both maxima and has a fixed power saving. This
proves the claimed extension from the precise classical input.

## Averaged Type I estimate: paper proof

**[PROVED HERE, using the classical input above]** Fix `K` and
`A>0`, put `Z=exp(L^(24/100))`, and let `R_Z(n)` indicate that
`n` has no prime factor at most `Z`. For coefficients
`|α_d|≤L`, define

`T_q(t)=Σ_{d≤X^(1/5),R_Z(d)=1} α_d
 Σ_{X<dk≤t,k odd} R_Z(k) μ(dk+2)W_X(dk+2)1_{q|dk+2}`.

Then

`Σ_{q≤X^(51/100),q odd squarefree,gcd(q,P_X)=1}
 sup_{X≤t≤2X}|T_q(t)| ≪_{A,K} X L^(-A)`.

All bounds below are uniform in `t` and the allowed coefficients.
This is a Type I estimate, not the corresponding prime sum.

**Finite expansions.** Take `J=ceil(C_A log L)`. Inclusion–exclusion
on odd `k` gives

`R_Z(k)=Σ_{r|k,r squarefree,p|r⇒2<p≤Z,ω(r)≤J} μ(r)
       + O(binom(ω_{≤Z}(k),J+1))`.

Here `ω_{≤Z}` counts prime factors in `(2,Z]`. All retained and
error divisors satisfy `r≤Z^(J+1)=X^o(1)`. Since `R_Z(d)=1`,
`ω_{≤Z}(k)=ω_{≤Z}(dk)` in every original term.

For a marking factor use the finite Taylor identity with remainder

`|uρ^(u-1)-Σ_{j=1}^J j(ρ-1)^(j-1)binom(u,j)|
 ≤(J+1)binom(u,J+1)`, `ρ=1/2`.

Expand the product one factor at a time. Bounded unexpanded factors
and absolute values of the preceding expanded factors give

`W_X(N)=Σ_{a|N}c_a + O(Σ_{a|N}e_a)`, `e_a≥0`.

All `a` are odd squarefree, supported on the marking primes, and
`a≤exp(O_K(JL^(1/5)))=X^o(1)`. Furthermore,

`Σ_a |c_a|/a≪_K1`,

`Σ_a e_a τ(a)/a≪_K C_0^J/J!`

for an absolute fixed `C_0`. For the second bound, squarefreeness
gives `τ(a)=2^ω(a)`. In each group the reciprocal sum over
`j` distinct primes is at most `V_i^j/j!`; inserting `τ(a)`
replaces `V_i` by `2V_i`. The one remainder factor contributes
`(2V_i)^(J+1)/J!`, while the other factors have bounded exponential
sums. Here `V_i` is bounded above and away from zero. Constants
may depend on fixed `K`, but the logarithmic losses below do not.

**Truncation errors after the modulus sum.** Write `N=dk+2`.
Summing allowed root moduli costs at most `τ(N)`, and summing
`d|N-2` costs at most `Lτ(N-2)`. Thus the sieve truncation error is
at most

`C_K L Σ_{N≤2X+2,N odd} τ(N)τ(N-2)
                         binom(ω_{≤Z}(N-2),J+1)`.

Expand the binomial coefficient into its squarefree divisors `r`
and write `N=rh+2`. Since `τ(rh)≤2^(J+1)τ(h)`, the inner sum is
bounded by `2^(J+1) Σ_h τ(h)τ(rh+2)`. Cauchy–Schwarz and
`τ²≤τ_4`, with the largest-factor argument already used above,
give, uniformly for these odd `r=X^o(1)`,

`Σ_{h≤2X/r} τ(h)τ(rh+2)≪(X/r)L³`.

Consequently the sieve error is

`≪_K XL⁴ (2Σ_{2<p≤Z}1/p)^(J+1)/(J+1)!`.

Since `Σ_{p≤Z}1/p≤log L` for large `X`, choose `C_A` so that
this is `O(XL^(-A))`.

After that replacement, the absolute truncated sieve is at most
`τ(k)≤τ(N-2)`. The marking truncation error is therefore at most

`L Σ_{N≤2X+2,N odd} τ(N)τ(N-2)² Σ_{a|N}e_a`.

For each `a`, use `N=ah` and `τ(ah)≤τ(a)τ(h)`. The inner sum
is bounded by

`Σ_{h≤(2X+2)/a,ah>2} τ(h)τ(ah-2)²
 ≤ sqrt((Σ_h τ(h)²)(Σ_h τ(ah-2)^4)) ≪(X/a)L⁹`.

The exponents are respectively `3` and `15`, from the same
ordered-factorization proof. Its error term is absorbed uniformly
for `a≤X^(1/100)`, which holds eventually. Hence the marking
error is `O_K(XL^10 C_0^J/J!)`, with every fixed logarithmic saving.
Neither truncation error was multiplied by the number of moduli.

**Main sums.** Enlarge `X` so that both divisor supports are at
most `X^(1/100)`. Fix a retained `a` and an allowed `q`. They
are coprime and squarefree. Put `N=aqh`. Then

`μ(N)=μ(a)μ(q)μ(h)1_{gcd(h,aq)=1}`.

The condition `r|k` becomes `dr|aqh-2`. Because all involved
integers are odd, a nonempty sum requires `gcd(dr,aq)=1`, and
the resulting residue `h≡2(aq)^(-1) mod dr` is reduced. Oddness
of `k` is equivalent to oddness of `h`. Thus the Möbius sum has
the extra restriction `gcd(h,R_0)=1`, with `R_0=2aq`, and
modulus `m=dr` coprime to `R_0`.

For fixed `m`, its factorization as `dr` is unique: `r` is the
entire small-prime part of `m`, while `d` has no prime factor
at most `Z`. Therefore regrouping by `m` gives coefficients of
absolute value at most `L`, without a divisor multiplicity.
The ranges satisfy

`m≤X^(21/100)`,

`H=ceil((2X+2)/(aq))≳X^(48/100)`, `R_0≤H²`,

`m≤H^(1/2-1/20)`

for sufficiently large `X`; the last inequality uses
`21/100 < (48/100)(1/2-1/20)`. Apply the proved coprimality
extension with `C=2`, `δ=1/20`, and precision `B`. The difference
of the two endpoints costs at most twice the maximal-prefix
bound. The total for fixed `a,q` is `O(LH/(log H)^B)`.

Summing the main terms over `a,q` now gives

`≪ XL^(1-B) (Σ_a|c_a|/a)(Σ_{q≤X^(51/100)}1/q)
 ≪_K XL^(2-B)`.

Choosing `B` sufficiently large and including the truncation
errors proves the Type I claim. Taking Vaughan cutoffs
`U=V=X^(1/10)` places its second Type I term in exactly this
range, since `UV=X^(1/5)` and the coefficient is at most `log d`.
For its first term, `log k=log(dk)-log d`; partial summation
and one additional requested logarithmic saving handle `log(dk)`.
The smaller range `d≤U` and coefficient `μ(d)log d` are already
covered. This proves both averaged Type I contributions on paper.

## Remaining elementary errors

For square-divisibility errors after dropping `gcd(a,h)=1`, sum root
moduli first: their multiplicity is at most `τ(h)`, hence at most
`τ(ah)`. The resulting majorant has the form

`C_K L Σ_{p∈∪P_i} Σ_{N≤CX,p²|N} τ(N-2)τ(N)`.

Cauchy–Schwarz and the largest-factor argument with four factors
bound each inner sum by `O((X/p²)L³)` when the marked primes have
subpolynomial size. For the second factor use
`τ(p²h)≤3τ(h)`; for the first use the odd modulus `p²`.
Thus this majorant is
`O_K(XL⁴ Σ_{p∈∪P_i}p^(-2))`, which has every fixed logarithmic
saving. The precise expansion satisfies

`(∏V_i^(-1)) Σ_{a|N, one mark per group} ρ^ω(N/a)
 ≤ W_X(N)≪_K1`.

Indeed `ω(N/a)≥ω(N)-K` and `0<ρ<1`; there are
`∏ω_i(N)` choices. Thus the same majorant applies even to
the added square-divisible terms. This checks the mark weights
against the root-averaged error account.

Proper prime powers, and nonrough prime powers discarded by the
Vaughan decomposition, must also be charged by their root-divisor
multiplicity rather than by the number of moduli. The elementary
bound `τ(n)≪_ε n^ε` makes the proper-prime-power contribution
`O_{K,ε}(X^(1/2+ε)L^C)` before centering. The centered error has
only the additional harmonic-totient sum. These errors are
elementary; they do not supply the missing signed Type II energy.

## Assembly of the exact prime-weight statement

Fix the desired `A`. Apply Vaughan's identity with
`U=V=X^(1/10)` and the multiplicative indicator `R_Z`.
Both Type I terms have the averaged maximal estimate proved above.
In Type II, split `m,n` into dyadic blocks, retaining `m>U,n>V`.
Their lengths satisfy `MN≍X` and `M,N≥X^(9/100)` for large `X`.
Expand the marks as `mn+2=ah` and drop `gcd(a,h)=1`, charging
the root-averaged square-divisibility error proved above.

Since `gcd(q,P_X)=1`, the remaining root restriction is exactly
`q|h`, with coefficient `c_h=μ(h)ρ^ω(h)` independent of `q`.
Split `a` by the fixed smooth dyadic partition. For each block,
the physical endpoint gives

`S_q(t)=Σ_{h≤H,q|h}c_h A_h(t)`, `H≪X/Y`.

The finite energy inequality applies also when the endpoint is
inside `A_h`: bound each summand by `sup_t|A_h(t)|` after
Cauchy–Schwarz. With

`E_j^max=Σ_{h≤H}τ(h)^j sup_t|A_h(t)|²`,

it yields

`(Σ_q sup_t|S_q(t)|)²≤H(1+log H)E_1^max`,

`E_1^max≤sqrt(E_0^max E_2^max)`.

For source precision `D`, the preceding results give

`E_0^max≪_K XYL^(2-D)`, `E_2^max≪_K XYL^17`.

Therefore each Type II block contributes
`O_K(XL^((21-D)/4))`. There are `O(L²)` blocks for `m,n`
and `O_K(L)` for `a`. Choose `D≥4A+41`; each block then has
precision at least `A+5`, and the total Type II contribution
is `O(XL^(-A-2))`. Choose the source major-arc parameter and
`K` only after fixing this `D`. All block-count exponents are
independent of `K`. The chosen marking exponents in the exact
statement satisfy the source hypotheses for this fixed `K`.

Request precision `A+2` in Type I and in the elementary errors.
Replacing `Λ(n)R_Z(n)` by prime weights changes the modulus
sum by at most

`C_K Σ_{X<p^j≤2X,j≥2} (log p)τ(p^j+2)
 ≪_{K,ε}X^(1/2+ε)L²`,

which has every fixed logarithmic saving. The omitted nonrough
prime powers are a subset of this same error. Lower endpoints
are differences of two maximal prefixes and cost a constant.
We have consequently proved the uncentered statement

`Σ_{q≤X^(51/100),q odd squarefree,gcd(q,P_X)=1}
 sup_{X≤t≤2X}|Σ_{X<p≤t,p prime,q|p+2} log p μ(p+2)W_X(p+2)|
 ≪_{A}XL^(-A-2)`.

The summand `q=1` bounds `sup_t|B_W(t)|` by the same quantity.
Finally `Σ_{q≤Q}1/φ(q)≪1+log Q`: expand
`n/φ(n)=Σ_{d|n}μ²(d)/φ(d)` and use the convergent series
`Σ_d μ²(d)/(dφ(d))=∏_p(1+1/(p(p-1)))`.
The triangle inequality now gives the centered statement, with
one logarithm to spare. This completes the paper deduction.

## Formalization obligation

No analytic result on this card is formalized yet. The required
dependency chain includes the maximal Möbius progression theorem,
the determinant-energy theorem, its character–Mellin input, and
the finite transfers above. They must be proved, rather than
assumed through a `Prop` interface, before the exact displayed
statement can be declared as an unconditional Lean theorem.

## Connection back to the main target

The paper result leaves a separate arithmetic problem: moduli that
consume selected marking primes and the signed removal of the marks.
The unmarked Gram calculation retains precisely those cases. The
programme may use this candidate to isolate them, but must not call a
protected marked estimate a proof of the full root distribution.

## Gates

- [x] Exact conjecture, source interface and falsification points recorded.
- [x] Paper deduction of the marked root-average estimate from precisely cited analytic theorems.
- [x] Relevant source proofs and parameter interfaces inspected; no gap identified.
- [ ] Unconditional Lean proof of that exact estimate.
- [ ] Extension giving an unconditional lower bound for twin primes.

## Log

- 2026-10-23 — Derived the positive-energy transfer cost after the full
  root Gram audit. New analytic candidate recorded; no arithmetic
  cancellation bound or twin-prime theorem claimed.
- 2026-10-23 — Closed the elementary weighted-energy subclaim with
  exponent `17`, independent of the number of marks. Derived a
  maximal-endpoint Fourier reduction and the uniform-coprimality
  reduction for a prospective Möbius progression estimate. The
  source energy audit and actual Type I estimate remain open.
- 2026-10-23 — Located and checked the precise classical Möbius
  progression statement. Closed its uniform-coprimality extension
  and both averaged Type I terms on paper, including divisor-weighted
  truncation errors. Checked the square-divisibility error against
  the actual marked expansion. The signed Type II energy audit,
  complete block assembly, and mark removal remain open.
- 2026-10-23 — Completed the source-level audit of the relevant
  determinant and major-arc arguments, checking the classical
  Mellin estimate at its original statement. Assembled the exact
  marked root-average statement with `D≥4A+41`, including maximal
  endpoints, all dyadic blocks, prime powers, and centering.
  Promoted the paper deduction; Lean dependencies and all steps
  removing marks or their modulus coprimality remain outstanding.
