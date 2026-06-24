# Hurwitz Quadratic All-N Tail Independence

- **ID:** hurwitz-quadratic-all-n-tail-independence
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** hurwitz-in-a-weld-escape-ht.md; hurwitz-quadratic-n2-density-shadow.md
- **Statement:** For `Re(s)>1` and `s notin Z`, every finite Hurwitz shift ladder `{zeta(s+k,a)}_{0<=k<=N}` satisfies no nonzero `C(a)`-polynomial relation of total degree at most two.

## Goal

Upgrade the proven `N=2` quadratic density shadow to every finite shift ladder. This is still far below full hypertranscendence, but it closes the first uniform nonlinear gate in the Hurwitz weld model: rational coefficients cannot hide the branch-regular tails produced by the shift ladder.

## Gates

- [x] 0 -> 1 in-progress: exact obstruction and reduction named
- [x] 1 -> 2 fully-proven: rational-tail independence lemma and quadratic row descent proved below
- [ ] 2 -> 3 formalized: not formalized
- [ ] 3 -> 4 publication-ready: not extracted

## Theorem

Fix `Re(s)>1`, `s notin Z`, and `N>=0`. Set

`F_k(a)=zeta(s+k,a)`, for `0<=k<=N`.

If

`P(a,F_0(a),...,F_N(a))=0`, with `P in C(a)[Y_0,...,Y_N]` and `deg_Y P<=2`,

then `P=0`.

Via `partial_a^k zeta(s,a)=(-1)^k(s)_k zeta(s+k,a)`, this excludes all algebraic ODEs for `zeta(s,a)` whose order is at most `N` and whose polynomial degree in the jet variables is at most two.

## Lemma 1: Rational-Tail Independence

Let `Re(s)>1`, `s notin Z`. If rational functions `r_0,...,r_M,R in C(t)` satisfy

`sum_{j=0}^M r_j(n) H_n^(s+j) = R(n)`

for all sufficiently large integers `n`, where `H_n^(u)=sum_{m=1}^n m^(-u)`, then every `r_j=0`.

### Proof

Clear denominators, reducing to polynomials `p_j,P in C[t]`:

`sum_j p_j(n) H_n^(s+j)=P(n)`.

Ordinary generating functions give

`sum_{n>=1} H_n^(u) z^n = Li_u(z)/(1-z)`.

For a polynomial `p`, multiplication of coefficients by `p(n)` is the operator `p(theta)`, `theta=z d/dz`. Since the displayed sequence identity holds from some point on, the generating function

`sum_j p_j(theta)(Li_{s+j}(z)/(1-z))`

is rational.

Put `z=e^(-mu)`, so `theta=-d/dmu`, and write `h(mu)=1/(1-e^(-mu))`. For noninteger `alpha`, the fractional polylogarithm has the classical local branch expansion

`Li_alpha(e^(-mu)) = Gamma(1-alpha) mu^(alpha-1) + holomorphic integral-power terms`

near `mu=0`. Therefore the non-meromorphic branch part of the rationality relation is

`B(mu)=sum_j p_j(-D)( Gamma(1-s-j) mu^(s+j-1) h(mu) )`, with `D=d/dmu`.

All non-branch terms have integral Laurent expansions. Since `s notin Z`, a rational function of `z=e^(-mu)` cannot contain a nonzero `mu^s` branch term. Hence `B(mu)=0` as a multivalued meromorphic germ.

It remains to prove injectivity of the map `(p_j)_j -> B`. Let `d` be the maximum degree of the polynomials `p_j`, and write `a_{j,d}` for the coefficient of `X^d` in `p_j`. Continue `B` as a meromorphic function of `mu` on a branch of `C*`. The function `h(mu)` has simple poles at every nonzero `mu_m=2 pi i m`. At such a pole, the highest pole order `d+1` in `B` comes only from applying `D^d` to `h`; its coefficient is

`d! mu_m^(s-1) sum_j a_{j,d} Gamma(1-s-j) mu_m^j`.

Since `B=0`, this coefficient vanishes for every nonzero integer `m`. The factor `mu_m^(s-1)` is nonzero, and the remaining factor is an ordinary polynomial in `mu_m` with infinitely many roots. Thus every `a_{j,d}=0`, because `Gamma(1-s-j)` is finite and nonzero for `s notin Z`.

Descending on `d` gives `p_j=0` for every `j`. Then `P=0`, and the original rational coefficients `r_j` also vanish. This proves the lemma.

## Quadratic Row Descent

Let

`P=Q+L+C`

be the decomposition into quadratic, linear, and constant parts in the `Y` variables. Near `a=-n`, set `x=a+n` and

`F_k(-n+x)=x^(-s-k)+R_{n,k}(x)`.

The monodromy-line lemma from the parent card says that

`P(-n+x, R_n(x)+T H(x))`

vanishes identically as a polynomial in `T`, where `H_k(x)=x^(-s-k)`.

The `T^2` coefficient is `Q(-n+x,H(x))`. If

`A_w(a)=sum_{i+j=w} q_{ij}(a)`,

then

`Q(-n+x,H(x))=x^(-2s) sum_w A_w(-n+x)x^(-w)`.

For each large `n`, this is zero as a rational function of `a`. Taking the largest `w` with `A_w` nonzero and evaluating after multiplication by `(a+n)^w` forces `A_w(-n)=0` for infinitely many `n`; hence `A_w=0`. Descending gives `A_w=0` for all `w`: the quadratic part vanishes on the rational-normal leading direction.

The `T^1` coefficient is

`L(-n+x,H(x))+2Q(-n+x,R_n(x),H(x))`.

Look at the highest remaining column `j=N`. The coefficient of `x^(-s-N)` gives, for all large `n`,

`l_N(-n)+2 sum_i q_{iN}(-n) R_{n,i}(0)=0`.

For the chosen branch,

`R_{n,i}(0)=zeta(s+i)+eta_i H_n^(s+i)`,

with nonzero constants `eta_i`. The rational-tail independence lemma forces every `q_{iN}=0`, and then `l_N=0`. Repeating the same argument for `j=N-1,N-2,...,0` gives `Q=0` and `L=0`. Finally the original relation gives `C=0`.

Thus no nonzero relation of total degree at most two exists.

## Retired Shortcut

The first attempted proof of the tail lemma used high finite differences to remove the harmonic sums, leaving shifted powers `(n+q)^(-s-j)`. That shortcut is invalid by itself because, for fixed `q`,

`(n+q)^(-s-j) = (n+q)^(k-j)(n+q)^(-s-k)`.

The pole-tower proof above is the replacement: it proves the needed full-rank statement after translating the problem to fractional polylogarithms.

## Source Check

A first source pass found adjacent known theory, but not this exact polynomial-operator gate.

- Costin--Garoufalidis, *Resurgence of the fractional polylogarithms*, treats noninteger `Li_alpha(z)`, including analytic continuation and monodromy around `0` and `1`.
  Source: https://people.mpim-bonn.mpg.de/stavros/publications/resurgencepolylogarithms.pdf
- Deneufchatel--Duchamp--Minh--Solomon, *Independence of hyperlogarithms over function fields via algebraic combinatorics*, records broad independence results for hyperlogarithms over coefficient rings such as `C[z,1/z,1/(1-z)]`.
  Source: https://oro.open.ac.uk/33699/1/HL_v19.pdf

This theorem may still be a small consequence of standard fractional-polylog monodromy. Its role here is the weld-model gate: it gives a uniform quadratic obstruction for every finite Hurwitz shift ladder.

## Anti-Theatre Check

This card does not mention zero localization, Stieltjes positivity, or an RH-equivalent target. It proves a native obstruction in the Hurwitz weld model: rational coefficients cannot hide the branch-regular tails produced by the shift ladder, at quadratic degree.

The result remains narrow. Higher-degree algebraic relations and full hypertranscendence are still open in the parent card.

## Log

- 2026-06-24 -- created after the proven `N=2` quadratic shadow exposed the exact all-ladder gate.
- 2026-06-24 -- finite-difference shortcut retired; polylog branch/pole-tower proof closes the rational-tail lemma and the all-`N` quadratic row descent.
