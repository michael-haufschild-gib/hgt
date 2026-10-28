# Finite prime flips have an exact positive harmonic density

- **ID:** ACP-FINITE-PRIME-DENSITY
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean formalization follows)
- **Parent:** arithmetic-counting-finite-flip-exhaustion.md
- **Statement:** For every finite set of primes `F`, the signed harmonic count has mean `c_F=prod_{p in F}(p-1)/(p+1)>0` with uniformly bounded error, and pays hyperplane gap `(2 log 2)c_F^2`.

## Exact statement

Let `S_F(N)=sum_{1<=n<=N}omega_F(n)/n` and `H_N=sum_{1<=n<=N}1/n`.
There is a constant `K_F>=0`, independent of `N`, such that

`|S_F(N)-c_F H_N|<=K_F`.

Consequently `S_F(N)/H_N -> c_F`, and the literal prime form twisted by
`omega_F` has hyperplane gap `(2 log 2)c_F^2>0`.
No finite-horizon lower floor `S_F(N)>=c_F H_N` is asserted for general `F`.

## Dependency-closed paper proof

The product satisfies `0<c_F<=1`. For a prime `p` outside `F`, put
`G=F union {p}`. Away from multiples of `p` the two gauges agree.
Multiplication by `p` preserves `omega_F` and reverses `omega_G`. Exact
reindexing of the multiples, including their harmonic weights, gives

`p S_G(N)+S_G(floor(N/p))=p S_F(N)-S_F(floor(N/p))`.

Set `c=c_F`, `c'=c(p-1)/(p+1)=c_G`, `E_F(N)=S_F(N)-c H_N`, and
`E_G(N)=S_G(N)-c' H_N`. Subtracting the means gives exactly

`p E_G(N)=p E_F(N)-E_F(floor(N/p))
 +[2cp/(p+1)](H_N-H_floor(N/p))-E_G(floor(N/p))`.

The corpus harmonic-shell bound is
`0<=H_N-H_floor(N/p)<=L`, where `L=1+log p`. The bracketed coefficient
lies in `[0,2]`. If `|E_F(M)|<=K` for every `M`, define `C=3K+2L`.
Strong induction on `N` proves `|E_G(N)|<=C`: the zero case is exact;
for positive `N`, `floor(N/p)<N` and the displayed identity gives

`p|E_G(N)| <= (p+1)K+2L+C <= pC`.

The last difference is `2(p-2)(K+L)>=0`. This establishes the induction
step with an explicit admissible constant. Finite-set induction starts at
`F=empty`, where `S_F=H`, `c_F=1`, and `K_F=0`.

Since `H_N>=log N -> infinity`, division by `H_N` proves the exact mean.
The already formalized uniform pole-angle transfer gives, for every
`eta>0`, eventually in `N`,

`P_N(omega_F x)<=(log N-gamma-(2 log 2)(S_F(N)/H_N)^2+eta)|x|^2`

on the harmonic hyperplane. Convergence of the squared mean, with half the
desired error allocated to this transfer and half to convergence, proves
the claimed gap. Its positivity follows from `c_F>0` and `log 2>0`.

## Inputs and scope

Exact divisibility reindexing, the harmonic-shell bound and the uniform
pole-angle inequality are checked corpus inputs. The new count is on all
integers, unlike the existing finite-flip Mertens law weighted by `Lambda`.
It supplies arbitrary finite prime sets, including sets containing prime two;
it makes no claim to the optimal gap or complete Weil positivity.

## Gates

- [x] Corpus searches distinguish this law from singleton parity and Mertens matching.
- [x] Exact recurrence and closed bounded-error induction.
- [x] Six public theorems pass the Lean and transitive axiom audit, with only the three standard axioms.
- [ ] Final canonical source check, umbrella, README.

Installed as `ArithmeticCountingPositivity/FinitePrimeFlipsHavePositiveHarmonicDensity.lean`
and wired into the own umbrella. Final installed-source check is running.
Its first olean will be needed by the already written exhaustion leaf.
