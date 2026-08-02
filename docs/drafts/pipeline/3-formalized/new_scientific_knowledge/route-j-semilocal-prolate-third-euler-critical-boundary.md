# Route J semilocal prolate third-Euler critical boundary

**Status:** `[PAPER+LEAN-PROVED]`
`[CANDIDATE SOURCE-SPECIFIC NEW SCIENTIFIC KNOWLEDGE]`

## Exact statement

Let

```text
c_n=4^(-n)binom(2n,n),
t_n=2sqrt(2)(-1)^n c_n,
r_n=sqrt((n+1/2)(n+1)),
Y_n={}_2F_1(1,n+1/2;n+1;-1).
```

Write positive one-prime semilocal Jacobi radius as

```text
a_n(q)=r_n+u_nq+v_nq^2+w_nq^3+O(q^4)
```

and Route-J four-radius critical residual as

```text
R_k(q)
  =a_(2k)(q)a_(2k+1)(q)-a_(2k+1)(q)^2
   -a_(2k+2)(q)^2+a_(2k+2)(q)a_(2k+3)(q).
```

Let `H_k=[q^3]R_k(q)` and `m_n=2(n+1)`. Then

```text
H_(n+1)/((m_n+1)^2 sqrt(m_n+1))
  -> -160 sqrt(2/pi).                                  (1)
```

Consequently third Euler correction becomes order one when

```text
q^3 n^(5/2) asymp 1,
n asymp q^(-6/5)=p^(6/5) for q=p^(-1).                 (2)
```

This is strictly earlier than order-one/order-two scale `n asymp p^2`. Matching `p^2` behavior
through Euler order two does not extend to order three.

## Published source input

Connes--Consani--Moscovici give determinant-ratio expansion through `O(q^4)`. Put

```text
s_n=1+t_n(n+1-Y_n/2),
s_(n-1)=1-t_n(n+Y_n/2),
p_n=1-(4n+1)^2/2.
```

Their direct relative `q^3` squared-radius coefficient is

```text
B_n+A_n,                                               (3)

B_n=
 t_(n+1)(s_(n-1)-2)s_(n-1)
 -t_n(s_n-2)s_n
 +t_nt_(n+1)(s_(n-1)+s_n-2),

A_n=t_(n+1)p_(n+1)-t_np_n.
```

Their published anomaly coefficient is first difference of absolute coefficient from (3). Both
formulas are source input. Novelty claimed here begins with exact cancellation and Route-J
critical propagation below.

## New `ell=1` dominant amplitude

Central-binomial recurrence gives

```text
t_(n+1)=-q_nt_n,
q_n=(2n+1)/(2n+2).
```

New trace term in (3) factors exactly:

```text
A_n=(-1)^n T_nD_n,                                    (4)
T_n=2sqrt(2)c_n,
D_n=16n^2+20n+5+1/(4n+4).                             (5)
```

Polynomial `D_n` is source of changed exponent and is absent at first two Euler orders. Wallis
gives, with `tau=2sqrt(2/pi)`,

```text
sqrt(n+1)T_n ->tau,
D_n/(n+1)^2 ->16,
(-1)^n A_n/((n+1)sqrt(n+1)) ->16tau.                  (6)
```

## Base determinant-ratio cancellation

Substitution of `s_n,s_(n-1)` into `B_n` gives exact identity

```text
B_n
 =(1+q_n)t_n
  -t_n^3[
      q_n(n+Y_n/2)^2
      +(n+1-Y_n/2)^2
      +q_n(1-Y_n)
    ].                                                 (7)
```

Earlier alternating-tail theorem proves

```text
1/2 <=Y_n<=1/2+1/(4n+4),  Y_n->1/2.
```

Therefore

```text
(-1)^nB_n/sqrt(n+1) ->-2tau^3.                        (8)
```

So `B_n` is only order `sqrt(n)`, one full power below `A_n`. Literal `ell=1` source atom,
not products of first-order data, dominates third order.

## Squared radius and positive square root

Let `S_n=[q^3]a_n(q)^2=r_n^2(B_n+A_n)`. Then

```text
(-1)^nS_n/((n+1)^3sqrt(n+1)) ->16tau.                 (9)
```

Positive-square-root identity is

```text
w_n=(S_n-2u_nv_n)/(2r_n).                             (10)
```

Since `u_n=O(sqrt(n))` and `v_n->4/pi`, mixed term is negligible. Hence

```text
(-1)^nw_n/((n+1)^2sqrt(n+1))
  ->8tau=16sqrt(2/pi).                                 (11)
```

Lean proves controlled subleading term. For exact dominant amplitude

```text
F_n=r_nT_nD_n/2,
```

one has

```text
((-1)^nw_n-F_n)/((n+1)sqrt(n+1)) ->-tau^3.            (12)
```

## Two-step regular variation

Pointwise (11) cannot be differenced. Proof uses exact ratio

```text
F_(n+2)/F_n
 =(r_(n+2)/r_n)(q_nq_(n+1))(D_(n+2)/D_n).             (13)
```

First-order ratio limits are

```text
(n+1)(r_(n+2)/r_n-1) -> 2,
(n+1)(q_nq_(n+1)-1)  ->-1,
(n+1)(D_(n+2)/D_n-1) -> 4.                            (14)
```

Their sum is `5`, proving

```text
(F_n-F_(n+2))/((n+1)sqrt(n+1))
  ->-5C,                                               (15)
C=8tau=16sqrt(2/pi).
```

This closes hostile gap between pointwise regular variation and finite-difference asymptotics.

## Four-radius weld

At even start `m`, write `w_j=(-1)^j(F_j+G_j)` with remainder from (12). Dominant linear
third-radius critical stencil has exact decomposition

```text
L_m(F)
 =r_(m+1)(F_m-F_(m+2))
  +r_(m+2)(F_(m+1)-F_(m+3))
  +(2r_(m+1)-r_m-r_(m+2))F_(m+1)
  +(r_(m+1)-2r_(m+2)+r_(m+3))F_(m+2).                (16)
```

Jacobi-radius increment tends to one, so second-difference coefficients tend zero. First two
terms each contribute `-5C` by (15). Thus

```text
L_m(F)/((m+1)^2sqrt(m+1))->-10C.                      (17)
```

Remainder `G_n` is order `n^(3/2)`. Its six degree-scale products cancel with coefficients
`1,-1,2,-2,1,-1`, so normalized stencil tends zero. Mixed `u_nv_n` terms are order `sqrt(n)` and
also vanish. Consequently

```text
H_(n+1)/((m_n+1)^2sqrt(m_n+1))
 ->-10C=-160sqrt(2/pi),                                (18)
```

proving (1).

## Hostile audit

1. **Published q³ formulas are not novelty.**  
   Source paper already gives determinant ratios through `O(q^4)` and q³ anomaly. Equation (3)
   and its first difference are inputs.

2. **No anomaly summation heuristic.**  
   Proof uses direct published squared-radius coefficient (3), not endpoint summation.

3. **Pointwise asymptotics are not illegally differenced.**  
   Exact ratio (13) and first-order limits (14) prove two-step law (15).

4. **Subleading terms are not informally discarded.**  
   Exact remainder limit (12), vanishing remainder stencil, and vanishing mixed `uv` stencil are
   separate Lean theorems.

5. **Earlier conjecture is falsified.**  
   Orders one and two scale as `n^(1/2)` and `n`; order three scales as `n^(5/2)`, not
   `n^(3/2)`. New `ell=1` polynomial `D_n` is mechanism.

6. **No all-orders or resummation claim.**  
   Result shows first breakdown and new interaction scale. Orders four and above remain open.

7. **No global-source overclaim.**  
   Fixed-prime theorem remains zero in global source-clock quotient. Complete shell
   finite-support rigidity forbids promotion by ordinary differential-field completion.

8. **No self-adjoint extension selected.**  
   Boundary growth does not choose prolate parity boundary angle or prove Sonin-corner resolvent
   convergence.

## Novelty audit

Primary-source comparison checked Connes--Consani--Moscovici, arXiv:2310.18423 and
arXiv:2403.01247. Latter contains q³ determinant, Jacobi, and anomaly coefficients. Searched
sources contain no Route-J four-radius q³ weld, no `n^(5/2)` critical law, no multiplier `-10`,
no constant `-160sqrt(2/pi)`, and no `p^(6/5)` interaction boundary. Verdict:

```text
[NOVELTY PLAUSIBLE -- PRIMARY-SOURCE SEARCH NOT EXHAUSTIVE]
```

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  SemilocalProlateThirdEulerCriticalJet.lean
```

Umbrella:

```text
formal/GaloisForLFunctions/RHTower.lean
```

Capstones:

```text
publishedThirdBaseRelativeCoefficient_eq_simplified
publishedThirdAdditionalRelativeCoefficient_eq_signed
tendsto_publishedThirdBaseRelativeCoefficient_signed_div_sqrt
tendsto_squaredJacobiRadiusThirdCoefficient_signed
tendsto_thirdRadiusRemainderAmplitude
tendsto_jacobiRadiusThirdCoefficient_signed
tendsto_thirdRadiusDominantAmplitude_twoStepDifference
tendsto_alternatingThirdLinearStencil_dominant
tendsto_alternatingThirdLinearStencil_remainder
tendsto_criticalResidualFirstSecondMixedCoefficient
tendsto_criticalResidualThirdCoefficient
thirdCriticalBoundaryConstant_eq_sqrt_div
```

Direct `lake env lean` and exact-target module build pass. `#print axioms` on capstones reports only
`propext`, `Classical.choice`, and `Quot.sound`; no project axioms, `sorry`, `admit`, `opaque`,
`unsafe`, or computation-based proofs.
