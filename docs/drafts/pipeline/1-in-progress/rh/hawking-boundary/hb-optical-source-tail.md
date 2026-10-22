# HB: optical-coordinate evaluation of the common-source pairing

Status: analytical reduction of the mixed source pairing. The actual radial primitive, its definite integral, logarithmic source factorization, and principal-cusp annihilation are [formalized in Lean](../../../3-formalized/hb-optical-source-tail.md). Physical boundary transport, complete extinction and RH remain unproved. Frontier map is read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hard target remains `2 Omega(B(p,p)/2,B(m,m)/2)=0`, with independent SS/SV/VV amplitudes. This calculation attacks the SV–SV source pairing exposed by the [complete-current transgression](hb-mixed-complete-current.md). It evaluates its radial integral instead of adding a vanishing-pairing assumption. The finite horizon expression and its contacts remain those in [the circle cancellation card](hb-causal-circle-taylor-cancellation.md).

## Conjecture: source-adapted optical time removes the radial complex powers

Write `t=-s-3`, `delta=2s+3`, `lambda=(s+1)(s+2)`, so `delta²=4lambda+1`. In the original ingoing chart, `h=v-v'>0`, target inverse radius `u`, source inverse radius `w`, both in `(0,1)`. The actual seed factors are

```
chi(v)e^(2sv)(1+u)^(2s) Q,
chi(v')e^(2tv')(1+w)^(2t) Q.
```

All real positive bases use their real logarithms. Define

```
ell=h+log((1+u)/(1+w)),     L=exp(ell),
h=log(L(1+w)/(1+u)).                                      (1)
```

The actual direct/image invariants become

```
Z_+=1+[(L-1)²-(u-Lw)²]/(2L),
Z_-=1+[(L-1)²-(u+Lw)²]/(2L).                             (2)
```

Proof: substitute `exp(h)=L(1+w)/(1+u)` into
`cosh(h)+sinh(h)(u-w)+(±1-cosh(h))uw` and cancel the positive factors. Thus direct support is `|u-Lw|<=L-1`; image support is `u+Lw<=L-1`. On the actual forward cone `ell>=0`: the direct upper characteristic `w<=(u+eta)/(1+eta*u)`, `eta=tanh(h/2)`, gives `exp(h)(1+u)/(1+w)>=1`; the image cone is contained in it. Conversely these inequalities with `L>=1` imply `h>=0` by their upper bound `u-Lw<=L-1`. No additional negative-time sheet is introduced.

Integrating the common earlier time produces the known scalar clock

```
J_chi(h)=integral_0^infinity exp(-6v)chi(v+h)chi(v)dv.
```

The complementary powers then satisfy exactly

```
exp(2sh)(1+u)^(2s)(1+w)^(2t)
 =L^(-3+delta)(1+w)^(-6).                                (3)
```

For the reversed branches replace `delta` by `-delta`. This proves the conjecture. The complex powers in BOTH radial variables have disappeared; their sole branch-dependent exponent is the optical Mellin factor `L^(±delta)`.

The clock transition has bounded optical extent. For `L>=L0:=2 exp(1)`, every original radial point has `h>=1`, hence

```
J_chi(h)=J0:=integral_0^infinity exp(-6v)chi(v)dv.
```

This uses the literal fixed onset, which equals one from time one onward. It does not replace the onset on `1<=L<L0`.

For a finite terminal time `V`, the exact clock is instead

```
J_chi,V(h)=integral_0^(V-h) exp(-6v)chi(v+h)chi(v)dv
         =J_chi(h)-integral_(V-h)^infinity exp(-6v)chi(v+h)chi(v)dv,
```

for `0<=h<=V`, and zero otherwise. This terminal remainder must accompany the formulas below until its paired limit is justified. The reduction does not drop the finite temporal edge.

## Exact angular bulk and its retained boundary

Use the original source operators

```
A0=(5lambda-6)/4,
k_s=s(s-1)/4, B_s=(s+2)(2s+3),
P_s(u)=A0+k_s u²(B_s-Delta/2),
P_t(w)=A0+k_t w²(B_t-Delta/2),
R=-Delta(Delta-2).
```

They are the two evaluations of the already proved common producer. The scalar master Green kernel has the fixed factor `-1/(2uw)` and master measure `u²du w²dw`; the actual master sources each contribute `2 coexact(P F)`. Therefore the ordered source bulk has coefficient `-2uw`, before the clock and source powers. These conjugating and source factors are retained.

On a finite angular region, transferring the coexact pairing and target source operator to the kernel gives the bulk `Q R P_s(u) M_Z P_t(w)Q`. Its boundary is explicit. Put `f=P_s(u)Q`, `g=M_Z P_t(w)Q`, and `b_s=-k_s u²/2`. With the geometric angular normal and measure, the transfer adds

```
integral_boundary [ f partial_n((Delta-2)g)
  +b_s{(partial_n Q)R g-Q partial_n(R g)} ].              (4)
```

This follows from two scalar Green identities; it is not assigned zero. Modular side cancellation and the cusp-top limit are separate. Formula (4), the temporal remainder above, and the source-contact/current boundary from the transgression remain attached to the bulk evaluation. All occurrences of `Delta` below are actual differential operators on the native circle mean; no angular eigenprojection is used.

## Conjecture: the long-delay radial integral has an elementary primitive

For `L>=L0`, set `y=Lw`. The total Jacobian and common weight simplify to

```
L^(-3) uw(1+w)^(-6) dw d ell
 =u y/(L+y)^6 dy dL.                                    (5)
```

The direct/image difference can now be joined by odd extension of the target polynomial `u P_s(u)` from `[0,1]` to `[-1,1]`. This extension is valid here because the clock is constant in the radial variables. On the transition interval it would retain `J_chi(log(L(1+w)/(1+|u|)))`; it cannot be silently removed there.

Set `z=u-y`. The native circle factor depends only on

```
Z(L,z)=(L²+1-z²)/(2L).
```

For `L>=2`, the exact joint domain is

```
1-L <= z <= 1,
max(0,-1-z) <= y <= 1-z.                                (6)
```

Indeed `u in [-1,1]`, `y in [0,L]` and `|z|<=L-1`; their interval intersection gives (6), with no discarded image edge. Write `d=L-z`, `q=L+y`, so the endpoints are

```
q_minus=max(L,d-1),     q_plus=d+1.
```

After changing order, the entire remaining radial integrand is

```
(q-L)(q-d)/q^6
 [A0+A_s(q-d)^2] [A0+A_t(q-L)^2/L^2] M_Z Q,             (7)
A_s=k_s(B_s-Delta/2), A_t=k_t(B_t-Delta/2).
```

The coefficients commute as polynomials in the actual angular Laplacian. Thus only four primitives are required. For positive `q`, let `H=L+d`, `J=Ld`:

```
F11= -1/(3q^3)+(L+d)/(4q^4)-Ld/(5q^5),

F13= -1/q+(L+3d)/(2q^2)-(Ld+d^2)/q^3
       +(3Ld^2+d^3)/(4q^4)-Ld^3/(5q^5),
F31= F13 with L and d exchanged,

F33= q-3H log(q)-(3H^2+3J)/q
       +(H^3+6HJ)/(2q^2)-(H^2 J+J^2)/q^3
       +3HJ^2/(4q^4)-J^3/(5q^5).
```

Direct differentiation gives

```
F_mn'(q)=(q-L)^m(q-d)^n/q^6,
(m,n)=(1,1),(1,3),(3,1),(3,3).
```

Consequently define the explicit endpoint operator

```
D_st(L,z)= [A0² F11+A0 A_s F13
            +A0 A_t F31/L²+A_s A_t F33/L²]_(q_minus)^(q_plus).  (8)
```

Equation (8) evaluates the radial integral (7) completely. This proves the second conjecture: no radial integral or complex radial power remains in the long-delay bulk. The ordered difference is now

```
-2 a_s² a_t² J0 integral_(L0)^infinity integral_(1-L)^1
  integral_Omega Q R [L^delta D_st(L,z)-L^(-delta)D_ts(L,z)]
                   M_(Z(L,z))Q dvol dz dL.               (9)
```

The formula applies first with finite optical bounds and the separate terminal remainder retained. Passing to the displayed infinite optical bound requires paired convergence. The compact optical transition, (4), and physical current/source-contact boundary terms are not included in (9) and remain to be added.

## Next cancellation test: one explicit logarithmic angular channel

The only logarithm in (8) comes from `F33`. Its coefficient is

```
-3(L+d) A_s A_t/L²,
A_s A_t=(lambda-2)(lambda-6)/64
          [Delta²-2(4lambda+1)Delta+4lambda(4lambda+1)].   (10)
```

Proof of the factorization: `k_s k_t=(lambda-2)(lambda-6)/16`, `B_s+B_t=4lambda+1`, and `B_s B_t=lambda(4lambda+1)`. These follow directly from `t=-s-3`. The logarithmic term is unchanged by exchanging the source branches, so its ordered difference is multiplied by `L^delta-L^(-delta)`. The remaining rational terms in (8) remain part of the same cancellation test.

The operator in brackets is a concrete source channel, not an assigned angular eigenvalue. Applied to the literal half-square `Q=f²/2`, the hyperbolic Bochner identity rewrites it as

```
2 |Hess^TF f|_bilinear²-4(lambda+1)|grad f|_bilinear²
  +6lambda² Q.                                         (11)
```

Here squares are complex bilinear contractions. To verify (11), use `Delta f=lambda f`, `Delta Q=2lambda Q+|grad f|²`,
`Delta|grad f|²=2|Hess f|²+2(lambda-1)|grad f|²`, and
`|Hess f|²=|Hess^TF f|²+lambda² Q`. This is an analytical identity for the actual smooth scalar; the corpus has the Bochner calculation for its convergent Poincare realization, while the needed continued-field identification must be discharged before claiming this exact form in Lean.

## Conjecture: the physical logarithmic channel removes the entire principal cusp source

Let `rho=q.1`. The literal principal half-square is the already formalized sum

```
Q_principal=c_plus² y^(2rho)/2+c_plus c_minus y
              +c_minus² y^(2-2rho)/2.
```

Each displayed height power has its actual geometric eigenvalue `p(p-1)`. The two roots of the fourth-order bracket in (10) are

```
2rho(2rho-1),     (2-2rho)(1-2rho).
```

It therefore kills the two extreme powers. The middle power has eigenvalue zero, so the physical weight `R=-Delta(Delta-2)` kills that term as well. With

```
T_lambda=-Delta^4+4(2lambda+1)Delta^3
             -4(lambda+1)(4lambda+1)Delta²+8lambda(4lambda+1)Delta,
```

the result is the exact field identity

```
T_lambda Q_principal=0,
T_lambda Q=T_lambda(Q-Q_principal).                      (12)
```

This proves the third conjecture analytically, using all three original coefficients, including the cross term. The logarithmic bulk channel is thus fixed by the complete Fourier remainder of the square. That remainder includes principal-times-tail and tail-times-tail terms; it is not set to zero. A smooth cutoff is not part of (12): applying the operator to a cutoff principal part also produces its explicit compact transition commutators.

## Direct cancellation test after the radial evaluation

There is a concrete differential test for the remaining density. At interior `Z>1`, direct differentiation of `Z=(L²+1-z²)/(2L)` gives

```
Z_L²-Z_z²=(Z²-1)/L²,   Z_LL-Z_zz=2Z/L².
```

The proved native Darboux equation therefore yields

```
Delta M_Z=L²(partial_L²-partial_z²)M_Z.
```

Under `dL dz`, its transpose on a scalar density is the explicit operator

```
D_star F=partial_L²(L²F)-partial_z²(L²F).                 (13)
```

Every angular polynomial in (9) can consequently be transferred to its now explicit radial/optical density on a finite interior domain, with its integration-by-parts edges retained. These edges include the characteristic `z=1-L`, the source edge `z=1`, the interface `z=-1` where `q_minus` changes formula, and the optical bounds. The characteristic right jets must be used at `Z=1`.

This test has a finite algebraic structure. In coordinates `(L,d=L-z)`,

```
D_star[L^a f(d)]=(a+2)(a+1)L^a f(d)
                     +2(a+2)L^(a+1)f'(d).              (14)
```

On `z<=-1`, both endpoints are `d±1`. Each of `F11`, `F13`, `F31/L²`, and `F33/L²`, evaluated between them, is a sum of just the powers `L^1,L^0,L^(-1),L^(-2)`, with explicit rational/logarithmic functions of `d` as coefficients. Thus the complete transferred density can be tested by a finite sequence of ordinary derivatives of these known coefficients. The logarithmic angular roots `delta(delta-1)` and `delta(delta+1)` are exactly the diagonal factors in (14) at powers `a=delta-2` and `a=delta-1`; no fitted parameter enters this match.

The stronger guess that the transferred bulk vanishes identically does not survive this test. Its useful output is an explicit boundary-directed term. Define

```
H_nr(d)=integral_(-1)^1 u^n(d+u)^(r-6)du,  d>1.
```

Then `partial_d H_nr=(r-6)H_n,r-1`. In particular,

```
F31/L²=L^(-2)H_13-3L^(-1)H_12+3H_11-L H_10,
H_12=-8d/[3(d²-1)^3].
```

Write `mu_s=delta(delta+1)`, `mu_t=delta(delta-1)`. Since `A_t=-k_t(Delta-mu_t)/2`, (14) shows that the coefficient of the lowest surviving power `L^(delta-1)` in the fully transferred ordered bulk `R(D_star)D_st(D_star)[L^delta]` is

```
16 k_t delta A0 mu_s(mu_s-2) d/(d²-1)^3
 =-4 k_t delta A0 mu_s(mu_s-2) partial_d[(d²-1)^(-2)].    (15)
```

Here the notation means: expand (8) as a polynomial in `Delta`, multiply each scalar coefficient by `L^delta`, then replace each `Delta` by `D_star` acting on that product. The `A_s A_t` part loses its two lowest powers because of the two exact diagonal roots; the `A0 A_t F31/L²` part supplies (15). The reversed term is obtained by `delta→-delta`, `s↔t`. Thus pointwise bulk annihilation is not the needed mechanism. Its lowest survivor is a known null-coordinate derivative, exposing a specific primitive to assemble with the interface and characteristic edges.

The active next conjecture is that the complete finite sequence of coefficients combines into an exact boundary reduction whose edge values cancel the compact optical transition and the retained physical boundaries. Equation (15) fixes the first coefficient of that proposed primitive; no boundary value is adjustable. This cancellation has not been proved. Equation (12) separately removes the principal cusp powers from the logarithmic bulk. Global bounds for the differentiated Fourier remainder and angular/temporal transport remain open, as do the independent SS/VV coefficients.
