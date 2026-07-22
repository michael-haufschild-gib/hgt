# Sharp Pólya-frequency order of the de Bruijn--Newman kernel

- **ID:** `debruijn-newman-sharp-polya-frequency-order-four`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / CANDIDATE THEOREM
- **Source:** Michałowski, arXiv:2602.20313v2, Problem 1
- **Statement:** The de Bruijn--Newman kernel `K(u) = Φ(|u|)` is strictly totally positive through order four; combined with the certified order-five counterexample, its exact Pólya-frequency order is four.
- **Scientific status:** `[CONJECTURE] [PF3 PAPER-PROVED] [PF4 SEAM PAPER-PROVED] [OPEN GLOBAL J4] [NOVELTY UNVERIFIED] [NO NUMERICAL EVIDENCE]`

## Goal

Resolve the published global `PF4` problem for the de Bruijn--Newman kernel.  This is outside the
Suzuki and Connes--Consani--Moscovici lanes.  The result would classify the exact finite total-
positivity order of the canonical Riemann--Jacobi kernel; it does not by itself prove RH.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, formal lint PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + novelty audit)

## Normalization

The formal source satisfies

```text
thetaCuspFullSource(2u) = 2 Φ(u).
```

Positive rescaling of the argument and value preserves every finite Pólya-frequency order, so the
problem is equivalent for `f = thetaCuspFullSource`.

## Attack

For a smooth translation kernel `T_f(x,y)=f(x-y)`, define the signed confluent Hankel jets

```text
J_m(t) = (-1)^(m(m-1)/2) det [ f^(i+j)(t) ]_(0<=i,j<m).
```

Karlin's extended-total-positivity theorem reduces strict `TP4` to `J_m(t)>0` for
`m=1,2,3,4` and every real `t`.  Reflection reduces to `t>=0`.

This implication is not an assumed local-to-global principle.  Karlin's definition of `ETP_r`
is exactly positivity of the fully coalesced determinant in both variables; his derivative
extension theorem gives `ETP_r => STP_r`.  Applied to `f(x-y)`, its fully coalesced determinant
is `J_m(x-y)`.  Thus the four scalar jet signs are sufficient for every nonconfluent admissible
configuration, not only for equally spaced Toeplitz minors.

The equal-spacing Toeplitz coefficient has the exact confluent form

```text
lim_(h→0) det[f(t+(i-j)h)] / h^(m(m-1))
  = J_m(t).
```

Here the two Vandermonde factors `Delta(0,...,m-1)` exactly cancel the two Taylor-factorial
products.  In particular the coefficient depends only on derivatives through order `2m-2`.  For
`m=5`, all apparent Taylor terms of orders
`9,...,14` in the uncollected Leibniz expansion cancel.  This corrects the nonminimal derivative
wall stated in Remark 3.3 and Section 5.1 of arXiv:2602.20313v2; the confluence identity itself is
classical and is not claimed as new science.

Existing corpus input:

- `thetaCuspFullSource_pos_all` gives `J_1>0`.
- `thetaCuspLogConcavityNumerator_neg_all` gives `J_2>0`.
- `thetaCuspLogSource_fourthTuran_gt_one_hundred_sixty` and the source derivative hierarchy are
  candidate inputs for `J_3`.
- Sixth logarithmic/source jets are available, but no theorem currently signs the full `J_4`.

The atom family also has the exact ordered-translate form

```text
thetaCuspSourceTerm(x,n)=n^(-1/2)*thetaCuspSourceTerm(x+log n,1),   n>=1.   (0a)
```

This follows immediately from `thetaCuspSourceTerm(x,n)=exp(x/2)*thetaCuspSeed(n*exp x)`.
Consequently the completed source on `x>=0` is a positive, arithmetically weighted mixture of
right translates of one profile.  The current nonperturbative attack is to prove that the
curvature--speed cone below is preserved by this particular likelihood-ordered translate
mixture.  Arbitrary positive mixtures need not preserve finite total positivity, so no generic
mixture-closure assertion is being assumed.

## Universal three-curvature law `[BRIDGE]`

Let `f>0` be `C^6`, put `ell=log f`, and define

```text
q = -ell'',
r = 2q - (log q)'',
s = 2r - q - (log r)''.
```

Whenever the displayed logarithms are defined, the Desnanot--Jacobi/Toda identity gives the exact
factorization

```text
J_1 = f,
J_2 = f^2 q,
J_3 = f^3 q^2 r,
J_4 = f^4 q^3 r^2 s.                                  (1)
```

Indeed the signed Hankel jets obey

```text
J_(m+1) = -(J_m^2/J_(m-1)) (log J_m)'',
```

and `(1)` follows successively for `m=1,2,3`.  Consequently a positive smooth translation kernel
is `ETP_4`, hence `STP_4`, once `q,r,s` are positive everywhere.  The Toda identity and Karlin
extension are classical.  The compact curvature cascade is recorded as a reusable bridge, not as
the publication-level novelty claim.

## Global order-three theorem `[PAPER-PROVED]`

On `x>=0` write the complete source as `f=f_1 exp(epsilon)`, where `f_1` is its first theta atom.
Put

```text
d = 2*pi*exp(2x)-3 > 3,
Q = -(log f_1)'' = 2(d+3)(d^2+6)/d^2,
V = Q'' = -(log f_1)''''
  = (d+3)(8+48/d^2+864/d^3+2592/d^4).
```

The exact atom inequalities are

```text
Q >= 19,                 V < (3/2) Q^2.                (2)
```

For the second inequality, after clearing the positive denominator the gap is

```text
6d^5+10d^4+72d^3+168d^2-648d-1944
 = 1836+5814y+2976y^2+732y^3+100y^4+6y^5,
y=d-3>0.
```

Existing exact tail estimates give, for `x>0`,

```text
epsilon'' < 13/10,       epsilon'''' > -17.             (3)
```

At a fixed point multiply `f` by an exponential gauge so that `ell'=0`; this does not change any
`J_m`.  With `a=ell''`, `b=ell'''`, and `c=ell''''`, direct expansion gives

```text
det[f^(i+j)]_(0<=i,j<3) / f^3 = a*c+2a^3-b^2.          (4)
```

Set `p=Q-epsilon''=-a`.  Equations `(2)`--`(4)` imply

```text
det_3/f^3
 < p(V+17-2p^2)
 < p((3/2)Q^2+17-2(Q-13/10)^2) < 0,
```

because, for `Q>=19`,

```text
2(Q-13/10)^2-(3/2)Q^2-17
 = Q^2/2-(26/5)Q-681/50 > 0.
```

The order-three sign convention is `J_3=-det_3`, hence `J_3(x)>0` for every `x>0`.
The seam value `x=0` is strict by the exact modular calculation below, and evenness covers the
negative half-line.  Thus the de Bruijn--Newman kernel is unconditionally strict `PF3`; no
sampling, interval arithmetic, or zero information enters.

For reference, the first atom itself has the stronger exact cascade

```text
R = 4d(d+3)(d^3+18d-24)/(d^2+6)^2 > 18,
S = 6(d+3)(1+6C/(d^3+18d-24)^2) > 36,
C = d^2(d-4)^2+8d^2+48d+156 > 0.
```

These are its `r` and `s` from `(1)`.

## Conditional sixth-order Schur law `[PAPER-PROVED UNIVERSAL BRIDGE]`

At one point remove the affine exponential gauge, so `ell'=0`, and write

```text
a=ell'', b=ell''', c=ell'''', d=ell''''', e=ell''''''.
```

Put

```text
U=c+2a^2, C=c+3a^2, V=d+9ab,
W=e+15ac+9b^2+15a^3.
```

Two exact Schur eliminations in the confluent order-four Hankel matrix give

```text
J_4/f^4
 =(aU-b^2)(W-C^2/a)-a(V-bC/a)^2.                     (5a)
```

For a log-concave kernel set `q=-a>0` and define the gauge-invariant conditional sixth curvature

```text
T_6 = e-9q*c+9b^2-6q^3+c^2/q = W+C^2/q.              (5b)
```

If `J_3>0`, then `aU-b^2<0`.  Hence the single strict inequality

```text
T_6<0                                                       (5c)
```

forces `J_4>0`: the first term in `(5a)` is positive and the second is nonnegative because
`a<0`.  This is a universal sufficient law for every positive `C^6` translation kernel.  It is
an exact Schur-complement bridge, not yet claimed as literature-new.

There is a sharper geometric form.  With the Toda curvatures `q,r,s` from `(1)` and
`u=q^2*r=J_3/f^3`, direct differentiation gives

```text
T_6=q*r*(((log u)')^2-s).                              (5d)
```

Thus the fourth-order Schur cone is the curvature--speed inequality

```text
s > ((log(q^2*r))')^2.                                 (5e)
```

This is stronger than the necessary and sufficient condition `s>0`, but it is stable under a
useful two-budget proof: a lower curvature floor and an upper logarithmic-speed ceiling.

There is an equivalent Schrödinger form with no quotient derivatives.  Since

```text
u=q^2*r=J_3/f^3,
(log u)''=3q-s,
```

one has the exact universal identity

```text
q*T_6=u''-3q*u.                                        (5f)
```

Therefore

```text
u'' < 3q*u                                              (5g)
```

is sufficient for strict `PF4` once `q>0` and `J_3>0` are known.  This is the current preferred
open core: the normalized order-three confluent density must be a strict subsolution of the
one-dimensional operator `d^2/dx^2-3q`.  It is tailored to the exact Born--Witten amplitude
factorization of the theta source and avoids treating the sixth log jet as an isolated error term.

For the first theta atom the cancellation is exact.  Its formulas above give

```text
q^2*r=16*(d+3)^3*(d^3+18d-24)/d^3,
(log(q^2*r))'
 =6*((d+3)*(d^2+6)/(d^3+18d-24)-3/d).
```

For every `d>3`,

```text
0 < (log(q^2*r))' < 6,
```

because the two cleared gaps are respectively

```text
d^4+6d^2-36d+72>0,
12*(d+3)*(d-2)>0.
```

Together with the exact first-atom floor `s>36`, this proves `(5e)` strictly for every positive
first-atom coordinate.  The unresolved source step is now precise: transfer the strict
`speed < 6 < sqrt(s)` cone through the ordered right-translate theta mixture.

The first-atom margin is in fact uniformly much larger.  Put

```text
H=d^3+18d-24,
N=d^4+6d^2-36d+72,
C=d^4-8d^3+24d^2+48d+156,
y=d-3.
```

Clearing the positive denominator in the exact formulas for `s` and the squared speed gives

```text
d^2 H^2 * (s-((log(q^2*r))')^2-32) = 2 P(y),
P(y)=3y^9+56y^8+498y^7+2448y^6+6600y^5+7524y^4
     +5670y^3+52344y^2+224397y+252396.                 (5h)
```

Every coefficient of `P` is positive, so the exact uniform gap is

```text
s-((log(q^2*r))')^2 > 32.                              (5i)
```

This identity has been checked by `ring` in the project Lean toolchain, but has not yet been moved
into a dependency-closed project theorem.

## Two-atom polarized fourth-order law `[LEAN-SCRATCH-PROVED]`

Remove the harmless common exponential gauge from the source and put

```text
y=2*pi*exp(2x),
psi_n(x)=n^2*(n^2*y-3)*exp(-n^2*y/2).
```

For `P_k(Y)=exp(Y/2)*(d/dx)^k((Y-3)exp(-Y/2))`, where `Y'=2Y`, the exact recurrence is

```text
P_(k+1)=2Y*P_k'-Y*P_k,
P_0=Y-3.
```

In particular the corrected upper jets are

```text
P_4=Y^5-23Y^4+136Y^3-204Y^2+40Y,
P_5=-Y^6+33Y^5-320Y^4+1020Y^3-856Y^2+80Y,
P_6=Y^7-45Y^6+650Y^5-3580Y^4+6976Y^3-3504Y^2+160Y.   (5k)
```

The earlier exploratory coefficients `-180,-620,...` were not generated by the recurrence and
are discarded.  This correction does not affect the pure Laplace-response polynomials used for
the `epsilon` estimates; those start from `P_0=1`, not `Y-3`.

Set `z=y-6>=0` and `q=exp(-3y/2)`.  Direct polarization of the fourth Hankel determinant of the
first two atoms gives the exact alternating decomposition

```text
exp(2y)*J_4(psi_1+psi_2)
 = C_0(z)-A_1(z)q+C_2(z)q^2-A_3(z)q^3+C_4(z)q^4,        (5l)
```

where every displayed polynomial has strictly positive coefficients.  Their coefficient lists,
in increasing powers of `z`, are

```text
C0=[13221937152,21391589376,16903655424,8283119616,2718987264,
    618347520,98654976,10957824,815616,36864,768]
A1=[30580728201216,129128555593728,210007037657088,191775162802176,
    113469000450048,46704828801024,13903960725504,3054904109568,
    498502598400,59972931648,5190508608,306835776,11119680,186624]
C2=[135418306343731200,376661648954621952,488391392092815360,
    390936205090750464,215707796923908096,86773330337955840,
    26245683031302144,6064922785628160,1076335642211328,146033346327552,
    14914320733440,1111931131392,57201811200,1816971264,26873856]
A3=[8417271706703364096,20284656771215130624,22595500203854266368,
    15406904631795646464,7176276446388682752,2411875441091543040,
    601912147307397120,112961938534170624,15945270000353280,
    1672195732733952,126642643206144,6558845239296,208174841856,
    3057647616]
C4=[7837334190050770944,13617468191658737664,10657995623157989376,
    4948363050152361984,1509309134464352256,316015235775332352,
    45999319588798464,4596392395800576,301738632413184,
    11751030521856,206158430208].
```

Let

```text
T_6(z)=sum_(j=0)^6 ((3z/2)^j/j!).
```

Two positive-coefficient certificates are enough:

```text
A_1(z)<3500*C_0(z)*T_6(z),
A_3(z)<8000*C_2(z).                                      (5m)
```

Since `8000<exp(9)` and `T_6(z)<exp(3z/2)`, one has
`8000*T_6(z)*q<1`.  Hence

```text
C_0-A_1*q > (9/16)*C_0,
C_2-A_3*q > 0,
```

and `(5l)` proves `J_4(psi_1+psi_2)>0` for every `x>=0`.  The determinant identity, both
coefficient certificates, the exponential estimate, and the final strict sign have been checked
without `sorry` by `lake env lean /tmp/ThetaPairPF4.lean`.  This is the first cancellation-
preserving global fourth-order theorem in the attack; it is not yet the completed source.

For a further atom with square scale `k>=9`, polarize the coefficient linear in that atom against
three choices from `{psi_1,psi_2}`.  After `y=z+6` and `k=m+9`, all coefficients are strictly
negative for each of the four possible numbers `0,1,2,3` of `psi_2` factors.  After removing the
sign, the response divided by `C_0(z)` is decreasing in `z`: the cleared derivative polynomial

```text
lambda*A*C_0-A'*C_0+A*C_0',  lambda=4+3r/2,
```

has positive coefficients for `r=0,1,2,3`.  Thus every one-higher-atom loss is maximal at the
left endpoint.  This coefficient statement is exact symbolic evidence and is the live next Lean
target; quadratic and higher occurrences of atoms `n>=3` remain to be bounded before global
`J_4` is closed.

## Polarized spectral-envelope closure `[CANDIDATE PAPER PROOF; TWO FINITE LEAN AUDITS OPEN]`

Write the gauge-normalized source as

```text
F=sum_(n>=1) psi_n=G+R,  G=psi_1+psi_2,  R=sum_(n>=3) psi_n.
```

Expanding the fourth Hankel determinant by rows according to the number of rows drawn from `R`
gives the exact absolutely convergent polarization

```text
J_4(F)=J_4(G)+H_1(G;R)+H_2(G;R)+H_3(G;R)+J_4(R).        (5n)
```

Put `C00=C_0(0)=13221937152`.  For an atom `n>=3`, write `n^2=9+m`.  Its exponential
relative to the four-first-atom scale splits as

```text
exp(-24)*exp(-3m)*exp(-4z)*exp(-mz/2).
```

The elementary bounds

```text
20<exp(3),  exp(-24)<10^(-10),  exp(-48)<10^(-20),
sum_(m>=0) 1/20^m=20/19,
sum_(m>=0) m^j/20^m <= j!*20^j/19^(j+1)  (j>=1)         (5o)
```

are enough.  The moment inequality follows from
`m^j<=m*(m+1)*...*(m+j-1)=j!*binom(m+j-1,j)`.  Also
`z^i*exp(-lambda*z)<=i!/lambda^i` by the exponential series.

For `r=0,1,2,3`, let `L_r(z,m)` be the polarized coefficient with one scale `9+m`, `r`
copies of scale four, and `3-r` copies of scale one, including arithmetic weights.  Exact
expansion gives

```text
-L_r(z,m)=sum_(0<=i<=15,0<=j<=8) a_(r,i,j)*z^i*m^j,
a_(r,i,j)>=0.                                           (5p)
```

Using `(5o)`, `lambda=4+3r/2`, and the bound `q^r<8000^(-r)`, the exact rational
coefficient sum satisfies

```text
sum_r 10^(-10)*8000^(-r)
 *sum_(i,j) a_(r,i,j)*(i!/lambda^i)*U_j < C00/40,       (5q)
U_0=20/19,  U_j=j!*20^j/19^(j+1).
```

Replacing the square gaps `m=n^2-9` by every integer `m>=0` only enlarges the positive
envelope.  Thus

```text
|H_1(G;R)| < exp(-2y)*C_0(z)/40.                        (5r)
```

For the quadratic term, take the coefficientwise absolute envelope of the polarization with
scales `9+m`, `9+n`, `r` copies of four, and `2-r` copies of one.  If its coefficients are
`b_(r,i,j,k)`, the corresponding exact rational certificate is

```text
sum_(r=0)^2 10^(-20)*8000^(-r)
 *sum_(i,j,k) |b_(r,i,j,k)|*(i!/(8+3r/2)^i)*U_j*U_k
 < C00/10^6.                                            (5s)
```

Hence

```text
|H_2(G;R)| < exp(-2y)*C_0(z)/10^6.                      (5t)
```

Claims `(5p)`--`(5s)` use only integer/rational polynomial arithmetic.  Their present status is
`[EXACT CERTIFICATES GENERATED, NOT YET LEAN-CHECKED]`; they are the two finite audits blocking
promotion of the global theorem.

Cubic and quartic terms no longer need polarized cancellation.  For `Y>=6`, the corrected atom
polynomials obey

```text
|P_j(Y)|<=c_j*Y^(j+1),  (c_0,...,c_6)=(2,2,3,5,10,21,49).  (5u)
```

For derivative exponent `a=2,...,8`, first-two and higher spectral moments at `y=6` obey

```text
S_a <= (2,2,2,2,2,4,10)_a,
T_a <= (10^-8,10^-7,10^-6,10^-5,10^-4,10^-3,10^-2)_a.  (5v)
```

Every higher moment gains `exp(-4z)`.  Summing the 24 determinant permutations and row choices
gives

```text
|H_3(G;R)| < exp(-2y)*C_0(z)/10^5,
|J_4(R)|   < exp(-2y)*C_0(z)/10^12.                     (5w)
```

The cleared rational ratios before rounding are

```text
7083866063871/1025000000000000000 < 10^-5,
18867249/256250000000000000000 < 10^-12.
```

The factors `(z+6)^16*exp(-12z)` and `(z+6)^16*exp(-16z)` are maximal at `z=0`, so
these bounds are uniform.  Combining `(5l)` and `(5n)`--`(5w)` yields

```text
exp(2y)*J_4(F)
 > C_0(z)*(9/16-1/40-1/10^6-1/10^5-1/10^12)>0.         (5x)
```

Thus `(5x)` becomes a dependency-closed paper proof once and only once `(5p)`, `(5q)`, and
`(5s)` pass Lean.  Until then the card remains `[OPEN GLOBAL J4]`.

The important reduction is that `(5c)` contains no fifth logarithmic derivative.  The remaining
kernel-specific frontier is therefore one even sixth-order inequality, not simultaneous control
of all fifth and sixth jets.  For the first-atom factorization `f=f_1 exp(epsilon)`, it uses only
`epsilon''`, `epsilon'''`, `epsilon''''`, and `epsilon''''''`.  The exact higher-tail Laplace
measure already in the corpus supplies the raw moments needed for the last term.

An absolute-jet perturbation is now ruled out as a proof architecture.  Since

```text
-T_6=q*r*(s-speed^2)>19*18*32=10944,
```

the available direct gapped-Laplace estimate `|epsilon''''''|<138000` already exceeds the entire
first-atom margin before the lower jets are charged.  This is not evidence against `PF4`; it shows
that separating the sixth jet destroys the determinant cancellation.  Any successful tail proof
must estimate the combined Schur functional `T_6`, or the exact necessary-and-sufficient numerator

```text
J_4/f^4=(3q*u^2-u*u''+(u')^2)/q,  u=q^2*r,              (5j)
```

without taking absolute values term by term.

## Exact modular seam at order four `[PAPER-PROVED]`

Let

```text
H(x)=exp(x/2) theta_3(i exp(2x)),
M=H(0), R_0=pi*M^4, X=R_0^2.
```

The self-dual modular differential system already derived in the corpus yields, for
`f=thetaCuspFullSource=(H''-H/4)/2`,

```text
f_0 = M (X-6)/16,
f_2 = -M (X^2+90X-120)/128,
f_4 = M (51X^3+382X^2+14400X-9120)/1024,
f_6 = M (849X^4-51510X^3-173464X^2-3785760X+1418880)/8192.   (5)
```

The first three formulas follow by differentiating the autonomous system through order five.  The
last is equivalently obtained from its dependency-closed sixth-seam identity

```text
f_0^2 f_6-15f_0f_2f_4+30f_2^3 = M^3 Q_6(X)/131072,
Q_6(X)=99X^6+12X^5-3160X^4-544272X^3
       -1446144X^2-1509120X+276480.
```

Besides the existing lower bound `X>191/10`, the theta series gives `X<20`: if
`q_0=exp(-pi)`, the exponential Taylor lower bound gives `q_0<11/250`, whence

```text
M = 1+2 sum_(n>=1) q_0^(n^2)
  < 1+2(q_0+q_0^4/(1-q_0^3)) < 109/100,
X = pi^2 M^8 < 10(109/100)^8 < 20.                    (6)
```

At an even seam the fourth signed Hankel determinant factors as

```text
J_4(0)=(f_0 f_4-f_2^2)(f_2 f_6-f_4^2).               (7)
```

Using `(5)`, the first factor is `M^2/16384` times

```text
A(X)=50X^4-104X^3+4248X^2-73920X+40320 > 0           (8)
```

for `X>=19`; group `(8)` as
`X^3(50X-104)+X(4248X-73920)+40320`.
The second factor is `M^2/1048576` times

```text
B(X)=-3450X^6-63864X^5+3296520X^4+3144960X^3
     +118091520X^2-319334400X+87091200.               (9)
```

For `19<=X<20`, group `(9)` as

```text
X^4(3296520-63864X-3450X^2)
 +3144960X^3+X(118091520X-319334400)+87091200,
```

whose four summands are positive.  Therefore `J_4(0)>0`.  Equations `(7)`--`(8)` also give the
strict seam value needed above for `J_3(0)=-f_2(f_0f_4-f_2^2)>0`.

## Open core

`[OPEN CORE]` Prove globally, without computation,

```text
J_4(t) > 0  for every t>0.
```

The seam and all lower orders are closed.  The genuine frontier is now the positive-half `J_4`:
after exponential-gauge normalization it is one explicit differential polynomial in `(log f)''`
through `(log f)^(6)`.  The live attack is a sixth-order extension of the exact first-atom/tail
likelihood domination used above.  No Toeplitz sampling, RH assumption, zero simplicity, or
interval arithmetic may enter.

## Significance gate

- A proof resolves Michałowski's named Problem 1 and, with the published `PF5` failure, gives the
  sharp order `PF4 \ PF5`.
- A proof of only the confluence formula is `[REDISCOVERED]`, not publication significance.
- A proof only for equal-spaced Toeplitz minors is insufficient: global admissible configurations
  are required.
- If `J_4` is negative anywhere, the same route instead gives an analytic `PF4` counterexample and
  still resolves Problem 1.

## Literature audit

- I. J. Schoenberg, finite-order Pólya-frequency and zero-location theory (1955).
- S. Karlin, extended total positivity and confluent derivative criteria (1964; 1968 monograph).
- A. Khare, characterization of `TN_p` functions by largest minors under decay
  (arXiv:2008.05121v2, Theorem E).
- W. Michałowski, certified `PF5` failure and open global `PF4` problem
  (arXiv:2602.20313v2, Problem 1).

## Log

- 2026-07-22 — Created after corpus/literature audit.  Identified exact confluent-Hankel reduction,
  corrected order-eight rather than order-fourteen derivative wall for `C5`, and isolated global
  `J_4` positivity as the noncomputational frontier.
- 2026-07-22 — Proved global strict `PF3` on paper by first-atom/tail domination.  Derived the
  universal three-curvature factorization and exact first-atom `q,r,s` laws.  Closed `J_4(0)>0`
  symbolically through the self-dual modular system and the exact chamber `191/10<X<20`.  Only
  `J_4(x)>0` for `x>0` remains.
- 2026-07-22 — Strengthened the first-atom fourth-order Schur margin to the exact uniform gap
  `s-speed^2>32`, with a positive-coefficient degree-nine certificate checked by Lean `ring`.
  Ruled out isolated sixth-log-jet domination: its absolute tail budget is larger than the full
  Schur margin.  Live route now requires cancellation-preserving control of `(5j)` or a modular
  core/far-field decomposition.
- 2026-07-22 — Found and Lean-scratch-proved the cancellation-preserving two-atom law `(5l)`--
  `(5m)`: the first two theta atoms have global strict fourth Hankel positivity with a uniform
  `9/16` base margin.  Corrected the stripped source-jet recurrence through order six.  Exact
  polarization shows every term linear in an atom `n>=3` is negative but its normalized loss is
  monotone decreasing away from the seam.  Nonlinear higher-tail polarizations remain open.
- 2026-07-22 — Derived candidate full spectral-envelope closure `(5n)`--`(5x)`.  Exact rational
  bounds leave more than one-half of the base determinant margin.  Cubic/quartic bounds are
  elementary; linear/quadratic bounds reduce to two finite coefficient audits.  No global theorem
  is claimed until those exact envelopes pass Lean.
