# Bounded weak Suzuki zero modes have signed half-log traces

- **ID:** `suzuki-weak-signed-half-log-trace`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / WEAK-TO-TRACE REGULARITY
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parent:** `suzuki-exact-log-remainder-signed-trace-rigidity.md`
- **Input:** `suzuki-completed-eigenmode-atomic-jump-boundedness.md`
- **Route:** Connes/CCM restricted-Weil form through Suzuki's completed zero modes
- **Statement:** The signed half-log trace theorem for the one-dimensional logarithmic
  Dirichlet operator remains true for bounded continuous weak solutions.  Pointwise Dini
  regularity is unnecessary.  Consequently every completed Suzuki zero mode has two signed
  endpoint traces.

## 1. Weak exact theorem

Let \(F:[0,\infty)\to\mathbb R\) be bounded and continuous, set

```text
H(L)=sqrt(L)F(L),
Y(L)=integral_0^L F(t)dt,
P F(L)=2L F(L)-Y(L),                                    (1)
```

and extend \(F\) by zero to a function \(f\) on the whole real line.  Let

```text
k(s)=1/(exp(s)-1)
```

and define the translation-invariant symmetric jump operator

```text
(R_full f)(L)
 =integral_0^infinity k(s)
   [2f(L)-f(L+s)-f(L-s)]ds                              (2)
```

in the distributional/jump-form sense.

Assume:

1. \(H\) is bounded on a terminal half-line;
2. for some \(G\in L^\infty\) the equation

```text
P F+R_full f=G                                           (3)
```

holds distributionally on a terminal half-line.

`[PROVED]` Then the signed trace exists:

```text
lim_(L->infinity) sqrt(L)F(L)=beta.                      (4)
```

No pointwise definition of `(2)`, Dini modulus, positivity, or conormal
expansion is assumed.

## 2. Why `(3)` is the exact Dirichlet equation

The half-line remainder in the parent theorem is

```text
(R_half F)(L)
 =integral_0^infinity k(s)[F(L)-F(L+s)]ds
  +integral_0^L k(s)[F(L)-F(L-s)]ds,                    (5)

q(L)=-log(1-exp(-L)).
```

Since

```text
integral_L^infinity k(s)ds=-log(1-exp(-L))=q(L),         (6)
```

zero extension gives the exact identity

```text
R_full f=R_half F+qF                                    (7)
```

whenever the expressions are pointwise meaningful, and `(7)` holds in the
jump-form sense without pointwise regularity.  Thus the exact log-coordinate
Dirichlet normal form

```text
J u(exp(-L))=P F+R_half F+qF
```

is precisely `(3)`.  The apparent boundary correction is the missing
negative-half-line part of a translation-invariant jump operator.

## 3. Averaged trace survives in the weak class

Let \(w\) be integrable and of bounded variation on the half-line, extended
by zero to the line.  For bounded \(F\), the jump-form pairing

```text
E_R(F,w)
 =(1/2) integral_0^infinity integral_0^infinity
  k(|L-M|)[F(L)-F(M)][w(L)-w(M)]dM dL                  (8)
```

is absolutely convergent because

```text
integral_0^infinity |w(L+s)-w(L)|dL
 <=s Var(w_tilde),
integral_0^infinity s k(s)ds<infinity.                  (9)
```

Taking truncated weights

```text
w_M(L)=1_[L_0,M](L)L^(-3/2)
```

in the distributional equation proves convergence of

```text
integral_(L_0)^infinity L^(-3/2)(R_full f)(L)dL.         (10)
```

Since

```text
A(L)=Y(L)/(2sqrt(L)),
A'(L)=P F(L)/(4L^(3/2))                                 (11)
```

(The constant is 4, not 2: differentiating `Y/(2sqrt(L))` gives
`F/(2sqrt(L))-Y/(4L^(3/2))=[2LF-Y]/(4L^(3/2))`.  The normalisation
`A=Y/(2sqrt(L))` is the one forced by `(13)`, since it is the one for
which `A` and `H` share a limit, and it is the one that makes the display
preceding `(28)`, `P f/sqrt(L)=2[H-A]`, correct.)

distributionally and the bounded source is integrable against
\(L^{-3/2}\), `(10)` implies

```text
alpha=lim_(L->infinity) A(L)                            (12)
```

exists.  Weighted Cesaro comparison gives

```text
liminf H<=alpha<=limsup H.                              (13)
```

This repeats the parent BV argument and requires no strengthening.

## 4. Translation-invariant mollification

Choose an even nonnegative \(C^\infty_c(-1,1)\) mollifier \(\rho\) of mass
one and write

```text
rho_epsilon(s)=epsilon^(-1)rho(s/epsilon),
f_epsilon=rho_epsilon*f.                                (14)
```

The whole-line operator `(2)` is translation invariant, so convolution
commutes with it exactly in distributions:

```text
R_full f_epsilon=rho_epsilon*(R_full f).                (15)
```

Write

```text
Y_f(L)=integral_(-infinity)^L f(t)dt.
```

Since \(Y_f=\mathbf 1_{[0,\infty)}*f\), primitive formation also commutes
with convolution:

```text
Y_(f_epsilon)=rho_epsilon*Y_f.                           (16)
```

Only multiplication by \(L\) fails to commute.  A direct calculation gives

```text
P f_epsilon
 =rho_epsilon*(P f)
  +2 integral_R s rho_epsilon(s)f(L-s)ds.               (17)
```

For points whose \(\epsilon\)-neighborhood lies in the half-line on which
`(3)` holds, `(15)`--`(17)` give the pointwise smooth equation

```text
P f_epsilon+R_full f_epsilon=G_epsilon+C_epsilon,        (18)

G_epsilon=rho_epsilon*G,
C_epsilon(L)=2 integral_R s rho_epsilon(s)f(L-s)ds.
```

Uniformly for \(0<\epsilon\le1\),

```text
||G_epsilon+C_epsilon||_infinity
 <=||G||_infinity+2||f||_infinity.                      (19)
```

Moreover, if \(\sqrt L F(L)\) is bounded, then

```text
sqrt(L)|f_epsilon(L)|
 <=C sup_(|s|<=1) sqrt(L/(L-s)) ||H||_infinity          (20)
```

on a fixed terminal half-line.  Thus the smooth approximants satisfy exactly
the same source and critical-profile bounds, uniformly in \(\epsilon\).

## 5. Moving-mollifier penalized maxima

Put

```text
M=limsup_(L->infinity)H(L).
```

Choose \(L_n\to\infty\) with \(H(L_n)\to M\).  Continuity of \(F\) permits a
choice \(0<\epsilon_n<1/n\) such that

```text
sqrt(L_n)|f_(epsilon_n)(L_n)-F(L_n)|<1/n.                (21)
```

Define

```text
H_n(L)=sqrt(L)f_(epsilon_n)(L),
delta_n=L_n^(-1/2),
```

and let \(X_n\) maximize

```text
H_n(L)-delta_n|L-L_n|                                   (22)
```

on a fixed terminal half-line.  The uniform bound `(20)` and `(21)` imply

```text
|X_n-L_n|=O(sqrt(L_n)),
X_n/L_n->1,
H_n(X_n)->M.                                             (23)
```

The maximizer is interior for large \(n\).  Hence

```text
H_n(X_n+s)<=H_n(X_n)+delta_n s,
H_n(X_n-s)<=H_n(X_n)+delta_n s.                          (24)
```

For \(0<s\le X_n/2\), the same elementary expansion of
\((X_n\pm s)^{-1/2}\) as in the parent theorem gives

```text
2f_(epsilon_n)(X_n)
 -f_(epsilon_n)(X_n+s)-f_(epsilon_n)(X_n-s)
 >=-C[
   ||H_n||_infinity s^2 X_n^(-5/2)
   +delta_n s X_n^(-1/2)].                              (25)
```

Both moments \(\int s k(s)ds\) and \(\int s^2k(s)ds\) are finite, while
the range \(s>X_n/2\) is exponentially small.  Therefore

```text
(R_full f_(epsilon_n))(X_n)
 >=-o(sqrt(X_n)).                                        (26)
```

The source in `(18)` is uniformly bounded by `(19)`.

Let

```text
A_n(L)=Y_(f_(epsilon_n))(L)/(2sqrt(L)).
```

From `(16)`,

```text
A_n(X_n)
 =integral rho_(epsilon_n)(s)
   A(X_n-s)sqrt((X_n-s)/X_n)ds
 ->alpha.                                                (27)
```

Divide `(18)` at \(X_n\) by \(\sqrt{X_n}\).  Since

```text
P f_(epsilon_n)(X_n)/sqrt(X_n)
 =2[H_n(X_n)-A_n(X_n)],
```

equations `(19)`, `(23)`, `(26)`, and `(27)` yield

```text
M<=alpha.                                                (28)
```

For

```text
m=liminf_(L->infinity)H(L),
```

choose a minimizing sequence, select mollifiers as in `(21)`, and minimize

```text
H_n(L)+delta_n|L-L_n|.
```

All signs reverse, giving

```text
(R_full f_(epsilon_n))(X_n)<=o(sqrt(X_n)),
m>=alpha.                                                (29)
```

Together with `(13)`, `(28)`--`(29)` give

```text
m=alpha=M.
```

This proves `(4)`. `QED`

## 6. Literal Suzuki consequence

The atomic-jump boundedness theorem proves that every

```text
u in ker A_a
```

is a bounded continuous weak solution of the ordinary logarithmic
Dirichlet equation with bounded source and satisfies the optimal bound

```text
|u(x)|=O(log(1/dist(x,{ -a,a }))^(-1/2)).                (30)
```

The exact logarithmic change of variables is valid distributionally, and all
finite von-Mangoldt translations and the compact polar--Gamma convolution
remain bounded sources.  Applying the weak theorem at each endpoint gives

```text
beta_+(u)=lim_(x->a-)
  sqrt(log(1/(a-x)))u(x),

beta_-(u)=lim_(x->-a+)
  sqrt(log(1/(x+a)))u(x).                                (31)
```

Thus:

```text
every completed Suzuki zero mode has two signed half-log traces.            (32)
```

The entire pre-trace regularity gate is closed.  The next RH-bearing theorem
is now the trace-zero lift:

```text
SUZUKI-TRACE-ZERO-H1:
u in ker A_a and beta_+(u)=beta_-(u)=0
implies u in H^1_0(-a,a).                                (33)
```

## 7. Hostile audit

### Fixed mollification would be insufficient

A fixed convolution radius can erase oscillations occurring on smaller
scales.  The proof chooses \(\epsilon_n\) after the extremal sequence and
uses only estimates uniform in \(\epsilon\).  Equation `(21)` therefore
retains the original limsup or liminf.

### No commutator is hidden in the hard operator

Mollifying \(R_{\rm half}\) directly would produce a boundary commutator.
Identity `(7)` first joins it to \(qF\), producing the whole-line
translation-invariant operator.  The only commutator is the explicit bounded
term `(17)`.

### No pointwise weak equation is assumed

Equation `(3)` is convolved as a distribution.  The mollified equation
`(18)` is genuinely pointwise because \(f_\epsilon\) is smooth and the
symmetric second difference makes `(2)` locally integrable.

### High-frequency oscillation remains visible

The radius \(\epsilon_n\) may tend to zero arbitrarily fast.  The source
bound `(19)` does not involve derivatives of the mollifier, so rapid
oscillations cannot escape by making the mollified equation expensive.

### Signed and nonpositive modes are covered

Maxima and minima of the normalized signed profile are treated separately.
No maximum principle for \(u\) or ground-state hypothesis appears.

## 8. Novelty boundary

The parent theorem introduced the BV weighted pairing and penalized-extremum
sign argument for pointwise Dini solutions.  The new step is the exact
whole-line identity `(7)` and the moving-mollifier transfer
`(14)`--`(29)`, which removes all pointwise regularity from the source
theorem.  A targeted primary-literature search through 1 August 2026 found no
weak signed normalized boundary-trace result of this kind for the logarithmic
Dirichlet Laplacian or Suzuki's restricted-Weil operator.

Distributional convolution and moving mollifiers are classical separately.
Novelty is claimed only for their exact conjunction with the zero-extended
logarithmic jump, critical half-log normalization, and Suzuki completed
zero-mode consequence.  Specialist priority review remains required.

## 9. Formalization decision

Exact Lean formalization must include:

1. the half-line/whole-line identity `(6)`--`(7)`;
2. convolution commutation and the explicit \(P\)-commutator `(17)`;
3. moving mollifier selection `(21)`;
4. penalized extrema and uniform moment bounds.

An abstract theorem assuming a pointwise remainder or an unexplained
commutator bound would not certify the scientific result.  Lean work begins
only with this exact decomposition.

## Gates

- [x] half-line remainder plus killing term identified with whole-line jump
- [x] distributional averaged trace retained
- [x] hard nonlocal operator shown to commute exactly with mollification
- [x] only principal commutator computed and uniformly bounded
- [x] moving mollifier preserves original extremal sequences
- [x] penalized-extremum proof transferred to bounded continuous weak solutions
- [x] both signed endpoint traces proved for every completed Suzuki zero mode
- [ ] prove trace-zero completed zero modes lie in \(H^1_0\)
- [ ] identify trace-zero square-Evans kernel with raw Evans kernel
- [ ] prove two-ended corona no-return
- [ ] prove raw Evans positivity for every aperture
- [ ] RH
