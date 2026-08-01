# Exact logarithmic remainder forces a signed half-log trace

- **ID:** `suzuki-exact-log-remainder-signed-trace-rigidity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SOURCE-BEARING BOUNDARY RIGIDITY
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Route:** Connes/CCM restricted-Weil form through Suzuki's completed zero-mode problem
- **Primary source:** M. Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1
- **Boundary sources:** H. Chen and T. Weth, *The Dirichlet Problem for the Logarithmic
  Laplacian*, arXiv:1710.03416v6; V. Hernandez-Santamaria, L. F. Lopez Rios, and A. Saldana,
  *Optimal boundary regularity and a Hopf-type lemma for Dirichlet problems involving the
  logarithmic Laplacian*, arXiv:2401.18033v2
- **Statement:** For the literal one-dimensional logarithmic Dirichlet jump operator, the optimal
  signed bound `u(r)=O(log(1/r)^(-1/2))` and a bounded source force the actual limit
  `sqrt(log(1/r))u(r)`. No conormal expansion, derivative of the nonlocal remainder, positivity,
  or one-signed hypothesis is needed. The exact logarithmic remainder cannot support the
  previously surviving nonconormal oscillatory escape.

## 1. Exact source theorem

Let `u` vanish outside `(0,1)` and put

```text
r=exp(-L),
F(L)=u(exp(-L)),
H(L)=sqrt(L)F(L).
```

For the unit-range logarithmic jump

```text
(J u)(r)=integral_(r-1)^(r+1) [u(r)-u(y)]/|r-y| dy,
```

the exact log-coordinate normal form is

```text
(J u)(exp(-L))
 =2L F(L)-integral_0^L F(t)dt
  +(R F)(L)+q(L)F(L),                                    (1)

(R F)(L)
 =integral_0^infinity k(s)[F(L)-F(L+s)]ds
  +integral_0^L k(s)[F(L)-F(L-s)]ds,                     (2)

k(s)=1/(exp(s)-1),
q(L)=-log(1-exp(-L)).
```

Assume:

1. `F` is bounded and continuous, and is locally Dini wherever needed so `(2)` is pointwise
   defined;
2. `H` is bounded on a terminal half-line;
3. `G(L)=(J u)(exp(-L))` is bounded on that half-line.

`[PROVED]` The signed half-log trace exists:

```text
beta=lim_(L->infinity) H(L).                              (3)
```

This is a signed theorem. It applies separately to every real zero mode and does not use a
maximum principle for `u`.

## 2. Symmetric remainder pairing

On the half-line, `(2)` is exactly the symmetric jump operator

```text
(R F)(L)
 =integral_0^infinity k(|L-M|)[F(L)-F(M)]dM.              (4)
```

Let `w` have bounded variation and be integrable on `[0,infinity)`, and extend it by zero to the
negative half-line. For bounded `F`,

```text
E_R(F,w)
 =(1/2) integral_0^infinity integral_0^infinity
   k(|L-M|)[F(L)-F(M)][w(L)-w(M)]dM dL                  (5)
```

is absolutely convergent. Indeed,

```text
integral_0^infinity |w(L+s)-w(L)|dL
 <=s Var(w_tilde),
```

and therefore

```text
|E_R(F,w)|
 <=2 ||F||_infinity Var(w_tilde)
   integral_0^infinity s/(exp(s)-1)ds
 <infinity.                                               (6)
```

Fubini and exchange of `L,M` give the exact integration-by-parts identity

```text
integral_0^infinity w(L)(R F)(L)dL=E_R(F,w).              (7)
```

For a fixed `L_0>0`, take

```text
w_M(L)=1_[L_0,M](L)L^(-3/2).
```

The zero extensions are BV, and

```text
Var((w_infinity-w_M)_tilde)=O(M^(-3/2)).
```

Equations `(5)`--`(7)` consequently show that the ordinary improper integral

```text
integral_(L_0)^infinity L^(-3/2)(R F)(L)dL               (8)
```

converges. This is the first key point: absolute pointwise control of `R F`, differentiation of
`R F`, and log-conormality of `F` are all unnecessary.

## 3. Exact averaged trace

Put

```text
Y(L)=integral_0^L F(t)dt,
P F(L)=2L F(L)-Y(L),
A(L)=Y(L)/(2sqrt(L)).
```

Direct differentiation gives

```text
A'(L)=(P F)(L)/(2L^(3/2)).                                (9)
```

By `(1)`,

```text
P F=G-R F-qF.                                             (10)
```

The `G` term in `(10)` is absolutely integrable against `L^(-3/2)` by boundedness. The same is
true of `qF` because `q(L)=O(exp(-L))`. The remainder term has a convergent improper pairing by
`(8)`. Hence `(9)` has a convergent improper integral and

```text
alpha=lim_(L->infinity) A(L)                              (11)
```

exists.

If

```text
m=liminf_(L->infinity) H(L),
M=limsup_(L->infinity) H(L),
```

then the weighted Cesaro form of `A` gives

```text
m<=alpha<=M.                                              (12)
```

The missing issue is whether an oscillatory `H` can have the averaged limit `(11)` without a
pointwise limit. The exact sign geometry of `R` excludes it.

## 4. Penalized-extremum noncancellation

Choose `L_n->infinity` with `H(L_n)->M`, set `epsilon_n=L_n^(-1/2)`, and let `X_n` maximize

```text
H(L)-epsilon_n |L-L_n|
```

on a terminal half-line. Boundedness of `H` gives

```text
|X_n-L_n|=O(epsilon_n^(-1))=O(sqrt(L_n)),
X_n/L_n->1,
H(X_n)->M.                                                (13)
```

At the maximizer,

```text
H(X_n+s)<=H(X_n)+epsilon_n s,
H(X_n-s)<=H(X_n)+epsilon_n s.                            (14)
```

For `0<s<=X_n/2`, Taylor's theorem for `x^(-1/2)` and `(14)` give

```text
2F(X_n)-F(X_n+s)-F(X_n-s)
 >=-C[
   ||H||_infinity s^2 X_n^(-5/2)
   +epsilon_n s X_n^(-1/2)].                             (15)
```

Both kernel moments

```text
integral_0^infinity s k(s)ds,
integral_0^infinity s^2 k(s)ds
```

are finite. The part `s>X_n/2` is exponentially small because `k(s)=O(exp(-s))`; the compact
left endpoint is harmless because `F` is bounded there. Integrating `(15)` yields

```text
(R F)(X_n)
 >=-C[
   ||H||_infinity X_n^(-5/2)
   +epsilon_n X_n^(-1/2)
   +exp(-X_n/2)].                                        (16)
```

Divide `(1)` by `sqrt(X_n)`. Since

```text
(P F)(L)/sqrt(L)=2[H(L)-A(L)],
G(L)/sqrt(L)->0,
q(L)F(L)/sqrt(L)->0,
```

and `(16)` says `(R F)(X_n)/sqrt(X_n)` has no negative limiting contribution, `(11)` gives

```text
M<=alpha.                                                 (17)
```

For the liminf sequence, minimize

```text
H(L)+epsilon_n|L-L_n|.
```

The reversed inequalities give

```text
(R F)(X_n)
 <=C[
   ||H||_infinity X_n^(-5/2)
   +epsilon_n X_n^(-1/2)
   +exp(-X_n/2)]
```

and hence

```text
m>=alpha.                                                 (18)
```

Combining `(12)`, `(17)`, and `(18)` gives

```text
m=alpha=M.
```

Thus `(3)` holds with `beta=alpha`. `QED`

## 5. Literal Suzuki consequence

At fixed aperture, Suzuki's distributional Weil operator is the logarithmic jump plus:

1. finitely many visible von-Mangoldt translations;
2. bounded zeroth-order polar--Gamma terms;
3. smooth endpoint-range corrections.

Every one of these maps a bounded interval function to a bounded source. Therefore any bounded
classical Suzuki zero mode satisfies assumption 3. The optimal boundary theorem of
Hernandez-Santamaria--Lopez Rios--Saldana gives assumption 2 once the bounded weak-source
hypotheses are available. Consequently:

```text
bounded classical Suzuki zero mode
 -> exact signed traces beta_+, beta_- exist.             (19)
```

The nonlocal remainder is no longer an open trace-integrability gate on this class. It has been
handled exactly, including nonconormal boundary frequencies.

The live source gate is now earlier and sharper:

```text
SUZUKI-BOUNDED-CLASSICAL-LIFT:
every completion-safe square-Evans zero mode belongs to the bounded weak/classical
solution class to which the optimal half-log estimate applies.              (20)
```

Only after `(20)` is proved may trace-zero regularity, corona no-return, and raw Evans positivity
be attacked. Assuming boundedness or classical pointwise evaluation for a completed zero mode
would be theorem theatre.

## 6. Hostile tests

### Averaging alone is insufficient

For

```text
F(L)=L^(-1/2)sin(sqrt(L)),
```

one has `A(L)->0` while `H(L)=sin(sqrt(L))` has no limit. But `P F` has size `sqrt(L)` along
extrema, so the bounded-source hypothesis fails. This shows why the extremal use of the exact
equation is essential.

### High log frequency does not escape

For a tail such as

```text
F(L)=L^(-1/2)sin(exp(L)),
```

`R` has logarithmic high-frequency size comparable to `sqrt(L)`. It cannot cancel `P` at both
upper and lower penalized extrema: `(16)` and its minimum analogue fix the favorable one-sided
sign. Thus the proof does not hide a conormal or low-frequency assumption.

### Sign changes are allowed

No positivity of `F`, `G`, or the zero mode appears. The maximum and minimum arguments are applied
to the conjugated signed profile `H`, not through a comparison principle.

### Exact kill boundary

The theorem does not cover an unbounded form-domain zero mode for which `J u` exists only weakly.
Such a mode is the only remaining boundary-frequency escape before trace formation. Proving `(20)`
or constructing a counterexample decides this theorem's exact reach.

## 7. Novelty boundary

The 2024 optimal-boundary theorem proves the sharp upper rate and a Hopf lower bound for
nonnegative supersolutions; it does not prove a signed normalized boundary limit. The earlier
Chen--Weth theory gives subcritical log-Holder decay and weak/classical solution infrastructure.
A targeted primary-literature search through 1 August 2026 found no signed half-log trace theorem,
no BV duality treatment of the exact remainder `(2)`, and no penalized-extremum noncancellation
argument for the critical normalized profile.

The Volterra identity `(9)`, BV jump-form integration by parts, and penalized maximum arguments
have classical parents separately. Novelty is claimed only for their exact conjunction on the
logarithmic Dirichlet normal form and the resulting removal of the nonconormal signed-trace gate.
Specialist priority review remains required.

## 8. Formalization decision

No Lean module is added yet. The theorem is source-bearing, but an exact formalization must include
the literal half-line kernel `(2)`, BV cutoff convergence, the two kernel moments, and penalized
extrema. Formalizing only `(9)` or an abstract `L1` perturbation would not certify the result and
would violate the anti-theatre rule. Lean starts after the source theorem is decomposed without
replacing `R` by an assumed bounded multiplier.

## Gates

- [x] exact symmetric half-line form of `R` used
- [x] BV pairing proves the weighted remainder integral without conormality
- [x] exact averaged half-log trace proved
- [x] penalized extrema eliminate slow and high-frequency signed oscillations
- [x] pointwise signed half-log trace proved for bounded-source optimal-boundary solutions
- [x] exact Suzuki lower terms checked to preserve boundedness
- [x] literature and corpus novelty boundary audited
- [ ] prove `SUZUKI-BOUNDED-CLASSICAL-LIFT`
- [ ] prove trace-zero completed zero modes enter `H1_0`
- [ ] prove two-ended corona no-return
- [ ] prove raw Evans positivity
- [ ] RH
