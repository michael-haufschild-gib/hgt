# Route J semilocal prolate third-Euler critical boundary

**Status:** `[PROVED; FORMALIZED]`

## Source input

Let

```text
t_n=2sqrt(2)(-4)^(-n)binom(2n,n),
Y_n={}_2F_1(1,n+1/2;n+1;-1).
```

Connes--Consani--Moscovici prove that coefficient `delta_3(n)` of `q^3` in squared-radius
increment anomaly is

```text
delta_3(n)
 = -(16n^2+8n+3)t_n^3Y_n^2/16
   +(4n^2+11n+3)t_n^3Y_n/4
   -(4n^4+4n^3+23n^2/4+7n/2+3/4)t_n^3
   +(32n^4+32n^3+48n^2+20n+27/8)t_n.                  (C1)
```

This published formula is input, not proposed novelty.

## First hostile prediction — resolved

Put

```text
tau=2sqrt(2/pi).
```

Wallis and `Y_n->1/2` give

```text
(-1)^n t_n sqrt(n) -> tau.
```

Last term of `(C1)` is therefore

```text
(-1)^n 32 tau n^(7/2)(1+o(1)).
```

Every `t_n^3` term is at most order `n^(5/2)`, and `Y_n` is uniformly bounded. Alternating
summation predicts that exact squared-radius coefficient

```text
S_n=[q^3]a_n(q)^2=sum_(j=0)^n delta_3(j)
```

obeys

```text
S_n / ((-1)^n n^(7/2)) -> 16 tau.                     (C2)
```

Writing

```text
a_n(q)=r_n+u_nq+v_nq^2+w_nq^3+O(q^4),
S_n=2r_nw_n+2u_nv_n,
```

and using `u_n=O(sqrt(n))`, `v_n->4/pi`, predicts

```text
w_n / ((-1)^n n^(5/2)) -> 8 tau
  =16sqrt(2/pi).                                       (C3)
```

This already falsifies naive order law `[q^r]R_n=O(n^(r/2))` at radius level.

## Critical weld theorem

Let `H_k=[q^3]R_k(q)` for Route-J four-radius residual. Terms involving `u_nv_n` are only
`O(sqrt(n))`. Linear `w` terms have alternating four-radius stencil. For a regularly varying
amplitude `f_n~Cn^(5/2)`, that stencil has leading multiplier

```text
-4*(5/2)=-10.
```

With `C=8tau`, proved theorem is

```text
H_(n+1)/(2(n+1))^(5/2)
  -> -80tau
   = -160sqrt(2/pi).                                   (C4)
```

Consequently third Euler order becomes order one at

```text
q^3 n^(5/2) asymp 1,
n asymp p^(6/5),                                       (C5)
```

strictly before first- and second-order `p^2` scale. This shows that `p^2` persistence through
order two is exceptional, not all-orders evidence.

## Resolved hostile checks

1. Prove `(C2)` from exact finite alternating sum, not endpoint heuristic.
2. Show all `t_n^3Y_n^j` contributions are negligible at `n^(7/2)` after summation without assuming
   unproved monotonicity of `Y_n`.
3. Prove regularly-varying shift differences needed for multiplier `-10`; pointwise asymptotics
   alone are insufficient.
4. Propagate exact positive-square-root identity, including `2u_nv_n`.
5. Prove all mixed `u v` critical terms vanish at `n^(5/2)` scale.
6. If `(C4)` fails, record exact surviving exponent and constant rather than forcing `p^2`.
7. Do not infer resummation or global-current existence from any fixed-order result.

## Lean target

```text
formal/GaloisForLFunctions/RHTower/
  SemilocalProlateThirdEulerCriticalJet.lean
```

No assumptions, computations, `sorry`, `admit`, project axioms, opaque constants, or unsafe
declarations.

## Resolution

Proof bypasses initial anomaly-summation heuristic and uses direct published determinant-ratio
coefficient. Its new `ell=1` term factors exactly as

```text
(-1)^n T_n(16n^2+20n+5+1/(4n+4)).
```

This yields signed squared-radius growth `n^(7/2)`, positive-radius growth `n^(5/2)`, exact
two-step multiplier `-5`, and four-radius multiplier `-10`. Canonical dependency-closed
certificate:

```text
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  route-j-semilocal-prolate-third-euler-critical-boundary.md
```

Direct `lake env lean` validation and exact-target module build pass. `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`.
