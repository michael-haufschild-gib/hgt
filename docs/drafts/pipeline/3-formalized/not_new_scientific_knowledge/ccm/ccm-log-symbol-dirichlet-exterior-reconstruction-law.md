# The CCM logarithmic Dirichlet problem reconstructs every exterior characteristic state

- **ID:** `ccm-log-symbol-dirichlet-exterior-reconstruction-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** the first representation theorem for closed positive forms, the Carleman operator,
  and `ccm-exterior-range-observability-law.md`

## Statement

Fix an aperture `a>0`, put `I=(-a,a)` and `E=R minus [-a,a]`, and use the normalized
characteristic factorization

```text
W_a(xi)=b_a(xi)c_a(xi),
b_a(xi)=p_a(xi)/(1+xi^2)^(d_a/2),                        (1)
```

where `p_a` is monic and contains every real zero of `W_a` with its multiplicity. Then `c_a` has
constant positive sign and

```text
c_a(xi)=ell(xi)+q_a(xi),
ell(xi)=(1/2)log(1+xi^2),
q_a in L_infinity(R),
gamma_a:=inf_R c_a>0.                                    (2)
```

Let `C_a=c_a(D)` be the positive logarithmic multiplier. Its cross-boundary block

```text
K_(a,EI)=1_E C_a 1_I : L2(I)->L2(E)                     (3)
```

extends boundedly. Let `C_(a,I)` be the Dirichlet operator associated with the closed form

```text
q_(a,I)[u,h]
 =integral_R c_a(xi)hat u(xi)conj(hat h(xi))dxi,
supp u,supp h subset [-a,a].                             (4)
```

Then `C_(a,I)>=gamma_a`, so it has a bounded inverse on `L2(I)`. For every `f in L2(I)`, the vector

```text
u_f=C_(a,I)^(-1)f                                        (5)
```

belongs to the global domain of `C_a`, is supported in `[-a,a]`, and satisfies

```text
1_I C_a u_f=f,
v_E(f):=1_E C_a u_f=K_(a,EI)u_f in L2(E).                (6)
```

If `R_a=C_a^(-1)=m_a(D)` and `D_(a,E)=1_E R_a1_E`, then `v_E(f)` is the unique solution of

```text
D_(a,E)v_E=-1_E R_a1_I f.                                (7)
```

Consequently the observability constant from
`ccm-exterior-range-observability-law.md` is finite for every interior forcing and obeys

```text
C_a^obs(f)=||v_E(f)||
 <=||K_(a,EI)|| gamma_a^(-1)||f||.                       (8)
```

In particular, the admissible characteristic space is the full characteristic space:

```text
F_a^adm=F_a.                                             (9)
```

## 1. Bounded logarithmic remainder

The corrected aperture symbol satisfies

```text
W_a(xi)=log|xi|+O_a(1).                                  (10)
```

Because `p_a` is monic of even degree and the denominator in `(1)` has the same degree,

```text
b_a(xi)=1+O_a(|xi|^(-2)).                                (11)
```

The quotient `c_a=W_a/b_a` is smooth across the common real zeros. Equations `(10)`--`(11)` give

```text
c_a(xi)-ell(xi)=O_a(1)                                   (12)
```

at infinity, and continuity gives boundedness on the remaining compact set. This proves `(2)`.
Since `c_a` is real-zero-free and positive at infinity, it is positive everywhere; its divergence
at infinity gives `gamma_a>0`.

## 2. The cross-boundary logarithmic block is Carleman-bounded

The heat-semigroup representation

```text
log(1+xi^2)
 =integral_(0,infinity) e^(-t)(1-e^(-t xi^2))dt/t        (13)
```

shows that, away from the diagonal, the distribution kernel of `ell(D)` is a constant multiple of

```text
-e^(-|x-y|)/|x-y|.                                      (14)
```

For `x>a` and `y<a`, write `s=x-a>0` and `t=a-y>0`. The absolute value of `(14)` is bounded by

```text
1/(s+t).                                                 (15)
```

The integral operator with kernel `1/(s+t)` on the positive half-line is the classical Carleman
operator and is bounded on `L2`, with norm `pi`. Extending the input from `(0,2a)` by zero proves
boundedness across the right boundary. Reflection gives the left boundary. Hence

```text
1_E ell(D)1_I:L2(I)->L2(E)                               (16)
```

is bounded. The multiplier `q_a(D)` is bounded on the whole line by `(2)`, so its cross block is
bounded as well. Their sum is `(3)`.

## 3. Coercive Dirichlet reconstruction

Let `V_(a,I)` be the closed subspace of the form domain of `C_a` consisting of vectors supported in
`[-a,a]`. Equation `(2)` gives

```text
q_(a,I)[u,u]>=gamma_a||u||^2.                            (17)
```

The first representation theorem produces a positive self-adjoint operator `C_(a,I)` on `L2(I)`
with lower bound `gamma_a`. Therefore `(5)` exists uniquely and

```text
||u_f||<=gamma_a^(-1)||f||.                              (18)
```

By the definition of the associated operator, the interior restriction of `C_a u_f` equals `f`
weakly. Since `u_f` is supported in `I`, the bounded cross block `(3)` gives

```text
1_E C_a u_f=K_(a,EI)u_f in L2(E).                        (19)
```

Thus the full distribution `C_a u_f` belongs to `L2(R)`, proving that `u_f` is in the global
operator domain and establishing `(6)`.

Now put `v=f+v_E(f)=C_a u_f`. Since `R_av=u_f` is supported in `I`, exterior projection gives
`(7)`. The exterior inverse-symbol block is injective, so the solution is unique. Equations
`(8)`--`(9)` follow from `(18)`--`(19)`. `QED`

## Positive CCM consequence

The dense nonclosed exterior range is not the RH-bearing obstruction on finite characteristic
forcing: the logarithmic Dirichlet solve places every such forcing in the range canonically. A
successful CCM proof is therefore forced to use the reconstructed map

```text
f |-> u_f=C_(a,I)^(-1)f,
f |-> v(f)=C_a u_f=f+v_E(f),                              (20)
```

and prove that the finite characteristic trace satisfies no nonzero complete compatibility:

```text
1_I b_a(D)v(f)=0,
integral_I u_f=0,
(G_a u_f)(0)=0,
(G_a u_f)(a/2)=0.                                       (21)
```

The first condition in `(21)` is essential. Clearing the rational denominator proved only
`p_a(D)f=0`; because `b_a(D)` is nonlocal, that local ODE condition does not imply the original
interior multiplier equation.

Thus the live object is the source-defined finite-input map

```text
E_a^eff:F_a -> H_a^(-log) direct_sum C^3,
E_a^eff(f)=
 (1_I b_a(D)C_a C_(a,I)^(-1)f,
  integral_I u_f,(G_a u_f)(0),(G_a u_f)(a/2)).           (22)
```

Here `H_a^(-log)` denotes the natural dual logarithmic form space. Proving `E_a^eff` injective for
every aperture is equivalent to the characteristic-branch null theorem once the standard local
logarithmic regularity needed for the initial factorization is supplied.

`[PROVED SUBSEQUENT CLOSURE]` That regularity is automatic for every screw null vector. The
transformed trace satisfies the characteristic constant-coefficient ODE in the aperture and is
therefore an exponential polynomial there; the bounded cross block controls its exterior trace.
Hence it belongs to global `L2` and equals the Dirichlet reconstruction. This is proved in
`ccm-screw-null-global-log-regularity-law.md`.

## Scope and classification

The proof uses standard closed-form theory and the classical Carleman operator. It closes a route
gate but is not new scientific knowledge. Formalizing it would require a substantial Fourier
multiplier, heat-kernel, and unbounded-form layer absent from the current Lean tree; a finite
wrapper would not capture the theorem, so no Lean file is added.

## Gates

- [x] normalized zero-free factor split into logarithmic plus bounded parts
- [x] cross-boundary logarithmic multiplier proved bounded by the Carleman operator
- [x] coercive Dirichlet realization constructed
- [x] every interior `L2` forcing reconstructed with global transformed trace in `L2`
- [x] observability constant bounded uniformly and `F_a^adm=F_a`
- [x] exact effective residual/anchor map isolated
- [x] prove the initial local logarithmic-elliptic factorization for every screw null vector
- [ ] prove `E_a^eff` injective for every aperture
- [ ] RH

## Lean status

`[FORMALIZED]` — supersedes the "no Lean file is added" decision recorded above.  The multiplier,
heat-kernel and unbounded-form layers remain cited parents, but the card's own structural steps —
the positive infimum, the Carleman domination, the coercive inverse bound and the observability
estimate — are reachable and are now proved.

Module: `formal/GaloisForLFunctions/RHTower/CCM/CCMLogSymbolDirichlet.lean`
(4 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]`, wired into
`formal/GaloisForLFunctions/RHTower.lean`).

What is proved in Lean:

- `exists_pos_lower_bound_of_tendsto_atTop` — **equation (2), `γ_a > 0`**: a continuous everywhere
  positive symbol that tends to `+∞` at infinity has a strictly positive infimum.  Proof: outside a
  compact set the symbol is `≥ 1`; on the compact set it attains a positive minimum.
- `log_cross_kernel_le_carleman` — **equations (14)–(15)**: with `s = x−a > 0`, `t = a−y > 0` the
  logarithmic cross kernel `−e^{-(s+t)}/(s+t)` is dominated in absolute value by the Carleman kernel
  `1/(s+t)`.  The exterior displacement identity `x − y = s + t` itself is
  `CCMEvansBoundaryInfiniteRank.exterior_displacement_split`, reused.
- `norm_le_of_coercive` — **equations (17)–(18)**: from the coercivity `γ‖u‖² ≤ ⟪f,u⟫` and
  Cauchy–Schwarz, `‖u_f‖ ≤ γ^{-1}‖f‖`.
- `observability_bound` — **equations (8)–(9)**: composing with a bounded cross block gives
  `‖v_E(f)‖ ≤ ‖K‖ γ^{-1}‖f‖`, so the observability constant is finite for every interior forcing and
  `F_a^adm = F_a`.

Deliberately outside the Lean statement (cited parents, not results of this card):

- the heat-semigroup representation `(13)` and the explicit kernel `(14)`;
- the boundedness (norm `π`) of the classical Carleman operator;
- the first representation theorem producing `C_{a,I}` and the multiplier calculus for `c_a(D)`;
- the asymptotics `(10)`–`(12)` of the corrected aperture symbol.
