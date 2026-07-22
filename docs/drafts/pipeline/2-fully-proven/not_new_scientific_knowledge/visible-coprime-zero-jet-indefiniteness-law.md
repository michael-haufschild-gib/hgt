# Visible-coprime zero-jet orientation and indefiniteness law

- **ID:** `visible-coprime-zero-jet-indefiniteness-law`
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** THEOREM (paper) / NO-GO / BRIDGE
- **Scientific status:** `[PAPER-PROVED] [REDISCOVERED PARENTS] [BRIDGE] [NOT RH]`
- **Source:** Möbius--Laplace renewal law / visible-lattice inversion / GCD-matrix inertia
- **Statement:** Primitive-lattice convolution gives an exact signed zero-orientation jet, but
  its coprimality kernel has Möbius inertia and therefore unbounded negative index; no positive
  divisor-stationary kernel can retain the critical-line zero.

## Goal

Test whether the exact Möbius--Laplace Lambert law can be squared over primitive dilation pairs
to produce a positive source for the missing half-power bound.  The answer is exact: primitive
convolution does detect horizontal zero orientation, but precisely through an indefinite kernel.
This closes positive GCD-kernel and finite-negative-index versions of the route.

Put

```text
Phi(x)=sum_(n>=1) mu(n) exp(-n x),    x>0.
```

## Exact visible-addition law

Absolute convergence and the Lambert identity give

```text
sum_(n>=1) Phi(n x)=exp(-x).                                  (V1)
```

For `r>=2` and `x_1,...,x_r>0`, define

```text
P_r(x_1,...,x_r)
 = sum_(gcd(a_1,...,a_r)=1) product_j Phi(a_j x_j).           (V2)
```

Every positive lattice point has a unique common gcd.  Hence

```text
sum_(d>=1) P_r(d x_1,...,d x_r)
 = product_j sum_(a_j>=1) Phi(a_j x_j)
 = product_j exp(-x_j)=exp(-(x_1+...+x_r)).                  (V3)
```

Möbius inversion along the common dilation gives the exact universal law

```text
P_r(x_1,...,x_r)
 = sum_(d>=1) mu(d) exp(-d(x_1+...+x_r))
 = Phi(x_1+...+x_r).                                        (V4)
```

For `r=2`,

```text
sum_((a,b)=1) Phi(a x) Phi(b y)=Phi(x+y).                    (V5)
```

This is a genuine nonlinear identity, but it is not a source estimate.

## Mellin symbol and zero radical

For `Re(s),Re(t)>1`, the primitive-lattice Mellin symbol is the classical identity

```text
K(s,t)=sum_((a,b)=1) a^(-s)b^(-t)
      =zeta(s)zeta(t)/zeta(s+t).                             (V6)
```

Thus every zeta-zero mode belongs to the radical of primitive convolution.  This is the exact
reason `(V5)` can hold in the presence of a hypothetical off-line zero: the nonlinear carrier
annihilates, rather than controls, the offending Mellin mode.

## Hermitian zero-jet orientation law

Let `rho` be a nontrivial zeta zero of multiplicity `m`, and put `beta=Re(rho)`.  Interpret
`1/zeta(u)` at `u=1` by its holomorphic continuation, whose value is zero.  Then

```text
J(rho)
 = (partial_s^m partial_t^m K)(rho,conj(rho))
 = |zeta^(m)(rho)|^2 / zeta(2 beta).                         (V7)
```

Indeed, every zeta derivative of order below `m` vanishes at `rho` and `conj(rho)`.  In the
two Leibniz expansions, any derivative falling on `1/zeta(s+t)` therefore leaves a lower zeta
derivative and vanishes.  The unique survivor differentiates each numerator factor exactly `m`
times, proving `(V7)`.

For `0<u<1`, the alternating eta series is positive and

```text
zeta(u)=eta(u)/(1-2^(1-u))<0.
```

For `u>1`, the positive Dirichlet series gives `zeta(u)>0`, while `1/zeta(1)=0`.  Since the
leading zero derivative is nonzero,

```text
sign J(rho)=sign(2 Re(rho)-1),                              (V8)
J(rho)=0  iff  Re(rho)=1/2.                                (V9)
```

This is an exact pointwise orientation law, not proof that the jet vanishes.

### Primitive Dirichlet-character form

Let `chi` be primitive modulo `q`, and let `chi_0(n)=|chi(n)|^2` be the principal character.
For `Re(s),Re(t)>1`,

```text
K_chi(s,t)
 =sum_((a,b)=1) chi(a)conj(chi(b))a^(-s)b^(-t)
 =L(s,chi)L(t,conj(chi))/L(s+t,chi_0).                      (V10)
```

If `rho` is a nontrivial zero of `L(s,chi)` of multiplicity `m`, coefficient conjugation makes
`conj(rho)` a zero of `L(t,conj(chi))` with the same multiplicity.  The same Leibniz argument gives

```text
J_chi(rho)
 = |L^(m)(rho,chi)|^2 / L(2 Re(rho),chi_0).                 (V11)
```

Since

```text
L(u,chi_0)=zeta(u) product_(p|q)(1-p^(-u)),                 (V12)
```

and every finite Euler factor is positive for real `u>0`, `(V8)`--`(V9)` hold unchanged.  This
includes real exceptional zeros; no simplicity assumption is used.

## Exact finite inertia law

Let `C_N` be the real `N x N` coprimality matrix

```text
C_N(i,j)=1 if gcd(i,j)=1, and 0 otherwise.                  (V13)
```

Let `E_N(i,d)=1` when `d|i` and zero otherwise.  Divisor Möbius inversion gives

```text
C_N=E_N diag(mu(1),...,mu(N)) E_N^T.                        (V14)
```

In numerical order, `E_N` is lower triangular with diagonal one, hence invertible.  Sylvester's
law of inertia proves

```text
n_+(C_N)=#{d<=N:mu(d)=+1},
n_0(C_N)=#{d<=N:mu(d)=0},
n_-(C_N)=#{d<=N:mu(d)=-1}.                                 (V15)
```

In particular the negative index is unbounded: every new prime supplies another `mu(p)=-1`
diagonal direction.  No correction of fixed finite rank can make all `C_N` positive semidefinite.

The same formula gives an exact spectral-flow law.  If `sig(A)=n_+(A)-n_-(A)`, then

```text
sig(C_N)=sum_(d<=N)mu(d)=M(N),                              (V15a)
sig(C_N)-sig(C_(N-1))=mu(N).                               (V15b)
```

Thus the prime number theorem is exactly `sig(C_N)=o(N)`, and the classical Littlewood
criterion rewrites RH as

```text
for every epsilon>0, sig(C_N)=O_epsilon(N^(1/2+epsilon)).   (V15c)
```

This is an exact `0`--`1` matrix encoding of Mertens cancellation, not an independent spectral
bound: factorization `(V14)` already contains every Möbius sign on its diagonal.

## Universal positive-kernel obstruction

For a real arithmetic sequence `c(d)`, consider the divisor-stationary kernel

```text
H_c(a,b)=sum_(d|gcd(a,b)) c(d).                             (V16)
```

On every initial finite interval its matrix factors as

```text
H_(c,N)=E_N diag(c(1),...,c(N)) E_N^T.                      (V17)
```

Consequently `H_(c,N)` is positive semidefinite for every `N` if and only if `c(d)>=0` for every
`d`.  Its Mellin symbol, wherever absolutely convergent, is

```text
sum_(a,b>=1) H_c(a,b)a^(-s)b^(-t)
 =zeta(s)zeta(t) C(s+t),
C(u)=sum_(d>=1)c(d)d^(-u).                                 (V18)
```

If the critical energy `C(1)` is finite and `c` is nonzero and nonnegative, then `C(1)>0`; if it
is infinite, no finite critical kernel value exists.  Therefore a nonzero positive
divisor-stationary kernel can neither have a finite zero at `s+t=1` nor reproduce `(V9)`.
The coprimality detector uses `c=mu` and `C=1/zeta`; its critical zero is purchased exactly by
the unbounded negative inertia `(V15)`.

## Positive diagonal completion destroys the detector

The obstruction is not confined to divisor-stationary corrections.  Let `W=(w_(a,b))` be any
Hermitian kernel supported on coprime pairs of integers greater than one, with some
`w_(a,b) != 0`.  Its diagonal is zero because `gcd(a,a)>1`.  If

```text
W + diag(d_1,d_2,...)
```

is positive semidefinite, every nonzero `2 x 2` coprime block forces

```text
d_a>=0, d_b>=0, d_a d_b >= |w_(a,b)|^2,                    (V19)
```

so in particular some `d_n>0` with `n>1`.  If the correction has a finite critical Dirichlet
symbol

```text
D(u)=sum_(n>=1)d_n n^(-u),                                  (V20)
```

then at a multiplicity-`m` zero its Hermitian mixed-jet contribution is

```text
(partial_s^m partial_t^m D(s+t))_(t=conj(s))
 =D^(2m)(2 Re(s))
 =sum_(n>=1)d_n (log n)^(2m)n^(-2 Re(s)) > 0.              (V21)
```

Thus any positive diagonal completion capable of repairing even one nonzero coprime edge adds a
strictly positive critical-line jet and destroys `(V9)`.  The two requirements—positive
completion and exact critical-line vanishing—are incompatible before any asymptotic estimate is
attempted.

## Hostile verdict

`REDISCOVERED / BRIDGE`, not candidate new scientific knowledge.

1. Visible-lattice decomposition and `(V6)` are classical Möbius inversion.
2. GCD-matrix incidence factorizations, inertia, and positivity criteria are established parent
   theory.
3. The zero-jet, spectral-signature, and Dirichlet-character formulas are short consequences of those parents plus
   zero multiplicity.  Exact searches found no matching packaged statement, but packaging does
   not overcome routine derivability.
4. `(V9)` is a zero-location certificate, not a source theorem.  It measures orientation only
   after a zero is supplied.
5. Positivity cannot be added inside this representation: `(V15)`, `(V17)`, and `(V21)` are exact
   obstructions, not missing estimates.

## No-go closure

- **Exact killing theorem/mechanism:** Mellin zero modes lie in the radical of visible
  convolution; differentiating lifts the radical only into the indefinite coprimality form.
  Coprimality inertia is exactly Möbius sign inertia and has unbounded negative index.
- **Strongest positive survivor:** the universal zero-jet orientation law `(V7)`--`(V12)`, the
  exact spectral signature law `(V15a)`--`(V15c)`, and the
  exact positive-kernel/completion impossibility theorems `(V16)`--`(V21)`.
- **New insight:** a successful Möbius--Laplace source cannot be a positive GCD-stationary form,
  a finite-negative-index correction of coprimality, or a primitive-dilation norm.  It must use a
  source-defined nonstationary cancellation before positivity, or retain an infinite Krein
  cancellation with an independent sign-selection theorem.
- **Status:** dependency-closed paper proof.  Parent mechanisms are known, so no novelty claim.
  Full analytic Lean formalization is deferred; a matrix-only wrapper would not formalize the
  claimed zeta/Dirichlet zero-jet theorem.

## Literature boundary

- Geoffrey B. Campbell, *Visible Point Vector Partition Identities for Hyperpyramid Lattices*,
  arXiv:2309.16094, records the general visible-lattice zeta quotient
  `product_j zeta(s_j)/zeta(sum_j s_j)`.
- Pentti Haukkanen and Jori K. Merikoski, *Inertia, positive definiteness and l_p norm of GCD and
  LCM matrices and their unitary analogs*, arXiv:1707.09473, develops incidence factorizations,
  inertia, and positivity through Sylvester congruence.
- The local Dirichlet `L`-function continuation, Euler product, and functional equation are
  standard; no claim of novelty is attached to `(V10)`--`(V12)`.

## Gates

- [x] internal Möbius--Laplace and heat-finite-part corpus audited
- [x] visible-lattice and GCD-matrix parent literature audited
- [x] visible-addition law paper-proved
- [x] zero-jet orientation law paper-proved, including multiplicity and complex characters
- [x] finite inertia and positive-kernel no-go paper-proved
- [x] exact coprimality spectral flow identified with the Mertens function
- [x] positive diagonal completion proved to destroy the critical zero jet
- [ ] source-defined nonstationary sign selector
- [ ] half-power Möbius--Laplace control
- [ ] RH

## Log

- 2026-07-22 — visible-addition conjecture derived, reduced to classical visible-lattice
  inversion, and rejected as a source because zeta-zero modes lie in its radical.
- 2026-07-22 — strongest survivor extracted: exact zero-jet orientation, Möbius inertia, and
  positive divisor-kernel impossibility.
