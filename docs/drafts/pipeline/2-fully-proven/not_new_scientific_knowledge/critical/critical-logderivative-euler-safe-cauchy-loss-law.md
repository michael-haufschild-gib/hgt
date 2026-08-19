# The critical logarithmic-derivative RH kernel is an Euler-safe Cauchy-loss contraction

- **ID:** `critical-logderivative-euler-safe-cauchy-loss-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `ccm-safe-kernel-diagonal-fock-lift-rh-law.md` and
  `critical-logderivative-two-channel-weil-resolvent-law.md`
- **Statement:** On every half-plane lying strictly inside absolute Euler convergence, the
  RH-deciding critical logarithmic-derivative kernel is exactly an unconditional positive
  Carathéodory kernel minus its positive Hardy--Cauchy Schur loss.  RH is equivalent to the one
  remaining source-specific kernel domination, equivalently to an explicit finite
  Cauchy--Laplace observability inequality whose density is given by the absolutely convergent
  prime--Gamma logarithmic derivative.

## Goal

Replace the opaque request to prove positivity of the critical logarithmic-derivative kernel by a
static comparison of two kernels that are separately defined in the absolute Euler half-plane.
The unconditional term must have an explicit positive boundary density; the lost term must be a
canonical positive tensor factor; and the comparison must remain strictly stronger than ordinary
positive-realness.

The fixed half-unit, real-ray diagonal-Fock version of this carrier is already proved in
`ccm-safe-kernel-diagonal-fock-lift-rh-law.md`.  The incremental content here is the arbitrary
safe offset `a>1/2`, complex sampling nodes, and the explicit Herglotz boundary-density form of the
same contractivity problem.  This card is therefore a refinement of that bridge, not an independent
RH route.

## Setup

Put

```text
X(w)=xi(1/2+w),
L(w)=X'(w)/X(w).                                          (1)
```

Fix a real number `a>1/2` and write

```text
H_a={w in C : Re(w)>a},
d(w,v)=w+conjugate(v),
N(w,v)=L(w)+conjugate(L(v)).                              (2)
```

Every `w in H_a` corresponds to `s=1/2+w` with `Re(s)>1`.  Thus `X` is zero-free there and the
Euler series for the logarithmic derivative converges absolutely.

Define three kernels on `H_a`:

```text
K_a(w,v)=N(w,v)/(d(w,v)-2a),
C_a(w,v)=2a/d(w,v),
K_0(w,v)=N(w,v)/d(w,v).                                  (3)
```

Here `K_0` is the RH-complete kernel of the parent card.  The subscript zero records that its
denominator is the Cauchy kernel of the critical half-plane `Re(w)>0`, even though it is sampled
only in `H_a`.

## Unconditional Euler-safe positivity

`[PROVED]` Both `K_a` and `C_a` are positive semidefinite kernels on `H_a`, and

```text
C_a(w,w)=a/Re(w)<1.                                      (4)
```

Indeed, the Sondow--Dumitrescu horizontal-monotonicity theorem applied to the zero-free half-plane
`Re(s)>1` gives

```text
Re L(w)=d/dsigma log|xi(1/2+sigma+i Im(w))| at sigma=Re(w)>0.  (5)
```

Thus `L` maps `H_a` to the open right half-plane.  The half-plane Carathéodory theorem says
precisely that the first kernel in `(3)` is positive.  The second has the explicit Gram
representation

```text
C_a(w,v)=integral_(0,infinity)
           2a exp(-w x) exp(-conjugate(v) x) dx,           (6)
```

which proves its positivity and `(4)`.

## Exact Cauchy-loss identity

`[PROVED]` Pointwise on `H_a x H_a`,

```text
K_0=K_a-K_a circle C_a,                                  (7)
```

where `circle` denotes the Schur, or entrywise, product.  Consequently,

```text
RH
  <-> K_0 is positive on H_a
  <-> K_a circle C_a <= K_a.                              (8)
```

### Proof

The algebraic identity is immediate:

```text
K_a(w,v)*(1-C_a(w,v))
 =N(w,v)/(d(w,v)-2a) * (1-2a/d(w,v))
 =N(w,v)/d(w,v)
 =K_0(w,v).                                               (9)
```

The Schur product theorem and the preceding section also give

```text
K_a circle C_a >=0                                       (10)
```

unconditionally.  Hence `(7)` turns positivity of `K_0` into the domination in `(8)`.

The parent complete-detector theorem proves that positivity of `K_0` on an Euler uniqueness
half-plane is equivalent to RH.  For completeness, the same argument works on every `H_a`.
Positivity of the kernel

```text
(L(w)+conjugate(L(v)))/(w+conjugate(v))                   (11)
```

on the nonempty open set `H_a` is the Nevanlinna--Pick condition for the values of `L` to be the
restriction of a positive-real function on `Re(w)>0`.  The extension agrees with the actual
meromorphic `L` on `H_a`; uniqueness of analytic continuation therefore rules out every pole of
`L` in `Re(w)>0`.  Such a pole is a right-half nontrivial Xi zero.  Functional-equation symmetry
then gives RH.  Conversely, RH makes `Re(w)>0` zero-free, so the same Carathéodory theorem gives
positivity of `(11)` and hence its restriction to `H_a`.

This proves `(8)`.

## RKHS contraction form

Let `H(K_a)` and `H(C_a)` be the reproducing-kernel Hilbert spaces of the two unconditional
kernels, with kernel vectors `e_w` and `c_w`.  On the algebraic kernel span consider

```text
Delta_a(e_w)=e_w tensor c_w.                              (12)
```

For every finite node/coefficient system,

```text
||sum_j c_j e_(w_j)||^2
  =sum_(j,k)c_j conjugate(c_k) K_a(w_j,w_k),

||sum_j c_j e_(w_j) tensor c_(w_j)||^2
  =sum_(j,k)c_j conjugate(c_k)
     K_a(w_j,w_k) C_a(w_j,w_k).                           (13)
```

Therefore `(12)` descends to a contraction

```text
Delta_a : H(K_a) -> H(K_a) tensor H(C_a)                 (14)
```

if and only if `K_a circle C_a<=K_a`.  Combining with `(8)` gives the static operator criterion

```text
RH <-> Delta_a is contractive.                            (15)
```

This is a constraint on a canonical diagonal embedding, not a spectral flow or an auxiliary
determinant carrying a prescribed Xi divisor.

## Absolute-Euler boundary realization

On the boundary of `H_a` put

```text
h_a(t)=Re L(a+it).                                        (16)
```

The preceding monotonicity theorem gives `h_a(t)>0` unconditionally.  The logarithmic growth of
`L` kills the possible linear mass at infinity in the half-plane Herglotz representation, while
analyticity across `Re(w)=a` makes the finite boundary measure absolutely continuous.  Hence

```text
K_a(w,v)
 =1/pi * integral_R h_a(t)
    /((w-a-it)(conjugate(v)-a+it)) dt.                    (17)
```

Writing `s=1/2+a+it`, the density is source-defined by

```text
L(a+it)
 =1/s+1/(s-1)-1/2 log(pi)+1/2 psi(s/2)
  -sum_(n>=2) Lambda(n)n^(-s),                            (18)
```

and the series in `(18)` is absolutely convergent because `Re(s)=1/2+a>1`.

Insert `(6)` and `(17)` into the kernel domination.  The common factor `1/pi` cancels, giving the
following exact finite source inequality:

```text
2a * integral_R h_a(t) integral_(0,infinity)
       |sum_j c_j exp(-w_j x)/(w_j-a-it)|^2 dx dt

 <= integral_R h_a(t)
       |sum_j c_j/(w_j-a-it)|^2 dt.                       (19)
```

Thus, for every fixed `a>1/2`,

```text
(19) for every finite node/coefficient system
  -> K_a circle C_a<=K_a
  -> K_0>=0
  -> RH.                                                  (20)
```

Every quantity in `(19)` is formed before choosing a Xi zero and inside absolute Euler
convergence.  No divisor enumeration, real-rootedness, anti-Herglotz continuation sign,
RH-equivalent limiting measure, or theta-current bound occurs in the premise.

## Countable source criterion

Fix any rational `a>1/2`; `a=1` is the simplest choice, with boundary line `Re(s)=3/2`.
Continuity of the kernels and density of `Q(i)` imply that it is enough to test `(19)` for

```text
N in N,
w_1,...,w_N in Q(i) intersect H_a,
c_1,...,c_N in Q(i).                                     (21)
```

Consequently `(19)` is a countable family of finite, absolute-Euler value inequalities.

## The domination is not generic positivity

The pointwise estimate `(4)` does not imply the matrix domination.  This is already false for the
positive-real function

```text
F_a(w)=1/(w-a).                                           (22)
```

Its Carathéodory kernel is

```text
K_a^F(w,v)=1/((w-a)(conjugate(v)-a)).                     (23)
```

For two distinct real nodes `x,y>a`, the matrix of
`K_a^F-K_a^F circle C_a` is a positive diagonal congruence of

```text
S_a(x_i,x_j)=1-2a/(x_i+x_j).                              (24)
```

But

```text
det [[S_a(x,x),S_a(x,y)],
     [S_a(y,x),S_a(y,y)]]
 =-a*(x+y-a)*(x-y)^2/(x*y*(x+y)^2)<0.                    (25)
```

So even an unconditional positive Carathéodory kernel and a strictly subunit Cauchy factor do not
give `(19)`.  The open inequality is genuinely multi-node and must use exact structure of the
prime--Gamma density `h_a`.

## Interfaces with the formal corpus

The current Lean tree already supplies the target-side Cauchy algebra:

- `RHTower/XiWeilResolventSource.lean` proves absolute summability, exact divided differences of
  the Xi relative resolvent, and prime--Gamma formulas for finite Cauchy packets;
- `RHTower/XiWeilOneCauchyGate.lean` proves the existing one-Cauchy diagonal criterion, whose open
  sign is the RH-equivalent continued anti-Herglotz condition;
- `RHTower/XiHurwitzOrientationCauchyClosure.lean` proves that the full orientation vector lies in
  the continued regular-Cauchy source closure.

The new criterion is complementary.  It never enters the continued zero strip: it asks for a
matrix contraction on the line `Re(s)=1/2+a>1`, where the density is unconditionally positive and
the Euler series is absolute.  It therefore does not discharge the existing continued-Cauchy sign
by relabelling it.  The reusable missing formal infrastructure is the half-plane
Carathéodory/Herglotz kernel, its boundary `L^2(h_a dt)` realization, and the diagonal RKHS tensor
map `(12)`.

## Research consequence

The earlier vague source task

```text
construct a positive Gram factorization of K_0
```

can be replaced by the sharper positive task

```text
prove that the absolute-Euler boundary Cauchy family loses no more norm
under the canonical Laplace tensoring Delta_a.             (26)
```

The whole unconditional part of the decomposition is explicit.  The only open theorem is the
source-specific finite inequality `(19)`.  A successful proof would give the short chain

```text
absolute-Euler Cauchy--Laplace observability
  -> critical logarithmic-derivative kernel positivity
  -> RH.                                                   (27)
```

## Scientific status

The exact half-unit subtraction and diagonal-Fock contraction were already isolated in
`ccm-safe-kernel-diagonal-fock-lift-rh-law.md`.  The arbitrary-offset complex-node extension and its
boundary observability formula are a composition of classical Carathéodory, Herglotz,
Schur-product, RKHS, and Nevanlinna--Pick facts.  The card is therefore conservatively classified as
not new scientific knowledge and not a new carrier.  Its value is narrower: it converts the
existing Fock defect into an explicit absolute-Euler boundary inequality while removing divisor
data and nonpositive continued-source terms from the premise.

## References

- Jonathan Sondow and Cristian Dumitrescu, *A monotonicity property of Riemann's xi function and a
  reformulation of the Riemann Hypothesis*, arXiv:1005.1104.
- The classical Herglotz representation and Carathéodory/Nevanlinna--Pick kernel criteria on a
  half-plane.
- `ccm-safe-kernel-diagonal-fock-lift-rh-law.md`.
- `critical-logderivative-two-channel-weil-resolvent-law.md`.
- `xi-shift-loewner-prime-generator-law.md`.

## Lean decision

No Lean file is added.  The exact kernel subtraction is elementary, but wrapping only that identity
would add a theorem facade without certifying the analytic content.  Formalization should begin
only with reusable half-plane positive-kernel and Herglotz/RKHS infrastructure, then connect it to
the existing finite Cauchy-packet source formulas.

No Lean build, lint, numerical experiment, or scratch computation was run in producing this paper
theorem, in accordance with the active instruction.

## Gates

- [x] absolute-Euler positivity of `L` established
- [x] unconditional positive kernels `K_a` and `C_a` identified
- [x] exact critical-kernel loss identity proved
- [x] RKHS contraction criterion proved equivalent to RH
- [x] explicit prime--Gamma boundary density attached
- [x] finite Cauchy--Laplace observability inequality derived
- [x] countable rational test family extracted
- [x] generic positive-real shortcut ruled out by a two-node theorem
- [ ] prove `(19)` from exact relations of the canonical density `h_a`
- [ ] deduce RH
