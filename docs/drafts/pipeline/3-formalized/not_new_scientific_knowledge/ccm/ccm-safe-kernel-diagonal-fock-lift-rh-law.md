# The CCM half-unit covariance is a canonical diagonal Fock lift

- **ID:** `ccm-safe-kernel-diagonal-fock-lift-rh-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [RH-EQUIVALENT TARGET]`
- **Parents:** Schur products of positive kernels, RKHS feature maps, Douglas factorization, and
  `ccm-infinitesimal-half-unit-cauchy-seam-law.md`

## Statement

For `x,y>1/2`, put

```text
A(x,y)=J_safe(x,y)=[Q(x)+Q(y)]/(x+y-1),                  (1)
C(x,y)=1/(x+y),                                         (2)
D(x,y)=A(x,y)C(x,y).                                    (3)
```

Both `A` and `C` are positive semidefinite, hence so is their Schur product `D`. Moreover,

```text
J_RH=A-D.                                                (4)
```

Let `H_A` be the reproducing-kernel Hilbert space of `A`, with kernel vectors `k_x`, and realize
`C` on `L2(R_+)` by

```text
c_x(t)=exp(-xt),
<c_x,c_y>=1/(x+y).                                      (5)
```

On the algebraic kernel span define the canonical diagonal Fock lift

```text
T_0 k_x=k_x tensor c_x.                                  (6)
```

Then

```text
RH
 iff T_0 extends to a contraction
     H_A -> H_A tensor L2(R_+).                           (7)
```

More precisely, the negative index of the defect form

```text
I-T_0^*T_0                                               (8)
```

on its kernel core is exactly the total right-half off-line zero multiplicity.

## Proof

The safe kernel `A` is positive by the positive-real theorem, while `(2)` is the classical Cauchy
kernel with the feature realization `(5)`. The Schur product theorem proves positivity of `D`.
The denominator calculation gives

```text
A(x,y)-J_RH(x,y)
 =[Q(x)+Q(y)]
   [1/(x+y-1)-1/(x+y)]
 =A(x,y)/(x+y)=D(x,y),                                  (9)
```

which is `(4)`.

For a finite linear combination `v=sum_j alpha_j k_(x_j)`, equations `(3)`, `(5)`, and `(6)` give

```text
||v||_(H_A)^2
 =sum_(j,k)conj(alpha_j)alpha_k A(x_j,x_k),              (10)

||T_0v||^2
 =sum_(j,k)conj(alpha_j)alpha_k D(x_j,x_k).              (11)
```

Thus

```text
||v||^2-||T_0v||^2
 =sum_(j,k)conj(alpha_j)alpha_k J_RH(x_j,x_k).            (12)
```

The map in `(6)` is understood on the quotient by any zero-norm relation in the kernel span. If
`J_RH>=0`, equation `(12)` shows that every such relation also has zero image, so `T_0` is
well-defined and contractive and extends uniquely by density. Conversely, a contractive extension
makes `(12)` nonnegative for every finite coefficient vector, hence `J_RH>=0`. The infinitesimal
Euler-ray index theorem says

```text
J_RH>=0 iff RH,                                          (13)
```

proving `(7)`.

Without assuming positivity, `(12)` identifies the finite negative squares of `J_RH` with the
expanding directions of the graph relation `(6)`. Its negative index is the right-half off-line
zero count, proving `(8)`. `QED`

## Positive CCM carrier law

The missing half-unit is a specific grade-two feature:

```text
safe source feature k_x
  -> diagonal tensor feature k_x tensor exp(-x t)
  -> leakage Gram D
  -> defect Gram A-D=J_RH.                               (14)
```

A successful proof is therefore forced to construct the diagonal lift `(6)` from the completed
Euler--Gamma source and prove it is contractive. This is more precise than asking for unspecified
operator-valued covariance.

The lift also explains why scalar Schur transport fails. The leakage is not a scalar multiple of
`k_x`; it adds one genuine Cauchy/Laplace coordinate. The target has exactly the two-grade form

```text
degree one: H_A,
degree two: H_A tensor L2(R_+).                           (15)
```

## Formal source-side topology law

The prime-log carrier fixes the topology in which `(6)` can be approached.  In prime coordinates,
positive transport by `b>0` produces the Cauchy sections

```text
v_(b,z)(p)=p^(b-1/2)/(log p-z).                           (15a)
```

Lean proves in `PrimeLogHerglotz.lean` that for every fixed finite cancellation order `m`,

```text
sum_p p^(2b-1)/(1+(log p)^2)^m=infinity.                 (15b)
```

The strengthened theorem in `PrimeLogCauchySeamRank.lean` proves, for distinct upper-half-plane
nodes, the exact equivalence

```text
sum_p p^(2b-1)
  |sum_j c_j/(z_j-log p)|^2 < infinity
iff c_j=0 for every j.                                   (15c)
```

Consequently, a source construction of `T_0` cannot be a strong graph limit in one fixed
uncoupled prime `ell^2` space of columns having uniformly bounded rational Cauchy-cancellation
order.  The approximating system is forced to carry at least one of the following positive
resources:

```text
cofinal cancellation/renormalization rank;
Gamma-damped channel covariance formed before completion;
a relative or indefinite graph norm before scalar trace;
or an equivalent infinite-dimensional marked source--divisor state.  (15d)
```

This obligation is sharp as a category statement.  The Gamma-damped stationary covariance already
crosses the critical half-weight because its diagonal satisfies

```text
phi(2 log p) asymp 1/p,                                  (15e)
```

while retaining nonzero cross-prime entries.  Thus the formal transport wall does not kill the
diagonal Fock route.  It forces the finite CCM lifts to remain channel-resolved through the
prime--Gamma sewing and only then converge in a relative graph topology to `(6)`.

The universal Laplace leg in `(6)` has now also been identified with the existing finite-aperture
source carrier.  The exact identity

```text
1/(x+y)
 =-zeta'(1+x+y)/zeta(1+x+y)-1/(x+y+1)
  +integral exp(-(x+y+1/2)h)dR(h)                         (15f)
```

decomposes it into a positive resolved prime-power Gram, a positive shifted polar Gram with the
opposite colligation sign, and the signed critical Mellin-defect channel.  Tensoring `(15f)` with
`A` turns contractivity of `T_0` into an exact four-channel source passivity inequality.  See
`ccm-diagonal-fock-polar-prime-mellin-incidence-law.md`.

## Residue-bundle source selection

The Laplace vector in `(6)` is already selected by the canonical closed completed-logarithmic
source graph.  For an upper-half-plane pole `w`, its anti-causal rank-one Hardy coordinate is

```text
u |-> 1/(u-w).                                             (15g)
```

Under the reflected Paley--Wiener unitary, the specialization `w=i x` is, up to the fixed Fourier
normalization,

```text
t |-> exp(-xt),       t>0.                                (15h)
```

Therefore `T_0` is the diagonal residue bundle

```text
safe source feature k_x
  -> k_x tensor (anti-causal residue coordinate at w=i x). (15i)
```

This also identifies the role of the formal prime-log theorem exactly.  Sampling `(15g)` on the
prime-log support gives `(log p-i x)^(-1)`; positive exponential transport produces the Cauchy
sections whose finite-order nonsummability and finite-packet independence are proved in
`PrimeLogHerglotz.lean` and `PrimeLogCauchySeamRank.lean`.  Gamma sewing supplies the missing domain,
while the closed Xi graph supplies the orbit-sensitive residue coordinate.

The remaining source-selection theorem is consequently precise: prove that the distinguished
Sonin compression of the closed Xi graph is contractive on the complete diagonal residue bundle
`(15i)`, with cofinal defect index preserved.  This is neither an arbitrary RKHS factorization nor
an external choice of damping.

For an off-line zero `lambda=a+i gamma`, the corresponding causal and anti-causal resolvents
diagonalize into a positive `cosh(a t)` channel and a negative `sinh(a t)` channel.  The latter is
exactly one expanding direction of `I-T_0^*T_0`; its decaying anti-causal half has the inverse-depth
energy measured by the four-unit boundary relative trace.  Hence Fock defect index and boundary
trace slope are the quantized and metric readings of one bilateral residue coordinate.  See
`ccm-quartet-resolvent-bilateral-polarization-law.md`.

## Relation to the finite local-ratio Fock carrier

`ccm-higher-subset-covariance-fock-lift.md` constructs, for every finite place set, the positive
subset-graded carrier and its compact Gauss-paired Hardy realization. The present theorem identifies
the exact cofinal degree-two target that those finite carriers must realize:

```text
weighted finite degree-two subset columns
  -> channel-resolved prime--Gamma sewing
  -> relative graph convergence to T_0
  + uniform contractivity
  -> J_RH>=0
  -> RH.                                                  (16)
```

The algebraic positive lift is already complete. The load-bearing theorem is now a quantitative
Gauss/Sonin convergence theorem identifying its limit with `(6)` and preserving the contraction
bound.

## Relation to the square Evans line

The defect index in `(8)` equals

```text
ind_-(I-T_0^*T_0)
 =ind_-(J_RH)
 =sup_(a>0)kappa(a).                                     (17)
```

Hence the diagonal Fock lift and the square restricted-Weil Evans line carry the same integer
charge. A source construction of `(6)` which preserves the defect index supplies the missing
prime-side-to-Evans incidence transform.

## Scope and classification

Equations `(3)`--`(12)` are standard RKHS tensor-product and Douglas-factorization calculus. The
result specifies the correct CCM carrier but is a bridge rather than new scientific knowledge.

The formal tree has finite Gram and tensor-product primitives but no Xi safe kernel, analytic RKHS,
or cofinal Gauss/Sonin limit. Formalizing the abstract implication alone would be a wrapper, so no
Lean file is added.

**Superseded, 2026-08-15.**  A Lean file *is* added, and it is not a wrapper: the Cauchy factor's
positivity is proved from its exponential Gram realization rather than assumed, so the diagonal
tensor feature is constructed rather than posited.

## Lean status

Module `formal/GaloisForLFunctions/RHTower/CCMDiagonalFockLift.lean` (wired, axiom-clean, 10
declarations), over `RHTower/CCMHalfUnitCauchySeam.lean` from the parent card.

- `cauchyKernel`, `kernelMatrix` — equation `(2)` and the Gram matrix of a kernel at a finite node
  family.
- `integrableOn_expPair`, **`cauchy_quadratic_form`** — equation `(5)` at the level of quadratic
  forms:

  ```text
  sum_(i,j) alpha_i alpha_j /(x_i + x_j)
    = int_0^infinity (sum_i alpha_i exp(-x_i t))^2 dt .
  ```

- **`posSemidef_cauchyMatrix`** — hence the Cauchy kernel is positive semidefinite *because it is a
  Gram matrix of the exponential feature `c_x(t) = exp(-x t)`*, which is exactly the realization
  `(5)` the diagonal Fock lift uses.
- **`fockMatrix_eq_hadamard`** — equation `(3)`: `D = A o C` is a Schur product.
- **`posSemidef_fockMatrix`** — equation `(3)`, positivity: the Schur product theorem applied to the
  safe kernel and the Cauchy kernel.
- **`rhMatrix_eq_sub`** — equation `(4)`: `J_RH = A - D`, exactly.
- **`defect_form_eq`** — equations `(10)`-`(12)`: on every finite kernel core,

  ```text
  alpha* A alpha - alpha* D alpha = alpha* J_RH alpha ,
  ```

  i.e. the defect form `I - T_0^* T_0` *is* the `J_RH` form.  In particular the two forms have the
  same negative index, which is equation `(8)`.
- **`contractive_iff_rhForm_nonneg`** — equation `(7)` at form level: the diagonal Fock lift is
  contractive on a finite kernel core exactly when the RH quadratic form is nonnegative there.

`#print axioms` on all ten declarations returns exactly `[propext, Classical.choice, Quot.sound]`.

Imported, not reproved: positive semidefiniteness of the safe kernel `A` (the de
Branges--Rovnyak positive-real theorem, a hypothesis of `posSemidef_fockMatrix`), the equivalence
`(13)` `J_RH >= 0 iff RH` from the infinitesimal Euler-ray index card, and the analytic RKHS
completion.  The formal prime-log transport wall `(15b)`, `(15c)` is already in the tree, in
`HTGeometry/PrimeLogHerglotz.lean` and `HTGeometry/PrimeLogCauchySeamRank.lean`.

## Gates

- [x] half-unit loss written as a positive Schur-product kernel
- [x] exact diagonal tensor feature constructed
- [x] contractivity proved equivalent to the RH kernel positivity
- [x] expansion index identified with off-line multiplicity
- [x] cofinal target of the finite subset-Fock carriers identified
- [x] diagonal Fock and square Evans charges identified
- [x] formal prime-log transport wall converted into a source-topology obligation
- [x] diagonal Laplace coordinate decomposed into exact polar--prime Mellin source channels
- [x] diagonal Laplace coordinate identified with the closed Xi graph's anti-causal residue bundle
- [x] Fock negative index and boundary trace slope linked on each off-line quartet
- [ ] prove finite Gauss/Sonin degree-two columns converge to `T_0`
- [ ] prove the limiting lift is contractive
- [ ] RH
