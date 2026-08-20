# The shifted-Xi Pick kernel has an exact additive all-prime Loewner generator

- **ID:** `xi-shift-loewner-prime-generator-law`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** logarithmic differentiation, Carathéodory/Pick kernels, and the completed
  Euler logarithmic derivative
- **Statement:** The nonlinear shifted-Xi Pick kernel is the integral of congruences of an additive
  meromorphic Carathéodory-type kernel. In the Euler region its generator splits exactly into a
  finite-degree archimedean term and the complete infinite prime-log phase series. The critical
  generator is an exact additive RH criterion, whereas every positive-shift generator is
  necessarily indefinite; its signed integral, not its pointwise sign, is the viable carrier.

## Shifted quotient and Pick kernel

For `omega>=0`, define

```text
Theta_omega(z)
 =xi(1/2-omega-iz)/xi(1/2+omega-iz),                       (1)

k(z,w)=i/(z-conjugate(w)),                                 (2)

S_omega(z,w)
 =k(z,w)(1-Theta_omega(z)conjugate(Theta_omega(w))).        (3)
```

At `omega=0`, one has

```text
Theta_0=1,
S_0=0.                                                     (4)
```

Put `L=xi'/xi` and

```text
s_-(omega,z)=1/2-omega-iz,
s_+(omega,z)=1/2+omega-iz,

H_omega(z)=L(s_-(omega,z))+L(s_+(omega,z)).                 (5)
```

All identities below are first taken on a common open set avoiding the poles of the displayed
meromorphic functions. On the Euler region used later there are no poles.

## Loewner generator identity

`[PROVED]` One has

```text
partial_omega log Theta_omega(z)=-H_omega(z),               (6)

partial_omega S_omega(z,w)
 =Theta_omega(z)conjugate(Theta_omega(w))
   *C_omega(z,w),                                          (7)

C_omega(z,w)
 =k(z,w)(H_omega(z)+conjugate(H_omega(w))).                 (8)
```

Consequently, whenever the segment `0<=tau<=omega` is pole-free at `z,w`,

```text
S_omega(z,w)
 =integral_0^omega
    Theta_tau(z)conjugate(Theta_tau(w)) C_tau(z,w) d tau.   (9)
```

### Proof

Differentiate the numerator and denominator in `(1)`:

```text
partial_omega log xi(s_-)=-L(s_-),
partial_omega log xi(s_+) = L(s_+).                         (10)
```

Their difference is `(6)`. Hence

```text
partial_omega Theta_omega=-H_omega Theta_omega.             (11)
```

Differentiating `(3)` and using `(11)` gives

```text
partial_omega(1-Theta_omega(z)conjugate(Theta_omega(w)))
 =Theta_omega(z)conjugate(Theta_omega(w))
   (H_omega(z)+conjugate(H_omega(w))),                      (12)
```

which proves `(7)`--`(8)`. Integrating from `(4)` proves `(9)`.

## Finite-matrix positive integration theorem

Fix `omega>0` and nodes `z_1,...,z_N` for which the whole segment is pole-free. Let

```text
C_tau[Z]=(C_tau(z_j,z_k))_(j,k),
D_tau[Z]=diag(Theta_tau(z_1),...,Theta_tau(z_N)).            (13)
```

Then `(9)` is the matrix identity

```text
S_omega[Z]
 =integral_0^omega D_tau[Z] C_tau[Z] D_tau[Z]^* d tau.      (14)
```

Therefore

```text
C_tau[Z]>=0 for every tau in [0,omega]
 -> S_omega[Z]>=0.                                          (15)
```

If `C_tau` is positive on every finite node set throughout the segment, then so is `S_omega`.
This is an exact complete-positivity transfer, not a norm estimate.

Conversely, if `S_tau[Z]>=0` for every sufficiently small positive `tau`, then the closedness of
the finite-dimensional positive cone and `(7)` at `tau=0` give

```text
C_0[Z]>=0.                                                  (16)
```

Thus the infinitesimal correlation carrier at the critical shift is necessary for a positive
shift family.

## Exact Euler--Gamma generator

On `Re s>1`,

```text
L(s)
 =1/s+1/(s-1)-1/2 log pi+1/2 psi(s/2)
  -sum_(n>=2) Lambda(n)n^(-s).                              (17)
```

For

```text
U_omega={z:Im z>1/2+omega},                                (18)
```

both arguments in `(5)` lie in `Re s>1`, and the two prime series converge absolutely. Since

```text
n^(-s_-)+n^(-s_+)
 =2 n^(-1/2)cosh(omega log n)e^(iz log n),                  (19)
```

one obtains the exact source split

```text
H_omega(z)
 =B_omega(z)
  -2 sum_(n>=2) Lambda(n)n^(-1/2)
       cosh(omega log n)e^(iz log n),                       (20)
```

where

```text
B_omega(z)
 =b(s_-(omega,z))+b(s_+(omega,z)),                          (21)

b(s)=1/s+1/(s-1)-1/2 log pi+1/2 psi(s/2).                  (22)
```

Thus `C_omega` is linear in the complete von Mangoldt phase carrier. No individual zero, zero
height, or critical-strip continuation occurs in `(20)`.

For fixed `omega`, convergence in `(20)` is locally uniform on `U_omega`. Indeed a compact subset
has `Im z>=1/2+omega+delta` for some `delta>0`, and the absolute majorant is

```text
sum_n Lambda(n)n^(-1-delta)<infinity.                       (23)
```

## Critical-generator equivalence

At the critical shift,

```text
C_0(z,w)
 =2k(z,w)(L(1/2-iz)+conjugate(L(1/2-iw))).                 (24)
```

Let

```text
U_0={z:Im z>1/2}.                                           (25)
```

Then

```text
RH
 <-> C_0[Z]>=0 for every finite Z subset U_0.               (26)
```

### Proof

Assume RH. The function `M(z)=L(1/2-iz)` is analytic in the upper half-plane. By the
Sondow--Dumitrescu horizontal monotonicity theorem,

```text
Re M(x+iy)
 =partial_sigma log|xi(sigma-ix)| at sigma=1/2+y
 >0                                                        (27)
```

for `y>0`. Thus `2M` is a Carathéodory function on the upper half-plane, and its standard kernel is
exactly `C_0`; hence every finite matrix is positive.

Conversely, suppose the matrices in `(26)` are positive. The Nevanlinna--Pick extension theorem
gives a Carathéodory function on the full upper half-plane agreeing with `2M` on the nonempty open
set `U_0`. Uniqueness of analytic continuation makes that extension equal to the meromorphic
continuation of `2M` wherever the latter is regular. Therefore `M` has no pole in the upper
half-plane. A pole at `z` is exactly a zero of `xi(1/2-iz)` with real part greater than `1/2`.
Hence there is no right-half zero, and the functional equation gives RH.

On `U_0`, formula `(20)` becomes the exact all-prime source coordinate

```text
H_0(z)
 =2b(1/2-iz)
  -2 sum_(n>=2)Lambda(n)n^(-1/2)e^(iz log n).               (28)
```

Thus `(26)` is a complete matrix-positivity theorem stated entirely through the convergent
Euler--Gamma incidence. It is not weaker than RH, but it moves the deciding sign onto the additive
source carrier rather than a zero list or a nonlinear Euler product.

## Positive-shift generator obstruction

The sufficient implication `(15)` cannot be used by proving `C_tau>=0` pointwise throughout a
positive shift interval. In fact:

```text
for every omega>0,
C_omega is not positive on all finite subsets of U_omega.   (29)
```

### Proof

Hardy's theorem supplies a critical-line zero `rho=1/2+i gamma` of `xi`. The first logarithmic
derivative in `(5)` has a nonremovable pole when

```text
s_-(omega,z)=rho,
z=-gamma+i omega.                                          (30)
```

This point lies in the upper half-plane. If `C_omega` were positive on every finite subset of the
open Euler region `U_omega`, Nevanlinna--Pick extension would produce a Carathéodory function on the
full upper half-plane agreeing there with `H_omega`. Analytic continuation would then make the pole
in `(30)` removable, a contradiction. This proves `(29)` unconditionally.

Therefore the endpoint kernel can be positive even though its Loewner derivative is sign-indefinite
at every positive shift. Equation `(14)` is a signed matrix integral with nontrivial cancellation;
positivity is a holonomy of the full shift interval, not positivity of its infinitesimal pieces.

## Relation to the finite-Gamma boundary law

Equations `(20)` and `(26)` realize the structural law requested by the finite-archimedean theorem:

```text
one finite-degree archimedean generator B_0
  + one infinite rationally independent prime-log phase module
  -> one complete matrix-positivity constraint.             (31)
```

The archimedean term is not asked to generate the arithmetic phase space. It supplies the boundary
against which the entire von Mangoldt carrier is tested. The load-bearing theorem must retain the
whole sum before taking the positive cone; finite phase rank, factorwise signs, or pointwise
contractivity cannot establish `(26)`.

## Schur-complement interface

For a fixed finite node set, the critical criterion `(26)` is equivalent to a positive-semidefinite
completion of the
linear prime matrix by the archimedean matrix:

```text
C_(B,0)[Z] >= C_(P,0)[Z].                                  (32)
```

Here the right side denotes the Hermitian matrix obtained from the prime series in `(28)` with
the sign moved across. Neither side is termwise positive in general. A source-built Hilbert-space
factorization

```text
C_(B,0)[Z]-C_(P,0)[Z]=R_Z^*R_Z                             (33)
```

compatible under enlargement of `Z` would prove `(26)`. This is the precise place where a positive
Fock/Toeplitz prime carrier could enter: it must furnish the **full Gram completion `(33)`**, not
only the squared prime weights or the correct Schatten scale.

There is a second viable target: prove positivity directly for the integrated matrices `(14)` at
every positive endpoint. What is ruled out by `(29)` is only termwise Loewner positivity. The
positive-shift proof must retain the signed ordering and cancellation of the complete interval.

## Scientific status

The Loewner identity is elementary differentiation, `(17)` is the classical completed Euler
logarithmic derivative, and `(15)` is integration in the positive matrix cone. The theorem is a
new route coordinate but not new scientific knowledge.

## References

- The classical completed-zeta logarithmic derivative in `Re s>1`.
- `euler-pick-inertia-offline-zero-count.md`.
- `finite-archimedean-gamma-product-boundary-law.md`.

## Lean formalization

Everything above is now formalized unconditionally, in the centred coordinate `W = -i z` (so that
the card's Cauchy factor `i/(z - conj w)` is `1/(W + conj V)` — recorded as
`xiShiftGenKernel_cardCoordinates`).  The missing analytic object was **Nevanlinna--Pick
extension**, which the corpus did not own; it was built for this card.

- `formal/GaloisForLFunctions/HTGeometry/PosSemidefKernelGram.lean` — `IsPSDKernel` and its Gram
  realization (the scalar case of Moore's theorem).
- `formal/GaloisForLFunctions/HTGeometry/SchurNevanlinnaPick.lean` — **Nevanlinna--Pick for the
  Schur class** (`exists_schur_interpolant_of_pickKernel`), by the lurking isometry: the Pick
  identity factors two coefficient maps through an isometry, extended by zero to a contraction.
- `formal/GaloisForLFunctions/HTGeometry/TransferFunction.lean` — the contraction's transfer
  function, with `BoundedCoeffPowerSeries.lean` supplying holomorphy from bounded coefficients.
- `formal/GaloisForLFunctions/HTGeometry/CaratheodoryNevanlinnaPick.lean` — the half-plane form
  (`exists_caratheodory_interpolant`), by the Cayley transform.
- `formal/GaloisForLFunctions/HTGeometry/LogDerivNoZero.lean` — `ne_zero_of_deriv_eq_mul`: a
  holomorphic logarithmic derivative forbids zeros.  This replaces the card's appeal to analytic
  continuation of a meromorphic function.
- `formal/GaloisForLFunctions/HTGeometry/PSDKernelMatrixBridge.lean`,
  `IntegralMatrixPosSemidef.lean` — the finite-Gram/energy bridge and entrywise integration of
  positive semidefinite matrix densities.
- `formal/GaloisForLFunctions/RHTower/XiShiftLoewnerCriticalGenerator.lean` — `xiShiftGen` `(5)`,
  `xiShiftGenKernel` `(8)`, the no-zero transfer, and the two main theorems:
  `riemannHypothesis_iff_isPSDKernel_criticalGenerator` is `(26)` (its forward half comes from the
  imaginary-divisor Bezoutian of the companion card, no Sondow--Dumitrescu needed), and
  `not_isPSDKernel_shiftGenerator` is `(29)`.
- `formal/GaloisForLFunctions/RHTower/XiShiftLoewnerFlow.lean` — `xiShiftTheta` `(1)`,
  `xiShiftPick` `(3)`, `(4)`, the Loewner generator identity `(6)`--`(8)`
  (`hasDerivAt_xiShiftTheta`, `hasDerivAt_xiShiftPick`), the integral representation `(9)`
  (`xiShiftPick_eq_integral`), and the finite-matrix positive integration law `(14)`--`(15)`
  (`posSemidef_xiShiftPickMatrix`).
- `formal/GaloisForLFunctions/RHTower/XiShiftLoewnerEulerSplit.lean` — the exact Euler--Gamma
  split `(17)`--`(20)` (`xiShiftGen_eq_arch_sub_primeSeries`), absolute convergence in the Euler
  region `(23)` (`summable_xiShiftPrimeTerm`), and the Schur-complement interface `(32)`
  (`posSemidef_criticalGenerator_iff_arch_sub_prime`).

Every capstone audits to `[propext, Classical.choice, Quot.sound]`.  What remains open is exactly
what the card says is open: the source-defined factorization `(33)`.

## Gates

- [x] shifted quotient differentiated exactly
- [x] Loewner kernel identity proved
- [x] finite-matrix positive integration theorem proved
- [x] complete all-prime Euler--Gamma generator extracted
- [x] local uniform convergence in the Euler region proved
- [x] critical-generator positivity proved equivalent to RH
- [x] positive-shift generator positivity proved impossible
- [x] critical Gram-completion interface isolated
- [x] Lean formalization of every item above
- [ ] construct the source-defined factorization `(33)`
- [ ] or prove endpoint positivity directly from the signed integral `(14)`
- [ ] deduce RH
