# Adelic high-shell prime-dilation purity-or-escape law

- **ID:** `adelic-high-shell-prime-dilation-purity-or-escape`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / `[ZERO-NORMAL PURITY-OR-ESCAPE]`
- **Scientific status:** `[PROVED HERE] [REPORTER/ESCAPE CLASSIFIER, NOT SOURCE CONNECTOR]`
  `[EXTERNAL NOVELTY UNVERIFIED] [COFINAL EXTENDED-TATE DOMAIN PROVED] [NOT RH]`
- **Parents:**
  - `adelic-mfree-shell-fourier-rank-one-fracture.md`;
  - `../../../3-formalized/high-exponent-shell-zero-free-common-divisor-law.md`;
  - `high-shell-critical-hardy-conormal-uniformization.md`;
  - `../2-fully-proven/deninger-unitary-flow-riesz-eigenfunctional-purity.md`;
  - `../../../3-formalized/new_scientific_knowledge/prime-residue-valuation-interaction-superselection-law.md`.
- **Statement:** Bare Fourier reflection is rank one on every finite-adele source supported in
  `Zhat`, even after arbitrary prime marking. Rational prime dilation is the first canonical
  operation that escapes this collapse. Its self-adjoint functional-equation symmetrization has
  an exact tridiagonal action on the high exponent shells and a nonzero transverse compression.
  At a Xi zero, the first nonzero completed Tate normal is a transpose eigenfunctional for every
  prime character `p^rho+p^(1-rho)`. If this normal is bounded after closing the
  shell source under any one normalized prime dilation, then `Re(rho)=1/2`. More sharply, at an
  off-line point its algebraic kernel is dense, so the corresponding conormal fibre dies in the
  maximal Hausdorff Hilbert quotient. However the shell Tate orbit is already Xi-divisible:
  its normal is a scalar multiple of generic evaluation after division by Xi. Thus the orbit does
  not itself explain why a zero should survive as a positive source state. It classifies the exact
  topological fate any genuine source-divisor attachment must have.

## 1. Why prime marking does not repair bare Fourier reflection

Let

```text
H = Zhat = product_p Z_p
```

inside the finite adeles, with normalized additive Haar measure, and choose the self-dual
character for which `H` is its own annihilator. Let `F` be additive Fourier transform and `P_H`
the orthogonal projection onto functions supported in `H`.

### Theorem A: universal compact-open rank-one compression

For every `f,g in L2(A_f)` supported in `H`,

```text
<f,Fg> = conjugate(integral_H f) * integral_H g.          (1)
```

Equivalently,

```text
P_H F P_H = |1_H><1_H|.                                  (2)
```

In particular every pair of zero-mean vectors supported in `H` has zero Fourier cross-pairing.
This remains true after arbitrary valuation-depth, prime-residue, unique-maximal-prime, or
finite-interaction marking.

### Proof

For `x,y in H`, the standard additive character satisfies `psi(xy)=1`. Hence, for `x in H`,

```text
F g(x)=integral_H g(y) psi(xy) dy=integral_H g(y)dy.
```

Pairing with `f` proves `(1)` and `(2)`.

This strictly strengthens the shell-specific rank-one theorem in the parent card. The collapse
does not come from forgetting the prime that realizes the maximal valuation. It is the universal
self-annihilating compact-open compression law.

## 2. High-shell source

For `m>=2`, let

```text
E_m = {x in H : v_q(x_q)<m for every prime q},
A_m = E_(m+1) \ E_m,
a_m = 1_(A_m),
w_m = mu(A_m)=1/zeta(m+1)-1/zeta(m)>0.                   (3)
```

Thus `A_m` is the set on which the largest finite-prime valuation is exactly `m`. The vectors
`a_m` are orthogonal and `||a_m||^2=w_m`.

With the fixed self-dual real Gaussian, the completed Tate transform of `a_m` is

```text
Xi_m(s)=Xi(s) H_m(s),
H_m(s)=1/zeta((m+1)s)-1/zeta(ms).                        (4)
```

For `m>=12`, `H_m` is holomorphic and zero-free on `Re(s)>1/2`.

## 3. Rational prime dilation

For a rational prime `p`, its finite idelic norm is `|p|_f=p^-1`. Define the unitary additive
dilation

```text
(U_p f)(x)=p^(-1/2) f(px).                               (5)
```

Its adjoint is

```text
(U_p^* f)(x)=p^(1/2) f(x/p).                             (6)
```

and the functional-equation-symmetric prime operator is

```text
J_p=sqrt(p)(U_p+U_p^*).                                  (7)
```

`J_p` is bounded and self-adjoint.

### Theorem B: exact completed Tate covariance

For every test vector for which the Tate integral is initially defined,

```text
Xi_(U_p f)(s)=p^(s-1/2) Xi_f(s),
Xi_(U_p^* f)(s)=p^(1/2-s) Xi_f(s),
Xi_(J_p f)(s)=(p^s+p^(1-s)) Xi_f(s).                    (8)
```

### Proof

Multiplicative Haar measure is invariant. In the first integral use `y=px`; then
`|x|_f=p|y|_f`. In the second use `y=x/p`; then `|x|_f=p^-1|y|_f`. The real Gaussian and the
entire completion factor are unchanged because only the finite component is dilated. Equations
`(5)`--`(7)` give `(8)`.

The character

```text
lambda_p(s)=p^s+p^(1-s)                                 (9)
```

is invariant under `s -> 1-s` and is real on the critical line.

### Theorem B0: cofinal extended-Tate domain

The change-of-variables calculation in `(8)` is unconditional on any common Tate domain on which
the displayed integrals or their meromorphic continuations are defined.  The shell indicators
`a_m` are `L2` compact-open limits, not ordinary finite restricted-tensor
Bruhat--Schwartz functions: infinitely many local factors differ from the standard vector.
Consequently `(4)` and `(8)` cannot be connected by silently treating `a_m` as a classical test
function.  Additive `L2` Haar and multiplicative Tate Haar are different measures; continuity for
one does not imply continuity for the other.

Fix a prime `p` and `M>=2`.  On the algebraic finite-adele orbit

```text
D_(M,p)=span{Q(J_p)a_m : Q in C[X], m>=M},               (9a)
```

there is nevertheless a well-defined meromorphic completed-Tate map

```text
T_p:D_(M,p)->Mer(C)
T_p(Q(J_p)a_m)(s)=Q(lambda_p(s)) Xi(s)H_m(s).            (9b)
```

It agrees on `Re(s)>1` with the cofinal limit of ordinary Tate integrals of
Bruhat--Schwartz approximants, and

```text
T_p(J_p f)=lambda_p T_p(f).                              (9c)
```

#### Proof

For a finite prime set `P`, put

```text
R_(m,P)(s)=product_(q in P)(1-q^(-ms)),
H_(m,P)=R_(m+1,P)-R_(m,P).
```

The finite-packet shell `a_(m,P)` is Bruhat--Schwartz and its completed Tate integral is

```text
Xi(s)H_(m,P)(s).
```

On `Re(s)>1`, absolute Euler-product convergence gives

```text
H_(m,P)->H_m
```

locally normally as `P` exhausts the primes.  Every finite word in `J_p` remains
Bruhat--Schwartz at finite `P`; classical Tate change of variables multiplies its integral by the
corresponding word in `lambda_p`.  This proves existence, `(9b)`, and `(9c)` on the convergence
half-plane, and the displayed formula supplies meromorphic continuation.

It remains to show that `(9b)` descends through equality in additive `L2`.  Every finite
combination in `(9a)` is constant on the valuation cells

```text
{v_p=r, max_(q!=p)v_q=k}
```

that meet its support.  For finite `r` and every relevant `k>=2`, these cells have strictly
positive additive Haar mass: the `p`-coordinate annulus has positive mass and the remaining
maximum has mass

```text
product_(q!=p)(1-q^(-(k+1)))
 -product_(q!=p)(1-q^(-k))>0.
```

Thus an `L2`-zero orbit combination vanishes on every finite valuation cell, hence on its
restriction to the finite ideles.  Absolute convergence on `Re(s)>1` then makes its cofinal Tate
integral zero.  The identity theorem makes the meromorphic continuation zero.  Therefore `(9b)`
is independent of the chosen orbit expression and is a genuine map on `D_(M,p)`.

This proof uses multiplicative Tate integration only on finite Bruhat stages and in its absolutely
convergent half-plane.  It does not assert that Tate evaluation is continuous for the ambient
additive `L2` norm; Theorem F identifies precisely when such extra continuity would have
zero-location content.

## 4. Exact shell Jacobi incidence

For `m>=2`, define the marked transition mass

```text
c_(m,p)
 =mu{x in H : max_q v_q(x_q)=m and v_p(x_p)=m}
 =(p-1)/(zeta(m+1)(p^(m+1)-1)) > 0.                     (10)
```

The event in `(10)` permits ties: `p` is a maximal prime, not necessarily the unique maximal
prime.

### Theorem C: tridiagonal shell compression

For `m,k>=2`,

```text
<a_m,J_p a_k>
 =
  c_(m,p)             if k=m+1,
  2(w_m-c_(m,p))      if k=m,
  c_(m-1,p)           if k=m-1,
  0                    if |m-k|>1.                       (11)
```

Consequently

```text
<a_m,(J_p-2I)a_k>
 =
  c_(m,p)             if k=m+1,
  -2c_(m,p)           if k=m,
  c_(m-1,p)           if k=m-1,
  0                    if |m-k|>1.                       (12)
```

### Proof

On `H`, multiplication by `p` increases only `v_p` by one. If `x in A_m`, then `px` has
maximal valuation `m+1` exactly when `v_p(x_p)=m`; otherwise its maximal valuation remains `m`.
The transition event therefore has measure

```text
(p^-m-p^(-(m+1))) product_(q!=p)(1-q^(-(m+1)))
 =1/zeta(m+1) * (p^-m-p^(-(m+1)))/(1-p^(-(m+1)))
 =(p-1)/(zeta(m+1)(p^(m+1)-1)).
```

The factor `p^-1/2` in `U_p` is cancelled by `sqrt(p)` in `J_p`. The adjoint supplies the
reverse transition. No single valuation change can move the maximum by more than one. This proves
`(11)`; subtracting `2I` gives `(12)`.

### Corollary: the first transverse test is passed

Let `S_M` be the closed shell span generated by `a_m`, `m>=M`, and let the pole vector have
normalized coordinates

```text
r_M=(sqrt(w_m))_(m>=M).                                  (13)
```

Then

```text
P_(r_M perp) P_(S_M)(J_p-2I)P_(S_M) P_(r_M perp) != 0.  (14)
```

Indeed,

```text
f_m=a_m/w_m-a_(m+1)/w_(m+1)                             (15)
```

has zero Haar integral and hence lies in the transverse hyperplane. Equations `(10)` and `(12)`
give

```text
<f_m,(J_p-2I)f_m>
 =-2c_(m,p)/w_m^2
  -2c_(m,p)/(w_m w_(m+1))
  -2c_(m+1,p)/w_(m+1)^2 <0.                             (16)
```

Thus rational dilation creates genuine transverse shell incidence. This is exactly what bare
Fourier transform cannot do.

## 5. Strict-right Xi-zero normal as a prime-dilation eigenfunctional

Let `rho` be a nontrivial Xi zero with `Re(rho)>1/2`, of order `d>=1`. By the functional
equation, excluding such zeros is sufficient for RH. Fix one prime `p`, and let `D_(M,p)` be the
algebraic span of the `J_p` orbits of `a_m`, `m>=M`. For `f in D_(M,p)`, define the first nonzero
completed Tate normal

```text
N_rho(f)=1/d! * (d/ds)^d Xi_f(s)|_(s=rho).               (17)
```

Every element of `D_(M,p)` is obtained from a shell by prime dilations. Equation `(8)` therefore
shows that its completed Tate transform remains divisible by `Xi`.

### Theorem D: exact transpose character

For the fixed prime `p` and every `f in D_(M,p)`,

```text
N_rho(J_p f)=lambda_p(rho) N_rho(f),                    (18)
lambda_p(rho)=p^rho+p^(1-rho).                          (19)
```

Moreover `N_rho` is nonzero. In fact, for every `m>=max(M,12)`,

```text
N_rho(a_m)=Xi^(d)(rho)/d! * H_m(rho) !=0.               (20)
```

### Proof

Differentiate `(8)` `d` times at `rho`. Every term in Leibniz's rule in which fewer than `d`
derivatives hit `Xi_f` vanishes because `Xi_f` has order at least `d` there. The surviving term
is `(18)`. Equation `(20)` follows from `(4)`, the definition of `d`, and zero-freeness of `H_m`
in the strict right half-plane. The reflected left-half statement follows by the functional
equation.

## 6. One-prime contractive selector

### Theorem E

Normalize

```text
K_p=J_p/(2 sqrt(p))=(U_p+U_p^*)/2.                       (21)
```

Then `K_p` is a self-adjoint contraction and its Tate character is

```text
kappa_p(s)=lambda_p(s)/(2 sqrt(p))
          =cosh((s-1/2) log p).                          (22)
```

If `kappa_p(s)` belongs to the spectrum of `K_p`, or is the character of a nonzero bounded
transpose eigenfunctional of `K_p`, then

```text
Re(s)=1/2.                                               (23)
```

### Proof

Write `s=1/2+h+it`. Since `K_p` is a self-adjoint contraction, every eigenvalue is real and lies
in `[-1,1]`. But

```text
Im(kappa_p(s))=sinh(h log p) sin(t log p).               (24)
```

If `h!=0` and `(24)` is nonzero, `kappa_p(s)` is not real. If `(24)` vanishes, then
`sin(t log p)=0` and

```text
|kappa_p(s)|=cosh(|h| log p)>1.                          (24a)
```

again impossible. Hence `h=0`. This is strictly stronger than the earlier two-prime reality
argument: the norm bound of one canonical contraction removes the accidental-real resonances.

### Theorem E0: ambient finite-adelic dilation has no point spectrum

The critical-line condition in Theorem E is only necessary. It is not sufficient for a bounded
normal in the ordinary finite-adelic `L2` space.

Up to a null set, decompose the `p`-adic coordinate as

```text
Q_p^x = disjointUnion_(r in Z) p^r Z_p^x.
```

If

```text
g_r(u)=p^(-r/2) f(p^r u),     u in Z_p^x,
```

then additive Haar scaling gives a unitary identification

```text
L2(Q_p) =
  l2(Z) tensor L2(Z_p^x),
```

under which

```text
U_p:(g_r)_r |-> (g_(r+1))_r.                             (24b)
```

The remaining finite-adele coordinates contribute only a multiplicity tensor factor. Thus `U_p`
is a bilateral shift of constant multiplicity. It has purely absolutely continuous circle
spectrum and no eigenvectors; correspondingly

```text
K_p=(U_p+U_p^*)/2
```

is multiplication by `cos(theta)` after Fourier transform in `r`, has purely absolutely
continuous spectrum `[-1,1]`, and has no eigenvectors.

Consequently no nonzero transpose eigenfunctional is bounded in the ambient finite-adelic `L2`
norm, even when its parameter lies on the critical line. Any RH-capable positive realization must
be a singular quotient, boundary extension, or rigged source module which creates divisor point
fibres; it cannot be the ordinary `L2` closure of the adelic shell orbit.

## 7. Purity-or-escape theorem

### Theorem F

Let `rho` be a strict-right nontrivial Xi zero and fix any prime `p`. Suppose the nonzero
functional `N_rho` from `(17)` is bounded
for the ambient `L2(A_f)` norm on `D_(M,p)`, or more generally for a source-defined positive Hilbert
norm satisfying:

1. `D_(M,p)` has a Hilbert completion `K`;
2. `K_p` extends to a self-adjoint contraction on `K`;
3. `N_rho` extends to a nonzero bounded functional on `K`.

Then

```text
Re(rho)=1/2.                                             (25)
```

Equivalently, for every strict-right Xi zero, the one-prime covariance functional in `(18)` is
unbounded on the corresponding invariant positive completion. The
functional equation gives the reflected statement for strict-left zeros.

### Proof

By Riesz representation, write `N_rho(f)=<y_rho,f>` with `y_rho!=0`. Equation `(18)` and
self-adjointness make `y_rho` an eigenvector of `K_p` with eigenvalue
`kappa_p(rho)` (up to the harmless conjugation determined by the inner-product convention).
Theorem E gives `(25)`.

## 8. Relation to the high-shell Hardy norm

The parent high-shell conormal theorem proves that, for `Re(rho)>1/2`, the coordinate functional

```text
(c_m) -> sum_(m>=M)c_m H_m(rho)                          (26)
```

is bounded in the residue-weighted aggregate shell norm. Thus a hypothetical strict-right zero
does not escape at the unmarked shell level.

Theorem F locates the mandatory escape more sharply:

```text
aggregate high-shell conormal bounded
 + close under one normalized prime dilation K_p
 + retain a self-adjoint contractive Hilbert action
 -> critical line.                                      (27)
```

Therefore an off-line zero must make the normal unbounded in the prime-marked leakage created
when `K_p` leaves the aggregate shell span. The failure is neither in the common zeta divisor
nor in the high-shell residue weights. It is exactly in extending the normal across the
prime-dilation joining.

This is consistent with the corpus's strict prime valuation--interaction creation tower:
prime-local fusion and dilation produce new relatively hypertranscendental marked layers outside
every finite aggregate prefix. The new theorem identifies the analytic role of those layers:
they are the only place where an off-line zero can evade self-adjoint spectral purity.

## 9. RH impact and exact open theorem

### Xi-divisible blindness

Define the divided Tate map on the algebraic orbit by

```text
G_p(f)(s)=T_p(f)(s)/Xi(s).
```

Equations `(9b)` and `(17)` give, at a zero `rho` of order `d`,

```text
N_rho(f)=Xi^(d)(rho)/d! * G_p(f)(rho).                  (28)
```

The right side is ordinary evaluation of `G_p(f)` multiplied by a nonzero scalar. The evaluator
`G_p(f)(s)` exists at every regular complex point `s`, whether or not `Xi(s)=0`, and obeys the same
prime covariance. Hence zerohood does no work in Theorem D: it only reinterprets a generic
evaluator as the first derivative normal of an Xi-divisible transform.

The zero-sensitive object is instead the principal conormal module

```text
I/I^2,                  I=(Xi),                          (29)
```

whose fibre exists only on the Xi divisor. Prime dilation preserves `I` and acts on the fibre at
`rho` by `kappa_p(rho)`. This is the natural torsion-seam replacement required by the corpus's
sigma-divisor multiplicative-kill theorem and theta-convolution Hilbert--analytic defect
trilemma. It is not supplied by merely dividing every shell transform by Xi.

### Off-line Hausdorff-collapse theorem

Let `D` be a dense invariant subspace of a Hilbert space, let `K` be a self-adjoint contraction,
and let `ell:D->C` be a nonzero algebraic functional satisfying

```text
ell(Kf)=kappa ell(f).
```

If `kappa` is outside `[-1,1]`, then

```text
closure(ker ell)=H.                                     (30)
```

Indeed `kappa-K` has a bounded inverse. For `g in D`, approximate
`(kappa-K)^(-1)g` by `d_n in D`. Then

```text
h_n=(kappa-K)d_n -> g,
ell(h_n)=0.
```

Thus `ker ell` is dense. For `kappa=kappa_p(rho)`, Theorem E shows that every off-line `rho` has
`kappa` outside `[-1,1]`. Therefore its algebraic Xi conormal fibre has zero maximal Hausdorff
Hilbert quotient in every source completion retaining the self-adjoint prime contraction.
This strengthens “the normal is unbounded”: the off-line fibre is topologically annihilated.

This gives an exact landing mechanism:

```text
analytic Xi zero
  -> nonzero algebraic conormal fibre;
faithful positive source attachment
  -> nonzero Hausdorff Hilbert fibre;
self-adjoint prime dilation
  -> kappa_p(rho) in [-1,1]
  -> Re(rho)=1/2.                                       (31)
```

Zeros on the line are the only divisor fibres which are not forced to disappear by prime
spectral purity. Off-line zeros remain legitimate analytic torsion but cannot be positive
Hausdorff source states.

Theorem E0 adds a second boundary: ordinary adelic `L2` makes every fibre disappear. The desired
source attachment must therefore be singular enough to create point fibres but rigid enough to
create them only at spectral characters in `[-1,1]`. This is the exact divisor-to-spectrum
localization problem; neither ambient `L2` nor a generic analytic RKHS has the required type.

### Exact RH-bearing source theorem

The missing theorem is now:

> Construct, before selecting any zero, a source-derived morphism from the Xi conormal module
> `I/I^2` into a positive Hausdorff Hilbert prime module, faithful on every strict-right divisor
> fibre, on which one `K_p` acts as a self-adjoint contraction.

Together with `(31)`, this is an RH proof. The theorem cannot be replaced by:

- bare finite-adele Fourier reflection, by Theorem A;
- a fixed separable archimedean tensor, which preserves rank one;
- aggregate shell boundedness alone, because that span is not prime-dilation invariant;
- the ambient finite-adelic `L2` closure, because Theorem E0 gives purely continuous spectrum and
  no divisor point fibres even on the line;
- an abstract Riesz or self-adjointness axiom, which merely inserts the conclusion-bearing
  Hodge theorem;
- a zero-selected quotient or norm.

The next research target is not another norm on the Xi-divided shell orbit. It is a
pre-specialization Euler--Gamma morphism into `(29)` whose Hermitian calibration is source-forced
and whose prime action is adjoint-compatible. The existing Burnol conductor graph and Sonin
principal-relative splitting are natural source parents; their current scalar traces do not yet
construct this conormal attachment.

### HT/Gamma capacity no-go

The publication-ready Gamma spectrum--clock theorem and the Gamma--Meixner polarization flow
prove that the completed chiral phase is genuinely HT and requires an infinite differential state.
That fact does not imply the boundedness premise of Theorem F. The formalized
hypertranscendental capacity-realization theorem proves that HT plus positivity permits every
admissible monotone scalar capacity profile, including bounded and arbitrarily divergent ones.
The all-prime multiple-elliptic-Gamma completion theorem further shows that finite-face HT can
collapse to a DA limit while every Euler boundary jet survives.

Therefore no argument of the form

```text
phase is HT / infinite-state
  -> its Xi-zero normal is bounded in the prime-dilation Hilbert completion
```

is valid. The missing boundedness theorem must use the completed Xi multiplier ideal essentially:
continuity may occur only on its annihilator fibres. Generic analytic-RKHS continuity is also
excluded by the corpus's peripheral-spectrum no-go.

The Gamma source-conormal topology does not by itself fill this gap. The formal projective
calibration theorem proves that a conormal-induced topology is unchanged under any nonzero scalar
rescaling, while its Hermitian norm changes by the squared modulus. In the open critical strip the
Gamma factor is a holomorphic unit, so a factorwise Gamma-to-Xi map can only rescale the principal
conormal generator. It cannot determine the missing Hilbert calibration or adjoint compatibility.
The publication-ready Gamma spectrum--clock theorem makes the reason structural: intensity and
projective source topology omit the HT phase clock. Any viable attachment must retain a genuinely
phase-sensitive Euler--Gamma cross-term before zero specialization.

## 10. Novelty and anti-theatre audit

- The abstract fact that bounded eigenfunctionals of self-adjoint/unitary operators have
  real/unimodular characters is standard and already present in the corpus. No novelty is claimed
  for it.
- The local Tate dilation covariance is standard. No novelty is claimed for it in isolation.
- The route-local new combination is:

  ```text
  positive HT largest-exponent divisor frame
    + universal rank-one compact-open Fourier obstruction
    + exact rational-prime shell Jacobi coefficients
    + nonzero transverse dilation compression
    + Xi-zero normal transpose character
    + one-prime contractive purity-or-marked-escape dichotomy.
  ```

- The result is significant only as a classification of the precise source sector in which an
  off-line zero must escape and as the dense-kernel/Hausdorff-collapse law `(30)`. It is not an RH
  proof and is not a source connector: faithfulness of the Xi conormal attachment remains open.
- Initial exact searches found the standard parents but not the connector:
  Jean-Francois Burnol's Fourier/zeta and co-Poisson analysis; Connes--Consani's semilocal scaling
  Hamiltonian, unitary half-density normalization, and trace formula; Tate local zeta covariance;
  and adelic density/dynamical treatments of power-free integers. None of the inspected sources
  states the largest-exponent shell Jacobi coefficients `(10)`--`(12)` or the resulting
  HT-shell one-prime purity-or-escape law. This is not an exhaustive priority audit.

## Gates

- [x] universal `P_H F P_H` rank-one theorem proved on paper
- [x] exact unitary rational-dilation normalization proved on paper
- [x] exact Tate multiplier `p^s+p^(1-s)` proved on paper
- [x] exact high-shell Jacobi matrix and marked transition mass proved on paper
- [x] nonzero transverse compression proved on paper
- [x] cofinal extended-Tate domain and descent through the algebraic `L2` orbit proved on paper
- [x] Xi-zero first-normal eigenfunctional law proved on paper
- [x] one-prime self-adjoint-contraction selector proved on paper
- [x] ambient finite-adelic dilation reduced to a bilateral shift and its point spectrum excluded
- [x] purity-or-escape theorem proved on paper
- [x] Xi-divisible blindness of the shell normal proved on paper
- [x] off-line dense-kernel / maximal-Hausdorff-collapse theorem proved on paper
- [x] source object corrected from generic divided evaluation to the conormal `I/I^2`
- [x] factorwise Gamma projective-topology shortcut rejected
- [ ] hostile specialist audit of Haar, Tate, and inner-product normalizations
- [ ] exhaustive primary-literature novelty audit
- [ ] construct source-positive completed marked-leakage norm
- [ ] prove every Xi-zero normal bounded in that completion
- [ ] RH
- [ ] Lean formalization only after the normalization, novelty, and significance gates pass

## Log

- 2026-07-28 — Strengthened the shell Fourier rank-one computation to the universal
  self-annihilating compact-open compression theorem. Replaced the failed prime-marking repair by
  rational prime dilation, computed its exact shell Jacobi matrix, and proved a one-prime
  Xi-normal purity-or-escape theorem. The result localizes the RH-bearing obstruction to
  boundedness of the prime-marked completed leakage, not the aggregate high-shell conormal.
- 2026-07-28 — Strengthened the selector from two-prime reality to the spectrum of one normalized
  self-adjoint contraction. Proved the cofinal extended-Tate domain on the algebraic dilation
  orbit and recorded the formal HT-capacity no-go: hypertranscendence and positivity alone cannot
  imply bounded zero normals.
- 2026-07-28 — Hostile audit showed the Xi-divisible shell orbit is a reporter, not a source
  connector: its zero normal is generic divided evaluation. Replaced it by the actual principal
  conormal target `I/I^2`, proved that every off-line fibre has dense algebraic kernel and zero
  maximal Hausdorff Hilbert quotient under one self-adjoint prime contraction, and isolated the
  missing theorem as a source-derived faithful calibrated Euler--Gamma attachment.
- 2026-07-28 — Proved the ordinary finite-adelic `p`-dilation is a constant-multiplicity bilateral
  shift after valuation decomposition. Its symmetrization has purely continuous spectrum and no
  point fibres, including on the critical line. Any proof must therefore construct a singular
  source-derived divisor quotient rather than complete the shell orbit inside ambient `L2`.
