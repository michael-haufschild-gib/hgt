# The CCM prime-channel separating locus is open dense

- **ID:** `ccm-generic-ground-separating-incidence-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** separating vectors for a finite operator space, Kato's simple-eigenvalue
  response formula, and injectivity of the compact-support Mellin transform
- **Statement:** The compressed prime-shift operator space has an open dense set of separating
  vectors. At every simple finite-Weil ground state in this set, the reduced-resolvent derivative
  of the CCM characteristic function is injective in the finite prime coefficients. Hence
  source-to-divisor incidence failure is confined to an explicit Gram-determinant seam.

## 1. Separating vectors for a finite operator space

Let `H` be a complex Hilbert space and let `A_0=I,A_1,...,A_k` be bounded operators. Call `x in H`
**separating** for their span when

```text
A_0 x,A_1 x,...,A_k x                                    (1)
```

are linearly independent. Define the separating Gram determinant

```text
Delta_A(x)=det((<A_i x,A_j x>)_(0<=i,j<=k)).             (2)
```

Then `x` is separating exactly when `Delta_A(x)>0`.

`[PROVED]` If one separating vector exists, the separating locus

```text
Omega_A={x in H:Delta_A(x)>0}                             (3)
```

is open and dense in `H`.

### Proof

Continuity of `(2)` makes `(3)` open. Fix one `x_0 in Omega_A` and an arbitrary `x in H`. For real
`t`,

```text
t |-> Delta_A(x+t x_0)                                    (4)
```

is a real polynomial. Its leading coefficient is `Delta_A(x_0)>0`, because the Gram determinant
of the `k+1` vectors `A_i(x+t x_0)` has top degree `2(k+1)`. Thus `(4)` is not the zero polynomial
and has only finitely many real roots. Arbitrarily small nonzero `t` avoiding those roots give
separating vectors `x+t x_0` arbitrarily close to `x`.

## 2. Compressed prime shifts have a separating vector

Let `H_A=L2([0,A],e^(-x)dx)` and let

```text
T_(A,h)=P_A S_h P_A,       0<h<A,                         (5)
```

be the compressed weighted shifts from
`ccm-compressed-prime-shift-arithmetic-complement-law.md`. Fix distinct

```text
0<h_1<...<h_k<A.                                           (6)
```

Choose

```text
0<epsilon<min(h_1,h_2-h_1,...,h_k-h_(k-1),A-h_k)          (7)
```

and a nonzero `x_0` supported in `[0,epsilon]`. Then `x_0` is supported in `[0,epsilon]`, while

```text
T_(A,h_j)x_0
```

is nonzero and supported in `[h_j,h_j+epsilon]`. These intervals are pairwise disjoint, so

```text
x_0,T_(A,h_1)x_0,...,T_(A,h_k)x_0                         (8)
```

are linearly independent.

The same conclusion holds for the symmetric prime-correlation operators

```text
B_(A,h)=T_(A,h)+T_(A,h)^*.                                (9)
```

Indeed `(7)` makes `T_(A,h_j)^*x_0=0`, so `B_(A,h_j)x_0=T_(A,h_j)x_0`. Consequently the separating
locus for

```text
I,B_(A,h_1),...,B_(A,h_k)                                 (10)
```

is open and dense.

For prime cutoffs `P<e^A`, take `h_p=log p`. Unique factorization makes the labels distinct, and
the theorem gives an open dense set of vectors separating all `pi(P)` prime channels modulo the
identity.

### Exact Weil specialization

This shift family is the actual prime perturbation of the restricted Weil form. On the weighted
Laplace space, `critical-euler-weighted-shift-accretivity-law.md` proves

```text
n^(-1-z) <-> n^(-1)S_(log n).                             (10a)
```

Hence the Hermitian prime correlation is represented by

```text
C_n=n^(-1)(S_(log n)+S_(log n)^*).                        (10b)
```

On an aperture core supported in `[0,A]`, its compression is

```text
P_A C_n P_A
 =n^(-1)(T_(A,log n)+T_(A,log n)^*).                     (10c)
```

The alternative Suzuki normalization absorbs one factor `n^(-1/2)` into the coefficient form;
this only multiplies each channel by a nonzero scalar and does not change the separating locus.
The support-overlap law makes `(10c)` zero exactly for `log n>A`, or `log n>2a` on a symmetric
interval of diameter `2a`. Thus the operators `A_j` in the coefficient-pointed finite-Weil family
are precisely the symmetric compressed shifts in `(9)`, up to their fixed nonzero critical
weights.

### Degree-one Euler-ray specialization

Independent prime-power coefficients form a larger deformation space than the degree-one Euler
source. For a local factor

```text
(1-a_p p^(-s))^(-1),                                      (10d)
```

differentiation at a nonzero source point changes the whole finite ray `p^m`, not only the first
prime term. The corresponding aperture operator has the form

```text
W_(A,p)
 =sum_(m>=1,m log p<A) alpha_(p,m)
    B_(A,m log p),                                        (10e)
```

where every displayed `alpha_(p,m)` is nonzero. At the zeta point the unnormalized logarithmic
flux derivative contributes the factor `m log p` together with the fixed critical weight.

For distinct primes, the shift-label sets

```text
{m log p:m>=1,m log p<A}                                  (10f)
```

are disjoint. Equality `m log p=ell log q` exponentiates to `p^m=q^ell`; unique factorization
gives `p=q` and `m=ell`.

Choose `epsilon` smaller than the distance between every two labels in the finite union `(10f)`,
smaller than its least label, and smaller than the distance of its largest label from `A`. For the
test vector `x_0` supported in `[0,epsilon]`, all shifted pieces

```text
B_(A,m log p)x_0
```

have pairwise disjoint supports. Hence

```text
x_0,(W_(A,p)x_0)_(p<=P)                                   (10g)
```

are linearly independent. Section 1 gives an open dense locus separating the exact degree-one
Euler-ray operators `W_(A,p)`. Thus the theorem carries `pi(P)` genuine local Euler parameters,
not an artificially independent list of prime powers.

## 3. Projection criterion

Let `x` be a unit vector and `P_x^perp=I-|x><x|`. Then the following are equivalent:

```text
(i)  x,A_1x,...,A_kx are linearly independent;
(ii) P_x^perp A_1x,...,P_x^perp A_kx are linearly independent. (11)
```

### Proof

A relation among the vectors in `(ii)` says

```text
sum_j c_j A_jx=c_0 x                                      (12)
```

for some `c_0`; this is exactly a relation among the vectors in `(i)`. The converse follows by
applying `P_x^perp`.

Thus for `x in Omega_A`, the prime-incidence map

```text
(c_1,...,c_k) |-> P_x^perp sum_j c_j A_jx                (13)
```

is injective.

## 4. Kato response and Mellin incidence

Fix a finite aperture and consider the coefficient-pointed restricted Weil family

```text
A_b=A_infinity-sum_(j=1)^k b_j A_j.                       (14)
```

Assume its lowest eigenvalue `epsilon(b)` is simple and isolated, with normalized eigenvector
`xi_b`. Put

```text
R_b^perp=(A_b-epsilon(b))^(-1) on xi_b^perp.              (15)
```

The Kato response formula proved in `ccm-prime-source-ground-incidence-response.md` is

```text
D_c xi_b
 =R_b^perp P_(xi_b)^perp sum_j c_j A_j xi_b.              (16)
```

Because `R_b^perp` is injective on `xi_b^perp`, equations `(11)`--`(13)` imply:

> `[PROVED]` If `xi_b` separates `I,A_1,...,A_k`, then the ground-vector derivative
> `c |-> D_c xi_b` is injective.

Let

```text
F_b(z)=M_lambda(xi_b)(z)                                  (17)
```

be the dephased CCM characteristic function. The derivative is

```text
D_c F_b=M_lambda(D_c xi_b).                               (18)
```

The Mellin transform is injective on the compact-support aperture space: after `u=e^t`, it is the
Fourier--Laplace transform of a compactly supported `L2` function, and vanishing identically forces
that function to vanish. Hence `(18)` is injective whenever `(16)` is. The complete characteristic
response therefore distinguishes every finite prime-coefficient direction at every simple ground
state in the separating locus.

## 4a. Eventual Galerkin preservation

Let `P_M` be the nested logarithmic Fourier projections and suppose `P_M->I` strongly. At fixed
aperture, `ccm-galerkin-cofinal-diagonal-transfer.md` proves, under a simple continuous ground
state,

```text
xi_M->xi in H.                                             (18a)
```

For every bounded prime or prime-ray operator `A_i`,

```text
P_M A_i P_M xi_M -> A_i xi.                               (18b)
```

Indeed `P_M xi_M=xi_M`, the input converges by `(18a)`, boundedness controls `A_i`, and the final
projection converges strongly. Therefore every entry of the finite Gram matrix

```text
G_M=(<P_M A_i P_M xi_M,P_M A_j P_M xi_M>)_(0<=i,j<=k)    (18c)
```

converges to the corresponding entry of the continuous Gram matrix. If `xi` lies outside the
separating seam, its Gram determinant is positive, so

```text
det G_M>0                                                  (18d)
```

for all sufficiently large `M`.

Thus fixed-aperture source incidence survives every sufficiently large CCM Galerkin cutoff. The
full Fourier-coordinate vector of the finite ground response is injective in the source
directions; these coordinates are exactly the residues entering the finite relative determinant,
up to its nonzero normalization. If a base residue vanishes, the stratified law in
`ccm-euler-observability-relative-index-allocation-law.md` records the direction as nearby index
birth rather than incorrectly charging it to the base active index.

## 5. The determinantal incidence seam

For either the independent prime-correlation operators or the degree-one Euler-ray operators,
define

```text
Sigma_(A,P)
 ={x in H_A:
   det((<A_i x,A_j x>)_(0<=i,j<=pi(P)))=0},              (19)
```

where `A_0=I` and the remaining operators are the labeled prime or prime-ray channels. Sections
1--2 prove

```text
Sigma_(A,P) is closed and has empty interior.              (20)
```

At a simple finite-Weil ground state, failure of the full prime-to-characteristic derivative is
equivalent to

```text
xi_b in Sigma_(A,P).                                       (21)
```

Thus the source-to-divisor problem is not the existence of prime channels or of a response map.
Both already exist. It is the exclusion of one explicit algebraic-analytic seam for the true
source-selected ground state.

## 6. Orbit-sensitive meaning

The map

```text
b |-> F_b                                                  (22)
```

is pointed: it assigns a unique characteristic function to the marked coefficient vector through
the restricted Weil ground-state problem. Multiplying `F_b` externally by a symmetric orbit
polynomial changes the divisor without changing `b` and is not another value of the map `(22)`
unless a separate source deformation produces it. Hence injectivity of the differential in
Section 4 supplies local source sensitivity, while the exact determinant identity supplies the
required source--divisor pointing.

This does not yet give global orbit separation. A cofinal RH argument must prove that the pointed
map remains divisor-preserving and that its complete Euler-Pick/Weil inertia changes under every
off-line orbit insertion.

## 7. Positive CCM reduction

The finite incidence theorem is now:

```text
simple isolated ground state
  + xi_b outside Sigma_(A,P)
  -> injective pi(P)-direction ground response
  -> injective prime-to-characteristic response.           (23)
```

The cofinal theorem forced on a successful construction is:

```text
for coupled P->infinity and A->infinity,
  xi_(Lambda,A) stays outside Sigma_(A,P)
  with a quantitative least-Gram-eigenvalue bound strong enough
  for growing-aperture Mellin transfer.                     (24)
```

Qualitative genericity is not enough. The least eigenvalue of the Gram matrix in `(19)` may tend
to zero while never vanishing, which would destroy uniform source-to-divisor transport. The
required positive invariant is therefore the **cofinal separating margin**

```text
sigma_(A,P)
 =lambda_min((<A_i xi_A,A_j xi_A>)_(0<=i,j<=pi(P)))>0,     (25)
```

coupled to the reduced-resolvent spectral gap and the exact Mellin evaluation norm.

The margin cannot remain positive for free as prime logarithms crowd.
`ccm-prime-log-crowding-separating-margin-law.md` proves, for the translation-generator norm
`||D xi_A||` and nearest-neighbour prime-log spacing `delta_P`,

```text
sigma_(A,P)<=delta_P^2||D xi_A||^2/2                     (26)
```

for the translation channels, with the corresponding factor `2` for symmetric channels. Hence
any proposed lower bound for `(25)` must be accompanied by inverse-spacing growth of the ground
state's generator energy. A norm-stable cofinal transversality proof is therefore a quantitative
oscillation law, not merely avoidance of a nowhere-dense set. A construction allowing the margin
to vanish must instead specify a renormalized topology that still transports those singular
directions; qualitative injectivity alone supplies no uniform inverse.

For the exact degree-one Euler-ray operators, the same conclusion applies to the top prime shell
`e^(A/2)<p<=e^A`: every such ray contains only its first shift inside the aperture. After the
invertible critical-weight normalization, the nearest log-prime spacing in this shell is
`O(A^2e^(-A))`. A fixed normalized incidence margin therefore requires generator norm at least
of order `e^A/A^2`.

## 8. Attacks and scope

- Linear independence of the operators does not make every vector separating. The true ground
  state must be shown to avoid `(19)`.
- Open density at each fixed cutoff does not give a cofinal lower bound for `(25)`.
- The exact weighted-Laplace identification `(10a)`--`(10c)` is load-bearing. An unrelated abstract
  shift representation would not identify the zeta ground state.
- Injective first variation is local source sensitivity, not locally uniform determinant
  convergence and not positivity.
- The theorem is standard operator linear algebra plus Kato response and therefore a bridge, not
  new scientific knowledge.

## 9. Lean decision

The tree contains finite linear independence and Euler-source Jacobian components but no
parameterized closed Weil operator, Kato eigenprojection, or analytic Mellin transform interface.
Formalizing only the finite Gram determinant lemma would not certify `(23)`, so no Lean file is
added.

## Gates

- [x] open-dense separating-vector theorem proved
- [x] compressed prime shifts and symmetric correlations shown to admit a separating vector
- [x] symmetric compressed shifts identified with the actual finite-Weil prime perturbations
- [x] exact degree-one Euler-ray operators proved to have an open dense separating locus
- [x] projected incidence injectivity characterized exactly
- [x] Kato ground-response injectivity proved on the separating locus
- [x] Mellin characteristic-response injectivity proved
- [x] separating response proved stable under sufficiently large fixed-aperture Galerkin cutoffs
- [x] determinantal exceptional seam isolated
- [x] cofinal separating margin defined
- [x] exact prime-crowding/ground-oscillation tradeoff proved
- [ ] prove the true cofinal ground state avoids the incidence seam
- [ ] prove a quantitative lower bound for the separating margin
- [ ] combine with the reduced-resolvent and Mellin-growth bounds
- [ ] prove divisor-preserving convergence or complete Weil positivity
- [ ] RH
