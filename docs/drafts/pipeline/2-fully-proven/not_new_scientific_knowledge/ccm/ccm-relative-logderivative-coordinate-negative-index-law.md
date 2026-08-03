# Every active CCM Fourier coordinate contributes one relative logarithmic negative square

- **ID:** `ccm-relative-logderivative-coordinate-negative-index-law`
- **Stage:** 2-fully-proven / paper proof complete
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** CCM's finite relative-determinant formula and finite-dimensional
  generalized-Nevanlinna kernel theory
- **Statement:** The Pick kernel of the logarithmic derivative of a CCM relative determinant has
  negative-square index exactly equal to the number of active periodic Fourier coordinates of the
  finite-Weil ground vector. Hence a cofinally growing coordinate carrier necessarily requires a
  cofinally growing positive background cancellation; no fixed-index scalar relative kernel can
  carry the CCM limit.

## 1. Rational relative determinant

Let `J` be a finite index set, let the numbers `d_j`, `j in J`, be distinct and real, and let

```text
xi_j in R\{0},
sum_(j in J)xi_j=1.                                         (1)
```

Put

```text
R(z)=sum_(j in J) xi_j/(d_j-z).                             (2)
```

Assume all zeros of `R` are real. This is automatic for the CCM relative determinant under the
simple-even hypothesis because its numerator is the characteristic polynomial of the finite
self-adjoint perturbed scaling operator.

The pole at every `d_j` is genuine because its residue is nonzero. Since `(1)` gives

```text
R(z)=-1/z+O(1/z^2),       z->infinity,                      (3)
```

the numerator has degree `|J|-1`. Let `E` be its set of distinct real zeros and let `m_e` be the
multiplicity of `e in E`. Then

```text
R(z)=C product_(e in E)(e-z)^(m_e)
        /product_(j in J)(d_j-z),

sum_(e in E)m_e=|J|-1.                                     (4)
```

No `e` equals a `d_j`, again because the pole at `d_j` is genuine.

## 2. Exact signed Cauchy decomposition

On the right half-plane put

```text
M_R(w)=d/dw log R(-iw),                                    (5)

K_R(w,v)
 =(M_R(w)+conjugate(M_R(v)))/(w+conjugate(v)).              (6)
```

Logarithmic differentiation of `(4)` gives

```text
M_R(w)
 =sum_(e in E)m_e/(w-ie)
  -sum_(j in J)1/(w-id_j).                                 (7)
```

For real `t`, define

```text
phi_t(w)=1/(w-it).                                          (8)
```

The elementary identity

```text
1/(w+conjugate(v))
 *(1/(w-it)+1/(conjugate(v)+it))
 =phi_t(w)conjugate(phi_t(v))                               (9)
```

turns `(7)` into the exact kernel decomposition

```text
K_R(w,v)
 =sum_(e in E)m_e phi_e(w)conjugate(phi_e(v))
  -sum_(j in J)phi_(d_j)(w)conjugate(phi_(d_j)(v)).          (10)
```

Thus every perturbed zero supplies a positive Cauchy square, whereas every active base coordinate
supplies a negative Cauchy square.

## 3. Exact negative-square index

Let `U` be any nonempty open subset of `Re w>0`. Then

```text
ind_-(K_R restricted to U x U)=|J|.                         (11)
```

### Proof

Equation `(10)` is a Pontryagin-space realization with `|J|` negative coordinates, so the index is
at most `|J|`.

The rational functions

```text
{phi_e:e in E} union {phi_(d_j):j in J}                     (12)
```

are linearly independent. Indeed, a linear combination vanishing on `U` vanishes identically by
the identity theorem; its partial-fraction residue at each distinct pole then kills the
corresponding coefficient.

Consequently the feature vectors

```text
w |->((sqrt(m_e)phi_e(w))_(e in E),(phi_(d_j)(w))_(j in J)) (13)
```

span the full coordinate space as `w` ranges over `U`. Choose finitely many nodes for which these
vectors span. Their kernel Gram matrix is congruent, after restriction to a basis, to the diagonal
signature matrix with `|J|` negative entries. Sylvester inertia gives at least `|J|` negative
eigenvalues. Together with the upper bound, this proves `(11)`.

The conclusion is independent of the signs of the residues `xi_j`. Those signs determine whether
`R` itself is Herglotz, but the logarithmic derivative records every genuine pole with coefficient
`-1`.

## 4. CCM specialization

For the CCM cutoff, put

```text
d_j=2pi*j/L,
L=2log(lambda),
xi=sum_(-N<=j<=N)xi_j V_j,
c_j=L^(-1/2)xi_j,
sum_(-N<=j<=N)c_j=1.                                      (14)
```

The relative determinant is

```text
R_(lambda,N)(z)
 =sum_(-N<=j<=N)c_j/(d_j-z).                               (15)
```

Let

```text
J_(lambda,N)={j:c_j!=0}={j:xi_j!=0}.                        (16)
```

Coordinates outside `J_(lambda,N)` correspond exactly to canceled apparent poles and are removed
before applying the theorem. Therefore

```text
ind_- K_(R,lambda,N)=#J_(lambda,N)                          (17)
```

on every nonempty open node region in the right half-plane. In the generic full-support case this
is

```text
ind_- K_(R,lambda,N)=2N+1.                                 (18)
```

This is a quantized carrier law: activating one additional Fourier coordinate creates one
additional relative negative square. Reality of all perturbed spectral zeros does not reduce this
charge.

## 5. Every divisor-carrying CCM limit has linearly growing coordinate charge

Let `lambda_n->infinity`, let `N_n` be Galerkin cutoffs, and suppose nonvanishing normalizations of
the CCM determinants converge locally uniformly to `Xi`. Equivalently for the present zero
argument, suppose

```text
E_n(z)F_(lambda_n,N_n)(z)->Xi(z)                              (19)
```

locally uniformly, where every `E_n` is entire and zero-free and `F_(lambda,N)` is the dephased
Fourier determinant.

Since `Xi(0)!=0`, continuity supplies `delta>0` such that

```text
Xi(z)!=0 for every real z in [-delta,delta].                  (20)
```

Uniform convergence on this interval makes `E_nF_(lambda_n,N_n)`, and hence
`F_(lambda_n,N_n)`, zero-free there for all sufficiently large `n`.

Proposition 5.9 of *Zeta Spectral Triples* gives the exact residual lattice rule. With

```text
d_(n,j)=2pi*j/L_n=pi*j/log(lambda_n),
L_n=2log(lambda_n),                                          (21)
```

the point `d_(n,j)` remains a zero of `F_(lambda_n,N_n)` whenever either

```text
|j|>N_n,
```

or `|j|<=N_n` and `xi_(n,j)=0`. Therefore every integer satisfying

```text
|j|<=delta*log(lambda_n)/pi                                  (22)
```

must lie inside the Galerkin window and belong to `J_(lambda_n,N_n)`. Consequently

```text
#J_(lambda_n,N_n)
 >=2 floor(delta*log(lambda_n)/pi)+1.                        (23)
```

Combining `(17)` and `(23)` gives

```text
ind_- K_(R,lambda_n,N_n)
 >=2 floor(delta*log(lambda_n)/pi)+1.                        (24)
```

Thus any divisor-preserving CCM limit forces relative negative charge to grow at least linearly
in the logarithmic aperture. This is not an optional inefficiency of the Galerkin basis: inactive
coordinates leave exact unwanted spectral zeros in a fixed zero-free neighborhood of the target.

## 6. Positive requirement for the cofinal CCM route

The periodic background and relative displacement satisfy

```text
K_(D,lambda,N)=K_(0,lambda)+K_(R,lambda,N),                 (25)
```

where `K_(0,lambda)` is the background kernel isolated in
`ccm-euler-pick-logderivative-transfer-boundary-law.md`. That kernel becomes locally small in the
Euler half-plane, but at each finite stage it carries the base spectral coordinates needed to
cancel `(17)`.

Consequently every successful cofinal construction is forced to provide an index-matched positive
carrier:

```text
active Fourier state #J_(lambda,N)
  + relative negative charge #J_(lambda,N)
  + source-defined periodic/operator covariance canceling that charge
  -> asymptotically positive complete Euler kernel.          (26)
```

If `#J_(lambda,N)->infinity`, no fixed-negative-index Pontryagin space, fixed-rank correction, or
fixed-order scalar determinant ratio can perform this cancellation. The compensating carrier must
grow with the coordinate state, remain genuinely infinite-dimensional, or be imposed by an exact
global constraint.

This is the positive form of the obstruction: the relative scalar kernel does not lose the growing
state. It records it faithfully as negative index, one coordinate at a time.

## 7. Exact scope

- `[PROVED]` The signed Cauchy decomposition `(10)` is exact.
- `[PROVED]` The negative-square index is exactly the active coordinate count `(11)` and `(17)`.
- `[PROVED]` The result holds on every nonempty open node region; shrinking the Euler node window
  does not reduce the charge.
- `[PROVED]` Every locally uniform divisor-carrying CCM limit forces the logarithmic lower bound
  `(23)`--`(24)` on active coordinates and relative negative charge.
- `[NOT PROVED]` The theorem does not show that `#J_(lambda,N)` grows for the true CCM ground vector.
- `[NOT PROVED]` It does not construct the index-matched positive background cancellation.
- `[NOT PROVED]` It does not prove RH.

## 8. Scientific classification and Lean decision

The theorem is a direct finite-dimensional generalized-Nevanlinna realization of a rational
logarithmic derivative. It is useful CCM route infrastructure but is standard parent theory and
not new scientific knowledge.

The Lean tree can express finite Hermitian inertia, but it does not contain the analytic Cauchy
feature independence or the CCM relative determinant. Formalizing only the resulting signature
matrix would be a wrapper around the missing analytic specialization. No Lean file is added.

## Gates

- [x] rational relative determinant factored
- [x] signed Cauchy kernel decomposition proved
- [x] exact negative-square index proved
- [x] CCM active-coordinate specialization proved
- [x] logarithmic support/negative-index floor proved for every divisor-carrying CCM limit
- [ ] prove an unconditional support floor for the true CCM ground vector
- [ ] construct the index-matched positive background carrier
- [ ] prove cofinal Euler-kernel positivity
- [ ] RH
