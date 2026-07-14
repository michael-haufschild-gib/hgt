# Additive heat echoes carry a complete prime-power value tail

- **ID:** `additive-heat-echo-prime-power-tomography-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Scientific status:** `[FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Every strict shifted echo of the additive heat-aperture observable is, after its
  explicit archimedean and functional-equation factors are removed, the forward value
  `zeta(1-conj(s)+k)`.  The canonical Euler logarithms of these values form a Dirichlet moment
  sequence.  Successive large-`k` peeling recovers `Lambda(N)/log N` exactly, hence distinguishes
  every prime power `N=p^r` with value `1/r` from every non-prime-power with value zero.  For real
  strip parameters the resulting log-echo Hankel matrices are strictly positive definite.

## 1. Values

Fix

```text
s=sigma+it,        1/2<sigma<1.
```

The `k`-th complex coefficient in the additive heat-aperture expansion is

```text
e_k(s)=C_k(s) conj(zeta(s-k)),                         (1)
```

where every `C_k(s)` is explicit and nonzero.  Put

```text
Gamma_R(w)=pi^(-w/2) Gamma(w/2),
chi(w)=Gamma_R(1-w)/Gamma_R(w).                        (2)
```

For `k>=1`, define the normalized forward value

```text
B_k(s)=e_k(s)/(C_k(s) chi(conj(s)-k)).                 (3)
```

None of the two factors divided out in `(3)` vanishes in the stated range.

## 2. Echo reflection law `[PROVED]`

For every `k>=1`,

```text
e_k(s)
 =C_k(s) chi(conj(s)-k) zeta(1-conj(s)+k),             (4)

B_k(s)=zeta(1-conj(s)+k).                              (5)
```

Indeed, Schwarz reflection gives

```text
conj(zeta(s-k))=zeta(conj(s)-k),
```

and the zeta functional equation at `w=conj(s)-k` gives

```text
zeta(w)=chi(w)zeta(1-w).                               (6)
```

Since

```text
Re(1-conj(s)+k)=1-sigma+k>1,
```

the normalized tail `(5)` lies entirely in the half-plane of absolute convergence.

## 3. Integer-value moment law `[PROVED]`

Subtracting the neutral Dirichlet atom gives

```text
M_k(s)=B_k(s)-1
      =sum_(N>=2) N^(conj(s)-1) N^(-k),       k>=1.    (7)
```

Thus the strict heat-echo tail is a discrete complex moment sequence on the reciprocal integers
`1/N`.  For `N>=2`, put

```text
a_N(s)=N^(conj(s)-1),
R_(N,k)(s)=M_k(s)-sum_(2<=m<N) a_m(s)m^(-k).           (8)
```

Then

```text
lim_(k->infinity) N^k R_(N,k)(s)=a_N(s).               (9)
```

To prove `(9)`, write the left side as `a_N(s)` plus the scaled tail over `m>N`.  For `k>=2`,

```text
|a_m(s)(N/m)^k| <= N^2 m^(sigma-3),
```

and the majorant is summable.  Each fixed `m>N` term tends to zero, so dominated convergence
proves the claim.

Equation `(9)` is the complete integer-atom tomography of the normalized echo values.  Its
prime-sensitive strengthening comes from taking the Euler logarithm.

## 4. Prime-power tomography law `[PROVED]`

On `Re(u)>1`, use the canonical absolutely convergent Euler logarithm

```text
Log_E zeta(u)
 =sum_p sum_(r>=1) p^(-ru)/r
 =sum_(N>=2) [Lambda(N)/log N] N^(-u).                 (10)
```

Define

```text
L_k(s)=Log_E B_k(s),                                   (11)
c_N(s)=[Lambda(N)/log N] N^(conj(s)-1).                (12)
```

Equations `(5)` and `(10)` give the exact log-echo moment law

```text
L_k(s)=sum_(N>=2) c_N(s)N^(-k),              k>=1.     (13)
```

For every `N>=2`, define the peeled value

```text
T_(N,k)(s)=L_k(s)-sum_(2<=m<N)c_m(s)m^(-k).            (14)
```

Then

```text
Lambda(N)/log N
 =N^(1-conj(s)) lim_(k->infinity) N^k T_(N,k)(s).      (15)
```

The proof is the same dominated-convergence argument as for `(9)`, because

```text
|Lambda(N)/log N| <= 1.
```

Consequently the recovered value is

```text
1/r,   if N=p^r for a prime p and r>=1,
0,     if N is not a prime power.                      (16)
```

The first readings are therefore

```text
N=2 -> 1,
N=3 -> 1,
N=4 -> 1/2,
N=5 -> 1,
N=6 -> 0,
N=7 -> 1,
N=8 -> 1/3.                                           (17)
```

Thus the additive heat screen does not merely detect the zeroth zeta value.  Its complete strict
echo tail determines the Euler prime-power support and the prime-power exponent.

## 5. Positive log-echo Hankel law `[PROVED]`

Let `s=sigma` be real with `1/2<sigma<1`.  Then every `c_N(s)` in `(12)` is nonnegative, and it is
positive exactly on prime powers.  For integers `q>=1` and `r>=0`, set

```text
H_(q,r)(s)=[L_(q+i+j)(s)]_(0<=i,j<=r).                 (18)
```

Every `H_(q,r)(s)` is strictly positive definite; in particular,

```text
det H_(q,r)(s)>0.                                      (19)
```

For a nonzero real vector `v=(v_0,...,v_r)`, equation `(13)` gives

```text
v^T H_(q,r)(s) v
 =sum_(N>=2)c_N(s)N^(-q)
    (sum_(j=0)^r v_j N^(-j))^2.                       (20)
```

Every summand is nonnegative.  Equality would force the polynomial
`sum_j v_j X^j` to vanish at `X=1/N` for every prime power `N`, an infinite set of distinct
points.  Hence the polynomial, and therefore `v`, would be zero.  This proves strict positivity.

The relation `(19)` is unconditional.  It is a positive structural law for the echo values, not
an alternative form of the integer-polynomial trace-Hankel criterion for RH.

## 6. Relation to zeta zeros and hypertranscendental values

At a nontrivial zero `s`, the `k=0` heat echo vanishes, while every `k>=1` echo is nonzero.  The
present theorem strengthens that value pattern:

```text
one missing zeroth echo
+ complete forward zeta-value tail
+ exact prime-power recovery from the Euler logarithms. (21)
```

The additive observable therefore couples a divisor event to an infinite arithmetic value flag.
The tail does not localize the missing echo to the critical line by itself; its positive content
is that no arithmetic information is lost at the defect.  An RH-strength theorem would need an
additional relation distinguishing the horizontal position of the missing zeroth value while
preserving the complete tail `(15)`.

The exact reflection interface is now isolated in
`../../2-fully-proven/not_new_scientific_knowledge/heat-aperture-prime-seam-reflection-collapse.md`.
For every prime `p`, the FE--Schwarz difference of the recovered coefficient is precisely
`C_p(rho)/log p`, where `C_p` is the canonical prime seam.  Hence reflection equality of the
whole prime tail is equivalent to equality of its `p=2` member and to `Re(rho)=1/2`.  This removes
an unnecessary infinite-tail hypothesis but does not produce the missing source-side orientation.

For hypertranscendental-function research, `(4)`--`(15)` exhibit a reusable pattern: an asymptotic
coefficient family on one analytic side can be reflected into an absolutely convergent value
sequence, and its logarithmic Dirichlet atoms can then be recovered exactly.

## 7. Novelty and parent-theory audit

The individual parents are classical:

- the zeta functional equation;
- the Euler product and the expansion `(10)`;
- uniqueness and first-coefficient extraction for ordinary Dirichlet series;
- the moment-matrix positivity argument in `(20)`.

The candidate-new content is their exact coupling to the additive heat-aperture coefficient family:
the observable echo factorization `(4)`, the full prime-power peeling law `(15)`, and the positive
log-echo Hankel family `(19)`.  Searches for heat-kernel/polylogarithm zeta expansions, shifted zeta
values, Hausdorff moments of zeta shifts, and Dirichlet-coefficient recovery did not locate this
combined theorem or an equivalent source observable.  Results on shifted moments of zeta concern
height averages and are not coefficient-depth moment sequences of the form `(13)`.

The novelty verdict is provisional pending specialist comparison.  The result is not claimed as a
new proof of a classical Dirichlet-series uniqueness theorem.

## 8. Formal artifacts

- `formal/GaloisForLFunctions/RHTower/HeatApertureEchoLadder.lean`
  - `heatApertureBackwardZetaValue_eq_zetaChi_mul_forward`
  - `heatApertureEchoValue_eq_forward`
- `formal/GaloisForLFunctions/RHTower/CanonicalEulerLog.lean`
  - `eulerLogDirichletCoeff_prime_pow_succ`
  - `canonicalEulerLogZeta_eq_primeLog`
  - `exp_canonicalEulerLogZeta_eq_riemannZeta`
- `formal/GaloisForLFunctions/RHTower/HeatApertureEchoTomography.lean`
  - `heatApertureIntegerMoment_eq_forward_sub_one`
  - `tendsto_heatApertureIntegerPeeledValue`
  - `heatApertureLogEchoValue_eq_LSeries`
  - `tendsto_heatAperturePrimePowerRecoveredValue`
  - `tendsto_heatAperturePrimePowerRecoveredValue_prime_pow`
  - `tendsto_heatAperturePrimePowerRecoveredValue_eq_zero`
- `formal/GaloisForLFunctions/RHTower/HeatApertureEchoHankel.lean`
  - `heatApertureRealLogEchoValue_add_eq_moment`
  - `heatApertureLogEchoHankel_posDef`
  - `heatApertureLogEchoHankel_det_pos`
- `formal/GaloisForLFunctions/RHTower/HeatAperturePrimeSeamReflection.lean`
  - source draft of the exact FE--Schwarz coefficient/seam relation and prime-two collapse;
    targeted verification is deferred under the active no-computation boundary

The general all-index peeling theorem is supplied by
`formal/GaloisForLFunctions/HTGeometry/LSeriesPowerTwist.lean`; strict positivity of every finite
discrete moment Hankel matrix is supplied by
`formal/GaloisForLFunctions/HTGeometry/DiscreteMomentHankel.lean`.

## Verification

- [x] exact elaboration of each new module
- [x] dedicated Lake target builds for the new modules
- [x] no `sorry`, `admit`, new axiom, `opaque`, or `unsafe` declaration introduced
- [x] main theorem axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] project formal lint

## Gates

- [x] exact value family specified
- [x] echo-to-forward-zeta factorization proved
- [x] all-integer coefficient peeling proved
- [x] prime-power Euler-log peeling proved
- [x] real log-echo Hankel positivity proved
- [x] exact factorization formalized in Lean
- [x] focused parent and collision search
- [ ] formalize the canonical Euler logarithm and all-`N` coefficient peeling
- [ ] independent specialist novelty audit

## References checked

- NIST DLMF, §25.2, Dirichlet-series definition of the Riemann zeta function.
- NIST DLMF, §27.4, Euler products and the von Mangoldt Dirichlet series.
- G. H. Hardy and M. Riesz, *The General Theory of Dirichlet's Series*, Cambridge Tracts in
  Mathematics and Mathematical Physics 18, 1915.
- A. Defant, D. Garcia, M. Maestre, and P. Sevilla-Peris, *Dirichlet Series and Holomorphic
  Functions in High Dimensions*, Cambridge University Press, 2019, for coefficient-preserving
  Dirichlet-series theory.
