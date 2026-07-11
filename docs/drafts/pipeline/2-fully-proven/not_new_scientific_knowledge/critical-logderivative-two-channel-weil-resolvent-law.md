# The critical logarithmic-derivative kernel is a complete two-channel Weil resolvent family

- **ID:** `critical-logderivative-two-channel-weil-resolvent-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** the centered Hadamard product, the polarized Weil form, and the
  Carathéodory criterion for the completed logarithmic derivative
- **Statement:** On the Euler half-plane, the critical logarithmic-derivative Pick kernel is exactly
  the sum of two polarized Weil Gram kernels evaluated on canonical rational resolvent tests. This
  two-channel family is complete for RH: its positivity is equivalent to the full Weil criterion.

## Centered divisor and Weil polarization

Put

```text
X(w)=xi(1/2+w),
L(w)=X'(w)/X(w).                                           (1)
```

For every nontrivial zero `rho`, write

```text
alpha_rho=(rho-1/2)/i,                                    (2)
```

so that `X(i alpha_rho)=0`. The centered divisor is invariant under

```text
alpha -> -alpha,
alpha -> conjugate(alpha).                                (3)
```

For Weil-admissible functions `F,G`, use the polarized form

```text
q_W(F,G)
 =sum_rho m_rho F(alpha_rho)G#(alpha_rho),

G#(z)=conjugate(G(conjugate(z))).                          (4)
```

By the completed explicit formula, `(4)` is also defined from the full von Mangoldt tail plus the
Gamma, pole, and normalization terms.

## Canonical resolvent channels

For `Re w>1/2`, define

```text
A_w(z)=w/(w^2+z^2),
B_w(z)=z/(w^2+z^2).                                       (5)
```

Every nontrivial centered zero satisfies `|Im alpha_rho|<1/2`. The poles `z=+-iw` of `(5)` are
therefore outside the closed zero strip. Products of two channels have quadratic decay on
horizontal strips, so they belong to the standard completed Weil class. In particular, all
pairings below are source-defined by the explicit formula.

Equivalently, put

```text
R_w^+(z)=1/(w-iz),
R_w^-(z)=1/(w+iz).                                        (6)
```

Then

```text
A_w=(R_w^++R_w^-)/2,
B_w=(R_w^+-R_w^-)/(2i).                                   (7)
```

These are the two Hardy resolvent orientations forced by functional-equation parity.

## Exact resolvent--Weil identity

`[PROVED]` For `Re w,Re v>1/2`,

```text
(L(w)+conjugate(L(v)))/(w+conjugate(v))
 =q_W(A_w,A_v)+q_W(B_w,B_v)                               (8)

 =1/2*(q_W(R_w^+,R_v^+)+q_W(R_w^-,R_v^-)).                (9)
```

### Proof

The even entire function `X` has the paired Hadamard product

```text
X(w)/X(0)
 =product_(alpha mod +-)(1+w^2/alpha^2)^(m_alpha),         (10)
```

with locally uniform convergence after the standard symmetric ordering; convergence follows from
the exponent-two summability of the centered divisor. Logarithmic differentiation gives

```text
L(w)
 =sum_(alpha mod +-)
    2m_alpha w/(w^2+alpha^2).                              (11)
```

Reality of `X` gives `conjugate(L(v))=L(conjugate(v))`. For each `+-` orbit, elementary algebra
gives

```text
1/(w+conjugate(v))
 *(2w/(w^2+alpha^2)
   +2conjugate(v)/(conjugate(v)^2+alpha^2))

 =2(w conjugate(v)+alpha^2)
   /((w^2+alpha^2)(conjugate(v)^2+alpha^2)).               (12)
```

On the other hand,

```text
A_v#(alpha)=conjugate(v)/(conjugate(v)^2+alpha^2),
B_v#(alpha)=alpha/(conjugate(v)^2+alpha^2).                (13)
```

Hence the contribution of `alpha` to the right side of `(8)` is

```text
(w conjugate(v)+alpha^2)
 /((w^2+alpha^2)(conjugate(v)^2+alpha^2)).                 (14)
```

The same value occurs at `-alpha`. Summing the two points in every orbit turns `(14)` into `(12)`,
including multiplicity. Summing all orbits proves `(8)`. Equation `(9)` follows from `(7)` by
polarization; the cross terms cancel.

## Complete-detector theorem

For nodes `w_1,...,w_N` in `Re w>1/2` and coefficients `c_1,...,c_N`, put

```text
A_c=sum_j c_j A_(w_j),
B_c=sum_j c_j B_(w_j).                                    (15)
```

Then the following are equivalent:

```text
(i)  RH;

(ii) q_W(A_c,A_c)+q_W(B_c,B_c)>=0
     for every finite node/coefficient system;             (16)

(iii) the kernel
      K_L(w,v)=(L(w)+conjugate(L(v)))/(w+conjugate(v))
      is positive on Re w>1/2.                              (17)
```

### Proof

Identity `(8)` gives `(ii)<->(iii)`. Under the coordinate change

```text
w=-iz,
Re w>1/2 <-> Im z>1/2,                                    (18)
```

the kernel `(17)` is one half of the critical generator `C_0` in
`xi-shift-loewner-prime-generator-law.md`. That theorem proves that positivity on this nonempty
Euler uniqueness half-plane is equivalent, by Nevanlinna--Pick extension and analytic
continuation, to absence of a pole of `L` in `Re w>0`. Such a pole is exactly a zero of `xi` with
real part greater than `1/2`. Functional-equation symmetry then gives RH. This proves
`(iii)<->(i)`.

Thus the diagonal two-channel span in `(16)` is already a complete Weil detector. One does not need
to search over an unspecified family of compactly supported tests. What remains is to prove its
nonnegativity from the Euler--Gamma source.

## Exact Euler presentation

For `Re w>1/2`, the corresponding `s=1/2+w` lies in `Re s>1`, and

```text
L(w)
 =1/s+1/(s-1)-1/2 log pi+1/2 psi(s/2)
  -sum_(n>=2)Lambda(n)n^(-s).                              (19)
```

Therefore every matrix entry in `(17)` is given by an absolutely convergent all-prime series and
the explicit finite-degree completion. Combining `(8)` and `(19)` yields the exact incidence
diagram

```text
Euler--Gamma logarithmic derivative
  -> critical Caratheodory matrix K_L
  = two-channel polarized Weil Gram
  -> positivity iff RH.                                    (20)
```

No zero ordinate is used to form the left side of `(20)`.

## Quantitative signed-Gamma carrier budget

The proved neutral signed-Gamma boundary theorem gives the two-stage carrier chain

```text
K_G
 ->C[z,exp(beta z),exp(-beta z)]
 ->C[exp(beta z),exp(-beta z)]                              (20a)
```

and, for every recurrent output `f` that is DA over `K_G`,

```text
rank_Q Gamma_B(f)<=delta_beta+2m(n+1),
delta_beta in {0,1}.                                       (20b)
```

At prime cutoff `N`, the truncated source in `(19)` contains

```text
V_N=span_Q{log p:p<=N},
dim_Q V_N=pi(N).                                           (20c)
```

Therefore any recurrent DA implementation of the Gram factorization of `(17)` has the positive
resource decomposition

```text
pi(N)
 <=delta_beta+2m(n+1)+rank_Q A_N,                          (20d)
```

where `A_N` is the complementary arithmetic character module carried by the operator, test space,
factorization coordinates, or determinant. Equivalently,

```text
rank_Q A_N
 >=pi(N)-delta_beta-2m(n+1).                               (20e)
```

Thus the factorization left open by `(17)` cannot place its unbounded phase rank in Gamma
logarithms, polynomial jets, or Stokes corrections. Those supply the finite boundary chain `(20a)`.
The cofinal Gram object must positively transport `A_N`, or its differential order/state atlas must
grow at least at the rate forced by `(20d)`.

## Relation to CCM aperture charge

`ccm-aperture-morse-index-conservation-law.md` identifies RH with conservation of the zero Morse
charge of the compact screw operators `G_a`. The present theorem supplies a canonical cofinal test
family for that charge, and its aperture transport is explicit.

With the Fourier convention

```text
hat f(z)=integral_R f(x)e^(izx)dx,                          (21)
```

put

```text
u_w^A(x)=1/2 e^(-w|x|),
u_w^B(x)=1/(2i) sgn(x)e^(-w|x|).                           (22)
```

For `Re w>0`, direct integration gives

```text
hat(u_w^A)=A_w,
hat(u_w^B)=B_w.                                           (23)
```

For `a>0`, truncate both functions to `[-a,a]` and denote their transforms by `A_(w,a)` and
`B_(w,a)`. Explicitly,

```text
A_(w,a)(z)
 =1/2*((1-e^(-(w-iz)a))/(w-iz)
       +(1-e^(-(w+iz)a))/(w+iz)),                         (24)

B_(w,a)(z)
 =1/2*((1-e^(-(w-iz)a))/(w-iz)
       -(1-e^(-(w+iz)a))/(w+iz))/i.                       (25)
```

The hard truncations belong to the logarithmic form domain: their Fourier transforms are
`O((1+|t|)^(-1))`, so the high-frequency integral with weight `log(2+|t|)` is finite. Standard
mollification at `-a,0,a` approximates them by `C_c^infinity(-a-epsilon,a+epsilon)` in the form
norm. Hence strict signs obtained below are valid restricted-Weil signs.

## Explicit aperture-transport theorem

`[PROVED]` Fix finitely many nodes `w_j` with `Re w_j>1/2` and coefficients `c_j`. Put

```text
A_c=sum_j c_j A_(w_j),       A_(c,a)=sum_j c_j A_(w_j,a),
B_c=sum_j c_j B_(w_j),       B_(c,a)=sum_j c_j B_(w_j,a).  (26)
```

Then

```text
q_W(A_(c,a),A_(c,a))+q_W(B_(c,a),B_(c,a))
 ->q_W(A_c,A_c)+q_W(B_c,B_c)                              (27)
```

as `a->infinity`.

### Proof

Choose `delta>0` smaller than every `Re w_j-1/2`. For a centered zero `alpha`, one has
`|Im alpha|<1/2`. Equations `(24)`--`(25)` therefore give the uniform tail estimate

```text
|A_(w,a)(alpha)-A_w(alpha)|
 +|B_(w,a)(alpha)-B_w(alpha)|
 <=C_w e^(-delta a)/(1+|Re alpha|).                        (28)
```

The same channels themselves are `O((1+|Re alpha|)^(-1))` on the zero strip. Since the centered
zero counting function is `O(T log T)`,

```text
sum_rho m_rho/(1+|Re alpha_rho|)^2<infinity.               (29)
```

Expand the two quadratic differences in `(27)`, use `(28)`, and dominate every term by a constant
times the summable sequence in `(29)`. The total difference is `O(e^(-delta a))`. This proves
`(27)` on the zero side, and hence for the same source-defined Weil form by the explicit formula.

## Index-faithful consequence

If a finite Euler resolvent matrix in `(17)` has a negative vector `c`, then `(8)` and `(27)` give

```text
q_W(A_(c,a),A_(c,a))+q_W(B_(c,a),B_(c,a))<0               (30)
```

for all sufficiently large `a`. At least one summand is negative. After form-core mollification,
the exact restricted Weil form therefore has a negative even or odd vector at a finite aperture,
so

```text
kappa(a)>=1.                                               (31)
```

Conversely, if every finite-aperture Weil form is nonnegative, both terms on the left of `(27)`
are nonnegative; passing to the limit makes every resolvent matrix positive. Consequently

```text
all finite-aperture Weil forms are nonnegative
 <-> all two-channel Euler resolvent matrices are positive
 <-> RH.                                                   (32)
```

This is the required index-preserving incidence transport. It is cofinal in aperture and
zero-preserving automatically because `(27)` converges in the actual Weil form, not merely in
`L2`, compact-open, or determinant topology.

A source-defined proof may now take either of two equivalent forms:

```text
Euler resolvent route:
  prove every K_L node matrix is positive;

CCM aperture route:
  prove every truncated exponential channel has nonnegative Weil energy.  (33)
```

The equivalence does not say that the two-channel span exhausts the whole positive form domain
topologically. It proves the exact statement needed for the negative charge: if any off-line zero
exists, one of these cofinal truncated channel combinations becomes negative at a finite aperture.

## Compatibility with the compact-detector obstruction

The family `(5)` is not a compact fixed-aperture family when used as a complete detector. An
off-line pole below the Euler sampling region is recovered by Nevanlinna--Pick continuation; finite
witnesses may require nodes escaping every fixed compact subset or matrices approaching the
positive cone's radical. This is exactly the growing-support/near-radical alternative proved in
`ht-weil-compact-detector-near-radical-alternative.md`.

Thus `(16)` does not contradict the remote-quartet invisibility theorem. It supplies the positive
cofinal family that theorem requires.

## Scientific status

The proof is a direct composition of the paired Hadamard logarithmic derivative, standard Weil
polarization, and the classical Carathéodory criterion. The two-channel identity is useful new
route infrastructure but does not clear the novelty gate as independent scientific knowledge.

## References

- The centered Hadamard product for Riemann's xi function.
- Weil's explicit formula and positivity criterion.
- `xi-shift-loewner-prime-generator-law.md`.
- `hedenmalm-pair-weil-polarization-law.md`.
- `signed-archimedean-gamma-orbit-charge-phase-law.md` and
  `quasianalytic-exponential-log-phase-jet-law.md`.

## Lean decision

The formal tree contains the completed logarithmic derivative and abstract finite Krein Gram
algebra, but not the infinite Hadamard log-derivative convergence, the Weil distribution, or the
Nevanlinna--Pick extension theorem. A finite rational-identity wrapper would not certify `(8)` or
the completeness theorem, so no Lean file is added.

## Gates

- [x] canonical two-channel resolvents defined
- [x] Weil admissibility checked
- [x] exact resolvent--Weil identity proved
- [x] two-channel family proved complete for RH
- [x] Euler-region source formula attached
- [x] signed-Gamma versus prime-character carrier budget attached
- [x] inverse Fourier aperture channels computed
- [x] exponential Weil-form convergence proved
- [x] index-faithful finite-aperture transport proved
- [x] compact-detector compatibility proved
- [ ] construct the source-defined positive Gram factorization of `K_L`
- [ ] deduce RH
