# The limiting CCM radial first row is uniformly arithmetically summable

- **ID:** `ccm-limiting-radial-first-row-weber-bound`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** Dunster's radial Bessel model, Bessel symbol asymptotics, stationary phase,
  and the Weber Gaussian--Bessel transform
- **Statement:** The complete first row of the limiting radial Bessel Gram matrix satisfies the
  uniform bound `M_c(k)=O(c^(-1/2)k^(-2))`. Its logarithmically weighted arithmetic sum is therefore
  `O(c^(-1/2))`.

## Model

Put

```text
rho(x)=sqrt(x^2-1),
R_c(x)=x^(-1/2)J_0(c*rho(x)),

M_c(k)=c/sqrt(k) integral_1^infinity R_c(x)R_c(k*x)dx.          (1)
```

The equality

```text
M_c(k)=c/sqrt(k) integral_0^infinity r/(1+r^2)J_0(c*r)
       J_0(c*sqrt(k^2*r^2+k^2-1))dr                             (2)
```

follows from `r=rho(x)`. This is the `sigma=0` limit of the normalized first-row Gram entry in
Dunster's uniform radial approximation.

## Uniform theorem

`[PROVED HERE]` There is an absolute constant `C` such that, for `c>=2` and every integer `k>=2`,

```text
|M_c(k)|<=C/(sqrt(c)*k^2).                                      (3)
```

Consequently,

```text
sum_(k>=2)log(k)|M_c(k)|=O(c^(-1/2)).                           (4)
```

## Bulk proof: `2<=k<=c`

Use the standard Bessel symbol decomposition

```text
J_0(t)=exp(i*t)a_+(t)+exp(-i*t)a_-(t),
|d^j/dt^j a_+-(t)|<=C_j*t^(-1/2-j),   t>=1,                    (5)
```

and leave `J_0` unexpanded for bounded argument. Split `(2)` at `r=2/c`. Since the second Bessel
argument is at least `c*sqrt(k^2-1)`, the endpoint part is bounded absolutely by

```text
C*c/sqrt(k) *c^(-2)*(c*k)^(-1/2)
 =C*c^(-3/2)/k
 <=C*c^(-1/2)/k^2.                                             (6)
```

On `r>=2/c`, the difference phase is

```text
phi_k(r)=r-sqrt(k^2*r^2+k^2-1).                                 (7)
```

It has exactly one critical point on the full half-line,

```text
r_k=1/k,
|phi_k''(r_k)|=(k^2-1)/k asymptotic to k.                       (8)
```

If `k<=c/2`, this point lies in the bulk piece. After the prefactor in `(2)` is included, the
amplitude at `r_k` is `O(k^(-3/2))` and its first symbol seminorm on a fixed relative neighbourhood
has the corresponding scaled bound. The one-dimensional stationary-phase lemma gives

```text
C*k^(-3/2)*(c*k)^(-1/2)=C*c^(-1/2)k^(-2).                      (9)
```

On the complement of that neighbourhood, `phi_k'` is monotone and bounded below by its distance
from the critical point times a constant comparable to `k`. One integration by parts on dyadic
annuli gives the same bound. If `c/2<k<=c`, the critical point already lies in the endpoint piece
estimated in `(6)`, so the whole bulk piece is nonstationary. The sum phase has no critical point
in either case and is smaller. After the measure in `(2)` is included, the differentiated
far-field amplitudes are `O(r^(-2))`, so the boundary at infinity vanishes. This proves `(3)` for
`k<=c`.

## Endpoint proof: `k>=c`

Now `r_k=1/k` lies inside the Bessel endpoint `r<=1/c`. On `r<=2/c`, set `z=c*r` and then `w=z^2`.
The second Bessel phase is

```text
Theta_(c,k)(w)=sqrt(k^2*w+c^2*(k^2-1)),

Theta_(c,k)'(w)
 =k^2/(2*sqrt(k^2*w+c^2*(k^2-1))) asymptotic to k/c.            (10)
```

The factor `z dz=dw/2` in `(2)` removes the apparent stationary endpoint. The second Bessel
symbol has size `O((c*k)^(-1/2))`; one integration by parts in `w` therefore gives

```text
C/(c^(3/2)*k) *c/k=C/(sqrt(c)*k^2).                             (11)
```

On `r>=1/c`, both Bessel phases are nonstationary because their only possible difference critical
point satisfies `r_k<=1/c`. The same symbol integration by parts on dyadic annuli gives `(11)`.
This proves `(3)` for `k>=c` and completes the theorem.

## Exact transition calibration

The power in `(3)` is sharp at the coalescing scale. If `k/c->u>0`, then after `z=c*r`,

```text
Theta_(c,k)(z^2)
 =c*k-1/(2u)+u*z^2/2+o(1).                                     (12)
```

The classical Weber transform

```text
integral_0^infinity z J_0(z)exp(i*u*z^2/2)dz
 =i/u*exp(-i/(2u))                                              (13)
```

holds by Abel continuation of the Gaussian--Bessel formula. Its factor `1/u=c/k` is exactly the
extra decay in `(11)`. Thus `k` comparable to `c` contributes at scale `c^(-5/2)`, consistent with
`(3)`.

## CCM consequence

For the constrained source, the `m=4` exterior mode supplies the leading radial profile and the
boundary normalization is a fixed multiple of `d_1(lambda)`, with `c=2*pi*lambda^2`. Therefore the
limiting-model first row obeys

```text
sum_(k>=2)log(k)G_lambda^model(1,k)
 =O(d_1(lambda)c^(-1/2))=o(d_1(lambda)).                         (14)
```

Equation `(14)` proves that the endpoint coalescence itself does not create a gap-scale prime
charge. The exact CCM theorem now requires only stability of `(3)` under the nonzero
`sigma_4(c)^2=O(c^(-1))` phase perturbation and Dunster's exact two-parameter remainder.

## Novelty and significance verdict

The decomposition into bulk stationary phase and the Weber endpoint transform is useful for the
CCM route, but it is a direct synthesis of classical Bessel asymptotics and one-dimensional
oscillatory integration. It does not clear the parent-theory novelty gate and is classified as a
bridge.

## References

- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699.
- NIST Digital Library of Mathematical Functions, Eqs. 10.17.3 and 10.22.51.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.

## Lean decision

The formal tree has no Bessel symbol, stationary-phase, or oscillatory improper-integral
infrastructure. Formalizing this classical bridge would not certify the exact PSWF remainder. No
Lean file is added.

## Gates

- [x] exact limiting radial model isolated
- [x] bulk critical point and curvature computed
- [x] endpoint coalescence converted to a nonstationary `w=z^2` phase
- [x] uniform `c^(-1/2)k^(-2)` bound proved
- [x] logarithmically weighted first row summed
- [ ] exact nonzero-`sigma` and Dunster-remainder transfer
