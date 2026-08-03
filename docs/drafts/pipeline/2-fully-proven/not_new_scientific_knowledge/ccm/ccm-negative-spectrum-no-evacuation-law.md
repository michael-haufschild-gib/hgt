# Negative restricted-Weil spectrum cannot evacuate cofinally

- **ID:** `ccm-negative-spectrum-no-evacuation-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** nested Rayleigh quotients and Suzuki's compact generalized eigenvalue
  formulation
- **Statement:** The lowest restricted-Weil floor is nonincreasing with aperture. Once it is
  negative, its negative magnitude stays uniformly bounded away from zero at every larger
  aperture. Hence a cofinal floor limit zero means that negative spectrum never appears.

## Nested-floor theorem

Let

```text
epsilon_0(a)
 =inf{QW(v,v)/||v||_2^2:
      0!=v in H01(-a,a)}.                                      (1)
```

If `0<a<=b`, zero extension embeds `H01(-a,a)` isometrically into `H01(-b,b)` and preserves the
global Weil form. Therefore

```text
epsilon_0(b)<=epsilon_0(a).                                     (2)
```

Consequently, if `epsilon_0(a_0)=-delta<0`, then

```text
epsilon_0(b)<=-delta
for every b>=a_0.                                                (3)
```

Equivalently,

```text
n(a)=max(0,-epsilon_0(a))                                       (4)
```

is nondecreasing. In particular,

```text
epsilon_0(a_j)->0 for some a_j->infinity
 -> epsilon_0(a)>=0 for every a>0.                              (5)
```

The converse implication follows once the known prolate trial vectors give
`limsup_(a->infinity)epsilon_0(a)<=0`.

## Compact-kernel formulation

Suzuki proves that, for `u=Dv` in the zero-mean space,

```text
QW(v,v)=<G_a u,u>,
||v||_2^2=<K_a u,u>,
K_a=(-Delta_N)^(-1)>0.                                         (6)
```

Thus

```text
epsilon_0(a)=inf_(u!=0)<G_a u,u>/<K_a u,u>,                    (7)
```

where both `G_a` and `K_a` are compact operators with continuous kernels. Define the repair
threshold

```text
eta_a=inf{eta>=0:G_a+eta*K_a>=0}.                               (8)
```

Then

```text
eta_a=max(0,-epsilon_0(a)).                                    (9)
```

Equations `(2)`--`(4)` show that `eta_a` is nondecreasing. Therefore

```text
eta_(a_j)->0 cofinally <-> eta_a=0 for every a>0.               (10)
```

There is no nontrivial mechanism in which a genuine negative spectral component shrinks away as
the aperture grows.

## Positive CCM interpretation

The direct CCM route must have the form

```text
G_a>=0 for every finite aperture a,
and prolate near-radical vectors force epsilon_0(a)->0 from above. (11)
```

The first clause is the full Weil positivity content; the second clause explains the logarithmic
boundary layer and the small CCM eigenvalues. Finite determinants and source approximations can
address the second clause but cannot weaken the first.

## Novelty and significance verdict

The theorem is elementary domain monotonicity plus Suzuki's published generalized eigenvalue
identity. It is a route bridge, not new scientific knowledge.

## References

- M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096, Sections 3 and 8.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.

## Lean decision

The formal tree does not represent the nested restricted-Weil domains or their spectral floors.
An abstract infimum-monotonicity wrapper would not certify the analytic embedding, so no Lean file
is added.

## Gates

- [x] nested-domain floor monotonicity proved
- [x] negative-part monotonicity proved
- [x] compact repair threshold identified
- [x] evacuation mechanism excluded
- [x] positive no-negative-birth formulation isolated
