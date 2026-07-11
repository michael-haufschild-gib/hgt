# Shift-covariant pole-to-divisor transfer costs one norm unit per divisor copy

- **ID:** `ccm-shift-covariant-pole-divisor-capacity-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** the commutant theorem for the unilateral translation semigroup and elementary
  half-plane Hardy multiplier theory
- **Statement:** The unique bounded translation-covariant operator sending the incoming Euler-pole
  vector to a finite transverse divisor profile has norm at least the total divisor multiplicity.
  Hence a norm-one scalar transfer cannot carry even one full FE--Schwarz off-line pair; every
  viable CCM transfer must place the missing charge in a cutoff-dependent, noncommuting boundary
  seam or in additional channel arity.

## 1. Pole and divisor vectors

On `H=L2(0,infinity)`, let

```text
(V_hf)(t)=1_(t>=h)f(t-h),       h>=0.                   (1)
```

The incoming completed Euler pole is

```text
ell_pole(t)=2 exp(-t/2).                                 (2)
```

For a finite right-half divisor packet

```text
D={(lambda_j,m_j)}_(j=1)^r,
lambda_j=a_j+i gamma_j,       a_j>0,       m_j in N,    (3)
```

put

```text
ell_D(t)=2 sum_j m_j exp(-lambda_j t),
kappa(D)=sum_j m_j.                                     (4)
```

Both vectors belong to `H`.

## 2. Exact covariant transfer cost

Suppose `T in B(H)` commutes with every `V_h` and

```text
T ell_pole=ell_D.                                       (5)
```

Then

```text
||T||
 =||phi_D||_(H-infinity(Re z>0))
 >=kappa(D),                                            (6)
```

where

```text
phi_D(z)
 =(z+1/2) sum_j m_j/(z+lambda_j).                       (7)
```

Conversely, `(7)` is a bounded rational half-plane multiplier, so it defines the unique bounded
operator in the translation commutant satisfying `(5)`. Thus `||phi_D||_infinity` is the exact
scalar shift-covariant transport cost.

### Proof

The Laplace transform identifies `H` with the Hardy space of the right half-plane and sends `V_h`
to multiplication by `exp(-hz)`. The commutant of the full semigroup is therefore the algebra of
Hardy multipliers: there is a unique `phi in H-infinity(Re z>0)` such that

```text
L(Tf)(z)=phi(z)Lf(z),       ||T||=||phi||_infinity.      (8)
```

The two relevant transforms are

```text
L ell_pole(z)=2/(z+1/2),
L ell_D(z)=2 sum_j m_j/(z+lambda_j).                    (9)
```

Equation `(5)` forces `(7)`. Its poles lie in the open left half-plane, so `phi_D` is bounded on
the right half-plane. Along the positive real axis,

```text
lim_(x->infinity)phi_D(x)=sum_j m_j=kappa(D).           (10)
```

Taking the supremum proves `(6)`. Conversely multiplication by `phi_D` and `(9)` prove `(5)`.

## 3. Functional-equation cost

A nontrivial zeta zero in the open critical strip is not real. Indeed, for `0<s<1`, the alternating
eta representation has positive numerator and negative denominator, so `zeta(s)<0`. Schwarz
symmetry therefore pairs every right-half zero `1/2+a+i gamma` with the distinct right-half zero
`1/2+a-i gamma`, with the same multiplicity. Every nonempty conjugation-closed right-half packet
satisfies

```text
kappa(D)>=2.                                            (11)
```

Combining `(6)` and `(11)` gives

```text
T commutes with all V_h,
||T||<=1,
T ell_pole=ell_D
  -> D is empty.                                        (12)
```

Thus a scalar norm-one translation-covariant pole-to-divisor transfer cannot represent a
hypothetical off-line Xi quartet.

## 4. Positive CCM carrier law

The theorem does not kill the CCM route, because the semilocal aperture cutoff deliberately breaks
translation covariance. It identifies where a successful construction is forced to live:

```text
one incoming pole channel of capacity 1
  + full FE--Schwarz transverse multiplicity at least 2
  -> cutoff-dependent noncommuting seam,
     extra channel arity,
     or a singular graph relation.                      (13)
```

The current Xi graph realizes the third option, while its boundary projections realize the first.
The relevant noncommuting carrier is precisely the cutoff interface whose density is

```text
limsup_(a->0+) 1/(2a)||[P_a,D_Xi]||_(S_2,ext)^2.        (14)
```

Consequently the four-unit theorem cannot be replaced by a global scale-invariant Schur
multiplier. Every successful proof must control the aperture seam itself. This is the positive
form of the obstruction: transverse multiplicity is paid by boundary noncommutation.

The result is standard Hardy commutant theory and is therefore a bridge, not new scientific
knowledge.

## Gates

- [x] unique shift-covariant multiplier computed
- [x] exact operator-norm cost identified
- [x] multiplicity lower bound proved
- [x] FE--Schwarz pair costs at least two norm units
- [x] cutoff/noncommuting seam forced positively
- [ ] construct the source-selected cutoff transfer
- [ ] prove its four-unit boundary density
- [ ] RH
