# The RH-facing exceptional divisor carries Hardy--Green capacity, not Fubini--Study area

- **ID:** `ht-exceptional-divisor-hardy-green-metric`
- **Stage:** 3-formalized
- **Type:** `[THEOREM] [GENERAL HT METRIC SELECTION] [NO-GO WITH POSITIVE SUCCESSOR]`
- **Scientific status:** `[FORMALIZED IN LEAN] [SOURCE-INDEPENDENT LOCAL MODEL] [NOT RH]`
- **Parents:**
  - `../1-in-progress/source-polarized-laurent-pluecker-tangent-ward-law.md`;
  - `../1-in-progress/ht-capacity-ward-holonomy-rh.md`;
  - `../3-formalized/not_new_scientific_knowledge/infinitesimal-euler-leakage-cauchy-energy-threshold.md`;
  - `new_scientific_knowledge/projective-horizon-solomon-tits-topological-charge.md`.

## 1. Two inequivalent positive metrics on a divisor point

Put the critical line at the boundary of the transverse half-plane and let

```text
z=a+i gamma,                  0<a<1/2.                    (1)
```

The coefficient-two anti-causal Cauchy vector attached to this point is

```text
k_z(t)=2 exp(-conj(z)t),      t>0.                        (2)
```

Its Hardy--Green energy is

```text
E_HG(z)=||k_z||_2^2
       =4 integral_0^infinity exp(-2at)dt
       =2/a>4.                                           (3)
```

For a finite divisor packet `D=sum_j m_j[z_j]`, the corresponding energy is the positive
Cauchy--Gram form

```text
E_HG(D)
 =4 sum_(j,k) m_j m_k
    (a_j+a_k)/[(a_j+a_k)^2+(gamma_j-gamma_k)^2].          (4)
```

This is exactly the finite off-line Cauchy energy already formalized in
`RHTower/FiniteOfflineCauchyEnergy.lean`.

Ordinary divisor geometry assigns a completely different scale.  For the real point `z=a`, use
the Cayley coordinate

```text
w(a)=(a-1)/(a+1),
J(a)=-log|w(a)|=log[(1+a)/(1-a)].                         (5)
```

`J(a)` is the one-point Jensen/Blaschke counting charge in the disk.  As `a` tends to zero,

```text
J(a)->0,                    E_HG(a)->infinity.            (6)
```

Indeed `J(a)=2a+O(a^3)`, so more sharply

```text
E_HG(a) J(a)->4.                                         (7)
```

Thus the two metrics are asymptotic duals at the exceptional boundary.

## 2. No-go theorem

There is no constant `C` and no neighborhood `0<a<delta` for which

```text
E_HG(a)<=C J(a).                                         (8)
```

The right side tends to zero while the left side diverges.  Consequently none of the following
can by itself deliver the RH four-unit estimate:

- the ordinary Fubini--Study area of a projective section;
- the Chern form of its determinant line;
- Poincare--Lelong divisor mass;
- a Nevanlinna/Jensen counting bound with its usual boundary weight.

This kills the ordinary exceptional Gauss--Codazzi interpretation.  Its second fundamental form
controls a derivative of a section, whereas the RH current is its logarithmic derivative and is
singular at the section's divisor.

## 3. Positive HT successor

The correct geometric object is the **dual Hardy--Green capacity form** on the exceptional corona
conormal.  It is characterized locally by the reproducing kernel

```text
K(z,w)=4/(z+conj(w)),                                    (9)
```

whose real quadratic form is `(4)`.  This is not an arbitrary replacement metric:

1. the source Laurent seam produces a negative-mode conormal rather than an ordinary divisor
   cycle;
2. the Hardy/Laplace polarization realizes that conormal by `(2)`;
3. the general HT capacity--innovation theorem computes the norm of a boundary conormal as the
   supremum of its finite inverse-Gram response capacities;
4. reflection identifies the opposite Laurent half, while the Steinberg apartment class supplies
   the cofinal orientation needed to compare finite packets.

Hence an RH-bearing HT Hodge theorem must be a **Green--Hodge theorem for the corona conormal**,
not a positivity theorem for the scalar determinant line.

## 4. Revised bold conjecture

> **[CONJECTURE -- EXCEPTIONAL HT GREEN--HODGE DOMINATION.]**  For a regular source-polarized
> Laurent HT object, the source capacity form on the critically normalized Pluecker tangent
> extends to the deformation-to-the-normal-cone.  Its exceptional transgression into the negative
> Laurent corona is closable, and the induced Hardy--Green capacity is no larger than the source
> tangent capacity.

For the squarefree Euler--Gamma source the conjectural inequality is exactly

```text
E_HG(P_anti Q_sq)<=||chi_sq^crit||^2=4.                  (10)
```

The left side is source-defined before a principal-part expansion.  After the proved identity
`P_anti Q_sq=ell_E`, equation `(10)` is the Ward estimate.  A strict right-half Xi zero would
contribute `(3)`, strictly more than four, and is therefore impossible.

This is stronger and more precise than the discarded ordinary Gauss--Codazzi statement.  The
open theorem is now a comparison of two independently constructed positive capacity forms:

```text
critical Pluecker/Fisher capacity
  -> exceptional Laurent-corona transgression
  -> Hardy--Green divisor capacity.                       (11)
```

## 5. Falsifier and positive failure invariant

The conjecture fails if the source-derived exceptional transgression is nonclosable, or if one
finite Cauchy response matrix

```text
[[G_P,r_P],[r_P^*,4]]                                    (12)
```

has a negative direction.  Either failure produces a nontrivial general HT invariant: the
**exceptional Green-capacity defect**, namely the negative part of `(12)` along the cofinal
corona clock.  This measures exactly how much logarithmic-divisor energy is created beyond the
available Pluecker tangent capacity.

## Gates

- [x] identify the coefficient-two one-point Hardy--Green energy
- [x] identify the finite divisor energy with the positive Cauchy Gram form
- [x] prove ordinary Jensen charge vanishes while Hardy--Green energy diverges
- [x] kill ordinary Fubini--Study/Chern/Poincare--Lelong domination
- [x] identify the asymptotically dual product constant four
- [x] state the source-pure Green--Hodge successor with a finite PSD falsifier
- [x] formalize the one-point energy, three boundary limits, and no-domination theorem in `RHTower/ExceptionalDivisorHardyGreenMetric.lean`
- [x] direct leaf build and axiom audit pass; theorem dependencies are only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] construct the exceptional Laurent-corona transgression
- [ ] prove positivity of every augmented response matrix
- [ ] four-unit Ward estimate
- [ ] RH
