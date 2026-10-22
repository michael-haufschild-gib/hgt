# Euler defect amplifies every noncentral Carleman pole and one source germ suffices for RH

- **ID:** `suzuki-carleman-jump-euler-defect-pole-rigidity`
- **Stage:** 3-formalized
- **Type:** THEOREM / FRONTIER REDUCTION / RH DISCHARGE CONNECTOR
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:** `suzuki-even-carleman-pole-carrier`,
  `suzuki-anchored-euler-wronskian-escape-elimination`
- **Lean:** `GaloisForLFunctions.RHTower.Suzuki.SuzukiCarlemanJumpEulerDefectWeld`
- **RH used:** no
- **Computation used:** no

## Corrected frontier

For two distinct actual Suzuki shifts below the finite-aperture floor, the corpus constructs the
even sewn characteristic `P`, odd sheet-jump carrier `C_odd`, and exterior quotient

```text
m_ext(z)=-C_odd(z)/P(z).
```

The finite Donoghue quotient cannot equal `m_ext` at fixed aperture: their pole divisors differ.
This falsifies handover Conjecture 41-A in its literal form. Requiring direct locally uniform
convergence of the finite functions to `m_ext` also carries a useless linear-endpoint escape
ambiguity.

The degree-one Euler defect

```text
E[f](z)=z f'(z)-f(z)                                  (1)
```

removes exactly that ambiguity. The theorem below proves it does not weaken divisor detection.

## Theorem A: exact Euler pole amplification `[LEAN-PROVED]`

Let `f` be meromorphic at `z_0!=0` with pole order `k>=1`, so

```text
ord_(z_0)(f)=-k.
```

Then

```text
ord_(z_0)(E[f])=-k-1.                                 (2)
```

### Proof

Write the local normal form

```text
f(w)=(w-z_0)^n g(w),  n=-k<0,
```

where `g` is analytic and `g(z_0)!=0`. Differentiation and collection of the lowest power give

```text
E[f](w)=(w-z_0)^(n-1) G(w),                           (3)

G(w)=w[n g(w)+(w-z_0)g'(w)]-(w-z_0)g(w).
```

At the center,

```text
G(z_0)=z_0 n g(z_0)!=0,                               (4)
```

which proves `(2)`. The hypothesis `z_0!=0` is necessary: the Euler vector field vanishes at the
origin, where pole order can be preserved instead of raised.

Lean theorem:

```text
meromorphicOrderAt_suzukiEulerDefect_eq_sub_one
```

## Theorem B: the admissible jump defect has an exact double Xi pole `[LEAN-PROVED]`

At any Xi zero `z_0` away from the real source divisor `P`, the previously proved exterior
tomography and analytic triangle correction give

```text
ord_(z_0)(m_ext)=-1.                                  (5)
```

Every nonreal point is nonzero, so Theorem A yields

```text
ord_(z_0)(E[m_ext])=-2.                               (6)
```

This strengthens the universal coefficient law. The Euler transform annihilates arbitrary
linear Nevanlinna escape but turns every hypothetical nonreal Xi pole into a double pole.

Lean theorems:

```text
meromorphicOrderAt_suzukiAffineSewnExteriorWeylQuotient_eq_neg_one
meromorphicOrderAt_suzukiEulerDefect_affineSewnExteriorWeylQuotient_eq_neg_two
```

## Theorem C: one analytic source germ propagates through the domain `[LEAN-PROVED]`

Let `U` be preconnected, `f` meromorphic on `U`, and `D` analytic on `U`. If at one `u in U`

```text
f = D  as pointed germs at u,                         (7)
```

then

```text
ord_z(f)>=0  for every z in U.                        (8)
```

Indeed, `f-D` has infinite meromorphic order at `u`. The infinite-order locus of a meromorphic
function is clopen in its domain. Preconnectedness makes it the entire domain, so `f` and `D`
agree as pointed germs everywhere and `f` inherits nonnegative order.

Lean theorem:

```text
meromorphicOrderAt_nonneg_of_analytic_source_germ_weld
```

## Theorem D: source-germ Euler weld proves RH `[LEAN-PROVED]`

Suppose the actual two-shift source data satisfy Suzuki's entire/real-zero characteristic laws.
It is enough to construct one function `D_src` analytic on the upper half-plane and one upper
point `u` such that

```text
E[m_ext] = D_src  as pointed germs at u.               (9)
```

Theorem C makes `E[m_ext]` pole-free throughout the upper half-plane. Equation `(6)` excludes
every upper nonreal Xi zero; centered Xi evenness excludes every lower one. Therefore RH follows.

Lean theorem:

```text
riemannHypothesis_of_suzukiAffineSewnExteriorWeylEulerDefect_source_germ_weld
```

The weaker global-analyticity connector is also formalized as

```text
riemannHypothesis_of_suzukiAffineSewnExteriorWeylEulerDefect_analytic_offReal.
```

## Scientific tests

1. **Fixed finite quotient mismatch:** passed. The theorem never identifies a finite Donoghue
   quotient with `m_ext`; it identifies only an analytic source limit of Euler defects.
2. **Endpoint escape:** passed. Adding `c z` changes neither side of `(9)`.
3. **Pole cancellation:** passed. Exact order `(6)`, not a residue heuristic, rules out hidden
   cancellation at every Xi multiplicity.
4. **Origin:** passed. The pole-amplification theorem explicitly excludes `0`; RH exclusion uses
   only nonreal points, hence never needs the false central statement.
5. **Global convergence:** removed. One pointed germ in the unconditional high half-plane is
   enough after constructing analytic `D_src`.
6. **Source circularity:** still active. `D_src` must be built from finite deficiency measures and
   prime--Gamma screw data without Xi-zero locations or assumed Pick positivity.

## Exact open core after theorem

Finite Donoghue Euler kernels vanish at both compactified spectral endpoints and are uniformly
bounded on every compact upper-half-plane set after compactification. Thus weak-* subsequential
limits of the probability measures are natural analytic candidates for `D_src`; linear endpoint
mass cannot survive this observable. The remaining frontier is one local source identification:

> Construct such an analytic subsequential defect `D_src` from actual finite Suzuki deficiency
> measures and prove, on one unconditional high-half-plane neighborhood, that its homogeneous
> common-gauge Euler--Wronskian is the Euler defect of the affine-sewn Carleman sheet jump.

No uniqueness of the subsequential limit, no anchor reconstruction of `m_ext`, no global
characteristic convergence to Xi, and no prior Herglotz positivity are required for RH once this
germ identity is proved.

## Novelty boundary

Meromorphic local normal forms, Euler operators, identity principles, and normal families are
classical. Internal corpus search found the endpoint-escape Euler--Wronskian theorem and the
Carleman pole carrier separately, but no pole-amplification law `(2)`, exact double-pole
specialization `(6)`, or one-germ RH discharge `(9)`. Candidate novelty is this source-specific
synthesis. No priority claim is made.

