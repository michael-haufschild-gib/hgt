# A derived inverse limit of acyclic finite fibers cannot create the zeta defect

- **ID:** `acyclic-finite-fibers-derived-limit-zero`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); route no-go
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** standard derived-category functoriality and the finite prime Koszul proposal
- **Statement:** After specialization at a fixed parameter, an inverse system of acyclic complexes
  is a diagram of zero objects in the derived category, so its derived inverse limit is zero.  In
  particular, the proposed zeta defect cannot be ordinary `R^1 lim` cohomology created from finite
  specialized complexes `[C --(1-p^(-s))--> C]` that are all acyclic.

## The theorem

Let `(C_N)` be an inverse sequence in a derived category and assume

```text
H^q(C_N)=0
```

for every `N` and every degree `q`.  Then every `C_N` is isomorphic to the zero object.  The whole
diagram is therefore isomorphic to the zero diagram, and functoriality gives

```text
R lim_N C_N = 0.                                       (1)
```

Equivalently, whenever the standard derived-limit spectral sequence applies,

```text
E_2^(p,q)=R^p lim_N H^q(C_N)
  => H^(p+q)(R lim_N C_N),                              (2)
```

its `E_2` page is identically zero.

## Application to the raw finite prime complexes

For a prime `p`, put

```text
K_p(s)=[C --(1-p^(-s))--> C].
```

If `0<Re(s)<1`, then `|p^(-s)|<1`, so `1-p^(-s)!=0`.  The differential is an isomorphism and
`K_p(s)` is contractible.  Every finite tensor product over a prime set is therefore contractible.
For any cofinal sequence of finite prime sets, equation (1) applies after specialization at `s`.

Thus zeta zeros cannot arise as ordinary `R^1 lim` cohomology of those already-specialized finite
fibers.

## The only legitimate escape

A nonzero defect can instead measure failure of specialization to commute with a global completion:

```text
Cone(
  L delta_s^*(R lim_P M_P)
    ->
  R lim_P(L delta_(P,s)^* M_P)).                        (3)
```

If the finite specialized terms on the right are acyclic, any defect in (3) belongs entirely to a
base-change, nonclosed-range, singular-completion, or determinant-discontinuity failure on the
left.  Finite-stage perfectness and polarization do not automatically pass through such a failure.

This is a squeeze, not a construction:

- if completion is regular enough for specialization and determinant to commute with the limit,
  the defect vanishes;
- if completion is singular enough to create the defect, its support and positivity require new
  theorems and cannot be inherited formally from finite stages.

## Route consequence

The raw pro-polarization mechanism in the retired prime-aperture card is invalid under the standard
derived interpretation.  A live route must define the singular completion or closed operator first
and prove its base-change defect directly.  Calling the defect `lim^1` does not supply it.

## Gates

- [x] abstract zero-diagram argument proved
- [x] raw prime complexes proved contractible in the strip
- [x] legitimate base-change escape stated without claiming it exists
- [ ] no Lean formalization planned; this is standard derived-category infrastructure
