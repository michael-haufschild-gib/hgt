# The exact conductor of a reflected product row

- **ID:** goldbach-reflected-row-conductor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); classical finite arithmetic bridge; no novelty claim
- **Parent:** [flat prime-dilation dispersion](../../2-fully-proven/goldbach-flat-prime-dilation-dispersion.md)
- **Dependency:** [determinant coordinates](goldbach-reflected-product-determinant.md)
- **Module:** `formal/GaloisForLFunctions/goldbach/ReflectedProductConductor.lean`
- **Lean status:** Full compatibility, conductor, uniqueness, and bounded classification verified; all five transitive closure audits pass with standard foundations only.

## Exact statement

Let p,h,y be positive integers, q a natural number, and T,u arbitrary
integers. Put a=qh, g=gcd(a,y)>0, b=y/g. Let α,β be the actual integer
Bézout coefficients with aα+yβ=g. Define

    s₀=α(T/g),  A=T−phs₀,  L=phb>0.

The integer division T/g is total; the statement itself retains the
necessary condition g|T. Then

    ∃r,z∈ℤ: h|r, u+pr=T, yz+qr=T
      ↔ g|T and u≡A (mod L).                      (C)

Both r and z are unique when they exist. Thus the exact conductor is
ph·y/gcd(qh,y), with no coprimality premise and no omitted nonunit row.

For arbitrary integer endpoints X,R, set D=T(q−p). Adding the actual
bounds 0<r≤R and X<z≤2X on the left of (C) is exactly equivalent to
adding

    0<T−u≤Rp,
    D+pyX<qu≤D+2pyX                              (B)

on the right. All equalities and inequalities are integer statements.
No division of the curved boundaries is needed.

## Paper proof [PROVED HERE]

### The complete linear congruence

For every natural a and positive y, write g=gcd(a,y), a₀=a/g, b=y/g.
The actual Bézout coefficients satisfy a₀α+bβ=1, by dividing
aα+yβ=g by the nonzero g. For every integer s,T,

    as≡T (mod y)
      ↔ g|T and s≡α(T/g) (mod b).                 (L)

Forward, write T−as=yk. Since g divides a and y, it divides T.
Writing t=T/g, cancel g to obtain t−a₀s=bk. Then

    s−αt=b(βs−αk).

Conversely, if g|T and s−αt=bℓ, the same Bézout identity gives

    t−a₀s=b(βt−a₀ℓ).

Multiplying by g gives y|(T−as). This proves (L) for all a,
including a=0, and all integer T, including negative targets.

### The reflected row

If r=hs, the second row equation gives qhs≡T modulo y. Applying
(L) gives g|T and s=s₀+bk for some integer k. The first equation
then gives u=A−Lk, proving (C) forward.

Conversely, write u−A=Lk, set s=s₀−bk and r=hs. Equation (L)
produces an integer z with yz=T−qhs. The definition of A and L gives
u+pr=T. Nonzero p makes r unique from the first equation; nonzero y
then makes z unique from the second.

For the bounds, T−u=pr and qu−D=pyz. Both p and py are positive.
Multiplication by them therefore carries the two intervals exactly to
(B), in both directions. This proves the bounded classification.

### The actual prime-dilation rows

In the flat dispersion source, p,q are distinct primes not dividing T,
h is one of 1,p,q,pq, and y is the actual second factor. Hence qh is
coprime to T. The required compatibility g|T forces g=1. Thus the
conductor becomes phy and the excluded rows are precisely those with
nontrivial gcd(y,qh). This is an arithmetic deduction from the selected
prime pool, not an analytic estimate.

The remaining gcd identity for the residue in the flat dispersion
paper uses A≡T modulo ph and qA≡D modulo y. Together with the source's
coprimalities these give gcd(A,phy)=gcd(D,y). Its Lean integration,
the curved-region discrepancy, and the averaged row density remain
separate obligations.

## Corpus audit

The inspected BVI `ChineseRemainderBezoutPeriodicityAndSawtoothDefect`
module gives exact successor-incidence counts on coprime periods. It
does not directly state (C), which retains a noncoprime linear-congruence
compatibility divisor and its quotient conductor.
`HTGeometry/HolomorphicPoincareSeries.lean` uses the actual
`Int.gcd_eq_gcd_ab` identity; its elementary Bézout construction supplies
the coefficient convention used above. No analytic theorem from the
Poincaré-series module is needed.

## Lean certificate

The five unconditional roots in `GaloisForLFunctions.Goldbach` are:

- `linearCongruence_reduced_bezout`
- `linearCongruence_iff_gcd_and_residue`
- `reflectedRow_iff_conductor`
- `reflectedRow_existsUnique_iff_conductor`
- `reflectedRow_bounded_iff_conductor`

Direct final check from `formal/`:

```text
lake --old env lean GaloisForLFunctions/goldbach/ReflectedProductConductor.lean
```

Exit 0, no warnings or errors. All five transitive `#print axioms`
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
The two reduced-gcd helpers and the modulus cast are included in
these closures. No added axiom, analytic premise, hole, or increased
elaboration limit occurs. Log:
`/tmp/hgt-goldbach-reflected-conductor-audit.log`.
Audit directives were removed after verification. The leaf is wired
into `goldbach/Main.lean`; no umbrella build was run.

The [universal residue-gcd identity](goldbach-reflected-row-gcd.md) is
certified separately. The prime-pool specialization, curved-region
estimate, and averaged row density remain outside this certificate.

## Log

- 2026-10-24 — Derived the full compatibility divisor and quotient
  conductor, retaining both range endpoints. Formalized the complete
  classification and uniqueness; all five roots pass direct leaf
  verification and transitive dependency audits.
