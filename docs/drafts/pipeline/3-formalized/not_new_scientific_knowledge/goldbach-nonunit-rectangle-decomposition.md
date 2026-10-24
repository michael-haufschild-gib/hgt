# Exact nonunit decomposition of a modular product rectangle

- **ID:** goldbach-nonunit-rectangle-decomposition
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); classical finite arithmetic bridge; no novelty claim
- **Parent:** [flat prime-dilation dispersion](../../2-fully-proven/goldbach-flat-prime-dilation-dispersion.md)
- **Dependency:** [finite rectangle completion](goldbach-modular-inverse-rectangle-completion.md)
- **Module:** `formal/GaloisForLFunctions/goldbach/ModularProductRectangleDecomposition.lean`
- **Lean status:** Full finite decomposition, completion error, and area-rounding bounds verified; all seven closure audits pass with standard foundations only.

## Exact statement

For a positive integer M and arbitrary natural A,H,B,K,c, let C count

    (m,n) ∈ (A,A+H] × (B,B+K],  mn≡c (mod M).

For each positive divisor g of gcd(M,c), put

    M_g=M/g,   L_g=floor((A+H)/g)−floor(A/g),
    U_g={floor(A/g)+1,...,floor((A+H)/g)},
    V={B+1,...,B+K}.

Let C_g count the actual pairs (u,n)∈U_g×V with gcd(u,M_g)=1
and un≡c/g modulo M_g. Then

    C=Σ_(g|gcd(M,c)) C_g.                        (D)

More strongly, the original finite pair set is the disjoint union of
the images of these actual unit rectangles under (u,n)↦(gu,n).

Define the exact discrete main term

    J=Σ_g φ(M_g)L_g K/M_g².

The certified finite rectangle estimate gives

    |C−J| ≤ Σ_g [24 τ(M_g) M_g^(2/3) δ_g^(1/3)
                         (1+log M_g)²
                 + τ(M_g)(1+log M_g)(L_g δ_g+K)/M_g],

where δ_g=gcd(M_g,(c/g) mod M_g). All endpoints, empty intervals,
zero targets, and modulus one are included. There is no hypothesis
that a first coordinate or target is a unit.

There is also an area main term with an explicit rounding budget. Put

    density=Σ_g φ(M_g)/(M M_g),
    E_round=K Σ_g φ(M_g)/M_g².

Then `|J−density·H·K|≤E_round`; adding this to the displayed
completion bound gives the error against the area H·K. Thus the
first-coordinate floors can be removed with their full cost paid.

## Dependency-closed proof [PROVED HERE]

For an original pair put g=gcd(m,M)>0. Since M divides mn−c,
the common divisor g divides c, hence g|gcd(M,c). Write m=gu,
M=gM_g, c=gc_g. The gcd factorization gives gcd(u,M_g)=1.
Cancelling nonzero g in the divisibility M|(mn−c) gives
M_g|(un−c_g), exactly the reduced modular product equation.

For positive g the integer inequalities A<gu≤A+H are equivalent
to floor(A/g)<u≤floor((A+H)/g). Thus the first coordinate has
exactly L_g indexed positions. The second coordinate is unchanged.

Conversely a pair in a reduced unit rectangle maps to an original
pair. The same gcd factorization shows gcd(gu,M)=g. This identifies
its divisor label uniquely, proving disjointness of distinct images.
Each map is injective because g>0. Finite cardinality now proves (D).

Subtract the sum of the certified unit-rectangle main terms from
(D). Apply the finite triangle inequality and the certified bound
to every summand. This proves the stated complete error bound;
no analytic or asymptotic input is added.

For the area corollary, the exact count of multiples in (A,A+H]
gives `|L_g−H/g|<1`. The existing interval-multiples theorem proves
this by subtracting the two floor sandwiches. Since gM_g=M,

    φ(M_g)L_g K/M_g²−φ(M_g)HK/(M M_g)
      =φ(M_g)K/M_g² · (L_g−H/g).

The coefficient is nonnegative. Sum the absolute-value bound over
g and apply the triangle inequality once more. This proves both
the area error and its final combination with completion.

## Scope and attack audit

The divisor g=M and c=0 are essential: they must not be silently
discarded by a unit-only argument. The quotient modulus can be one;
the existing rectangle theorem already includes it. The main term
retains exact floor lengths, so no endpoint rounding error is hidden.
The exact rounding corollary pays the replacement by real lengths;
treating curved regions remains a separate quantitative obligation.
This is elementary finite
arithmetic and a classical bridge, not a novelty or cancellation claim.

## Lean certificate

The seven unconditional roots in `GaloisForLFunctions.Goldbach` are:

- `modularProductUnitPairs_mem_iff`
- `modularProductPairLift_injective`
- `modularProductRectanglePairs_eq_biUnion`
- `modularProductRectanglePairs_card`
- `modularProductRectanglePairs_error_le`
- `modularProductRectangleMain_area_error_le`
- `modularProductRectanglePairs_area_error_le`

The source is the actual finite set `modularProductRectanglePairs`.
The reduced sets are `modularProductUnitPairs`; their injective lifts
preserve both integer coordinates and have disjoint gcd labels.
`modularProductRectangleMain` retains the floor lengths, while
`modularProductRectangleDensity` and `modularProductRectangleRounding`
give the area density and its complete endpoint cost.

Direct final check from `formal/`:

```text
lake --old env lean GaloisForLFunctions/goldbach/ModularProductRectangleDecomposition.lean
```

Exit 0, no warnings or errors. All seven transitive `#print axioms`
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
No added axiom, analytic premise, hole, or increased elaboration
limit occurs. Log: `/tmp/hgt-goldbach-nonunit-rectangle-audit.log`.
Audit directives were removed after verification. The leaf is wired
into `goldbach/Main.lean`; no umbrella build was run.

Curved-region bracketing, arithmetic averaging, both mixed terms,
the full dispersion estimate, and signed cancellation remain separate
obligations.

## Log

- 2026-10-24 — Derived the complete nonunit decomposition, disjointness,
  and summed quantitative error. Formalized the exact decomposition,
  summed completion bound, and complete area-rounding cost. All seven
  roots pass direct leaf verification and transitive dependency audits.
