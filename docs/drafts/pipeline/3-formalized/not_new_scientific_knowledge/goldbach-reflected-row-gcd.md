# The exact gcd of a reflected row residue

- **ID:** goldbach-reflected-row-gcd
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); classical finite arithmetic bridge; no novelty claim
- **Parent:** [flat prime-dilation dispersion](../../2-fully-proven/goldbach-flat-prime-dilation-dispersion.md)
- **Dependency:** [row conductor](goldbach-reflected-row-conductor.md)
- **Module:** `formal/GaloisForLFunctions/goldbach/ReflectedProductConductorGcd.lean`
- **Lean status:** Full unconditional identity verified; all three transitive closure audits pass with standard foundations only.

## Exact statement

Let c,y be positive integers, a a natural number, T,t arbitrary integers.
Put g=gcd(a,y), a₀=a/g, b=y/g, and let α,β be the actual Bézout
coefficients of a,y, so a₀α+bβ=1. Put

    A=T−cαt,   d=gcd(T,c)>0,
    B=a₀(T/d)−(c/d)t.

Then, with all gcds nonnegative and all displayed quotients integral,

    gcd(A,cb)=d gcd(B,b).                         (G)

No compatibility or coprimality premise is required. In particular,
for c=ph, a=qh, and t=T/g, this identifies the gcd of the actual
reflected-row residue with its exact conductor. It removes the Bézout
coefficient from the gcd that enters the finite Kloosterman estimate.

When gcd(T,ph)=gcd(qh,y)=1, the expression B reduces to hT(q−p).
Since gcd(h,y)=1 in that case, (G) gives gcd(A,phy)=gcd(T(q−p),y),
the source-specific identity used in the flat dispersion paper.
This specialization remains a separate Lean integration obligation.

## Dependency-closed proof [PROVED HERE]

First, for every integer v, positive c, and integer b, let e=gcd(v,c).
The identities v=e(v/e), c=e(c/e), and gcd(v/e,c/e)=1 imply

    gcd(v,cb)=e gcd(v/e,b).                       (F)

Indeed factor e out of both arguments, then remove c/e from the
second argument using coprimality with v/e. Positivity of c ensures
e>0, including when v=0.

For (G), adding cαt preserves gcd with c, so gcd(A,c)=gcd(T,c)=d.
Write T=dT₀ and c=dc₀. Cancelling d in A=T−cαt gives
A/d=T₀−c₀αt. The reduced Bézout identity proves gcd(a₀,b)=1 and

    a₀(A/d)=a₀T₀−c₀t+b c₀βt=B+b c₀βt.

Subtracting a multiple of b and then removing the unit factor a₀
shows gcd(B,b)=gcd(A/d,b). Apply (F) with v=A to obtain (G).
Every division here is justified by the actual gcd divisor. The free
integer t need not be divisible by any additional integer, and the
specialization t=T/g uses ordinary total integer division even when
the reflected row is incompatible.

## Corpus and attack audit

The existing row conductor retains the exact compatibility divisor.
The searched BVI gcd reindexing and coprime product laws do not directly
identify its residue gcd. The identity above is elementary Bézout and
Euclidean arithmetic, not a cancellation theorem or a novelty claim.
It remains valid for a=0, T=0, negative T,t, and b=1; no excluded
exception is needed. The stronger arbitrary-t identity is proved above
before Lean implementation.

## Lean certificate

The three unconditional roots in `GaloisForLFunctions.Goldbach` are:

- `gcd_product_eq_gcd_mul_quotient`
- `bezoutReflection_gcd`
- `reflectedRow_gcd_eq_reducedDeterminant`

The last root uses the actual `reflectedRowResidue` and
`reflectedRowModulus`; `reflectedRowReducedDeterminant` is the explicit
expression B specialized to c=ph, a=qh, t=T/g.

Direct final check from `formal/`:

```text
lake --old env lean GaloisForLFunctions/goldbach/ReflectedProductConductorGcd.lean
```

Exit 0, no warnings or errors. All three transitive `#print axioms`
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
No added axiom, analytic premise, hole, or increased elaboration
limit occurs. Log: `/tmp/hgt-goldbach-reflected-gcd-audit.log`.
Audit directives were removed after verification. The leaf is wired
into `goldbach/Main.lean`; no umbrella build was run.

The [nonunit rectangle decomposition](goldbach-nonunit-rectangle-decomposition.md)
is certified separately. The actual prime-pool specialization, curved
regions, and full dispersion theorem remain separate obligations.

## Log

- 2026-10-24 — Derived the unconditional residue-gcd formula and its
  factorization proof. Formalized the full identity, including its
  actual reflected-row specialization. All three roots pass direct
  leaf verification and transitive dependency audits.
