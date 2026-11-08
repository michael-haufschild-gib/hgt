# Discriminant covers as signed arithmetic counts

- **ID:** RIAC-discriminant-cover
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [RIAC](renormalized-intersection-arithmetic-counts.md)
- **Statement:** Construct the actual finite-field cover `y²=disc(f)` and derive its point count independently from Frobenius orientation and normal-basis counts.

## Mathematical target

For an odd finite field `F` of cardinality `q`, define
`D_n(F)={(f,y): f monic of degree n, y∈F, y²=disc(f)}`.
The count is independent of Möbius signs. Pellet's formula predicts
`#D_n=q^n+(-1)^n Σ_(deg f=n) μ(f)`, hence `#D_0=2`,
`#D_1=2q` and `#D_n=q^n` for `n≥2`.
The root-discriminant double cover supplies the orientation character;
Frobenius cycles supply the number of irreducible factors.

## Proof obligations

1. Actual square-root fibres, including the ramified fibre over zero.
2. Discriminant character equals Frobenius permutation sign.
3. Frobenius cycles correspond to irreducible factors; derive Pellet's formula.
4. Compare with independently counted Frobenius-stable alternating orbits.
   The existing polynomial Möbius sum remains a separate calibration.
5. Direct Lean audit and transitive axiom check of the actual count.

## Relation to integer local indices

The governing target remains `Σ_p index_p(N)=1−M(N)` with bound
`Oε(N^(1/2+ε))`. This finite-field count calibrates a sign-producing
arithmetic mechanism. No compatible discriminant family or Frobenius action
on the integer cutoff complex has been constructed. An arbitrary permutation
encoding factor parity supplies no estimate. Neither this calibration nor
its point-count identity proves integer cancellation.

## Literature and novelty boundary

Pellet's identity and its Frobenius proof are classical; see
[Afshar, §§1–2](https://arxiv.org/html/2001.05641v1).
The proposed contribution is a dependency-closed formal construction of the
actual cover and its arithmetic signed-count comparison, not a new version
of Pellet's formula. The number-field construction in §3 chooses auxiliary
cyclic extensions; it supplies no uniform cutoff count or cancellation bound.

## Independent count mechanism to formalize

For `n≥2`, take the alternating group `G=A_n` acting on ordered root tuples
in `E^n`, where `E/F` is the finite extension of degree `|G|`.
Frobenius commutes with the action. Count its fixed orbits in `E^n/G`.
Twisted Burnside reduces this count to
`|G|⁻¹ Σ_(g∈G) #{x:Frob(x)=g·x}`. A cycle of length `d` contributes
`q^d` choices, since `d` divides `|G|`; consequently each summand is `q^n`.
This would prove the point count without using a Möbius cancellation theorem.

The comparison must retain collisions: a repeated coordinate gives an odd
stabilizer and one alternating orbit; distinct roots give two alternating
orbits, fixed or exchanged according to the Frobenius sign. The intended
bridge identifies these fixed orbits with the discriminant-cover fibres.

The [independent twisted orbit count](../3-formalized/riac-independent-frobenius-orbit-counts.md)
is formalized. The collision-aware cover comparison remains open.
The [formalized normalization count](../3-formalized/riac-finite-field-orientation-counts.md)
constructs residue-field trace-discriminant fibres; its aggregate count
uses the already derived polynomial Möbius sums. That is a sign-retaining calibration, not an independent cancellation
proof. The usual polynomial-discriminant comparison remains separate.


The formalized normal-basis construction supplies a direct bijection for each
twist: `x_i=Σ_σ a_(σ⁻¹·i) σ(θ)`, with unrestricted `a∈F^n`.
The Galois action on labels is derived by sending Frobenius to the chosen
permutation; its order divides the extension degree. Both this bijection
and the transporter proof of the orbit count have direct Lean audits.

## Signed orbit refinement

For a Frobenius-stable root orbit with transporter `g` and stabilizer `H`,
the natural orientation index is `|H|⁻¹ Σ_(h∈H) sign(gh)`.
A repeated root supplies an odd transposition in `H`, forcing this index
to vanish. For distinct roots it is the Frobenius sign.
[Gadish, Definition 1.1 and Corollary 1.4](https://arxiv.org/html/1703.01710v2)
places this stabilizer average in a general ramified-cover trace formula.
For the sign character its polynomial average is zero in degree at least two.

The [direct signed construction](../3-formalized/riac-finite-field-signed-orbits.md)
now proves this orbit cancellation through actual transporter counts and
normal-basis bijections. Every local weight is `−1`, `0` or `1`; repeated
coordinates vanish and distinct coordinates retain Frobenius sign.
The Vieta/factorization comparison and the integer cutoff comparison remain
additional obligations.

## Vieta comparison

Use the extension of degree `n!` so that every monic degree-`n` polynomial
splits: each irreducible factor has degree `d≤n`, hence its residue field
embeds in that extension. Ordered roots then define a Frobenius-stable
permutation orbit. The root product makes this map injective; equality of
the independently proved cardinalities `q^n` makes it bijective.

The remaining cover comparison is `disc(f)=V(roots)^2`, with Vandermonde
`V` transforming by permutation sign. This route does not use a polynomial
Möbius degree sum. Neither comparison is yet claimed as formalized.

An explicit intermediate cover is
`{(f,y): f monic of degree n, y∈F, (ιy)²=V(x_f)²}`,
where `x_f` orders the roots in the common extension and `ι:F→E`.
Permutation sign makes the equation independent of that ordering.
Collisions give the single point `y=0`; distinct roots should give two or
zero points according to Frobenius orientation. Proving this fibre count
and summing the independent orientation weights would give `q^n` directly.
The existing integral symmetric discriminant polynomial provides a route
to coefficient equations; identification with `Polynomial.discr` remains
a separate obligation.
