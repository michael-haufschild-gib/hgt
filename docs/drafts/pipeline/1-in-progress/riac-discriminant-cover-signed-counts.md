# Discriminant covers as signed arithmetic counts

- **ID:** RIAC-discriminant-cover
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [RIAC](renormalized-intersection-arithmetic-counts.md)
- **Statement:** Construct the actual finite-field cover `y²=disc(f)` and derive its point count from Frobenius orientation and polynomial Möbius cancellation.

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
4. Apply the already proved `ArithmeticGaugeTheory.sum_monicOfDeg_polyMoebius`.
   Do not duplicate its scalar cancellation proof.
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

Neither the twisted orbit count nor this comparison is formalized here.
The current draft instead constructs residue-field trace-discriminant
fibres; its aggregate count uses the already derived polynomial Möbius
sums. That is a sign-retaining calibration, not an independent cancellation
proof. The usual polynomial-discriminant comparison remains separate.

