# Cardinality-only fourth moments over square finite fields

- **ID:** quasi-rh-cardinality-only-cm4
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** [Additive-shift route](../1-in-progress/quasi-rh-shift-correlation.md)
- **Statement:** For every finite field K of size q, every character χ of exact order six, and every B-point set S with `B≤q^(1/3)`, the fourth moment is `Oε(q^(1+ε)B²)`, with constants uniform in K, χ and S.

## Exact obstruction

For each n≥0, take F of order `r=5^(6n+3)` and its quadratic extension K. Then `q=5^(12n+6)` and `6|(r+1)`. K has a complex multiplicative character of exact order six. Every such character is trivial on F×: norm surjectivity expresses a nonzero base-field element as `y^(r+1)`, a sixth power.

Choose any `B=5^(4n+2)` elements of F as shifts. For x∈F the packet equals B off S and B−1 on S, so

`M₄(χ,S) ≥ (r−B)B⁴+B(B−1)⁴ ≥ 4·5^(2n)·qB²`.

Here `B³=q` and `4·5^(2n)=(4/5)q^(1/6)`. For any fixed `ε<1/6`, the ratio to `q^(1+ε)B²` diverges. This disproves the uniform arbitrary-set statement. It does not disprove CM4 for intervals over prime fields or for balanced Eisenstein boxes.

## Positive survivor

The exact subfield contribution is `(r−B)B⁴+B(B−1)⁴`, not merely a negative asymptotic conclusion. More generally, for every nonprincipal character trivial on F×,

`Σ_{a∈F}χ(x−ua)=χ(u)(r·1[x/u∈F]−1)` for u≠0.

Thus an arbitrary shift packet has affine-line average

`Σ_{a∈F}Σ_{h∈S}χ(x−ua−h)=χ(u)(r·|S∩(x−uF)|−|S|)`.

For x outside F, the first identity follows by summing χ over the bijection `(a,b)↦bx−a` from F² to K. The b=0 row contributes r−1; each nonzero row gives the same line sum; the complete sum is zero. The general direction follows by scaling, and the packet identity follows by interchanging finite sums.

## No-go closure

- **Killing mechanism:** exact order-six characters constant on a subfield amplify shifts supported on one line.
- **Strongest positive survivor:** exact subfield fourth-moment contribution and exact affine-line occupancy formula for arbitrary shift packets.
- **New insight:** a source-applicable bound must retain window geometry; counting shifts alone loses an explicit arithmetic component.
- **Paper status:** the construction, lower bound, divergence and projection identities have complete proofs above.
- **Lean status:** `RHTower.QuasiRHShiftCorrelation.exists_sextic_subfield_moment_obstruction` in `QuasiRHSubfieldMoment.lean` constructs the whole family with no character-existence premise. The same file proves the exact contribution. `subfield_affineLine_packet_sum` in `QuasiRHSubfieldProjection.lean` proves the projection identity. Both leaves pass focused `lake --old env lean` checks without warnings; all ten exported theorem audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
- **Novelty status:** no external novelty claim; local corpus only, as requested.

The prime-interval and balanced-box routes remain in progress on the source card.
