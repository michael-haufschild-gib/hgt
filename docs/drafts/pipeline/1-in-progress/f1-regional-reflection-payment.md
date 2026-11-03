# Regional logarithmic payment of the first reflection

- **ID:** F1-RP
- **Stage:** 1-in-progress
- **Type:** CONJECTURE; quintic obstruction under audit
- **Source:** [Joint first-fold payment](f1-joint-cubic-prime-payment.md)
- **Statement:** The lower form below is nonnegative for every real odd C² function supported
  in `[-1,1]`.

Put `E=∫₀¹G²`, `d=2log2`, `w=log2/√2`, `W(u)=−½log(1−u²)`,
`c=γ+logπ+5/96`, and `s(u)=2sinh(u/4)`. Let `J` be the regional logarithmic energy
on `[-1,1]` from `RegionalLogarithmicGap`. The proposed payment is

`B(G)=J(G)/4+∫₀¹(W−c)G²+w∫_{d−1}¹G(u)G(d−u)du−½(∫₀¹Gs)² ≥ 0`.

For `F(x)=G(2x)`, the Gamma comparison and exact regional/exterior decomposition suggest
`Q(F)≥B(G)`. The reflection coefficient is `w`: scaling gives
`C_F(log2)=−½∫_{d−1}¹G(u)G(d−u)du`. The pole pairing is exactly `∫₀¹Gs`.
The logarithmic endpoint potential is integrable against these tests.

## Sign problem

The exact regional spectrum is `TPₙ=2HₙPₙ`. Keeping all levels below five and replacing
higher levels by `H₅` suggests the stronger finite-rank lower form

`∫₀¹(H₅−c+W)G²+w∫_{d−1}¹G(u)G(d−u)du
 −(77/20)(∫₀¹uG)²−(63/20)(∫₀¹P₃G)²−½(∫₀¹sG)²`.

Its multiplication/reflection part has paired matrix
`[[A(u),w],[w,A(d−u)]]`, `A=H₅−c+W`, on the reflection strip, and multiplication by
`A` outside. It is positive because `H₅−c>w` and `W≥0`.
The remaining question is the sign after subtracting the three moment squares. Positivity
of the paired matrix alone does not establish that sign. The finite-rank lower form may be
strictly weaker than `B`; reject it if its exact moment matrix has a negative direction.

## Gates

- [ ] Audit the stronger finite-rank form analytically, retaining its reflection and pole.
- [ ] Prove the actual low-moment payment or identify the discarded positive term needed.
- [ ] Formalize any dependency-closed proof, then apply it to the complete first stage.

## Quintic obstruction under audit

For `g(u)=u(1−u²)(1−u²/2)` on `[-1,1]`, zero outside, the exact formulas are

- `∫₀¹g²=62/1155`, `∫₀¹ug=11/105`;
- `g=(11/35)P₁−(17/45)P₃+(4/63)P₅`;
- `J(g)/4=121/3675+3179/85050+548/654885`;
- `∫₀¹Wg²=4/9−23/25+572/735−563/1890+1627/38115−(62/1155)log2`.

The [retained-form obstruction](../2-fully-proven/f1-quintic-retained-gamma-obstruction.md)
uses the exact correlation of `F(x)=g(2x)` directly. It proves negativity of the stronger
lag-moment Gamma lower form on this continuous quintic, including the prime and pole,
with standard-only transitive Lean axioms. This avoids an endpoint-logarithm or
reflection-integral enclosure. The quintic's zero extension is not C²; support-preserving
mollification and rescaling remain under formalization. No C² counterexample is claimed yet.

**Positive survivor:** retain the first and second lag moments in the Gamma
comparison. With `D(t)=E−C(t)`, it gives
`ΓE+J∞≥∫₀¹D/t−(γ+logπ+log2)E+E/48−(∫₀¹tD)/24−(∫₀¹t²D)/16`.
The second moment is `E/3+(∫xF)²`; the first is `E/2+∫(∫_{−∞}ˣF)²`.
These terms were replaced by worst-case mass bounds in `B`.
[Retained Gamma payment](../3-formalized/f1-gamma-lag-moment-payment.md) and the
[primitive identity](../3-formalized/f1-first-lag-moment-primitive.md) prove both moment
substitutions, the common-primitive Gamma/pole bound and uniform loss `7/192` in Lean,
with standard-only transitive axiom audits. For `H(x)=∫_{−1}ˣF`, the gain over the old
uniform lag form is exactly `E/32−(∫H²)/24−(∫xF)²/16`. The bounds `∫H²≤E/4` and
`(∫xF)²≤E/12` make that gain at least `E/64`. The equality identifying the regional
form `B` with the old uniform lag form still needs its Lean proof.

The direct quintic correlation and its lag moments are proved in
`WindowTowerOfSpecZ.TheQuinticWindowHasExactLagData`. The negative continuous retained
form is `retainedOddGammaLowerForm_quintic_neg`. The complete Weil form's sign remains
open; its omitted nonnegative Gamma remainder must be retained in the joint payment.
