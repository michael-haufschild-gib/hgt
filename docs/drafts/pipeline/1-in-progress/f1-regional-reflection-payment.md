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

Centering the reflection at `l=log2` gives
`g(l+v)g(l−v)=(l²−v²)[(1−l²−v²)²−4l²v²][(1−(l²+v²)/2)²−l²v²]`.
On its overlap, both bracketed factors decrease with `l`. Bound them at
`693147/1000000`, the first factor at `693148/1000000`, and enlarge the integration
interval to `|v|≤1−693147/1000000`. The resulting rational polynomial integral,
`w≤4902/10000`, `γ>577215/1000000`, and `logπ≥log3+1−3/π` give a strictly negative
upper bound after subtracting the linear pole lower bound `121/88200`.
The final rational sign has a kernel-checked proof. The integral identities, monotone
enclosure and approximation by C² tests still require their Lean proofs.

The quintic is continuous and Lipschitz, but its zero extension is not C². Let `p` be its
polynomial and `η=Real.smoothTransition`. The support-preserving approximation
`gₙ(u)=p(u)η(n(1−u²))` is smooth and odd. Its derivative is bounded uniformly by
`8+2Λ`, where `Λ` bounds `η′`: the transition derivative vanishes unless
`0≤n(1−u²)≤1`, and the factor `1−u²` in `p` pays the factor `n`.
The corpus supplies `HTGeometry.exists_bound_deriv_smoothTransition`.
The regional energies then converge by dominated convergence. The potential, reflection
and pole terms converge too; `g²W≤1/2` controls the endpoint logarithm. These approximation
claims still need Lean proofs. No C² counterexample is claimed before that audit. This
obstruction concerns the proposed lower form, not the complete Weil form.

**Positive survivor:** retain the first and second lag moments in the Gamma
comparison. With `D(t)=E−C(t)`, it gives
`ΓE+J∞≥∫₀¹D/t−(γ+logπ+log2)E+E/48−(∫₀¹tD)/24−(∫₀¹t²D)/16`.
The second moment is `E/3+(∫xF)²`; the first is `E/2+∫(∫_{−∞}ˣF)²`.
These terms were replaced by worst-case mass bounds in `B`.
[Retained Gamma payment](../3-formalized/f1-gamma-lag-moment-payment.md) now proves the
retained inequality, exact second-moment substitution and uniform loss `7/192` in Lean,
with standard-only axiom audits. The first-moment primitive identity remains under
[formalization](../2-fully-proven/f1-first-lag-moment-primitive.md). The quintic obstruction above concerns
the old loss `5/96`; it does not decide the improved lower form.

No numerical evidence is used. Neither proposed positivity statement is established.
