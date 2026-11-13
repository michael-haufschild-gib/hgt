# Critical half-line states have no terminal support gap

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** The delay obstruction in the critical-state outerness route, B104/B4.
- **Statement:** Every actual critical state F satisfies `∫_(-d,0) F²>0` for every `d>0`.
- **Contribution count:** Supporting theorem; no separate contribution counted.

## Proof

**[PROVED HERE; Lean verified]** Translation `F_c(u)=F(u+c)` preserves every Fourier modulus and every translated correlation. Hence the Gamma and prime energies are unchanged. Its real Laplace moment at s is multiplied by `exp(-sc)`; the opposite half-pole characters therefore cancel in the polar product. The exponential square mass is multiplied by `exp(8c)`. Whenever the translate retains negative support, all actual-domain conditions persist and

`E_R(F_c)=E_R(F)+alias(R)(exp(8c)-1)I₈(F)`.

Suppose an actual unit critical state has zero square mass on `(-d,0)`. It vanishes almost everywhere there. Let `G=1_(-∞,-d/2)F`. This measurable, negatively supported profile agrees with F almost everywhere, so it retains unit norm, domain admission, and zero critical energy. Its exponential mass satisfies `I₈(G)≥∫G²=1` because `exp(-8u)≥1` on negative support.

The right translate `G(u-d/2)` still has negative support. Its energy is
`alias(W₀)(exp(-4d)-1)I₈(G)<0`, since `W₀>0` and `d>0`. This contradicts full-energy nonnegativity at the critical threshold. Thus every terminal interval has positive mass. The existing unconditional critical-state existence dichotomy yields RH or a state with this property.

## Formalization

Module: `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateHasNoTerminalSupportGap`.

- `criticalHalfLineFullEnergy_comp_add_right`: exact translation defect.
- `criticalHalfLineGroundState_endpoint_mass_pos`: positive terminal square mass.
- `riemannHypothesis_or_exists_endpointFullSupport_criticalHalfLineGroundState`: unconditional dichotomy.

Final check: `lake --old env lean GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateHasNoTerminalSupportGap.lean` passed. The unconditional dichotomy's transitive axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. The module is wired into the umbrella.
