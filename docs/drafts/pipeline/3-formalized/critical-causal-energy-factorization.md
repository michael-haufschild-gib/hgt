# Positive-square factorization of critical causal energy

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Target:** B104; reconstruct the actual critical form on its dense causal span.
- **Status:** All five Lean modules passed final source and transitive-axiom audits. One contribution. Polar pairing remains open.

## Exact identity

Let `F` be the actual critical state at `W₀`, `T_s F(u)=F(u+s)` for `s≥0`, `a=criticalAliasCoefficient W₀`, and `W(G,H)=∫G(u)H(u)exp(-8u)du`. Write `B` for the full mixed critical form. The exact kernel is

`B(T_s F,T_t F) = a (1-exp(-8 min(s,t))) W(T_s F,T_t F)`.

For ordered delays `0=s₋₁≤s₀≤⋯≤sₙ`, set `G_k=∑_{i≥k}c_i T_{s_i}F`. The resulting positive-square expansion is

`E(∑ c_i T_{s_i}F) = a ∑_k (exp(-8s_{k-1})-exp(-8s_k)) W(G_k,G_k)`.

For distinct positive delays the energy matrix is positive definite; adding delay zero leaves precisely the critical-state direction in its kernel. The advance is an exact positive-square representation of the actual arithmetic energy.

Thus the full Gamma, prime, and pole contributions on these sums reduce to explicit positive weighted tail masses, without a one-sign assumption on `F`.

## Sharp terminal-wall law

The same covariance gives a sharp weighted floor for every profile `H` in the actual domain supported on `u<-h`, `h≥0`:

`E(H) ≥ a (1-exp(-8h)) W(H,H)`.

Equality holds exactly for scalar multiples of `T_h F`, modulo null sets. The weighted ground-energy curve under displacement of the terminal wall is explicit, with its full extremizer line. It is part of this same energy representation, not a separate count.

## Corpus connection and proof route

`criticalHalfLineFullEnergy_comp_add_right` gives the exact simultaneous-translation defect. Polarize it, then use `criticalHalfLineMixedEnergy_groundState_eq_zero` after subtracting the smaller delay. Weighted change of variables yields the kernel above. Ordered telescoping gives the square expansion. Causal cyclicity identifies its underlying L² span as dense; density in the energy norm is not yet established.

The finite minimum-kernel mechanism appears in `SurfaceOfSpecZ.schur_min_posSemidef`, in `HyperbolicQuotientsJetCarriersAndCoupledDamping.lean`. Existing signed ground-state transforms instead use conductances across nodes (`ArithmeticCriticalityTheory/GeneralGaugeGroundStateRepresentation.lean`); their hypotheses and forms differ from this actual critical state.

## Proof

1. The actual domain is closed under scalar combinations and all support-preserving translations. Polarization of `E(T_hG)=E(G)+a(exp(8h)-1)W(G,G)` gives simultaneous mixed covariance. For `s≤t`, apply it to `F,T_(t-s)F`; the weak equation kills their mixed energy. Weighted covariance supplies the factor `1-exp(-8s)`. Symmetry handles `t≤s`.
2. The weak equation also gives `E(G+cF)=E(G)`. Apply translation to this identity, then induct over consecutive delay increments to obtain the recursive square formula below. Weighted covariance converts each term to the displayed ordered-tail formula.
3. If `G` has zero energy, set `c=ℒG(1)/ℒF(1)`. The denominator is nonzero. The weak equation makes `G-cF` zero-energy with zero Laplace value. The verified positive-Laplace zero-energy exclusion forces it to vanish almost everywhere. Hence the full nullspace is the critical-state line.
4. For a wall-supported `H`, the exact deficit is `E(H)-a(1-exp(-8h))W(H,H)=E(T_-h H)`. Endpoint nonnegativity proves the bound; step 3 classifies equality. Translation of `F` attains it and has positive mass. For `h>0`, every nonzero wall-supported profile has strictly positive energy.
5. Distinct positive ordered causal translates are independent modulo null sets: after undoing the first delay, only the first coefficient contributes on the terminal interval before the second translate starts. Positive endpoint mass of `F` forces that coefficient to vanish. Repeat on the remaining terms. Step 4 therefore makes every finite energy matrix with distinct positive delays positive definite. Adding the zero-delay translate contributes exactly the ground-state null direction by the weak equation.

Every final application uses the actual critical state supplied by the unconditional RH-or-state dichotomy. No extra analytic input is assumed.

## Exact recursive square formula

For a list of nonnegative increments and real coefficients, define `P([])=0` and `P((h,c)::l)=T_h(P(l)+cF)`. Its ordinary delays are the cumulative sums of the increments. Then

`E(P(l)) = a ∑_{(h,c)::r suffix of l} (exp(8h)-1) W(P(r)+cF,P(r)+cF)`.

Every summand is nonnegative. If `s_prev` is the cumulative delay before a suffix and `s=s_prev+h`, its absolute tail is `T_s(P(r)+cF)`. Weighted covariance changes the displayed term into `(exp(-8s_prev)-exp(-8s)) W(absolute tail,absolute tail)`, giving the stated ordered formula.

## Lean declarations and audit

All modules lie under `GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/` and are imported by the programme umbrella.

| Module | Principal declaration |
|---|---|
| `CriticalCausalEnergyTranslation.lean` | `criticalHalfLineFullEnergy_causal_ground_shear`; `criticalHalfLineFullEnergy_zero_eq_laplace_ratio_ae` |
| `CriticalTerminalWallEnergy.lean` | `riemannHypothesis_or_exists_sharp_terminal_wall_groundState` |
| `CriticalCausalEnergyKernel.lean` | `riemannHypothesis_or_exists_causal_minimum_energy_kernel` |
| `CriticalCausalEnergySquares.lean` | `riemannHypothesis_or_exists_ordered_causal_tail_square_formula` |
| `CriticalCausalEnergyIndependence.lean` | `riemannHypothesis_or_exists_strict_ordered_causal_energy_matrices`; `criticalHalfLineFullEnergy_causalPolynomial_zero_head_eq_zero_iff` |

Every final audit used `lake --old env lean <source>`. The unconditional statements have no hypotheses; their transitive axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. Required dependency oleans are built, all five scratch proof files removed, and no umbrella was compiled. No energy-norm density claim.
