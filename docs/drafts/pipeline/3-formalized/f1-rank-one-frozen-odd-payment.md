# Rank-one payment of the frozen odd direction

- **ID:** F1-OP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [F1 assembly](../1-in-progress/f1-window-tower-assembly.md)
- **Statement:** For every odd real C² test supported in `[-1/2,1/2]`,
  `Q₁(F)+20(∫F(x)x(1−16x²/5)dx)² ≥ (1/125)∫F²`.

The bound isolates at most one frozen negative direction. The signed prime-2 payment remains open.

## Paper proof

Write `E=∫F²`, `C(t)=∫F(x)F(x+t)dx`, `M=∫F(x)x(1−16x²/5)dx`.
For odd `F` supported in `[-1/2,1/2]`, put `U(s)=F(s/2)` and
`h(s)=s(1−4s²/5)` on `(0,1)`.

The reflected logarithmic kernel is `K(s,t)=1/(2|s−t|)−1/(2(s+t))`.
For `0<t<s<1`, `K=t/(s²−t²)` and

`[K/(h(s)h(t))]⁻¹ ≤ s³(1−4s²/5) ≤4/15`.

For the last inequality, with `u=s²`,

`27−400[s³(1−4s²/5)]²=(3−4u)²[16u²(1−u)+8u+3]≥0`,

and `27/400<16/225`. Symmetry gives `K≥(15/4)h(s)h(t)` off the diagonal.
The exact ground-state remainder is

`K(U(s)−U(t))²−K(h(s)−h(t))(U(s)²/h(s)−U(t)²/h(t))`
`=K/(h(s)h(t)) [U(s)h(t)−U(t)h(s)]²`.

After integration it contributes at least
`(15/2)[(∫h²)(∫U²)−(∫Uh)²]`, with `∫h²=11/105`.
LST's cubic potential plus exterior killing is at least `log2+7/5`.
The exact folding and scaling identities, `E=∫₀¹U²` and `2M=∫₀¹Uh`, give

`∫₀¹(E−C(t))/t dt ≥(log2+7/5+11/28)E−15M²`.

All ground-state terms are integrable: `h≥s/5`, Lipschitz oddness gives
`|U(s)|≤Ls`, and `|K(s,t)(h(s)−h(t))|≤17/10`.

Oddness gives `∫₀¹C=0`; Cauchy–Schwarz gives `|C|≤E`.
Consequently `∫₀¹(E−C)=E`, `∫₀¹t(E−C)≤3E/4` (center `C` at `t=1/2`),
and `∫₀¹t²(E−C)≤2E/3`. The sharp Gamma kernel lower bound
`2ω(t)≥1/t+1/2−t/24−t²/16` and the exact exterior tail give

`ΓE+J ≥ (5849/3360−γ−logπ)E−15M²`.

Here `Γ=−γ−logπ−3log2−π/2` cancels the logarithmic and circular terms from
`Ω(1)≥log2+π/4−1/4+1/96`; `γ` is Euler's constant.

For the pole let `h₁(x)=x(1−16x²/5)`, `d=x−(5/3)h₁`,
`r=2sinh(x/2)−x`. On `[-1/2,1/2]`,
`|r|≤|x|³cosh(1/4)/24` and `cosh(1/4)²≤16/15`.
Exact polynomial integration gives `∫d²=11/945` and `∫x⁶=1/448`.
Thus

`∫(d+r)²≤(21/20)(11/945)+21(16/15)/(576·448)<1/80`.

Cauchy–Schwarz and `(a+b)²≤3a²+(3/2)b²` yield
`⟨F,2sinh(·/2)⟩²/2≤25M²/6+3E/320`.
For odd `F`, the cosh pairing vanishes, so the actual frozen stage equals
`Q₁(F)=ΓE+J−⟨F,2sinh(·/2)⟩²/2`.
Thus `Q₁(F)+(115/6)M² ≥ (5849/3360−γ−logπ−3/320)E`.
The bounds `logπ≤log3+π/3−1` and `γ<577216/1000000` imply
`5849/3360−γ−logπ−3/320>1/125`. Finally `115/6<20` proves the stated rational bound.

## Lean proof

Namespace: `GaloisForLFunctions.WindowTowerOfSpecZ`.

- `TheOddCubicGaugeRetainsAVariance`: `principalOddKernel_cubic_minorant`,
  `principalOddKernel_cubic_energy_ge`, `folded_logarithmic_jump_cubic_gap`.
- `TheCubicMomentPaysTheFrozenOddComplement`: `stageForm_one_cubicMoment_lower`,
  `stageForm_one_add_cubicMoment_ge`, `stageForm_one_coercive_of_cubicMoment_zero`;
  `unit_odd_gamma_jump_lower` retains the logarithmic energy before any spectral estimate.

Both modules pass individual `lake --old env lean` source checks and are imported by the WTZ
umbrella. The gap, Gamma comparison and all three stage bounds depend only on `propext`, `Classical.choice`,
`Quot.sound`. [Joint prime-2 payment](../1-in-progress/f1-joint-cubic-prime-payment.md) remains open.
