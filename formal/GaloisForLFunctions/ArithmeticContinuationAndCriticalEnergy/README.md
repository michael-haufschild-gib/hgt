# Arithmetic Continuation and Critical Energy (`GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy`)

**One question.** A critical energy of an exact arithmetic source is finite at one end of a
parameter range — at half damping, at a finite cutoff, at a bounded aperture — and the Riemann
Hypothesis is the statement that it stays finite as the parameter runs to the critical end. Which
*arithmetic identities* prevent the energy from escaping on the way, and what exactly must be
estimated to use them?

Arithmetic continuation and critical energy (ACCE) is a theory of *transport in a parameter*.
Where the incidence, lag and aperture faces of the critical form each ask for a sign at a fixed
parameter, ACCE asks for the derivative: how much energy can the family lose per unit of parameter,
measured through a scale, and what pays that loss. Its objects carry two indices at once — a
continuous parameter and an observation horizon — and its only currency is a bound uniform in the
horizon. Every statement here is unconditional, names the parameter interval it concerns, and keeps
the horizon quantifier where the mathematics puts it.

---

## Place in the research

ACCE studies whether a bound survives a change of parameter. Its model is the exact damped Möbius
divisor source in the pronic norm: the endpoint at half damping is admitted, while admission at
positive dampings accumulating at zero is RH. The transport variable and the observation horizon
must stay separate. Smooth dependence at every fixed horizon does not give a uniform budget.

The main pillars are exact work identities, linear and Osgood transport, the equivalence between
signed averaged budgets and admission, and the dilation calculus of integer prefixes. Two further
reductions make the arithmetic demand concrete: the work is edge mass minus dilation jump energy
plus its polar correction, and the full receiver norm is equivalent to one-step block energy.
Neither reduction supplies the missing estimate on the actual source.

| Programme | Connection |
|---|---|
| [Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md) | Fixes the source and complete energy before a transport is proposed. |
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Supplies blind models and distinguishes recoverable observations from stable energy estimates. |
| [Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) | Owns the finite-horizon receiver and its damping admission problem. |
| [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) | Supplies the Markov derivative, divisor identities and pronic arithmetic geometry. |
| [Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md) | Supplies the aperture ground-energy path and the vanishing upper bound any continuation must respect. |
| [Square-Root Threshold](../SquareRootThreshold/README.md) | Identifies the damping threshold with zero width and converts partial transport into a strip bound. |
| [Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md) | Supplies local window certificates and the signed prime–polar decomposition to be continued. |
| [Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md) | Tests whether a proposed observation preserves the sign and limiting parameter information. |
| [Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md) | Develops the coupled flux–forcing budget beyond separate estimates on derivative terms. |
| [Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) | Seeks arithmetic effectivity that could provide a source of the required energy estimate. |
| [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Studies the source's signed incidence kernel, a possible input to continuation. |
| [Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md) | Lists cofinal admission as the damping unit of the width dictionary. Shows that on residue-mode combinations the damping flow keeps the sign pattern of the coefficients exactly: what transport must control is magnitude in the pronic norm, not orientation. |

**The shared target.** The programmes in the table work on RH as the sign of one critical
arithmetic form and on the critical cancellation of the actual Möbius source. ACCE supplies what no
fixed-parameter face states: the transport of a finite critical energy along damping, cutoff or
aperture, with the observation horizon quantified uniformly, and a partial result in the shared width
unit — a budget on `(a₀, c]` is the strip `Θ ≤ ½ + a₀`.

Read §2 for the quantifiers and normalisation, then the exact derivative and averaged criterion
in §3; §4 lists the pillar theorems and §§6–7 the questions and open problems. The dilation, block-energy and zero-anchor descriptions are alternative ways to expose the
same arithmetic obligation. They should be compared by what estimate they require, not by how many
equivalent receivers they produce.

---

## 1. Why: motivation

The corpus proves many equivalent forms of the Riemann Hypothesis and many sharp statements about
why the surveyed methods stop. Three of those obstructions bear directly on the choice made here.

- A change of receiver coordinates is not an improved arithmetic bound. Width dictionaries convert
  one unknown rate into another; they never produce an estimate for the source.
- A bounded aperture cannot decide an arbitrary configuration. A certificate at finite aperture is
  progress in the aperture, not in the conclusion.
- Below half damping no sign-blind datum controls the receiver. Magnitudes, unsigned majorants,
  two-point data and stationary translated moments are shared with parity partners at every damping
  `ε ≤ ½`, so any estimate that uses only such data proves nothing about `ζ`.

What those obstructions leave open is a *quantitative* statement about the actual signed source.
The damped Möbius critical energy makes the gap explicit. With

`c_ε(d) = μ(d) d^{-ε}`,  `A_ε(n) = Σ_{d ≤ n} c_ε(d) ⌊n/d⌋ − n·Re(1/ζ(1+ε))`,
`E_T(ε) = Σ_{n ≤ T} A_ε(n)² / (n(n+1))`,

the family is admitted at every `ε ≥ ½` unconditionally, admission at dampings accumulating at `0`
is exactly RH, and the infimum of the accumulation points of the admitted dampings is exactly the
zero width `Θ − ½`. So RH is not an inequality at a single damping. It is the question whether a
finite energy *survives transport* from an admitted endpoint down to zero damping.

That reframing is the reason for a separate programme. A transport theorem does not need a bound at
the critical end, which is where every estimate fails; it needs a bound on the rate of loss on each
compact interval away from the critical end, where the family is smooth and the arithmetic is
explicit. The analytic demand changes shape in two ways. It starts from a known finite state instead
of trying to enter the critical norm from the singular end. And it asks only for the
*energy-increasing part* of the derivative when moving backwards: large tangential motion is free.

The same reframing applies to the other two parameters. Removing a coefficient cutoff and growing an
aperture are continuations in exactly the same sense, and the transport theorems here are stated for
an arbitrary parameter so that they can be instantiated in all three.

---

## 2. What: objects and language

**Energy families.** An energy family is a function `E : ℝ → ℕ → ℝ` of a continuous parameter and a
discrete observation horizon. Three graded notions of success are kept apart, because conflating
them is the standard error (`CriticalEnergyFamilies`):

- `Admits E ε` — `∃ B, ∀ T, E ε T ≤ B`. One bound at one parameter, uniform in the horizon. The
  quantifier order is the content: `∀ T, ∃ B` is free and says nothing.
- `CofinallyAdmits E` — admission at parameters arbitrarily close to `0`, each with its own bound.
  No bound uniform in the parameter is asked for.
- `UniformlyAdmitsOn E s` — one bound for the whole parameter set. Strictly stronger than admission
  at each of its points.

Because the critical energy is nondecreasing in the horizon, admission is insensitive to how the
horizon is sampled: a bound along any cofinal set of horizons, in particular the dyadic ones, is
admission, and a bound on the Cesàro means over horizons is admission as well — equivalent to it,
up to a factor two (`HorizonAveragesAndSparseHorizons`). Mean values over a growing range are what
analytic machinery produces; the reduction says they are enough.

**The critical energy of record** is `dampedMobiusEnergy = pmPowerDampedDivisorDiscreteEnergy`
(`TheDampedMobiusCriticalEnergy`). Its source is fixed before any closure: every coefficient, the
exact pole subtraction `n·Re(1/ζ(1+ε))` and the pronic observation weight `1/(n(n+1))` are named,
and nothing is selected from the zeros. Two dictionary entries fix what continuation must deliver:
`mem_receiverDampings_iff_admits` (admission is membership in the admissible damping set) and
`riemannHypothesis_iff_cofinallyAdmits` (cofinal admission is RH). The energy is strictly positive
at every positive damping and every positive horizon — the first cell is `1 − 1/ζ(1+ε) > 0` — so no
criterion below is asking for the sign of something that vanishes.

**The complete signed work** is

`W_T(ε) = Σ_{n ≤ T} A_ε(n) · E_ε(n) / (n(n+1))`,  `E_ε(n) = ∂_ε A_ε(n)`,

the pronic pairing of the centred source with its own damping tangent (`signedDampingWork`). It is
one signed number. It is not a norm, not a sum of absolute cross terms, and not an energy with the
pole correction deleted.

**The tangent family and its autocorrelation.** The source is the damping primitive of its tangent,
so the work is a self-pairing of one family of vectors across dampings. The Gram kernel

`K_T(η, ε) = Σ_{n ≤ T} E_η(n) E_ε(n) / (n(n+1))`

is the **damping autocorrelation** of the centred damped Chebyshev function; its diagonal is
`‖E_ε‖_T²`. The second damping tangent `F_ε = ∂_ε E_ε` is the centred prefix of
`Λ⁽²⁾_ε(k) = Σ_{d ∣ k} μ(d)(log d)² d^{−ε}`, and `W'_T = ‖E_ε‖_T² + ⟪A_ε, F_ε⟫_T`.

**Budgets.** A *pointwise* continuation budget on `[a, c]` is a primitive `β` — the same function
for every horizon — with

`−E'_T(ε) ≤ β'(ε) · (1 + E_T(ε))` for all `T` and all `ε ∈ [a, c]`

(`LinearContinuation`); its nonlinear form replaces `1 + E` by a growth function `Φ` and asks for a
*scale* `Ψ` with `Ψ' = 1/Φ` coercive on `[0, ∞)` (`OsgoodContinuation`); coercivity is the Osgood
condition `∫^∞ du/Φ(u) = ∞` in the form actually used. An *averaged* budget is a horizon-free bound
on the parameter integral of the **relative loss**

`r_T(ε) = −E'_T(ε)/(1 + E_T(ε)) = −∂_ε log(1 + E_T(ε))`

(`AveragedContinuation`). The averaged form is the bottom of the hierarchy and the one to aim at:
every pointwise budget is an averaged budget of total `β c − β a`, and the converse fails badly.

**Dilation coordinates.** The prefix dilations `(D^f v)(n) = Σ_{j ≤ n} f(j) v(⌊n/j⌋)` compose
exactly, `D^f ∘ D^g = D^{f*g}`, because `⌊⌊n/j⌋/k⌋ = ⌊n/(jk)⌋`: on integer prefixes they represent
the Dirichlet ring with no error term. The damped prime row is `Λ_ε(j) = Λ(j) j^{−ε}`, the damped
unit row `ζ_ε(j) = j^{−ε}`, and the laws the source obeys are `Λ_ε * ζ_ε = (log)_ε` together with
the inversion law `Σ_{j ≤ n} j^{−ε} A^{raw}(⌊n/j⌋) = n`. Grouping dilations by the level they land
on gives the **quotient incidence kernel** `κ_ε(n, m) = Σ_{⌊n/j⌋ = m} Λ(j) j^{−ε}`.

**Prime-pair, polar and level coordinates.** Summing the pronic weight first converts a pairing of
prefixes into a sum over pairs of prime powers against the Nyman–Beurling kernel,

`Σ_{n ≤ T} (Σ_{j ≤ n} a_j)(Σ_{k ≤ n} b_k)/(n(n+1))
   = Σ_{j,k ≤ T} a_j b_k / max(j,k) − (Σ_{j ≤ T} a_j)(Σ_{k ≤ T} b_k)/(T+1)`,

and since `1/max(j,k)` is constant on levels the double sum collapses again to a single **scale
sum** `Σ_{M ≤ T}(a_M B_M + A_M b_M − a_M b_M)/M`.

**Vocabulary.** The following words are used only with the content listed beside them.

| Term | Meaning that must accompany it |
|---|---|
| Admission | finiteness of a named complete norm, with its quantified parameters |
| Continuation | propagation of admission through a parameter interval, with a stated bound |
| Compensation | a bound on a combined signed expression, not smallness of its separate terms |
| Observation | a specified map from source to data, together with its indistinguishability class |
| Stability | a quantitative estimate in the norm the receiver requires |
| Completion | a specified topology, and a theorem saying which source, pole and sign data survive |
| Selectivity | a proved reason the estimate holds for the actual source and fails for a named model |

These are not new axioms. They specify what a theorem in this programme has to say. The available
algebraic identities — `μ * 1 = δ₁`, `Λ * 1 = log`, `Λ * μ = −μ log`, the exact tangent law, the
explicit formula — are starting facts. Global positivity, small-damping admission, purity and the
zero width remain conclusions.

---

## 3. How: mechanisms

### The master inequality

Everything rests on one monotonicity statement (`scaledEnergy_add_budget_le`). Along `[a, c]`, if

`0 ≤ ψ(ε) · E'_T(ε) + β'(ε)`,

that is, if the energy read through the scale loses no faster than the budget pays, then
`Ψ ∘ E_T + β` is nondecreasing, hence

`Ψ(E_T(a)) ≤ Ψ(E_T(c)) + (β(c) − β(a))`.

The derivative of the scale is indexed by the parameter rather than by the value, which keeps the
hypothesis pointwise and avoids demanding differentiability of `Ψ` off the range of the energy.

### Linear transport and coercive transport

With `Ψ = log(1 + ·)` the master inequality becomes the Grönwall form
(`one_add_le_mul_exp_of_linear_work`)

`1 + E_T(a) ≤ (1 + E_T(c)) · exp(β(c) − β(a))`,

whose right side contains no horizon. `Admits.of_linearContinuation` turns that into the transport
theorem: a budget on `[a, c]` plus admission at `c` is admission at `a`. For a general scale the
same step gives a bound on `Ψ ∘ E`, and `bddAbove_of_tendsto_atTop` converts it back into a bound on
`E` — the only place coercivity is used (`Admits.of_osgoodContinuation`). The budget may deteriorate
arbitrarily fast as the left endpoint approaches `0`.

### The exact derivative, in two faces

The damping derivative of the critical energy is twice the complete signed work
(`hasDerivAt_dampedMobiusEnergy`): `∂_ε E_T(ε) = 2 W_T(ε)`. The same derivative has a Markov face
owned by `BezoutValuationIncidence`: boundary flux minus nonnegative jump energy minus density
forcing, and uniqueness of derivatives identifies the two
(`two_mul_signedDampingWork_eq_markov`). One consequence is immediate: since the jump energy is
nonnegative and enters `−2W` with a `+` sign, a continuation budget must control the net combination of dissipation,
forcing and boundary flux; it need not bound dissipation separately. Dissipation helps the forward direction and obstructs the backward one; in the
Markov reading the sign criterion says exactly that the flux dominates dissipation plus forcing.

Integrated, the two faces give the two exact dictionaries. The relative loss integrates to the
logarithm of the energy ratio; the work itself integrates to the energy difference,
`∫_a^c 2W_T = E_T(c) − E_T(a)` (`TheWorkIntegralIsTheEnergyDrop`). Hence, with an admitted right
end, admission at `a` is *equivalent* to a horizon-free bound on the signed integral `∫_a^c −2W_T` — and failure is always visible as deep negative work at a specific damping and horizon,
never as a diffuse effect.

### The averaged budget is exactly admission, and the pointwise one is strictly stronger

The parameter average of the relative loss *is* the logarithm of the ratio of shifted energies, so
no slack remains between hypothesis and conclusion: on an interval with admitted right end, an
averaged budget holds if and only if the family is admitted at the left end
(`averagedContinuation_iff_admits`), and cofinal averaged budgets are *equivalent* to RH
(`riemannHypothesis_iff_cofinal_averagedDampingContinuation`) — the first equivalence of the layer.
For the arithmetic family the relative loss is unconditionally integrable on every compact damping
interval away from zero, so the averaged demand is a bound and not a regularity assumption, and
cancellation between dampings is allowed: the signed work may be arbitrarily negative at individual
dampings.

The pointwise budget is strictly stronger, and not by an artefact of the arithmetic: a family can be
admitted at *every* parameter — the state RH asserts — and still carry no pointwise linear budget on
any nondegenerate interval (`exists_admits_everywhere_not_linearContinuation`; the witness is a
relative-loss spike of height `T + 1` and width `(T+1)^{−2}`, whose averaged budget is `π` on every
interval). So a pointwise horizon-free bound on the negative part of the signed work is not known to
follow from RH, while the **signed relative-loss integral** is equivalent to admission
with an admitted right endpoint. **The obligation is the averaged
one**, and the same weakening applies to the tangent-norm receiver, where `∫_a^{1/2} ‖E_ε‖_T dε ≤ C`
with `C` free of the horizon suffices (`riemannHypothesis_of_averaged_tangentNorm`).

Compensation Theory sharpens this distinction. The smooth horizon-monotone family
`E_T(ε)=Σ_{k=1}^T 2^{−k}(2+sin(16^k ε))` is bounded by `3` everywhere, yet its positive-part
relative-loss integrals diverge on every nondegenerate interval
(`exists_admitted_monotone_not_positivePartContinuation`). Signed recovery is essential even
under horizon monotonicity. A comparable adapted energy `H_T=1+E_T+C_T`, with
`m(1+E_T)≤H_T≤M(1+E_T)` and a uniform signed log-loss budget, transfers admission from right to
left. Under the regularity assumptions, existence of such an adapted energy is equivalent to
left-end admission (`adaptedEnergy_iff_admits`); progress requires constructing its arithmetic
corrector and constants independently.

### Subsumption of the tangent-norm receiver

Cauchy–Schwarz in the pronic norm and the elementary `2√E ≤ 1 + E` give
`−2W_T(ε) ≤ g(ε)(1 + E_T(ε))` whenever `‖E_ε‖_T ≤ g(ε)` for every horizon, so a horizon-uniform
bound on the pronic norm of the damped Chebyshev tangent *is* a continuation budget and the owned
tangent-norm criterion reappears as the special case in which the budget dominates a norm. Nothing
is lost by passing to the signed form, and the norm route only ever used
`|K_T(η, ε)| ≤ ‖E_η‖_T‖E_ε‖_T`.

### The endpoint, how short the interval is, and the partial deliverable

Any admitted damping serves as the endpoint (`riemannHypothesis_of_dampingContinuation_endpoint`).
Half damping is unconditional, and the cleared Mellin / Dirichlet receiver law admits every damping
strictly above the zero width `Δ = Θ − ½` (`admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt`),
improving the `Θ/2` Littlewood threshold by `½(1 − Θ)` so the interval to cross is `(0, Θ − ½]`
(`riemannHypothesis_of_averagedDampingContinuation_above_zeroWidth`). Across `[a, c]` with `c`
admitted, admission at `a`, membership in `receiverDampings`, relative-loss averaged continuation,
dyadic relative-loss continuation, additive signed work continuation, dyadic additive work
continuation, Cesàro additive work continuation, and residual averaged continuation are eight-way
equivalent (`signedAveragedContinuation_tfae`), and all eight hold unconditionally on every compact
interval inside `(Θ − ½, ∞)` (`averagedDampingContinuation_of_zetaZeroAbscissa_sub_half_lt`,
`exists_neg_signedDampingWork_integral_le_of_zetaZeroAbscissa_sub_half_lt`). Conversely, a budget
available on `(a₀, c]` forces `Θ ≤ ½ + a₀`, so the infimum of valid continuation thresholds is
exactly `Δ = Θ − ½` (`sInf_averagedContinuationThresholds_eq_zetaZeroAbscissa_sub_half`,
`exists_not_averagedDampingContinuation_below_zeroWidth`). Along the Vinogradov–Korobov band
`a ≥ ½ − κ σ(T)/(480 log T)` above any floor `ε₀ > 0`, the signed work integral, relative-loss
integral, and residual work integral are bounded uniformly in `(T, a, c)` while the parity twin
diverges logarithmically (`exists_signedWorkIntegral_and_relativeLoss_le_on_vinogradovKorobovBand`),
and at every fixed `0 < a < ½` they obey the sub-power saving
`O_a(T^{1−2a} exp(−κ σ(T)/270))` (`eventually_signedWorkIntegral_and_relativeLoss_le_vk_saving`).

### What one admitted damping says about the zeros

A single admitted damping is a statement about the zero divisor, not only about energy. If
`ε ∈ (0, ½]` is admitted, every zero `ρ` with `½ + ε ≤ Re ρ < 1` is translated to a zero `ρ − ε` of
at least the same multiplicity, the boundary line included; on the boundary the translate is a
critical zero (`analyticOrderAt_le_analyticOrderAt_sub_of_mem_receiverDampings`,
`riemannZeta_criticalLine_eq_zero_of_mem_receiverDampings`). The mechanism is the cleared Mellin
identity `s Z(s + ε) M(s) = (s + ε − 1)(1 − 2^{1−s}) ζ(s)`, `Z(w) = (w − 1)ζ(w)`, on `½ < Re s < 1`,
together with `|M(s)| ≤ C(2(Re s − ½))^{−1/2}` for the Mellin transform of the admitted `L²` source:
approaching `ρ − ε` from the right, a loss of `u^{−1/2}` is less than one power of `u`, so orders of
vanishing cannot drop. At the width itself, if `Θ > ½` is attained at `ρ₀`, admission at `Θ − ½`
forces a critical zero at `½ + i Im ρ₀` of at least the multiplicity of `ρ₀`; when no such
critical-line shadow exists the admitted dampings at or above the width are exactly `(Θ − ½, ∞)`
(`receiverDampings_inter_Ici_eq_Ioi`). This is why one isolated admitted damping has only the
zero-translation conclusion: the width is read by accumulation, not by a single point.

### A superlinear scale

The double logarithm `Ψ(u) = log(1 + log(1 + u))` is increasing and coercive on `[0, ∞)`, so the
permitted loss may be `Φ(u) = (1 + u)(1 + log(1 + u))`, superlinear in the energy
(`SuperlinearOsgoodScale`): the arithmetic estimate may lose an extra logarithm of the energy at
every damping and still suffice.

### Both ends are paid: the escape is an interior bump

Transport is not a walk from a paid end to a forbidden one. *Both* ends of the damping range are
paid, uniformly in the horizon: at half damping the energy is bounded unconditionally, and at zero
damping the source collapses to the constant one, so `E_T(ε) → Σ_{n ≤ T} 1/(n(n+1)) ≤ 1` as `ε ↓ 0`
(`tendsto_dampedMobiusEnergy_nhdsGT_zero`). What RH forbids is therefore an **interior** bump whose
location drifts to zero as the horizon grows. Two consequences: a horizon-wise *shape* hypothesis
suffices — no horizon's energy exceeding the larger of its two end values is RH
(`riemannHypothesis_of_no_interior_bump`), and so is convexity in the damping; and conversely,
failure of RH forces interior bumps of unbounded height at a fixed interior damping while both ends
stay bounded. An estimate that only improves the endpoints cannot decide the question.

The bump also lives far out in the horizon. Against the undamped identity
`Σ_{d≤n} μ(d)⌊n/d⌋ = 1`, `1 − d^{−ε} ≤ ε log d` gives the head bound
`|A_ε(n) − 1| ≤ ε Σ_{d ≤ n}(log d)⌊n/d⌋ + n m₀(ε)`
(`abs_pmPowerDampedCenteredDivisorPrefix_sub_one_le`), so for every horizon and tolerance some
damping keeps the head of the energy within the tolerance of the pronic mass
(`exists_damping_head_energy_le`). The obstruction is confined to the corner of small damping
*and* large horizon where `ε Σ_{d≤n}(log d)⌊n/d⌋` is no longer small — the same corner,
`n ≳ 2^{1/ε}`, where the positive core reaches size `1/ε`.

A bump needs the energy to rise and then fall, so the signed work must change sign from positive to
negative inside. Forbidding that *order* of sign change is enough
(`riemannHypothesis_of_signedWork_single_sign_change`): no constant, no norm and no uniformity in
the horizon beyond the shape. Monotone work — equivalently convexity of the energy — is one
such sufficient shape condition. Global nonnegative work is already false on the actual source:
Compensation Theory proves `W_1(ε)→−½` as `ε↓0` (`tendsto_signedDampingWork_one`). A viable
criterion must permit that adverse first-cell work.

### The sign is an angle: the damping autocorrelation

With `δ ↓ 0` the work becomes the autocorrelation of the tangent family across dampings,

`W_T(ε) = ⟪A_δ, E_ε⟫_T + ∫_δ^ε K_T(η, ε) dη`,

whose first term is the scalar moment that is already paid. The diagonal of `K_T` is nonnegative, so
the obstruction to backward continuation is entirely **off-diagonal anti-correlation** between
tangents at different dampings: nonnegativity of `K_T` on each `(0, ε]` gives RH with the paid
scalar constant as the budget, and a merely *bounded* total anti-correlation does as well
(`TheSignedWorkIsTheTangentAutocorrelation`).

Polarisation turns that sign into an angle,
`K_T(η, ε) = (‖E_η‖_T² + ‖E_ε‖_T² − ‖E_η − E_ε‖_T²)/2`, so the obstruction is not a size problem:
arbitrarily large tangents are harmless and only an anti-aligned pair of dampings obstructs. Hence
**relative stability** suffices — if between any two dampings below one half the tangent changes by
no more than its own size, RH follows (`riemannHypothesis_of_relative_tangent_stability`) — and the
mean value theorem converts that into a comparison with the second tangent: a pointwise majorant `G`
for the second tangent gives `‖E_η − E_ε‖_T ≤ (ε − η)‖G‖_T`, so the angle is non-obtuse as soon as
the gap times `‖G‖_T` is at most `‖E_ε‖_T` (`SecondTangentControlGivesTheAngle`). What matters is
the *ratio against the gap*, but a local angle bound on adjacent steps does not by itself control correlations with all
earlier dampings. A partition argument must also bound those accumulated cross terms.

On the actual source at horizon `T = 1`, `W_1(ε) = −(1 − Re(1/ζ(1+ε))) m(ε)/2 → −½` while
`K_1(η, ε) = m(η)m(ε)/2 → ½ > 0`, so there is a positive damping interval `(0, δ₀)` on which the
autocorrelation is strictly positive while the signed work is strictly negative
(`exists_damping_tangentCorrelation_one_pos_and_signedDampingWork_one_neg`). Moreover, relative
stability is strictly stronger than non-obtuse angle (`exists_pos_pairing_not_relative_stability`),
monotone work is strictly stronger than single sign change (`exists_single_sign_change_not_monotoneOn`),
and the no-interior-bump condition forces damping-uniform admission across `(0, ½]`
(`uniformlyAdmitsOn_of_no_interior_bump`). Integrating the autocorrelation over the square
`[a, c] × [a, c]` restores unconditional positivity and matches admission exactly:
`∫_a^c ∫_a^c K_T(η, ε) dη dε = ‖A_c − A_a‖_T² ≥ 0`
(`double_integral_tangentCorrelation_eq_pronicNorm_sub_sq`,
`double_integral_tangentCorrelation_nonneg`), and with `c` admitted a horizon-uniform bound on the
signed double integral `∫_a^c ∫_a^c K_T(η, ε) dη dε` is **equivalent** to admission at `a`
(`admits_iff_bounded_double_integral_tangentCorrelation`) and holds unconditionally on `(Θ − ½, ∞)`
and on the Vinogradov–Korobov band (`SourceAngleShapeHierarchyAndIntegratedAutocorrelation`).

### Convexity, and the second tangent as an iterated dilation

Since both ends are paid, convexity of the energy closes the problem, and convexity is exactly

`−‖E_ε‖_T² ≤ ⟪A_ε, F_ε⟫_T`

(`riemannHypothesis_of_second_tangent_pairing_ge`) — a demand with **no constant and no uniformity
in the horizon**: the source must not be anti-aligned with its own second tangent by more than the
energy of the first. The second tangent is itself a dilation: applying the pointwise logarithm twice
to `μ * 1 = δ` gives `(μ log²) * 1 = Λ * Λ − Λ log`, so `F_ε` is the source dilated by the
second-order prime kernel `K = Λ * Λ − Λ log` with an explicit polar correction
(`TheSecondTangentIsAnIteratedDilation`). The convexity criterion is thus one iterated prime
dilation of the literal source against itself.

### Prime-pair, polar and level coordinates of the obstruction

Exchanging the order of summation puts the autocorrelation in the coordinates the incidence and Gram
programmes use. With the increment `a_M(η) = Λ^{resp}_η(M) − m(η)`, where
`Λ^{resp}_η(M) = −Σ_{d∣M} μ(d) log(d)d^{−η}` is the divisor-response tangent, of the centred damped Chebyshev function (distinct from the dilation weights
`Λ(M)M^{−η}`):

- **Prime pairs.** `K_T(η, ε) = Σ_{j,k ≤ T} a_j(η) a_k(ε)/max(j,k) − E_η(T)E_ε(T)/(T+1)`, so the
  sign is the sign of one Vasyunin-type bilinear form in the damped von Mangoldt weights at two
  dampings against one explicit boundary term (`TheMaxKernelFormOfTheDampingAutocorrelation`); the
  identity also proves the Nyman–Beurling kernel positive semidefinite, with an exact formula.
- **Polar calibration.** The pole subtraction contributes one constant per prime-power cell, and the
  kernel weights sum in closed form (`Σ_{k ≤ T} 1/max(j,k) = 1 − 1/j + Σ_{j ≤ m ≤ T} 1/m`,
  `Σ_{j,k ≤ T} 1/max(j,k) = 2T − Σ_{m ≤ T} 1/m`), leaving a four-term split: one genuinely bilinear
  prime-pair form, two row-weighted prime sums and one explicit polar term
  (`ThePolarCalibrationOfTheMaxKernelForm`). The explicit terms grow linearly in the horizon, so the
  prime-pair sum must cancel them to **relative precision `1/T`**: leading-order prime asymptotics
  are not enough, and this is the exact price of the sign criterion, stated before any estimate.
- **Level collapse.** Because `1/max(j,k)` is constant on levels, the double sum is not genuinely
  bilinear: it collapses to one scale sum
  `K_T(η, ε) = Σ_{M ≤ T}(a_M(η)E_ε(M) + E_η(M)a_M(ε) − a_M(η)a_M(ε))/M − E_η(T)E_ε(T)/(T+1)`
  (`TheLevelCollapseOfTheMaxKernelForm`), a cross-correlation of an increment with the centred
  prefix at the *same* scale. On the diagonal the same identity is the discrete energy balance
  `d(E²) = 2E dE − (dE)²`.
- **Unconditional diagonal and integrated positivity up to boundary at relative precision `1/T`.**
  The polar-calibrated prime-pair form and the single-scale level-sum form are identical
  (`polarCalibratedPrimePairForm_eq_levelSum`), dominate the nonnegative boundary term
  `E_ε(T)²/(T+1)` unconditionally on the diagonal (`diagonal_polarCalibratedPrimePairForm_ge_boundary`,
  `diagonal_primePairMaxKernelForm_ge`), and satisfy the exact double-integral law
  `∫_a^c ∫_a^c L_T(η, ε) dη dε = ‖A_c − A_a‖_T² + (A_c(T) − A_a(T))²/(T+1) ≥ ∫_a^c ∫_a^c E_η(T)E_ε(T)/(T+1)`
  on every damping square `[a, c] × [a, c]` (`double_integral_levelSum_eq`,
  `double_integral_polarCalibratedPrimePairForm_ge_boundary`). Dividing by the linear scale `T + 1`,
  admission at `a` is equivalent to relative-precision `C/(T+1)` cancellation against the boundary
  term (`admits_iff_relative_precision_inv_T_primePair`), which holds unconditionally on
  `(Θ − ½, ∞)` (`exists_relative_precision_inv_T_primePair_above_zeroWidth`,
  `tendsto_relative_precision_primePair_zero_above_zeroWidth`) and on the Vinogradov–Korobov band
  (`exists_relative_precision_inv_T_primePair_on_vinogradovKorobovBand`).

### The dilation picture of the work

Differentiating the damped Möbius row multiplies its coefficients by `−log d`, and `Λ * μ = −μ log`
turns that into convolution by the damped prime row: the tangent is the source **dilated by prime
powers**, `E_ε(n) = Σ_{j ≤ n} Λ(j)j^{−ε} A_ε(⌊n/j⌋) + (m₀(ε)Ψ_ε(n) − n m(ε))`
(`TheTangentIsADilationAverageOfTheSource`). Pairing with the source makes the signed work the
**numerical range of the prime dilation operator at the literal source**, plus an explicit polar
pairing. Since `Λ = μ * log` and the damping twist is a ring homomorphism, the prime dilation
factors as `D^{Λ_ε} = D^{μ_ε} ∘ D^{(log)_ε}`, and the logarithmic dilation of the source is a
Möbius-free expression in the von Mangoldt weights and the two densities; so the tangent is the
**Möbius dilation of one explicit row**, up to an explicit correction
(`prefixDilation_dampedPrime_factor`, `dampedChebyshevError_eq_moebiusDilation`). The whole Möbius
content of the work therefore sits in a single dilation, and the work is bilinear in the Möbius
row — the shape the single-modulus bilinear mechanism of Bézout–Valuation Incidence is built for.
Five facts fix what a proof of its sign can look like.

- **No form positivity is available.** Grouped by level the form has kernel `κ_ε`, whose diagonal
  vanishes (`⌊n/j⌋ = n` forces `j = 1` and `Λ(1) = 0`) while `κ_ε(2,1) = (log 2)2^{−ε} > 0`: the
  form is a pure cross term and changes sign with the relative sign of two cells
  (`TheQuotientIncidenceKernelIsIndefinite`). The sign must be proved for the actual source, never
  for an arbitrary row.
- **The scales are exactly paid down to one half and no further.** Dilation contracts the pronic
  norm sharply, `‖v(⌊·/j⌋)‖_T ≤ j^{−1/2}‖v‖_T` for `v(0) = 0`, because a dilation fibre carries exactly `1/j` of the
  level's pronic mass (`TheDilationSelfSimilarityOfThePronicMeasure`); the off-diagonal cost of a
  term-by-term bound is therefore `Σ_{j ≥ 2} j^{−(ε+1/2)}·E_T`, and that series converges exactly
  for `ε > ½` (`ThePronicDilationContractionAndItsThreshold`). The scale sum is finite above half damping; absorbing it in a self-improving inequality
  additionally needs its coefficient below one or a separate estimate. Below half damping
  the majorant diverges, which is why the anti-correlation must be signed. Every finite head
  of the dilation scales is paid.
- **The source satisfies exact laws against every dilation kernel.** The prefix dilations represent
  the Dirichlet ring exactly, `Λ_ε * ζ_ε = (log)_ε` is the damped form of `Λ * 1 = log`, and
  composing with the inversion law gives an explicit linear law for the centred source against the
  damped logarithmic row (`TheDilationCalculusOnIntegerPrefixes`,
  `TheDilationInversionLawOfTheSource`, `TheTangentObeysAnExplicitDilationLaw`). These laws are the
  structural input the indefiniteness of the kernel demands.
- **The work is a correlation with the source's own window means.** The pronic adjoint of the
  dilation by `j` is an averaging operator over the fibre of horizons it folds together, and by the
  self-similarity of the pronic measure it is `1/j` times a genuine average; so the dilation form —
  hence the work — is the correlation of the source with its block averages over
  `[jm, jm + j − 1]`, weighted by `Λ(j)j^{−ε}` (`TheWorkIsACorrelationWithWindowMeans`). That is the
  shape analytic methods handle: a smoothing of the source against itself.
- **The form has a positive core.** At zero damping the source collapses to the constant one, and a
  constant row is positively correlated with its own prime dilations:
  `Q_ε(1) = Σ_{n ≤ T} ψ_ε(n)/(n(n+1)) ≥ 0` (strict for `T≥2`), with `ψ_ε(n) = Σ_{j ≤ n} Λ(j)j^{−ε}`. Splitting at the
  constant keeps every cross term, so the sign of the work is the sign of a positive explicit core
  plus two explicit *linear* functionals of `A_ε − 1` plus the residual's own dilation form
  (`ThePositiveCoreOfTheDilationForm`); renormalisation neutrality makes the quadratic residual the
  only unpaid part, and it vanishes with the deviation from constancy. The deviation row is exactly
  the source minus the constant one, so its pronic energy *is* the Báez–Duarte residual, and the
  quadratic term is at most `Θ_ε(T)` times that residual, hence at most `3Θ_ε(T)(1 + E_T(ε))`, with
  `Θ_ε(T) = Σ_{j ≤ T} Λ(j)j^{−(ε+1/2)}` (`pronicNorm_deviationRow_sq`, `abs_workQuadratic_le_energy`):
  the accounting closes in the programme's own units, and its one unpaid coefficient converges
  exactly above half damping. The core itself has explicit units: the powers of two alone give
  `ψ_ε(n) ≥ (log 2)/(4ε)` once `n ≥ 2^{1/ε}` (`dampedPrimePrefix_ge_inv_damping`), so it is `O(1)`
  before the horizon `2^{1/ε}` and of order `1/ε` beyond it.
- **The core has an explicit damping-endpoint law.** Sum
  the integrated core by *scales* rather than by horizons: the pronic weights telescope,
  `Σ_{n = j}^{T} 1/(n(n+1)) = 1/j − 1/(T+1)`, leaving one sum over scales
  `∫_η^ε core_x(T) dx = Σ_{j ≤ T} (Λ(j)/log j)(j^{−η} − j^{−ε})(1/j − 1/(T+1))`
  (`integral_workCore_eq_scaleSum`). The density `Λ(j)/log j` is `1` at a prime and `1/k` at a
  `k`-th prime power, so the scale sum *is* a prime harmonic series, its prime terms being
  `(p^{−η} − p^{−ε})(1/p − 1/(T+1))`. For the zero-anchored integral (`η = 0`) the core grows without bound
  in the horizon, with prime-harmonic growth `Σ_{p ≤ T} 1/p`. For a fixed positive `η`, the
  factors `p^{−η}` instead make the horizon sum convergent. More precisely, for `0<η≤ε`,
  its limit is `log ζ(1+η)−log ζ(1+ε)` and the same quantity bounds every finite horizon
  (`ArithmeticCompensationTheory.tendsto_integral_workCore_logZeta`,
  `ArithmeticCompensationTheory.integral_workCore_le_logZeta`). The zero-anchor divergence is proved by
  (`exists_horizon_integral_workCore_ge`). The explicit positive core is therefore a **debt of size
  `log log T`**, and under any energy budget the integrated deviation must carry it: it tends to
  `−∞` along the horizons (`integral_workDeviation_le_primeHarmonic`). This is the sharpest
  cancellation demanded by admission in this zero-anchored decomposition. The only way the critical energy can stay bounded is that the
  source's deviation from constancy cancels, to leading order, the prime harmonic growth of its own
  tangent — cancellation of the divergent zero-anchored core. The cited theorem proves unboundedness;
  an exact asymptotic for the complete deviation is a separate statement. Two consequences for
  method choice: a horizon-uniform absolute bound on the complete **zero-anchored** deviation is
  impossible under admission. This does not obstruct bounds on a fixed positive interval, where
  constants may depend on its endpoints. The function-field calibration has a different finite
  source and does not supply the number-field cancellation estimate.

### The self-improving identity: admission at a single damping

The damped unit dilation differs from the prime dilation in one decisive respect — its weight at
`j = 1` is `1`, not `Λ(1) = 0` — so its diagonal *is* the critical energy, and the inversion law
turns that diagonal into an explicit linear pairing:

`E_T(ε) = ⟪A_ε, ρ_ε⟫_T − ⟪A_ε, D^{ζ_ε,≥2}A_ε⟫_T`,  `ρ_ε(n) = n − m₀(ε)Φ_ε(n)`

(`TheSelfImprovingEnergyIdentity`). No transport, no interval and no horizon-free budget appear: if
at one damping both pairings are at most `κ√E_T + κ'`, the identity closes on itself and the energy
is bounded by `(κ + √(κ² + 2κ'))²`, so that damping is admitted, and cofinal versions give RH. The
defect of the inversion law is moreover **nonnegative**, `0 ≤ ρ_ε(n) ≤ n`, with
`(density).re = 1/realZetaSeries(1+ε)`, so only the positive excursions of the centred source feed
the explicit term and the criterion becomes one-sided: a sublinear bound on the *positive part* of
the source against an explicit positive weight, plus a lower bound on the off-diagonal
anti-correlation (`TheInversionDefectIsPositive`). Crucially, the inversion defect is the negative
majorant prefix times the density, `ρ_ε(n) = −m₀(ε) A_ε^{maj}(n)`, so `‖ρ_ε‖_T² = m₀(ε)² E_T^{maj}(ε)`
(`pronicNorm_inversionDefect_sq_eq`). Hence `‖ρ_ε‖_T` diverges for `0 < ε ≤ ½`
(`not_bddAbove_pronicNorm_inversionDefect_of_le_half`) and is uniformly bounded for `ε > ½`
(`exists_pronicNorm_inversionDefect_le_of_half_lt`), establishing the exact threshold dichotomy
`Admits majorantEnergy ε ↔ ½ < ε` (`admits_majorantEnergy_iff_half_lt`) and unconditional one-sided
sublinear pairings `⟪A_ε⁺, ρ_ε⟫_T ≤ κ√E_T(ε)` and `|⟪A_ε, D^{ζ_ε,≥2}A_ε⟫_T| ≤ κ√E_T(ε)` above half
damping (`exists_onesided_sublinear_pairings_of_half_lt`). At any damping `ε > 0` and integer scale
`q ≥ 2`, admission `Admits dampedMobiusEnergy ε`, `ε ∈ receiverDampings`, localized block-energy
admission `Admits (dampedBlockEnergy q) ε`, and the combined sublinear pairing bound
`⟪A_ε, ρ_ε⟫_T − ⟪A_ε, D^{ζ_ε,≥2}A_ε⟫_T ≤ κ√E_T(ε) + κ'` are four-way equivalent
(`singleDamping_admission_tfae`), with `dampedBlockEnergy q ε` unconditionally bounded above
`Θ − ½` and on the Vinogradov–Korobov band (`admits_dampedBlockEnergy_of_zetaZeroAbscissa_sub_half_lt`,
`exists_dampedBlockEnergy_le_on_vinogradovKorobovBand`).

### Dilation graph and block energy

For a row `v`, put `Q_ε(v) = Σ_{n≤T} Σ_{j≤n} Λ(j)j^{−ε}v(n)v(⌊n/j⌋)/(n(n+1))`.
Polarising every edge gives `2Q_ε(v) = M_ε(v) − J_ε(v)`, where `M` sums the squares at both
endpoints and `J` sums their squared differences (`two_mul_rowDilationForm_eq`). On the actual
source the work includes the polar correction `P_ε`, so its nonnegativity is
`J_ε(A) ≤ M_ε(A) + 2P_ε`. Omitting that correction changes the criterion. The inequality
`Q_ε(v) ≤ Q_ε(|v|)` locates the sign issue in the source's oscillations; it does not make the
signed form positive.

The pronic contraction also gives a Hardy inequality for one fixed integer `q ≥ 2`:

    ‖v‖²_T ≤ q/(√q − 1)² · Σ_{n≤T}(v(n) − v(⌊n/q⌋))²/(n(n+1)),    v(0) = 0.

The reverse bound has constant `2(1 + 1/q)` (`pronicNorm_sq_le_dilationStepEnergy`,
`dilationStepEnergy_le`). For `A_ε`, the difference is the centred divisor sum over
`(⌊n/q⌋, n]`. Thus a uniform pronic mean square of these blocks is equivalent to admission;
at `q = 2` the forward constant is `6 + 4√2`. This is a concrete target for short-sum methods,
with no loss of the norm or of the horizon quantifier.

### The zero anchor and signed excursions

At each fixed horizon `A_ε → 1` as `ε ↓ 0`, so the energy tends to the pronic mass, at most one.
Consequently admission at a positive `ε` is equivalent to a bound on
`∫_η^ε 2W_T` uniform in `T` and `0 < η ≤ ε`
(`admits_of_work_integral_bound`, `work_integral_le_of_bddAbove`). Cofinal such bounds give RH.
This uses the signed work; it imposes no bound on its total variation.

An interior excursion has a necessary geometric cost:
`∫_a^c ‖∂_ε A_x‖_T dx ≥ 2√E_T(ε) − √E_T(a) − √E_T(c)` for `a ≤ ε ≤ c`.
Also at most `1 + 1/δ` unit tangents can be pairwise correlated by at most `−δ`. These constrain
excursions and pairwise anti-alignment, respectively. Neither bounds the measure of all negatively
correlated damping pairs, nor the accumulated signed work, without a further arithmetic estimate.

### Selectivity: the majorant source is never admitted

Every estimate that uses only the sizes of the coefficients applies verbatim to the row `d ↦ d^{−ε}`,
which dominates `|μ(d)d^{−ε}|` cell by cell. That row is a legitimate arithmetic source with the same
divisor prefix, the same pole subtraction and the same observation weight, and it is **never
admitted** at or below half damping: the floor is at most the quotient, so
`A^{maj}_ε(n) ≤ −2^{−(1+ε)}n^{1−ε}`, and the pronic energy of a row that size diverges whenever
`Σ n^{−2ε}` does (`TheMajorantSourceIsNeverAdmitted`). So the Möbius signs are not a convenience of
the proof: any argument that survives replacing `μ(d)d^{−ε}` by its absolute value proves a false
statement below the threshold. This is the layer's own selectivity certificate, and it is
unconditional.

### The mirror form: no crossing of a ground floor, and the aperture instance

On the aperture side the question is mirrored: a ground floor must not reach zero as the aperture
grows. Read through `Ψ = log` on a positive floor the master inequality becomes
(`floor_le_of_relative_decay`)

`−μ'(A) ≤ β'(A)·μ(A)` on `[a, c]`  ⟹  `μ(c) ≥ μ(a)·exp(−(β(c) − β(a)))`,

a bound on the *relative* decay, not on the decay; under a budget with nonnegative derivative the
same explicit positive bound holds uniformly on the interval, so a first crossing forces the relative
decay to exceed every budget of finite total on the interval leading to it. This is a quantitative no-crossing law.

The ground energy is an infimum over a form domain and need not be differentiated. A discrete
relative bound gives `μ_J ≥ μ_0 ∏_{i<J}(1 − c_i)`; an additive one gives
`μ_J ≥ μ_0 − Σ_{i<J} r_i`. These are valid finite-interval transport tools. However, retaining a
fixed positive margin along an unbounded aperture sequence is impossible: ACT proves an
unconditional upper bound for `μ(A)` tending to zero doubly exponentially. In particular the
half-summable relative-loss and fixed-margin additive criteria cannot be realised on such a
sequence for this ground energy. Compensation Theory makes the constraint quantitative: a floor
`μ(A)≥m₀e^{−B(A)}` forces `B(A)≥πe^{2(A−2)}−(11/2)A+log(m₀/K)`, and even harmonic-product
transport is too slow along linearly growing apertures (`TheApertureFloorMustDecayDoublyExponentially`).

The useful target is non-crossing with a lower bound allowed to tend to zero, or a graded negative
floor. Along any unbounded sequence `A_j → ∞` starting at `(A 0).1 ≤ 3/10`, a relative step bound
`(1 − c_j) μ(A_j) ≤ μ(A_{j+1})` with `c_j < 1` keeps the floor `(∏_{i<J}(1 − c_i))/5000` **strictly
positive** at every finite stage `J` (`0 < μ(A_J)`, excluding finite contact and certifying
`ZetaWindowPositive B` for `0 < B < A_J`) while allowing `∏_{i<J}(1 − c_i) → 0` at the doubly
exponential Gaussian ceiling rate, and proves RH (`strict_vanishing_relative_step`,
`riemannHypothesis_of_vanishing_relative_step`). Along a monotone unbounded sequence `A_j → ∞`, RH
is four-way equivalent to the existence of relative step factors `0 ≤ q_j`, to the partial-sum
spectral jump bound `∀ J, ∑_{j<J} Δ_spec(A_j, A_{j+1}) ≤ μ(A_0)`, and to `HasSum Δ_spec (μ(A_0))`
(`vanishing_aperture_transport_tfae`), while monotonicity of the ceiling-renormalized Lyapunov
functional `ceilingScaledGroundEnergy A = e^{β_ceil(A)} μ(A)` (unconditionally bounded above by `K`
for `A ≥ 3`, `exists_ceilingScaledGroundEnergy_le`) propagates the doubly exponential positive floor
`(1/5000) e^{β_ceil(A_0)} e^{apertureCeilingExponent(A_J)}` (`riemannHypothesis_of_ceilingScaledGroundEnergy_mono`).
Alternatively, a graded negative-floor step `e^{−2σA_{j+1}} μ(A_{j+1}) ≥ e^{−2σA_j} μ(A_j) − e^{−2σA_{j+1}} δ_j`
along `A_j → ∞` with bounded step gaps `A_{j+1} − A_j ≤ Δ` upgrades by antitonicity of `μ` to the
continuous `CompensatedWidthFloor σ`, bounding `zetaZeroWidth ≤ σ`, `polarGroundEnergyRate ≤ σ`, and
transporting damping admission on `(σ, ∞)` (`compensatedWidthFloor_of_discrete_aperture_sequence`,
`zetaZeroWidth_le_of_graded_aperture_step`, `averagedDampingContinuation_of_graded_aperture_step`).

### The cutoff parameter is free

The denominator cutoff is the layer's second parameter. The Ramanujan truncation error pays every
cutoff change along a compatible sequence of growing heads, the exact stage balance retains its
signed cross term and its new physical shell, and the transport depth is dyadically summable. The
accumulated shell cost — the cutoff analogue of the damping budget — is not a second arithmetic
obligation: on a shell the Ramanujan prefix differs from the actual source by at most
`n Q^{−β}C_{ε,β}`, each stage costs at most twice the actual energy of its own cells plus one
geometric term, and along the dyadic schedule the cells of different stages are disjoint and exhaust
the horizon, so the shells telescope into the critical energy and the geometric terms sum. Given
admission at a damping, the accumulated shell cost is bounded there with no further arithmetic input
(`TheCutoffParameterCostsNothingBeyondAdmission`). The open obligation of the layer is the damping
one alone.

### The aperture parameter: unsigned depth sampling

At a single positive aperture a source-uniform bound controls squared off-line depths on every
unit-height window, with literal complex smooth interior probes, and conversely, so the two are
equivalent (the sampling side is maintained in
`SquareRootThreshold/UnsignedDepthSamplingDetectsLocalMass.lean`). This identifies the hypothesis
under which the width equals the ground-energy rate with a sampling statement about the source. It
is unsigned difference energy, not the signed Weil floor: it bounds the *hypothesis* of the floor
theorem rather than the floor, and an aperture-dependent constant at even one aperture already
reinstates the local-depth condition. Polarising each zero-copy term on the smooth core gives
`Q_a(u) = E_+(u) − E_−(u)` with `E_±(u) = ¼ Σ_q ‖û(−z_q) ± û(−z̄_q)‖²` unconditionally summable
(`summable_pairedPlusTerm`, `summable_pairedMinusTerm`,
`sourceQuadratic_eq_pairedPlusEnergy_sub_pairedMinusEnergy`). Consequently the compensated sampling
bound `E_−(u) ≤ E_+(u) + B ‖u‖₂²` at aperture `a` is **equivalent** to `−B ≤ μ(a)`
(`compensatedSamplingBound_iff_groundEnergy_ge`), holds unconditionally at every aperture
(`exists_compensatedSamplingBound`), and holds with `B = −1/5000 < 0` on `a ≤ 3/10`
(`compensatedSamplingBound_neg_one_div_5000_of_le_three_tenths`). Across apertures,
`CompensatedWidthFloor σ` (`E_−(u) ≤ E_+(u) + C e^{2σa} ‖u‖₂²`) is equivalent to
`μ(A) ≥ −C e^{2σA}` (`compensatedWidthFloor_iff_groundEnergy_ge_neg_exp`), bounds `zetaZeroWidth ≤ σ`
and `polarGroundEnergyRate ≤ σ` (`zetaZeroWidth_le_of_compensatedWidthFloor`,
`polarGroundEnergyRate_le_of_compensatedWidthFloor`), and holding for every `σ > zetaZeroWidth`
closes `polarGroundEnergyRate = groundEnergyRate = zetaZeroWidth`
(`polarGroundEnergyRate_eq_zetaZeroWidth_of_forall_compensatedWidthFloor`), which holds under
`OffLineDepthLocallyBounded W` or `OffLineCopiesLocallyBounded M`
(`compensatedWidthFloor_of_offLineDepthLocallyBounded`,
`compensatedWidthFloor_of_offLineCopiesLocallyBounded`).

### Iterated compensation

A compensation between a sector and its complement is useful only if it iterates. The abstract shape
is the affine recurrence `F_{j+1} ≤ q_j F_j + r_j`, with closed form `affineEnvelope_eq` and the
usable criterion: multipliers below `θ < 1` and sources below `R` give the stage-free bound
`max(F₀, R/(1−θ))` (`affineEnvelope_le_of_contraction`). The contraction is not a formality —
`affineEnvelope_one_one` shows unit multipliers with unit sources diverge linearly — so a scheme that
merely cancels at leading order per stage proves nothing. On the actual source along the dyadic
Ramanujan schedule `(Q_j, R_j) = (2^j, 2^{m(j+1)})`, the complementary denominator defect
`D_{Q,R} = A_ε − R_Q` obeys the exact two-stage identity
`R_{Q_{j+1}} = R_{Q_j} + S_{Q_j, Q_{j+1}}`, `D_{Q_{j+1}} = D_{Q_j} − S_{Q_j, Q_{j+1}}`
(`ramanujanPrefix_stage_step`, `complementarySector_step_eq`), and for every contraction parameter
`θ ∈ (0, 1)` the reweighted shell residual `F_j = θ^j ‖R_{Q_j}(R_j)‖² + E^{shell}_j` satisfies the
exact contracting recurrence `F_{j+1} ≤ θ F_j + r_j` (`reweightedShellResidual_step_le`) with stage-
uniform ceiling `F_j ≤ max(F_0, R/(1−θ))` (`exists_reweightedShellResidual_contracting_bound_of_admits`).
Moreover, admission `Admits dampedMobiusEnergy ε`, `ε ∈ receiverDampings`, bounded dyadic Ramanujan
prefix energy `BddAbove (range (dyadicRamanujanPrefixEnergy m ε))`, and the contracting affine
envelope bound are four-way equivalent (`complementarySectorPropagation_tfae`), holding
unconditionally on `(Θ − ½, ∞)` (`exists_dyadicRamanujanPrefixEnergy_le_of_zetaZeroAbscissa_sub_half_lt`)
and on the Vinogradov–Korobov band (`exists_dyadicRamanujanPrefixEnergy_le_on_vinogradovKorobovBand`).

### What is already paid, and what is not

Subtracting the constant source is a renormalisation that changes the signed work by a scalar
moment, and that moment is *uniformly paid*: the absolute first pronic moment of the damped
Chebyshev tangent has one bound valid for every horizon and every damping above a fixed positive
number (`exists_uniform_scalar_damping_work_bound`); the tangent itself need not have bounded
critical square energy, so this is strictly less than the tangent-norm demand. The renormalisation is
neutral — the original energy and its residual at the constant source have uniformly comparable
shifted energies, admission holds for one exactly when for the other, and a linear budget exists for
one exactly when for the other (`linearContinuation_residual_iff`). So the open demand is the
*covariance* part of the signed work and nothing else; subtracting means does not move it.

The residual half carries a sharp obstruction. The literal residual has a linear cusp — a critical
zero gives `c > 0` such that every sufficiently small damping has a horizon with `D_T(ε) > cε`,
through the exact step-source Mellin identity including its floor correction — so although the
residual work tends to zero at each fixed horizon, the mean value theorem produces positive work at
arbitrarily small damping and arbitrarily large horizons. Positive work escaping every fixed horizon
is what a horizon-free budget has to absorb, and it rules out proving the covariance demand by a
fixed-horizon limit.

### The function-field calibration

Over `F_q[T]` the reciprocal of the zeta function of the polynomial ring is a *polynomial*: the
degree-wise Möbius sums are `1`, `−q`, and `0` beyond degree one. Building the damped source with
the same divisor prefix, the same pole subtraction `1 − q^{−ε}` and the same observation weight makes
the centred prefix **exactly constant**, `A^{F_q}_ε(n) = q^{−ε}` for every degree `n ≥ 1` and every
damping, so the critical energy is bounded by one uniformly in the damping and the horizon so admission follows directly from the explicit formula (`TheFunctionFieldCalibration`). Adding any positive mass at degree two
while keeping the centring makes the prefix grow without bound. The calibration therefore places the
whole number-field difficulty in the absence of that exact cancellation, not in the shape of the
transport mechanism.

---

## 4. Foundational pillar theorems

All unconditional; RH appears only inside equivalences or as a conclusion.

1. **The master inequality and transport.** A scale-read loss bounded by a budget makes
   `Ψ ∘ E_T + β` monotone (`scaledEnergy_add_budget_le`); linear and coercive Osgood budgets transport
   admission from an admitted right end (`Admits.of_linearContinuation`, `Admits.of_osgoodContinuation`).
2. **The exact derivative.** `∂_ε E_T(ε) = 2W_T(ε)` (`hasDerivAt_dampedMobiusEnergy`), equal to the
   Markov boundary-flux form (`two_mul_signedDampingWork_eq_markov`), and the work integral is the
   energy drop (`TheWorkIntegralIsTheEnergyDrop`).
3. **The averaged budget is admission.** With an admitted right end, an averaged budget holds iff
   the left end is admitted (`averagedContinuation_iff_admits`), and cofinal averaged budgets are RH
   (`riemannHypothesis_iff_cofinal_averagedDampingContinuation`); a pointwise budget is strictly
   stronger (`exists_admits_everywhere_not_linearContinuation`).
4. **The partial deliverable.** A budget on `(a₀, c]` gives `Θ ≤ ½ + a₀`
   (`zetaZeroAbscissa_le_half_add_of_partial_dampingContinuation`).
5. **Both ends are paid.** The energy tends to the pronic mass as `ε ↓ 0`
   (`tendsto_dampedMobiusEnergy_nhdsGT_zero`), so RH is the absence of an interior bump
   (`riemannHypothesis_of_no_interior_bump`), and one forbidden order of sign change of the work
   suffices (`riemannHypothesis_of_signedWork_single_sign_change`).
6. **The sign is an angle.** The work is the autocorrelation of the tangent family; relative tangent
   stability gives RH (`riemannHypothesis_of_relative_tangent_stability`), and convexity is a
   pairing with the second tangent, itself an iterated prime dilation
   (`riemannHypothesis_of_second_tangent_pairing_ge`).
7. **The dilation calculus.** Prefix dilations represent the Dirichlet ring exactly
   (`TheDilationCalculusOnIntegerPrefixes`); the pronic contraction `j^{−1/2}` makes the scale sum
   finite exactly above half damping (`ThePronicDilationContractionAndItsThreshold`); the quotient
   incidence kernel is indefinite (`TheQuotientIncidenceKernelIsIndefinite`).
8. **The self-improving identity.** At one damping, the energy is a linear pairing with the
   nonnegative inversion defect minus the source's anti-correlation with its proper dilations
   (`TheSelfImprovingEnergyIdentity`, `TheInversionDefectIsPositive`).
9. **Block energy is admission.** For fixed `q ≥ 2` the pronic norm is equivalent to the energy of
   the one-step dilation blocks (`pronicNorm_sq_le_dilationStepEnergy`, `dilationStepEnergy_le`).
10. **Selectivity.** The majorant row `d^{−ε}` is never admitted at or below half damping
    (`TheMajorantSourceIsNeverAdmitted`), and over `F_q[T]` the centred prefix is exactly constant
    (`TheFunctionFieldCalibration`).
11. **Admission translates zeros with multiplicity, up to the boundary**
    (`analyticOrderAt_le_analyticOrderAt_sub_of_mem_receiverDampings`).
12. **The cutoff parameter is free** given admission (`TheCutoffParameterCostsNothingBeyondAdmission`).

---

## 5. Traps

- **Horizon-dependent budgets transport nothing.** `escapeEnergy ε T = exp(2(½−ε) log(T+1)) − 1`
  vanishes at the endpoint `ε = ½`, satisfies the *exact* linear continuation identity
  `−∂_ε Esc_T = 2 log(T+1)·(1 + Esc_T)` with a coefficient finite for each horizon, and is admitted
  at no damping below `½` (`HorizonUniformityIsTheTheorem`). The placement of the horizon quantifier
  is the mathematics, not a convenience of the formulation.
- **The pointwise budget is not implied by RH.** A family can be admitted at every parameter and
  carry no pointwise linear budget on any interval. Stating the layer's open demand pointwise asks
  for more than the conclusion; the averaged form is equivalent to it.
- **The tangent norm is a strictly stronger demand.** A row rotating in two pronic cells at
  frequency `K` has constant energy, identically vanishing signed work, and tangent norm `|K|`
  (`exists_vanishing_signed_work_with_large_tangent`). A continuation budget yields no bound whatever
  on the tangent norm; attacking the norm is attacking a harder problem.
- **No positivity of the dilation kernel is available.** The quotient incidence kernel has zero
  diagonal and a positive off-diagonal entry at `(2,1)`, so the dilation form is indefinite on rows.
  A proof must use the actual source, with its polar correction.
- **An absolute dilation estimate cannot reach below half damping.** The term-by-term cost is
  `√2 Σ_{j ≥ 2} j^{−(ε+1/2)}`, which converges exactly for `ε > ½`. The prospective input is a lower
  bound on the signed numerical range along the literal source, not a majorant.
- **Size-blind arguments are refuted, not merely unselective.** The majorant row `d^{−ε}` has the
  same sizes and is never admitted at or below half damping, so any argument surviving the removal of
  the Möbius signs proves a false statement.
- **The deviation terms cannot be bounded in absolute value.** The zero-anchored integrated core contains a divergent prime
  harmonic series, so admission forces the integrated deviation to `−∞` along
  the horizons. Any estimate that discards the deviation's sign — a majorant, a triangle
  inequality, an `ℓ¹` bound — contradicts a proved divergence. This divergence concerns the joint zero-damping and large-horizon limit, not a fixed interval
  bounded away from zero.
- **Ratio smallness is not a bound.** A complete energy can tend to infinity while its ratio to a
  sector energy tends to zero. A proved ratio limit is evidence of a mechanism, not an admission
  statement; what must improve is the rate in the complete norm, with the horizon and cutoff
  quantifiers intact.
- **Sector energies may not be added.** `m` identical sectors have complete energy `m²` times a
  sector energy while the sum of the sector energies is `m` times it; the cross terms carry the whole
  cost (`pronicNorm_add_sq`). A decomposition is useful only with its interaction terms attached.
- **A scale without coercivity says nothing.** A bound on `Ψ ∘ E` for a bounded `Ψ` is vacuous; the
  Osgood hypothesis enters only as `Tendsto Ψ atTop atTop`.
- **A fixed positive aperture margin cannot persist.** The ground-energy upper bound tends to
  zero unconditionally. Relative transport may have a product tending to zero; positivity at each
  finite stage, or a graded negative floor, is the relevant demand.
- **Recovery is not control.** An injective observation map, even a complete invariant, supplies no
  bound. All logarithmic pronic moments determine a damped source, and yet admission is incompatible
  with an unweighted uniform lower modulus
  (`RHTower.not_exists_uniform_lower_bound_primeGammaCauchyHorizonGrade`); rows agreeing in every
  stationary translated moment split the receiver. A theorem using finitely many moments must state
  how its constants depend on the number of moments, the damping and the horizon.
- **Compactness in the wrong space is not an estimate.** The chain's centered transition is compact
  on `c₀` and its rows converge in total variation, but the entrance tail is not square-summable at
  or below half damping while the reciprocal observable's omitted tail is. Those objects belong to
  `BezoutValuationIncidence`; what this layer takes from them is the choice of observable, not a
  critical Hilbert-space bound.
- **The integer prefix is not the real-centred extension.** Replacing `A_ε(⌊x⌋)` by the real-centred
  `𝒜_ε(x)` introduces a fractional-part correction; the convolution identity
  `∂_ε 𝒜_ε(x) = Σ_k Λ(k)k^{−ε}𝒜_ε(x/k)` holds for the extension and its `k > x` tail is a convergent
  pole tail, not zero. The two must not be silently identified.
- **Leading-order prime asymptotics cannot settle the sign.** In prime-pair coordinates the explicit
  polar and row-weighted terms grow linearly in the horizon, so the prime-pair form must cancel them
  to relative precision `1/T`.

---

## 6. Questions the theory answers and the tools it builds

### 6.1 Questions

1. **What exactly must be estimated to transport a finite critical energy to smaller damping?** A
   horizon-free bound on the signed relative-loss integral over each compact interval — equivalent
   to admission at its left end, and strictly weaker than any pointwise or norm demand.
2. **Where can the energy escape?** Only through an interior bump drifting to zero as the horizon
   grows; both ends are paid.
3. **What is the arithmetic shape of the obstruction?** Off-diagonal anti-correlation of the
   damping tangents — equivalently the numerical range of the prime dilation operator at the literal
   source, a correlation of the source with its own window means, with an explicit positive core
   whose zero-anchored integral diverges like `log log T`.
4. **Which demands are false or vacuous?** Global nonnegative work, positive-part budgets, horizon-
   dependent budgets, size-blind estimates, a fixed positive aperture margin.
5. **What does a single admitted damping say?** Zeros translate with multiplicity; the width is
   read only by accumulation.

### 6.2 Tools

Built and reusable:

- *Energy families* with the admission hierarchy and horizon sampling laws.
- *The master inequality* with linear, Osgood and superlinear scales; discrete relative and additive
  transport; the affine envelope.
- *Work identities*: the exact derivative, the Markov face, the work integral, the zero anchor.
- *The tangent autocorrelation* with polarisation, relative stability and second-tangent control.
- *The dilation calculus* on integer prefixes: composition, inversion law, pronic contraction,
  window means, positive core, Hardy and block-energy inequalities.
- *Coordinates*: prime-pair (Nyman–Beurling max-kernel), polar calibration, level collapse.
- *Calibrations*: the majorant row, the function-field source, the escape family.

To be built:

- a source-derived signed estimate of the averaged relative loss on a compact interval below the
  admission frontier;
- a contraction factor for an iterated sector-compensation scheme on the actual Möbius row;
- a uniform pronic mean square of the short blocks `(⌊n/q⌋, n]` of the centred divisor sum;
- an aperture step estimate compatible with the doubly exponential ceiling.

---

## 7. Open problems

1. **Signed averaged continuation (Resolved: `SignedAveragedContinuationAndTheZeroWidthBand`).**
   For `0 < a ≤ c` with admitted `c`, admission at `a`, `a ∈ receiverDampings`, relative-loss
   averaged continuation `∫_a^c r_T ≤ C`, dyadic relative-loss continuation `∫_a^c r_{2^k} ≤ C`,
   additive signed work continuation `∫_a^c −2W_T ≤ C`, dyadic additive work continuation, Cesàro
   additive work continuation, and residual averaged continuation `AveragedResidualContinuation a c`
   are eight-way equivalent (`signedAveragedContinuation_tfae`). All eight hold unconditionally on
   every compact interval `[a, c] ⊂ (Θ − ½, ∞)`, the infimum threshold for continuation is
   `Δ = Θ − ½` (`sInf_averagedContinuationThresholds_eq_zetaZeroAbscissa_sub_half`), boundary
   continuation at `Δ` forces a critical-line shadow zero of at least the extremal multiplicity
   (`analyticOrderAt_le_of_averagedDampingContinuation_at_zeroWidth`), and on the Vinogradov–Korobov
   band `a ≥ ½ − κ σ(T)/(480 log T)` the signed work and relative-loss integrals are bounded
   uniformly in `(T, a, c)` (`exists_signedWorkIntegral_and_relativeLoss_le_on_vinogradovKorobovBand`)
   with sub-power saving `O_a(T^{1−2a} exp(−κ σ(T)/270))` at every fixed `0 < a < ½`
   (`eventually_signedWorkIntegral_and_relativeLoss_le_vk_saving`).
2. **Source-specific angle or shape control (Resolved: `SourceAngleShapeHierarchyAndIntegratedAutocorrelation`).**
   At `T = 1`, `K_1(η, ε) = m(η)m(ε)/2 > 0` while `W_1(ε) < 0` on `(0, δ₀)`
   (`exists_damping_tangentCorrelation_one_pos_and_signedDampingWork_one_neg`); relative tangent
   stability is strictly stronger than `0 ≤ K_T` (`exists_pos_pairing_not_relative_stability`);
   monotone work is strictly stronger than single sign change (`exists_single_sign_change_not_monotoneOn`);
   and no-interior-bump forces `UniformlyAdmitsOn dampedMobiusEnergy (Ioc 0 (1/2))`
   (`uniformlyAdmitsOn_of_no_interior_bump`). The weaker signed integrated estimate that survives
   off-diagonal negativity is the double damping integral
   `∫_a^c ∫_a^c K_T(η, ε) dη dε = ‖A_c − A_a‖_T² ≥ 0`
   (`double_integral_tangentCorrelation_eq_pronicNorm_sub_sq`,
   `double_integral_tangentCorrelation_nonneg`), whose horizon-uniform boundedness is **equivalent**
   to admission at `a` (`admits_iff_bounded_double_integral_tangentCorrelation`) and holds
   unconditionally on `(Θ − ½, ∞)` and on the Vinogradov–Korobov band
   (`exists_double_integral_tangentCorrelation_le_of_zetaZeroAbscissa_sub_half_lt`,
   `exists_double_integral_tangentCorrelation_le_on_vinogradovKorobovBand`).
3. **The prime-pair form to relative precision `1/T` (Resolved: `PrimePairLevelSumAndRelativePrecisionCancellation`).**
   The polar-calibrated prime-pair form `P_T(η, ε) − m(ε)R_T(η) − m(η)R_T(ε) + m(η)m(ε)(2T − H_T)`
   equals the single-scale level sum `L_T(η, ε)` (`polarCalibratedPrimePairForm_eq_levelSum`), is
   unconditionally nonnegative up to `E_ε(T)²/(T+1)` on the diagonal
   (`diagonal_polarCalibratedPrimePairForm_ge_boundary`), and satisfies the unconditional integrated
   positivity law `∫_a^c ∫_a^c L_T(η, ε) dη dε = ‖A_c − A_a‖_T² + (A_c(T) − A_a(T))²/(T+1) ≥ ∫_a^c ∫_a^c boundary ≥ 0`
   on every `[a, c] × [a, c]` (`double_integral_polarCalibratedPrimePairForm_ge_boundary`). Relative
   to the linear scale `T + 1`, cancellation of the boundary-adjusted integral at precision
   `C/(T+1)` is equivalent to admission (`admits_iff_relative_precision_inv_T_primePair`) and holds
   unconditionally on `(Θ − ½, ∞)` and on the Vinogradov–Korobov band
   (`exists_relative_precision_inv_T_primePair_above_zeroWidth`,
   `exists_relative_precision_inv_T_primePair_on_vinogradovKorobovBand`).
4. **The one-sided sublinear pairing at a single damping (Resolved: `SingleDampingSublinearPairingAndBlockEnergy`).**
   The inversion defect satisfies `ρ_ε(n) = −m₀(ε) A_ε^{maj}(n)` and `‖ρ_ε‖_T² = m₀(ε)² E_T^{maj}(ε)`
   (`inversionDefect_eq_neg_density_mul_majorantCenteredPrefix`, `pronicNorm_inversionDefect_sq_eq`),
   so `‖ρ_ε‖_T` diverges on `(0, ½]` (`not_bddAbove_pronicNorm_inversionDefect_of_le_half`) and is
   bounded on `(½, ∞)` (`exists_pronicNorm_inversionDefect_le_of_half_lt`), giving the exact
   majorant threshold `Admits majorantEnergy ε ↔ ½ < ε` (`admits_majorantEnergy_iff_half_lt`) and
   unconditional one-sided sublinear pairings `⟪A_ε, ρ_ε⟫_T ≤ ⟪A_ε⁺, ρ_ε⟫_T ≤ κ√E_T(ε)` and
   `|⟪A_ε, D^{ζ_ε,≥2}A_ε⟫_T| ≤ κ√E_T(ε)` for `ε > ½`
   (`exists_onesided_sublinear_pairings_of_half_lt`). At any `ε > 0` and integer scale `q ≥ 2`,
   `Admits dampedMobiusEnergy ε`, `ε ∈ receiverDampings`, `Admits (dampedBlockEnergy q) ε`, and the
   combined sublinear pairing bound `⟪A_ε, ρ_ε⟫_T − ⟪A_ε, D^{ζ_ε,≥2}A_ε⟫_T ≤ κ√E_T(ε) + κ'` are
   four-way equivalent (`singleDamping_admission_tfae`), and `dampedBlockEnergy q` is unconditionally
   controlled above `Θ − ½` (`admits_dampedBlockEnergy_of_zetaZeroAbscissa_sub_half_lt`) and on the
   Vinogradov–Korobov band (`exists_dampedBlockEnergy_le_on_vinogradovKorobovBand`,
   `eventually_dampedBlockEnergy_le_vk_saving`).
5. **Which terms obstruct (Resolved: `ObstructingTermsAndRegimeClassification`).**
   Twice the negative signed work `−2W_T(ε)` admits five exact decompositions:
   `−2 workDeviation ε T − 2 workCore ε T` (`neg_two_mul_signedDampingWork_eq_deviation_sub_core`),
   `dilationJumpEnergy ε T A_ε − dilationEdgeMass ε T A_ε − 2 polarDilationCorrection ε T`
   (`neg_two_mul_signedDampingWork_eq_dilationJump_sub_edgeMass`),
   `arithmeticDampingTotalJumpEnergy (arithmeticDampingCenteredMean ε) T + 2 dampedReadout ε Σ_n (n/(n+1)) arithmeticDampingCenteredMean ε n − arithmeticDampingBoundaryFlux (arithmeticDampingCenteredMean ε) T`
   (`neg_two_mul_signedDampingWork_eq_markov`),
   `−2(Σ_{j≤T} Λ(j)j^{−ε}⟪F_j A_ε, A_ε⟫_T + polarDilationCorrection ε T)`
   (`neg_two_mul_signedDampingWork_eq_windowMean`), and the Möbius-factored tangent pairing
   (`signedDampingWork_eq_moebiusDilation_pairing`). At the zero anchor `(0, ε]`, admission at `ε`
   forces the integrated deviation to diverge to `−∞` across `(η, T)` to cancel the prime-harmonic
   core (`exists_horizon_damping_integral_workDeviation_le`). On a compact positive interval
   `[a, c]` (`0 < a ≤ c`), `0 ≤ ∫_a^c workCore ≤ log ζ(1+a) − log ζ(1+c)` uniformly in `T`
   (`integral_workCore_bounds_on_positive_interval`), `|∫_a^c 2 workDeviation|` is uniformly bounded
   when both endpoints are admitted (`exists_abs_integral_workDeviation_le_of_admits`), admission at
   `a` is five-way equivalent to a horizon-uniform bound on the negative deviation, dilation
   jump-minus-edge-mass, Markov jump-plus-forcing-minus-flux, or negative window-mean integral
   (`obstructingTerms_positive_interval_tfae`), and all four hold unconditionally on `(Θ − ½, ∞)`
   and on the Vinogradov–Korobov band
   (`exists_obstructing_integrals_le_of_zetaZeroAbscissa_sub_half_lt`,
   `exists_obstructing_integrals_le_on_vinogradovKorobovBand`).
6. **Propagating the complementary-sector cancellation (Resolved: `ComplementarySectorPropagationAndAffineContraction`).**
   For the Ramanujan denominator sector `R_Q(n)` and its literal complement `D_Q(n) = A_ε(n) − R_Q(n)`,
   any scale transition `Q₁ → Q₂` satisfies `R_{Q₂} = R_{Q₁} + S_{Q₁,Q₂}` and
   `D_{Q₂} = D_{Q₁} − S_{Q₁,Q₂}` (`ramanujanPrefix_stage_step`, `complementarySector_step_eq`), with
   exact pronic polarisation `‖A_ε‖_R² = ‖R_Q‖_R² + 2⟪R_Q, D_Q⟫_R + ‖D_Q‖_R²` and truncation bound
   `‖D_Q‖_R² ≤ Q^{−2β} C_{ε,β}² R` (`pronicNorm_complementarySector_sq_le`). Along the compatible
   dyadic schedule `(Q_j, R_j) = (2^j, 2^{m(j+1)})`, the reweighted shell residual
   `F_j = θ^j ‖R_{Q_j}‖_{R_j}² + E^{shell}_j` (`0 < θ < 1`) satisfies the contracting recurrence
   `F_{j+1} ≤ θ F_j + r_j` (`reweightedShellResidual_step_le`) and stage-free bound
   `F_j ≤ max(F_0, R/(1−θ))` (`exists_reweightedShellResidual_contracting_bound_of_admits`).
   Admission `Admits dampedMobiusEnergy ε`, `ε ∈ receiverDampings`, bounded dyadic Ramanujan prefix
   energy, and the contracting affine recurrence for `F_j` are four-way equivalent
   (`complementarySectorPropagation_tfae`), and hold unconditionally on `(Θ − ½, ∞)` and on the
   Vinogradov–Korobov band (`exists_dyadicRamanujanPrefixEnergy_le_of_zetaZeroAbscissa_sub_half_lt`,
   `exists_dyadicRamanujanPrefixEnergy_le_on_vinogradovKorobovBand`).
7. **The compensated width floor (Resolved: `CompensatedWidthFloorAndGroundEnergyRate`).**
   For every smooth interior source `u` at aperture `a`, both `E_+(u) = ¼ Σ_q ‖û(−z_q) + û(−z̄_q)‖²`
   (`pairedPlusEnergy`) and `E_−(u) = ¼ Σ_q ‖û(−z_q) − û(−z̄_q)‖²` (`pairedMinusEnergy`) converge
   unconditionally (`summable_pairedPlusTerm`, `summable_pairedMinusTerm`), with
   `Q_a(u) = E_+(u) − E_−(u)` (`sourceQuadratic_eq_pairedPlusEnergy_sub_pairedMinusEnergy`). At a
   single aperture `a`, `∀ u, E_−(u) ≤ E_+(u) + B ‖u‖₂²` (`CompensatedSamplingBound a B`) is
   equivalent to `−B ≤ μ(a)` (`compensatedSamplingBound_iff_groundEnergy_ge`), whereas the
   uncompensated bound `∀ u, E_−(u) ≤ B ‖u‖₂²` is equivalent to `UnsignedDepthSamplingBound a (4B)`
   (`forall_pairedMinusEnergy_le_iff_unsignedDepthSamplingBound`) and to `∃ W, OffLineDepthLocallyBounded W`
   (`exists_uncompensated_pairedMinusEnergy_bound_iff`). Across apertures, `CompensatedWidthFloor σ`
   (`E_−(u) ≤ E_+(u) + C e^{2σa} ‖u‖₂²`) is equivalent to `μ(A) ≥ −C e^{2σA}`
   (`compensatedWidthFloor_iff_groundEnergy_ge_neg_exp`), implies `zetaZeroWidth ≤ σ`,
   `polarGroundEnergyRate ≤ σ`, the lag floor `−C' e^{σv}`, and damping continuation on `(σ, ∞)`
   (`zetaZeroWidth_le_of_compensatedWidthFloor`, `lag_primeWindow_ge_neg_exp_of_compensatedWidthFloor`,
   `averagedDampingContinuation_of_compensatedWidthFloor`), and holding for all `σ > zetaZeroWidth`
   closes `polarGroundEnergyRate = groundEnergyRate = zetaZeroWidth`
   (`polarGroundEnergyRate_eq_zetaZeroWidth_of_forall_compensatedWidthFloor`,
   `forall_compensatedWidthFloor_or_depthMass_clusters`).
8. **The aperture sequence with a vanishing floor (Resolved: `VanishingApertureFloorAndGradedTransport`).**
   Along any unbounded sequence `A_j → ∞` starting at `(A 0).1 ≤ 3/10`, fixed-margin additive step
   transport (`not_additive_step_transport`) and half-summable relative step transport
   (`not_relative_step_transport`) are ruled out by the Gaussian ceiling. Replacing them with
   `c_j < 1` (`0 < 1 − c_j`) in `(1 − c_j) μ(A_j) ≤ μ(A_{j+1})` gives strict finite-stage
   non-contact `0 < (∏_{i<J}(1 − c_i))/5000 ≤ μ(A_J)`, window positivity below `A_J`, compatibility
   with the doubly exponential ceiling, and RH (`strict_vanishing_relative_step`). Along a monotone
   unbounded sequence `A_j → ∞`, RH is four-way equivalent to `∃ q ≥ 0` with `q_j μ(A_j) ≤ μ(A_{j+1})`,
   to `∀ J, ∑_{j<J} Δ_spec(A_j, A_{j+1}) ≤ μ(A_0)`, and to `HasSum Δ_spec (μ(A_0))`
   (`vanishing_aperture_transport_tfae`), and monotonicity of the ceiling-renormalized functional
   `ceilingScaledGroundEnergy A = e^{β_ceil(A)} μ(A)` (bounded above by `K` on `A ≥ 3`,
   `exists_ceilingScaledGroundEnergy_le`) propagates the doubly exponential positive floor
   (`riemannHypothesis_of_ceilingScaledGroundEnergy_mono`). For a graded negative floor at rate
   `σ ≥ 0`, the discrete step bound `e^{−2σA_{j+1}} μ(A_{j+1}) ≥ e^{−2σA_j} μ(A_j) − e^{−2σA_{j+1}} δ_j`
   along `A_j → ∞` with `A_{j+1} − A_j ≤ Δ` upgrades to `CompensatedWidthFloor σ`, giving
   `zetaZeroWidth ≤ σ`, `polarGroundEnergyRate ≤ σ`, and `AveragedDampingContinuation` on `(σ, ∞)`
   (`compensatedWidthFloor_of_discrete_aperture_sequence`, `zetaZeroWidth_le_of_graded_aperture_step`,
   `averagedDampingContinuation_of_graded_aperture_step`).
9. **A stability theorem for a signed observation.** Find an observation map that is both
   origin-sensitive and sign-reading, and prove a quantitative stability estimate for it in the
   receiver's norm — the missing half of the recovery theorems.

### Research topics

- Source-derived continuation below the existing admission frontier. The sharper threshold is
  `Δ = Θ − ½`: on `[a, ½]`, `a > Δ` supplies continuation and continuation forces `a ≥ Δ`; at the
  boundary `a = Δ` admission requires every attained extremal zero to cast a critical-line zero of at
  least its multiplicity (§3), and the target is every positive `a`.
- The contraction factor of a sector-compensation scheme for the actual Möbius row, with every
  transition cross term paid, as the input to iterated compensation.
- Selectivity certificates for any proposed continuation estimate against the shifted pair
  `ζ(s−a)ζ(s+a)`, a Beurling system with an off-line zero, and the Liouville-twisted weight. The
  majorant source is the unconditional certificate against size-blind estimates; what is missing is
  one against sign-reading but non-arithmetic estimates.
- The aperture continuation of the window certificates of `ArithmeticIncidencePositivity` past a
  prime, with the per-prime gain required by the affine envelope, and the aperture analogue of the
  averaged budget.
- The aperture analogue of the exact derivative. In damping the derivative is an exact identity,
  boundary flux minus jump energy minus density forcing. No aperture-derivative identity for the
  ground energy `μ(A)` with that structure is known, and no monotone or Lyapunov quantity in `A`.
  Find one with a sign-definite jump term. The ceiling fixes its shape: any such functional must
  decay like `exp(−πe^{2(A−2)})`.
- The arithmetic content the function-field model lacks: the number-field source has no exact
  vanishing of degree-wise Möbius sums beyond degree one, and the whole obligation is that defect.
  Quantify it — a bound on the deviation of the centred prefix from a constant at a fixed damping is
  the model-faithful form of the covariance demand.

---

## 8. Principles

1. **Exact source before closure.** Every coefficient, prime power, Gamma term and pole term is
   fixed before an estimate is claimed. A source selected from the zeros is not an arithmetic
   construction.
2. **Keep signs until their cancellation is paid.** Absolute values are allowed where their loss is
   proved acceptable. The default object is the complete signed pairing.
3. **Uniformity is part of the theorem.** `∀ε ∃C_ε ∀T` is stated when that is what is meant. A
   horizon-dependent band or a complete-period limit is a different result.
4. **State the demand at the bottom of its hierarchy.** Between a pointwise budget, an averaged
   budget and the conclusion, use the weakest form that still transports: the averaged one is
   equivalent to admission, the pointwise one is stronger for general energy families and is not known to follow from RH for this source.
5. **Distinguish recovery from control.** An injective observation, even a complete invariant,
   requires a stability estimate before it bounds an energy.
6. **Preserve the required norm.** An `H¹` estimate does not pay an `L²`-normalised floor; pointwise
   convergence does not replace convergence in the receiver's energy; compactness on `c₀` is not a
   bound on a pronic energy.
7. **Test selectivity against the known adversaries.** Shifted zeta pairs, altered prime weights,
   parity partners, coherent blocks and the majorant row must fail a named hypothesis.
8. **Pay both ends of a limit.** Origin, infinity, fractional-part terms and polar constraints
   belong to the same accounting; a missing boundary term can contain the whole obstruction.
9. **Separate endpoint success from bridge success.** A larger certified interval or the equality of
   two unknown rates is useful; it is not a smaller zero width.
10. **Require a positive survivor from failure.** If a continuation fails, extract the sharp growth
    law, the obstruction measure, the classification or the weaker valid estimate.
