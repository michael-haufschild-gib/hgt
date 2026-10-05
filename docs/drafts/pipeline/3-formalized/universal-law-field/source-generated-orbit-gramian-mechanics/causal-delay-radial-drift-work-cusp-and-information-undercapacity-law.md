# Causal-delay radial-drift work cusp and information-undercapacity law

- **ID:** ULF-SGOGM-4
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source programme:**
  `../../../1-in-progress/universal-law-field/source-generated-orbit-gramian-mechanics/field-programme.md`
- **Hardy admission parent:**
  `spectral-hardy-trace-formation-admission-and-radial-capital-wall-law.md`
- **Functional-equation recovery parent:**
  `split-recovery-formation-capital-monotonicity-functional-equation-neutrality-law.md`
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE]`
  `[EXACT DELAY/DRIFT/WORK LAW] [FORMATION CUSP] [INFORMATION UNDERCAPACITY]`
  `[LEAN-PROVED] [NOT RH]`

## 1. Purpose

The unsmoothed radial multiplier `exp(delta z)-1` has infinite Euler-shell formation capital for
every nonzero drift `delta`. That wall does not say off-neutral formation is impossible. A source
may delay and average the defect.

This card classifies that escape exactly. For a width-`T` average and delay `b`, the drift is
formable precisely when both ends of its translated control remain in causal time. Its least work
is independent of the delay once admitted and has a nonsmooth cusp at zero drift:

\[
 \boxed{
 \text{work}(\delta,T)
 ={2\min(|\delta|,T)\over T^2}.}
 \tag{CDW.1}
\]

Functional-equation pairing sends `delta` to `-delta`. A common causal realization requires delay
at least `|delta|`; its paired work is twice `(CDW.1)`. For the same Euler-shell Gibbs source, that
work is linear in `|delta|` near the neutral point, whereas reflected Jeffreys information is
quadratic. Information is therefore too soft to generate causal formation properness.

## 2. Delayed smoothed radial packet

Use an Euler-shell source pair `(L,v)` from `ULF-SGOGM-3`, so the reachability map `W` is injective
and least capital equals the squared `L^2(0,infinity)` norm of the unique source history.

Let

\[
 \delta,b\in\mathbb R,
 \qquad T>0.
 \tag{CDW.2}
\]

Define the multiplier

\[
 \Phi_{\delta,b,T}(z)
 =e^{-bz}(e^{\delta z}-1){1-e^{-Tz}\over Tz}
 ={e^{-(b-\delta)z}-e^{-bz}\over Tz}(1-e^{-Tz}).
 \tag{CDW.3}
\]

The removable value at `z=0` is understood. Whenever the multiplier packet belongs to the ambient
Euler-shell Hilbert space, put

\[
 x_{\delta,b,T}=\Phi_{\delta,b,T}(L)v.
 \tag{CDW.4}
\]

## 3. Main theorem

### Theorem 3.1 — causal delay classification

If `delta=0`, then `x_(delta,b,T)=0` and its capital is zero for every `b`. Assume `delta!=0`.
Then the following are equivalent:

1. `x_(delta,b,T)` has finite source-orbit formation capital;
2. `Phi_(delta,b,T)` belongs to `H^2(C_+)`;
3. both translated interval starts are causal:

\[
 b\ge0,
 \qquad b-\delta\ge0;
 \tag{CDW.5}
\]

4. equivalently,

\[
 \boxed{b\ge\max(0,\delta).}
 \tag{CDW.6}
\]

In the admitted chamber the unique source history is

\[
 h_{\delta,b,T}(t)
 ={1\over T}\left(
 \mathbf1_{[b-\delta,b-\delta+T]}(t)
 -\mathbf1_{[b,b+T]}(t)
ight),
 \tag{CDW.7}
\]

and its exact least capital is

\[
 \boxed{
 q_G(x_{\delta,b,T})
 =\|h_{\delta,b,T}\|_2^2
 ={2\min(|\delta|,T)\over T^2}.}
 \tag{CDW.8}
\]

Thus delay decides admission, but not work after admission.

### Proof

When `(CDW.5)` holds, both indicators in `(CDW.7)` lie in `L^2(0,infinity)`, and direct Laplace
transformation gives

\[
 \mathcal L h_{\delta,b,T}=\Phi_{\delta,b,T}.
 \tag{CDW.9}
\]

The Hardy-trace formation theorem gives admission. The Euler-shell reachability map is injective,
so this history is unique and its squared norm is the least capital.

The intervals in `(CDW.7)` have length `T`; their displacement is `|delta|`; their overlap length
is `(T-|delta|)_+=max(T-|delta|,0)`. Therefore

\[
 \|h_{\delta,b,T}\|_2^2
 ={2T-2(T-|\delta|)_+\over T^2}
 ={2\min(|\delta|,T)\over T^2},
 \tag{CDW.10}
\]

proving `(CDW.8)`.

Conversely, suppose one start in `(CDW.5)` is negative. Since `delta!=0`, the two exponential
rates in `(CDW.3)` are distinct. Along the positive real ray, the term with negative start grows
exponentially and cannot cancel the other term. Hence

\[
 |\Phi_{\delta,b,T}(x)|\sqrt{x}\longrightarrow\infty
 \tag{CDW.11}
\]

along the Euler-shell spectral sequence `x=log n`. But every `H^2` function satisfies

\[
 |H(x)|\le {\|H\|_{H^2}\over\sqrt{2x}},
 \tag{CDW.12}
\]

contradicting `(CDW.11)`. The Hardy-trace theorem rules out finite capital. QED.

## 4. Functional-equation common-delay law

Reflection sends `delta` to `-delta`. A single delay `b` admits both orientations exactly when

\[
 b\ge\max(0,\delta)
 \quad\text{and}\quad
 b\ge\max(0,-\delta),
 \tag{CDW.13}
\]

that is,

\[
 \boxed{b\ge|\delta|.}
 \tag{CDW.14}
\]

At every common admitted delay, both orientations have the same work. On the direct-sum doubled
packet their exact total capital is

\[
 \boxed{
 \mathfrak C_{\rm pair}(\delta,T)
 ={4\min(|\delta|,T)\over T^2}.}
 \tag{CDW.15}
\]

The functional equation therefore does not select `delta=0`; it symmetrizes the causal financing
law and forces a common delay budget.

Common extra delay is a gauge inside the admitted chamber. For `c>=0`, let `S_c` denote the
right-shift isometry on `L^2(0,infinity)`, extended by zero before `c`. Then

\[
 h_{\delta,b+c,T}=S_ch_{\delta,b,T},
 \qquad
 \Phi_{\delta,b+c,T}(z)=e^{-cz}\Phi_{\delta,b,T}(z),
 \tag{CDW.15a}
\]

and

\[
 \boxed{
 \|h_{\delta,b+c,T}\|_2^2
 =\|h_{\delta,b,T}\|_2^2.}
 \tag{CDW.15b}
\]

Hence absolute delay after admission carries no work information. The invariant is the entrance
threshold `max(0,delta)` on one orientation and `|delta|` on the reflected pair.

## 5. Work cusp versus smooth information

Retain the same Euler-shell source. For real `u` near zero, define its Gibbs tilt

\[
 dP_u(n)={n^{-\sigma+u}\over S_m(\sigma-u)},
 \qquad n\in A_m,
 \tag{CDW.16}
\]

and put

\[
 F(u)=\log S_m(\sigma-u).
 \tag{CDW.17}
\]

Then

\[
 F'(u)=\mathbb E_{P_u}(\log n),
 \qquad
 F''(u)=\operatorname{Var}_{P_u}(\log n)>0.
 \tag{CDW.18}
\]

The reflected likelihood ratio is

\[
 \log{dP_u\over dP_{-u}}(n)
 =2u\log n+F(-u)-F(u),
 \tag{CDW.19}
\]

so its Jeffreys information is

\[
 J_m(u)
 =D(P_u\Vert P_{-u})+D(P_{-u}\Vert P_u)
 =2u\big(F'(u)-F'(-u)\big).
 \tag{CDW.20}
\]

Fix `u_0>0` with `sigma-u_0>1` and put

\[
 M_{u_0}=\sup_{|s|\le u_0}F''(s)<\infty.
 \tag{CDW.21}
\]

The mean-value theorem gives

\[
 0<J_m(u)\le4M_{u_0}u^2
 \qquad(0<|u|\le u_0).
 \tag{CDW.22}
\]

Using the same parameter `delta=u`, if `0<|u|<=T`, then

\[
 \mathfrak C_{\rm pair}(u,T)={4|u|\over T^2}.
 \tag{CDW.23}
\]

Consequently

\[
 \boxed{
 {\mathfrak C_{\rm pair}(u,T)\over J_m(u)}
 \ge {1\over M_{u_0}T^2|u|}
 \longrightarrow\infty
 \qquad(u\to0,\ u\ne0).}
 \tag{CDW.24}
\]

The two grades of the same source have different local geometry:

\[
 J_m(u)=O(u^2),
 \qquad
 \mathfrak C_{\rm pair}(u,T)=\Theta(|u|).
 \tag{CDW.25}
\]

No locally bounded multiple of smooth reflected information can dominate causal formation work near
the neutral point. KL/Jeffreys information remains valuable for distinguishability, but it cannot
serve as the missing properness capital.

## 6. Source-anchor selection theorem

Let `b_src(delta)` be a source-derived causal delay for the drift packet, defined before any zero
or target specialization. If the source law supplies

\[
 b_{\rm src}(\delta)=0
 \tag{CDW.26}
\]

and requires finite formation capital, then Theorem 3.1 forces

\[
 \delta\le0.
 \tag{CDW.27}
\]

If the same zero-delay law is functional-equation invariant, it also applies to `-delta`, hence

\[
 -\delta\le0.
 \tag{CDW.28}
\]

Therefore

\[
 \boxed{\delta=0.}
 \tag{CDW.29}
\]

This is an exact conditional selection theorem: **causal anchoring + finite capital + reflection
forces the neutral locus.** The condition is not yet an independent HGT source law. In the actual
Hedenmalm source formalization, source involution fixedness is already proved equivalent to
critical-line placement. Substituting that fixedness for `(CDW.26)` would therefore be circular.
The live problem is to derive a zero-slack causal formation from a parameter-free operation before
divisor specialization, not to rename source fixedness as an anchor.

## 7. Countermodels and load-bearing hypotheses

### 7.1 Delay destroys selection

For every nonzero `delta`, choosing

\[
 b\ge\max(0,\delta)
 \tag{CDW.30}
\]

produces finite capital. With both functional-equation orientations, `b>=|delta|` suffices.
Therefore finite capital plus reflection alone never selects zero.

### 7.2 Width is load-bearing

At `T=0`, the histories become signed point impulses and leave `L^2`; exact-time packets have
infinite capital. The finite law is a temporal averaging theorem.

### 7.3 Positivity is not used in the signed history

The control in `(CDW.7)` is a signed difference of positive windows. The resulting positive defect
`|x><x|` has nonnegative energy, but formation itself retains orientation. Erasing sign before
formation loses the cancellation that defines radial drift.

### 7.4 Source clock is constitutive

Changing the origin of source time changes the admissible delay chamber. The theorem does not call
zero delay canonical; it identifies that canonicity as the exact missing source datum.

### 7.5 Source origin does not imply radial zero slack

A source theory may have a canonical origin while a particular defect begins after a positive
latency. The corpus's Hedenmalm source-origin theorem and its fixed-flow classifier exhibit exactly
this distinction. Origin marks the causal boundary; it does not prove that the RH-bearing drift
history touches it.

## 8. Parent boundary and hostile verdict

The shifted-box Laplace transform and its `L^2` norm are elementary signal/control theory. Hardy
admission and diagonal-semigroup interpolation are established parents. This card is a `[BRIDGE]`.

Its corpus leverage is the joint law:

1. radial drift becomes a signed difference of source-time windows;
2. causality gives a sharp delay threshold;
3. least work has an exact nonsmooth cusp;
4. functional equation forces a common delay, not zero drift;
5. smooth information geometry provably underprices formation near the center;
6. a global zero-slack source formation would select the neutral locus, but source fixedness is an
   RH-equivalent substitute and is forbidden.

- [x] causal admission iff proved;
- [x] exact least-work formula proved;
- [x] functional-equation common-delay threshold proved;
- [x] information-undercapacity asymptotic proved;
- [x] zero-delay reflection selection theorem proved;
- [x] delay countermodel supplied;
- [x] Lean formalization;
- [ ] parameter-free source proof of zero-slack radial formation;
- [ ] RH consequence.

Lean: every numbered claim (CDW.1)–(CDW.30) and §7 is formalized; see the Lean certificate below.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.CausalDelayDriftWork`, `GaloisForLFunctions.HTGeometry.EulerShellTiltInformation`, `GaloisForLFunctions.HTGeometry.SpectralHardyTraceFormation`, `GaloisForLFunctions.HTGeometry.EulerShellHardyTraceFormation`, `GaloisForLFunctions.HTGeometry.CyclicHeatOrbitCost`, `GaloisForLFunctions.HTGeometry.EulerShellHeatOrbit`, `GaloisForLFunctions.HTGeometry.BurnolHalfLineWeightedShift`, `GaloisForLFunctions.HTGeometry.PaleyWienerHalfPlane`, `GaloisForLFunctions.HTGeometry.HardyLineIsometry`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

New modules: `GaloisForLFunctions.HTGeometry.CausalDelayDriftWork` and `GaloisForLFunctions.HTGeometry.EulerShellTiltInformation`.
They build on the Hardy-trace layer of the parent card (`GaloisForLFunctions.HTGeometry.SpectralHardyTraceFormation`,
`GaloisForLFunctions.HTGeometry.EulerShellHardyTraceFormation`), the orbit-Gramian modules (`GaloisForLFunctions.HTGeometry.CyclicHeatOrbitCost`,
`GaloisForLFunctions.HTGeometry.EulerShellHeatOrbit`), the corpus half-line right shift of `GaloisForLFunctions.HTGeometry.BurnolHalfLineWeightedShift`
(`burnolRightShift`, an isometry of `L²(0,∞)`), and the Paley–Wiener layer (`GaloisForLFunctions.HTGeometry.PaleyWienerHalfPlane`,
`GaloisForLFunctions.HTGeometry.HardyLineIsometry`). Both modules are clean under `lake env lean`, build as modules, and the axiom audit shows
only `[propext, Classical.choice, Quot.sound]`.
The packet `x_{δ,b,T}` is `spectralPacket (delayDriftMultiplier δ b T)` under its square-summability hypothesis ("whenever the packet
belongs to the ambient space"); in the causal chamber that hypothesis is proved (`summable_delayDrift`) and the packet is
`delayDriftPacket`. Theorem 3.1 is proved for every cyclic source with infinite index set; the exact work uses injectivity of `W`,
which holds on the Euler shell. The doubled-packet capital (CDW.15) is the least control energy `‖u₁‖² + ‖u₂‖²` of the direct-sum
formation `W ⊕ W`. Kullback–Leibler divergence is the discrete `Σ P log(P/Q)` on `A_m`.

| Claim | Lean declaration |
|-|-|
| (CDW.2)–(CDW.4) multiplier `Φ_{δ,b,T}` (= `m_{b-δ,T} - m_{b,T}`) and packet `x_{δ,b,T}` | `delayDriftMultiplier`, `delayDriftMultiplier_eq`, `delayDriftMultiplier_ofReal`, `delayDriftPacket`, `HeatSource.summable_delayDrift` |
| Theorem 3.1, `δ = 0`: `x = 0`, capital `0` for every `b` | `delayDriftMultiplier_zero`, `HeatSource.spectralPacket_delayDrift_zero`, `CyclicHeatSource.orbitCostForm_delayDrift_zero` |
| Theorem 3.1 (1)⟺(2)⟺(3)⟺(4), (CDW.5)–(CDW.6) | `CyclicHeatSource.orbitCostForm_delayDrift_lt_top_iff`, `eulerShell_orbitCostForm_delayDrift_lt_top_iff`, `isHalfPlaneHardy_delayDriftMultiplier_iff`, `causal_chamber_iff` |
| (CDW.7), (CDW.9) history `h_{δ,b,T}`, `ℒh = Φ`, `Wh = x`, uniqueness | `delayDriftControl`, `laplaceRay_sub`, `laplaceRay_delayDriftControl`, `isHalfPlaneHardy_delayDriftMultiplier`, `HeatSource.heatReachability_delayDriftControl`, `delayDriftPacket_unique_history` |
| (CDW.8), (CDW.10) `q_G(x_{δ,b,T}) = ‖h‖² = 2 min(∣δ∣,T)/T²` | `measureReal_Ioc_inter_Ioc`, `inner_offsetWindowControl`, `norm_delayDriftControl_sq`, `CyclicHeatSource.orbitCostForm_delayDrift_eq`, `orbitCostForm_delayDriftPacket` |
| (CDW.11)–(CDW.12) off the chamber `∣Φ(x)∣ → ∞`, while `H(x) → 0` for `H ∈ H²` | `tendsto_exp_sub_exp_div_atTop`, `tendsto_norm_delayDriftMultiplier_atTop`, `tendsto_isHalfPlaneHardy_atTop`, `not_isHalfPlaneHardy_delayDriftMultiplier`, `norm_le_hardyNormSq` |
| (CDW.13)–(CDW.14) common delay `b ≥ ∣δ∣` | `common_delay_iff`, `eulerShell_common_delay_iff` |
| (CDW.15) equal work of both orientations; paired capital `4 min(∣δ∣,T)/T²` | `pairWork`, `pairCapital_eq` |
| (CDW.15a)–(CDW.15b) right-shift gauge `h_{δ,b+c,T} = S_c h_{δ,b,T}`, `Φ_{δ,b+c,T} = e^{-cz}Φ_{δ,b,T}`, norm invariance | `delayDriftMultiplier_add_delay`, `offsetWindowControl_add_delay`, `delayDriftControl_add_delay`, `norm_delayDriftControl_add_delay`, `burnolRightShift`, `norm_burnolRightShift_apply` |
| (CDW.16)–(CDW.17) Gibbs tilt `P_u` (a probability on `A_m`), `F(u) = log S_m(σ-u)` | `shellTilt`, `shellTilt_pos`, `hasSum_shellTilt`, `shellLogPartition`, `eulerShellMoment`, `summable_eulerShellMoment`, `hasDerivAt_eulerShellMoment_sub` |
| (CDW.18) `F' = E_{P_u} log n`, `F'' = Var_{P_u} log n > 0` | `shellTiltMean`, `shellTiltVar`, `shellTiltMean_eq`, `shellTiltVar_eq`, `hasDerivAt_shellLogPartition`, `hasDerivAt_shellTiltMean`, `deriv_shellLogPartition`, `deriv_deriv_shellLogPartition`, `shellTiltVar_pos` |
| (CDW.19) `log(dP_u/dP_{-u}) = 2u log n + F(-u) - F(u)` | `log_shellTilt_div` |
| (CDW.20) `J_m(u) = D(P_u‖P_{-u}) + D(P_{-u}‖P_u) = 2u(F'(u) - F'(-u))` | `shellKL`, `shellJeffreys`, `shellKL_tilt`, `shellJeffreys_eq`, `shellJeffreys_neg` |
| (CDW.21)–(CDW.22) `M_{u₀} = sup_{∣s∣≤u₀} F'' < ∞`; `0 < J_m(u) ≤ 4M_{u₀}u²` | `shellVarSup`, `continuousOn_shellTiltVar`, `shellTiltVar_le_shellVarSup`, `shellVarSup_pos`, `shellJeffreys_pos_le_of_pos`, `shellJeffreys_pos_le` |
| (CDW.23)–(CDW.24) `𝔠_pair = 4∣u∣/T²`; `𝔠_pair/J_m ≥ 1/(M_{u₀}T²∣u∣) → ∞` | `pairWork_of_le`, `pairWork_div_shellJeffreys_ge`, `tendsto_pairWork_div_shellJeffreys` |
| (CDW.25) `J_m = O(u²)`, `𝔠_pair = Θ(∣u∣)` | `shellJeffreys_isBigO`, `pairWork_isTheta` |
| (CDW.26)–(CDW.29) zero source delay + finite capital + reflection ⟹ `δ = 0` | `source_anchor_selection` |
| (CDW.30) §7.1 delay destroys selection | `delay_destroys_selection` |
| §7.2 width is load-bearing: exact-time radial packet has infinite capital; `q_G(x_{δ,b,T}) → ∞` as `T ↓ 0` | `HeatSource.heatOrbit_sub_eq_spectralPacket`, `HeatSource.summable_expDiffPacket`, `orbitCostForm_exactTime_radial_eq_top`, `tendsto_orbitCostForm_delayDriftPacket` |
| §7.3 the history is signed (no nonnegative control); positive defect energy | `not_ae_nonneg_delayDriftControl`, `orbitDefectCost_delayDriftPacket` |
| §7.4 admissible delays `= [max(0,δ), ∞)` | `admissible_delays_eq` |
| §7.5 admitted histories may start after a positive latency | `delayDriftControl_eq_zero_of_lt` |

## Log

- 2026-10-03 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
