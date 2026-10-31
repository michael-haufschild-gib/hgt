# ShallowCauchyPrimeEnergy (SCPE)

Namespace `RHTower` (files under `ShallowCauchyPrimeEnergy/`); umbrella `ShallowCauchyPrimeEnergy.lean`; 4 modules. Every theorem is unconditional. No RH hypothesis, no `#print axioms` lines.

## 1. Motivation

An off-line zero `ρ = ½ + a + iγ` is a damped mode `e^{−(a+iγ)t}`. A packet of such modes has the Cauchy–Gram energy `E = 4 Σ m_j m_k (a_j + a_k)/((a_j + a_k)² + (γ_j − γ_k)²)`, the `L²(0,∞)` norm of the profile `Σ 2m_j e^{−(a_j+iγ_j)t}`. Ward-type and energy routes to RH need an upper bound for `E` over the shallow off-line zeros, those within `h ≈ 1/log T` of the line. The deterministic Riemann–von Mangoldt local count gives `E ≤ T log³T` at `h = 1/log T`. SCPE removes the extra `log T` and proves `E ≤ C T log²T` unconditionally, which is the size of the diagonal. That is the best possible prime-side bound, and it is a density statement, not a vanishing statement.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Transverse Cauchy kernel | `transverseCauchyKernel a b Δ` | `(a+b)/((a+b)² + Δ²)` = Re of the resolvent `1/((a+b) + iΔ)` |
| Off-line Cauchy energy | `finiteOfflineCauchyEnergy a γ m` | `4 Σ m_j m_k K(a_j, a_k, γ_j − γ_k)` |
| Narrow Lorentzian sum | `windowNarrowSum Z γ r t` | `G_r(t) = Σ_{q∈Z} r²/(r² + (t − γ_q)²)` |
| Dyadic zero window | `dyadicZeroWindow T` | all ξ-zero copies (with multiplicity) with ordinate in `[T, 2T]` |
| Right windows | `xiRightUpperWindow`, `xiShallowRightUpperWindow h T`, `xiDeepRightUpperWindow h T` | right copies in `[T, 2T]`; depth `≤ h`; depth `> h` |
| Shallow Cauchy energy | `xiShallowCauchyEnergy h T` | energy of all shallow right copies with damping `h + β` |
| Multiscale bad set | `MultiScaleBad S u t` | some scale `v ∈ [u, 1/16]` has `> 20 v log S` zeros within `v` of `t` |
| Superlevel sets | `narrowSuperlevel`, `narrowSuperlevelMajorant` | dyadic level sets of `G_{R₀/2}` on `[S, 2S]` |

External: `XiZeroCopy`, `XiRightUpperZeroCopy`, `xiRightCenteredZero`, `xiZeroCopyLineConjEquiv`, `lorentzMass`, `zeroWindow`, `finiteOfflineCauchyEnergy`, `exists_volume_multiscale_localZeroCount_gt_le`, `exists_selberg_exponential_nearLine_zeroDensity_long` (RHTower); `halfPlanePoisson` (HTGeometry); `Zeta23.Ncount`.

## 3. Language

- Depth `β = Re ρ − ½`; shallow at depth `h`: `0 < β ≤ h`; critical spacing `h = 1/log T`.
- Shift `h`: each shallow mode is damped by `h + β ∈ (h, 2h]`.
- Lorentzian pair sum at width `R₀`: `Σ_{q₁,q₂} R₀²/(R₀² + (γ₁ − γ₂)²)`, the smoothed pair correlation.
- Line-reflection saving: `ρ` and `1 − ρ̄` have the same ordinate and both lie in `dyadicZeroWindow T`.
- Diagonal: the `j = k` terms of `E`, equal to `Σ m_j²/(h + β_j)`.
- Deep tail: right copies at depth `> α/log T`.

## 4. Mechanisms

1. Kernel domination: for `0 ≤ a, b ≤ h` and `R₀ ≥ 2h`, `4h K(h+a, h+b, Δ) ≤ 4R₀²/(R₀² + Δ²)`. The shifted Cauchy kernel is a Lorentzian of width `≍ h`.
2. Poisson semigroup: `P_r ⋆ P_r = P_{2r}` turns a Lorentzian pair sum into an `L²` norm, `Σ R₀²/(R₀² + Δγ²) = (4/(πR₀)) ∫ G_{R₀/2}²`.
3. Pointwise control of `G`: far zeros (`|γ − t| > 1/16`) contribute `≤ 257 r² × Lorentz mass`. Near zeros at a good point are split into dyadic shells, each holding `≤ 20·2^{j+1}u log S` zeros with terms `≤ 4^{−(j+1)}`. This gives `G ≤ 105 u log S` off the bad set and `G ≤ 16 log S` everywhere.
4. Superlevel integration: `{G > 105·2^j R₀ log S} ⊂ MultiScaleBad(2^j R₀)`. The bad set has volume `≤ 12CS e^{−v log S/120000} + CS^{3/4}` (prime-cascade multiscale zero-count regularity). Summing `4^j e^{−2^j x} ≤ 17` gives `∫_{[S,2S]} G² ≤ C(R₀ log S)² S`.
5. Tails: outside `[T/2, 4T]` inverse-square decay gives `≤ 8πr⁴N²/T³` on each side.
6. Reflection saving: a shallow pair `(p, q)` appears four times among `{p, p̄*} × {q, q̄*}` in the global window, which cancels the prefactor `4`.
7. Diagonal lower bound: `E ≥ 2Σ m_j²/(h + a_j) ≥ Σ m_j²/h`. So `#shallow ≤ hE`, `Σ m² ≤ hE`, and close pairs at distance `≤ Kh` satisfy `Σ m_j m_k ≤ ((16 + K²)/8) hE`.
8. Deep tail: Selberg's two-length Barban–Vehov near-line density gives an `e^{−α/28}/α` fraction past depth `α/log T`. Two unit strips at the window ends are bounded by Lorentz mass.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Lorentzian pair sum = `(4/(πR₀)) ∫ G_{R₀/2}²` | `lorentz_pairSum_eq_integral_windowNarrowSum_sq` | proved |
| `∫_{[S,2S]} G_{R₀/2}² ≤ C₁(R₀ log S)² S` for `κ₂ ≤ R₀ log S`, `R₀ ≤ 1/16` | `exists_integral_Icc_windowNarrowSum_sq_le` | proved |
| Pair correlation on `[T, 2T]` at width `R₀ ≥ κ₂/log T` is `≤ C(R₀ log T) T log T` | `exists_dyadicZeroWindow_lorentzPairSum_le` | proved |
| `h E_h ≤ Σ` Lorentzian pair sum at width `R₀ ≥ 2h` | `shift_mul_xiShallowCauchyEnergy_le_dyadic_lorentzPairSum` | proved |
| `h E_h ≤ C max(κ₂, 2h log T) T log T` for `0 < h ≤ 1/64` | `exists_uniform_xiShallowCauchyEnergy_le` | proved |
| At `h = 1/log T`: `E ≤ C T log²T`; `#shallow · log T ≤ E` | `exists_xiShallowCauchyEnergy_one_div_log_le` | proved |
| Same for injective packets and for ζ zeros with multiplicity | `exists_finiteOfflineCauchyEnergy_xiRightUpper_one_div_log_le`, `exists_finiteOfflineCauchyEnergy_zetaZeros_one_div_log_le` | proved |
| `(1/log T) E ≤ C_N N(T, 2T)` | `exists_xiShallowCauchyEnergy_one_div_log_le_mul_Ncount` | proved |
| Saturation: `E_{α/log T} ≤ 2C T log²T` for `κ₂/2 ≤ α ≤ log T/64` | `exists_criticalScale_xiShallowCauchyEnergy_saturation` | proved |
| Shallow ζ zeros: `Σ m² ≤ C T log T`; close pairs at `K/log T` `≤ (C/8)(16+K²) T log T` | `exists_shallow_zetaZeros_sq_multiplicity_and_closePairs_le` | proved |
| Deep tail `≤ C(T log T e^{−α/28}/α + log²T)` | `exists_card_xiDeepRightUpperWindow_exponential_le` | proved |
| Joint budget: split, diagonal, shallow energy `O_α(N)`, deep tail | `exists_shallowCauchyEnergy_and_exponential_deepWindow_le` | proved |
| `∀ε ∃α`: deep `≤ εN`, `(α/log T)E + deep ≤ BN`, `E ≤ BT log²T` | `exists_arbitrary_deepFraction_with_linear_shallowEnergy_budget` | proved |

## 6. Tools

**Developed**
- Lorentzian/Poisson `L²` calculus for zero ordinates (`narrowKernel_mul_eq_poisson`, `integral_narrowKernel_mul`).
- Dyadic superlevel majorant of a zero-counting profile, integrated against a bad-set volume bound.
- Reflection embedding `xiRightUpperLineReflectedEmbedding` and multiplicity fibres `xiRightUpperFiber`, with sizes equal to analytic orders.
- Diagonal and close-pair extraction from a Cauchy–Gram energy (`sum_sq_multiplicity_le_shift_mul_finiteOfflineCauchyEnergy`, `sum_closePairs_le_shift_mul_finiteOfflineCauchyEnergy`).
- Unit-strip zero count `card_xiZeroCopy_unitStrip_le`.

**To build**
- An off-diagonal saving: a bound on `E_h − diagonal`, which the pair-correlation route cannot give.
- A sub-diagonal bound on the shallow census (`#shallow = o(N(T, 2T))`), which needs input that sees depth, not ordinates.
- A depth-weighted energy whose diagonal vanishes on the line.

## 7. Open questions

1. Can any prime-side input bound `E_{1/log T}` below its diagonal, or show that the diagonal itself is `o(T log²T)`?
2. Is the Lorentzian pair correlation at width `≍ 1/log T` below `κ₂` controllable, or does it require Montgomery-type pair correlation?
3. Does the joint budget combine with an index price (energy per negative square) to bound the number of off-line zeros?
4. Can the `κ₂ ≥ 120000` threshold be lowered to `O(1)`?

## 8. Traps

| Trap | Fact |
|---|---|
| `E ≤ C T log²T` excludes shallow off-line zeros | The diagonal alone is `#shallow · log T`; the bound only gives `#shallow ≤ C T log T = O(N)` |
| The bound is a zero-density estimate near the line | It is a pair-correlation (Lorentzian) bound; it says nothing about how many zeros are off the line |
| The factor `4` in `E` costs a constant | Reflection pairs absorb it exactly |
| Multiscale regularity holds at every point | It holds off a bad set of volume `e^{−v log S/120000}S + S^{3/4}`; the `L²` integral pays for that set |
| Saturation grows with `α` | `E_{α/log T}` is `α`-independent; only `hE_h` grows like `α` |
| Deep tail estimates also cover shallow zeros | Selberg density gives `e^{−α/28}/α` only beyond depth `α/log T`; shallow zeros need the energy route |

## 9. Context

**Uses**

| Programme | Imports | What |
|---|---|---|
| RHTower | 9 | finite off-line Cauchy energy, multiscale local zero counts, Ward source windows, reflection charge, Selberg near-line density, RvM counts |
| HTGeometry | 1 | half-plane Poisson kernel and its convolution identity |

**Used by**: `MainTheorems.lean` only.

| Neighbour | Relation |
|---|---|
| RHTower Ward source windows | define the energy (`FiniteOfflineCauchyEnergy`, its `L²` form in `FiniteOfflineCauchyL2`) and the diagonal lower bound `xiRight_shallowLayer_card_le_shift_mul_finiteOfflineCauchyEnergy`; SCPE supplies the matching upper bound |
| HeckeKreinToeplitz | prices negative squares by critical energy (`IndexIsEnergy`); SCPE is the unconditional size of a shallow energy |
| TransThresholdPairCorrelation | pair correlation beyond bandwidth one; SCPE uses only Lorentzian (smoothed) pair correlation at width `≳ 1/log T` |

## 10. Big picture

SCPE shows what unconditional zero statistics can do for an energy-based proof. Lorentzian pair correlation, multiscale zero counts and Selberg's near-line density together bound the shallow off-line energy by its own diagonal. The `log T` loss disappears and the deep zeros become an arbitrarily small fraction. The result is sharp: unconditional prime-side inputs reach the diagonal and stop there.

For the RH programme this marks a boundary. Energy or Ward arguments that need the shallow Cauchy energy to be small compared with its diagonal cannot be fed by pair-correlation or density estimates, because those inputs see ordinates, not depths. A zero at depth `1/log T` and a zero on the line look alike to every tool used here. Closing the gap needs an input that is sensitive to depth itself: an index, a positivity, or a structural identity.
