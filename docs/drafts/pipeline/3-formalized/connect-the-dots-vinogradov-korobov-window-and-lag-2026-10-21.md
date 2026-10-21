# Connecting the dots: the Vinogradov–Korobov prime number theorem and zero-free region feed the window spectrum and the lag envelope

- **ID:** connect-the-dots-vk-walls-2026-10-21
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), two modules
- **Source:** docs/reports/review-2110/walls-ledger.md (wall 1: "best unconditional" cells); task "connect the dots of theorems in different parts of the Lean corpus"
- **Statement:** For every `0 < ex < 3/5`: (W) there are `C ≥ 0`, `κ > 0` with `|c(L) − e^{L/2}| ≤ C e^{L/2 − κ L^ex}`, `|floor(L) + e^{L/2}| ≤ C e^{L/2 − κ L^ex}` for all large window lengths `L`, every window deviation satisfies `|x| ≤ e^{L/2} + C e^{L/2 − κ L^ex}`, some deviation is `≥ e^{L/2} − C e^{L/2 − κ L^ex}`, and the integrated Chebyshev deficit satisfies `|D(T)| ≤ C e^{T − κ T^ex}`; (E) for every width `w ∈ (0, ½ log 2)` there is a lag `V₀` with `P_v ≥ −|φ(0)| − (W + S₂) e^{v/2 − v^ex}` for all `v ≥ V₀`.

## Goal
The walls ledger states that unconditional methods stop at Vinogradov–Korobov savings, but its two
"best unconditional" cells for wall 1 (the window remainder and the lag envelope) stood at
de la Vallée Poussin strength `e^{−κ√L}`, `e^{−√v/10}`, because the modules that produce them
consumed the de la Vallée Poussin inputs. The Vinogradov–Korobov prime number theorem
(`RHTower.chebyshevError_bound_rpow`: `|ψ(t) − t| ≤ C t e^{−c (log t)^ex}` for `ex < 3/5`) and the
Vinogradov–Korobov zero-free region (`RHTower.Sieve.riemannZeta_ne_zero_vinogradovKorobov`:
`Re ρ ≤ 1 − (log γ)^{−2/3}(log log γ)^{−5/3}/10⁸` for large `γ`) live in `RHTower/Sieve` and had never
been composed with the BiScale window spectrum or the SRT lag family.

| # | dots joined | areas | wall | new statement |
|---|---|---|---|---|
| W | VK prime number theorem × polar Schur bound of the window ceiling (proved here for every nonincreasing error profile) × polar test lower side × Liouville mirror | RHTower/Sieve × BiScaleUncertainty | 1 | window ceiling, floor and the integrated Chebyshev deficit are the pole to precision `e^{L/2 − κ L^ex}`, every `ex < 3/5` |
| E | VK zero-free region (antitone width, read at a height cut) × de la Vallée Poussin profile below the cut × width–height tradeoff of the lag function | RHTower/Sieve × SquareRootThreshold | 1 | `P_v ≥ −|φ(0)| − (W + S₂) e^{v/2 − v^ex}` for all large lags, every `ex < 3/5` |

Non-circular: no RH input; all statements closed, the only parameters are `ex`, the width `w`, and
the existential constants. Both results carry exactly the strength of the analytic input: the
remainder mechanism (polar Schur bound) and the envelope mechanism (width–height tradeoff) lose
nothing against any subpower error, so the cells now equal the strongest zero-free region in the
corpus. The gap to RH is unchanged: RH is `c(L) ≤ e^{L/2} + O(L)` and `P_v ≥ 0`, and
`e^{L/2 − κ L^ex}` is `O(e^{θL})` for no `θ < 1/2`.

## Gates
- [x] 0 → 1 well-posed, source-pure (compositions of unconditional corpus theorems)
- [x] 1 → 2 paper proofs: see "Approach"
- [x] 2 → 3 Lean, `lake env lean` green with no warnings, `#print axioms` = `propext, Classical.choice, Quot.sound` for all 14 declarations, oleans built single-threaded, umbrella imports appended:
  - `formal/GaloisForLFunctions/BiScaleUncertainty/PrimeWindowCeilingVinogradovKorobovRemainder.lean` (umbrella `BiScaleUncertainty.lean`)
  - `formal/GaloisForLFunctions/SquareRootThreshold/ZetaLagFamilyVinogradovKorobovEnvelope.lean` (umbrella `SquareRootThreshold.lean`)
- [ ] 3 → 4 not pursued

## Approach
**W.** `abs_nodeArchEnergy_sub_weilEnergy_le_profile`: for `ψ(e^y) ≤ e^y + K e^y E(y) + B` with
`0 ≤ E ≤ 1` nonincreasing on `[0, ∞)`, the polar Schur constant on windows of length `L` is
`e^{L/2}(1 + 2K(E(L/4) + e^{−L/4})) + B + (1 + L)²`; the key inequality
`e^{−(L−s)/2} E(s) ≤ (E(L/4) + e^{−L/4})(e^{−s/2} + e^{−(L−s)/2})` is proved by the bulk/ends split
`s ≥ L/4` (profile pays, `E(s) ≤ E(L/4)`) and `s < L/4` (weight pays,
`e^{−(L−s)/2} ≤ e^{−L/4} e^{−s/2}`). The VK majorant `|ψ(e^y) − e^y| ≤ K e^y e^{−c y^ex} + B`,
`0 < c ≤ 1`, comes from `chebyshevError_bound_rpow` with Chebyshev's `ψ(x) ≤ (log 4 + 4)x` absorbing
small `y` (`exists_abs_psi_exp_sub_le_vk`). Upper side: `E(L/4) = e^{−c(L/4)^ex} ≤ e^{−(c/4)L^ex}`
(`L^ex/4 ≤ (L/4)^ex` since `4^ex ≤ 4`), and `κ L^ex ≤ L/8` eventually (`ex < 1`, via
`tendsto_rpow_atTop`), so `C = 4K + 1`, `κ = c/4`. Lower side: `e^{t − c t^ex} ≤ e·e^{T − c T^ex}` on
`[0, T]` by subadditivity `T^ex ≤ (T − t)^ex + t^ex` (`Real.rpow_add_le_add_rpow`) and
`c u^ex ≤ u + 1` for `c ≤ 1`; hence `|D(T)| ≤ T(K e·e^{T}e^{−cT^ex} + B)`; on the polar test with
cutoff `δ = e^{−L/2}`, `T = L − 2δ`: `L^ex ≤ T^ex + (2δ)^ex ≤ T^ex + 1`, `L ≤ e^{(c/2)L^ex}` eventually
(from `e^u ≥ u^N/N!`, `N·ex ≥ 2`), so `2δ|D(T)| ≤ 2K e^{1+c} e^{L/2 − (c/2)L^ex} + 2B` and the
deviation of the polar test is `≥ e^{L/2} − C e^{L/2 − (c/2)L^ex}`. Floor via the Liouville mirror
`|c(L) + floor(L)| ≤ 4(L + 7)`. Deficit corollary: `T e^{−cT^ex} ≤ e^{−(c/2)T^ex}` and
`T ≤ e^{T − (c/2)T^ex}` eventually.

**E.** `exists_re_le_of_mem_zetaCarrier_vk`: a height `γ₀ ≥ exp(e^{30})` such that every carrier
zero with `|γ| ≥ γ₀` has `Re ρ ≤ 1 − vkZeroFreeWidth |γ|` (reflection `ρ ↦ ρ̄` for negative
ordinates). `vkZeroFreeWidth_antitone`: the width decreases in the height (both rpow factors with
negative exponents). `exists_vk_zeroFree_profile`: for `G ≥ G₀` every exponent with `|Im z| ≤ G` has
`Re z ≤ ½ − min(η₁, vkZeroFreeWidth G)`, `η₁ = min(η₀, 1/(100 log G₀))` from the de la Vallée Poussin
profile below `G₀`. Envelope: cut `G = exp(v^θ)`, `θ = (ex + 3/5)/2`, so `ex < θ < 1` and
`r = 1 − 2θ/3 − ex > 0`; `(1 + G)^{−2} ≤ e^{−v^θ} ≤ e^{−v^ex}`; `η₁ v ≥ v^ex` once
`η₁ v^{1−ex} ≥ 1`; `vkZeroFreeWidth(G)·v ≥ v^{−2θ/3}(log v)^{−2} v/10⁸ = v^{ex} v^{r}/(10⁸ (log v)²)
≥ v^{ex}` once `10⁸ (log v)² ≤ v^r` (`isLittleO_log_rpow_atTop`), using
`(θ log v)^{−5/3} ≥ (log v)^{−5/3} ≥ (log v)^{−2}` for `log v ≥ 1`. Then the tradeoff
`abs_two_re_lagStructure_le_of_zeroFree` gives `|φ(v)| ≤ (W + S₂) e^{v/2 − v^ex}`.

## Surveyed and not built
- The zero-width dictionary (`zetaZeroWidth = zetaZeroAbscissa − ½` with the band, deficit, Mertens
  and heat readings) is being built concurrently by another session in
  `SquareRootThreshold/TheWallsMeasureOneZeroWidth` (unwired at the time of this card); not duplicated.
- A VK-strength floor for the polar ground energy `μ₀(A)` needs uniformity over all tests of
  aperture `A`, which the zero-side expansion gives only against the log-weighted energy; the lag
  family avoids this because its test is fixed. Not an assembly.
- Composing the VK zero-free region with the de Bruijn heat flow moves nothing: the heat strip is
  governed by the uniform width `sup |Re ρ − ½|`, which no height-dependent region lowers.

## What the statements do not give
The exponent gap is untouched: no `θ < 1/2` with `c(L) − e^{L/2} = O(e^{θL})` or `P_v ≥ −Ce^{θv}`
follows, and both forms are at scale `e^{L/2}` times a subpower factor. The lag threshold `V₀` of (E)
is existential because the VK region's starting height is.

## Log
- 2026-10-21 — created in 3-formalized; both modules compiled with `lake env lean` (no errors, no
  warnings), oleans built single-threaded (`lake --old env lean -j 1 -o … -i …`), 14 declarations
  audited (`propext, Classical.choice, Quot.sound`), umbrella imports appended, lint run (the only
  unreachable modules reported belong to other sessions). Walls ledger wall-1 cells, BiScale README
  §3.16 and cross-programme paragraph, SRT README item 26 state the new strength.
