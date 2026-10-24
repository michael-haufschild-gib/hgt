# A separating observable with an exponent: the mean value is the leading coefficient of the receiver

- **ID:** sep-obs-exponent
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-2410/fable.md §2.3 E · THIM README 7.8.1 · BVI README 7.8.4
- **Statement:** For `0 < ε < 1/2` and every bounded sign pattern `s` with mean value `L`, the receiver of
  `s(d) d^{-ε}` satisfies `A_s(n) = L Z_ε n^{1-ε} + o(n^{1-ε})` and `E_T(s) = (Γ_ε L² + o(1)) T^{1-2ε}`,
  `Z_ε = ζ(1-ε)/(1-ε)`, `Γ_ε = Z_ε²/(1-2ε) > 0`; a power rate `|S(x) - Lx| ≤ C x^β` transfers to a
  power saving in the remainder; for the Möbius pattern the power rate is equivalent to `Θ < 1`.

## Goal

Opening E asks for a ceiling `E_T(c) ≤ F(T)·(separating functional)² + (lower order)` in which a
functional that separates parity pairs carries an exponent. THIM 7.8.1 asks which separating
observable can be given an exponent so that separating a pair also bounds the paid member; BVI 7.8.4
asks which finite statistic, quantitative in the cutoff, separates the damped Möbius row from its
twin below the Vinogradov–Korobov band.

Answer. The observable is the mean value `L(s) = lim S_s(x)/x` of the sign pattern; for a weight
`k ⋆ d^{-ε}` it is the pole value `K(1-ε) = Σ k(j) j^{-(1-ε)}` of the kernel. It is linear, it reads
signs (the sign-blind data only see the mean of `|s|`), and it carries the exponent `1 - 2ε` with
the universal constant `Γ_ε`, two-sidedly, on the whole bounded damped class — including the actual
Möbius row, its raw twin `μ²` and its Ramanujan twin. The first pronic moment (von Mangoldt pairing)
carries no exponent. The finite statistic of BVI 7.8.4 is the cutoff mean `S_N/N`.

Non-circularity. The leading law uses only the all-damping rate transfer and the smooth-power prefix
asymptotic; its Möbius instance uses the prime number theorem with de la Vallée Poussin rate. The
next rung — a power saving below `T^{1-2ε}` for the actual source — is exactly a power rate for the
Möbius mean, and that is proved equivalent to `Θ < 1`; it is not claimed.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete paper proof, no open dependency
- [x] 2 → 3  formalized: both modules check with `lake --old env lean`; `#print axioms` on every
  headline theorem gives only `propext`, `Classical.choice`, `Quot.sound`; wired into
  `BezoutValuationIncidence.lean`
- [ ] 3 → 4  publication-ready

## Paper proof

Notation. `0 < ε < 1/2`, `a = 1 - 2ε`. For `s : ℕ → ℝ`: `c_s(d) = s(d) d^{-ε}`,
`m_s = Σ_d c_s(d)/d`, `A_s(n) = Σ_{j ≤ n} Σ_{d | j} c_s(d) - m_s n`, `‖f‖_T² = Σ_{n ≤ T} f(n)²/(n(n+1))`,
`E_T(s) = ‖A_s‖_T²`, `S_s(x) = Σ_{e ≤ x} s(e)`, `u ≡ 1`. `s` has mean value `L` if `S_s(x)/x → L`.

**Lemma 1 (linearity).** For bounded `s, t` and reals `α, β`, `A_{αs+βt} = α A_s + β A_t`: the
divisor sums are linear and the means are absolutely convergent series.

**Lemma 2 (smooth power).** `A_u(n) = Z_ε n^{1-ε} + O(n^{(1-ε)/2})` and `E_T(u)/T^a → Γ_ε`.
The first is the floor-sum asymptotic of `d^{-ε}`; the second is the probe energy law at frequency
`t = 0`, whose profile is the constant `|Z|²/(2a) + Z²/(2a) = Γ_ε`.

**Lemma 3 (mean zero gives a small prefix).** If `|r| ≤ 1` and `S_r(x) = o(x)` then
`A_r(n) = o(n^{1-ε})` and `E_T(r) = o(T^a)`.
*Proof.* Fix `θ > 0`; choose `δ ∈ (0,1]` with `3δ^{1-ε} ≤ θ/2` and `η > 0` with
`(13/ε) η (δ/2)^{-ε} ≤ θ/2`, then `X ≥ 1` with `|S_r(x)| ≤ ηx` for `x ≥ X`. For `n ≥ 2X/δ` put
`D = ⌊δn⌋`; then `X ≤ δn/2 ≤ D ≤ δn ≤ n`. The all-damping rate transfer
`|A_r(n)| ≤ 3D^{1-ε} + (13/ε) η n D^{-ε}` gives `|A_r(n)| ≤ θ n^{1-ε}`. For the energy, those cells
are `≤ θ² n^{-2ε}`, so `E_T(r) ≤ C_θ + θ²(1 + T^a/a)` and `limsup E_T(r)/T^a ≤ θ²/a`. ∎

**Theorem A (leading-exponent law).** If `|s| ≤ B` and `s` has mean value `L`, then
`A_s(n)/n^{1-ε} → L Z_ε` and `E_T(s)/T^a → Γ_ε L²`.
*Proof.* Scaling reduces to `B = 1`, so `|L| ≤ 1`. Put `r = (s - L)/2`: `|r| ≤ 1`, mean `0`, and
`A_s = L A_u + 2 A_r` (Lemma 1). The prefix limit follows from Lemmas 2 and 3. For the energy,
the triangle inequality in `‖·‖_T` gives `|‖A_s‖_T - |L| ‖A_u‖_T| ≤ 2‖A_r‖_T`; divide by `T^{a/2}`
and use `‖A_u‖_T/T^{a/2} → √Γ_ε`, `‖A_r‖_T/T^{a/2} → 0`. ∎

**Corollary A1 (the ceiling of opening E, with its floor).** For every `θ > 0` there is `C` with
`(Γ_ε L² - θ) T^a - C ≤ E_T(s) ≤ (Γ_ε L² + θ) T^a + C` for all `T`.

**Corollary A2 (payment forces mean zero).** If `s` has a mean value and `c_s` is paid, then
`L = 0`; if `L ≠ 0` the receiver diverges at the exact rate `Γ_ε L² T^a`.

**Corollary A3 (sign-blind maximum).** If `|s| ≤ t` pointwise and both have mean values, then
`Γ_ε L(s)² ≤ Γ_ε L(t)²`. Among the signings of a nonnegative amplitude `t` the positive signing has
the largest leading coefficient; amplitude data fix `L(t)`, the receiver reads `L(s)`.

**Corollary A4 (the pole value is the mean value).** For a kernel `k` on `[1, J]`, the weight
`k ⋆ d^{-ε}` is `c_s` with `s = (k(j) j^ε) ⋆ 1`, whose mean value is `Σ_j k(j) j^{-(1-ε)} = K(1-ε)`.
So `E_T(k ⋆ d^{-ε})/T^a → Γ_ε K(1-ε)²`: the hyperplane law `K(1-ε) = 0` of THIM §3.16 is the
vanishing of the leading coefficient.

**Theorem B (exponent transfer).** Let `|s| ≤ 1`, `0 ≤ β < 1`, `|S_s(x) - Lx| ≤ C x^β` for `x ≥ 1`,
and `γ = min(2(1-β)(1-ε)/(2-β), a/2) > 0`. Then `E_T(s - L) ≤ K(1 + T^{a-γ})` for all `T`, and
`|√E_T(s) - |L| √E_T(u)| ≤ √K (1 + T^{a-γ})^{1/2}·2`.
*Proof.* `r = (s - L)/2`, `|S_r(x)| ≤ (C/2) x^β`. Put `θ = 1/(2-β)` and `D = ⌊n^θ⌋`, so
`n^θ/2 ≤ D ≤ n^θ ≤ n`. For `x ≥ D`, `|S_r(x)| ≤ (C/2) D^{β-1} x`. The rate transfer gives
`|A_r(n)| ≤ 3 n^{θ(1-ε)} + (13C/ε) 2^{1+ε-β}/2 · n^{1+θ(β-1-ε)}`, and `1 + θ(β-1-ε) = θ(1-ε)`.
Hence `|A_r(n)| ≤ K₀ n^{θ(1-ε)}` for all `n ≥ 1`, each cell is `≤ K₀² n^{-κ}` with
`κ = 2 - 2θ(1-ε) = 2ε + 2(1-β)(1-ε)/(2-β) ≥ 2ε + γ`, and
`Σ_{n ≤ T} n^{-(2ε+γ)} ≤ 1 + T^{a-γ}/(a-γ)`. ∎

**Theorem C (the actual source; the first rung).** For the Möbius pattern:
(i) `S_μ(x)/x → 0` (de la Vallée Poussin rate), so `A_μ(n) = o(n^{1-ε})` and `E_T(μ_ε) = o(T^a)`;
(ii) `Θ < 1` if and only if `|M(x)| ≤ C x^β` for some `β < 1` and all `x ≥ 1`;
(iii) `Θ < 1` implies, for every `0 < ε < 1/2`, `E_T(μ_ε) ≤ K(1 + T^{a-γ})` with `γ > 0`.
*Proof.* (i) is `|M(x)| ≤ B x e^{-√(log x)/12}` with Lemma 3 and Theorem A. (ii) `⇒`: Littlewood's
bound `|M(N)| ≤ C(N+1)^{Θ+δ}` with `Θ + δ < 1`. `⇐`: `Σ_{k ≤ X} |M(k)| ≤ C(X+1)^{1+β}`, and the
absolute-moment exponent law gives `Θ + 1 ≤ 1 + β`. (iii) is Theorem B with `L = 0`. ∎

**Theorem D (the parity pair at the leading exponent; BVI 7.8.4).**
(i) The raw twin `μ²(d) d^{-ε}` has mean `6/π²`, so `E_T/T^a → Γ_ε (6/π²)²`, while
`E_T(μ_ε)/T^a → 0`.
(ii) The Ramanujan twin `c'_ε` satisfies `E_T(c'_ε) ≥ κ_ε T^a` for `T ≥ 200`, from the drift
`A_{c'}(n) ≤ -n Σ_{(n,2n]} c'(d)/d ≤ -K n (2n)^{-ε}`; hence `E_T(μ_ε)/E_T(c'_ε) → 0` at every
damping `0 < ε < 1/2`, in particular below the band.
(iii) The first-moment-blind weight `2ρ_ε δ₁ - μ_ε` has the twin's first pronic moment and the
twin's Ramanujan coefficients at every prime power, yet its receiver is the Möbius receiver,
`o(T^a)`, while the twin's is `≥ κ_ε T^a`: the first pronic moment carries no exponent.
(iv) The finite statistic is the cutoff mean: `|S_μ(N)/N| ≤ B e^{-√(log N)/12}` for `N ≥ N₀`,
while the twin pattern `c'_ε(d) d^ε ≥ (ρ_ε/U_ε) μ²(d)` has cutoff mean
`≥ (ρ_ε/U_ε)(6/π² - (2√N + 1)/N)`. Its limit squared is the leading coefficient of Theorem A.

## Lean

`formal/GaloisForLFunctions/BezoutValuationIncidence/TheMeanValueIsTheLeadingCoefficientOfTheReceiver.lean`
- Lemma 1: `patternPrefix_add`, `patternPrefix_eq_mean_add`.
- Lemma 2: `tendsto_patternReceiver_unitSign_div_rpow` (via `probeEnergyProfile_zero`),
  `tendsto_patternPrefix_unitSign_div_rpow`.
- Lemma 3: `eventually_abs_patternPrefix_le_of_meanZero`,
  `tendsto_patternReceiver_div_rpow_of_meanZero`.
- Theorem A: `tendsto_patternPrefix_div_rpow`, `tendsto_patternReceiver_div_rpow`,
  `tendsto_patternReceiver_div_rpow_of_abs_le`.
- A1: `exists_patternReceiver_floor_ceiling`. A2: `meanValue_eq_zero_of_receiverBounded`,
  `not_receiverBounded_of_meanValue_ne_zero`. A3: `sq_meanValue_le_of_abs_le`,
  `leadingCoeff_le_of_abs_le`. A4: `dirichletConv_unit_eq_dampedSignWeight`,
  `hasMeanValue_kernelPattern`, `tendsto_receiver_dirichletConv_unit_div_rpow`.
- Theorem B: `exists_patternReceiver_le_of_rate`, `hasMeanValue_of_rate`,
  `exists_abs_sqrt_patternReceiver_sub_le_of_rate`.

`formal/GaloisForLFunctions/BezoutValuationIncidence/TheParityPairAtTheLeadingExponent.lean`
- Theorem C: `hasMeanValue_moebiusReal`, `tendsto_moebius_receiver_div_rpow`,
  `tendsto_moebius_prefix_div_rpow`, `zetaZeroAbscissa_lt_one_iff_moebius_rate`,
  `exists_moebius_receiver_le_of_zetaZeroAbscissa_lt_one`.
- Theorem D: `hasMeanValue_moebiusSqPattern`, `tendsto_moebiusSq_receiver_div_rpow`,
  `exists_parityTwin_receiver_ge_rpow`, `tendsto_moebius_div_parityTwin_receiver`,
  `firstPronicMoment_carries_no_exponent`, `parityPair_cutoffMean_separation`,
  `parityPair_at_the_leading_exponent`.

Inputs used from the corpus: the all-damping rate transfer
`abs_weightCenteredPrefix_dampedSign_le_of_linear_all_pos`, the probe energy law
`tendsto_probeEnergy_div_sub_profile`, the smooth-power remainder `abs_subHalfRemainder_le`, the
de la Vallée Poussin rate `exists_abs_sum_moebiusReal_le_sqrtLog`, Littlewood's bound
`RHTower.mobiusMertens_subpower_zetaZeroAbscissa`, the absolute-moment exponent law
`RHTower.zetaZeroAbscissa_le_of_sum_norm_mertens_rpow_le`, the squarefree count
`RHTower.Sieve.abs_sum_moebius_sq_Icc_sub_le`, the twin drift `parityTwin_drift_ge`, and
`firstMomentBlind_parityPair`.

## Status of the opening

Resolved at the leading exponent, unconditionally: the separating observable that carries an
exponent is the mean value (equivalently the pole value of the kernel); its exponent is `1 - 2ε`
with constant `Γ_ε`, and the ceiling of opening E holds with its matching floor on every bounded
pattern with a mean value, the actual Möbius row and its twins included. The first pronic moment
and the von Mangoldt readout carry no exponent. The finite statistic of BVI 7.8.4 is the cutoff
mean.

Open, and identified exactly: the subleading exponent of the actual source. A power saving below
`T^{1-2ε}` for the Möbius receiver follows from, and the power rate of the Möbius mean value is
equivalent to, the zero-free strip `Θ < 1`. The leading law does not reach it: for the Möbius row
the leading coefficient is `0` by the prime number theorem, and what remains is the rate.

## Log
- 2026-10-24 — created in 1-in-progress
- 2026-10-24 — paper proof complete; both modules formalized and audited; moved to 3-formalized
