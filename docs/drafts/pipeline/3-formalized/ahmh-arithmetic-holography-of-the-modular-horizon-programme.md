# Arithmetic holography of the modular horizon programme

- **ID:** ahmh-arithmetic-holography-of-the-modular-horizon-programme
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), programme card
- **Source:** `docs/reports/review-0811/obstacles-summary.md` §2.7 (B117, B109), §2.12
- **Statement:** Decide modular confinement (B117) in its collective and frequency forms, answer Q1–Q4 of §2.12, and build the four tools (seed S-duality, Rademacher with arithmetic poles, Krein holography, cavity noncancellation).

## Goal
Folder `formal/GaloisForLFunctions/ArithmeticHolographyOfTheModularHorizon/`, umbrella
`ArithmeticHolographyOfTheModularHorizon.lean`, foundational README in the folder.

## Targets

| # | Target | Paper | Lean |
|---|---|---|---|
| T1 | Position rigidity: `Λ_F(s) = ∫_𝒟 F E*(s−½)` holomorphic off `{0,½,1}`, `Λ_F(1−s) = Λ_F(s)`, unfolding `Λ_F = ξ(2s)/(2s(2s−1))·𝓜[a₀F](s−1)` for every seed `F` | done | `TheModularMapIsPositionRigid` |
| T2 | Every-seed receiver: rate `y^α` of `a₀F − c` ⇒ `Λ_F(s₀)=0` at zeros of `ξ(2s₀)`, `Re s₀ > 1−α` | done | `TheModularMapIsPositionRigid` |
| T3 | Cavity reduction (B109): one cavity function sees every right resonance ⟺ every right resonance seen by a pair; cuspidal; complete receiver | done | `OneCavityFunctionSeesEveryResonanceThatAPairSees` |
| T3′ | Pair entries are Rankin–Selberg series `ξ(2s)/(2s(2s−1))(2π)^{−s}G(s;ν₁,ν₂)Σρ_u(n)ρ̄_v(n)|n|^{−s}` | done | `ThePairEntriesAreRankinSelbergSeries` |
| T4 | Momentum channels: `σ_w(n) ≠ 0` off `Re w = 0`; Rademacher image sum `σ_{1−w}(n)/ζ(w)` has full order at every zero; resonant state excites every mode | done | `EveryMomentumChannelCarriesEveryResonance` |
| T5 | Landau: one-sided remainder bound ⇒ two-sided zero-free region; seen resonance ⇒ both signs | done (via `N_F = ∫F·N(s−½)`, polar numerator, rescale `y = e^{−v/(2α)}`) | `TheDualSideHasNoSign` |
| T6 | B109 for cavity functions: every resonance seen by an odd tent field; one mirror-odd cuspidal function sees every right resonance; complete cuspidal receiver | done | `TheOddCavitySeesEveryResonance` |
| T7 | Krein holography: the resonance Krein form of the cavity has infinite index of both signs at every resonance, on or off the line | done | `TheCavityKreinFormIsBlindToTheCriticalLine` |
| T8 | Pairwise visibility of Maass cusp eigenforms at every resonance; B109 for Maass cusp forms | done | `TheMaassFormsSeeEveryResonanceInPairs` |
| T9 | Reflection Krein index law: `Λ(s)Λ̄(s*) + Λ(s*)Λ̄(s)` on tent energies has one negative square exactly off the line; RH ⟺ positivity | done | `TheReflectionKreinFormCountsTheOffLineResonances` |
| T10 | The ringdown rate of a seed with `e^{−π|t|}`-decaying polar transform is its zero-free region | done | `TheRingdownRateOfASeedIsTheZeroFreeRegion` |
| T11 | Zagier's theorem for the cavity: RH ⟺ two-mode energies ring down at `y^{3/4−ε}`; zero-free strip ⟺ common rate `α > ½` (M4, M5) | done | `TheTwoModeEnergiesRingDownAtTheZeroFreeRate` |
| T12 | One sharp receiver: one cuspidal function `g` of Maass forms with RH ⟺ rate `y^{3/4−ε}` of `|g|²`, strip ⟺ rate `α > ½` | done | `OneCavityFunctionIsASharpReceiver` |
| T13 | Hecke pairs: `T_p` self-adjoint on `L²(𝒟)`; Hecke eigenforms span each cusp space; pairs of Hecke–Maass eigenforms see every resonance; sharp Hecke receiver | done | `TheHeckeCosetsOfDeterminantP`, `TheHeckeOperatorIsSelfAdjoint`, `TheHeckeEigenformsSeeEveryResonanceInPairs` |
| T14 | Shimura's continuation for level-one cusp forms: weight-½ kernel, decay, holomorphic fold on `Re w > ¼`, unfolding | done | `TheShimuraIntegralOfACuspForm` |
| T15 | One-eigenform B109: diagonal = `ζ(s)` × Shimura integral; blindness to halving pairs; exact criterion | done | `OneHeckeEigenformIsBlindToHalvingPairs` |

## Paper derivations

**T1.** For `F` continuous, `Γ`-invariant, `|F(z)| ≤ C e^{−c Im z}` on `Im z ≥ ½`: on a compact set `K` of
`u` avoiding `{0, ±½}`, `|E*(u; z)| ≤ α y^A + β` on `𝒟` (BHR `exists_completed_bound`), so `F E*` is
dominated by an integrable function on `𝒟` and holomorphy follows by Cauchy domination; the functional
equation is pointwise `E*(−u) = E*(u)`. Unfolding for `Re s > 1`: `∫_𝒟 F E(s) = ∫_{Γ_∞\ℍ} F y^s dμ =
∫_0^∞ a₀F(y) y^{s−2} dy` (strip unfolding `HTGeometry.tsum_setIntegral_fd_eq_two_mul_setIntegral_modularStrip`).

**T2.** If `|a₀F(y) − c| ≤ C y^α` on `(0,1]`, then `𝓜[a₀F − c·1_{(0,1]}](s−1)` is holomorphic on
`Re s > 1 − α`; with T1 the function `Λ_F(s)·2s(2s−1)/ξ(2s)` agrees with it plus an explicit rational term
on `Re s > 1`, so by uniqueness of continuation `Λ_F` vanishes where `ξ(2s)` does in that half-plane.

**T3.** For eigenforms `u_j`, `a_{jk}(s₀) = ∫ u_j ū_k E*(s₀−½)`. For `c` in a weighted `ℓ¹` space,
`g_c = Σ c_j u_j` and `Λ_{|g_c|²}(s₀) = Σ c_j c̄_k a_{jk}`. A sesquilinear form vanishing on the diagonal
vanishes (complex polarization), so the zero set of `c ↦ Λ_{|g_c|²}(s₀)` is closed with empty interior when
some `a_{jk}(s₀) ≠ 0`. The off-line zeros are countable; Baire gives a dense `G_δ` of `c` seeing all of them.

**T4.** `c_c(n) = Σ_{d | (c,n)} μ(c/d) d`, so `Σ_c c_c(n) c^{−u} = σ_{1−u}(n)/ζ(u)` for `Re u > 1`;
`σ_{1−ρ}(n) = Π_{p^a ‖ n}(1 − p^{(a+1)(1−ρ)})/(1 − p^{1−ρ})` vanishes only if `|p^{1−ρ}| = 1`.

**T5.** Landau: if `R(y) ≤ C y^α` (one side) the nonnegative function `C y^α − R` has a Mellin transform whose
abscissa is a real singularity; there is none in the relevant range, so the transform of `R` continues and the
complex poles at the seen resonances are excluded.

**T6.** For a height profile `φ` (continuous, zero below `2` and high up) `G_φ(z) = φ(Im γz) sin(2π Re γz)` with
`Im γz > ½` is well defined (a matrix with `c ≠ 0` sends heights `> ½` below `2`), modular and mirror-odd. On `𝒟`,
`G_φ` is its profile; the unfolding identity `Σ_v ∫_𝒟 P(γ_v z) = 2∫_strip P` for the periodic `P = profile²·E*`,
vanishing below height `1`, keeps only the rows `(0, ±1)`, so `∫_𝒟 G_φ² E*(s − ½) = ∫_0^∞ φ² W_s dy/y²` with
`W_s(y) = ∫_0^1 sin²(2πx) E*(s − ½; x, y) dx`. At `ξ(2s) = 0`, `E* = κ y^{1−s} + tail`, `κ = ξ(2s−1)/((2s−2)(2s−1))`;
for `s = ρ/2`, `ξ(ρ − 1) = ξ(2 − ρ) ≠ 0`. The tail is bounded by `C` for `y ≥ ½`, and `∫_0^1 sin² = ½`, so
`W_s = ½κ y^{1−s} + O(1)`. On the tent `[a, a + 1]`, `a = j + 3 ≥ 2|Im s|`, `|log y − log(a + ½)| ≤ 1/a`, so
`Re(e^{iθ}·½κ y^{1−s}) ≥ ⅛|κ| y^{1−Re s}` when `cos(θ + arg κ − Im s log(a + ½)) ≥ ¾`, which beats `C` once
`a^{1−Re s} > 8C/|κ|`. The tent integral of a function with positive real part on `(a, a+1)` is nonzero. Baire
(T3) over the normalized tents gives one cavity function; mirror-oddness gives zero horocycle means.

**T7.** Tents of different index have disjoint supports, so `b_s(G_j, G_k) = 0` for `j ≠ k` and the Hermitian part
`𝒦_s` is diagonal with entries `Re d_j(s)`. The phase law with `θ = 0, π` gives the sign of `Re d_j` from
`cos(arg κ − Im s log(j + 7/2))`. `ζ` has no real zeros in `(0, 1)`, so `Im s ≠ 0`, and the phases
`Im s log(j + 7/2)` increase (or decrease) to infinity with steps `≤ |Im s|/(j + 7/2) → 0`: the first index past
a target `ψ + 2πk` lands within `½` of it. Infinitely many tents of each sign give negative and positive definite
diagonal blocks of any size.

**T8.** `G_j` is mirror-odd, hence `G_j = Σ_i c_i e_i` in `L²(𝒟)` over the cuspidal eigenbasis. `G_j E*` is bounded
on `𝒟` (`G_j = 0` there above height `j + 4`), so `h ↦ ∫ G_j h̄ E* = ⟨h, G_j E*⟩` is `L²`-continuous and
`0 ≠ d_j = Σ_i c̄_i ∫ G_j ē_i E*` gives `i` with `∫ G_j v̄_i E* ≠ 0`. Then `v_i Ē*` is bounded on `𝒟` (`v_i ≪ e^{−πy}`,
`E* ≪ y^a`), and `∫ G_j v̄_i E* = conj⟨G_j, v_i Ē*⟩ = conj Σ_l c̄_l ⟨e_l, v_i Ē*⟩` gives `l` with
`∫ v_l v̄_i E* ≠ 0`. The eigenbasis is countable (finitely many eigenvalues below each bound); Baire (T3) for an
enumeration gives the cavity function.

**T9.** `K = vw* + wv* = ½(v+w)(v+w)* − ½(v−w)(v−w)*`, so `neg K ≤ rank((v−w)(v−w)*) ≤ 1`, and `K = 2vv* ≥ 0` if
`v = w`. If `x*v = 1`, `x*w = −1` then `x*Kx = 2Re(1·(−1)) < 0`; on two coordinates such `x` exists iff
`v₀w₁ ≠ v₁w₀` (Cramer). `ρ* = 1 − ρ̄` is a zero (conjugation, functional equation) and `ρ* = ρ ⟺ Re ρ = ½`. Phase law
with the aligned rotation: `|d_j(s)| ≥ |κ|/2048 (j+3)^{−1−Re s}` (tent `≥ ¼` on its middle half, `y^{1−σ}|κ| ≥ 16C`);
size: `|d_j(s)| ≤ ¼(|κ| + C)(j+3)^{−1−Re s}`. If `v_j w_J = v_J w_j` for all `j ≥ J` the ratio `|w_j|/|v_j|` is constant,
but the bounds force it between constants times `(j+3)^{Re s − Re s*}`, unbounded or tending to `0` when
`Re s ≠ Re s*`. RH ⇒ every zero in the strip is critical ⇒ PSD; conversely a nontrivial zero has `Re > 0`, and an
off-line one gives a negative square.

**T10.** `P_F(s) = ∫ F (2u−1)N(u) = 4s(2s−1)(s−1)Λ_F(s)` is entire (seed domination) and odd under `s ↦ 1−s`
(`Λ_F` even, `s(s−½)(s−1)` odd). `polarNumerator = A₁Y^{½+u} + A₂Y^{½−u} + A₃·tail` with `A_i` polynomially bounded on the
strip (`ξ` on `−3/2 ≤ Re ≤ 5/2`), the tail bounded uniformly in `Im u`, so `|P_F| ≪ (1+|t|)^N` there. Given
`|P_F(5/4+it)| ≪ (1+|t|)^N e^{−π|t|}`, oddness gives the same on `Re = −¼`, and Phragmén–Lindelöf for
`P_F(z)e^{∓iπz}/(z+3)^N` gives it on the strip. `mellin(a_F)(w) = N_F(w+1)/ξ(2w+2) = P_F(w+1)/(2wξ(2w+2))`; subtract
`cΓ(w)`; `1/ξ(2s) ≪ |t| e^{π|t|/2}|1/ζ(2s)|` (Stirling); shift from `Re w = 1/8` to `θ/2 − 1 + ε`.

**T11.** On `Re s = 5/4`: `P_{uv̄} = 2(s−1)ξ(2s)G(s;ν_u,ν_v)(2π)^{−s}Σρ_uρ̄_v|n|^{−s}`, `ξ(2s)G = s(2s−1)π^{−s}ζ(2s)2^{s−3}ΠΓ`,
four Gammas at `5/8 + i(T ± t_u ± t_v)/2` with `|T+a| + |T−a| ≥ 2|T|`, so `ΠΓ ≪ (1+|T|)^{4N} e^{−π|T|}`; the series is
bounded by `Σ(|ρ_u|² + |ρ_v|²)|n|^{−5/4}/2`. `|u+cv|² = uū + c̄uv̄ + cvū + |c|²vv̄` at the level of responses and of
completed transforms. If `b(u,v) ≠ 0` and `Q(1) = Q(−1) = Q(i) = 0` then `B + B' = 0` and `i(B' − B) = 0`, so `B = 0`.
RH ⇒ zero-free right of `½` ⇒ rate `y^{3/4−ε}`; conversely a right zero `ρ` is seen by a pair (T8), hence by a two-mode
energy, and a rate `y^α` with `α > 1 − Re ρ/2` contradicts the receiver. Zero-free strip `Re > 1 − δ`: take
`Θ = max(1−δ, ½)` and `α = 3/4 − Θ/4 > ½`; conversely `δ = min(2α − 1, ½)`.

**T12.** The pair bound on `Re s = 5/4` is `D_{jk}(1+|t|)^{4N_Γ+3}e^{−π|t|}` with `N_Γ` from the Gamma bound only. Put
`E_j = Σ_{m≤j}(D_{jm} + D_{mj})`, `M_j = max(1, M_j⁰)(1 + E_j)`; then `D_{jk} ≤ E_{max(j,k)} ≤ M_{max} ≤ M_j M_k`. For
`a_j = x_j 2^{−j}`, `|g|² = Σ_{j,k} a_j ā_k v_j v̄_k/(M_j M_k)` (absolutely, `|v_j|/M_j ≤ e^{−πy}`); each term times the
polar kernel is integrable on `𝒟` with `∫|·| ≤ ‖x‖² 2^{−j−k} B`, so the integral of the series is the series of the
integrals and `|P_{|g|²}| ≤ Σ ‖x‖² 2^{−j−k}(1+|t|)^N e^{−π|t|} = 4‖x‖²(1+|t|)^N e^{−π|t|}`. T10 gives the rate; T3 with
pairwise visibility (T8) gives a generic `x` seeing every right zero; the every-seed receiver closes both equivalences.

**T13.** (a) For `M ∈ M₂(ℤ)`, `det M = p`: columns proportional mod `p`, so `M = γ' α_k` with `k = ∞` iff
`p | m₁₁, m₂₁`, else `(m₁₂, m₂₂) ≡ b (m₁₁, m₂₁)`, `k = b`; rows proportional, so `M = α_i^* γ` (`α^*` = adjugate).
(b) `⟨T_p f, g⟩ = Σ_i ∫_ℍ 1_𝒟(α_i^{-1}w) f(w) ḡ(α_i^{-1}w) = ∫_𝒟 f(w) Σ_{i,γ} (1_𝒟 ḡ)(α_i^* γ w)`; the bijection
`(i, γ) ↦ (γ', k)` with `α_i^* γ = γ' α_k` (mod `±1`) and `Σ_{γ'} 1_𝒟(γ' x) = 1` a.e. give `Σ_k ḡ(α_k w)`.
Exactly one `γ'` contributes off the null set `⋃_γ γ^{-1}(𝒟 ∖ 𝒟°)`, and the orbit family is finitely supported, so
the iterated sums may be exchanged. (c) Transport `cuspSpace λ ↪ L²` (injective), commuting symmetric `T_p` ⇒ the
joint eigenspaces span (Mathlib `iSup_iInf_eq_top_of_commute`); sesquilinearity of `b_s` on cusp forms (integrable
pair integrands) moves `b_s(v_l, v_i) ≠ 0` to Hecke eigenforms by induction over the spans; a finite Hecke basis per
eigenvalue, enumerated over the countable spectrum, feeds the cavity construction and the sharp receiver, which only
needs a sequence of cusp forms that sees in pairs.

**T14.** `4γz = γ'(4z)` (`conjFour`) and the multiplier of `θ` give the weight-½ law on `Γ₀(4)`; the Hermite form
`4gz = h((ez+β)/δ)` with `eδ = 4` gives decay `e^{−π Im z/4}` of every translate, so the corpus fold
`RHTower.HalfWeight.rsFold` is holomorphic on `Re w > ¼`. For `Re w > 7/4`: theta unfolding of the zeroth
coefficient, `a_{j²}(4y) = ρ_W(j²) W_ν(8πj²y)`, termwise Mellin transforms `∫ y^{w−7/4}e^{−Ay}W_ν(Ay) = A^{3/4−w}Mel_ν(w−¼)`
(complex order, `|Re ν| < Re w − ¼`), dominated by `|K_ν| ≤ √π√(2/t)` for `|Re ν| ≤ ½`.

**T15.** Hecke eigenvalues are real (Petersson symmetry); `τ = ρ/ρ(1)` is multiplicative with the Chebyshev
recursion, and `U_{2k+2} = U_{k+1}² − U_k²`, `U_{2k+3} = U_{k+1}(U_{k+2} − U_k)` give `τ² = ζ * τ(·²)`. For `Re s > 3`,
`Im s ≠ 0`: `Λ_u = ξ(2s)/(2s(2s−1))(2π)^{−s}G N ζ(s)T(s)` and `Sh_u(w) = 4(2s−2)(2s−1)ζ(2s) c(w) ρ(1) T(s) Mel_ν(s/2)` with
`T = Σ τ(m²)m^{−s}`, `s = 2w − ½`; the identity `4ρ(1)(s−1)c Mel P_u = Γ_ℝ(2s)(2π)^{−s}G N s (s−1)ζ(s) Sh_u` continues to
the half-plane `Re s > 0` (both sides holomorphic there; convex domain). Mirror symmetry of `E*` handles `ρ(1) = 0`.

## Log
- 2026-11-08 — created; README first draft written.
- 2026-11-09 — T1–T4 formalized (4 modules, umbrella wired in MainTheorems); README rewritten with answers.
- 2026-11-09 — T5 formalized (`TheDualSideHasNoSign`), with the worldline-tower corollary (M1).
- 2026-11-09 — T6, T7 formalized.
- 2026-11-09 — T8, T9 formalized; phase law made quantitative.
- 2026-11-09 — T10, T11 formalized.
- 2026-11-09 — T12 formalized.
- 2026-11-09 — T13 formalized.
- 2026-11-09 — T14, T15 formalized.

## No-go closure
- **Exact killing theorem/mechanism:** position rigidity (`differentiableAt_responseContinuation`): the kinematic
  and frequency forms of modular confinement cannot place resonances; the frequency form is RH
  (`CountingHolography.riemannHypothesis_iff_exists_standardForm_bornRule`).
- **Strongest positive survivor:** the collective form (every resonance seen by unitary seeds), the every-seed
  receiver, its one-sided (Landau) strengthening, B109 for cavity functions and the complete cuspidal receiver
  (T6).
- **Krein route:** the Krein form of one resonance has infinite index of both signs at every resonance (T7), so
  its index cannot count off-line zeros; positive survivor: the Krein sign law, and the reflection Krein form of a
  resonance pair, whose index is one exactly off the line (T9): RH ⟺ positivity.
- **New insight:** the holographic dictionary is a residue dictionary; physics contributes visibility, never
  positions.
- **One-eigenform B109:** killed as an unconditional target by the halving obstruction (`pairing_half_eq_zero`);
  positive survivor: the exact criterion `Λ_u(ρ/2) ≠ 0 ⟺ ζ(ρ/2) ≠ 0 ∧ Sh_u((ρ+1)/4) ≠ 0` and the implication
  one-eigenform B109 ⟹ no halving pairs (`zeta_half_ne_zero_of_hecke_seeing`), both in Lean.
- **Status:** seventeen Lean modules, each checked clean. M4 and M5 are proved equivalent to ringdown rates of one
  cuspidal energy of Hecke–Maass forms (they are the zero-free strip and RH). Open: the converse direction of
  one-eigenform B109 (absence of halving pairs and nonvanishing of `L(ρ/2, sym² u)` in the Hecke family).
