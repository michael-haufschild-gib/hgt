# Frustrated Arithmetic Dirichlet Forms (FADF)

Namespace `GaloisForLFunctions.FrustratedArithmeticDirichletForms`; umbrella
`FrustratedArithmeticDirichletForms.lean`. Every theorem is unconditional; equivalences with RH are
labelled as such.

## 1. Motivation

Every window route to RH ends at one quadratic form: Weil's form `W` on tests supported in an interval
`[−c, c]`, for every `c`. RH is `W ≥ 0` on every interval (`a*(ζ) = ⊤`, WVL). The corpus has fixed
what this form is and what a proof of its sign cannot be:

- it is a **nonlocal Dirichlet form**: a logarithmic-order archimedean jump kernel `ω(t) ~ 1/(2t)` (the
  logarithmic Laplacian of the real place), arithmetic jumps of length `log n` at rates
  `w_n = Λ(n)/√n`, a constant potential `2θ′(0)`, a rank-two pole term and the infinite-rank
  trivial-zero Hankel correction;
- it is **frustrated**: its Markov part dies at width `e^{−3/4}`, the even sector is Markov exactly to
  the plastic threshold `log ρ`, the odd sector is frustrated by the prime anti-diagonals (SWC); no
  positive ground state of the whole-line Markov part exists (ACT);
- it is **critical**: no Hardy weight, no rate or variance slack, Weil cone a point, margins doubly
  exponentially small (ACT, GWZ, SWC);
- its extremals are **singular at the boundary** of the interval (SWC);
- its sign is **sensitive to the Euler product inside the strip**: size, density, domination,
  identification and counts do not decide it (ZCG, WVL).

No existing theory treats positivity of such forms. Dirichlet-form theory needs the Beurling–Deny
property, which fails past `log ρ`. Criticality theory (Allegretto–Piepenbrink, Pinchover, optimal
Hardy weights) needs positive supersolutions, which do not exist. Krein and Pontryagin theory count
negative squares but do not decide their absence. Moment theory turns the sectors into Hamburger and
Stieltjes problems but supplies no measure. FADF treats **signed positivity, at exact criticality, of
frustrated nonlocal Dirichlet forms with arithmetic jumps on intervals**, with Weil's form as the
arithmetic instance and the forms obtained by changing the arithmetic data as its calibration space.

The calibration space is the point of the field. A theorem of FADF says which data it reads: a
statement valid for every weight sequence in a convex set cannot select `ζ`, and a mechanism that does
not separate `ζ` from twins, flips, Beurling systems or finite carriers cannot prove RH. Each question
is asked twice: for the arithmetic datum `Λ`, and as a structure statement on the space of data.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Window form | `weilQuad` (SSHA), `weilFullFunctional` (RHTower) | `W(F) = 2θ′(0)‖F‖² + 𝒥(F) − P(F) + 2C(F)² − 2S(F)²` on `C²` tests in `[−c, c]` |
| Lévy energy | `levyEnergy` | `𝒥(F) = ∫_0^∞ω(x)‖F − F(· + x)‖²dx`, `ω(x) = e^{−x/2}/(1 − e^{−2x})` |
| Arithmetic part | `primePart`, `weightedPrimePart` | `P_λ(k) = Σ_{n≥2}λ(n)n^{−1/2}(k(log n) + k(−log n))` on `k = F⋆F̃` |
| Archimedean–polar part | `weilFullFunctional (fun _ => 0)` | `H = W + P`: the form with the arithmetic jumps removed |
| Hardy interval | `hardyInterval c` | `ℋ(c) = {t : H − tP ≥ 0 on [−c, c]}` |
| Calibration space | `calibration c` | `𝒜(c) = {λ : the form with weights λ is ≥ 0 on [−c, c]}`, the finite-level Weil cone |
| Stage fibre | `withWeight`, `stageFibre_interval` | `{t : λ with λ(n₀) := t lies in 𝒜(c)}` |
| Edge cost, edge-law constant | `edgeCost`, `edgeLawConstant` | `|λ(n)|/(√nΩ(2c − log n))` for acting `n`; `E_c(λ)` their sum, `Ω(δ) = ∫_δ^∞ω` |
| Two-site test | `twoSiteTestAt ℓ r ε` | bumps of radius `r` at `±ℓ/2`, relative sign `ε` |
| Sector kernels | `evenSectorKernel`, `oddSectorKernel` | `k₊ = ω(|u−v|) + ω(−u−v) − 4cosh(u/2)cosh(v/2)`, `k₋ = ω(|u−v|) − ω(−u−v) + 4sinh(u/2)sinh(v/2)` on the half-window |
| Sign gauge | `IsSignGauge` | `σ : ℝ → {±1}`, switching `k(u, v) ↦ σ(u)σ(v)k(u, v)` |
| Edge masses | `leftEdgeMass`, `rightEdgeMass` | mass of `f²` within distance `x` of an edge |
| Regional energy, edge killing | `regionalEnergy`, `edgeKilling` | jumps inside `[a, b]`; `∫_0^∞ω(x)(m_a(x) + m_b(x))dx` |
| Spike | `dilatedSpike` | `C²` bump of height `1`, width `w` |
| Mirror moment, mirror mass | `mirrorMoment`, `mirrorKilling` | `m_α(f) = ∫fe^{αu}`; `K_α(f) = (∫_{−c}^0e^{αv})∫f²e^{αu}` |
| Reflected, antireflected energy | `neumannEnergy`, `dirichletEnergy` | `½∬_{[−c,0]²}e^{α(u+v)}(f(u) ∓ f(v))²` |
| Trivial modes | `trivialMode j` | `α_j = 2j + ½`, `Σ_je^{−α_jx} = ω(x)` |

## 3. Language

- **Z-type / Markov**: every off-diagonal conductance `≥ 0`; `|F|` does not raise the energy.
  **Frustrated**: no sign gauge makes every conductance `≥ 0`. **Balanced**: some sign gauge does.
- **Switching** changes conductance signs and moves mass to the potential; positive gauges never change
  a conductance sign.
- **Hardy term**: `P` with `H − P ≥ 0`; **optimal**: a Hardy term on every window, no other multiple is
  one, and no Hardy weight remains.
- **Entry** of `n`: the half-width `½log n`; **sliver width** `δ = 2c − log n`.
- **Edge data**: what a functional continuous in the energy norm can read at a boundary; the
  **centre** of a symmetric window is a boundary of the half-window.
- **Calibration**: dependence on the arithmetic datum; a statement is **selective** if it fails for
  some datum sharing the archimedean place and the pole with `ζ`.

## 4. Mechanisms

1. **Affinity in the data.** On every test the functional is affine in the weights
   (`weilFullFunctional_eq_sub_weightedPrimePart`): `ℋ(c)` and `𝒜(c)` are closed convex sets, nested in
   `c`, and a window is a family of half-spaces in the space of data.
2. **Two sites read one weight.** Bumps at `±½log n₀` narrower than the gaps of `log` at `n₀` have an
   autocorrelation meeting the single lag `log n₀`; their even and odd versions bound the weight
   `λ(n₀)` from above and below (`weightedPrimePart_twoSiteAt`). Their archimedean–polar energy is the
   Weil energy without its prime part, `O(r log(1/r))` by the logarithmic self-energy of an atom, while
   the weight is read with mass `r`: the confinement is logarithmic in the radius.
3. **Cone uniqueness.** A weight sequence admissible on every window is `Λ` (RHTower,
   `eq_vonMangoldt_of_weilPositiveFull`): every scaling but `1` is eventually excluded.
4. **The logarithmic diagonal forbids nodes.** `ω(t) ≥ e^{−1/2}/(2t)` makes both sector kernels large
   and positive near the diagonal; a sign gauge that changes sign does so at arbitrarily close pairs
   (bisection), so every node is a negative switched conductance.
5. **Regional–edge decomposition.** For `f` vanishing off `[a, b]` each jump either stays, leaves
   through `b` or enters through `a`; integrating, `𝒥 = 𝒥_reg + 𝒦` with the edge killing energy `𝒦`.
6. **Atoms of height one are cheap.** A spike of width `w` has `𝒥 ≤ 2√w + O(w)`: point values are
   invisible in the energy norm, and, Weil's form being continuous in that norm (SSHA), invisible to
   Weil's form.
7. **Every lag of an acting power is an edge datum.** For `ℓ = 2c − δ` the correlation
   `∫f(s)f(s − ℓ)ds` lives on the two edge slivers of width `δ`, so `2Ω(δ)|∫f(s)f(s − ℓ)ds| ≤ 𝒦 ≤ 𝒥`.
   Summed over the acting powers this is the edge law `|P_μ| ≤ E_c(μ)𝒥`: size pays a change `μ` of the
   weights as long as the form has Lévy margin `E_c(μ)`. On odd tests the archimedean–polar form is
   `2θ′(0)‖f‖² + 𝒥 − 2S² < 𝒥` (`θ′(0) < 0`), so the edge law dies at `E_c = 1`. Every size-only
   certificate dies at a finite window: there `H` itself is negative on a real test, and every
   admissible weight system has a strictly helpful prime part on that test.
8. **Mode-wise Cauchy–Schwarz at the centre.** For each trivial-zero mode,
   `m_α² + ½∬e^{α(u+v)}(f(u) − f(v))² = K_α`; summing, the trivial-zero Hankel form is the centre's
   mirror mass minus a reflected energy (even sector) or an antireflected energy minus the mirror mass
   (odd sector), and the mirror mass is centre-edge killing (`Σ_je^{−α_jx} = ω(x)`, Fubini).
9. **Pole charges, sliver signatures, contraction law, visibility** (SWC, CSTW, WVL): used as stated
   there.

**The mechanisms §2.7 asks for, in their present form.** The *exact collective identity* on
reflection pairs is the mirror pairing `𝒞_m(f) = W(f, f∘R_m)` (proved; its sign is the band, open
past the base). The *renormalization from `a` to `2a`* that keeps the cross-correlation is the
parity reduction of a window to its half-window with the centre as a reflecting or antireflecting
boundary (proved, with the trivial zeros paid at the centre); what it does not supply is the prime
cross-correlation at the doubled scale. The *margin transport law* across entries is the stage fibre
with its logarithmic entry law, proved from both sides, and the summed edge law beyond the sliver. The *criticality-preserving signed gauge flow* and the
*repulsion law at near-coincidences* are open (§7).

## 5. Questions

| # | Question (review §2.7) | Answer |
|---|---|---|
| Q1 | Is the arithmetic part an optimal Hardy weight for the archimedean logarithmic jump operator with the pole kept? | **Iff RH**; everything but admissibility is unconditional. `ℋ(c)` is a closed interval, `= ℝ` before the first prime (`2c < log 2`), bounded from the first entry on (`2c > log 2`); a multiple admissible on every window is `1`; Weil's form admits no Hardy weight on odd tests (`question_one`, `isOptimalHardyTerm_iff_RH`) |
| Q2 | What replaces Perron–Frobenius past `log ρ`; which nodal structure; stable across entries? | Balance holds exactly to `log ρ` (even, `evenSectorKernel_nonneg_iff`) and to `½log 2` (odd). Past these thresholds frustration survives **every** sign gauge (`even_frustrated_in_every_sign_gauge`, `odd_frustrated_in_every_sign_gauge`): a certificate is either a positive gauge whose negative Doob edges are paid by the positive network, or a nodal gauge paying a negative light-cone conductance at each node. The even frustration locus is the pole's (edge, centre) pairs for every choice of nonnegative prime weights (SWC `evenBand_markov_iff`), hence stable across entries; the odd light cone is positive, and each acting prime power adds one anti-diagonal frustrated in every sign gauge (`odd_frustrated_at_every_entry`, `question_two`) |
| Q3 | Which gauge family, exact on the line, restricts to every window with a nonnegative remainder in both sectors? | The theta gauge `Φ` in the even sector and the shifted ground states `ω_a` (every `a > 0`) in the odd sector, **with the pole-charge variance retained**: on every window the window is nonnegative iff both remainders are (SWC); so the family exists on every window iff RH (`question_three`). Pointwise remainders are impossible for nonnegative gauges: nonnegative even theta gauges have a negative cosh-charged defect, variance-dropped odd certificates fail below `log 4` (SWC). Survivor: the even deficit is an artifact of nonnegativity — the signed gauge `τ_0 − ¼(τ_b + τ_{−b})`, `b ≥ max(2c, 4)`, is positive on the window and has negative outside cosh charge, so its even potential term is a credit (`exists_signedThetaGauge`, `fullZeroForm_signedThetaGauge_eq`); the cost moves into negative jump conductances toward the lobes, which the theta functional equation pays back exactly. A nonnegative remainder must therefore control the jumps toward the outside charges |
| Q4 | Collective law of the sliver signatures against the pole square on a reflection pair, uniformly in the stage? | On a reflection pair the collective pairing is Weil's pairing of the test with its mirror, `𝓗_m(f) − Σ_nw_n(f⋆f)(2m − log n) = W(f, f∘R_m)` (`coupling_eq_weilPair`); its kernel form is minus the Weil jump measure `κdt + Σw_nδ_{log n}` against the reflected autocorrelation (CSTW). The band `|𝒞_m(f)| ≤ W(f)` is positivity of the pair; uniformly in the stage — on the centred pairs of every half-window — it is RH (`question_four`). For an even bump the stage-`m` law is its orbit correlation at `2m` (`coupling_eq_weilOrbitCorr_of_even`), strict under RH at every stage (`abs_coupling_lt_of_RH`): the stage-uniform collective law is an orbit Cauchy–Schwarz, whose failure is an exponential rate (GWZ, AOG) |
| Q5 | Trace theory of critical extremals; which boundary data does a certificate see? | **No trace.** `𝒥 = 𝒥_reg + 𝒦` with the edge killing `𝒦 ≤ 𝒥` (`levyEnergy_eq_regional_add_edge`); the plateau `1_{[a,b]}` has finite energy, all of it edge killing (`edgeKilling_indicator`); point evaluation is unbounded in the energy norm (`exists_spike`), and Weil's form itself changes by at most `ε` when a height-one spike is added at any point of the window, the edge included (`exists_spike_weilQuad_close`). A certificate sees boundary values only as logarithmically weighted edge masses. At the centre of a symmetric window the half-window pays the trivial zeros exactly, mode by mode: reflected in the even sector, antireflected in the odd sector (`even_sector_iff_reflected`, `odd_sector_iff_antireflected`) |
| Q6 | How are margins transported across prime entries; what replaces soft entry beyond the sliver? | **Each entry confines its weight**: for `log n₀ < 2c` the weight `λ(n₀)` is bounded on `𝒜(c)` (`calibration_coord_bounded`), and for fixed older weights the admissible values of the newest weight form a compact interval (`stageFibre_interval`). **The entry is logarithmically soft**: once the sliver `δ = 2c − log n₀` is below the gap of `log` at `n₀`, `|λ(n₀)| ≤ √n₀(A log(1/δ) + B)` on `𝒜(c)` (`abs_calibration_coord_le_log`), and **soft from inside at every prime power**: with a Lévy margin `η` the fibre contains every `t` with `|t − λ(n₀)| ≤ √n₀ηΩ(δ)`, `Ω(δ) ≥ (e^{−1/2}/2)log(1/δ)` (`stageFibre_two_sided`). **The leading constant is one outside and one half inside**: `|λ(n₀)| ≤ √n₀(log(1/δ) + B)` on `𝒜(c)` (`abs_calibration_coord_le_log_add`, exact two-atom pair energy), and the fibre contains `|t − λ(n₀)| ≤ √n₀η(½log(1/δ) − ¼)` (`stageFibre_sharp`). So the transported quantity is the position of `Λ(n₀)` in a stage fibre of length `≍ √n₀ log(1/δ)` at the entry, with leading constant between `η` and `2`, bounded beyond the sliver. **Beyond the sliver** soft entry is replaced by the summed edge law: size pays a change `μ` of all acting weights up to the edge-law constant `E_c(μ)` (`add_mem_calibration_of_edgeLaw`), and this size-only certificate dies at `E_c = 1` (`not_edgeLaw_of_one_le`) — for `ζ` at a unique window `c*` with `E_{c*}(Λ) = 1` and `2c* ∈ (log 5, log 6]`; `E_c(Λ) < 1` exactly for `c < c*` (`exists_edgeLaw_threshold`, `edgeLaw_fails_from_log_six`). Past it the primes are paid collectively and by sign (SWC sliver signature), and from a finite window on they **must** be: one real test has `H(f) < 0`, so `P_λ(f) < 0` for every `λ ∈ 𝒜(c)` and no bound `|P| ≤ E𝒥` certifies the window (`primes_pay_by_sign`) (`question_six`, `question_six_beyond_the_sliver`) |
| Q7 | The global canonical system; does positivity propagate stage by stage? | Positivity propagates from `ℓ` to `ℓ + ε` iff translation by `ε` is a contraction (CSTW); RH iff every growth step is (`question_seven`). Propagation is not automatic: in the calibration space each step is a compact interval constraint on one new weight. The continuum system with the kicks is open (B17) |
| Q8 | How does the Euler product inside the strip act as a repulsion law at near-coincidences? | Reality at near-coincidences is the absence of heat collisions: RH iff every heat zero is simple for `t > 0` (RHTower); size cannot repel: Lindelöf-bounded pair models collide below every positive time scale (ZCG) (`question_eight`). The repulsion input is open (B44) |

## 6. Tools

Developed here:
- **Calibration calculus**: affinity of Weil's functional in the weights; the Hardy interval and the
  calibration space as closed convex sets; two-site tests at any distance; the entry confinement; the
  stage fibre; the archimedean–polar energy of a narrow two-site test
  (`2θ′(0)‖F‖² + 𝒥(F) + 2C² − 2S²`, `O(r log(1/r))`); the logarithmic entry law from both sides; real
  tests decide `𝒜(c)`.
- **Edge-law calculus**: every lag of an acting power as an edge datum; edge costs; the edge-law
  constant; the edge-law certificate and the threshold `E_c = 1` where size stops paying; the finite
  window beyond which the primes must pay by sign.
- **Switching calculus** of the sector kernels: the logarithmic lower bound for `ω`; bisection for sign
  gauges; balance and frustration thresholds.
- **Trace calculus** of the logarithmic jump form: pointwise split of jumps at the edges; edge masses;
  regional energy; edge killing; plateau energy `2∫_0^∞ω(x)min(x, b − a)dx`; height-one spikes.
- **Centre calculus**: mode-wise Cauchy–Schwarz with exact defect; mirror masses; Fubini at the centre
  edge; reflected and antireflected energies; sector forms with the trivial zeros removed.

The tools review §2.7 lists, and where each lives:

| Tool (§2.7) | Where |
|---|---|
| Criticality theory, optimal Hardy weights | here (Hardy interval, Q1); ACT (null sequences, no Hardy weight) |
| Signed-graph theory: switching, frustration index, Kron reduction | here (switching of the continuum sector kernels, Q2); AOT (frustration index of finite ledgers); SAEI (Kron domination) |
| Krein and Pontryagin spaces | PM/RIT (Krein–Lax–Phillips space, Krein squares); AKG (index calculus) |
| Krein strings, de Branges spaces, Szegő–Levinson | GWZ, SWC (lattice Levinson recursion, jet Hankel system, reflection coefficients at `±1`); RHTower (de Branges gauges) |
| Hamburger/Stieltjes moment theory | SWC (sectors as moment problems of jet energies) |
| Beurling–Malliavin completeness radii | TMWP (Beurling radius of receivers) |
| Doob transforms | ACT, SWC (ground-state and pole-charged representations) |
| Exactness by homogeneity | SSHA (logarithmic self-energy of atoms, used here for the entry law) |
| Pole-charged representation, sliver signature, outward-edge calculus | SWC; here the edge calculus is extended to the regional–edge decomposition and the centre calculus |
| Onset-aperture calculus, camera | WVL, ZCG |

Used from the corpus: SWC (window form, parity sectors, band, collar Hankel form, Markov–Hankel
equivalences, sliver signature, retained-variance certificates, Perron sign law); ACT (Doob gauges,
null sequences, theta gauges); RHTower (Weil cone uniqueness, finite-level cones, Lévy form, base floor,
heat collisions); DZG (locality of the finite-level cone); SSHA (Lévy form of `W`, atom self-energy);
CSTW (ordered coupling, contraction law); WVL, SRT (onset aperture, window positivity ⇔ RH); ZCG (pair
models).

## 7. Open research topics

1. **The structural certificate below `log 4`** (review §2.8, B5): `(Λ(2)/√2, Λ(3)/√3)` in the stage
   fibres for every `c < log 2`. After the centre calculus the sector forms read: even
   `P ≤ 2θ′(0)‖f‖² + (𝒥 − Σ_jK_j) + Σ_jN_j + 4C²`, odd `4S² ≤ 2θ′(0)‖f‖² + (𝒥 − Σ_jK_j) + Σ_jD_j + P`,
   every term except `2θ′(0)‖f‖²`, the pole square and the prime reflections nonnegative. The open core
   is how the pole square pays the constant potential (even) and how the prime reflections pay the pole
   square (odd).
2. **Signed ground states past `log ρ`** (B49): the nodal structure of the critical gauge.
3. **Sharp entry constant**: the stage fibre of `λ(n₀)` has half-length between `√n₀η(½log(1/δ) − ¼)`
   (with a Lévy margin `η`) and `√n₀(log(1/δ) + B)` (both proved, leading constants `η/2` and `1`).
   Open: whether the outer constant `1` is attained, and the dependence on the older weights.
4. **Collective payment on every reflection pair** (B3); equivalent to RH (`question_four`).
5. **The global canonical system with the kicks** (B17); positivity at every growth step is equivalent
   to RH (`question_seven`).
6. **Repulsion at near-coincidences through the prime channel** (B44); absence of heat collisions is
   equivalent to RH (`question_eight`).

## 8. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| `H − tP` is affine in `t`; `ℋ(c)` closed, convex, antitone | `weilFullFunctional_scaledWeights`, `convex_hardyInterval`, `isClosed_hardyInterval`, `hardyInterval_anti` | unconditional |
| `ℋ(c) = ℝ` before the first prime; bounded from the first entry on | `hardyInterval_eq_univ`, `hardyInterval_bounded` | unconditional |
| Scaling optimality; criticality; optimal Hardy term iff RH | `eq_one_of_forall_mem_hardyInterval`, `not_exists_hardyWeight`, `isOptimalHardyTerm_iff_RH`, `riemannHypothesis_iff_iInter_hardyInterval_eq` | unconditional / RH-equivalent |
| Balance thresholds and non-switchable frustration of both sectors; every entry frustrates the odd sector | `evenSectorKernel_nonneg_iff`, `even_frustrated_in_every_sign_gauge`, `odd_frustrated_at_every_entry`, `oddSectorKernel_pos`, `exists_close_pair_ne` | unconditional |
| Regional–edge decomposition; edge Hardy inequality; plateau energy | `levyEnergy_eq_regional_add_edge`, `edgeKilling_le_levyEnergy`, `levyEnergy_indicator`, `edgeKilling_indicator` | unconditional |
| No point traces; Weil's form cannot read point values | `exists_spike`, `levyEnergy_dilatedSpike_le`, `exists_spike_weilQuad_close` | unconditional |
| Mode identities at the centre; mirror mass is edge killing; sector forms with the trivial zeros removed | `sq_moment_add_neumann_eq`, `dirichlet_eq_add_sq_moment`, `tsum_mirrorKilling_le_edgeKilling`, `even_sector_iff_reflected`, `odd_sector_iff_antireflected`, `markov_sub_mirror_eq` | unconditional |
| Calibration space convex; entry confinement; stage fibre a compact interval | `convex_calibration`, `calibration_coord_bounded`, `stageFibre_interval` | unconditional |
| The entry is logarithmically soft, from both sides; real tests decide `𝒜(c)` | `abs_calibration_coord_le_log`, `stageFibre_two_sided`, `realCalibration_eq_calibration` | unconditional |
| The entry constant is one outside, one half inside; exact two-site energy | `abs_calibration_coord_le_log_add`, `stageFibre_sharp`, `levyEnergy_twoSite_eq`, `levyTail_ge_half_log` | unconditional |
| Every lag is an edge datum; the summed edge law; the edge-law certificate and its death at `E_c = 1` | `abs_integral_mul_shift_le_edgeKilling`, `abs_re_weightedPrimePart_le`, `add_mem_calibration_of_edgeLaw`, `re_archPolar_eq`, `not_edgeLaw_of_one_le`, `edgeLaw_fails_for_vonMangoldt` | unconditional |
| The edge law of `ζ` has a unique threshold `c*`, `E_{c*}(Λ) = 1`, `2c* ∈ (log 5, log 6]`; edge costs continuous across entries | `exists_edgeLaw_threshold`, `continuous_edgeCost`, `strictMonoOn_edgeLawConstant_vonMangoldt`, `edgeLaw_fails_from_log_six` | unconditional |
| Beyond a finite window the primes pay by sign, uniformly over `𝒜(c)` | `exists_archPolar_neg`, `primes_pay_by_sign` | unconditional |
| The collective law is the mirror pairing; for even bumps the orbit correlation | `coupling_eq_weilPair`, `coupling_eq_weilOrbitCorr_of_even`, `abs_coupling_lt_of_RH` | unconditional / under RH |
| Signed theta gauges reverse the even outside deficit | `exists_signedThetaGauge`, `fullZeroForm_signedThetaGauge_eq` | unconditional |
| The eight answers | `question_one` … `question_eight` | unconditional / RH-equivalent |

## 9. Traps

| Trap | Truth |
|---|---|
| A positive gauge can remove a frustrated conductance | Positive gauges never change conductance signs; sign gauges do, and past the thresholds no sign gauge removes all of them |
| A clever sign gauge balances the even band past `log ρ` | Every sign change is a negative light-cone conductance (logarithmic diagonal); a constant gauge keeps the pole's (edge, centre) pair negative |
| Frustration past `log ρ` means the ground state changes sign | Beurling–Deny fails; whether the critical gauge has a node is open (numerically it has none) |
| The window form imposes a boundary condition | The energy space has no traces; plateaus with jumps at the edge have finite energy |
| Boundary values of an extremal are certificate data | Only edge masses weighted by `Ω(δ) ~ ½log(1/δ)` are |
| The trivial-zero squares are part of the frustration | The centre pays them exactly, mode by mode; the frustration is the constant potential, the pole square and the prime reflections |
| The Lévy energy pays the primes on wide windows | Only up to edge-law constant `E_c < 1`: on odd tests `H < 𝒥`, so size fails for `ζ` from `2c = log 6` on |
| A window reads all the arithmetic | It reads the finitely many weights it sees, convexly; a weight is free before its entry and confined after |
| A statement valid on a convex set of weights selects `ζ` | It holds for every datum in the set; selection is the tower `⋂_c𝒜(c)` |
| Reformulations are progress | Band, Markov–Hankel, retained-variance, Hodge index, Künneth and reflected forms are all equivalent to window positivity |

## 10. Place in the research and relation to other programmes

| Programme | Relation |
|---|---|
| SWC | the window form with the pole kept and every sign used; FADF takes its sector forms, band and certificate format as the arithmetic instance and answers the §2.7 questions about the class |
| ACT | whole-line ground states, Doob gauges, null sequences (criticality in Q1) |
| RHTower | Weil cone uniqueness and finite-level cones (Q1, Q6), heat collisions (Q8) |
| DZG | locality of the finite-level cone |
| SSHA | Lévy form of `W`, self-energy of atoms (Q5) |
| CSTW, GWZ, WTZ | ordered coupling, contraction law, lattices and two sites (Q4, Q7) |
| WVL, SRT | onset aperture; every FADF lower bound is a lower bound for `a*(ζ)` |
| ZCG | pair models and the camera (Q8) |
| AOT | frustration index of finite ledgers |

## 11. Success criteria and criteria for contributions

The criteria of review §2.7: reproduce the base, `log ρ`, the first stages and their margins; pay the
pole's negative square (odd) and the cosh deficit (even) with variance retained; be critical; deliver
the band on every reflection pair; pay the primes `3 ≤ p ≤ 73` by sign; cross `log 5`; distinguish `ζ`
from finite carriers, pair models, twins, flips, Beurling systems and Epstein data; use the functional
equation and the Euler product together; explain `λ = ½`.

| Criterion | Status in FADF |
|---|---|
| Base, `log ρ`, first stages | `log ρ` is the even balance threshold, `½log 2` the odd one and the first entry of the calibration space; the base enters as `1 ∈ ℋ(c)` up to the unconditional floor aperture `> 181/500` |
| Criticality | optimal Hardy term iff RH, with scaling optimality and no Hardy weight unconditional |
| Band on reflection pairs | the Q4 answer |
| Distinguish `ζ` | windows read weights convexly and confine each acting weight; only the tower `⋂_c𝒜(c) = {Λ}` (under RH) selects |
| Cross `log 5` | the edge law of `ζ` reaches one at a unique window `c*`, `2c* ∈ (log 5, log 6]` (`exists_edgeLaw_threshold`): the review's `log 5` is the one-edge count, and paying each lag at both edges moves the crossing past it. From `log 6` on no size-only edge certificate holds, and every size-only certificate dies at a finite window (`primes_pay_by_sign`); crossing needs sign |
| Pay the primes by sign, pay the pole squares | open (§7.1, §7.4) |

A contribution must be an identity, an equivalence, a classification, a sharp law, or a no-go with its
strongest positive survivor; it must say which data it reads; it must be unconditional.

## 12. Big picture

Weil's form on a window is a frustrated nonlocal Dirichlet form, and the field asks what positivity of
such a form can rest on. Seen in the space of its arithmetic data, a window is a closed convex set: it
reads only the weights it sees, leaves each weight free until its entry and confines it from then on
(logarithmically in the sliver width at the entry, from both sides, so that each stage step is a
compact interval in the newest weight). It pays changes of its weights by size only while their
edge-law constant stays below one, and beyond a finite window the primes must pay by sign. The tower
of windows shrinks to the single point `Λ` exactly under RH, so the arithmetic part is an optimal Hardy
term for the archimedean operator iff RH, with every other optimality property unconditional. Seen as a form on the half-window, its boundary carries no traces: the energy is regional
plus logarithmic edge killing, and the centre of the window, a second boundary, pays the trivial zeros
exactly, reflecting them in the even sector and antireflecting them in the odd sector. What remains is
frustration that no sign gauge removes — the pole's long-range pairs in the even sector past `log ρ`,
the prime anti-diagonals in the odd sector from each entry on — and three terms that must pay each
other: the constant potential, the pole square and the prime reflections. Gauges move these payments
around but do not remove them: a signed theta gauge turns the even outside deficit into a credit and
pays for it with negative jumps toward its lobes. The first open instance is the window
below `log 4`, where that payment is two numbers in a compact interval per stage.
