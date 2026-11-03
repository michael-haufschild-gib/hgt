# Dimension-Zero Geometry of Spec ℤ (DZG)

Namespace `GaloisForLFunctions.DimensionZeroGeometryOfSpecZ`; umbrella `DimensionZeroGeometryOfSpecZ.lean`.
Every theorem is unconditional; equivalences with RH are labelled as such.

## 1. Motivation

On a window `W_A` (real `C²` tests supported in `[−A, 0]`) the arithmetic acting on Weil's form is the
Dirichlet ring truncated at `⌊e^A⌋`, and Weil's arithmetic term is the derivative at dimension zero
of a family whose values in positive dimension are point counts (WTZ):

`Q(H) = D(H) − 2⟨ρ_A(Λ)H, H⟩ = Ω(0)τ_H(0) − 2τ_H′(0) + J_∞(H) + pole(H)`, `τ_H(k) = ⟨ρ_A(J_k)H, H⟩`,

with `J_k(m) = φ(m)#ℙ^{k−1}(ℤ/m)` Jordan's totient and `D(H) = Ω(0)‖H‖² + J_∞(H) + pole(H)` the
archimedean–polar part. RH is the sign of this jet on every window. Three facts fix the kind of theory
that can produce the sign:

- **No slack.** The Weil cone is a point; window margins are doubly exponentially small; no finite
  identity, finite carrier or lossy estimate survives (CWS, ACT, RHTower).
- **Positivity in positive dimension is soft.** The counts are nonnegative in every positive dimension
  for `ζ` and for fakes alike (`ζ(s)ζ(s−ε)`, WTZ).
- **One wall.** Every route ends at the same statement: on every window, the folded arithmetic jump
  process has a positive ground state with sinh capacity at most one.

Over `𝔽_q` the passage from counts to positivity is made by the geometry of `C × C`. Over `ℤ` there is
no surface: there is a tower of windows, a jump process on each, a reflection `σ_A`, and a family of
counts in a continuous dimension `k` whose derivative at `k = 0` is the arithmetic. DZG is the
geometry of that point `k = 0`: what positivity a family in nonzero dimension can carry to it, what
the archimedean place is in dimension `k`, which operators can play Frobenius, and what the
archimedean place alone satisfies.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Autocorrelation | `corr`, ACT `autoCorr` | `c_H(t) = ∫H(u)H(u + t)du` |
| Archimedean–polar part | `archPolar` | `D(H) = Ω(0)‖H‖² + J_∞(H) + ½⟨c,H⟩² − ½⟨s,H⟩²` |
| Jet pairings | `jetPairing j A H`, `tateJetFunction` | `⟨ρ_A(Λ_j)H, H⟩`, Bombieri's `Λ_j = μ * log^j`; `Λ_1 = Λ`, `Λ_2` = Selberg's function |
| Prime-blind remainder | `tateRemainder A k` | `R_A(k) = Σ_{n≤e^A}(n^k − 1 − k log n)n^{−1/2}` |
| Canonical dominating family | `canonicalArch A H k` | `A_k(H) = kD(H) + 2R_A(k)‖H‖²` |
| Tate-twisted pairing | `tateTwistedForm k H` | `Q^{(k)}(H) = W(e^{k·}H, e^{−k·}H)` (symmetric dimension) |
| Tilted jump measure | `tiltedLevyEnergy`, `tiltedPrimeSum`, `tiltedPole` | archimedean rate `ω(t)cosh(kt)`, prime rate `Λ(n)n^{−1/2}cosh(k log n)` |
| Bumps on a window | `bumpAt b ρ ℓ` | a short bump moved to `[−2ρ − ℓ, −ℓ]` |
| Finite-level Weil cone | RHTower `WeilPositiveFullUpTo lam A` | weights making Weil's functional of `ζ`'s archimedean datum `≥ 0` on tests in `[−A, A]` |
| Leading coefficient at `k = 0` | `logRadical n` | `∏_{p∣n} log p` |
| Imaginary twist | `imagTwistedForm θ H` | `Q(H cos θ·) + Q(H sin θ·)`: Weil's form of `He^{iθu}` (unitary dimension `iθ`) |
| Archimedean Tate family | `archTate k s` | `𝒢_k(s) = Γ_ℝ(s − k)/Γ_ℝ(s)` |
| Shifted weight | `shiftedWeight ε n` | `Λ(n)(1 + n^ε)`, the von Mangoldt function of `ζ(s)ζ(s−ε)` |
| Centred Tate family, radical | `centredTate k`, `radical n` | `K_k(n) = n^{−k/2}J_k(n)`, coefficients of `ζ(s − k/2)/ζ(s + k/2)`; `rad n = ∏_{p∣n} p` |
| Centred exponent | `centredExponent k` | `c_k(n) = ℓ(n)(n^{k/2} − n^{−k/2}) = 2ℓ(n)sinh(k log n/2)`, `ℓ = Λ/log` |
| Collar potential, fold Doob energy | `foldPotential A ℓ φ H`, `foldDoobEnergy A ℓ φ H` | the two parts of a new fold in the gauge `φ` |

From the corpus: window tests, level, folds (CWS `IsWindowTest`, `windowLevel`); window algebra and
Tate function (WTZ `windowRepFun`, `jordanFun`, `tateFunction`, `genVonMangoldt`, `tateJet`,
`stageForm`); Weil's form and pairing (`weilQuad`, ACS `weilPair`, `realTests`); shifted pair (AIP
`shiftedPairZeroForm`); Lévy form (RHTower `levyEnergy`, `primeSum`, `archLevyDensity`).

## 3. Language

- **Dimension**: the parameter `k` of a Tate family. Three normalizations: *Jordan* (residue-ring
  counts, one-sided, `ζ(s−k)/ζ(s)`), *logarithmic* (finite-field counts `#(𝔸^k∖0)(𝔽_{p^a})/a`), *symmetric*
  (twisted pairing, `Λ(s−k)Λ(s+k)`). Weil's form is the derivative at `0` of the first two and the value
  at `0` of the third.
- **Domination at dimension `k`**: `A_k(H) ≥ 2(τ_H(k) − ‖H‖²)` for an archimedean family `A_k` with
  `A_0 = 0`, `∂_kA_k|₀ = D(H)`. **Descent**: domination near `0` gives `Q ≥ 0`.
- **Structured** archimedean family: a Tate family of the Gamma factor (a tilt or a cocycle), as
  opposed to an arbitrary form with the right 1-jet.
- **Tilt**: reweighting the jump measure by `e^{kt}` (the Esscher transform); symmetrized, `cosh(kt)`.
- **Wall**: `k = 0`, where the Tate family passes from positive values (`k > 0`) to parity-signed
  values (`k < 0`).
- **Hecke similitude**: a window operator `S` with `Q(SH) = λQ(H)` on window tests.
- **Soft / selective**: true for fakes with off-line zeros / fails on them.

## 4. Mechanisms

**A. Criticality.** Positivity of a Z-type jump form is the existence of a positive supersolution
(Allegretto–Piepenbrink); the ground-state representation is an exact identity of unbounded rank.
The pole-free window form is Markov — normal contraction lowers it, `M_N(|g|) ≤ M_N(g)`, and the pole
is the only anti-Markovian term (RHTower `markovForm_abs_le`, `pole_le_pole_abs`) — so its ground state
is a positive (Perron) direction. On the whole line no positive folded supersolution exists (ACT); on
windows existence is open, and the stage step is exact in every gauge (F).

**B. Descent from positive dimension.** If `P_k = A_k − 2(τ_H(k) − ‖H‖²) ≥ 0` on `(0, k₀]`, then
`Q(H) = ∂_kP_k|₀ ≥ 0`. The descent uses only the 1-jet of `A_k`; whatever structure the family has
beyond its 1-jet is where the content must lie.

**C. Reflection and similitude.** Weil's argument over `𝔽_q`: Rosati positivity plus a Frobenius that
is a similitude of the intersection form. On windows `σ_A` is the Rosati involution of the window
algebra and an isometry of `Q`.

**D. Prime-blind existence.** RH holds iff every finite-level cone `C_A` is nonempty (compactness and
uniqueness of the Weil cone, RHTower). The witness at each level may be any weight.

**E. Tilting.** The Tate twist acts on the jump measure `ω(t)dt + Σ Λ(n)n^{−1/2}δ_{log n}` by
`m(dt) ↦ cosh(kt)m(dt)` — archimedean and prime jumps of the same length get the same factor — and on
autocorrelations by `c_H(x) ↦ e^{kx}c_H(x)`. On a window it is conjugation by the exponential gauge
`e^{kM}`; dimension (B) and gauge (A) are one parameter. The tilt moves the zeros of `ζ` to `ρ ± k`.
In imaginary dimension `iθ` the tilt is `cos(θt)`: the unitary twist `n^{−iθ}`, which moves the zeros
along the line and preserves positivity window by window. Positivity lives on the line `Re k = 0` of
complex dimension.

**F. Ground-state representation of a stage.** Each new fold is one collar-to-collar correlation; in
any positive gauge `φ` it splits exactly into the Doob energy of `H/φ` across the fold minus a potential
`φ(u±ℓ)/φ(u)` on the two collars. This is the form in which a supersolution passes a stage.

## 5. Questions and answers

| Question (obstacles §2.7, §2.8) | Answer |
|---|---|
| **§2.8.** Is there an archimedean Tate family `A_k`, `A_0 = 0`, `∂_kA_k|₀ = D`, dominating the counts near `k = 0`? | **As posed, the question is Weil positivity itself.** Domination near `0` gives `Q(H) ≥ 0` (`weilQuad_nonneg_of_dominates`). Conversely the explicit prime-blind family `A_k = kD(H) + 2R_A(k)‖H‖²` (Gamma factor, pole, the integers `n ≤ e^A`; no prime) satisfies `A_k − 2(τ_H(k) − ‖H‖²) ≥ kQ(H)` for all `k ≥ 0` (`mul_weilQuad_le_canonicalArch_sub`), because the Taylor remainder of the counts is prime-blind: `0 ≤ J_k(n) − [n=1] − kΛ(n) ≤ n^k − 1 − k log n` (`jordanTotient_sub_tangent_le`). So a dominating family exists iff `Q(H) ≥ 0`, iff the canonical one dominates in every dimension (`exists_dominating_iff`, `canonicalArch_dominates_iff`; RH ⇔ domination on every window, `riemannHypothesis_iff_canonicalArch_dominates`). The question carries content only for families with imposed Tate structure. |
| How do the higher Taylor coefficients (Bombieri's `Λ_j`) relate to the first? | **They are generated by it.** The Tate family solves a linear flow equation driven by Weil's arithmetic weight, `∂_kJ_k = D J_k + J_k * Λ`, `D = ·log` (`hasDerivAt_jordanTotient`, `tateVelocity_eq`); on a window `U′ = [M, U] + Uρ_A(Λ)` for `U(k) = ρ_A(J_k)` (`windowRep_tateVelocity`). The jets satisfy `ρ_A(Λ_{j+1}) = [M, ρ_A(Λ_j)] + ρ_A(Λ)ρ_A(Λ_j)`, `ρ_A(Λ₂) = [M, ρ_A(Λ)] + ρ_A(Λ)²` (`windowRep_genVonMangoldt_succ`, `windowRep_genVonMangoldt_two`), and every jet operator lies in every algebra containing `M` and `ρ_A(Λ)` (`windowRep_genVonMangoldt_mem`). The sieve-accessible coefficients are noncommutative polynomials in the position and Weil's operator; recovering `ρ_A(Λ)` from them inverts a commutator with `M`, which preserves no sign. |
| What must a dominating family do beyond first order? | On a null test (`Q(H) = 0`) its second jet must pay Selberg's form: `∂²_kA_k|₀ ≥ 2⟨ρ_A(Λ₂)H, H⟩` (`two_mul_selbergPairing_le_of_null`). On null directions the first Taylor coefficient is exhausted and domination becomes a statement about `Λ₂ = Λ log + Λ*Λ`. |
| What positivity of a family of point counts survives `∂_k` at `k = 0`? | **The Tate family changes sign at `k = 0`.** `J_k(n) > 0` for `k > 0` (`jordanTotient_pos`); `(−1)^{ω(n)}J_k(n) > 0` for `k < 0` (`neg_one_pow_mul_jordanTotient_pos`); `J_k(n)` vanishes at `k = 0` to order exactly `ω(n)`, with leading coefficient `∏_{p∣n} log p > 0` (`tendsto_jordanTotient_div_pow`). An integer with `ω(n)` primes enters at order `ω(n)` with the sign `sign(k)^{ω(n)}`; the first jet sees exactly `ω(n) = 1`. The derivative at the wall is the exact form of the parity barrier: a positivity transported from `k > 0` must survive the parity sign that every coefficient with `ω(n) ≥ 2` acquires for `k < 0`. |
| Which normalization of dimension uses the archimedean data? | The symmetric one is the explicit formula of a fake: `Q^{(k)} = ½Ẑ_k`, the zero form of `Λ(s−k)Λ(s+k)` (`tateTwistedForm_eq_half_shiftedPairZeroForm`). It is even in `k` (`tateTwistedForm_neg`), equals `Q` at `0` (`tateTwistedForm_zero`), and **on every window of positive length is negative on some test in every large dimension** (`exists_window_tateTwistedForm_neg`). On windows of length `A ≤ 3/5` it stays positive near `k = 0`: `Q^{(k)}(H) ≥ (1/5000 − 10Ak²)‖H‖²` (`tateTwistedForm_ge_of_window`, from AIP's exact short-window formula and the kernel bound `abs_kernel_le`), so **the critical Tate dimension of a short window lies in `[1/200, ∞)`** (`shortWindow_criticalTateDimension`): a short window does not see zeros moved off the line by less than `1/200` and sees every deep enough shift. |
| What is the archimedean place in dimension `k`? | **The tilted Lévy density `ω(t)cosh(kt)`**, with the prime rate tilted by the same factor `cosh(k log n)` (`tateTwistedForm_eq_tilted`; the Tate twist tilts autocorrelations, `weilTest_tateTwist`). The tilt only amplifies (`archLevyDensity_le_tilted`), is even (`tiltedLevyEnergy_neg`) and is the Lévy energy at `0` (`tiltedLevyEnergy_zero`). It does not change the ratio between the two places at any length, so positive dimension cannot separate the archimedean place from the primes. |
| Is there a Hecke operator on windows commuting with `σ_A` and acting as a similitude of `Q`? | **No, inside the window algebra.** If `Q(ρ_A(f)H) = λQ(H)` on window tests, then `λ = f(1)²` and `f(n) = 0` for `2 ≤ n < e^A` (`windowRep_similitude`); the `Q`-isometries of the window algebra are `±1` (`windowRep_isometry`). Commutation with `σ_A` alone already forces scalars (WTZ `windowRepFun_commutes_reflection_iff_scalar`). The reflection is an isometry outside the algebra (`weilQuad_windowReflection`). A Frobenius for windows must change the window (translations, dilations) or leave the Hecke side, as over `𝔽_q`, where Frobenius is a correspondence on `C × C`, not a Hecke operator. |
| Is the archimedean place positive on the annihilator of `log ℕ`? | RH-equivalent (SRT `primeBlindPositiveOn_iff_…`). Without that restriction it is not: **the Gamma factor and the pole alone fail Weil positivity at a finite aperture** (`not_weilPositiveFull_zero`, `exists_not_weilPositiveFullUpTo_zero`). Below the first prime (`2A < log 2`) the weights are invisible and the finite-level cone is all or nothing, decided by the archimedean place (`weilPositiveFullUpTo_iff_zero`); under RH the archimedean place fails only at `2A ≥ log 2` (`log_two_le_of_not_weilPositiveFullUpTo_zero`). The cones are convex (`convex_setOf_weilPositiveFullUpTo`). |
| Is there an identity across the wall `k = 0`? | **Yes: reflection is Dirichlet inversion.** `J_{−k}(n) = (−1)^{ω(n)}rad(n)^k n^{−2k}J_k(n)` (`jordanTotient_neg`). For the centred family `K_k(n) = n^{−k/2}J_k(n)`, `K_{−k} * K_k = 1` (`centredTate_neg_mul`) and pointwise `K_{−k}(n) = (−1)^{ω(n)}(rad n/n)^kK_k(n)` (`centredTate_neg_apply`); on squarefree `n`, `K_{−k}(n) = μ(n)K_k(n)` (`centredTate_neg_of_squarefree`). Crossing dimension zero inverts the Tate family, and the inversion is diagonal with the Möbius function as its sign. Structurally, `K_k` is the exponential of an **odd** exponent: `c_k(n) = 2ℓ(n)sinh(k log n/2)` (`centredExponent_apply`, `centredExponent_neg`, `centredExponent_nonneg`), and on every window `ρ_A(K_k) = Σ_{j≤L}ρ_A(c_k)^j/j!` (`expTrunc_sub_centredTate_mem`, `windowRep_centredTate_eq_exp`); the wall negates the exponent. |
| Does Tate positivity in positive dimension carry anything to `k = 0`? | **No.** The shifted datum `ζ(s)ζ(s−ε)` is Tate positive in every real dimension `k ≥ 0`, its dimension-zero derivative is `λ_ε = Λ(1 + n^ε)`, and `λ_ε` is not Weil positive with `ζ`'s archimedean datum (`tatePositivity_does_not_descend`). Any descent must use the archimedean data at `k = 0`; selection never happens in positive dimension. |
| Is there a dimension in which positivity is preserved? | **Yes, the imaginary directions.** The twist by `iθ` is Weil's form of `He^{iθu}`, `Q(H cos θ·) + Q(H sin θ·)` (`imagTwistedForm`), modulates the jump measure by `cos(θt)` (`imagTwistedForm_eq_tilted`, `autoCorr_cos_add_autoCorr_sin`) and is nonnegative on every window where `Q` is (`imagTwistedForm_nonneg_of_window`). Real dimension tilts by `cosh(kt)` and fails on every window for large `k`. |
| What is the Gamma factor's counterpart of the point counts? | The archimedean Tate family `𝒢_k(s) = Γ_ℝ(s − k)/Γ_ℝ(s)` is a Tate cocycle (`archTate_zero`, `archTate_add`), and in even dimension it is finite: `𝒢_{2j}(s) = π^j/∏_{i<j}(s/2 − 1 − i)` (`archTate_two_mul`, from the Hensel step `Gammaℝ_eq_mul_Gammaℝ_sub_two`): `j` archimedean points at `s = 2, …, 2j`. |
| Does the structured (completed) archimedean family dominate the counts? | **On the critical line it balances them exactly.** The completed family is the product of the two places, `Λ(s − k)/Λ(s) = 𝒢_k(s)·ζ(s − k)/ζ(s)` (`completedTate_eq_archTate_mul`); in the centred position it is unimodular on the critical line in every real dimension, `‖Λ(½ + it − k/2)/Λ(½ + it + k/2)‖ = 1` (`norm_completedCentredTate_critical`, from `completedRiemannZeta_conj` and `norm_completedRiemannZeta_reflect`), so `‖𝒢_k‖·‖ζ-ratio‖ = 1` there (`norm_archTate_mul_norm_zetaRatio`). Domination by the completed family is the functional equation, an identity without sign; Weil's sign sits in the singular part of the balance (the zeros) and off the line. |
| How does a ground state pass a stage? | **By an exact gauge identity on the collars.** For every weight `φ > 0` continuous on the window, `Q(H) = Q_N(H) − w E_φ(H) + w·(Doob energy of H/φ across the new fold)` (`weilQuad_eq_groundState`; the fold alone: `neg_two_mul_corr_eq`; one correlation per stage: `weilQuad_eq_stageForm_sub_corr`). Positivity crosses the stage as soon as `Q_N` pays the collar potential of some positive weight (`weilQuad_nonneg_of_foldPotential_le`), losslessly on tests whose ratio `H/φ` matches across every new fold (`weilQuad_eq_stageForm_sub_foldPotential`). `φ ≡ 1` is WTZ's transfer identity. Existence of a ground state at every length remains open (§7.1). |
| Unique continuation; zero modes? | **Zero modes are the radical** of a nonnegative window: they pair to zero with every window test (`weilPair_eq_zero_of_zeroMode`), are translation stable (`weilQuad_comp_sub_zeroMode`), and **at a first critical length touch both ends** of the window (`zeroMode_ne_zero_on_left_collar`, `zeroMode_ne_zero_on_right_collar`). At an edge the Tate twists are explicit: `Q^{(k)}(H) = Q(H(cosh k· − 1)) − Q(H sinh k·)` and `Q^{(iθ)}(H) = Q(H(cos θ· − 1)) + Q(H sin θ·)` (`tateTwistedForm_zeroMode`, `imagTwistedForm_zeroMode`); the real twist subtracts the energy of the odd correction that the imaginary twist adds, so it pushes an edge into negativity at second order unless `uH` is itself a zero mode (`tateTwistedForm_zeroMode_le`). A unique-continuation principle for the Euler–Lagrange equation remains open (§7.2). |
| Over `𝔽_q(C)`, which structure supplies each answer? | See §10; the soft theorems above hold verbatim over curves. |

## 6. Tools

**Developed.**
- Jet calculus at `k = 0`: first- and second-order descent for functions vanishing at `0`
  (`nonneg_of_hasDerivAt_of_nonneg`, `nonneg_of_hasDerivAt_deriv`); prime-blind Taylor bounds for the
  Jordan family from `Σ_{d∣n}J_k(d) = n^k` (`sum_divisors_jordanTotient`) and `Σ_{d∣n}Λ(d) = log n`;
  `|c_H(t)| ≤ ‖H‖²` (`abs_corr_le`).
- The Tate twist as tilt: twisted cross-correlation (`weilTest_tateTwist`), Lorentz splitting
  `Q^{(k)} = Q(H cosh) − Q(H sinh)` (`tateTwistedForm_eq`), translation invariance of the twisted
  pairing (`tateTwistedForm_comp_sub`, `weilPair_comp_sub`), `∫(F − F(·+x))² = 2‖F‖² − 2c_F(x)`
  (`integral_sub_shift_sq`).
- Similitude calculus on windows: Weil's form on a plane (`weilQuad_plane`), short bumps of positive
  Weil energy (`exists_short_bump`), shifts of bumps (`windowShift_bumpAt`,
  `windowShift_bumpAt_eq_zero`), the right-end eigenvector (`windowRepFun_rightBump`) and the plane image
  of a Hecke operator (`windowRepFun_plane`).
- Finite-level cones below the first prime (`re_weilFullFunctional_eq_zero_weight`).
- Sign and vanishing order of the Jordan family by multiplicativity (`jordanTotient_pos`,
  `neg_one_pow_mul_jordanTotient_pos`, `tendsto_jordanTotient_div_pow`).
- Locality of the finite-level cone (`weilPositiveFullUpTo_congr`, `weilPositiveFullUpTo_iff_firstFold`).
- Gauge calculus of a fold: the pointwise Doob identity `−2ab = pq(a/p − b/q)² − (q/p)a² − (p/q)b²`
  integrated over the left collar and transported to the right (`neg_two_mul_corr_eq`).
- Gamma ratios: Hensel step and even-dimension product formula (`archTate_two_mul`); global conjugation
  symmetry of `Λ` by the identity theorem (`completedRiemannZeta₀_conj`).
- Radical calculus for nonnegative windows; vanishing on collars from continuity
  (`eq_zero_on_Icc_of_Ioo`).
- The Tate flow equation and the commutator calculus of jets on windows (`windowRep_tateVelocity`,
  `windowRep_genVonMangoldt_succ`).
- Elementary kernel bounds: `ω(t) ≤ e^{3t/2}/(2t)`, `cosh x − 1 ≤ (x²/2)e^{x²/2}`, `|c_F(t)| ≤ ‖F‖²`, and
  the vanishing of autocorrelations beyond the support diameter.

**Used from the corpus.** WTZ (window algebra, Tate function, jets, tangent principle, stage transfer,
reflection centralizer); CWS (window tests, RH ⇔ window positivity); ACT/AIP (shifted-pair
selectivity, `autoCorr`); LST (`weilPair = fullZeroForm`, coercivity on `[−3/10, 3/10]`); ACS (`weilPair`
bilinearity, translation); RHTower (Weil functional, cone uniqueness, finite-level existence, Lévy form).

**To develop.** Ground-state representations of the whole censored window form (not only of the new
fold); unique continuation for the window Euler–Lagrange equation; positive-definite (damped)
modulations in negative dimension; a structured archimedean domination built from `𝒢_k`.

## 7. Open research topics

1. **Ground states on windows (2.6.1).** A positive supersolution of the folded odd-sector process on
   every window, compatible with the stage transfer. The stage step is now exact in every gauge
   (`weilQuad_eq_groundState`): a supersolution `φ` of `Q_N` passes the stage iff its slack pays the
   collar potential `E_φ`. Open: existence of `φ` at every length, and the slack on the collars.
2. **Zero modes.** Under RH no window has a zero mode; at the first critical length of a failure one
   appears, in the radical, touching both ends (§5). Open: a unique-continuation principle for the
   window Euler–Lagrange equation (logarithmic Laplacian plus `Λ`-weighted shifts plus two pole
   constraints) that excludes such radical vectors.
3. **Structured archimedean families.** The bare question collapses (§5), and the completed family
   balances the counts exactly in modulus on the critical line (§5). The open question is a structured
   family that is *not* balanced by the functional equation — one whose excess over the counts at the
   first-fold stage, `A_k(H) ≥ √2(2^k − 1)c_H(log 2)`, is a positive object (a square, a count, a
   supersolution) rather than an identity.
4. **Across the wall.** The arithmetic identity is proved: reflection is Dirichlet inversion with the
   Möbius sign (§5). For `k < 0` the modulation `e^{k|t|}` is positive definite (Schur product with an
   autocorrelation), so under RH Weil's functional is nonnegative on `c_H e^{k|t|}` (zero-side
   positivity; not formalized here), while the counts there carry the parity sign. Open: an
   identity across the wall for Weil's functional itself, transporting positivity of the functional
   at `k < 0` and of the counts at `k > 0` through the inversion.
5. **The second jet on near-null tests.** Domination with a bounded second jet requires Selberg's form
   to be paid on null tests; quantify this on near-null tests (margins are doubly exponentially small).
6. **Function-field dictionary** for each mechanism (§10).

## 8. Pillar theorems

| Theorem | Lean |
|---|---|
| Descent: domination near dimension zero gives Weil positivity | `nonneg_of_hasDerivAt_of_nonneg`, `weilQuad_nonneg_of_dominates` |
| Prime-blind Taylor remainder of the Jordan counts | `sum_divisors_jordanTotient`, `jordanTotient_sub_tangent_le`, `abs_jordanTotient_sub_tangent_le`, `abs_tateFunction_sub_tangent_le` |
| Collapse of the bare domination question | `canonicalArch_zero`, `hasDerivAt_canonicalArch`, `mul_weilQuad_le_canonicalArch_sub`, `canonicalArch_dominates_iff`, `exists_dominating_iff`, `riemannHypothesis_iff_canonicalArch_dominates` |
| Second-jet constraint on null tests | `nonneg_of_hasDerivAt_deriv`, `two_mul_selbergPairing_le_of_null` |
| The Tate twist is the shifted pair | `weilTest_tateTwist`, `tateTwistedForm_eq`, `tateTwistedForm_zero`, `tateTwistedForm_neg`, `tateTwistedForm_comp_sub`, `tateTwistedForm_eq_half_shiftedPairZeroForm` |
| Positivity fails in large symmetric dimension on every window | `exists_window_tateTwistedForm_neg`, `shortWindow_tateTwisted_dichotomy` |
| The Tate family solves a flow equation | `tateVelocity_eq`, `tateJet_one_eq`, `hasDerivAt_jordanTotient`, `windowRep_tateVelocity`, `windowRep_genVonMangoldt_succ`, `windowRep_genVonMangoldt_two`, `windowRep_genVonMangoldt_mem` |
| Short windows stay positive in small symmetric dimension | `archLevyDensity_le`, `cosh_sub_one_le`, `abs_kernel_le`, `abs_autoCorr_le`, `autoCorr_eq_zero_of_lt`, `tateTwistedForm_ge_of_support`, `tateTwistedForm_ge_of_window`, `shortWindow_criticalTateDimension` |
| The Tate twist tilts the jump measure | `integral_sub_shift_sq`, `tateTwistedForm_eq_tilted`, `tiltedLevyEnergy_zero`, `tiltedLevyEnergy_neg`, `archLevyDensity_le_tilted` |
| Hecke similitudes of a window are scalars | `exists_short_bump`, `windowRepFun_rightBump`, `windowRepFun_plane`, `windowRep_similitude`, `windowRep_isometry`, `weilQuad_windowReflection` |
| The archimedean place alone is not Weil positive; cones below the first prime | `not_weilPositiveFull_zero`, `exists_not_weilPositiveFullUpTo_zero`, `re_weilFullFunctional_eq_zero_weight`, `weilPositiveFullUpTo_iff_zero`, `log_two_le_of_not_weilPositiveFullUpTo_zero`, `convex_setOf_weilPositiveFullUpTo` |
| The Tate family changes sign at dimension zero | `jordanTotient_pos`, `neg_one_pow_mul_jordanTotient_pos`, `tendsto_jordanTotient_div_pow`, `logRadical_pos` |
| Tate positivity does not descend | `shiftedDatum_tateFamily_nonneg_real`, `hasDerivAt_shiftedDatum_tateFamily`, `not_weilPositiveFull_shiftedWeight`, `tatePositivity_does_not_descend` |
| The imaginary Tate twist is unitary | `imagTwistedForm_zero`, `autoCorr_cos_add_autoCorr_sin`, `imagTwistedForm_eq_tilted`, `imagTwistedForm_nonneg_of_window` |
| The archimedean Tate family | `archTate_zero`, `archTate_add`, `Gammaℝ_eq_mul_Gammaℝ_sub_two`, `archTate_two`, `archTate_two_mul` |
| The completed Tate family is unimodular on the critical line | `completedRiemannZeta₀_conj`, `completedRiemannZeta_conj`, `norm_completedRiemannZeta_reflect`, `norm_completedCentredTate_critical`, `completedTate_eq_archTate_mul`, `norm_archTate_mul_norm_zetaRatio` |
| Locality of the finite-level cone | `weilPositiveFullUpTo_congr`, `weilPositiveFullUpTo_iff_firstFold` |
| The ground-state representation of a stage | `weilQuad_eq_stageForm_sub_corr`, `corr_eq_intervalIntegral`, `neg_two_mul_corr_eq`, `weilQuad_eq_groundState`, `weilQuad_nonneg_of_foldPotential_le`, `weilQuad_eq_stageForm_sub_foldPotential` |
| Zero modes are the radical | `weilPair_eq_zero_of_zeroMode`, `weilQuad_comp_sub_zeroMode`, `zeroMode_ne_zero_on_left_collar`, `zeroMode_ne_zero_on_right_collar` |
| The Tate twists at an edge | `weilQuad_add_zeroMode`, `tateTwistedForm_zeroMode`, `tateTwistedForm_zeroMode_le`, `imagTwistedForm_zeroMode` |
| The wall is a Dirichlet inversion | `jordanTotient_neg`, `centredTate_eq`, `centredTate_neg_mul`, `centredTate_neg_apply`, `centredTate_neg_of_squarefree` |
| The centred Tate family is an odd exponential | `centredExponent_apply`, `centredExponent_neg`, `centredExponent_nonneg`, `tateTwist_expTrunc`, `expTrunc_sub_centredTate_mem`, `windowRep_centredTate_eq_exp` |

## 9. Traps

| Trap | Truth |
|---|---|
| An archimedean family dominating the counts near `k = 0` would reduce RH to an easier comparison | Bare domination is Weil positivity: the prime-blind family `kD + 2R_A(k)‖·‖²` dominates iff `Q ≥ 0` |
| Positivity in positive dimension can be pushed to `k = 0` | The Jordan family changes sign at `k = 0` (parity for `k < 0`); the symmetric twist is negative on every window for large `k` |
| Every positive dimension already fails on short windows | Short windows are positive for `|k| ≤ 1/200`; failure needs depth beyond a window-dependent critical dimension |
| Positive dimension weights the archimedean place against the primes | The tilt multiplies archimedean and prime jumps of the same length by the same `cosh(kt)` |
| The window algebra contains a Frobenius | Its similitudes of `Q` are scalars; its isometries are `±1` |
| The archimedean place is positive by itself | It fails at a finite aperture; positivity is a balance with the primes (the Weil cone is `{Λ}`) |
| Counts in positive dimension select `ζ` | `ζ(s)ζ(s−ε)` is Tate positive in every real dimension `k ≥ 0` and its weight at `k = 0` is not Weil positive |
| Every complex dimension behaves like the real one | Imaginary dimension is unitary and preserves positivity; only real dimension destroys it |
| The stage step needs the unweighted end mass | Any positive gauge gives an exact representation; the end mass is the gauge `φ ≡ 1` |
| A zero mode can be pushed into a shorter window | At a first critical length a zero mode touches both ends |
| Negative dimension is a new family | It is the inverse of positive dimension: `K_{−k} = K_k^{−1}`, diagonally the Möbius sign on squarefree `n` |
| The completed Tate family supplies the missing archimedean domination | On the critical line it is unimodular in every dimension: the two places balance exactly by the functional equation, and the balance has no sign |
| Finite identities can produce the sign | Refuted at the first prime (CWS); no slack anywhere |

## 10. Place in the research and relation to other programmes

| Programme | Relation |
|---|---|
| WTZ (`WindowTowerOfSpecZ`) | window algebra, Tate families and jets, stage transfer, Rosati centralizer; DZG studies positivity at their dimension-zero point |
| CWS (`CohomologyOfWindowsOfSpecZ`) | one window at a time; RH ⇔ window positivity; curve windows (finite rank, genus saturation) |
| AHD / ADT | the degeneration produces the Tate pieces as conductor counts; DZG shows what of their positivity reaches `k = 0` |
| ACT (`ArithmeticCriticalityTheory`), AIP | whole-line ground states, two-moment no-go; shifted-pair selectivity, which DZG identifies with the Tate twist |
| LST, ACS | coercivity of short windows, Weil's pairing; ACS/AOG: Frobenius graphs and orbit Hodge index |
| RHTower Weil-cone modules | uniqueness and finite-level existence (Mechanism D) |

**Function-field dictionary.** Over a curve datum the window form is a Toeplitz form of power sums of
`2g` Frobenius eigenvalues (CWS): finite rank, genus saturating at `2g`. The Tate twist multiplies the
eigenvalues by `q^{±k}`; the symmetric twist moves them off the unit circle exactly as it moves the
zeros of `ζ` to `ρ ± k`, the imaginary twist rotates them on it. The soft statements of DZG (collapse,
tilt, sign wall `J_k(P^a) = q^{k deg P(a−1)}(q^{k deg P} − 1)`, similitude no-go inside the Hecke algebra)
use only the Euler product and the jump-measure form, and their proofs apply over curves. What `𝔽_q` adds is outside the Hecke side: the Frobenius graph
on `C × C` and Castelnuovo–Severi, i.e. Rosati positivity of the correspondence ring generated by a
geometric Frobenius. Over `ℤ` the window algebra contains no such element; the scaling translations
are `Q`-isometries that move the window, and Rosati positivity of the translation-generated ring is the
orbit Hodge index (AOG), which is RH.

## 11. Success criteria and criteria for contributions

The programme succeeds when each question of §5 has a theorem as answer — an identity, an equivalence
labelled as such, a classification, or a no-go with its strongest positive survivor — and when
positivity at `k = 0` is produced by a structured mechanism or shown to be out of reach of every
mechanism of a named class.

A contribution must:
1. concern the passage to dimension zero, the archimedean place in dimension `k`, the reflection and
   similitudes, ground states on windows, or the prime-blind cone — not re-prove window algebra facts;
2. be exact (identity, equivalence, classification, structural inequality), not an estimate losing a
   factor growing with `A`;
3. say what it does on fakes (shifted products, flip twins, Epstein data, curves);
4. be unconditional; RH-equivalent statements are labelled and count only if they move the problem to
   an object with new structure.

## 12. Big picture

Weil's window form is the derivative at `k = 0` of the Tate family of a window, and DZG is the
geometry of that point. In complex dimension `k + iθ` the twist acts on the jump measure of the window
by `cosh(kt)` and `cos(θt)`, the same factor for archimedean and prime jumps of the same length.
Imaginary dimension is unitary: it moves the zeros along the line and preserves positivity window by
window. Real dimension is the depth of a fake: it moves the zeros to `ρ ± k` and destroys positivity on
every window once `k` passes the window's critical Tate dimension, which on short windows is at least
`1/200`. Uniformly in the window, positivity lives only on the line `Re k = 0`.

On the arithmetic side the Jordan counts are positive for `k > 0` and carry the parity `(−1)^{ω(n)}`
for `k < 0`. The wall between the two regimes is a Dirichlet inversion: the centred family is the
exponential of an odd exponent, and on squarefree `n` it is reflected by `μ(n)`. Weil's arithmetic term
is the first jet at the wall, which sees only the primes.

Every route through positive dimension collapses at `k = 0`:
- Bare domination of the counts by an archimedean family is Weil positivity itself, realized by an
  explicit prime-blind family.
- Tate positivity in every positive dimension holds for fakes whose weight fails Weil positivity.
- The window algebra contains no Frobenius: its similitudes are scalars.
- The archimedean place alone is not positive.
- The completed family balances the two places exactly on the critical line, unimodular in every
  dimension, with no sign.

What remains is positivity at `k = 0` produced by a structure that sees the archimedean place and the
primes at once. A ground state of the window process does this, and DZG makes its passage across each
stage exact. A structured archimedean Tate family, of which the Gamma ratios are the cocycle, would also
do it. Both are open and are where the programme points.

