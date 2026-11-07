# Review 0711 — consolidated research report (Fable)

Status report on the RH programme of this repository at checkpoint `a4fb22e174`. Sources: the five
ledgers named in the task (`rh-current-frontier-map.md`, `rh-killed-routes.md`,
`review-0711/route-unification-ledger.md`, `review-0711/route-obstacles.md`,
`review-0711/walls-ledger.md`), the programme READMEs listed in `docs/reports/research-programmes.md`
(read oldest to newest), and the Lean corpus itself through `scripts/formal_tools.py research`, with
every cited declaration's statement read. Working notes are in `logs/fable-review-0711-research.md`.
Nothing here was compiled or audited; the report interprets the mathematics as the corpus states it.

Conventions. `Q`, `W` is Weil's quadratic form on tests; `W_{φ,c,N}` the complete Weil matrix on
atoms of width `c/N` at `log n`, `n ≤ N`, with overlap `c`; `R = c⁸/log N` the critical ratio of the
tilted spline (tail exponent `β = 7`); `κ = κ(K_ζ)` the Krein–Langer index (number of distinct zeros
right of the line); `Θ = zetaZeroAbscissa`; `ZAL` the zero abscissa law (finitely many zeros deeper
than every positive depth); `AAL` the asymptotic abscissa law (`Θ∞ = Θ`, where `Θ∞` is the infimum of
the abscissae right of which only finitely many zeros lie); `qRH` a zero-free strip `Re s > 1 − δ`;
`L = log T`, `ℓ = log L`. Programme abbreviations are those of the READMEs (ACS, HWV, ADT, AHD, CWS,
WTZ, GWZ, SWC, FADF, CHT, ZCG, NGF, APR, AAD, RAC, PTT, TAPO, SPL, AIF, ASH, …); a glossary is in §9.

---

## 1. Big picture: what the corpus has established, what it has solved, what still stands

### 1.1 One scalar, many coordinates

The corpus has reduced RH to the vanishing of a single quantity and proved that quantity equal, as a
theorem, to the following readings. Each line is an unconditional equivalence in Lean.

| Coordinate | Statement equivalent to RH | Where |
|---|---|---|
| Krein–Langer index | `κ(K_ζ) = 0`; `κ` = number of distinct right zeros, even; finite `κ` ⇔ finitely many off-line zeros ⇔ all zeros above some height on the line, and finite `κ` ⇒ Lindelöf | HKT `zetaKernel_finiteIndex_tfae`, `lindelof_of_negIndex_zetaKernel_lt_top` |
| Onset aperture | `a*(ζ) = ⊤`: Weil's form nonnegative on every window `[−a, a]`; off RH `a*(ζ)` is the contact aperture, and positivity holds at it | WVL `riemannHypothesis_iff_onsetAperture_zeta_eq_top` |
| Best margin | `λ*(c) → 0`: the inradius of the window cone `𝒜(c) = {λ : W_λ ≥ 0 on [−c,c]}` tends to zero; `⋂_c 𝒜(c) = {Λ}` under RH and empty otherwise | CHT `riemannHypothesis_iff_tendsto_bestMargin` |
| Critical curve | positivity of the conductor Gram of the complete Weil family at every multiple `c = 2K(log N)^{1/8}` | HWV `riemannHypothesis_iff_conductorGram_nonneg_eighthRoot` |
| Coupling | bounded coupling `C(u,v) = K(uv) − K(u) − K(v) + K(1)` on one two-prime lattice `⟨p⟩ × ⟨q⟩`, all `a, b ∈ ℤ`; zero width `≤ σ` ⇔ coupling grows at most `e^{σ·height}` | ACoT `riemannHypothesis_iff_exists_bound_coupling_zpow`, `zetaZeroWidth_le_iff_coupling_rate` |
| Window tower | every growth step `A ↦ A + ε` is a translation contraction `W(τ_εu, v)² ≤ W(u)W(v)` | CSW `riemannHypothesis_iff_translation_contraction` |
| Lattice canonical system | every Levinson margin of every bump at every step is positive; no lattice ever degenerates into a curve; the two-site band `|c_φ(t)| < Q(φ)` for every bump and `t ≠ 0` | GWZ `riemannHypothesis_iff_levinsonErr_pos`, `riemannHypothesis_iff_no_degenerate_lattice`, `riemannHypothesis_iff_abs_weilOrbitCorr_lt` |
| Canonical system of the de Branges chain | `Ψ` locally bounded to contact; no finite contact | CSW, RW |
| Inner field | `I(w₀) = 0` at one point; equivalently a mollifier family with Szegő budget `→ 1`; equivalently zero surplus `I(1) − I_δ(1)` at a single shift `δ ∈ (0, ½)` | AIF `riemannHypothesis_iff_innerField_eq_zero`, `riemannHypothesis_iff_exists_budget_lt`, `riemannHypothesis_iff_log_dilation_quotient_eq` |
| Window index / horizon pencil | window index `ind₋(P_K) = 0` for all families and multiples | AHD `riemannHypothesis_iff_windowIndex_eq_zero` |
| Count | a naive height (nonnegative function at bounded distance from the Rosati form) exists on every scaling cycle | AET `riemannHypothesis_iff_forall_exists_naiveHeight` |
| Same-point form | Weil's form equals the collided form `D = Σ m_ρ|f̂(ρ)|²`; horizontal collision charge `< 2` at every height | APol/HEF, RHTower `riemannHypothesis_iff_forall_horizontalCollisionCharge_lt_two` |
| Frobenius at infinity | the defect involution `ρ ↦ 1 − ρ̄` fixes every zero; the collided form is translation invariant | EHT `frobeniusAtInfinity_iff` |
| Heat | `Λ_X = 0` at every height; every heat zero simple for `t > 0` | ZCG, RHTower |
| Parity | `L(x) = Σ_{n ≤ x} λ(n) ≪ x^{½+ε}`; more generally the parity exponent equals the zero abscissa | RAC `riemannHypothesis_iff_liouville_power`, `zeroFree_iff_liouville_power` |
| Production | integer stencils of rate `K^{−a}` for every `a < ½` | AAD `riemannHypothesis_of_hasRate` |
| Hull | the Liouville fibre `ζ(2s)/ζ(s)` of the gauge torus extends holomorphically to `Re s > ½` | PTT `riemannHypothesis_iff_liouvilleFibre_extends` |
| Integer probes | the Krein square of integer probes is nonnegative | ASH `riemannHypothesis_iff_integerProbes` |
| Split | RH ⇔ ZAL ∧ AAL | RHTower `riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw` |

The unification ledger's reading is confirmed by the corpus: all these meet at one inequality, the
arithmetic Hardy inequality `P ≤ H` on every window (prime part dominated by the archimedean–polar
part), which is the two-site band `|𝒞_m(f)| ≤ W(f)` on reflection pairs, which is nonnegativity of one
quadratic form on integer probes. The ledgers' sentence holds: equivalence through RH transfers truth,
not mechanism. No coordinate above comes with a mechanism that produces its own sign.

### 1.2 The three walls, and where they stand

The walls ledger's families are the right taxonomy and the corpus confirms their content.

**Σ (sign).** The critical sign of the window form, equivalently of the complete family at the
critical curve. What is proved: positivity on the whole space for every `c ≤ (log N)^α`, `α < 1/8`
(CACT `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_eighth`) and at one fixed
small multiple of the critical curve, `1 ≤ c ≤ 2K₁(log N)^{1/8}`
(`exists_tiltedUnitSpline_completeWeilMatrix_posDef_at_critical_multiple`); on windows, positivity up
to total length `181/250` (GWZ `weilQuad_pos_of_short`), on the cosh hyperplane up to `log 2 + 1/50`,
hence window index at most one there (CWS, AHD). What is open: the sign at every multiple `K`. The
corpus has turned the exponent question into a constant question: at `c⁸ ≍ K log N` the horizon layer
has the exact limit `κ_φ Q(H) + (7J(1)/K)‖H‖²_{−8}` (AHD `horizon_layer_criticalCurve_exact`), so
positivity at one multiple `K` is the sub-RH inequality `κQ(H) ≥ −7J(1)‖H‖²_{−8}/K` on horizon windows
and positivity at all multiples is `Q(H) ≥ 0`, Weil positivity on windows. Negative directions at the
critical ratio must meet the top logarithmic window of length `(1/8) log R + O(1)` (CACT
`eventually_nonpos_completeWeilEnergy_not_escape_log_window`) and, on packets, sit in a finite
conductor sector (ACoT); what carries the sign there is the non-ratio successor–dilation part
`½A_N − Σ d_n F(n)²` (ACoT), i.e. the top coprime stratum, which holds every successor pair `(n, n+1)`
(HWV `successor_coprime`).

**Π (precision).** The production of a count at square-root precision. What is proved: every classical
tool has an exact limit. Type I and Type II information are parity-blind, the corrected Liouville twin
`λΛ + 2` shares every error law with `Λ`, finite systems of convergent linear laws have stabilizers
outside the square-root class, mollifiers need length `log N ≥ log²T/(6K₀)` for an excess `K₀/log T`
(APR); integer stencils have rate exactly the Mertens level, and polynomial rates are zero-free strips
(AAD `hasRate_exp_iff_mertens`, `exists_hasRate_rpow_iff`); every unconditional saving in the corpus
sits at Vinogradov–Korobov (`exists_vk_zero_free_region_abs`, surrogate width
`log^{−5/7}T/10¹²`). What is open: the deciding input, a provable statement whose stabilizer lies in
the square-root class; equivalently an upper bound for a long mollified second moment at
superpolynomial length (APR §6). The corpus's structural reduction of this wall is new: the near-line
wall, the necessary mollifier length and the first scale of absolute non-alignment of the prime phases
are one scale, `(log t)²`, and the whole difficulty lives in the **dark range**
`log t ≲ y ≲ exp((log t)^{2/3})` of the prime orbit (TAPO, PTT, S5/S11 of the obstacles ledger).

**Γ (selection and reflection).** What identifies the reflection pairing `ρ ↔ 1 − ρ` with the
conjugation pairing `ρ ↔ ρ̄`, and what selects `ζ` among its fakes. What is proved: every soft law
(theta polarization, convexity of counts, KMS positivity, Hecke positivity, flux, unitarity,
functional equation at genus one, Tate positivity in positive dimension) holds on explicit fakes
(golden curve, Epstein lattices beyond `e²`, prime flips, Liouville twin, `ζ(s)ζ(s−ε)`, tree-lattice
black holes, bounded-count Beurling model); selection happens only at the pole hyperplane (margin
`2 log 2`), through the unit gap of ℤ (the successor), along the whole window tower (lattice
selection of `Λ`, GWZ `lattice_selects_vonMangoldt`), and in the exactness of the count
(`nonempty_label_equiv_primes`). What is open: a construction of the reflection (Frobenius at
infinity exists iff RH, EHT), a non-holomorphic identity reaching the same-point side (HEF), and the
count whose quadratic law is the parallelogram law on integer probes (ASH, Γ97).

The two gaps every route meets, named in the unification ledger, are exactly what the corpus
searches confirm: the **dark range** of the prime orbit, and the **missing count** (a nonnegative
arithmetic function at bounded distance from `Q`, which Manin's height supplies on a curve and nothing
supplies over ℤ).

### 1.3 Hard obstacles that have been solved

These are the obstacles that stood between the classical state of the art and the present
formulation. Each is a Lean theorem or a closed family of theorems.

1. **The divergences of the explicit formula.** The renormalized prime form has a clean spectrum
   (energies `log m + tameDifferent(m)` on Ramanujan packets, the pole as ground state); the
   archimedean place pays the prime channel down to the atom spacing; the literal complete Weil
   matrix is positive at every fixed overlap (RAPT). The Metzler wall at `c = 1` is crossed by an
   explicit margin without any gauge (TM), the Liouville twin and every pole-free sign gauge failing
   above `c_RE < ½`.

2. **The universal regime and its edge.** Positive definiteness of the whole complete family below
   `(log N)^{1/8}` and at one small multiple of the critical curve (CACT); the inheritance radius of
   the rescaled Jordan-totient limit is exactly the RH exponent `1/(β+1) = 1/8` (ADT
   `inheritance_radius`); the obstruction at the edge is logical, not technical: a positivity proved
   without zero information holds for data with off-line zeros and cannot cross their edge, and only
   identities, inherited polarizations and integer invariants are edge-valid (EHT).

3. **The second order of the degeneration.** At the critical curve the complete form on a horizon
   window converges to Weil's form of the synthesized test plus the dilation derivative of the
   first-order point count, `κ_φQ(H) + (βJ/K)‖H‖²_{−(β+1)}`; every twisted window (Ramanujan sums,
   characters, frequencies) carries exactly a count (Jordan totient `φ(m)#ℙ⁷(ℤ/m)`, Hurwitz forms) and
   sees no zero; the second-order Gram is block-diagonal by conductor, Weil's form living only on
   the conductor-one block (AHD). The sign of RH is thereby located at the pole of a count.

4. **The anatomy of a window.** Weil's form on `[−A, 0]` is an exact finite arithmetic object:
   archimedean jumps, one fold per active prime power (antisymmetric count minus symmetric mass), a
   canonical class `ψ_{1/2}(e^{−u}) + ψ_{1/2}(e^{A+u})` concentrated at the ends, and the pole plane
   (CWS). The window algebra is the Dirichlet ring truncated at the level; Weil's form is the 1-jet
   at dimension zero of the Tate function whose values at positive integers are point counts of
   punctured affine space over `ℤ/m` (WTZ `weilQuad_eq_tateJet`, `weilQuad_eq_signedCount`). Window
   positivity is decided by positivity on all finite rational Hecke configurations
   (`windowForm_nonneg_iff_rationalHeckePositive`). Growth is one mixed pairing per step (CSW), and
   on lattices it is an exact Schur–Levinson canonical system whose degenerate windows are windows
   of curves over `𝔽_q` (GWZ `degenerate_window_is_curve`).

5. **Signed criticality.** The parity split of the pole, the frustration loci (prime anti-diagonals
   in the odd sector, the pole at long range in the even sector), the death of the Markov part at
   width `e^{−3/4}`, the pole-charged ground-state representation, the collar Hankel form of the
   growth step as "one pole square against the trivial-zero squares minus the smoothed prime count",
   the causal (outer) certificate replacing a positive ground state, and the jet Hankel system as a
   moment problem of the parity sectors (SWC, FADF, AIF). Unconditional base: `181/250`.

6. **The index dichotomy.** For tower data the index is `0` or `∞`; the archimedean gluing formula
   `κ(K(|a|) − c|a|^{−1/2}|b|) = κ^{(½)}(K) + 1`; the pole–successor state as the substitute for
   conformal Frobenius; finite index implies Lindelöf and eventually-on-line (AKG, HKT, RIT).

7. **The structure of ¬AAL.** `¬AAL` ⇔ the prime error is a finite oscillation,
   `ψ(x) − x = x^Θ T(log x) + O(x^{Θ−η})` with `T` a nonzero finite trigonometric polynomial ⇔ two-prime
   dilation annihilation ⇔ a finite isolated top layer of zeros attaining `Θ` (ZCG
   `not_asymptoticAbscissaLaw_iff_primeErrorIsFiniteOscillation`,
   `not_asymptoticAbscissaLaw_iff_twoPrime_dilationAnnihilation`); in particular `¬AAL` forces a
   strip `Re s > σ`, `σ < 1`, with only finitely many zeros (the ledgers' `qRH ∨ AAL`).

8. **The heat route to its floor.** `H_t` is real and simple near height `X` for
   `t ≥ (6600/9991 + ε)/log X` (sub-Weyl); below `½/log X` the Gaussian saddle enters the strip and the
   pair model has collided, so the band carries no zero information; `Λ ≥ 0` (Rodgers–Tao) is in Lean
   (`newmanConstant_nonneg`), so the descent cannot pass `t = 0` (ZCG, NGF). The camera
   (identification) is complete and sign-free and is proved to close nothing alone.

9. **Production limits.** Exact necessary mollifier lengths, exact filters, parity resolved as pole
   parity, the stencil rate as the Mertens level, the exponent gap `[1/4, 1/2]` under RH, LP duality
   with fake prime measures (APR, AAD, ASRP, AKL).

10. **The prime orbit at finite time.** Effective Kronecker for half-spaces and boxes with no Baker
    input (resonators); absolute non-alignment past the Kronecker scale (`L^{−8}ℓ^{−4}` on all
    primes, a power of `T` at the top of the column); lacunarity of the prime characters, so the
    critical line is a natural boundary for Haar-almost every fibre and almost every order-two point
    extends zero-free, while the Liouville point extends iff RH; the first return as the extreme
    value of `ζ(1 + 1/log N + it)`; the tail carries the zero at every cut, and every return at a zero
    is tail-bad (PTT, TAPO, RAC).

11. **Census.** Simple critical proportion `≥ 0.67250071` (IGP); `3/4` reduced to the signed
    coalescent surplus `≤ N/18` at bandwidth `4/3` (TTPC, ACS); the dichotomy "`70%` critical or `≥
    (HD(1) − 2/5 − 1/A)N` simple off-line zeros within `A/log T`" (RHTower
    `seventy_percent_or_simple_offLine_near_line`).

12. **Calibration.** Over `𝔽_q` the corpus reproduces Weil (Hodge index on the span), Stepanov
    (hyperelliptic of every genus), Hasse from the count law without Stepanov (ASH
    `elliptic_has_countLaw`, `hasse_of_countLaw`), the curve chain of Schur parameters, and the
    identification threshold `g log q` of the camera. The fakes battery is complete enough that every
    new mechanism can be tested.

13. **The physical door.** Flux, unitarity, causality, commuting positive Hecke at every degree and
    class, and the functional equation at genus two do not force universal damping; what survives is
    the Krein square (= degree form = half the Castelnuovo–Severi defect) and the count law (ASH).

### 1.4 Hard obstacles still standing, with their sharp boundary

1. **The constant at the critical curve (Σ).** Proved: one `K₁`. RH: all `K`. The gap is Weil
   positivity on windows of every length. HWV: "what is left is not an exponent but a constant", and
   the constant is the exact leading term of the bilinear residual, of order `c/log N`, against the
   margin constant `κ₀`, whose arithmetic sources are the Mertens remainders at shifted horizons, the
   archimedean cross errors and the shift distribution of the coprime shells.

2. **The growth step (Σ).** Past `181/250`, one inequality per stage with no slack: the mixed pairing
   with premises on the shorter window; on reflection sectors
   `2W(x_L + y) − W(y) ± 2𝒞_m(x_L) ≥ 0`, where `𝒞_m` is the collar Hankel form minus the smoothed prime
   count of the collar piece. The odd unit window reads exactly one arithmetic number `w₂ = log 2/√2`,
   convexly, with margin about `2·10⁻⁴` (SWC `odd_unit_nonneg_iff`); the first-prime even sector is the
   other bounded instance. The collar light cone pays the anti-diagonal of `n` at ratio
   `2Λ(n)n^{−1/2}e^h`, below `1` for `2` and above `1` for `3 ≤ p ≤ 73`: those primes cannot pay their
   own frustration inside their collar.

3. **The count (Π ∩ Γ).** Every count built from the base is bidegree-blind; definite counts are
   fakes; a realization of the window `h¹` exists iff RH and is never finite-dimensional; no identity
   "jump count + fold data + finitely many squares" exists at the first prime (CWS
   `not_exists_countIdentity`); the integrality of the Nair lattice gives exactly Chebyshev; over
   `𝔽_q` the primitive `h¹` is a kernel count and over ℤ it is half of Weil's form, quadratic but not
   known to be a count. The sharpest reformulations: a naive height on correspondences at bounded
   distance from the Rosati form; a count equal to the Krein square on integer probes; a quadratic
   (signature-type) invariant of the nerve refining the Mertens function; Stepanov's twist `x ↦ x^q`
   over ℤ, i.e. an operation making vanishing along prime progressions cheap.

4. **The deciding input (Π).** A provable statement `S`, not defined through `Λ`, with `S(Λ)` true and
   `S(a) ∧ S(a + δ) ⇒ δ ∈ 𝒬`; or a long mollified second moment bound at superpolynomial length. The
   corpus has a bounded mollified second moment at `θ = 21/50` near the line and the exact necessary
   lengths; nothing crosses VK.

5. **The dark range (Π).** Between the Kronecker scale `≈ log t` (where conditional laws stop) and
   the VK length: the constant-precision first-return exponent (VK would give `3/2`), the tail law
   past the Kronecker scale, the heavy first return at the size curve `y = L²/16` at weights
   `p^{−½}` (B46), and the required saving `εL/ℓ` against the proved `L^{−8}ℓ^{−4}`.

6. **AAL (Γ).** A bounded return at a right zero (B89), or a slow aligned return with a polynomial
   bound on `ζ` on a disc right of the line (AAD `asymptoticAbscissaLaw_of_slowReturns_right`), or a
   contradiction in the rigid object `¬AAL`. See §5.

7. **Reality inside near-coincidence clusters (B44) and a Hermite–Biehler half of the heat source
   below `½/log X` (B49).** Both are square-root cancellation of the Euler product at the scale of
   the mean spacing (ZCG).

8. **Reflection = conjugation (Γ).** No construction; every known involution (window involution,
   collar reflection, Serre duality as Rosati, KMS midpoint) is an isometry on every datum. The
   same-point side needs a non-holomorphic identity (HEF): the resolvent identity
   `(σ − ½)S − Re ξ′/ξ = D ≥ 0` on `Re s > 1` is the only same-point identity with a prime side, and
   its control near `½` is open.

### 1.5 The picture in one paragraph

Every positivity the corpus can prove is either universal (true for every twist, every datum of a
family, every zero configuration) or exactly RH; the proved universal regime ends at a sharp edge for
a logical reason, and past the edge only identities, inherited polarizations and integer invariants
can be stated. Every precision the corpus can prove is at the Vinogradov–Korobov scale, and every
saving anywhere on the width axis would be a zero-free strip. Every selection the corpus can prove is
a margin on a partial form at a specific place: the pole hyperplane, the prime two, the unit gap of ℤ,
the whole tower. The sign of RH has been located to one place, the additive–multiplicative coupling
of the integers (successor pairs in the top coprime stratum; the non-ratio successor–dilation part of
the complete form; the collar Hankel form minus the smoothed prime count of one collar piece), and
the precision of RH to one range, the dark range of the prime orbit between `log t` and
`exp((log t)^{2/3})`. The two meet at the missing count: the quantity that is a degree on a curve and
a quadratic form on ℤ.

---

## 2. Opportunities to overcome or partially solve the obstacles

I list the opportunities the corpus itself exposes, with what each would deliver and what it would
not. None is a route to RH by itself; each moves a named boundary.

**2.1 The constant at the critical curve, via the exact second order of the bulk.** AHD computes the
horizon layer exactly and the twisted sectors exactly, and shows the second-order Gram is
block-diagonal by conductor. The remaining term is the bulk second order at the critical curve
(constants `γ`, `γ₁`, logarithms of divisors; at the pole `2γ₁ + γ²`) together with the cross between
the pole packet and the horizon layer. If the complete second-order Gram at `c⁸ = K log N` is the
pencil `κW(H) + (βJ/K)A(H)` on the horizon block plus the Jordan form plus `Kκ(2 + γ − log 4π)` at the
pole, with no cross term, then positivity at multiple `K` on the whole space is exactly positivity of
the pencil on horizon windows of every length. That would complete the reduction of the atomic
frontier (routes RW, HF, SRT, AIP, ACS, SC) to the window problem with an explicit dictionary between
`K` and the window length. It would not produce the sign.

**2.2 Window positivity stage by stage as a finite problem.** WTZ proves that window positivity at
length `A` is equivalent to positivity on all finite rational Hecke configurations of spread below
`A`, and computes exact Tate horizons at stages one to four from finite graphs. GWZ gives the exact
lattice stage criterion `|β_n| < E_n`. CSW gives the frozen two-collar form in closed form at the
first two stages. SWC reduces the odd unit window to a half-window inequality with one arithmetic
number. The opportunity is to certify the first-prime stage completely (odd and even sectors,
through `log 3`), then stage two with the `T₂` transports, by finite rational graph computations
whose infinite components (ratio six) are handled by the Følner argument already in Lean. Each
certified length `A` transfers through WVL and SRT into explicit depth bounds for low heights
(`|β − ½| < 10⁶ exp(−a/(1200 log(|γ| + 3)))` at level `a`). This does not approach RH (every finite
aperture is consistent with every zero width, Σ82), but it would be the first signed, pole-charged
certificate past the Markov death, and it would show whether the signed-criticality engine
(pole-charged gauges, causal predictors, collar Hankel forms) is an engine or a reformulation.

**2.3 The AAL half.** See §5. The point here is that it is the only half of RH whose negation is a
single rigid object with a power-saving error term, so it is the only place where the corpus can
assume more than it knows about the zeros while refuting a hypothesis.

**2.4 Seventy percent through the dichotomy.** See §4. Two concrete targets: a one-sided bound on
the signed coalescent surplus (`≤ 19N/180` at bandwidth `4/3`), or a depth-sensitive near-line count
excluding `0.27N` simple zeros at depth below `A/log T`.

**2.5 The dark range by combining the two non-alignment mechanisms.** PTT has words (polylogarithmic
precision at `y ≍ L²ℓ`, but using every small prime) and pigeonhole (any set of primes, precision a
power of `T`). The next theorem the field names is polylogarithmic precision on a positive proportion
of the top of the column. TAPO adds the head–tail decoupling: below the Kronecker scale the tail is
Gaussian conditionally on any head. A conditional tail law at one moment past the Kronecker scale
(tilted resonators with budget `Σ f_p² log p ≲ log T`) is the first statement in the dark range that
is not a reformulation. It would still fall short of the required saving `εL/ℓ` unless the precision
becomes macroscopic.

**2.6 The count on integer probes.** ASH proves the count law (parallelogram law for `#ℤ[π]/(y − xπ)`
over probes) on a true curve from the addition law and derives Hasse from it; over ℤ the quadratic law
holds (`integerProbe_parallelogram`) and the count is unknown. HWV identifies the nerve of the star
cover, whose Euler characteristic is the Mertens function, and asks for a signature-type invariant of
the stratified forms over the nerve. LST isolates the primitive `h¹` on prime-free cycles as a jump
count. A quadratic invariant of the nerve, or a kernel count for the degree of a correspondence of
`Spec ℤ`, is the one structural object whose discovery would be a mechanism and not a reformulation.
There is no proposed construction; the opportunity is that the target is now exact (criteria in LST
§11, CWS §11, AHD §13).

**2.7 Charge accounting on the complete family.** CSAR shows that energy limits erase receiving
charges the complete form still pays (constant output `P_M(a)` surviving vanishing adjunction energy;
derivation law across coprime conductors). SWC asks which term of the complete decomposition (jump
energy, half affine Dirichlet energy, Mertens–Euler diagonal, minus shell degree, centre, cross,
pole-error, overlap) pays them. A term-by-term computation on the harmonic-pole-neutral prime-charge
families at `c ≍ (log N)^{1/8}` is finite and would either locate the sign carrier in the complete
form or show cancellation.

---

## 3. Is there a clear path to quasi-RH?

No. The corpus has made this answer sharp rather than vague.

1. **The width axis.** Every route has a parameter whose interior value is a zero-free strip: the
   stencil rate (`K^{−a}` ⇔ zero-free strip, AAD `exists_hasRate_rpow_iff_mertens`), the parity
   exponent (`L(x) ≪ x^a` ⇔ no zero right of `a`, RAC), the coupling rate (ACoT), the growth rate of
   the spline orbit (AOG), the mollifier defect (APR), the inner-field decay, the negativity exponent
   of windows (WTZ: between the zero width and `½`), the heat time of collisions. These are
   equivalences; they transfer truth, not mechanism.

2. **Every unconditional saving sits at VK.** `exists_vk_zero_free_region_abs`, the surrogate width
   `log^{−5/7}T/10¹²`, the stencil rate `exp(−(log K)^α)`, `α < 3/5`, the Mertens level: wherever the
   corpus measures its own precision, the number is Vinogradov–Korobov's.

3. **Where a saving would have to come from.** The dark range: a proportional saving of the prime
   column at length `L^{2K}`, `K > 1`, at weights `p^{−½}` is "quasi-RH strength up to crystal
   shielding" (PTT), and is exactly the absence of heavy first returns (TAPO
   `saving_of_no_heavy_return`). Equivalently, exponential sums for `t log(n + h)` where the Taylor
   degree exceeds `(log length)²` (SPL). This is the classical VK barrier, restated with exact
   thresholds and with the integer structure (unique factorization, Tarry–Escott words, winding
   numbers) identified as the only available input.

4. **Eventual quasi-RH from mollifiers.** A dyadic bound `∫_T^{2T}|ζM|² ≤ CT` with prefix cancellation
   through `T^{θ₁}`, `θ₁ > ½`, gives finitely many zeros deeper than `1/(2θ₁) + ε` (CDG
   `finite_offLineZeros_beyond_of_dyadic_long_mollifier`); a cofinal bound at arbitrarily large
   length exponents gives RH. The necessary-length laws say such a bound needs superpolynomial length
   for any excess tending to zero, and the Euler mollifier over primes up to `c log²T` is the shape
   forced. No upper bound beyond `θ = 21/50` exists in the corpus.

5. **What quasi-RH would not do.** Quasi-RH alone leaves AAL open and RH untouched; conversely
   `¬AAL` already contains a strip right of some `σ < 1` with only finitely many zeros, so AAL is not
   weaker than quasi-RH in any proved sense.

The honest statement: the corpus has no mechanism beyond VK and has proved that none of its
positivity, count, index, torus, heat or production tools supplies one. The only new ingredient it
offers for quasi-RH is the sum–product/winding structure of `t log n` (SPL), which is at the stage of
foundational identities, with the known real-set counterexamples (Roche-Newton–Schildkraut–Warren)
marking what cannot work without integer input.

---

## 4. Is there a clear path to at least 70% of the zeros on the line?

**Where it stands.** Unconditionally, simple critical zeros are at least a proportion
`0.67250071 − ε` cumulatively and dyadically (IGP `simple_critical_proportion_ge_67250071`,
`beyond_HD_one_simple_critical_dyadic`), slightly above `HD(1) = 3/2 − cot(1/√2)/√2 = 0.6725007…`,
obtained from the multiplicity census with Montgomery's pair-correlation bandwidth and a Gram pinching
of the Montgomery–Taylor window.

**What 70% is, exactly.** `seventy_percent_or_simple_offLine_near_line` (source read): for every
`A > 0` and `ε > 0`, eventually either `7/10 · N(T, 2T) ≤ N₀(T, 2T)`, or at least
`(HD(1) − 2/5 − 1/A − ε) N(T, 2T)` zeros in `[T, 2T]` are simple, off the line, and within distance
`A/log T` of it. The proof is the census `S + 2M ≤ (1 − HD(1) + ε)N` with `N = N₀ + S + M` and the far
mass removal `N/A`. So the failure of 70% forces about `27%` of all zeros to be simple and off the line
at depth below the mean spacing. The general form `critical_proportion_or_simple_offLine_near_line θ`
shows the census alone excludes failure of any proportion `θ > (1 + HD(1))/2 ≈ 0.836`; between
`0.6725` and `0.836` the census is silent.

**Why there is no clear path.** The alternative to 70% is a statement about zeros at depth `< A/log T`,
where every density and pair-correlation input is blind: SCPE proves pair-correlation and density
inputs see ordinates, not depths, and a zero at depth `1/log T` and one on the line look alike. The
sub-mean-spacing near-line regime is exactly where `D_zero` and `D_win` live (CDG), and those are
reached only by detectors at scale `V/log V` or mollifiers of superpolynomial length (APR Q2), both
open.

**The two concrete targets.**
1. *Signed coalescent surplus.* `zeta_N0star_and_offLineMoment_of_coalescentSurplus`: if the signed
   coalescent surplus (odd primes at even shifts in multiplicative windows `|log(n/m)| ≤ T^{−1+η}`) is
   at most `βN`, then `N₀* ≥ (29/36 − β − ε)N`. For 70% one needs `β ≤ 19/180 ≈ 0.106`; for 3/4,
   `β ≤ 1/18`. The expected value is negative (`−1/144` from Hardy–Littlewood/GUE), so a weak one-sided
   bound suffices. Unsigned sieves cannot do it (TTPC: they need `Υ ≤ 8/9`); the input is a signed
   Hardy–Littlewood-type correlation of primes at even shifts in short multiplicative windows. This is
   beyond current technology but is a single, well-posed analytic statement with explicit constants.
2. *Depth-sensitive near-line count.* Exclude `0.27N` simple off-line zeros at depth below `A/log T`.
   Any near-line density theorem at sub-mean-spacing depth with `ε(A) < HD(1) − 2/5 − 1/A` gives 70%.
   No such theorem exists; the corpus's hyperbolic density theorem (MZF) controls isolated zeros at
   depth `α/log T` with rate `e^{−2α}`, which is the right shape but with a constant that does not
   reach the census.

So: 70% is not on a clear path, but it is now a precise dichotomy whose unresolved side is a
depth-sensitive statement at the mean-spacing scale, not a proportion computation.

---

## 5. The one big question, less hard than RH and quasi-RH, whose answer would be a breakthrough

**The question: the asymptotic abscissa law (AAL).** Is the supremum of the depths of the zeros
approached infinitely often? Precisely: with `Θ = sup Re ρ` and `Θ∞ = inf{σ : finitely many zeros with
Re ρ > σ}`, is `Θ∞ = Θ`? Equivalently: can `ζ` have a finite, isolated layer of deepest zeros with a gap
below it?

**Why it is less hard than RH, and not quasi-RH in disguise.** RH ⇔ ZAL ∧ AAL
(`riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw`), and RH ⇒ AAL trivially. The
obstacles ledger records `qRH ∨ AAL` in the sense that `¬AAL` already contains a strip `Re s > σ`,
`σ < Θ < 1`, with only finitely many zeros (the top layer is attained, and `ζ(1 + it) ≠ 0`), so proving
AAL may *assume* a quasi-RH-type structure while refuting it; neither AAL nor a zero-free strip
implies the other in any proved sense. The
validation tests of this repository (RH-equivalents are not doors; a door must kill or establish
several routes) are passed: AAL is not RH-equivalent, and it is the hinge of the corpus's large-height
theory.

**Why its negation is one rigid object.** The corpus proves, unconditionally:
- `¬AAL` ⇔ `ψ(x) − x = x^Θ T(log x) + O(x^{Θ−η})` with `T` a nonzero finite real trigonometric
  polynomial whose frequencies are the ordinates of the top layer
  (`not_asymptoticAbscissaLaw_iff_primeErrorIsFiniteOscillation`,
  `exists_primeErrorFiniteOscillation_of_lt_gap`, `abscissa_eq_zetaZeroAbscissa_of_finiteOscillation`);
- `¬AAL` ⇔ two-prime dilation annihilation: for two primes `p ≠ q` there are finite dilation
  combinations `Σ_{s∈S} c_s ψ(p^s x)` and `Σ c_s ψ(q^s x)` that reduce the prime error to `O(x^{β−η})`
  (`not_asymptoticAbscissaLaw_iff_twoPrime_dilationAnnihilation`); the zeros of depth `β` then lie on
  `α + (2π/log p)ℤ` and on `α′ + (2π/log q)ℤ`, hence are finite
  (`re_eq_and_im_mem_periodic_of_dilation_bound`, `finite_xiZeroCopy_of_twoPrime_dilation_bound`);
- under `¬AAL` a zero of maximal angle is attained, every Hadamard factor points the same way there,
  and the extremal zero obeys a Hermite–Biehler modulus inequality and a Stieltjes sign (RAC
  `exists_zero_of_maximal_angle`, `norm_squaredXi_conj_lt`, `im_stieltjes_nonpos`);
- every return at a right zero is tail-bad at every cut with amplitude `|E_y(ρ)|`, and such returns
  have density zero (TAPO `zetaReturnSet_subset_eulerDiscTailBadSet`,
  `exists_returns_tailBad_and_rare`); under `¬AAL` at every aligned shift of length `N` past a height,
  `ζ` exceeds `N^A` on a disc right of the line joining the zero to `Re s ≥ 2`
  (AAD `exists_large_value_of_finite`).

No other object in the corpus about the zeros of `ζ` has this much structure. It is the only place
where a contradiction can be sought against a hypothesis stronger than anything known.

**What AAL would establish.** The obstacles ledger records, and the corpus confirms, that under AAL
every large-height receiver reads RH: finite Krein–Langer index, bounded heat nonreal counts, an
eventual central-gap sign, slow aligned returns, finite support of escape states, all become
RH-complete. AAL converts "all but finitely many" into "all" and "density one" into "every height" for
the zero-location statements of the corpus, which is exactly the objection (finite exceptional
layers, S-series blocks on almost-all theorems) that stops the route families Σ-continuation (ZCG,
NGF, heat), Π-long-moments (CDG, APR landings) and the finite-height transfers. It would also reduce RH
to ZAL, i.e. to eventual quasi-RH at every depth, which is the statement the production and near-line
programmes are built for.

**What AAL would kill.** Every mechanism that works on the finite top layer only through size or
through linear ledgers: the corpus has already shown linear floor identities annihilate zero modes,
that transport by returns is free and the golden fake returns exactly while failing the count, and that
size cannot repel below the saddle. AAL would therefore also settle which of the sign-free routes
(transport, camera, cut system) have content: a proof of AAL must use the tail or the carry, so the
route that proves it is the one that survives.

**The tools in hand and the exact missing step.** The missing step has three equivalent faces.
1. *Transport.* Exhibit, at a right zero `ρ`, aligned shifts `τ` of arbitrarily large length `N` with
   `|ζ(s + iτ)| ≤ N^A` on the disc of radius `3 − σ₀` about `3 + iγ` for some `σ₀ ∈ [½, Re ρ)`
   (`asymptoticAbscissaLaw_of_slowReturns_right`); the disc must stay right of the line (the left disc
   is killed: it forces power growth). This is a question about large values of `ζ` at aligned
   heights, right of the line.
2. *Tail.* Show a bounded return at a right zero exists or does not (B89): at the Kronecker scale the
   tail is Gaussian conditionally on the head and the cost of a tail-bad event is a Gaussian large
   deviation; past the Kronecker scale the tail law is open.
3. *Carry.* Show that `N(x) = ⌊x⌋` cannot coexist with a finite-oscillation prime error (SPL's "carry
   contradiction for finite oscillations"). The exact identities are boundary conditions and annihilate
   the zero modes; the inequality must come from the integer count, the carry `⌊kx⌋ − k⌊x⌋ = ⌊k{x}⌋`,
   which is never constant and is the Frobenius defect of ℤ.

**Caveat.** The corpus does not prove AAL is easier than quasi-RH; it proves it is different (no
implication either way) and that its negation is maximally structured. That is what makes it the
right question: a proof would come from exploiting the structure of `¬AAL`, not from a saving.

---

## 6. The same question when positivity, Weil positivity and spectral methods are excluded

The answer is the same question, because AAL is already sign-free in every formulation the corpus
gives it: the finite oscillation of the prime error, the two-prime dilation annihilators, the aligned
slow return with a size bound on a disc right of the line, the tail-bad law of returns at a zero, and
the carry. None uses a quadratic form with a sign, a self-adjoint operator, or Weil positivity. The
programmes that own these formulations (ZCG, AAD, RAC, TAPO, SPL) are the corpus's sign-free theory.

What changes under the assumption is which face of the missing step is admissible, and what the
second question is.

**Admissible faces.** Transport (1) is a size statement about `ζ` at aligned heights. Tail (2) is a
conditional probability statement about Dirichlet polynomials at one height. Carry (3) is an integer
combinatorial statement. All three are admissible. The extremal law of RAC (Hermite–Biehler modulus,
Stieltjes sign) is admissible as an inequality about an entire function of order `½`, not a positivity
of a form; RAC shows a real quadratic satisfies the whole inequality, so a further property of `Q`
(order `½`, log-concavity of coefficients, functional equation) must enter.

**The sharpest sign-free sub-target.** The constant-precision first return of the prime orbit and the
large values of `ζ` at it. TAPO: a return of the primes up to `N` at height `t` to precision `η` is a
spike `|ζ(1 + 1/log N + it)| ≍ (log N)^{1−η}` (`log_norm_zeta_ge_of_isReturn`), and precision buys
length (`R(y, η) > exp(√(y/48 log y))` at precision `y^{−9/2}`, the bound RH gives at constant
precision). The transport face of AAL asks for returns where `ζ` is *not* large right of the line
near the zero. So the sign-free question becomes: at a right zero, do the head-aligned heights at which
the tail stays small (tail-good on a disc right of the line) exist with a polynomial bound? TAPO
proves they are tail-bad at every cut by amplitude `|E_y(ρ)|` and rare; the open part is whether
rarity is impossibility.

**The second sign-free question: the count-distance geometry of ℤ.** Among positive integer-norm
Beurling systems, count error `o(log n)` forces the rational primes (SPL
`primes_of_sublogarithmic_count_error`); every nonclassical system has `|D(n)| ≥ c log n` infinitely
often; a positive-generator system with error `O((log x)²)` exists with exactly `ζ`'s zeros
(`PositiveNearCount.zetaSeriesC_eq_continuation`); a system with negative generators and count within
`3` of `x` has zeros at `Re s ≈ 0.80` in vertical progressions (RAC `ABoundedCountWithANewZero`). The
question: what count distance is necessary to insert a *finite* layer of right zeros into an
integer-norm system with nonnegative generators? If the answer is "none: a finite isolated layer
forces a count distance growing faster than any admissible one, or forces a vertical column", then
AAL follows for ℤ by taking the system to be ℤ itself. This is a question about counts and carries,
with Hasse–Weil through Stepanov as its finite-field calibration, and it is where the sign-free
programmes converge (RAC §9.3, SPL "Beurling metric geometry above the isolation gap").

If one insists on a question strictly about production rather than location: APR's restated
question, a provable statement `S` with stabilizer in the square-root class other than proximity, or
AAD's "an explicit family of stencils with `g ≥ 0` proved without a bound on `M(x)`". These are
RH-strength in their cofinal forms and are not doors; the first return and the count distance are.

---

## 7. The walls as questions, and the field of mathematics that would answer them

### 7.1 The walls as questions mathematics does not yet have tools for

Read as questions, with the boundary each has been pushed to:

- **Σ.** *What decides the sign of a quadratic form whose margin has fallen below the contribution of
  a single zero?* Below the edge the sign is universal; at the edge it is RH; the only statements
  valid at the edge are identities, inherited polarizations and integer invariants, and every integer
  read at RH-complete resolution is RH. Allegretto–Piepenbrink, Beurling–Deny, Perron–Frobenius,
  optimal Hardy weights, Krein–Pontryagin counting, moment theory each cover a part and none the
  whole (FADF §1): the form is frustrated in every sign gauge past `log ρ`, critical in every
  direction, singular at the boundary, and sensitive to the Euler product inside the strip.
- **Π.** *What produces a count at square-root precision over ℤ?* Dimensions and cardinalities do it
  over `𝔽_q`; over ℤ every count is soft or RH, integrality gives exactly Chebyshev, and the twist
  `x ↦ x^q` has no analogue.
- **Γ.** *What canonical operation identifies the reflection pairing with the conjugation pairing?*
  Over `𝔽_q` the polarization of the Jacobian; over ℤ four RH-equivalent readings and no construction.
- **Dark range.** *What is the law of the tail of the prime orbit past the Kronecker scale, at one
  height?* Below it, Gaussian conditionally on the head; above it, nothing.
- **Count.** *What nonnegative arithmetic function lies at bounded distance from Weil's form?*

### 7.2 The field

The corpus has already built the first chapters of the field that answers these, under many names
(HWV, ADT, AHD, LST, CWS, WTZ, GWZ, SWC, FADF, AIF, PTT, TAPO, SPL, RAC). Its name could be **the
arithmetic Hodge theory of the divisibility–successor complex at criticality**, with a second branch,
**the finite-time integral dynamics of the prime orbit**, and the two joined by **a count on integer
probes**. What follows describes it as a field: its questions, point of view, objects, language,
principles, criteria and topics, taking from the corpus what is proved and naming what is missing.

**Questions.**
1. Which part of a Kähler package exists for the divisibility–successor complex of `[1, N]`, and what
   replaces gluing? (Proved: stars are lower horizons, the counterterm is the boundary flux, the
   divisor identity `Λ ∗ 1 = log` selects `ζ`, deep stars are Hodge–Riemann with margin `log d`, the
   Möbius gluing telescopes into the gcd stratification, the nerve's Euler characteristic is the
   Mertens function. Missing: control of the top coprime stratum by the strata below with
   level-independent constants.)
2. What is the limiting mixed structure of the degeneration and its second order? (Proved: the
   Jordan-totient nilpotent orbit with the prime cone as monodromy, inheritance radius `1/8`, the
   exact second-order pencil, the count on twisted sectors. Missing: a count carrying `κQ(H)` at the
   pole of the frequency count.)
3. What is the cohomology of a window of `Spec ℤ`, with what control along the tower? (Proved: the
   window algebra, Tate pieces as point counts, Weil's form as the jet at dimension zero, exact stage
   transfer, Gorenstein only below `log 3`, genus `≍ 2e^A` as the Young conjugate of the zero density,
   no finite-dimensional realization, no Frobenius since the carry is never constant. Missing: a
   positivity of the Tate family surviving the derivative at dimension zero, uniformly along the
   tower.)
4. What certifies a frustrated, critical, nonlocal Dirichlet form with arithmetic jumps on an interval?
   (Proved: parity sectors, frustration loci, Markov death, pole-charged gauges, causal predictors,
   jet Hankel moment problems. Missing: the mixed pairing of one growth step with premises on the
   shorter window.)
5. What is the law of the tail of the prime orbit at a single height past the Kronecker scale?
6. What is the degree of a correspondence of `Spec ℤ` as a kernel count, and which quadratic invariant
   of the nerve refines the Mertens function?

**Point of view.** Positivity is to be a *structure*, not an inequality: a dimension, a cardinality, an
inherited polarization or an integer with a structural bound. The form is read as a degeneration along
the resolution axis with the dilation monoid as monodromy; the sign is the second order at the
critical curve, and it sits at the pole of a count. The arithmetic enters only where the additive and
multiplicative structures of ℤ meet: successor pairs in the top coprime stratum, the collar kick of a
stage, the non-ratio successor–dilation part of the complete form, the carry. The integers are the
regular representation of the window algebra; the primes generate it; the pole is its one negative
square.

**Objects.**
- The divisibility–successor complex of `[1, N]`; its stars (multiples of `d`), links (prime-tower
  cliques, disconnected), nerve (sets of primes with product `≤ N`), gcd strata (off-diagonal coprime
  parts), top coprime stratum (all successor pairs and coprime shells `(n, kn+h)`).
- The complete Weil family `W_{φ,c,N}` as a continuous Kähler family over the resolution plane; the
  pole packet `v₁` as Kähler class; `v₁^⊥` as primitive part; Ramanujan packets as graded pieces with
  Jordan-totient weights; the horizon layer and its pencil `κW(H) + (βJ/K)A(H)`.
- Windows `[−A, 0]` and the window tower: window algebra `D_N = 𝒜/I_N`, Tate family `J_k` (point counts
  of `𝔸^k ∖ 0` over `ℤ/m`), stage forms, collars, two-collar forms, lattice Toeplitz forms with their
  Levinson margins and Schur parameters, zero modes as palindromes with angles on the circle.
- The arithmetic Arakelov bundle `⊕_{m ≤ e^A} 𝒪(½ log m)` with the theta metric; Künneth and primitive
  `h¹`; the jump count on prime-free cycles; the window genus `≍ 2e^A`.
- Signed Dirichlet forms: sector conductances, frustration loci, pole charges (sinh and cosh), theta
  gauges, causal predictors, collar Hankel forms, the jet Hankel system.
- The Krein square `𝒬(x,y) = y² − txy + qx²` on integer probes, the degree form, the count law.
- The prime orbit `(t, ω_t)` at finite time: columns, defects, Bohr sets, resonators, Tarry–Escott
  words, the head–tail split at a cut `y`, the first return, the comb of a return, winding numbers of
  `t log n`.

**Language.**
- *Edge-valid*: an identity, an inherited polarization or an integer invariant, valid at every
  resolution including the edge. *Soft*: true for every datum of a family (every twist, every zero
  configuration, every finite ring). *Selective*: false on a named fake. *Carrier*: a count (A), an
  inherited polarization (B), an integer with a structural bound (C).
- *Frozen/complete*, *collar data*, *stage*, *kick*, *margin*, *prediction interval*, *outer ground
  state*, *first critical length*, *zero mode*, *angles*.
- *Stabilizer* of a statement; *precision class* `𝒬`; *receiver/producer/landing*.
- *Kronecker scale*, *size horizon*, *required saving*, *dark range*, *tail-good/tail-bad height*.
- *Reading* of a weight by a test (through the autocorrelation at `log n`); *blind* test.

**Foundational principles (proved in the corpus, to be taken as axioms of the field).**
1. *Edge logic.* A positivity proved without zero information cannot cross the edge of a datum with
   off-line zeros; what crosses is structure (EHT).
2. *Soft or RH.* Everything counting can do by itself is either soft or RH; there is nothing
   intermediate (AET, LST). A theory of the field must therefore produce statements that are partial
   but selective: pinning laws (`|λ(n) − Λ(n)| ≤ C e^{Kn − c/1104}`), stage fibres, first-prime weight
   bands, lattice selection.
3. *Index before sign; support and decay decide type; localize, then glue at the pole* (AKG). The pole
   is the one negative square RH permits; every other negative square is an off-line zero.
4. *Positivity of the graded pieces does not pass to the top stratum*: the forward cone expansion is
   sign-free and the Möbius inverse alternates (ADT). The inductive step must bound the top stratum
   by the strata below with constants independent of `N`.
5. *The sign is second order and sits at the pole of a count* (AHD).
6. *Growth is one mixed pairing per step with premises on the shorter window* (CSW, SWC); a certificate
   may lose constants only on rate landings, never a rate.
7. *Charges survive energy limits* (CSAR): norms are not signed forms; every passage to a limit must
   retain the receiving charges.
8. *Equivalence through RH transfers truth, not mechanism*; a reformulation counts only when it moves
   the problem to an object with a new tool.

**Criteria for a theorem of the field.** Unconditional; says which kind of statement it is (identity,
inherited polarization, integer invariant, estimate with its regime, equivalence, or no-go with its
positive survivor); says which part of the form it controls (archimedean jumps, antisymmetric fold
counts, symmetric fold masses, canonical density, pole; or algebra, lattice, pole plane); says what it
does on the fakes (golden curve, Epstein beyond the self-dual point, prime flips, Liouville twin,
`ζ(s)ζ(s−ε)`, tree-lattice black holes, bounded-count model); reproduces Weil and Stepanov over `𝔽_q`;
loses no multiplicative factor on the window and lattice landings; names the primes and lengths it
reads; is a law along the tower or turns into one.

**Research topics, in the order the corpus's own gaps suggest.**
1. The top coprime stratum against the strata below, level-independently (HWV §8.1): the exact leading
   term of the bilinear residual of order `c/log N` against `κ₀` from the Mertens remainders at shifted
   horizons, the archimedean cross errors and the shift distribution of the coprime shells.
2. A quadratic (signature) invariant of the nerve refining the Mertens function; its half-power law
   would be RH-hard, its existence is the Hodge index refining Betti numbers.
3. The Poincaré inequality for the Lévy count on the middle of a window paying the symmetric fold
   mass of `T₂` (CWS §7.1), and signed ground states past `log ρ`.
4. The degree of a correspondence of `Spec ℤ` as a kernel count; a count equal to the Krein square on
   integer probes; a naive height on window correspondences.
5. The layered Künneth step for the complete family (the archimedean part couples valuation layers
   through successor pairs).
6. Window Frobenius at infinity: an operator on the window object with fixed line `Re s = ½` that is
   not an isometry on every datum.
7. The tail law of the prime orbit at one moment past the Kronecker scale (tilted resonators of budget
   `Σ f_p² log p ≲ log T`); the heavy first return at the size curve.
8. The same-point identity: control of `D` in `(σ − ½)S − Re ξ′/ξ = D ≥ 0` near `½`.

---

## 8. The field when positivity, Weil positivity and spectral methods are excluded

Removing the sign removes the first branch of §7 (Hodge theory, Dirichlet forms, index theory, inner
functions, scattering) and leaves the corpus's sign-free theory: RAC, AAD, ZCG, NGF, PTT, TAPO, SPL,
the production theory of APR and ASRP. The field would be **the rigid arithmetic of cuts and carries,
with the integral dynamics of the prime orbit**: the theory of how the single object `N(x) = ⌊x⌋`
constrains the zeros by operations without a sign and not linear in `Λ`.

**Questions.**
1. Can the prime error be a finite oscillation? (`¬AAL`; §5.) What property of `⌊x⌋`, beyond the
   exact identities that annihilate every zero mode, contradicts `ψ(x) − x = x^Θ T(log x) + O(x^{Θ−η})`?
2. What plays the part of Stepanov's twist `x ↦ x^q` over ℤ: an operation making vanishing along prime
   progressions cheap? (EAHT: over `𝔽_q`, `x^q = x` makes vanishing at all points of one degree cheap;
   over ℤ each prime has its own progression, and multiplicity `r` on torsion loci costs support
   `2^{qr}`, AHA.)
3. Which degree-two (or higher) statement about `Λ` over ℤ has no analogue for a general meromorphic
   function with the same functional equation? (RAC, AAD: the ledgers `ζA^k` see a zero of order `m` at
   degree `m + 1`, but the order law is universal; their exact combination `ζ(A² − A′) = ζ″` is blind
   again.)
4. What auxiliary object vanishes on the odd Liouville class to growing order, finer than divisibility?
   (AKL: the index is set by one global law, an upper count for the odd Liouville class at square-root
   precision.)
5. What is the constant-precision first-return exponent of the prime orbit, and the tail law past the
   Kronecker scale? (TAPO.)
6. What count distance is necessary to insert a finite layer of right zeros into a positive
   integer-norm system? (SPL, RAC; §6.)
7. What survives when a dilation is written as an average of translations, and can carries bound the
   concentration of `t log n` on arcs with nonzero winding? (SPL.)

**Point of view.** Zeros are the power-law kernel of the cut system; parity is a size statement, not
missing information; the rate of any producer is the Mertens level; integrality is free and
multiplicity lives in fractional parts; the first return is an extreme value; the tail carries the
zero. The decisive input must be an *inequality* on a nonlinear functional of `Λ` (or of `⌊x⌋`), not an
identity, and must fail for a general meromorphic function, for continuous Beurling systems, for the
golden fake and for the bounded-count model.

**Objects.** Stencils and producers (factorial ratios `Π ⌊n/k⌋!^{c(k)}`), their multiplicity `g`,
slope, excess, rate and peak; fake prime measures and the real linear program with its extremal
measure; the cut system and its kernel (zero modes `r^{−s}`, superpositions, Hecke action); ledgers
of every degree `Σ_d Λ^{∗j}(d) g(⌊x/d⌋)`; the carry `⌊k{x}⌋`; parity ledgers and the exact identity
`Σ_k L(x/k) = ⌊√x⌋`; Beurling systems with their count distance, exchange exponent and Hamming law; the
near-count and bounded-count models; the prime orbit with its head–tail split, resonators, words,
first return, comb and winding occupation; shifted-product signatures `(ab, (a+1)(b+1))` and tuple
reconstruction by translated products; the heat flow of `H_t` as a parabolic object with Fock energy,
frequency, zero number, gap law and depth moments.

**Language.** Cut, carry, multiplicity against size, blind/exact functional, fake, tight, kernel vector,
filter, harmonic mass, parity exponent, oscillation and annihilator, head and tail, transport,
isolation, extremal position, dominance (RAC); producer, alphabet, rate, peak, entanglement, Mertens
level, ledger, return exponent (AAD); return, weak return, first return, heavy return, dark range,
resolution, fade, atypical member, exotic block, comb (TAPO); phase level set, shifted product
signature, mixed collision count, winding, carry, count distance (SPL); camera, mimic, cancelling
cluster, blind window, Ingham scale, density aperture (ZCG).

**Foundational principles (proved).**
1. Exact linear ledgers are blind at every zero; exact nonlinear combinations are blind again; the
   order law of `ζA^k` holds for every analytic function (RAC, AAD).
2. A stencil with a constant window contains `μ`; its rate is a bound on `M(x)`; integrality costs
   nothing; parity neutrality costs nothing (AAD).
3. The primes always recur, at positive density and effectively; at a zero the tail fails, at every
   length and every cut (RAC, TAPO).
4. Non-alignment past the Kronecker scale is forced by unique factorization alone; diagonal moments,
   one word, one polynomial phase and the rounded orbit are proved ceilings (PTT).
5. Identification is cheap and sign-free; hiding costs density and near-collisions; certification for
   `ζ` needs cancellation of the Euler product at the mean spacing (ZCG).
6. Count error `o(log n)` forces the rational primes; count distance alone does not measure the
   insertion of right zeros (SPL).
7. Reality leaves the line only through a collision; the parabolic tools are blind to the initial time;
   the central inequality `g_t² ≥ c min(t, log⁻²X)` is stronger than RH and holds on density-one heights
   down to the critical scale (NGF).

**Criteria.** No quadratic form with a sign, no self-adjoint operator, no Hadamard positivity; a
reading over `𝔽_q` recovering Hasse–Weil through Stepanov in the same language; separation of the
rational primes from continuous Beurling systems and discrete near-fakes (golden, bounded-count,
near-count); the stabilizer named, or a perturbation in it; the scale moved named against the Kronecker
scale, the diagonal range, the size horizon, the mixing time and the VK length; every exact identity
labelled as a boundary condition, not as the inequality; a power-saving parity claim must expose its
zero-free-strip consequence.

**Research topics.**
1. The carry contradiction for finite oscillations (AAL in sign-free form).
2. Positivity `g ≥ 0` of an explicit stencil family without a bound on `M(x)`, past the VK scale; the
   exponent gap `[1/4, 1/2]` under RH; compensation of primes below `√T` (target exponent `1/3`).
3. A nonlinear ledger bound not implied by meromorphy; parity through stencils whose twist `D_{cλ}`
   vanishes at a prospective zero.
4. Slow aligned returns right of the line, or their exclusion in a stated class; a bounded return at a
   right zero (B89) at the Kronecker scale as a Gaussian large deviation.
5. The constant-precision first-return exponent; a Lean form of `|ζ(1 + it)| ≪ (log t)^{2/3}(log log
   t)^{1/3}` would give `κ ≥ 3/2` through the dictionary.
6. Smooth numbers in short intervals of length `N/T` with polylogarithmic smoothness (the factor
   `k!(log y/4)^k` past the diagonal); the comb below `X ≍ t`.
7. Shifted-product concentration of actual phase level sets with nonzero windings; exponential sums
   for `t log(n + h)` past Taylor degree `(log length)²`.
8. The smallest count distance carrying a finite layer of right zeros among positive integer-norm
   systems (between the proved `c log n` obstruction and the `(log x)²` near-count construction).

---

## 9. Glossary of programme abbreviations used

ACS ArithmeticCastelnuovoSeveri; ACoT ArithmeticCouplingTheory; ADT ArithmeticDegenerationTheory;
AET ArithmeticEffectivityTheory; AHD ArithmeticHodgeTheoryOfDegenerations; AIF
ArithmeticInnerFunctionTheory; AKG AdelicKreinGeometry; AKL ArithmeticKreinLangerTheory; AAD
ArithmeticAuxiliaryDynamics; AOG ArithmeticOrientationGeometry; APol ArithmeticPolarization; APR
ArithmeticProduction; ASH ArithmeticScatteringHolography; ASRP ArithmeticOfSquareRootPrecision; CACT
CriticalArithmeticCorrelationTheory; CDG ConjugateDiagonalGeometry; CHT
CriticalHardyTheoryOfTheWindowCone; CSAR CriticalScaleArithmeticRigidity; CSW
CanonicalSystemOfTheWindowTower; CWS CohomologyOfWindowsOfSpecZ; EAHT EffectiveArithmeticHodgeTheory;
EHT EdgeHodgeTheory; FADF FrustratedArithmeticDirichletForms; GWZ GrowingWindowsOfSpecZ; HEF
HilbertianExplicitFormulas; HKT HeckeKreinToeplitz; HWV HodgeTheoryWithoutVarieties; IGP
IncommensurableGaborPinching; LST LatticeSectionTheory; MZF MultiscaleMollifiedZetaField; NGF
NodalGeometryOfTheDeBruijnFlow; PTT PrimeTorusTheory; RAC RigidArithmeticOfCuts; RAPT
RenormalizedArithmeticPotentialTheory; RIT RenormalizedIntersectionTheory; SCPE
ShallowCauchyPrimeEnergy; SPL SumProductArithmeticOfTheLogarithm; SRT SquareRootThreshold; SWC
SignedWindowCriticality; TAPO TailArithmeticOfThePrimeOrbit; TM TransMetzlerWeilPositivity; TTPC
TransThresholdPairCorrelation; WTZ WindowTowerOfSpecZ; WVL WindowVisibilityLaw; ZCG
ZeroConfigurationGeometry.
