# Weil positivity across a prime threshold: the log-soft entry law

- **ID:** `WEIL-ENTRY-001`
- **Stage:** 1-in-progress (Lean core closed; conditional theorem on paper)
- **Type:** THEOREM (paper + Lean core) / PRODUCER-SIDE STEP ON RESTRICTED WEIL POSITIVITY
- **Parents:** `3-formalized/archimedean-weil-kernel-sign-and-aperture.md` (§9–§12: the pointwise
  limit of the elementary route), the CCM restricted-Weil Friedrichs operator
  (`CCMRestrictedWeilFriedrichsOperator`, `CCMRestrictedWeilOneSidedFiniteBlock`)
- **RH used:** no · **Computation used:** no
- **Literature (Sept 2026):** Yoshida 1992 (archimedean positivity on `(1/2, 2)`, numerical);
  Connes–Consani 2021 (`W∞(g∗g*) ≥ Tr(ϑ(g)Sϑ(g)*)` for support `[2^{−1/2}, 2^{1/2}]`, one
  computer-checked `L¹` estimate); Connes 2026 survey §6.4: "positivity of `QW_λ` can be proved
  for small values of λ" — no result for the full Weil form beyond `λ = √2`, where the prime `2`
  enters.

## 1. The question

For `f` supported in `[λ^{−1}, λ]`, `S = 2 log λ`, `g = f ⋆ f̃`, the Weil form is

```
Q_S(f) = C(S)‖f‖² + ∫_0^S D(u) K(u) du − Σ_{p^k ≤ e^S} 2 (log p) p^{−k/2} g(k log p),
D(u) = ½‖f − T_u f‖²,   g(u) = ⟨f, T_u f⟩ = ‖f‖² − D(u),
```

with `C`, `K` the elementary aperture constant and weight of the parent card. The prime power
`p^k` switches on at `S = k log p`. Its term has operator norm `2(log p)p^{−k/2}` as soon as
`S > k log p`, however small the excess `ε = S − k log p` — the compressed shift between the two
end windows of length `ε` is a partial isometry. So no norm-perturbation argument can carry
positivity across a threshold; the parent card's §12 shows that no bound on `D(u)` depending on
`u` alone can either.

## 2. The log-soft entry law (Lean, `RHTower.ArchimedeanWeilSoftPrimeEntry`)

Write `M_ε = ∫_{b−ε}^{b} f²` for the mass of `f` in the end window of length `ε` below the right
endpoint `b` of its support.

**Lemma 1 (translate carries the window out).** If `f` vanishes beyond `b` and `u > 0`, then
`M_u ≤ ‖f − T_u f‖²`. Proof: the translate `T_u f` on `(b, b + u]` is `f` on `(b − u, b]`, where
`f − T_u f = −T_u f` because `f` vanishes there; the `L²` mass of `f − T_u f` on the whole line
dominates its mass on `(b, b + u]`. Lean: `weilEndWindowMass_le_sub_translate_sq`.

**Lemma 2 (singularity of the weight).** `K(u) ≥ 1/(2u)` for `0 < u ≤ 1/10`. Proof: from the
parent identity `K(u)·e^{−u/2}(1 − e^{−2u})/2 = e^{−3u} + e^{−2u} − 1`, the right side is at least
`1 − 5u ≥ 1/2` and the multiplier is at most `u`, using `e^{−t} ≥ 1 − t` and `e^{−u/2} ≤ 1`.
Lean: `inv_two_mul_le_weilKernel`.

**Theorem (log-soft window law).** For `0 < ε ≤ u ≤ 1/10`,
`M_ε/(4u) ≤ D(u) K(u)`, and hence, integrating over `u ∈ [ε, 1/10]`,

```
M_ε · log(1/(10ε)) ≤ 4 ∫_ε^{1/10} D(u) K(u) du .
```

Lean: `weilEndWindowMass_div_le_defect_mul_kernel`, `weilEndWindowMass_mul_log_le_integral`
(the integrated form takes the interval integrability of `u ↦ D(u)K(u)` as a hypothesis, which
holds for every `f ∈ L²` by continuity of translation). Axioms
`[propext, Classical.choice, Quot.sound]`.

**Reading.** Concentrating unit mass within `ε` of the end of the support costs archimedean
singular energy at least `¼ log(1/(10ε))`. The prime term at excess `ε` is bounded by
`2(log p)p^{−k/2} √(M_ε^{right} M_ε^{left}) ≤ (log p) p^{−k/2} (M_ε^{right} + M_ε^{left})`, so

```
|prime term| ≤ (4 (log p) p^{−k/2} / log(1/(10ε))) · (positive singular archimedean energy) .
```

The entry of a prime is *log-soft*: its term is a vanishing multiple of the archimedean energy as
the aperture crosses the threshold. This is the multi-aperture argument the parent card's §12
asked for: it uses `f` at all shifts `u ∈ [ε, 1/10]` at once.

## 3. Consequences on paper

**Theorem A (continuity of the ground value across prime thresholds).** Let
`μ(S) = inf { Q_S(f) : ‖f‖ = 1, supp f ⊂ [−S/2, S/2] }`. Then `S ↦ μ(S)` is continuous on
`(0, ∞)`, including at every `S = k log p`.
*Proof sketch.* Away from thresholds the form depends on `S` through its domain and through the
dilation `f ↦ f(e^{−δ}·)`, under which the singular part `1/u` of `K` is invariant and the rest
changes by `O(δ)` relative to the total energy; so `μ` is continuous there. At a threshold the
only new term is the prime term, bounded by `(4 (log p) p^{−k/2}/log(1/(10ε)))` times the
singular energy by §2, and the singular energy is bounded by `Q_S(f) + C‖f‖²` because the
non-singular part of the form is bounded; both sides tend to the same limit as `ε → 0`. ∎

**Theorem B (dichotomy at a prime threshold).** Suppose `Q_S ≥ 0` for `S ≤ k log p` and that the
form at `S = k log p` is strictly positive with no null vector in its form domain. Then there is
`ε₀ > 0` with `Q_S > 0` for all `S < k log p + ε₀`; in particular Weil positivity holds on
`[λ^{−1}, λ]` for `λ < p^{k/2} e^{ε₀/2}`.
*Proof sketch.* The form is `(singular energy) − (compact remainder)`: the non-singular part of
`K` is bounded, and the form domain of the logarithmic energy `∫ D(u)/u du` on a bounded interval
embeds compactly in `L²` (its Fourier symbol grows like `log|ξ|`). Strict positivity without null
vector therefore gives coercivity `Q ≥ κ · (singular energy)` with `κ > 0` by the minimizing-sequence
argument (a sequence with singular energy `1` and `Q → 0` has an `L²`-convergent subsequence
whose limit is a nonzero null vector). By §2 the prime term is at most
`(4(log p)p^{−k/2}/log(1/(10ε)))` times the singular energy, and the dilation of the archimedean
part costs `O(ε)`; so `Q_{k log p + ε} ≥ (κ − O(ε) − 4(log p)p^{−k/2}/log(1/(10ε))) ·
(singular energy) > 0` for `ε` small. ∎

**Corollary (beyond `√2`).** If the Connes–Consani archimedean form at `λ = √2` has no null vector
in its form domain, then full Weil positivity (with the prime `2`) holds on `[λ^{−1}, λ]` for all
`λ` in some interval `[√2, √2 e^{ε₀/2})`. The excess `ε₀` is not explicit because the coercivity
constant `κ` is not.

**What is not proved.** Strict positivity of the archimedean form at exactly `λ = √2` in the closed
form domain. Connes–Consani's inequality `W∞(g∗g*) ≥ ‖Sϑ(g)^*‖²_{HS}` is strict on smooth `g`
(the Mellin multiplier of `g ≠ 0` is injective), but strictness on the closure is a separate
statement; a null vector at exactly `λ = √2` would be a coincidence, and Connes–Consani's
numerics show minuscule positive eigenvalues there, but numerics are not a proof.

## 4. Why this is the producer step and not a receiver

The statement proved is unconditional and moves positivity *across* a prime threshold, which no
result in the literature does. The mechanism is created by the archimedean geometry (the `1/u`
singularity), not transported from the zeros. The two-line route test: the invariant (window mass
against singular energy) is computable without RH and moves when the zeros move (through `μ(S)`).

## 5. Next targets

1. Prove strict positivity of the archimedean form at `√2` on the closed form domain, i.e. that
   `Sϑ(f)^* ≠ 0` for every nonzero `f` in the form domain, from the corpus's Sonin-space assets.
2. Make `κ` explicit at `λ = √2` from the Connes–Consani Sonin-trace lower bound, which would give
   an explicit `λ₁ > √2`.
3. Formalize Theorem A's dilation comparison (the `1/u` part of `K` is dilation invariant;
   the remainder is bounded) as the next Lean block.

## Anti-theatre / anti-laziness (2026-09-03)

New beyond literature: the log-soft entry law and the continuity of the ground value across prime
thresholds; Yoshida and Connes–Consani stop at the threshold and the survey lists nothing
beyond. Corpus: the parent card asked exactly for this multi-aperture estimate and did not have
it; the CCM modules have the Friedrichs operator with primes but no threshold analysis. Not
theatre: the elementary numerics of the pointwise certificate were only used to decide that the
pointwise route cannot reach `log 2`, which the parent already knew. The hardest live problem in
the lane is now item 1 above.

## Addendum 2026-09-03 — deep inspection: what the corpus and Suzuki 2026 already own, and the sharpened theorem

**Correction.** Theorem A above (continuity of the ground value in the aperture, prime thresholds
included) is Suzuki 2026, *Weil's quadratic form via the screw function*, arXiv:2606.09096,
Theorem 1.3, and it is already formalized in the corpus for the exact CCM realization:
`RHTower.continuousAt_ccmRestrictedWeilGroundEnergy` (`SuzukiGroundEnergyContinuity`, right
continuity by compact ground states and no boundary escape, left continuity by inward dilation of
a smooth core). Suzuki uses it only for Yoshida's degeneracy corollary and does not mention the
Connes–Consani threshold. The corpus also owns: small-aperture positivity of the full form
(`exists_suzukiSmallAperture_intervalGroundEnergy_pos`, Suzuki Thm 1.4 asymptotic
`λ_a = log(1/a) + μ₁ − log 2π + ψ(2) − 1 + O(a)`), the endpoint-closure law
(`ccmRestrictedWeilSourceQuadratic_nonneg_iff_strictSubapertures`), the exact form with the
indefinite polar rank-two term and the finite von Mangoldt translation block, the log-weight
equivalence of the archimedean weight (`CCMArchimedeanLogWeightEquivalence`), the Birman–Schwinger
one-sided finite block, and the Sonin carriers (`SoninEvenCarrier`, infinite-dimensional). The
Connes–Consani inequality itself is not formalized (its proof has a computer-checked step).

**What remains new from the previous cycle.** The quantitative log-soft window law (Lean) is not
in Suzuki or the corpus; the qualitative propagation is Suzuki's theorem.

**The two forms.** The literature's positivity at `√2` (Connes–Consani, Yoshida) is on the
subspace `V₀(λ)` of test functions whose Mellin transform vanishes at the two poles; on `V₀` the
polar term vanishes and the form is archimedean minus primes. The corpus's ground energy is that
of the *full* form on all of `L²[λ^{−1}, λ]`, polar term included; both families are
RH-equivalent, but at a fixed aperture `V₀`-positivity is the weaker statement, and it is the one
the literature proves at `√2`.

**Theorem C (strict positivity at `√2` on `V₀`, given Connes–Consani).** Assume
`W∞(g∗g*) ≥ Tr(ϑ(g) S ϑ(g)^*)` for smooth `g ∈ V₀(√2)` (Connes–Consani 2021, Theorem 1). Then the
closed form on `V₀(√2)` has no null vector: `Q(v) > 0` for every nonzero `v` in its form domain.
*Proof.* `R(v) := Tr(ϑ(v) S ϑ(v)^*) = Σ_j ‖ϑ(v) e_j‖²` over an orthonormal basis of the Sonin
space `S(1,1)`. Each term is continuous in `v ∈ L²` (bounded bilinear), so `R` is lower
semicontinuous as an extended-real form. Smooth `g ∈ V₀` are dense in the constrained form domain
in form norm (the two constraints are `L²`-continuous functionals and smooth functions realize all
constraint values), so for `v` in the domain there is a core sequence `g_n → v` with
`Q(g_n) → Q(v)`, and lower semicontinuity gives `R(v) ≤ Q(v)`. Finally `R(v) > 0` for `v ≠ 0`:
`ϑ(v)` is the Mellin multiplier by the transform of `v`, an entire function of the line variable
not identically zero, hence nonzero a.e., so `ϑ(v)` is injective
(`denseRange_lpBoundedMulCLM_of_ae_ne_zero` is the corpus's dual statement), and the Sonin space
is nonzero (`evenSubspace_not_finiteDimensional`), so some `ϑ(v) e_j ≠ 0`. ∎
Lean for the abstract mechanism: `RHTower.SoninStrictPositivityTransfer`
(`lowerSemicontinuous_soninTypeEnergy`, `soninTypeEnergy_pos_of_injective`,
`le_of_lowerSemicontinuous_of_tendsto`, `pos_of_dominates_soninTypeEnergy`).

**Theorem D (beyond `√2` on `V₀`, given Connes–Consani).** Let `μ₀(λ)` be the ground value of the
form on `V₀(λ)`. Then `μ₀` is continuous in `λ` (Suzuki's proof goes through with the two
constraints: they are `L²`-continuous, so limits of constrained normalized ground states are
constrained, and the inward dilation multiplies each polar coefficient by the scalar `e^{±δ/2}`,
so it preserves `V₀`). By Theorem C, `μ₀(√2) > 0` (the constrained ground state is attained by
compactness of the form domain). Hence there is `λ₁ > √2` with `μ₀(λ) > 0` for all `λ < λ₁`:
**Weil positivity with the prime 2 holds on `V₀(λ)` for `√2 ≤ λ < λ₁`.** The log-soft window law
gives the modulus: `μ₀(√2 e^{ε/2}) ≥ μ₀(√2) − C(ε + 1/log(1/(10ε)))`, which makes `λ₁` explicit
once a lower bound for `μ₀(√2)` is known.

**Status of the inputs.** Connes–Consani Theorem 1 is a published theorem with one
computer-checked estimate; it is the only external input. The constrained continuity is a
re-proof of a formalized theorem with two dilation-invariant constraints (next Lean target). The
result is, to my knowledge, the first positivity statement for the Weil form past the entry of
the first prime; it is soft (no explicit `λ₁`) and conditional on a computer-assisted published
theorem, which is why it is recorded as a theorem on paper and not as a corpus-closed result.

**Next targets (ordered).**
1. Constrained ground-energy continuity in Lean, mirroring `SuzukiGroundEnergyContinuity` with
   the two polar constraints (dilation scaling of `inner (ccmPolarApertureVector a (±1/2)) ·`).
2. A lower bound for `μ₀(√2)` from the Sonin trace: `R(v) ≥ c‖v‖²` would need the smallest
   singular value of `ϑ(v) ↦ ϑ(v)|_{Sonin}`, which is where the prolate spectrum enters.
3. The Lean bridge between the elementary `K`-form and the CCM archimedean Fourier weight (the
   Plancherel identity `D(u) = ∫ (1 − cos uξ)|f̂|²` and `∫_0^{1/10}(1 − cos uξ)K(u)du ≤
   C(1 + log⁺|ξ|)`), so that the window law can be stated inside the CCM form domain.

## Addendum 2026-09-03 — Theorem D's continuity input is now Lean (right side)

`RHTower.CCMRestrictedWeilPolarConstrainedRightContinuity` (certificate
`3-formalized/weil-polar-constrained-right-continuity-lean.md`): a strictly positive Rayleigh floor
on the pole-vanishing subspace at aperture `a` persists, halved, on every aperture up to `a + δ`,
with the exact CCM source form including whatever prime powers enter in `[a, a + δ]`. Combined
with Theorem C this gives Theorem D in the form: **if the Connes–Consani inequality holds at `√2`,
then Weil positivity on the pole-vanishing subspace holds with the prime 2 for all `λ` in some
`[√2, λ₁)`**, with only the Sonin inequality itself outside Lean. Left continuity (not needed for
propagation) is not formalized.

## Addendum 2026-09-03 — Theorem D fully in Lean except the `√2` input

Certificate `3-formalized/weil-polar-ground-energy-continuity-lean.md`: the pole-vanishing ground
energy `μ₀(a)` is defined (nonzero pole-vanishing smooth sources exist at every aperture via
Cramer-corrected bumps), is antitone, continuous in the aperture (right side from the constrained
floor theorem, left side from the constrained smooth-core density), and its strict positivity is
an open condition (`eventually_ccmRestrictedWeilPolarGroundEnergy_pos`). Hence

> `μ₀(√2) > 0 ⇒ ∃ λ₁ > √2, Weil positivity on the pole-vanishing subspace for all λ < λ₁`,

with the prime 2 included through the exact CCM source form. `μ₀(√2) > 0` is Connes–Consani's
Theorem 6.11 (their inequality carries a term `−c|ĝ(0)|²`, `c = 4γ/log 2`, which vanishes on the
pole-vanishing subspace) transported to the closed form domain by
`SoninStrictPositivityTransfer`. Their proof of Theorem 6.11 is numerically certified with margin
`ε₂ − ε₁ ≈ 0.0032` (Lemma 6.10), so it cannot be reproduced in Lean under the no-computation rule.

## Addendum 2026-09-03 — the degeneracy law (Lean)

`3-formalized/weil-polar-degeneracy-threshold-lean.md`: the pole-vanishing ground energy is
attained at every aperture, and either it is positive everywhere or it vanishes at a unique
threshold `a*` where the form has a normalized pole-vanishing null vector and is nonnegative on
the pole-vanishing subspace. With Theorems C–D: given Connes–Consani's Sonin inequality,
`a* > √2` (in the aperture variable, `a* > (log 2)/2`), i.e. if RH fails, the first degeneracy of
the pole-vanishing Weil form occurs strictly after the entry of the prime 2. Open: the two RH links
on paper (RH ⇒ no threshold; no threshold ⇒ RH); the second needs the `s(s−1)` multiplier
argument inside the corpus's explicit-formula machinery.

## Addendum 2026-09-03 — the pole-vanishing multiplier, and the status of the two RH links

**Multiplier (Lean, `RHTower.CCMRestrictedWeilPolarMultiplier`).** Two integrations by parts give
`∫ e^{sx} g'' = s² ∫ e^{sx} g` for every smooth compactly supported `g`
(`integral_exp_mul_deriv_deriv`), so `D = ∂² − 1/4`, whose Mellin symbol in the centred variable
is `s(s − 1)`, kills both pole coefficients: `D g` is a pole-vanishing strict-interior source for
every strict-interior source `g` (`isPolarConstrained_polarMultiplier`). Converse on paper: for a
pole-vanishing smooth `f`, `g := −e^{−|x|/2} ∗ f` is smooth, satisfies `D g = f`, and is compactly
supported because beyond the support of `f` it equals `−e^{∓x/2} ∫ e^{±y/2} f(y) dy = 0`. So the
pole-vanishing smooth core is exactly the image of `D`.

**Status of the RH links (deep inspection).** The corpus's `RH ⟸ positivity` chain runs through
zero-mean two-bump tests localizing Suzuki's screw form at `2Ψ(t)` and the pointwise criterion
`Ψ ≥ 0 ⇒ RH` (`riemannHypothesis_of_suzukiSmoothTestFormNonnegative`). Two-bump tests are not
pole-vanishing, and the localization of `Q(D g)` is at the fourth-order distribution `D²Ψ`, whose
sign is not controlled by `Ψ(t₀) < 0`; Cramer-correcting a negative two-bump test costs `O(1)`
coefficients and does not preserve negativity. The zero-side route (`xiOffRealSignTest`,
`XiGuinandWeilExplicitFormula`) lives on the resolvent test algebra, and the corpus records that
the explicit formula does not yet extend to general compactly supported tests (the full test
algebra gate, `weil-polarization-layer-state`). Hence `μ₀ > 0 at every aperture ⇒ RH` is a known
theorem (Bombieri 2000 / Yoshida 1992 on pole-vanishing tests, via `s(s−1)`-weighted Weil
positivity) but is not formalizable from the corpus's present assets without either extending the
explicit formula to compact tests or building a pole-vanishing analogue of the screw
localization. Both are formalization projects of a known theorem; neither is new knowledge.

**Prime-necessity observation (paper, not yet certified).** The exact archimedean form is
`∫ 2θ′(2πξ)|f̂(ξ)|² dξ` on pole-vanishing tests, and `θ′ < 0` on `|t| < 6.29`. A pole-vanishing
test of long support with Fourier mass concentrated near `|ξ| = 1/2` (for instance `D g` with `g`
a smooth window modulated at frequency `1/2`) therefore has negative archimedean form. So the
archimedean form alone is indefinite on the pole-vanishing subspace beyond an explicit aperture,
and the prime terms are necessary for Weil positivity there. Yoshida's numerics give archimedean
positivity up to support `(1/2, 2)`; the explicit indefiniteness threshold is a computable but
unrecorded number.

## Addendum 2026-09-03 — numerical study (`2-fully-proven/computations/weil-polar-ground-energy/`)

Galerkin (orthonormal Legendre, `N ≤ 80`, double precision and mpmath 60–80 digits) of the exact
form `Q = 2c₊c₋ − 2Σ Λ(n)n^{−1/2} g(log n) + Arch` on `L²(−a, a)` and on the pole-vanishing
subspace `V₀`:

- `μ₀(√2) = 0.54704` (N = 64; monotone convergence), second constrained eigenvalue ≈ 0.84; the
  unconstrained minuscule eigenvalue is `1.3293·10⁻³`. The input of Theorem D holds with a
  margin of order one, not the 0.3 % of Connes–Consani's comparison.
- `μ₀(a)` is positive at every computed aperture and every basis size, converged to `≤ 5 %` up to
  `a = 0.75` (`λ = 2.12`, value `7.6·10⁻¹⁰`), then decays super-exponentially below the
  resolution of any basis (`4·10⁻³³` upper bound at `a = 1.4`). No degeneracy threshold is
  visible up to `λ ≈ 5`; an explicit `λ₁` cannot be read off because the energy tends to zero
  without changing sign.
- The archimedean form alone is positive on `V₀` up to `λ_arch = 1.81451` (`a = 0.595815`) and
  negative beyond: prime necessity is quantified, and the √2 threshold is not sharp for the
  archimedean term.
- Truncated forms fail right after the first excluded prime power enters: without 3 at
  `a = 0.5658` (3 enters at 0.5493), without 4 at `0.7025` (4 enters at 0.6931), without 7
  between 0.95 and 1.00 (7 enters at 0.973), without 8 between 1.00 and 1.05 (8 enters at
  1.040). Every prime power becomes decisive within about 0.01–0.02 of aperture after entry — the
  quantitative form of the log-soft entry law.
- The prime 2 lowers the constrained energy (0.5371 → 0.5331 at `a = 0.35`); later primes raise
  the truncated energies back to the full value. The prime terms have no fixed sign.

## Addendum 2026-09-03 — Fourier zeros of the pole-vanishing ground state

`computations/weil-polar-ground-energy/spectral_zeros.json`: the ground state of the
pole-vanishing form is even at every aperture computed and its Fourier zeros converge to the
zeta ordinates exactly as Connes–Consani–Moscovici's full-form ground state does: at `a = 0.9`
both reproduce `γ₁ … γ₈` to three decimals. The full form locks on slightly earlier (`a = 0.5`:
first zero 14.135 versus 14.251). At `√2` the pole-vanishing ground state is generic (zeros
spaced by `π/a`). Reading: the spectral realization is carried by the archimedean-plus-prime
part of the form, not by the pole terms; the two pole directions assist the unconstrained
minimizer rather than contaminate it. Beyond `a ≈ 1.3` extra real zeros interleave with the
zeta ordinates in both forms (zero counting of exponential type versus `N(T)`), and the
eigenvectors become numerically delicate; the reliable regime is `a ≤ 1.1`.

## Addendum 2026-09-26 — a computer-free certificate for `μ₀(√2) > 0` (plan, in progress)

**Trace certificate (paper, exact).** Let `W(ξ) = Re ψ(¼ + iπξ) − log π` (so the archimedean
form is `∫ W |f̂|²`). Let `V₀(a)` be the pole-vanishing subspace of `L²(−a,a)`, and let
`dist_a(ξ)` be the `L²(−a,a)` distance from `e_ξ = e^{2πixξ}` to `span{e^{±x/2}}`. For
`f ∈ V₀(a)`, `f̂(ξ) = ⟨e_ξ − Π e_ξ, f⟩`, so `|f̂(ξ)|² ≤ ‖f‖² dist_a(ξ)²`. Since
`W ≥ α − (α − W)₊`,

`Q_arch(f) ≥ (α − ∫ (α − W)₊ dist_a² dξ) ‖f‖²`   for every `α > 0`.

This is the trace of the compressed negative part of `W − α`; it is finite because
`(α − W)₊` has compact support (`W` grows like `log|ξ|`).

**Closed form.** With `C(ω) = ∫_{−a}^{a} cos(ωx) cosh(x/2)` and `S(ω) = ∫ sin(ωx) sinh(x/2)`,
`dist² = 2a − C²/(a + sinh a) − S²/(sinh a − a)`. At `a = ½ log 2`: `sinh a = √2/4` and
`e^{a/2} = 2^{1/4}`.

**Hand estimate at `a = ½ log 2`, `α = 0.3`.**
- `W(0) = −5.37`, `W(0.5) = −0.70`, `W(1) = −0.001`, `W(1.25) = 0.22`, `W(1.5) = 0.41`.
- `dist²(0) = 1.7·10⁻⁵`, `dist²(0.5) = 0.019`, `dist²(0.75) = 0.081`, `dist²(1) = 0.20`,
  `dist²(1.25) = 0.36`.
- `∫(α − W)₊ dist² ≈ 0.07`, so the certificate gives `μ₀(√2) ≳ 0.2`. The numerical value is
  `0.547`. The Lorentzian dip of `W` at `0` is killed almost completely by the two constraints.

**Lean plan.**
1. Plane-wave vector; `𝓕f(ξ) = ⟨e_ξ, f⟩`; the Cauchy–Schwarz bound under the constraints.
2. Closed-form residual norm via antiderivatives.
3. Certificate inequality for the CCM source quadratic at `a = ½ log 2`: the polar term and the
   `n = 2` prime term vanish (`inner_logTranslationCLM_two_aperture_eq_zero`).
4. Grid numerics:
   - `W` lower bounds from `re_digamma_mono_of_abs_le`, the digamma recurrence and `log_sub_inv_le_re_digamma`;
   - residual upper bounds at grid midpoints, with the Lipschitz constant `2π√(2a³/3)`.
5. `μ₀(½ log 2) > 0`, then `eventually_ccmRestrictedWeilPolarGroundEnergy_pos` gives Weil
   positivity with the prime 2 past `√2`, unconditionally.

## Addendum 2026-09-26 — `μ₀(√2) ≥ 1/10` and positivity past `√2` (Lean, unconditional, computer-free)

**Theorem (Lean, axioms `[propext, Classical.choice, Quot.sound]`).**
- `RHTower.one_tenth_le_ccmRestrictedWeilPolarGroundEnergy_halfLogTwo`: the pole-vanishing ground
  energy of the exact restricted Weil form at aperture `½ log 2` is `≥ 1/10`.
- `RHTower.exists_polarGroundEnergy_pos_past_halfLogTwo`: there is an aperture `b > ½ log 2` with
  positive pole-vanishing ground energy at every aperture `c ≤ b`. Past `½ log 2` the form contains
  the prime `2` (translation by `log 2`).

This closes the only external input of Theorems C–D above. Connes–Consani's computer-checked
Sonin inequality is no longer needed.

**Mechanism: the trace certificate.**
- For pole-vanishing `f`, `f̂(ξ) = ⟨e_ξ − (p cosh + iq sinh)(x/2), f⟩`, so `|f̂(ξ)|² ≤ ‖f‖²·ρ²(ξ;p,q)`.
  The residual `ρ²` has the closed form
  `2a − 2pC + p²(a+sinh a) − 2qS + q²(sinh a − a)`.
- `Q(f) ≥ (α − Σ_k 2h G_k R_k)‖f‖²`. Here `W(kh) ≥ α − G_k` on a grid, and `R_k` bounds the
  shell Fourier mass from `ρ²` at a reference frequency plus the Lipschitz offset
  `4π²d²·2a³/3`.
- Parameters: `α = 3/10`, `h = 1/10`, 14 shells.
  - `W` lower bounds come from the digamma recurrence (16 steps), the half-plane asymptotic, and
    `log π < 1.146`.
  - Residuals come from midpoint–radius enclosures of `log 2`, `2^{1/4}`, and degree-20 Taylor
    `sin`/`cos` at rational phases.
  - Total `β < 0.2`.
- The dip `W(0) = −5.37` is absorbed because `e_ξ` is within `O(ξ²)` of `span{e^{±x/2}}`:
  `dist²(0) = 1.7·10⁻⁵`, `dist²(0.5) = 0.019`.

**Modules.**
- `HTGeometry/MidpointRadiusTrigEnclosures` (enclosure arithmetic, Taylor enclosures).
- `RHTower/PoleVanishingWeilTraceCertificate` (plane-wave residual bound, closed form, Lipschitz
  bound, source-quadratic reduction at `½ log 2`, grid certificate).
- `RHTower/PoleVanishingWeilPositivityHalfLogTwo` (constants, 14 shell residuals, 15 grid values,
  assembly).
- Wired into the umbrellas; `lake build --old` passes; no heartbeat overrides.

**Scope.**
- The certificate is a small-aperture tool. At aperture `a`, the prime sum pushes the support of
  `(α − W_a)₊` out to `ξ* ≈ exp(4e^a)`, while `dist²_a → 2a`. So the trace bound diverges
  super-exponentially in `a`.
- Past `√2` the result is soft: `λ₁` is not explicit.
- Next target: an explicit `λ₁`. Combine the log-soft entry law (end-window mass ≤ singular
  energy / `log(1/ε)`) with a certificate at aperture `b` that controls the singular energy, not
  only `‖f‖²`.

**Correction (2026-09-26).** Positivity past `√2` is not new. Zhu, arXiv 2608.24827 (Aug 2026),
proves `Q(f) ≥ 8.9·10⁻¹⁸‖f‖²` for `supp f ⊂ [−0.8, 0.8]` (primes 2, 3, 4 included) by certified
interval computation. New here: a computer-free, Lean-verified proof with an order-one margin at
`√2`, and the trace-certificate criterion `μ₀ ≥ α − ∫(α − W)₊ dist²`. Parallel card:
`weil-pole-vanishing-bathtub-certificate-sqrt2.md` (same certificate; closed by the modules above).
