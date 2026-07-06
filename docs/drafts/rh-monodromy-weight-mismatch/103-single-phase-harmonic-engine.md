# 103 — (SMOOTH-LOW): the single-phase harmonic engine and its degradation law

The (SMOOTH-LOW) architecture (docs 86–87) reduced Route B′ to the small-ball / 2D density
of the smooth multiplicative packet `Z = Σ_{u≥2 z-smooth} u^{-1/2} w_u X_u`.  Its analytic
substrate had two kinds of building block in Lean: the **isolated bare phase**
(`arc_sublevel`: one prime `p > N/2` whose character `X_p` enters exactly one coefficient,
a single `e^{iθ}`), and the **linear four-phase caustic** (`RouteBThreePhase`,
`RouteBFullSupport`: four such isolated primes with a modulus gap).  Both require the
prime to be *isolated* (`p > N/2`).  But the packet's mass lives on **small** primes
(doc 86 §6: `M_q ≈ e^{−γ}/(2q)`, dominated by small `q`), where a prime is *not* isolated —
`X_p` enters the coefficient of every multiple of `p`, so conditioned on all other phases
the packet is a genuine **polynomial in the single phase** `X_p`, with harmonics
`e^{iθ}, e^{2iθ}, …, e^{iKθ}`, `K = ⌊log_p N⌋`.  That object had no anti-concentration brick.
This doc builds it.

## 1. The single-phase harmonic law [PROVED HERE — Lean, axiom-clean]

New module `RouteBSinglePhase.lean` (6 endpoints, `[propext, Classical.choice, Quot.sound]`).

- **`root_arc_measure`** — the single-root arc `{θ ∈ [0,2π] : ‖e^{iθ} − z‖ ≤ s}` has
  measure `≤ 2π·√(2s)`, uniformly in the center `z ∈ ℂ`.  (Case `s > ½`: total measure
  `2π ≤ 2π√(2s)`.  Case `s ≤ ½`: a nonempty arc forces `‖z‖ ≥ 1 − s ≥ ½` by the reverse
  triangle inequality, then the tree's `radial_band_measure` with `‖z‖ ≥ ½` gives the
  uniform √-law.)
- **`exists_factor_le`** — a product of `n ≥ 1` nonnegative reals `≤ M` has a factor
  `≤ M^{1/n}` (else all factors exceed `M^{1/n}` and the product exceeds `(M^{1/n})^n = M`).
- **`prod_circle_sublevel`** — the root form: for centers `z_i` (`i ∈ s`, `|s| = n ≥ 1`)
  and leading coefficient `leadC ≠ 0`,

  > `volume{θ ∈ [0,2π] : ‖leadC · ∏_i (e^{iθ} − z_i)‖ ≤ r} ≤ n · 2π · √(2·(r/‖leadC‖)^{1/n})`.

  (Factor: `∏‖e^{iθ}−z_i‖ ≤ r/‖leadC‖ ⟹ min_i ‖e^{iθ}−z_i‖ ≤ (r/‖leadC‖)^{1/n}`, so `θ`
  lies in one of `n` single-root arcs.)
- **`poly_circle_sublevel`** — the coefficient form: for a polynomial `p` of degree `n ≥ 1`,

  > `volume{θ ∈ [0,2π] : ‖p(e^{iθ})‖ ≤ r} ≤ n · 2π · √(2·(r/‖leadingCoeff p‖)^{1/n})`,

  by splitting `p` into linear factors over `ℂ` (`C_leadingCoeff_mul_prod_multiset_X_sub_C`
  + `toEnumFinset`).  **This is doc 86 §5's degeneration object made a theorem:** a single
  phase's value `p(e^{iθ})` traces an algebraic curve in `ℂ`, and its `r`-neighbourhood in
  angle has a genuine **power law** with exponent `1/n` — never a point mass, but never the
  two-dimensional `r²` either.

## 2. Shift-uniformity and the conditioning step [PROVED HERE — Lean]

- **`poly_circle_sublevel_shift`** — adding any constant `w` leaves the bound unchanged:
  `‖w + p(e^{iθ})‖ ≤ r` obeys the same degree-`n` estimate, because `p + C w` has the same
  degree and leading coefficient as `p`.  This is the property a conditioning argument
  consumes: the single-phase bound is **uniform over the value `w`** obtained by fixing
  every other phase.
- **`two_single_phase_sublevel`** — the conditioning composition: for two independent
  phases with single-phase polynomials `P`, `Q` (`deg P ≥ 1`),

  > `(vol×vol){(θ,φ)∈[0,2π]² : ‖c + Q(e^{iφ}) + P(e^{iθ})‖ ≤ r} ≤ 2π · [single-phase bound for P]`.

  (Fubini over `φ`; for each fixed `φ` the value `c + Q(e^{iφ})` is an additive constant the
  shift-uniform bound absorbs.)  **The joint field is at least as anti-concentrated as any
  single non-linear phase in it** — the hierarchical conditioning spine, now for the
  non-isolated (mass-carrying) small primes, not just the isolated caustic block.

## 2′. Landing on the product model [PROVED HERE — Lean, axiom-clean]

New module `RouteBSinglePhasePi.lean` carries the engine onto the Steinhaus product measure,
where a NON-isolated prime's character enters through all its harmonics.

- **`single_phase_interval_le`** — the `[0,1]`-average of the small-ball indicator of
  `V + P(unitPhase(·))` is `≤ (2π)⁻¹ · singlePhaseConst P t`.  The angle rescale `θ = 2π x`
  (`map_two_pi_smul`) turns the unit-interval average into the `[0,2π]` sublevel measure, then
  `poly_circle_sublevel_shift` applies with shift `V`.
- **`pi_single_phase_le`** — for the product measure over the phase coordinates, if the carrier
  is `g(x) + P(unitPhase(x_q))` with `g` invariant under coordinate `q` and `deg P = n ≥ 1`,

  > `(Measure.pi …){x : ‖g(x) + P(unitPhase(x_q))‖ ≤ t} ≤ (2π)⁻¹ · singlePhaseConst P t`.

  Proof: reduce `Measure.pi` to the coordinate marginal (`lmarginal_union` + `lmarginal_insert`),
  integrate out `q` by `single_phase_interval_le` (conditioning freezes `g` to the constant
  `g(z)`, absorbed by the shift-uniform bound), and the remaining coordinates integrate against
  probability measures.  **This is the honest reduction the (SMOOTH-LOW) argument needs at the
  model level:** the whole multiplicative packet is at least as anti-concentrated as ANY single
  non-isolated prime's harmonic block, uniformly in every other phase.

## 3. The degradation law — why one phase is not enough, exactly

The exponent is `1/n` with `n =` the harmonic depth.  For the certificate carrier
`Σ_{k≤N} k^{-1/2} X_k` conditioned on all primes but `p`, the depth is `n = ⌊log_p N⌋`, so a
single non-isolated prime alone gives only

> `meas{‖Z‖ ≤ t·rms} ≲ (log_p N) · √(t · rms^{...})` — exponent `1/⌊log_p N⌋ → 0`.

This is **not a weakness of the proof; it is the content of doc 86 §5's 1D-degeneration
falsifier, now quantitative.**  A single phase, no matter which, degenerates: its value lies
on a curve, and the deeper its harmonics the flatter the anti-concentration.  The `t²`-rate
of (K-bdd-n-log) can only come from **spreading** the mass across many multiplicatively
independent phases — each contributing an independent 2D-ish increment — so that no single
curve carries the whole field.  The single-phase engine is the correct *floor*: it is exactly
what one gets with the spread switched off.

## 3′. The transversal `t²` engine — the improvement mechanism [PROVED HERE — Lean, axiom-clean]

The single-phase floor degrades because one phase's value lies on a *curve* (dimension 1).  The
improvement to the two-dimensional `t²` rate comes from **transversality**: two phases whose combined
map `Φ` covers a 2-D patch of `ℂ`.  New module `RouteBTransversal.lean`:

- **`transversal_smallball`** — if `Φ : ℂ → ℂ` is injective on a measurable `region`, differentiable
  there, and its real Jacobian determinant has modulus `≥ λ > 0` throughout, then

  > `volume{z ∈ region : ‖Φ z‖ ≤ t} ≤ π t² / λ`.

  This is mathlib's area formula (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) read as a
  small-ball bound: `Φ` maps the level set into the disc of radius `t` (area `π t²`), and the
  `≥ λ` Jacobian expands area by at least `λ`, so the preimage has area `≤ π t² / λ`.  **The genuine
  `t²` rate, from a constraint (the Jacobian floor), not a flow.**

The engine fires on the concrete pair.  New module `RouteBTwoPhaseJacobian.lean`:

- **`hasFDerivAt_twoPhaseMap`** — the Fréchet derivative of `Φ(w) = c + A e^{i·w.re} + B e^{i·w.im}`
  is `reCLM.smulRight(iA e^{i·w.re}) + imCLM.smulRight(iB e^{i·w.im})` (chain rule through
  `HasFDerivAt.cexp`).
- **`smulRight_add_det`** — the real determinant of `h ↦ u·h.re + v·h.im` is `u.re·v.im − u.im·v.re`
  (the `2×2` determinant in the `basisOneI` frame).
- **`twoPhaseDeriv_det`** — **[PROVED HERE — Lean]** `det Φ'(w) = A·B·sin(w.im − w.re)`.  Transversal
  (`≠ 0`) exactly off the diagonal `w.im ≡ w.re (mod π)`, where the velocity vectors align.
- **`twoPhase_transversal_smallball`** — on a measurable region where `Φ` is injective and
  `|sin(w.im − w.re)| ≥ δ`,

  > `volume{w ∈ region : ‖Φ w‖ ≤ t} ≤ π t² / (|A|·|B|·δ)`.

  **The `t²` rate on a named phase pair** — two independent phases already produce the quadratic
  anti-concentration a single phase cannot.  (The injectivity is a hypothesis; discharging it on an
  explicit fundamental patch — via the inverse function theorem at the `≥ δ` Jacobian floor, or the
  two-circle-intersection orientation argument — makes it unconditional; it is the one remaining
  geometric lemma of the pair case.)

## 4. Status and the frontier this sharpens

| block | isolation | Lean | rate |
|---|---|---|---|
| bare phase (one large prime) | `p > N/2` | `arc_sublevel` | `r¹` |
| linear four-phase caustic | four `p > N/2`, modulus gap | `RouteBFullSupport…` | `r²·J` |
| **single non-linear phase (small prime)** | **none** | **`poly_circle_sublevel`** | **`r^{1/n}`** |
| two-phase conditioning | independent phases | **`two_single_phase_sublevel`** | inherits `P`'s |
| **product-model conditioning** | **any coordinate `q`** | **`pi_single_phase_le`** | **inherits `P`'s** |
| **transversal two-phase** | **Jacobian floor `λ`** | **`transversal_smallball`** | **`t²/λ`** |

The gate (CHAOS-DENS) (doc 86 §6) is now sharply framed: it is precisely the **gap between
the single-phase floor `r^{1/n}` and the target `r²`**, and closing it is exactly the
statement that spreading mass across the `M_q ≈ c/q` independent directions converts `n`
degenerate curves into one 2D density.  The single-phase engine supplies the per-phase input
that an Esseen/Lindeberg assembly over the independent block `(X_q : q ≤ N^{1/4})` would sum.

Three route-free **engines** are now banked (layer 1 of doc 104 §4): the single-phase floor
`r^{1/n}` (`poly_circle_sublevel`), its model landing (`pi_single_phase_le`), and the transversal
`t²` improvement (`transversal_smallball`).  Together they bracket the (SMOOTH-LOW) small-ball: the
floor is what one phase alone gives; `t²` is what a transversal pair gives.  The gate is the **global
assembly** that composes them across the packet — and it is genuine research, not further plumbing:

- **The single-prime composition is vacuous** (recorded so it is not re-attempted): via one prime `q`
  the exponent is `1/⌊log_q N⌋`, so the bound `⌊log_q N⌋ · 2π · √(2·(t/‖a_{q^k}‖)^{1/⌊log_q N⌋})`
  tends to `∞`, not `< 1`, as `N → ∞`.  Even though the top harmonic coefficient is the *constant*
  `a_{q^k}` (the pure prime power `q^k` is the unique term of maximal `q`-valuation, so its harmonic
  coefficient carries no other phase), a single phase cannot beat the floor.  So "compose via the best
  prime" is theatre; the useful bound must be many-phase.

- **The genuine core** is the `k`-phase Esseen/Fourier assembly: `Z = Σ_q Z_q` is a sum of independent
  2-D increments; its small-ball is `≤ ∫_{ℝ²} |φ_Z(ξ)| dξ` with `φ_Z = ∏_q φ_{Z_q}`, and the product
  decay over the `M_q ≈ c/q` directions is what yields `t²·log(2/t)`.  **The Fourier-side reduction is
  now built** — new module `MeasureParseval.lean`, axiom-clean:
  - `integral_measure_eq_integral_fourier_charFun` — the **measure-Parseval identity**
    `∫ g dμ = ∫ w, 𝓕 g w · charFun μ (2π·w)` (Fourier inversion of `g`, then Fubini);
  - `esseen_concentration` — **Esseen's concentration inequality** `μ(A) ≤ ∫ ‖𝓕 g‖` for any real
    majorant `g ≥ 1_A` (via `‖charFun‖ ≤ 1`).  This is the mathlib gap that reduces the smooth-packet
    small-ball to a Fourier-`L¹` bound on `charFun`: plug a bump `g` of width `t` over a ball to get
    `μ(ball) ≤ ∫ ‖𝓕 g‖`, whose value is governed by the `charFun` decay.
  What remains of this route is the **per-direction decay** — `charFun` of the model carrier factorises
  as `∏_q charFun(a_q X_q)`, each a Bessel-type integral `J₀(|ξ||a_q|)` with `√`-decay, whose product
  over the `M_q ≈ c/q` directions makes `∫‖𝓕g‖` small.  That Bessel `√`-asymptotic (stationary phase)
  is the one remaining mathlib gap; the reduction that consumes it is banked.

The concrete next bricks: (a) the two-phase Jacobian `|det| = |A||B||sin(φ−θ)|` + an injective patch,
making `transversal_smallball` fire on a named pair; (b) the Fourier-inversion 2-D density bound
`density ≤ ∫|φ_Z|`; (c) the per-direction char-function decay `|φ_{Z_q}(ξ)| ≤ 1 − c·M_q·(…)`, whose
product over `q` is the spread.
