# Harmonic residue: the analytic abscissa reader

- **ID:** harmonic-residue-analytic-abscissa-reader
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `route-r-harmonic-quantum-gap-criterion.md` · fifth-pass reader layer
- **Statement:** The harmonic residue of a prime field is simultaneously the limit of bounded cofinal
  profile averages and the `log(1/(s-1))`-normalised value of its prime Dirichlet series at the
  abscissa; hence the Route R first-wall criterion has an equivalent purely analytic form.

## Goal

The profile reader is combinatorial: it computes the residue by averaging against unit-mass weights.
It has been driven to its terminus, and the classification there says the obstruction is not the
device but the invariant. The natural next move is therefore not another combinatorial device but a
*change of language*: express the same invariant analytically, where the standard machinery of
Dirichlet series near their abscissa applies.

This card proves that the two readers compute the same number, and rewrites the Route R first-wall
criterion as a boundary statement about an explicit prime Dirichlet series.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted `lake build` green, axiom audit
- [ ] 3 → 4 publication-ready: standalone paper and refreshed external novelty audit

## Internal corpus audit

- `[CORPUS]` `HTGeometry/CofinalUnitProfileResidue` — `HasReferenceResidue`,
  `IsCofinalUnitProfile`, `profileAverage`, `tendsto_profileAverage`: the combinatorial reader and
  the residue it computes.
- `[CORPUS]` `RHTower/PrimeZetaLogAsymptotic` — `primeZeta s = ∑_p p^(-s)`, `primeLogDefect`, and
  the asymptotic `tendsto_primeZeta_add_log_sub`:

  `primeZeta s + log (s - 1) → -primeLogDefect 1`  as  `s → 1⁺`.

  This is exactly the analytic input needed; it is not re-derived here.
- `[CORPUS]` `RHTower/RouteRCriticalWallOrientedHarmonicQuantization` — the oriented three-value law
  and the bound `|1/p - F(p)| ≤ 3/p²` for the activation Fisher density `F(p) = p/(p+1)²`.
- `[CORPUS]` `RHTower/RouteRHarmonicQuantumGapCriterion`,
  `RHTower/RouteRFirstWallScaleQuantification` — the profile-side criterion, its two-sided scale law
  and its RH characterization.
- No corpus module connects the residue to the Dirichlet series at the abscissa, and none states the
  Route R criterion analytically.

## External audit

That `∑_p p^(-s) ~ log(1/(s-1))` is classical (Mertens, Landau); that a summable perturbation of a
prime field is invisible after `log(1/(s-1))` normalisation is elementary. The composite statement —
"the harmonic residue is the normalised abscissa value" — is folklore-adjacent and is claimed here
only as a bridge, `[NOVELTY UNVERIFIED]`, with no priority asserted. The Route R application is
corpus-internal.

## Complete paper proof `[PROVED HERE]`

Throughout `h(p) = 1/p` and `P(s) = ∑_p p^{-s}`.

### 1. The analytic reader is well defined

Let `a : Primes → ℂ` and `c : ℂ` with `b := a - c·h` summable. For real `s > 1` put

`A(s) = ∑_p a(p) · p^{-(s-1)}`.

Absolute convergence: `|a(p)| p^{-(s-1)} ≤ |c| p^{-s} + |b(p)| p^{-(s-1)} ≤ |c| p^{-s} + |b(p)|`,
and both majorants are summable for `s > 1`. Splitting the series,

`A(s) = c · P(s) + B(s)`,   `B(s) = ∑_p b(p) p^{-(s-1)}`,

and since `p^{-(s-1)} ≤ 1` for `s ≥ 1`, the remainder is *uniformly* bounded:
`|B(s)| ≤ ∑_p |b(p)| =: M`, independently of `s`.

### 2. Normalisation at the abscissa

Write `L(s) = -log(s-1)`. By the corpus asymptotic, `P(s) - L(s) → -primeLogDefect 1`, and
`L(s) → +∞` as `s → 1⁺`. Hence

`P(s) / L(s) → 1`   and   `B(s) / L(s) → 0`

(the second because `|B(s)/L(s)| ≤ M / L(s) → 0`). Therefore

`A(s) / L(s) → c`   as `s → 1⁺`.   **(AR)**

### 3. The two readers agree

Let `mu` be any bounded cofinal unit profile for `h`. The profile reader gives
`profileAverage mu N a → c`, and `(AR)` gives `A(s)/L(s) → c`. So both limits exist and coincide, and
either one determines the residue; uniqueness of the residue follows a third time, now from
uniqueness of limits in `(AR)` alone. The two formulas share no ingredient: one uses unit reference
mass and support escape, the other uses the pole of `ζ` through `P`.

### 4. The first-wall Dirichlet series, explicitly

Let `Φ(s) = ∑_p F(p) p^{-(s-1)}` for `F(p) = p/(p+1)²`. Since `|1/p - F(p)| ≤ 3/p²`,

`Φ(s) = P(s) + O(1)` uniformly on `(1, 2]`.

For the signed first-wall coefficient, `W_t(p) = -sign(t) · F(p) · (1 - p^{-2|t|})`, so

`∑_p W_t(p) p^{-(s-1)} = -sign(t) · (Φ(s) - Φ(s + 2|t|))`.

For `t ≠ 0` the shifted series is bounded on `(1,2]`:
`Φ(s + 2|t|) ≤ ∑_p p^{-1-2|t|} = P(1 + 2|t|) < ∞`. Hence

`∑_p W_t(p) p^{-(s-1)} = -sign(t) · P(s) + O(1)`,

and dividing by `L(s)`:

`(∑_p W_t(p) p^{-(s-1)}) / L(s) → -sign(t)`,

i.e. `-1` for `t > 0`, `+1` for `t < 0`, and `0` at `t = 0` (where `W_0 ≡ 0`). This reproves the
oriented three-value law analytically, with a strictly shorter argument than the profile route.

### 5. The analytic criterion

By quantization, for any `r < 1`,

`limsup_{s→1⁺} |Re (∑_p W_t(p) p^{-(s-1)})| / L(s) ≤ r  ⟹  t = 0`,

and conversely `t = 0` makes the numerator identically zero. Specialising `t` to
`2 Re rho - 1` at a Xi divisor point and using the corpus critical-line identification:

**RH holds iff at every Xi divisor point the normalised abscissa value of the explicit prime
Dirichlet series `∑_p W_{t_rho}(p) p^{-(s-1)}` drops below the harmonic quantum.**

## Hostile audit

- No RH premise, divisor criticality, or source-flatness hypothesis enters. Steps 1–4 are
  summability plus one classical asymptotic already formalized in the corpus.
- Not a renaming of the profile reader: the two computations share no ingredient, and step 4 is a
  genuinely shorter proof of an existing corpus theorem, which is evidence the language is better
  suited, not merely different.
- It remains a criterion re-encoding: the invariant is the same, so the fourth-pass classification
  of the first-wall lane is untouched. What changes is the toolset that can attack it — boundary
  behaviour of an explicit prime Dirichlet series, rather than cofinal averages.
- Non-vacuity: at `t = 0` the numerator vanishes identically, and for `t ≠ 0` the limit has modulus
  one, so the hypothesis is satisfiable exactly on the critical line.

## Door / frontier delta

Old open core (profile form): exhibit a bounded cofinal unit profile and `r < 1` with frequent
sub-quantum real parts.

New equivalent open core (analytic form): show

`limsup_{s→1⁺} |Re (∑_p W_{t_rho}(p) p^{-(s-1)})| / (-log(s-1)) < 1`

at every Xi divisor point. This is a boundary-behaviour statement about an explicit Euler-type prime
Dirichlet series, which is where the corpus's `PrimeZetaLogAsymptotic`, Euler-product and sieve layers
live.

## Log

- 2026-08-06 — created directly in stage 2. Paper proof complete and dependency-closed on the corpus
  asymptotic `tendsto_primeZeta_add_log_sub`. Formalization deferred: the RHTower dependency cone was
  being rebuilt by a concurrent session, so no build could be run; the Lean layer is the next step.

## Addendum — the analytic reader has the same resolution `[PROVED HERE]`

It would be easy to over-read the change of language. It buys tools, not strength, and the exact
correspondence can be written down.

Because `|1/p - F(p)| ≤ 3/p²`, we have `Φ(σ) = P(σ) + O(1)` uniformly on `σ ≥ 1`, so for `t ≠ 0`

`∑_p W_t(p) p^{-(s-1)} = -sign(t) · (P(s) - P(s + 2|t|)) + O(1)`.

Write `u = s - 1`. The corpus asymptotic gives `P(1 + v) = log(1/v) + C + o(1)` as `v → 0⁺`, and `P` is
finite and decreasing for `v` bounded away from `0`; hence up to `O(1)`

`P(s) - P(s + 2|t|) = log(1/u) - log(1/(u + 2|t|)) + O(1) = log((u + 2|t|)/u) + O(1)`.

Dividing by `L(s) = log(1/u)`:

`(∑_p W_t(p) p^{-(s-1)}) / L(s) = -sign(t) · (1 - log(1/(u+2|t|)) / log(1/u)) + O(1/log(1/u))`.

So the normalised value is close to `∓1` exactly when `2|t| ≫ u`, and close to `0` exactly when
`2|t| ≲ u`. **The reader at height `u` resolves grades down to `|t| ≈ u`.**

Comparing with the profile-side two-sided law, where a stage carried inside `[q, Q]` resolves grades
down to `|t| ≈ 1/log Q`, the two devices are matched under

`u ↔ 1 / log(depth)`,  i.e.  `depth ↔ exp(1/u)`.

Two consequences, both honest and both negative for hoping the analytic form is stronger:

1. **The bounded-depth no-go transfers.** For any fixed `u > 0` — that is, for `s` bounded away from
   the abscissa — there are nonzero grades whose normalised value is below any prescribed threshold,
   namely all `|t| ≲ u`. So no evaluation at a fixed `s > 1` decides, exactly as no bounded-depth
   stage decides. The limit `s → 1⁺` is as irreducible as unbounded depth.
2. **Real `s` cannot see more than the residue.** At real `s` the coefficients `p^{-(s-1)}` are
   positive, so the reader is again a positive functional of the prime field, and its only invariant
   is the harmonic coefficient. The change of language does not enlarge the set of visible invariants.

### Where a genuine change of invariant would have to come from

The first structural break available is to leave the positive cone: evaluate at `s = σ + iγ` with
`γ ≠ 0`. Then the reader is oscillatory, and `P(s)` is no longer a single log singularity at `s = 1`
but carries singularities at `ρ/k` for zeros `ρ` and `k ≥ 1` through `P(s) = ∑_k (μ(k)/k) log ζ(ks)`.
An oscillatory reader therefore *sees the zeros themselves* rather than only a positive coefficient,
which is an ontological change of the reader, not a sharpening of it.

This is recorded as a direction, not a claim: no proof route is asserted, and the corpus no-go
`route_r/phase_defect_character_blindness_no_go` — which concerns defect data on the adelic scaling
group — does not apply to `P(σ + iγ)` and so neither blocks nor supports it. Before any work is spent
there it must clear the usual gate: the corpus's Route R producer no-gos in
`docs/drafts/pipeline/5-failed`, and the criterion re-encoding template.

## 2026-08-07 — the general reader law is formalized

Module `formal/GaloisForLFunctions/RHTower/HarmonicResidueAbscissaReader.lean`, built green
(3178 jobs), axioms `[propext, Classical.choice, Quot.sound]` on every capstone. Imports only
`RHTower/PrimeZetaLogAsymptotic` and `HTGeometry/CofinalUnitProfileResidue`, deliberately keeping the
law off the heavy Route R cone.

- `primeAbscissaSeries a s = ∑' p, a p * p^(-(s-1))`, `abscissaLog s = -log (s-1)`.
- `primeHarmonicWeight_mul_abscissaShift` — the rpow bookkeeping `p⁻¹ · p^(-(s-1)) = p^(-s)` that puts
  the harmonic field exactly at the abscissa.
- `tendsto_abscissaLog_atTop` — `-log(s-1) → ∞` on `𝓝[>]1`, proved directly from
  `Iio_mem_nhds` and `Real.log_le_log` rather than through a named log-limit lemma.
- `tendsto_primeZeta_div_abscissaLog` — `P(s) / (-log(s-1)) → 1`, from the corpus asymptotic
  `tendsto_primeZeta_add_log_sub` plus `Tendsto.div_atTop`.
- `summable_primeAbscissaRemainderTerm`, `norm_primeAbscissaRemainder_le` — the remainder is bounded
  by `∑_p ‖a - c/p‖` *uniformly* for `s ≥ 1`, which is the whole point of the shift.
- `primeAbscissaSeries_eq` — the split `A(s) = c · P(s) + R(s)`.
- `tendsto_primeAbscissaSeries_div_abscissaLog` — **the reader law** `A(s) / (-log(s-1)) → c`.

Gate 2 → 3 is met for the general law. Still to formalize: the Route R specialization of §4–§5 (the
analytic three-value law and the analytic RH characterization), which needs the Route R first-wall
field and so must wait for the `RouteRHarmonicQuantumGapCriterion` cone to finish rebuilding.

## 2026-08-07 — the abscissa reader covers the enlarged domain too `[PROVED HERE]`

The profile reader was extended earlier from `ell^1` to `ell^1 + o(1/p)`. The analytic reader now
matches that domain, so the two readers agree on exactly the same class of fields.

**Statement.** If `b` is negligible against `1/p` — for every `ε > 0` there is a finite set off which
`‖b(p)‖ ≤ ε/p` — then `(∑_p b(p) p^{-(s-1)}) / (-log(s-1)) → 0` as `s → 1⁺`, even when `b` is not
summable.

**Proof.** Off the exceptional finite set `s₀`, `‖b(p)‖ p^{-(s-1)} ≤ ε · p^{-s}`; on `s₀` the shift is
at most one, so the terms are bounded by `‖b(p)‖`. Hence pointwise

`‖b(p)‖ p^{-(s-1)} ≤ ε · p^{-s} + 1_{s₀}(p) ‖b(p)‖`

for every `p`, and summing, `‖B(s)‖ ≤ ε · P(s) + C` with `C = ∑_p 1_{s₀}(p)‖b(p)‖` finite and
independent of `s`. Dividing by `L(s) = -log(s-1)` and using `P(s)/L(s) → 1` and `C/L(s) → 0`:

`‖B(s)‖ / L(s) ≤ ε · (P(s)/L(s)) + C/L(s) < 2ε + o(1)`.

Taking `ε` to be a quarter of the target tolerance gives the limit. Note the `ε` is absorbed by the
*normalised* prime zeta value, which is what makes a non-summable error harmless.

Adding the summable part gives the reader law on the enlarged domain,
`tendsto_primeAbscissaSeries_div_abscissaLog_mod`.

**Lean** (same module, `lake build` green, 3178 jobs, axioms
`[propext, Classical.choice, Quot.sound]`): `summable_primeAbscissaTermOfResidue`,
`summable_primeAbscissaNegligibleNorm`, `summable_primeAbscissaTermOfNegligible`,
`norm_primeAbscissaSeries_negligible_le`,
`tendsto_primeAbscissaSeries_div_abscissaLog_of_negligible`,
`tendsto_primeAbscissaSeries_div_abscissaLog_mod`.

## 2026-08-07 — §3 formalized: one invariant, two readers

The card's §3 claim is now a theorem, and it made one earlier premise disappear.

- `tendsto_profileAverage_eq_tendsto_primeAbscissa` — for any bounded cofinal unit profile, if a prime
  field has a residue over `1/p` (in the enlarged `ell^1 + negligible` sense) then the combinatorial
  limit of its cofinal averages and the analytic normalised boundary value of its Dirichlet series are
  the same number.
- `primeHarmonicResidueMod_unique_of_abscissa` — **uniqueness of the residue on the enlarged domain
  from the prime zeta asymptotic alone.** No averaging profile, no enumeration of the primes, no
  divergence argument: the analytic reader has a limit, and limits are unique.

The second item is the sharper one. Uniqueness has now been obtained three independent ways, each
weaker in hypotheses than the last:

1. via a cofinal profile and a prime enumeration (`routeRPrimeHarmonicAsymptotic_unique`, corpus);
2. via divergence of `∑ 1/p` alone, no reader at all (`HasReferenceResidue.unique`);
3. via the prime zeta asymptotic, on the *enlarged* domain where the error may be non-summable
   (`primeHarmonicResidueMod_unique_of_abscissa`).

Route 2 is cheapest on the `ell^1` domain; route 3 is the only one of the three that covers
`ell^1 + o(1/p)` without exhibiting a profile.

Both new theorems: `lake build` green (3178 jobs), axioms `[propext, Classical.choice, Quot.sound]`.

## 2026-08-07 — the analytic reader is now effective, not just asymptotic

A producer cannot act on a limit; it needs a bound at a height it can reach. Both theorems below hold
at a *single* `s > 1`, with no asymptotics.

### Deviation bound

`norm_primeAbscissaSeries_div_sub_residue_le`: writing `L(s) = -log(s-1)` and
`M = ∑_p ‖a - c/p‖`,

`‖A(s)/L(s) - c‖ ≤ (‖c‖ · |P(s) - L(s)| + M) / L(s)`.

Both ingredients on the right are explicit corpus objects: `|P(s) - L(s)|` is the prime zeta defect
against the normaliser, which the corpus asymptotic `tendsto_primeZeta_add_log_sub` shows converges to
`|primeLogDefect 1|`, and `M` is the total mass of the summable part. The proof is the split
`A/L - c = c(P-L)/L + R/L` followed by the uniform remainder bound.

### Height bound at a unit residue

`abscissaLog_le_of_norm_div_le`: if `‖c‖ = 1` and `‖A(s)/L(s)‖ ≤ r` for some `r < 1`, then

`L(s) ≤ (|P(s) - L(s)| + M) / (1 - r)`.

So a sub-quantum reading at height `s` bounds `L(s)`, hence bounds `s` away from the abscissa — the
exact analytic counterpart of the profile-side statement that a sub-quantum stage bounds the depth.
Contrapositive: past an explicit height, a unit residue *cannot* read below the quantum. Combined with
the third-pass no-go this is the same phenomenon in the analytic language, now with an explicit
constant.

Both: `lake build` green (3178 jobs), axioms `[propext, Classical.choice, Quot.sound]`. Neither uses
the Route R first-wall field, so both are available to any producer field with a unit residue.

## 2026-08-07 — both readers now have matched effective forms, and the profile side was de-duplicated

### Effective single-stage bound (profile side)

`GaloisForLFunctions.HTGeometry.norm_stageAverage_sub_residue_le`: for a unit stage `w` vanishing on a
finite set `s`, and a field with residue `c`,

`‖stageAverage w a - c‖ ≤ ∑_{i ∉ s} ‖a(i) - c·h(i)‖`.

This is the profile-side counterpart of the analytic deviation bound, and it *generalises* two lemmas
that were already in the layer: `norm_profileAverage_le_tsum_compl` is its `c = 0` case, and
`profileAverage_eq_add_remainder` is the profile instance of the new
`stageAverage_eq_add_remainder`. The stage-level statements are the honest ones — none of the four
uses cofinality, only one stage.

Consequently `norm_profileTerm_le`, `summable_profileTerm` and `hasSum_profileReference` are now
one-line delegations to their stage-level versions, with signatures unchanged so nothing downstream
moved.

### Matching lower bound (analytic side)

`RHTower.le_norm_primeAbscissaSeries_div`:

`‖c‖ - (‖c‖·|P(s) - L(s)| + M)/L(s) ≤ ‖A(s)/L(s)‖`.

Together with the deviation bound this brackets the analytic reading at every single height, exactly as
the two-sided scale law brackets the profile reading at every single depth.

All: `lake build` green (`CofinalUnitProfileResidue` 2357 jobs, `HarmonicResidueAbscissaReader` 3178
jobs), axioms `[propext, Classical.choice, Quot.sound]`.

### Discoverability

`scripts/formal_tools.py index` regenerated, and `research "harmonic residue cofinal profile average
abscissa"` now returns the layer's capstones —
`tendsto_profileAverage_eq_tendsto_primeAbscissa`, `primeHarmonicResidueMod_unique_of_abscissa`,
`norm_stageAverage_sub_residue_le` — so a future producer finds them instead of re-deriving
coefficient extraction inline, which is what the corpus has been doing.

## 2026-08-07 — §4–§5 formalized; card advances to stage 3

The Route R cone finished rebuilding (six successive capped `lake build` attempts, no errors, ending
at 11303/11303), which unblocked everything that was pending.

### Previously unverified, now confirmed

`primeHarmonicResidueMod_unique` and `riemannHypothesis_of_frequently_negligible_producer` in
`RouteRHarmonicQuantumGapCriterion` both elaborate and carry
axioms `[propext, Classical.choice, Quot.sound]`. They were written blind while the cone was down; the
low-risk assessment held.

### New module `RHTower/RouteRFirstWallAbscissaCriterion.lean`

`lake build` green (11307 jobs), axioms `[propext, Classical.choice, Quot.sound]`, in the umbrella.

- `tendsto_primeAbscissa_criticalWall_neg_one_of_pos`,
  `tendsto_primeAbscissa_criticalWall_one_of_neg` — the analytic three-value law. Both are one-line
  instantiations of the general reader against the corpus residue facts, which is the payoff of having
  built the reader generically.
- `primeAbscissaSeries_criticalWall_zero` — neutral grade gives the zero series at every height.
- `eq_zero_of_frequently_abs_re_primeAbscissa_le` — sub-quantum real parts, frequently as `s → 1⁺`,
  force neutral grade.
- `riemannHypothesis_iff_frequently_abs_re_primeAbscissa_lt_one` — **RH as a boundary statement about
  one explicit prime Dirichlet series**, an `iff`.

To state the criterion along the filter `𝓝[>]1` rather than a sequence, the helper
`not_frequently_abs_re_le_of_unit_limit` was generalised from `ℕ`/`atTop` to an arbitrary `NeBot`
filter; both existing call sites unify unchanged.

### Status

Gate 2 → 3 met. The card records an equivalent analytic form of a criterion whose lane was already
classified as a re-encoding, together with the addendum proving the analytic form has the same
resolution. It is a change of language with matched effective bounds, not a strengthening — that
scope note stands unaltered.
