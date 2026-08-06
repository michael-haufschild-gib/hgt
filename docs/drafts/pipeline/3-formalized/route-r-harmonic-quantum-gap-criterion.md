# Route R harmonic quantum gap criterion

- **ID:** route-r-harmonic-quantum-gap-criterion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `cofinal-bockstein-polarized-adelic-stokes.md` · first-wall open core, via
  `route-r-cofinal-sieve-harmonic-residue`
- **Statement:** The oriented first-wall harmonic residue is read by every bounded, unit-mass,
  cofinally escaping prime profile, and its values are quantized in `{-1,0,1}`; hence a strict
  modulus bound below one — not exact annihilation — already forces critical placement.

## Goal

Replace the producer obligation "make one explicit reporter converge to zero" by an open condition.
The previous open core asked for an exact limit `S_N(W_{t_rho}) -> 0`. Because the limit is a
quantized coordinate, any device-independent bound `limsup |average| <= r < 1` excludes both
orientations and therefore forces `t_rho = 0`. This widens the class of admissible source producers
from those achieving an equality to those achieving any strict inequality, and removes the
dependence on the particular Euler-sieve device.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2 fully-proven: complete paper proof, no open dependency
- [x] 2 → 3 formalized: Lean theorems below, targeted `lake build` green, axiom audit clean
- [ ] 3 → 4 publication-ready: standalone paper and refreshed external novelty audit

## Internal corpus audit

- `[CORPUS]` `RouteRCriticalWallOrientedHarmonicQuantization` proves the oriented three-value law
  for the first-wall coefficient modulo `ell^1`.
- `[CORPUS]` `RouteRCofinalSieveHarmonicResidue` builds one concrete reader — the restarted Euler
  sieve — and proves it recovers the coefficient. Its uniqueness lemma is proved through that
  reader.
- `[CORPUS]` No module isolated the properties of a reader actually used, and none stated a
  criterion weaker than exact vanishing.
- `[NEW]` `HTGeometry/CofinalUnitProfileResidue` isolates them: bounded by one, unit reference mass,
  supports escaping every finite set.
- `[NEW]` `RHTower/RouteRHarmonicQuantumGapCriterion` derives the gap criterion and the RH endpoint.

## Complete paper proof `[PROVED HERE]`

Let `h` be a weight on an index set and call `c` the *residue* of a field `a` over `h` when
`a - c h` is summable.

**Uniqueness.** If `a - c h` and `a - d h` are both summable then `(d - c) h` is summable. When `h`
is not summable this forces `c = d`. No averaging device occurs; divergence alone suffices. This
strictly simplifies the corpus uniqueness argument, which routed through a reporter and a fixed
prime enumeration.

**Reading law.** Call `mu_N` a *cofinal unit profile* for `h` when `0 <= mu_N <= 1` pointwise,
`sum_i mu_N(i) h(i) = 1`, and for every finite set `s` the stage `mu_N` vanishes on `s` for all
large `N`. Write `A_N(a) = sum_i mu_N(i) a(i)`. Then `A_N(h) = 1` exactly, and for summable `b`,
`|A_N(b)| <= sum_i mu_N(i)|b(i)| <= sum_{i notin s}|b(i)|` once `mu_N` vanishes on `s`; choosing `s`
with small complementary mass gives `A_N(b) -> 0`. Hence `A_N(a) -> c` whenever `a` has residue `c`.
Only the three listed properties are used, so every such device reads the same coordinate.

**Non-vacuity.** For strictly positive divergent `h` on the natural numbers, let `m(N)` be the least
index at which the accumulated tail mass from `N` first reaches one. Give weight `1` to the indices
`N, ..., m(N)-1` and weight `(1 - sum_{N <= i < m(N)} h(i)) / h(m(N))` to `m(N)`. Minimality gives
`sum_{N <= i < m(N)} h(i) < 1` and `sum_{N <= i <= m(N)} h(i) >= 1`, so the top weight lies in
`[0,1]` and the total mass is exactly one. Supports lie in `[N, m(N)]`, so they escape. Transport
along an equivalence carries this to any countable index set, in particular to the primes with
`h(p) = 1/p`.

**Quantum gap.** For the Route R first-wall field `W_t`, the corpus orientation theorems give
residue `-1` for `t > 0`, `+1` for `t < 0`, and `0` at `t = 0`. Let `mu` be any cofinal unit profile
for `p -> 1/p` and suppose `|A_N(W_t)| <= r` eventually with `r < 1`. Continuity of the norm and the
reading law give `|residue| <= r`, excluding `-1` and `+1`. Hence `t = 0`.

**Endpoint.** Specializing `t` to `2 Re rho - 1` at a Xi divisor point and using the corpus
identification of neutral grade with critical placement, a sub-quantum gap at every divisor point
gives the Riemann hypothesis. The threshold `r` may depend on the divisor point.

## Lean

Module `formal/GaloisForLFunctions/HTGeometry/CofinalUnitProfileResidue.lean`:

- `HasReferenceResidue`, `HasReferenceResidue.unique`, `HasReferenceResidue.of_summable_sub`
- `IsCofinalUnitProfile`, `profileAverage`, `tendsto_profileAverage`
- `unitWindowProfile`, `exists_isCofinalUnitProfile`, `exists_isCofinalUnitProfile_of_equiv`
- `primeHarmonicWeight`, `primeHarmonicResidue_unique`,
  `exists_isCofinalUnitProfile_primeHarmonic`

Module `formal/GaloisForLFunctions/RHTower/RouteRHarmonicQuantumGapCriterion.lean`:

- `routeRPrimeHarmonicAsymptotic_iff_hasReferenceResidue`
- `tendsto_profileAverage_criticalWall_neg_one_of_pos`,
  `tendsto_profileAverage_criticalWall_one_of_neg`,
  `tendsto_profileAverage_criticalWall_zero`
- `eq_zero_of_eventually_norm_profileAverage_le`
- `tendsto_profileAverage_criticalWall_zero_iff`
- `xiDivisorSupport_re_eq_half_of_eventually_norm_profileAverage_le`
- `riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half`
- `riemannHypothesis_of_eventually_norm_profileAverage_lt_one`
- `exists_isCofinalUnitProfile_primeHarmonic_nthPrime`

Axioms: `[propext, Classical.choice, Quot.sound]` for every listed capstone.

## Hostile audit

- No RH premise, divisor criticality, or source-flatness hypothesis occurs anywhere in the two
  modules. The reading law and the window construction are pure summability statements.
- The criterion is not a disguised assumption of its conclusion: its hypothesis is an inequality
  about an explicitly constructed average, and both orientations are proved to violate it.
- It is not vacuous in either direction. Profiles exist unconditionally, and at neutral grade the
  average provably tends to zero, so the hypothesis is satisfiable exactly on the critical line.
- It does not close Route R. What is gained is a strictly larger target set for producers: exact
  annihilation is replaced by any uniform gap below the harmonic quantum, and the reading device is
  now arbitrary rather than the Euler sieve.
- Novelty status `[NOVELTY UNVERIFIED]`. The reading law is a Banach-limit-style extraction of a
  coefficient modulo `ell^1`; the parent literature is standard summability theory. No priority is
  claimed for the general law; the Route R application is corpus-internal.

## Door / frontier delta

Old open core: `Tendsto (fun N => S_N(W_{t_rho})) atTop (nhds 0)` for the restarted Euler sieve.

New open core: for **some** bounded cofinal unit profile `mu` on the primes and **some** `r < 1`,

`eventually ‖profileAverage mu N (routeRPrimeGammaXiCriticalWallField rho)‖ ≤ r`.

Any pre-divisor Stokes/Cartier producer may now be tested against a strict inequality, and may
choose its own reading device.

## Log

- 2026-08-06 — created directly in stage 3: general reading law and window construction proved and
  formalized in `HTGeometry`, Route R gap criterion and RH endpoint formalized in `RHTower`,
  targeted builds green, axiom audit clean.

## 2026-08-06 (second pass) — the wall is a scale detector

Two further reductions, both formalized.

### Sharpened asymptotic form

The limiting residue is real and lies in `{-1,0,1}`. Two consequences weaken the criterion further:

1. only the **real part** of the average matters, since `|c.re| = ‖c‖` for a real `c`;
2. only a **subsequence** matters, since a convergent sequence cannot be frequently below `r < 1`
   while converging to something of modulus one.

Lean: `eq_zero_of_frequently_abs_re_profileAverage_le`,
`xiDivisorSupport_re_eq_half_of_frequently_abs_re_profileAverage_le`,
`riemannHypothesis_of_frequently_abs_re_profileAverage_lt_one`.

### Single-stage quantitative form `[PROVED HERE]`

No asymptotics are needed at all. Let `w` be one stage of a bounded unit profile carried by primes at
least `q ≥ 3`, and `F(p) = p/(p+1)^2` the activation Fisher density. Then

`|W_t(p)| = F(p)(1 - p^(-2|t|))`

exactly, for every `t` and `p`, with both orientation cases and the neutral case collapsing to the
same modulus. On the support, `1 - p^(-2|t|) ≥ 1 - q^(-2|t|)` and, from `1/p - F(p) ≤ 3/p²` together
with `q ≤ p`, `F(p) ≥ (1 - 3/q)/p`. Comparing against the unit reference mass gives

`(1 - q^(-2|t|))(1 - 3/q) ≤ ‖stageAverage w (W_t)‖`.

Thus a stage average below `r` forces `(1 - q^(-2|t|))(1 - 3/q) ≤ r`; with `q ≥ 4` and
`r < 1 - 3/q`, exponentiating back gives the explicit grade bound

`|t| ≤ log((1 - 3/q)/(1 - 3/q - r)) / (2 log q)`.

Letting `q → ∞` along stages sharing one threshold `r < 1` gives `t = 0`. The stage index is free:
only the depth of the carrying primes enters.

Lean: `abs_criticalWallCoefficient_eq`, `norm_stageAverage_criticalWall_eq`,
`le_norm_stageAverage_criticalWall`, `abs_le_of_norm_stageAverage_le`,
`eq_zero_of_deepStage_norm_profileAverage_le`, in
`formal/GaloisForLFunctions/RHTower/RouteRFirstWallScaleQuantification.lean`. Supporting single-stage
API in `HTGeometry/CofinalUnitProfileResidue.lean`: `IsUnitStage`, `stageAverage`,
`tsum_stageWeighted_le`, `le_tsum_stageWeighted`, `norm_stageAverage_ofReal`.

### What this says about the producer obligation

The lower bound is sharp in shape: the stage average is governed by `t · log q` and by nothing else
up to `O(1/q)`. So no profile can be *chosen* to make the average small at depth `q` when
`|t| ≫ 1/log q` — size alone never helps, and the producer must supply genuine cancellation at some
finite explicit depth. Conversely the obligation is now finite and quantitative: for a threshold
`r < 1`, exhibiting one stage at depth `q` with average below `r` already bounds `|t|` by
`C(r)/log q`.

Axioms for all new capstones: `[propext, Classical.choice, Quot.sound]`.

## 2026-08-06 (third pass) — the scale law is two-sided, and bounded depth provably fails

### Matching upper bound

For a stage carried by primes **at most** `Q`, the same termwise comparison run in the other
direction gives

`‖stageAverage w (W_t)‖ ≤ 1 - Q^(-2|t|)`,

using `F(p) ≤ 1/p` and `1 - p^(-2|t|) ≤ 1 - Q^(-2|t|)`. Together with the depth floor this traps the
modulus:

`(1 - q^(-2|t|))(1 - 3/q) ≤ ‖stageAverage w (W_t)‖ ≤ 1 - Q^(-2|t|)`

for a stage carried inside `[q, Q]`. Lean: `norm_stageAverage_criticalWall_le`,
`stageAverage_criticalWall_sandwich`.

### Bounded depth cannot decide `[NO-GO]`

The upper bound is not decoration: it kills the localized form of the criterion. Since
`1 - e^{-x} ≤ x`, taking `t = r / (2 log Q)` gives `1 - Q^(-2|t|) ≤ r`. Hence for **any** stage with
a depth ceiling `Q ≥ 2` and **any** tolerance `r > 0` there is a *nonzero* grade whose average at
that stage is within `r`. A finitely supported stage always has such a ceiling, so:

- no single stage separates neutral grade;
- no finite family of stages does either;
- the unbounded-depth quantifier in `eq_zero_of_deepStage_norm_profileAverage_le` is intrinsic.

Lean: `exists_ne_zero_norm_stageAverage_le`, `exists_depthCeiling_of_finite_support`,
`exists_ne_zero_norm_stageAverage_le_of_finite_support`, and the witnessed form
`exists_isCofinalUnitProfile_no_single_stage_decides` — there is a bounded cofinal prime-harmonic
profile all of whose stages are finite, and every one of its stages is evaded by some nonzero grade.
The witness comes from `exists_isCofinalUnitProfile_finiteSupport_primeHarmonic`, the window
construction strengthened to record finiteness of each stage support.

### What the sandwich means for the producer

The device is exactly a scale meter: its output is determined, up to the ratio `log Q / log q` of the
two depths and an `O(1/q)` Fisher correction, by the single number `|t| · log(depth)`. Two
consequences, both now theorems:

1. no reweighting inside the family helps — smallness at depth `q` is impossible once
   `|t| ≫ 1/log q` (depth floor);
2. no bounded depth suffices — smallness at depth `Q` is achievable by nonzero grades of size
   `≈ r/log Q` (depth ceiling).

So the remaining content is neither the choice of device nor a finite certificate: the producer must
deliver cancellation simultaneously at unboundedly deep scales. That is the exact shape of
`ROUTE_R_FIRST_WALL_FINITE_DEPTH_CANCELLATION` as recorded on the parent card, and the third pass
narrows it to its unbounded-depth core.

Axioms for all new capstones: `[propext, Classical.choice, Quot.sound]`.

## 2026-08-06 (fourth pass) — the criterion becomes an equivalence; lane classified

### The depth floor was never a hypothesis

The primes below any bound form a finite set, so cofinal escape *already* forces every stage far
enough out to be carried above that bound: `eventually_deepStage`. Consequently the deep-stage
criterion and the asymptotic criterion are the same condition
(`exists_deepStage_of_frequently`), and one frequent modulus bound yields the explicit grade bound at
every admissible depth simultaneously (`abs_le_of_frequently_norm_profileAverage_le`). The `hdeep`
hypothesis of the third pass is discharged, not assumed.

### Linearized ceiling

`1 - e^{-x} ≤ x` turns the ceiling bound into the usable form

`‖stageAverage w (W_t)‖ ≤ 2 |t| log Q`

(`norm_stageAverage_criticalWall_le_scale`): to certify threshold `r` at depth `Q` a producer must
reach `|t| ≤ r / (2 log Q)`, and nothing weaker.

### RH characterization `[PROVED HERE]`

Forward, neutral grade makes the coefficient field identically zero, hence every stage average zero
(`profileAverage_criticalWall_zero_eq_zero`), and RH puts every Xi divisor point on the critical line
by the corpus theorem `xi_divisor_support_re_eq_half_of_rh`. Backward is the sharpened gap criterion.
Therefore, for **any** bounded cofinal prime-harmonic profile `mu`:

`RiemannHypothesis ↔ ∀ rho, ∃ r < 1, ∃ᶠ N, |(profileAverage mu N (W_{t_rho})).re| ≤ r`

Lean: `riemannHypothesis_iff_frequently_abs_re_profileAverage_lt_one`. Axioms
`[propext, Classical.choice, Quot.sound]`.

### Lane classification `[TERMINUS]`

With the equivalence proved and both sides of the scale law in place, this lane is now *classified*
rather than open, and the classification is negative for the purpose of finding slack:

- the reading device carries no freedom (any bounded cofinal unit profile computes the same
  coordinate);
- the depth floor carries no freedom (escape supplies it);
- bounded depth carries no information (every depth-ceilinged stage is evaded by nonzero grades);
- the modulus is pinned two-sidedly by `|t| · log(depth)`, so no partial bound on `|t|` short of zero
  can be extracted: a bound `|t| ≤ δ` for fixed `δ > 0` is exactly a bounded-depth certificate, which
  the third-pass no-go shows is always satisfiable.

The remaining content is therefore the full statement `t_rho = 0`, i.e. RH itself. Per
`docs/meta/scientific-method.md` this is a criterion re-encoding, and the honest positive residue is
the quantified equivalence plus the four no-freedom statements above, not progress toward a proof.
The card stays at stage 3; no further sharpening of this reporter family is worth attempting.

## 2026-08-06 (fifth pass) — the reading law on an enlarged domain

The lane is closed as a criterion (fourth pass), but the *reader* was still tied to `ell^1`. This pass
enlarges its domain, which is what a producer actually needs: a source field that agrees with the
first wall up to a non-summable but pointwise small error.

### Negligible fields

Call `b` *negligible* against `h` when for every `ε > 0` there is a finite set off which
`‖b i‖ ≤ ε · h i`. Negligible fields need not be summable and summable fields need not be
negligible — the classes are incomparable. Over the primes with `h(p) = 1/p`, negligible means
`b(p) = o(1/p)` with an explicit depth threshold, and this catches non-summable examples: `∑_p 1/p`
diverges like `log log x`, so `b(p) = 1/(p log log p)` is not summable while `p · b(p) → 0`.

`[PROVED HERE]` Negligible fields are invisible to cofinal averaging. Once a stage vanishes on the
finite exceptional set, the bound `mu_N(i) ‖b(i)‖ ≤ ε · (mu_N(i) h(i))` holds at *every* index, so the
unit reference mass gives `‖A_N(b)‖ ≤ ε` directly — no convergence of `b` is used. Summability of the
stage terms at a fixed `N`, where escape has not yet happened, comes from majorizing by
`mu_N h + indicator(s)·mu_N‖b‖`.

Hence the residue is read modulo `ell^1 + negligible`:

`HasReferenceResidueMod h a c := ∃ b₁ b₂, Summable b₁ ∧ IsCofinitelyNegligible h b₂ ∧
   a - c h = b₁ + b₂`

and `tendsto_profileAverage_mod` gives `A_N(a) → c` on that larger domain, with uniqueness from the
existence of a single profile (`HasReferenceResidueMod.unique_of_profile`).

### Robust criterion

`[PROVED HERE]` The threshold test transfers to any producer field: if `a - W_t` is summable or
`o(1/p)`, then `a` carries the same oriented residue, so a frequent sub-quantum bound on `a`'s own
averages forces `t = 0`
(`eq_zero_of_frequently_abs_re_profileAverage_le_of_negligible_sub`), and

`riemannHypothesis_of_frequently_negligible_producer`

closes RH from producer fields that need never equal the first-wall field exactly.

### Lean

`HTGeometry/CofinalUnitProfileResidue.lean`: `IsCofinitelyNegligible`,
`summable_profileTerm_negligible`, `tendsto_profileAverage_zero_of_cofinitelyNegligible`,
`HasReferenceResidueMod`, `HasReferenceResidue.mod`, `profileAverage_add`,
`tendsto_profileAverage_mod`, `HasReferenceResidueMod.unique_of_profile`,
`primeHarmonicWeight_nonneg`, `finite_primes_lt`, `isCofinitelyNegligible_primeHarmonic`.

`RHTower/RouteRHarmonicQuantumGapCriterion.lean`: `not_frequently_abs_re_le_of_unit_limit` (the
sequence-level form, replacing the earlier specialized private lemma),
`hasReferenceResidueMod_of_negligible_sub_criticalWall`,
`eq_zero_of_frequently_abs_re_profileAverage_le_of_negligible_sub`,
`primeHarmonicResidueMod_unique`, `riemannHypothesis_of_frequently_negligible_producer`.

### Scope note

This enlarges what a producer may hand in; it does not reopen the lane. The fourth-pass classification
stands: the criterion is equivalent to RH per zero, and the enlargement changes the admissible error
class, not the difficulty.
